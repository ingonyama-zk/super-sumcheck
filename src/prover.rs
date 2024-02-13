use crate::{
    data_structures::{LinearLagrangeList, MatrixPolynomial},
    transcript::TranscriptProtocol,
    IPForMLSumcheck,
};
use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, vec::Vec};
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// A sumcheck proof contains all round polynomials
pub struct SumcheckProof<EF: PrimeField> {
    pub(crate) num_vars: usize,
    pub(crate) degree: usize,
    pub(crate) round_polynomials: Vec<Vec<EF>>,
}

pub enum AlgorithmType {
    Naive,
    WitnessChallengeSeparation,
    Precomputation,
    Karatsuba,
}

/// Prover State
/// EF stands for extension field and BF stands for base field
pub struct ProverState<EF: PrimeField, BF: PrimeField> {
    /// sampled randomness (for each round) given by the verifier
    pub randomness: Vec<EF>,
    /// Stores a list of multilinear extensions
    pub state_polynomials: Vec<LinearLagrangeList<BF>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
    /// Algorithm type for small field sumcheck
    pub algo: AlgorithmType,
}

impl<EF: PrimeField, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Initialise prover state from a given set of polynomials (in their evaluation form).
    /// The degree of the sumcheck round polynomial also needs to be input.
    pub fn prover_init(
        polynomials: &Vec<LinearLagrangeList<BF>>,
        sumcheck_poly_degree: usize,
        algorithm: AlgorithmType,
    ) -> ProverState<EF, BF> {
        // sanity check 1: no polynomials case must not be allowed.
        if polynomials.len() == 0 {
            panic!("Cannot prove empty input polynomials.")
        }

        // sanity check 2: all polynomial evaluations must be of the same size.
        let problem_size = polynomials[0].size;
        let _ = polynomials.iter().enumerate().map(|(i, poly)| {
            if poly.size != problem_size {
                panic!("Polynomial size mismatch at {}", i)
            }
        });

        // sanity check 3: size must be a power of two.
        if !problem_size.is_power_of_two() {
            panic!("Number of polynomial evaluations must be a power of two.")
        }

        let num_variables: usize = log2(2 * problem_size).try_into().unwrap();
        ProverState {
            randomness: Vec::with_capacity(num_variables),
            state_polynomials: polynomials.to_vec(),
            num_vars: num_variables,
            max_multiplicands: sumcheck_poly_degree,
            round: 0,
            algo: algorithm,
        }
    }

    pub fn compute_round_polynomial<G, C, F>(
        round_number: usize,
        state_polynomials: &Vec<LinearLagrangeList<F>>,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_polynomial_degree: usize,
        combine_function: &C,
        transcript: &mut Transcript,
    ) -> EF
    where
        G: CurveGroup<ScalarField = EF>,
        C: Fn(&Vec<F>) -> EF + Sync,
        F: Field,
    {
        let state_polynomial_len = state_polynomials[0].list.len();
        for k in 0..(round_polynomial_degree + 1) {
            for i in 0..state_polynomial_len {
                let evaluations_at_k = state_polynomials
                    .iter()
                    .map(|state_poly| {
                        // evaluate given state polynomial at x_1 = k
                        let o = state_poly.list[i].odd;
                        let e = state_poly.list[i].even;
                        (F::one() - F::from(k as u32)) * e + F::from(k as u32) * o
                    })
                    .collect::<Vec<F>>();

                // apply combine function
                round_polynomials[round_number - 1][k] += combine_function(&evaluations_at_k);
            }
        }

        // append the round polynomial (i.e. prover message) to the transcript
        <Transcript as TranscriptProtocol<G>>::append_scalars(
            transcript,
            b"r_poly",
            &round_polynomials[round_number - 1],
        );

        // generate challenge α_i = H( transcript );
        let alpha: EF = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
            transcript,
            b"challenge_nextround",
        );

        return alpha;
    }

    /// First algorithm
    pub fn prove_with_naive_algorithm<G, EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        to_ef: &T,
    ) where
        G: CurveGroup<ScalarField = EF>,
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
    {
        // The degree of the round polynomial is the highest-degree multiplicand in the combine function.
        let r_degree = prover_state.max_multiplicands;

        // Process round 1 separately as we need to only perform bb multiplications.
        let alpha = Self::compute_round_polynomial::<G, BC, BF>(
            1,
            &prover_state.state_polynomials,
            round_polynomials,
            r_degree,
            &bf_combine_function,
            transcript,
        );

        // From the next round onwards, all of the data will be extension field elements.
        // We copy all of the prover state polynomials to a new data structure of extension field elements.
        // This is because all of the data would be folded using a challenge (an extension field element).
        // So we update the prover state polynomials as follows.
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .iter()
            .map(|list| list.convert(&to_ef))
            .collect();
        for j in 0..prover_state.state_polynomials.len() {
            ef_state_polynomials[j].fold_in_half(alpha);
        }

        // Process the subsequent rounds with only ee multiplications.
        for round_number in 2..=prover_state.num_vars {
            let alpha = Self::compute_round_polynomial::<G, EC, EF>(
                round_number,
                &ef_state_polynomials,
                round_polynomials,
                r_degree,
                &ef_combine_function,
                transcript,
            );

            // update the state polynomials
            for j in 0..ef_state_polynomials.len() {
                ef_state_polynomials[j].fold_in_half(alpha);
            }
        }
    }

    ///
    /// Creates a sumcheck proof consisting of `n` round polynomials each of degree `d` using Algorithm 1.
    /// We allow for any function `combine_function` on a set of MLE polynomials.
    ///
    pub fn prove<G, EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC, // TODO: Using two combines is bad, templatize it?
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        to_ef: &T,
    ) -> SumcheckProof<EF>
    where
        G: CurveGroup<ScalarField = EF>,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<EF>> = (0..prover_state.num_vars)
            .map(|_| vec![EF::zero(); r_degree + 1])
            .collect();

        match prover_state.algo {
            AlgorithmType::Naive => Self::prove_with_naive_algorithm::<G, EC, BC, T>(
                prover_state,
                &ef_combine_function,
                &bf_combine_function,
                transcript,
                &mut r_polys,
                to_ef,
            ),
            AlgorithmType::WitnessChallengeSeparation => todo!(),
            AlgorithmType::Precomputation => todo!(),
            AlgorithmType::Karatsuba => todo!(),
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }

    ///
    /// Proves the sumcheck relation for product of MLE polynomials using the witness-challenge
    /// separation algorithm (Algorithm 2 that uses pre-computations).
    ///
    pub fn prove_product<G, P>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        mult_be: &P,
    ) -> SumcheckProof<EF>
    where
        G: CurveGroup<ScalarField = EF>,
        P: Fn(&BF, &EF) -> EF + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<EF>> = (0..prover_state.num_vars)
            .map(|_| vec![EF::zero(); r_degree + 1])
            .collect();

        // Create and fill matrix polynomials.
        let mut matrix_polynomials: Vec<MatrixPolynomial<BF>> =
            Vec::with_capacity(prover_state.max_multiplicands);

        for i in 0..prover_state.max_multiplicands {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();

        for round_index in 0..prover_state.num_vars {
            // Compute R = [P(1) ⊛ P(2) ⊛ ... ⊛ P(m)]
            let mut round_matrix_polynomial = matrix_polynomials[0].clone();
            for j in 1..prover_state.max_multiplicands {
                round_matrix_polynomial =
                    round_matrix_polynomial.tensor_hadamard_product(&matrix_polynomials[j]);
            }

            // Collapse R
            round_matrix_polynomial.collapse();

            for k in 0..(r_degree + 1) as u64 {
                let scalar_tuple = DenseMultilinearExtension::from_evaluations_vec(
                    1,
                    vec![EF::ONE - EF::from(k), EF::from(k)],
                );
                let scalar_tuple_matrix = MatrixPolynomial::from_dense_mle(&scalar_tuple);

                // Compute Γ = (Γ_i ⊛ Γ_i ⊛ ... ⊛ Γ_i)
                // where Γ_i = (Γ_challenges ⊛ Γ_scalar)
                let gamma_i_matrix =
                    challenge_matrix_polynomial.tensor_hadamard_product(&scalar_tuple_matrix);
                let mut gamma_matrix = gamma_i_matrix.clone();

                for _ in 1..prover_state.max_multiplicands {
                    gamma_matrix = gamma_matrix.tensor_hadamard_product(&gamma_i_matrix);
                }

                // Ensure Γ has only 1 column
                assert_eq!(gamma_matrix.no_of_columns, 1);

                // Compute round polynomial evaluation at k
                r_polys[round_index][k as usize] = MatrixPolynomial::dot_product(
                    &round_matrix_polynomial,
                    &gamma_matrix,
                    &mult_be,
                );
            }

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TranscriptProtocol<G>>::append_scalars(
                transcript,
                b"r_poly",
                &r_polys[round_index],
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Update challenge matrix with new challenge
            let challenge_tuple =
                DenseMultilinearExtension::from_evaluations_vec(1, vec![EF::ONE - alpha, alpha]);
            let challenge_tuple_matrix = MatrixPolynomial::from_dense_mle(&challenge_tuple);
            challenge_matrix_polynomial =
                challenge_matrix_polynomial.tensor_hadamard_product(&challenge_tuple_matrix);

            // Heighten the witness polynomial matrices
            for j in 0..prover_state.max_multiplicands {
                matrix_polynomials[j].heighten();
            }
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }
}

use crate::{
    data_structures::{LinearLagrangeList, MatrixPolynomial},
    transcript::TranscriptProtocol,
    IPForMLSumcheck,
};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, vec::Vec};
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// A sumcheck proof contains all round polynomials
pub struct SumcheckProof<F: PrimeField> {
    pub(crate) num_vars: usize,
    pub(crate) degree: usize,
    pub(crate) round_polynomials: Vec<Vec<F>>,
}

/// Prover State
pub struct ProverState<F: PrimeField> {
    /// sampled randomness (for each round) given by the verifier
    pub randomness: Vec<F>,
    /// Stores a list of multilinear extensions
    pub state_polynomials: Vec<LinearLagrangeList<F>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
}

impl<F: PrimeField> IPForMLSumcheck<F> {
    /// Initialise prover state from a given set of polynomials (in their evaluation form).
    /// The degree of the sumcheck round polynomial also needs to be input.
    pub fn prover_init(
        polynomials: &Vec<LinearLagrangeList<F>>,
        sumcheck_poly_degree: usize,
    ) -> ProverState<F> {
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
        }
    }

    ///
    /// Creates a sumcheck proof consisting of `n` round polynomials each of degree `d` using Algorithm 1.
    /// We allow for any function `combine_function` on a set of MLE polynomials.
    ///
    pub fn diagnostic_prove<G, C>(
        prover_state: &mut ProverState<F>,
        combine_function: &C,
        transcript: &mut Transcript,
    ) -> SumcheckProof<F>
    where
        G: CurveGroup<ScalarField = F>,
        C: Fn(&Vec<F>) -> F + Sync,
    {
        //fake FS
        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );
        let mut alpha = F::from(4u8);
        println!("\n Prover state: num_vars {:?}",prover_state.num_vars);
        println!("\n Prover state: Max degree {:?}",prover_state.max_multiplicands);
        println!("\n Prover state: Initial state polys: {:?}",prover_state.state_polynomials);
        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<F>> = (0..prover_state.num_vars)
            .map(|_| vec![F::zero(); r_degree + 1])
            .collect();

        for round_index in 0..prover_state.num_vars {
            println!("\n -------Round number: p: {:?}------------", round_index);
            println!("\n ------Begin Phase_1:accumulate----------");
            println!("\n Prover state: State polys in beginning of round {:?} are {:?}",round_index,prover_state.state_polynomials);
            let state_polynomial_len = prover_state.state_polynomials[0].list.len();
            println!("\n State poly length is {:?} in round {:?}",state_polynomial_len,round_index);
            for k in 0..(r_degree + 1) {
                for i in 0..state_polynomial_len {
                    let evaluations_at_k = prover_state
                        .state_polynomials
                        .iter()
                        .map(|state_poly| {
                            // evaluate given state polynomial at x_1 = k
                            let o = state_poly.list[i].odd;
                            let e = state_poly.list[i].even;
                            (F::one() - F::from(k as u32)) * e + F::from(k as u32) * o
                        })
                        .collect::<Vec<F>>();

                    // apply combine function
                    r_polys[round_index][k] += combine_function(&evaluations_at_k);
                }
            }
            println!("\n round poly r_{:?}[x] = {:?}",round_index,r_polys[round_index]);
            println!("\n ------Begin Phase_2:FS----------");
            // append the round polynomial (i.e. prover message) to the transcript
                       // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TranscriptProtocol<G>>::append_scalars(
                        transcript,
                        b"r_poly",
                        &r_polys[round_index],
            );
        
            // generate challenge α_i = H( transcript );
            // alpha += F::from(1u8);
                    //fake FS
            println!("\n Alpha_{:?} = {:?}",round_index,alpha);
            // update prover state polynomials
            println!("\n ------Begin Phase_3: folding----------");
            for j in 0..prover_state.state_polynomials.len() {
                prover_state.state_polynomials[j].fold_in_half(alpha);
            }
            println!("\n State polynomial at end of round {:?} is {:?}",round_index,prover_state.state_polynomials);
            alpha+=F::from(4u8);
        }
        println!("\n ------End Prover------");
        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }

    pub fn prove<G, C>(
        prover_state: &mut ProverState<F>,
        combine_function: &C,
        transcript: &mut Transcript,
    ) -> SumcheckProof<F>
    where
        G: CurveGroup<ScalarField = F>,
        C: Fn(&Vec<F>) -> F + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        println!("\n Prover state: num_vars {:?}",prover_state.num_vars);
        println!("\n Prover state: Max degree {:?}",prover_state.max_multiplicands);
        println!("\n Prover state: Initial state polys: {:?}",prover_state.state_polynomials);
        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<F>> = (0..prover_state.num_vars)
            .map(|_| vec![F::zero(); r_degree + 1])
            .collect();

        for round_index in 0..prover_state.num_vars {
            println!("\n Round number: p: {:?}", round_index);
            println!("\n Begin Phase_1:accumulate");
            println!("\n Prover state: State polys in beginning of round {:?} are {:?}",round_index,prover_state.state_polynomials);
            let state_polynomial_len = prover_state.state_polynomials[0].list.len();
            println!("\n State poly length is {:?} in round {:?}",state_polynomial_len,round_index);
            for k in 0..(r_degree + 1) {
                for i in 0..state_polynomial_len {
                    let evaluations_at_k = prover_state
                        .state_polynomials
                        .iter()
                        .map(|state_poly| {
                            // evaluate given state polynomial at x_1 = k
                            let o = state_poly.list[i].odd;
                            let e = state_poly.list[i].even;
                            (F::one() - F::from(k as u32)) * e + F::from(k as u32) * o
                        })
                        .collect::<Vec<F>>();

                    // apply combine function
                    r_polys[round_index][k] += combine_function(&evaluations_at_k);
                }
            }
            println!("\n round poly r_{:?}[x] = {:?}",round_index,r_polys[round_index]);
            println!("\n Begin Phase_2:FS");
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
            println!("\n Alpha_{:?} = {:?}",round_index,alpha);
            // update prover state polynomials
            println!("\n Begin Phase_3: folding");
            for j in 0..prover_state.state_polynomials.len() {
                prover_state.state_polynomials[j].fold_in_half(alpha);
            }
            println!("\n State polynomial at end of round {:?} is {:?}",round_index,prover_state.state_polynomials);
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
    pub fn prove_product<G>(
        prover_state: &mut ProverState<F>,
        transcript: &mut Transcript,
    ) -> SumcheckProof<F>
    where
        G: CurveGroup<ScalarField = F>,
    {
        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<F>> = (0..prover_state.num_vars)
            .map(|_| vec![F::zero(); r_degree + 1])
            .collect();

        // Create and fill matrix polynomials.
        let mut matrix_polynomials: Vec<MatrixPolynomial<F>> =
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
        let mut challenge_matrix_polynomial: MatrixPolynomial<F> = MatrixPolynomial::one();

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
                    vec![F::ONE - F::from(k), F::from(k)],
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
                r_polys[round_index][k as usize] =
                    round_matrix_polynomial.dot_product(&gamma_matrix);
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
                DenseMultilinearExtension::from_evaluations_vec(1, vec![F::ONE - alpha, alpha]);
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

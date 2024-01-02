use crate::{
    data_structures::{linear_lagrange_list, MatrixPolynomial},
    IPForMLSumcheck,
};
use ark_ff::{batch_inversion_and_mul, Field};
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, vec::Vec};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

// A sumcheck proof contains all round polynomials
pub struct SumcheckProof<F: Field> {
    pub(crate) num_vars: usize,
    pub(crate) degree: usize,
    pub(crate) round_polynomials: Vec<Vec<F>>,
}

/// Prover State
pub struct ProverState<F: Field> {
    /// sampled randomness (for each round) given by the verifier
    pub randomness: Vec<F>,
    /// Stores a list of multilinear extensions
    pub state_polynomials: Vec<linear_lagrange_list<F>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
}

impl<F: Field> IPForMLSumcheck<F> {
    pub fn prover_init(
        polynomials: &Vec<linear_lagrange_list<F>>,
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

    /// write comments
    ///
    pub fn prove<C, H>(
        prover_state: &mut ProverState<F>,
        combine_function: &C,
        hash_function: &H,
    ) -> SumcheckProof<F>
    where
        C: Fn(&Vec<F>) -> F + Sync,
        H: Fn(&Vec<F>) -> F + Sync,
    {
        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<F>> = (0..prover_state.num_vars)
            .map(|_| vec![F::zero(); r_degree + 1])
            .collect();
        let previous_alpha = F::zero();

        for round_index in 0..prover_state.num_vars {
            let state_polynomial_len = prover_state.state_polynomials[0].list.len();
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

            // generate challenge α_i = H(α_{i-1}, r_poly);
            let mut preimage: Vec<F> = r_polys[round_index].clone();
            preimage.insert(0, previous_alpha);
            let alpha = hash_function(&preimage);

            // update prover state polynomials
            for j in 0..prover_state.state_polynomials.len() {
                prover_state.state_polynomials[j].fold_in_half(alpha);
            }
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }

    pub fn prove_product<H>(
        prover_state: &mut ProverState<F>,
        hash_function: &H,
    ) -> SumcheckProof<F>
    where
        H: Fn(&Vec<F>) -> F + Sync,
    {
        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<F>> = (0..prover_state.num_vars)
            .map(|_| vec![F::zero(); r_degree + 1])
            .collect();
        let previous_alpha = F::zero();

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

            // generate challenge α_i = H(α_{i-1}, r_poly);
            let mut preimage: Vec<F> = r_polys[round_index].clone();
            preimage.insert(0, previous_alpha);
            let alpha = hash_function(&preimage);

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

    ///
    /// write comments $`a+b`$
    /// ```math
    /// f(x = v) = \sum_j g_j
    /// ```
    ///
    pub fn verify<H>(
        claimed_sum: F,
        proof: &SumcheckProof<F>,
        hash_function: &H,
    ) -> Result<bool, &'static str>
    where
        H: Fn(&Vec<F>) -> F + Sync,
    {
        if proof.num_vars == 0 {
            return Err("Invalid proof.");
        }

        let mut expected_sum = claimed_sum;
        let previous_alpha = F::zero();
        for round_index in 0..proof.num_vars {
            let round_poly_evaluations: &Vec<F> = &proof.round_polynomials[round_index];
            if round_poly_evaluations.len() != (proof.degree + 1) {
                panic!(
                    "incorrect number of evaluations of the {}-th round polynomial",
                    round_index + 1
                );
            }

            let round_poly_evaluation_at_0 = round_poly_evaluations[0];
            let round_poly_evaluation_at_1 = round_poly_evaluations[1];
            let computed_sum = round_poly_evaluation_at_0 + round_poly_evaluation_at_1;

            // Check r_{i}(α_i) == r_{i+1}(0) + r_{i+1}(1)
            if computed_sum != expected_sum {
                return Err("Prover message is not consistent with the claim.".into());
            }

            // generate challenge
            let mut preimage: Vec<F> = round_poly_evaluations.clone();
            preimage.insert(0, previous_alpha);
            let alpha = hash_function(&preimage);

            // Compute r_{i}(α_i) using barycentric interpolation
            expected_sum = barycentric_interpolation(round_poly_evaluations, alpha);
        }
        Ok(true)
    }
}

///
/// write comments
/// explain why this works only for num_points ≤ 20
/// Reference: Equation (3.3) from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf
///
pub(crate) fn barycentric_interpolation<F: Field>(evaluations: &[F], x: F) -> F {
    let num_points = evaluations.len();
    let mut lagrange_coefficients: Vec<F> =
        (0..num_points).map(|j| x - F::from(j as u64)).collect();
    let lagrange_evaluation = lagrange_coefficients
        .iter()
        .fold(F::one(), |mult, lc| mult * lc);

    for i in 0..num_points {
        let negative_factorial = u64_factorial(num_points - 1 - i);
        let positive_factorial = u64_factorial(i);

        let barycentric_weight = negative_factorial * positive_factorial;
        if (num_points - 1 - i) % 2 == 1 {
            lagrange_coefficients[i] *= -F::from(barycentric_weight);
        } else {
            lagrange_coefficients[i] *= F::from(barycentric_weight);
        }
    }

    batch_inversion_and_mul(&mut lagrange_coefficients, &F::one());

    return lagrange_evaluation
        * evaluations
            .iter()
            .zip(lagrange_coefficients.iter())
            .fold(F::zero(), |acc, (&e, &lc)| acc + e * lc);
}

/// compute the factorial(a) = 1 * 2 * ... * a
#[inline]
fn u64_factorial(a: usize) -> u64 {
    let mut res = 1u64;
    for i in 1..=a {
        res *= i as u64;
    }
    res
}

#[cfg(test)]
mod test {
    use super::u64_factorial;
    use crate::prover::barycentric_interpolation;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::Polynomial;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;

    type F = ark_bls12_381::Fr;

    #[test]
    fn test_u64_factorial() {
        let input = 10 as usize;
        let result = u64_factorial(input);
        let result_prev = u64_factorial(input - 1);
        assert_eq!((input as u64) * result_prev, result);
    }

    #[test]
    fn test_interpolation() {
        let mut prng = ark_std::test_rng();

        // test a polynomial with 20 known points, i.e., with degree 19
        let poly = DensePolynomial::<F>::rand(20 - 1, &mut prng);
        let evals = (0..20)
            .map(|i| poly.evaluate(&F::from(i)))
            .collect::<Vec<F>>();
        let query = F::rand(&mut prng);

        assert_eq!(
            poly.evaluate(&query),
            barycentric_interpolation(&evals, query)
        );
    }
}

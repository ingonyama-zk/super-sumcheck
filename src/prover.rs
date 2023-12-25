use crate::{data_structures::linear_lagrange_list, verifier::VerifierMsg, IPForMLSumcheck};
use ark_ff::{batch_inversion_and_mul, Field};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_iter_mut, log2, vec::Vec};
use blake2::digest::typenum::Len;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Prover Message
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverMsg<F: Field> {
    /// evaluations on P(0), P(1), P(2), ...
    pub(crate) evaluations: Vec<F>,
}

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

            // generate challenge
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

    ///
    /// write comments
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

            if computed_sum != expected_sum {
                return Err("Prover message is not consistent with the claim.".into());
            }

            // generate challenge
            let mut preimage: Vec<F> = round_poly_evaluations.clone();
            preimage.insert(0, previous_alpha);
            let alpha = hash_function(&preimage);

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

mod test {
    use crate::data_structures::linear_lagrange;
    use crate::data_structures::linear_lagrange_list;
    use crate::prover::barycentric_interpolation;
    use crate::prover::SumcheckProof;
    use crate::IPForMLSumcheck;
    use ark_ff::Zero;
    use ark_poly::evaluations;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::Polynomial;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;

    use super::ProverState;

    type F = ark_bls12_381::Fr;

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

    fn combine_fn(data: &Vec<F>) -> F {
        assert!(data.len() > 0);
        data[0]
    }

    fn hash_fn(data: &Vec<F>) -> F {
        assert!(data.len() > 0);
        data.iter().sum::<F>() / F::from(8)
    }

    #[test]
    fn test_sumcheck() {
        // Take a simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let claimed_sum = evaluations.iter().fold(F::zero(), |acc, e| acc + e);
        let poly = DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations);

        let polynomials: Vec<linear_lagrange_list<F>> =
            vec![linear_lagrange_list::<F>::from(&poly)];
        let mut prover_state = IPForMLSumcheck::prover_init(&polynomials, 1);
        let proof: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove(&mut prover_state, &combine_fn, &hash_fn);

        let result = IPForMLSumcheck::verify(claimed_sum, &proof, &hash_fn);
        assert_eq!(result.unwrap(), true);
    }
}

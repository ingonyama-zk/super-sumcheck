use ark_ec::CurveGroup;
use ark_ff::{batch_inversion_and_mul, PrimeField};
use merlin::Transcript;

use crate::{prover::SumcheckProof, transcript::TranscriptProtocol, IPForMLSumcheck};

impl<F: PrimeField> IPForMLSumcheck<F> {
    ///
    /// Verify a sumcheck proof by checking for correctness of each round polynomial.
    /// Additionally, checks the evaluation of the original MLE polynomial (via oracle access)
    /// at the challenge vector is correct.
    ///
    /// TODO: Add final evaluation check for verifier using an opening proof (of a commitment scheme).
    /// The verifier does not perform the final check: f(alpha_1, alpha_2, ..., alpha_n) == r_n(alpha_n).
    /// This is because we have not implemented a commitment scheme that can allow a prover to "open" an MLE polynomial.
    /// We could give the verifier an oracle access to the MLE polynomial `f` but we defer this to the commitment
    /// scheme implementation in a future release.
    ///
    pub fn verify<G>(
        claimed_sum: F,
        proof: &SumcheckProof<F>,
        transcript: &mut Transcript,
    ) -> Result<bool, &'static str>
    where
        G: CurveGroup<ScalarField = F>,
    {
        if proof.num_vars == 0 {
            return Err("Invalid proof.");
        }

        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            proof.num_vars as u64,
            proof.degree as u64,
        );
        println!("\n Verifier: Claimed sum {:?}",claimed_sum);
        let mut expected_sum = claimed_sum;
        for round_index in 0..proof.num_vars {
            println!("\n Verifier: Round number {:?}",round_index.clone());
            let round_poly_evaluations: &Vec<F> = &proof.round_polynomials[round_index];
            println!("\n Verifier: Round polynomials at round {:?} are {:?},",round_index,proof.round_polynomials[round_index].clone());
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
            println!("\n Verifier: Computed sum at round {:?} is {:?}",round_index,computed_sum.clone());
            println!("\n Verifier: Expected sum at round {:?} is {:?}",round_index,expected_sum.clone());
            if computed_sum != expected_sum {
                return Err("Prover message is not consistent with the claim.".into());
            }

            // append the prover's message to the transcript
            <Transcript as TranscriptProtocol<G>>::append_scalars(
                transcript,
                b"r_poly",
                &proof.round_polynomials[round_index],
            );

            // derive the verifier's challenge for the next round
            let alpha = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );
            println!("\n Verifier: alpha_{:?} = {:?}",round_index,alpha);
            // Compute r_{i}(α_i) using barycentric interpolation
            expected_sum = barycentric_interpolation(round_poly_evaluations, alpha);
        }
        Ok(true)
    }

    pub fn diagnostic_verify<G>(
        claimed_sum: F,
        proof: &SumcheckProof<F>,
        transcript: &mut Transcript,
    ) -> Result<bool, &'static str>
    where
        G: CurveGroup<ScalarField = F>,
    {
        if proof.num_vars == 0 {
            return Err("Invalid proof.");
        }

        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            proof.num_vars as u64,
            proof.degree as u64,
        );
        println!("\n Verifier: Claimed sum {:?}",claimed_sum);
        let mut alpha = F::from(4u8);
        let mut expected_sum = claimed_sum;
        for round_index in 0..proof.num_vars {
            println!("\n Verifier: Round number {:?}",round_index.clone());
            let round_poly_evaluations: &Vec<F> = &proof.round_polynomials[round_index];
            println!("\n Verifier: Round polynomials at round {:?} are {:?},",round_index,proof.round_polynomials[round_index].clone());
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
            println!("\n Verifier: Computed sum at round {:?} is {:?}",round_index,computed_sum.clone());
            println!("\n Verifier: Expected sum at round {:?} is {:?}",round_index,expected_sum.clone());
            if computed_sum != expected_sum {
                return Err("Prover message is not consistent with the claim.".into());
            }

            // append the prover's message to the transcript
            <Transcript as TranscriptProtocol<G>>::append_scalars(
                transcript,
                b"r_poly",
                &proof.round_polynomials[round_index],
            );

            // derive the verifier's challenge for the next round
            // let alpha = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
            //     transcript,
            //     b"challenge_nextround",
            // );
            println!("\n Verifier: alpha_{:?} = {:?}",round_index,alpha);
            // Compute r_{i}(α_i) using barycentric interpolation
            expected_sum = barycentric_interpolation(round_poly_evaluations, alpha);
            alpha+=F::from(4u8);
        }
        Ok(true)
    }
}

///
/// Evaluates an MLE polynomial at `x` given its evaluations on a set of integers.
/// This works only for `num_points` ≤ 20 because we assume the integers are 64-bit numbers.
/// We know that 2^61 < factorial(20) < 2^62, hence factorial(20) can fit in a 64-bit number.
/// We can trivially extend this for `num_points` > 20 but in practical use cases, `num_points` would not exceed 8 or 10.
/// Reference: Equation (3.3) from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf
///
pub(crate) fn barycentric_interpolation<F: PrimeField>(evaluations: &[F], x: F) -> F {
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
    use crate::verifier::barycentric_interpolation;
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

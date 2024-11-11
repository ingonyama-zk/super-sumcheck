#[cfg(test)]
mod integration_tests {
    use crate::data_structures::LinearLagrangeList;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::IPForMLSumcheck;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    use merlin::Transcript;

    type F = ark_bls12_381::Fr;
    type G = ark_bls12_381::G1Projective;

    #[test]
    fn test_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            data[0]
        }

        // Take a simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let claimed_sum = evaluations.iter().fold(F::zero(), |acc, e| acc + e);
        let poly = DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations);

        let polynomials: Vec<LinearLagrangeList<F>> = vec![LinearLagrangeList::<F>::from(&poly)];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 1);

        // create a proof
        let mut prover_transcript = Transcript::new(b"test_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<F>::prove::<G, _>(
            &mut prover_state,
            &combine_fn,
            &mut prover_transcript,
        );

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result = IPForMLSumcheck::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Take two simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let evaluations_b: Vec<F> = (0..num_evaluations).map(|i| F::from(i + 1)).collect();
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(F::zero(), |acc, (a, b)| acc + a * b);
        let poly_a =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_b);

        let polynomials: Vec<LinearLagrangeList<F>> = vec![
            LinearLagrangeList::<F>::from(&poly_a),
            LinearLagrangeList::<F>::from(&poly_b),
        ];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<F>::prove::<G, _>(
            &mut prover_state,
            &combine_fn,
            &mut prover_transcript,
        );

        let mut prover_state_dup: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let proof_dup: SumcheckProof<F> = IPForMLSumcheck::<F>::prove_product::<G>(
            &mut prover_state_dup,
            &mut prover_transcript_dup,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let result_dup =
            IPForMLSumcheck::verify::<G>(claimed_sum, &proof_dup, &mut verifier_transcript_dup);
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_r1cs_sumcheck() {
        // Define the combine function for r1cs: (a * b * e) - (c * e) = 0
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 4);
            data[0] * data[1] * data[3] - data[2] * data[3]
        }

        // Take four simple polynomial
        let mut rng = test_rng();
        const NV: usize = 10;
        let poly_a: DenseMultilinearExtension<F> = DenseMultilinearExtension::rand(NV, &mut rng);
        let poly_b: DenseMultilinearExtension<F> = DenseMultilinearExtension::rand(NV, &mut rng);
        let poly_c: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(
            NV,
            poly_a
                .evaluations
                .iter()
                .zip(poly_b.evaluations.iter())
                .map(|(a, b)| a * b)
                .collect(),
        );
        let poly_e: DenseMultilinearExtension<F> = DenseMultilinearExtension::rand(NV, &mut rng);
        let claimed_sum: F = F::zero();

        let polynomials: Vec<LinearLagrangeList<F>> = vec![
            LinearLagrangeList::<F>::from(&poly_a),
            LinearLagrangeList::<F>::from(&poly_b),
            LinearLagrangeList::<F>::from(&poly_c),
            LinearLagrangeList::<F>::from(&poly_e),
        ];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 3);
        let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<F>::prove::<G, _>(
            &mut prover_state,
            &combine_fn,
            &mut prover_transcript,
        );

        let mut verifier_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let result = IPForMLSumcheck::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_r1cs_sumcheck_diagnostic() {
        // Define the combine function for r1cs: (a * b * e) - (c * e) = 0
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 4);
            data[0] * data[1] * data[3] - data[2] * data[3]
        }

        // Take four simple polynomial
        let mut rng = test_rng();
        const NV: usize = 3;
        let poly_a: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(3, vec![F::from(1),F::from(2),F::from(3),F::from(4),F::from(5),F::from(6),F::from(7),F::from(8)]);
        let poly_b: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(3, vec![F::from(11),F::from(12),F::from(13),F::from(14),F::from(15),F::from(16),F::from(17),F::from(18)]);
        let poly_c: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(3, vec![F::from(21),F::from(22),F::from(23),F::from(24),F::from(25),F::from(26),F::from(27),F::from(28)]);
        let poly_e: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(3, vec![F::from(2),F::from(10),F::from(1),F::from(6),F::from(9),F::from(3),F::from(8),F::from(7)]);
        println!("Poly A {:?}",poly_a.evaluations);
        println!("Poly B {:?}",poly_b.evaluations);
        println!("Poly C {:?}",poly_c.evaluations);
        println!("Poly Eq {:?}",poly_e.evaluations);

        //calculate sum
        let sum_c: DenseMultilinearExtension<F> = DenseMultilinearExtension::from_evaluations_vec(
            NV,
            poly_a
                .evaluations
                .iter()
                .zip(poly_b.evaluations.iter())
                .zip(poly_c.evaluations.iter())
                .zip(poly_e.evaluations.iter())
                .map(|(((a, b), c), e)| a * b * e - c * e)
                .collect(),
        );
        let claimed_sum =sum_c.evaluations.iter().fold(F::zero(), |acc, &a| acc + a);
        println!("claimed sum {:?}",claimed_sum);

        assert_eq!(claimed_sum,F::from(2416));
        let polynomials: Vec<LinearLagrangeList<F>> = vec![
            LinearLagrangeList::<F>::from(&poly_a),
            LinearLagrangeList::<F>::from(&poly_b),
            LinearLagrangeList::<F>::from(&poly_c),
            LinearLagrangeList::<F>::from(&poly_e),
        ];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 3);
        let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let diagnostic_proof: SumcheckProof<F> = IPForMLSumcheck::<F>::diagnostic_prove::<G, _>(
            &mut prover_state,
            &combine_fn,
            &mut prover_transcript,
        );

        // let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");
        // let proof: SumcheckProof<F> = IPForMLSumcheck::<F>::prove::<G, _>(
        //     &mut prover_state,
        //     &combine_fn,
        //     &mut prover_transcript,
        // );
        let mut verifier_transcript = Transcript::new(b"test_r1cs_sumcheck");
        // let result = IPForMLSumcheck::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
       let diagnostic_result = IPForMLSumcheck::diagnostic_verify::<G>(claimed_sum, &diagnostic_proof,&mut verifier_transcript);
       assert_eq!(diagnostic_result.unwrap(),true)
       // assert_eq!(result.unwrap(), true);
    }
}

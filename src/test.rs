#[cfg(test)]
mod integration_tests {
    use crate::data_structures::LinearLagrangeList;
    use crate::prover::AlgorithmType;
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
    type BF = ark_bls12_381::Fr;
    type EF = ark_bls12_381::Fr;
    type G = ark_bls12_381::G1Projective;

    #[test]
    fn test_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            data[0]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            *base_field_element
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(extension_field_element: &EF, base_field_element: &BF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Take a simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let claimed_sum = evaluations.iter().fold(F::zero(), |acc, e| acc + e);
        let poly = DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations);

        let polynomials: Vec<LinearLagrangeList<F>> = vec![LinearLagrangeList::<F>::from(&poly)];
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 1, AlgorithmType::Naive);

        // create a proof
        let mut prover_transcript = Transcript::new(b"test_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove::<G, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn,
            &combine_fn,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
        );

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result =
            IPForMLSumcheck::<EF, BF>::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            *base_field_element
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(extension_field_element: &EF, base_field_element: &BF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
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
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove::<G, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn,
            &combine_fn,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let proof_dup: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove_product::<G, _>(
            &mut prover_state_dup,
            &mut prover_transcript_dup,
            &mult_be,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result =
            IPForMLSumcheck::<EF, BF>::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify::<G>(
            claimed_sum,
            &proof_dup,
            &mut verifier_transcript_dup,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_2() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            *base_field_element
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(extension_field_element: &EF, base_field_element: &BF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
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
        let mut prover_state: ProverState<EF, BF> = IPForMLSumcheck::prover_init(
            &polynomials,
            2,
            AlgorithmType::WitnessChallengeSeparation,
        );
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove::<G, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn,
            &combine_fn,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove_product::<G, _>(
            &mut prover_state_dup,
            &mut prover_transcript_dup,
            &mult_be,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result =
            IPForMLSumcheck::<EF, BF>::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify::<G>(
            claimed_sum,
            &proof_dup,
            &mut verifier_transcript_dup,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_r1cs_sumcheck() {
        // Define the combine function for r1cs: (a * b * e) - (c * e) = 0
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 4);
            data[0] * data[1] * data[3] - data[2] * data[3]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            *base_field_element
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(extension_field_element: &EF, base_field_element: &BF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
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
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::<EF, BF>::prover_init(&polynomials, 3, AlgorithmType::Naive);
        let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let proof: SumcheckProof<F> = IPForMLSumcheck::<EF, BF>::prove::<G, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn,
            &combine_fn,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
        );

        let mut verifier_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let result =
            IPForMLSumcheck::<EF, BF>::verify::<G>(claimed_sum, &proof, &mut verifier_transcript);
        assert_eq!(result.unwrap(), true);
    }
}

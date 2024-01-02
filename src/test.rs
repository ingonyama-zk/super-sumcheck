#[cfg(test)]
mod integration_tests {
    use crate::data_structures::linear_lagrange_list;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::IPForMLSumcheck;
    use ark_ff::BigInt;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;

    type F = ark_bls12_381::Fr;

    #[test]
    fn test_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            data[0]
        }

        // Define the hash function for testing
        fn hash_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            data.iter().sum::<F>() / F::from(8)
        }
        // Take a simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let claimed_sum = evaluations.iter().fold(F::zero(), |acc, e| acc + e);
        let poly = DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations);

        let polynomials: Vec<linear_lagrange_list<F>> =
            vec![linear_lagrange_list::<F>::from(&poly)];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 1);
        let proof: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove(&mut prover_state, &combine_fn, &hash_fn);

        let result = IPForMLSumcheck::verify(claimed_sum, &proof, &hash_fn);
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Define the hash function for testing
        fn hash_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            data.iter().sum::<F>()
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

        let polynomials: Vec<linear_lagrange_list<F>> = vec![
            linear_lagrange_list::<F>::from(&poly_a),
            linear_lagrange_list::<F>::from(&poly_b),
        ];
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let proof: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove(&mut prover_state, &combine_fn, &hash_fn);

        let mut prover_state_dup: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let proof_dup: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove_product(&mut prover_state_dup, &hash_fn);

        let result = IPForMLSumcheck::verify(claimed_sum, &proof, &hash_fn);
        assert_eq!(result.unwrap(), true);

        let result_dup = IPForMLSumcheck::verify(claimed_sum, &proof_dup, &hash_fn);
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_simple_product_sumcheck() {
        // Define the combine function
        fn combine_fn(data: &Vec<F>) -> F {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Define the hash function for testing
        fn hash_fn(data: &Vec<F>) -> F {
            assert!(data.len() > 0);
            let sum = data.iter().sum::<F>();
            let sum_bytes = BigInt::from(sum).0[0];
            F::from(sum_bytes / 2)
        }

        // Take two simple polynomial
        let num_variables = 2;
        let evaluations_a: Vec<F> = vec![F::from(2), F::from(3), F::from(4), F::from(1)];
        let evaluations_b: Vec<F> = vec![F::from(1), F::from(4), F::from(2), F::from(5)];
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(F::zero(), |acc, (a, b)| acc + a * b);
        let poly_a =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_b);

        let polynomials: Vec<linear_lagrange_list<F>> = vec![
            linear_lagrange_list::<F>::from(&poly_a),
            linear_lagrange_list::<F>::from(&poly_b),
        ];

        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let proof: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove(&mut prover_state, &combine_fn, &hash_fn);

        let mut prover_state_dup: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 2);
        let proof_dup: SumcheckProof<F> =
            IPForMLSumcheck::<F>::prove_product(&mut prover_state_dup, &hash_fn);

        let result = IPForMLSumcheck::verify(claimed_sum, &proof, &hash_fn);
        assert_eq!(result.unwrap(), true);

        let result_dup = IPForMLSumcheck::verify(claimed_sum, &proof_dup, &hash_fn);
        assert_eq!(result_dup.unwrap(), true);
    }
}

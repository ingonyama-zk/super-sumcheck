use criterion::{criterion_group, criterion_main, Criterion};
use mle_single_poly::*;
use mle_single_poly::{data_structures::*,prover::*};
use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_std::test_rng;
use ark_std::vec::Vec;
use merlin::Transcript;

type F = ark_bn254::Fr;
type G = ark_bn254::G1Projective;


const NV: usize = 22;

pub fn bench_sumcheck(c:&mut Criterion){
    let mut group = c.benchmark_group("Sumcheck_bench");
    fn combine_fn(data: &Vec<F>) -> F {
        assert!(data.len() == 4);
        data[0] * data[1] * data[3] - data[2] * data[3]
    }

    // Take four simple polynomial
    let mut rng = test_rng();
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

group.bench_function("sumcheck_prover", |b |b.iter(
    ||{
        let mut prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, 3);
        let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");    
        let _proof: SumcheckProof<F> = IPForMLSumcheck::<F>::prove::<G, _>(
            &mut prover_state,
            &combine_fn,
            &mut prover_transcript,
        );
    }));
}

criterion_group!(benches,bench_sumcheck);
criterion_main!(benches);
#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate mle_single_poly;

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::test_rng;
use criterion::{black_box, BatchSize, BenchmarkId, Criterion};
use merlin::Transcript;
use mle_single_poly::data_structures::LinearLagrangeList;
use mle_single_poly::prover::ProverState;
use mle_single_poly::IPForMLSumcheck;
use rand::Rng;
use std::ops::Range;

const NUM_VARIABLES_RANGE: Range<usize> = 10..28;

// Define the combine function for a product of values.
fn combine_fn<F: PrimeField>(data: &Vec<F>) -> F {
    data.iter().fold(F::one(), |prod, di| prod * di)
}

// Create a randomised prover state ready to create a sumcheck proof.
fn create_random_prover_state<R: Rng, F: PrimeField>(
    nv: usize,
    num_of_products: usize,
    rng: &mut R,
) -> (ProverState<F>, Transcript) {
    // Sample random polynomials and create a prover state
    let polynomials = (0..num_of_products)
        .map(|_| LinearLagrangeList::<F>::rand(nv, rng))
        .collect();

    // Create a prover state and a transcript
    let prover_state: ProverState<F> = IPForMLSumcheck::prover_init(&polynomials, num_of_products);
    let prover_transcript = Transcript::new(b"bench_product_sumcheck");

    (prover_state, prover_transcript)
}

fn prove_naive_algorithm_bench<F: PrimeField, G: CurveGroup>(
    c: &mut Criterion,
    num_of_products: usize,
) where
    G: CurveGroup<ScalarField = F>,
{
    let mut rng = test_rng();

    let mut group = c.benchmark_group("Prove");
    for nv in NUM_VARIABLES_RANGE {
        group.significance_level(0.05).sample_size(10);
        group.bench_function(BenchmarkId::new("NaiveSumcheck", nv), |b| {
            b.iter_batched_ref(
                || -> (ProverState<F>, Transcript) {
                    create_random_prover_state(nv, num_of_products, &mut rng)
                },
                |prover_input| {
                    IPForMLSumcheck::prove::<G, _>(
                        black_box(&mut prover_input.0),
                        &combine_fn,
                        &mut prover_input.1,
                    )
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

fn bench_bls_381(c: &mut Criterion) {
    type F = ark_bls12_381::Fr;
    type G = ark_bls12_381::G1Projective;
    prove_naive_algorithm_bench::<F, G>(c, 1);
}

criterion_group!(benches, bench_bls_381);
criterion_main!(benches);

# `super-sumcheck`: Parallelising Sumcheck Prover

Super-sumcheck is aimed at exploring algorithmic improvements to the sumcheck prover to run it in a fully parallelisable and memory-efficient manner. We implement two algorithms for running sumcheck prover for arbitrary statements in MLE polynomials (read the full description [here](<[Precomputations](https://github.com/ingonyama-zk/papers/blob/main/sumcheck_201_chapter_1.pdf)>)):

- Algorithm 1: Collapsing arrays
- Algorithm 2: Precomputations

### Highlights

`super-sumcheck` enables running sumcheck prover for any "gate" equation in MLE polynomials and hence provides a proof-system and arithmetisation agnostic sumcheck prover backend. The two algorithms fall in different ends of the performance spectrum, algorithm 1 is less-memory intensive but consumes more computation cycles, algorithm 2 is memory intensive but allows offloading lot of work to pre-computation.

### Roadmap

This is being actively developed and is not yet ready for production. We intend to follow the following roadmap to take this project ahead:

- [x] Reference implementation of the sumcheck prover with:
  - [x] Algorithm 1: Collapsing arrays
  - [x] Algorithm 2: Precomputations
- [x] Use [merlin](https://lib.rs/crates/merlin) library for computing challenges as per the Fiat-Shamir heuristic
- [ ] Multi-threading in both algorithms
- [ ] Benchmark the two algorithms and analyse space-time trade-offs in them
- [ ] Benchmark this implementation against other sumcheck implementations
- [ ] Implement a commitment scheme for MLE polynomials for final verifier evaluation check

### Example

WIP

### License

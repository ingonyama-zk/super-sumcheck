mod data_structures;
mod prover;
mod test;
mod transcript;
mod verifier;

use ark_ff::PrimeField;
use ark_std::marker::PhantomData;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<BF: PrimeField, SF: PrimeField> {
    #[doc(hidden)]
    _marker: PhantomData<BF>,
    _other_marker: PhantomData<SF>,
}

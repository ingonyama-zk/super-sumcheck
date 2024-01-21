//! Transcript for the MLE sumcheck

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;

pub trait TranscriptProtocol<G: CurveGroup> {
    /// Append a domain separator for sumcheck proof of with `num_vars` variables and degree `m` of combine function.
    fn sumcheck_proof_domain_sep(&mut self, num_vars: u64, m: u64);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &G::ScalarField);

    /// Append multiple `scalars` with the given `label`.
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[G::ScalarField]);

    /// Append a `point` with the given `label`.
    fn append_point(&mut self, label: &'static [u8], point: &G);

    /// Append multiple `points` with the given `label`.
    fn append_points(&mut self, label: &'static [u8], points: &[G]);

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField;

    /// Compute a `label`ed vector of challenges.
    fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<G::ScalarField>;
}

impl<G: CurveGroup> TranscriptProtocol<G> for Transcript {
    fn sumcheck_proof_domain_sep(&mut self, num_vars: u64, m: u64) {
        self.append_message(b"domain-separator", b"sumcheck v1");
        self.append_u64(b"n", num_vars);
        self.append_u64(b"m", m);
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &G::ScalarField) {
        let mut buf = vec![];
        scalar.serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }

    fn append_scalars(&mut self, label: &'static [u8], scalars: &[G::ScalarField]) {
        self.append_message(label, b"begin_append_vector");
        for item in scalars.iter() {
            <Self as TranscriptProtocol<G>>::append_scalar(self, label, item);
        }
        self.append_message(label, b"end_append_vector");
    }

    fn append_point(&mut self, label: &'static [u8], point: &G) {
        let mut buf = vec![];
        point.serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }

    fn append_points(&mut self, label: &'static [u8], points: &[G]) {
        self.append_message(label, b"begin_append_vector");
        for item in points.iter() {
            self.append_point(label, item);
        }
        self.append_message(label, b"end_append_vector");
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> G::ScalarField {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        G::ScalarField::from_le_bytes_mod_order(&buf)
    }

    fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<G::ScalarField> {
        (0..len)
            .map(|_i| <Self as TranscriptProtocol<G>>::challenge_scalar(self, label))
            .collect::<Vec<G::ScalarField>>()
    }
}

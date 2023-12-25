use ark_std::{fmt, fmt::Formatter};

use ark_ff::{Field, PrimeField};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};

///this struct is supposed to represent a polynomial in the canonical form
/// r_i(X)=f_{2i}(1-X)+ f_{2i+1} X. Where f_i are coefficients of the MLE of some polynomial f.
/// So F(0)= linear_lagrange.even , F(1)= linear_lagrange.odd
#[derive(Clone, PartialEq, Eq)]
pub struct linear_lagrange<F: Field> {
    pub even: F,
    pub odd: F,
}

#[derive(Clone, PartialEq, Eq)]
/// this struct is supposed to handle the verifier transcript, with all the round polys
pub struct linear_lagrange_list<F: Field> {
    pub size: usize,
    pub list: Vec<linear_lagrange<F>>,
}

impl<F: Field> linear_lagrange<F> {
    ///define a new linear_lagrange instance: f_{2i}(1-X)+f_{2i+1}X as
    /// [odd,even]\equiv [f_{2i},f_{2i+1}]
    pub fn new(even: &F, odd: &F) -> linear_lagrange<F> {
        linear_lagrange {
            even: *even,
            odd: *odd,
        }
    }
    /// Adds 2 linear_lagrange instances and outputs a resulting linear_lagrange instance.
    /// this is for instance the atomic operation in each step, and this should be parallelized
    /// per pair of instances.
    pub fn linear_lagrange_add(&self, other: &linear_lagrange<F>) -> linear_lagrange<F> {
        linear_lagrange {
            even: self.even + other.even,
            odd: self.odd + other.odd,
        }
    }
    /// Subtracts 2 linear_lagrange instances and outputs a new linear_lagrange instance
    pub fn linear_lagrange_sub(&self, other: &linear_lagrange<F>) -> linear_lagrange<F> {
        let even_result: F = self.even - other.even;
        let odd_result: F = self.odd - other.odd;
        linear_lagrange {
            even: even_result,
            odd: odd_result,
        }
    }
    /// Given a linear_lagrange instance [even,odd] and a challenge alpha, computes [even*(1-alpha), odd*alpha]
    pub fn linear_lagrange_mul_challenge(&mut self, alpha: F) -> linear_lagrange<F> {
        linear_lagrange {
            even: self.even.mul(F::ONE - alpha),
            odd: self.odd.mul(alpha),
        }
    }
    /// this should consume the self and output a F
    pub fn linear_lagrange_mul_challenge_and_add(&self, alpha: F) -> F {
        self.even.mul(F::ONE - alpha) + self.odd.mul(alpha)
    }
}

impl<F: Field> linear_lagrange_list<F> {
    /// Create a new list from evaluations of a dense MLE polynomial
    pub fn from(polynomial: &DenseMultilinearExtension<F>) -> linear_lagrange_list<F> {
        let list_size = polynomial.evaluations.len() / 2;
        let poly_list = (0..list_size)
            .map(|i| {
                linear_lagrange::new(
                    &polynomial.evaluations[i],
                    &polynomial.evaluations[i + list_size],
                )
            })
            .collect::<Vec<linear_lagrange<F>>>();
        linear_lagrange_list {
            size: list_size,
            list: poly_list,
        }
    }

    ///Create a new initialized list (create with vectors specified)
    pub fn new(list_size: &usize, poly_list: &Vec<linear_lagrange<F>>) -> linear_lagrange_list<F> {
        linear_lagrange_list {
            size: *list_size,
            list: poly_list.to_vec(),
        }
    }
    ///Create a new un-initialized list (create with zero vectors)    
    pub fn new_uninitialized(size: &usize) -> linear_lagrange_list<F> {
        let vec = linear_lagrange::new(&F::zero(), &F::zero());
        linear_lagrange_list {
            size: *size,
            list: vec![vec; *size],
        }
    }
    ///this function is for the round poly in the transcript for the verifier
    pub fn list_accumulator(self: &mut linear_lagrange_list<F>) -> linear_lagrange<F> {
        let mut acc: linear_lagrange<F> = linear_lagrange::new(&F::zero(), &F::zero());
        for i in 0..=self.size - 1 {
            acc = acc.linear_lagrange_add(&self.list[i]);
        }
        acc
    }

    pub fn fold_in_half(self: &mut linear_lagrange_list<F>, challenge: F) {
        assert_ne!(self.size, 0);
        for linear_lagrange_instance in &mut self.list {
            linear_lagrange_instance.even *= F::one() - challenge;
            linear_lagrange_instance.odd *= challenge;
            linear_lagrange_instance.even += linear_lagrange_instance.odd;
        }

        for i in 0..(self.size / 2) {
            self.list[i].odd = self.list[i + self.size / 2].even;
        }
        self.size /= 2;
        self.list.truncate(self.size);
    }

    // takes a structure and generates a structure half the size (to add conditions)
    pub fn fold_list(input: linear_lagrange_list<F>, challenge: F) -> linear_lagrange_list<F> {
        assert_ne!(input.size, 0);
        let mut poly_list: Vec<linear_lagrange<F>> = Vec::new();
        let abc = &input.list[0];
        for i in (0..=input.size - 1).step_by(2) {
            poly_list.push(linear_lagrange {
                even: linear_lagrange::linear_lagrange_mul_challenge_and_add(
                    &input.list[i],
                    challenge,
                ),
                odd: linear_lagrange::linear_lagrange_mul_challenge_and_add(
                    &input.list[i + 1],
                    challenge,
                ),
            });
        }
        linear_lagrange_list {
            size: poly_list.len(),
            list: poly_list,
        }
    }
}

impl<F: Field> fmt::Debug for linear_lagrange<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "LinearLagrange(even = {}, odd = {})",
            self.even, self.odd
        )?;
        Ok(())
    }
}

impl<F: Field> fmt::Debug for linear_lagrange_list<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "LinearLagrangeList(size = {}, list = [", self.size)?;
        for i in 0..self.list.len() {
            write!(f, "({}, {}) ", self.list[i].even, self.list[i].odd)?;
        }
        write!(f, "])")?;
        Ok(())
    }
}

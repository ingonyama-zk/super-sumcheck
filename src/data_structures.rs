use ark_std::{fmt, fmt::Formatter};

use ark_ff::Field;
use ark_poly::DenseMultilinearExtension;

/// Represents a pair of values (p(0), p(1)) where p(.) is a linear univariate polynomial of the form:
/// p(X) = p(0).(1 - X) + p(1).X
/// where X is any field element. So we have:
/// p(0) = `linear_lagrange.even`, p(1) = `linear_lagrange.odd`
#[derive(Clone, PartialEq, Eq)]
pub struct linear_lagrange<F: Field> {
    pub even: F,
    pub odd: F,
}

#[derive(Clone, PartialEq, Eq)]
/// Represents pairs of values (p(i), p(n/2 + i)) where p(.) multi-linear polynomial of the form: \newline
/// p(X_1, X_2, ..., X_m) = p(0).(1-X_1)(1-X_2)...(1-X_m) + p(1).(1-X_1)(1-X_2)...(X_m) + ...
/// where X_i can be any field elements. We pair values according to the first variable, i.e.
/// X_1 = 0 ==> p(i)
/// X_1 = 1 ==> p(n/2 + i)
/// This is particularly useful while working with sumcheck round computations.
pub struct linear_lagrange_list<F: Field> {
    pub size: usize,
    pub list: Vec<linear_lagrange<F>>,
}

impl<F: Field> linear_lagrange<F> {
    /// Define a new linear_lagrange instance: p(0).(1-X) + p(1).X as
    /// $`[e, o] \equiv [p(0), p(1)]`$
    pub fn new(even: &F, odd: &F) -> linear_lagrange<F> {
        linear_lagrange {
            even: *even,
            odd: *odd,
        }
    }
    /// Adds 2 linear_lagrange instances and outputs a resulting linear_lagrange instance.
    /// this is for instance the atomic operation in each step, and this should be parallelized
    /// per pair of instances.
    pub fn add(&self, other: &linear_lagrange<F>) -> linear_lagrange<F> {
        linear_lagrange {
            even: self.even + other.even,
            odd: self.odd + other.odd,
        }
    }

    /// Subtracts 2 linear_lagrange instances and outputs a new linear_lagrange instance
    pub fn sub(&self, other: &linear_lagrange<F>) -> linear_lagrange<F> {
        let even_result: F = self.even - other.even;
        let odd_result: F = self.odd - other.odd;
        linear_lagrange {
            even: even_result,
            odd: odd_result,
        }
    }

    /// Evaluates the linear polynomial at alpha and returns $`p(0) * (1 - \alpha) + p(1) * \alpha`$
    pub fn evaluate_at(&self, alpha: F) -> F {
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

    /// Create a new initialized list (create with vectors specified)
    pub fn new(list_size: &usize, poly_list: &Vec<linear_lagrange<F>>) -> linear_lagrange_list<F> {
        linear_lagrange_list {
            size: *list_size,
            list: poly_list.to_vec(),
        }
    }
    /// Create a new un-initialized list (create with zero vectors)    
    pub fn new_uninitialized(size: &usize) -> linear_lagrange_list<F> {
        let vec = linear_lagrange::new(&F::zero(), &F::zero());
        linear_lagrange_list {
            size: *size,
            list: vec![vec; *size],
        }
    }
    /// Accumulates the even and odd parts in a list
    pub fn list_accumulator(self: &linear_lagrange_list<F>) -> linear_lagrange<F> {
        let mut acc: linear_lagrange<F> = linear_lagrange::new(&F::zero(), &F::zero());
        for i in 0..=self.size - 1 {
            acc = acc.add(&self.list[i]);
        }
        acc
    }

    /// Folds a linear lagrange list in half according to the sumcheck protocol
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

    // Takes a structure and generates a new structure half the size (to add conditions)
    pub fn fold_list(input: &linear_lagrange_list<F>, challenge: F) -> linear_lagrange_list<F> {
        assert_ne!(input.size, 0);
        let mut poly_list: Vec<linear_lagrange<F>> = Vec::new();
        for i in (0..=input.size - 1).step_by(2) {
            poly_list.push(linear_lagrange {
                even: linear_lagrange::evaluate_at(&input.list[i], challenge),
                odd: linear_lagrange::evaluate_at(&input.list[i + 1], challenge),
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

#[cfg(test)]
mod test {
    use crate::data_structures::{linear_lagrange, linear_lagrange_list};
    use ark_bls12_381::Fr as F;
    use ark_ff::{Field, Zero};
    use rand::Rng;

    pub fn random_field_element<F: Field>() -> F {
        let mut rng = rand::thread_rng();
        let random_u128: u128 = rng.gen();
        F::from(random_u128)
    }

    pub fn get_random_linear_lagrange<F: Field>() -> linear_lagrange<F> {
        linear_lagrange::new(&random_field_element(), &random_field_element())
    }

    #[test]
    fn test_linear_lagrange_add() {
        let r1: linear_lagrange<F> = get_random_linear_lagrange();
        let r2: linear_lagrange<F> = get_random_linear_lagrange();
        let addition = r1.add(&r2);
        assert_eq!(r1.odd + r2.odd, addition.odd);
        assert_eq!(r1.even + r2.even, addition.even);
    }

    #[test]
    fn test_linear_lagrange_sub() {
        let r1: linear_lagrange<F> = get_random_linear_lagrange();
        let r2: linear_lagrange<F> = get_random_linear_lagrange();
        let subtraction = r1.sub(&r2);
        assert_eq!(r1.odd - r2.odd, subtraction.odd);
        assert_eq!(r1.even - r2.even, subtraction.even);
    }

    #[test]
    fn test_linear_lagrange_accumulate() {
        let list_size = 10;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<linear_lagrange<F>>>();
        let lagrange_list: linear_lagrange_list<F> =
            linear_lagrange_list::new(&list_size, &linear_lagrange_vec);
        let accumulated = linear_lagrange_list::list_accumulator(&lagrange_list);

        let expected_even_sum = linear_lagrange_vec
            .iter()
            .fold(F::zero(), |sum, ll_instance| sum + ll_instance.even);

        let expected_odd_sum = linear_lagrange_vec
            .iter()
            .fold(F::zero(), |sum, ll_instance| sum + ll_instance.odd);

        assert_eq!(accumulated.even, expected_even_sum);
        assert_eq!(accumulated.odd, expected_odd_sum);
    }

    #[test]
    fn test_fold_list() {
        let list_size = 8;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<linear_lagrange<F>>>();
        let lagrange_list: linear_lagrange_list<F> =
            linear_lagrange_list::new(&list_size, &linear_lagrange_vec);

        let alpha: F = random_field_element();
        let folded_list = linear_lagrange_list::fold_list(&lagrange_list, alpha);

        for i in (0..lagrange_list.size).step_by(2) {
            let expected_even = lagrange_list.list[i].evaluate_at(alpha);
            let expected_odd = lagrange_list.list[i + 1].evaluate_at(alpha);
            assert_eq!(folded_list.list[i / 2].even, expected_even);
            assert_eq!(folded_list.list[i / 2].odd, expected_odd);
        }
    }

    #[test]
    fn test_fold_in_half() {
        let list_size = 8;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<linear_lagrange<F>>>();
        let mut lagrange_list: linear_lagrange_list<F> =
            linear_lagrange_list::new(&list_size, &linear_lagrange_vec);
        let size_before = lagrange_list.size;

        let alpha: F = random_field_element();
        lagrange_list.fold_in_half(alpha);
        let size_after = lagrange_list.size;
        assert_eq!(2 * size_after, size_before);

        for i in 0..lagrange_list.size {
            let expected_even =
                (F::ONE - alpha) * linear_lagrange_vec[i].even + alpha * linear_lagrange_vec[i].odd;
            let expected_odd = (F::ONE - alpha) * linear_lagrange_vec[size_after + i].even
                + alpha * linear_lagrange_vec[size_after + i].odd;

            assert_eq!(lagrange_list.list[i].even, expected_even);
            assert_eq!(lagrange_list.list[i].odd, expected_odd);
        }
    }
}

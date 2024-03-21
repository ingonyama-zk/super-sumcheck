use std::vec;

use ark_std::{fmt, fmt::Formatter, iterable::Iterable};

use ark_ff::Field;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use rand::Rng;

/// Represents a pair of values (p(0), p(1)) where p(.) is a linear univariate polynomial of the form:
/// p(X) = p(0).(1 - X) + p(1).X
/// where X is any field element. So we have:
/// p(0) = `LinearLagrange.even`, p(1) = `LinearLagrange.odd`
#[derive(Clone, PartialEq, Eq)]
pub struct LinearLagrange<F: Field> {
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
pub struct LinearLagrangeList<F: Field> {
    pub size: usize,
    pub list: Vec<LinearLagrange<F>>,
}

impl<F: Field> LinearLagrange<F> {
    /// Define a new LinearLagrange instance: p(0).(1-X) + p(1).X as
    /// $`[e, o] \equiv [p(0), p(1)]`$
    pub fn new(even: &F, odd: &F) -> LinearLagrange<F> {
        LinearLagrange {
            even: *even,
            odd: *odd,
        }
    }
    /// Adds 2 LinearLagrange instances and outputs a resulting LinearLagrange instance.
    /// this is for instance the atomic operation in each step, and this should be parallelized
    /// per pair of instances.
    pub fn add(&self, other: &LinearLagrange<F>) -> LinearLagrange<F> {
        LinearLagrange {
            even: self.even + other.even,
            odd: self.odd + other.odd,
        }
    }

    /// Subtracts 2 LinearLagrange instances and outputs a new LinearLagrange instance
    pub fn sub(&self, other: &LinearLagrange<F>) -> LinearLagrange<F> {
        let even_result: F = self.even - other.even;
        let odd_result: F = self.odd - other.odd;
        LinearLagrange {
            even: even_result,
            odd: odd_result,
        }
    }

    /// Evaluates the linear polynomial at alpha and returns $`p(0) * (1 - \alpha) + p(1) * \alpha`$
    pub fn evaluate_at(&self, alpha: F) -> F {
        self.even.mul(F::ONE - alpha) + self.odd.mul(alpha)
    }
}

impl<F: Field> LinearLagrangeList<F> {
    /// Create a new list from evaluations of a dense MLE polynomial
    pub fn from(polynomial: &DenseMultilinearExtension<F>) -> LinearLagrangeList<F> {
        let list_size = polynomial.evaluations.len() / 2;
        let poly_list = (0..list_size)
            .map(|i| {
                LinearLagrange::new(
                    &polynomial.evaluations[i],
                    &polynomial.evaluations[i + list_size],
                )
            })
            .collect::<Vec<LinearLagrange<F>>>();
        LinearLagrangeList {
            size: list_size,
            list: poly_list,
        }
    }

    /// Create a new initialized list (create with vectors specified)
    pub fn new(list_size: &usize, poly_list: &Vec<LinearLagrange<F>>) -> LinearLagrangeList<F> {
        LinearLagrangeList {
            size: *list_size,
            list: poly_list.to_vec(),
        }
    }

    /// Create a random linear lagrange list
    pub fn rand<R: Rng>(nv: usize, rng: &mut R) -> Self {
        let poly = DenseMultilinearExtension::<F>::rand(nv, rng);
        Self::from(&poly)
    }

    /// Create a new un-initialized list (create with zero vectors)    
    pub fn new_uninitialized(size: &usize) -> LinearLagrangeList<F> {
        let vec = LinearLagrange::new(&F::zero(), &F::zero());
        LinearLagrangeList {
            size: *size,
            list: vec![vec; *size],
        }
    }
    /// Accumulates the even and odd parts in a list
    pub fn list_accumulator(self: &LinearLagrangeList<F>) -> LinearLagrange<F> {
        let mut acc: LinearLagrange<F> = LinearLagrange::new(&F::zero(), &F::zero());
        for i in 0..=self.size - 1 {
            acc = acc.add(&self.list[i]);
        }
        acc
    }

    /// Folds a linear lagrange list in half according to the sumcheck protocol
    pub fn fold_in_half(self: &mut LinearLagrangeList<F>, challenge: F) {
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
    pub fn fold_list(input: &LinearLagrangeList<F>, challenge: F) -> LinearLagrangeList<F> {
        assert_ne!(input.size, 0);
        let mut poly_list: Vec<LinearLagrange<F>> = Vec::new();
        for i in (0..=input.size - 1).step_by(2) {
            poly_list.push(LinearLagrange {
                even: LinearLagrange::evaluate_at(&input.list[i], challenge),
                odd: LinearLagrange::evaluate_at(&input.list[i + 1], challenge),
            });
        }
        LinearLagrangeList {
            size: poly_list.len(),
            list: poly_list,
        }
    }
}

impl<F: Field> fmt::Debug for LinearLagrange<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "LinearLagrange(even = {}, odd = {})",
            self.even, self.odd
        )?;
        Ok(())
    }
}

impl<F: Field> fmt::Debug for LinearLagrangeList<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "LinearLagrangeList(size = {}, list = [", self.size)?;
        for i in 0..self.list.len() {
            write!(f, "({}, {}) ", self.list[i].even, self.list[i].odd)?;
        }
        write!(f, "])")?;
        Ok(())
    }
}

///
/// For sumcheck prover (algorithm 2), we need to represent polynomial evaluations in a matrix form.
///
#[derive(Clone, PartialEq, Eq)]
pub struct MatrixPolynomial<F: Field> {
    pub no_of_rows: usize,
    pub no_of_columns: usize,
    pub evaluation_rows: Vec<Vec<F>>,
}

impl<F: Field> MatrixPolynomial<F> {
    pub fn one() -> Self {
        MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: 1,
            evaluation_rows: vec![vec![F::ONE]],
        }
    }

    pub fn from_dense_mle(input_polynomial: &DenseMultilinearExtension<F>) -> Self {
        let n = input_polynomial.evaluations.len();
        let mid_point = n / 2;
        let (first_half, second_half) = input_polynomial.evaluations.split_at(mid_point);

        MatrixPolynomial {
            no_of_rows: 2,
            no_of_columns: mid_point,
            evaluation_rows: vec![first_half.to_vec(), second_half.to_vec()],
        }
    }

    pub fn from_linear_lagrange_list(input_polynomial: &LinearLagrangeList<F>) -> Self {
        let n_by_2 = input_polynomial.size;
        MatrixPolynomial {
            no_of_rows: 2,
            no_of_columns: n_by_2,
            evaluation_rows: vec![
                input_polynomial
                    .list
                    .iter()
                    .map(|ll_instance| ll_instance.even)
                    .collect(),
                input_polynomial
                    .list
                    .iter()
                    .map(|ll_instance| ll_instance.odd)
                    .collect(),
            ],
        }
    }

    pub fn heighten(&mut self) {
        // Update the dimensions of the original matrix
        self.no_of_rows *= 2;
        self.no_of_columns /= 2;
        let mid_point = self.no_of_columns;
        let end_point = mid_point * 2;

        for row_index in 0..(self.no_of_rows / 2) {
            let vector_to_add = self.evaluation_rows[2 * row_index][mid_point..end_point].to_vec();
            self.evaluation_rows
                .insert(2 * row_index + 1, vector_to_add);
            self.evaluation_rows[2 * row_index].truncate(mid_point);
        }
    }

    pub fn tensor_hadamard_product(&self, rhs: &MatrixPolynomial<F>) -> MatrixPolynomial<F> {
        assert_eq!(self.no_of_columns, rhs.no_of_columns);

        let mut output = MatrixPolynomial {
            no_of_rows: self.no_of_rows * rhs.no_of_rows,
            no_of_columns: self.no_of_columns,
            evaluation_rows: Vec::with_capacity(self.no_of_rows * rhs.no_of_rows),
        };

        for i in 0..self.no_of_rows {
            for j in 0..rhs.no_of_rows {
                let left_vec: &Vec<F> = &self.evaluation_rows[i];
                let right_vec: &Vec<F> = &rhs.evaluation_rows[j];
                let left_right_hadamard: Vec<F> = left_vec
                    .iter()
                    .zip(right_vec.iter())
                    .map(|(&l, &r)| l * r)
                    .collect();
                output.evaluation_rows.push(left_right_hadamard);
            }
        }
        output
    }

    pub fn collapse(&mut self) {
        if self.no_of_columns == 1 {
            return;
        } else {
            self.no_of_columns = 1;

            for i in 0..self.no_of_rows {
                let new_value: F = self.evaluation_rows[i]
                    .iter()
                    .fold(F::zero(), |sum, &r| sum + r);
                self.evaluation_rows[i] = vec![new_value];
            }
        }
    }

    pub fn dot_product(&self, rhs: &Self) -> F {
        assert_eq!(self.no_of_columns, rhs.no_of_columns);
        assert_eq!(self.no_of_rows, rhs.no_of_rows);

        self.evaluation_rows
            .iter()
            .zip(rhs.evaluation_rows.iter())
            .fold(F::zero(), |acc, (l_row, r_row)| {
                acc + l_row
                    .iter()
                    .zip(r_row.iter())
                    .fold(F::zero(), |sum, (&l_val, &r_val)| sum + l_val * r_val)
            })
    }
}

impl<F: Field> fmt::Debug for MatrixPolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "MatrixPolynomial(cols = {}, rows = {}, evaluations:\n",
            self.no_of_columns, self.no_of_rows
        )?;
        for i in 0..self.evaluation_rows.len() {
            write!(f, "[")?;
            for j in 0..self.evaluation_rows[0].len() {
                write!(f, "{} ", self.evaluation_rows[i][j])?;
            }
            write!(f, "]\n")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::data_structures::{LinearLagrange, LinearLagrangeList};
    use ark_bls12_381::Fr as F;
    use ark_ff::{Field, Zero};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use rand::Rng;

    use super::MatrixPolynomial;

    pub fn random_field_element<F: Field>() -> F {
        let mut rng = rand::thread_rng();
        let random_u128: u128 = rng.gen();
        F::from(random_u128)
    }

    pub fn get_random_linear_lagrange<F: Field>() -> LinearLagrange<F> {
        LinearLagrange::new(&random_field_element(), &random_field_element())
    }

    #[test]
    fn test_linear_lagrange_add() {
        let r1: LinearLagrange<F> = get_random_linear_lagrange();
        let r2: LinearLagrange<F> = get_random_linear_lagrange();
        let addition = r1.add(&r2);
        assert_eq!(r1.odd + r2.odd, addition.odd);
        assert_eq!(r1.even + r2.even, addition.even);
    }

    #[test]
    fn test_linear_lagrange_sub() {
        let r1: LinearLagrange<F> = get_random_linear_lagrange();
        let r2: LinearLagrange<F> = get_random_linear_lagrange();
        let subtraction = r1.sub(&r2);
        assert_eq!(r1.odd - r2.odd, subtraction.odd);
        assert_eq!(r1.even - r2.even, subtraction.even);
    }

    #[test]
    fn test_linear_lagrange_accumulate() {
        let list_size = 10;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<LinearLagrange<F>>>();
        let lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);
        let accumulated = LinearLagrangeList::list_accumulator(&lagrange_list);

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
            .collect::<Vec<LinearLagrange<F>>>();
        let lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);

        let alpha: F = random_field_element();
        let folded_list = LinearLagrangeList::fold_list(&lagrange_list, alpha);

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
            .collect::<Vec<LinearLagrange<F>>>();
        let mut lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);
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

    #[test]
    fn test_matrix_polynomial_heighten() {
        let mut rng = rand::thread_rng();
        let poly = DenseMultilinearExtension::<F>::rand(3, &mut rng);
        let mut matrix_poly = MatrixPolynomial::from_dense_mle(&poly);
        let mid_point = poly.evaluations.len() / 2;
        let end_point = poly.evaluations.len();

        assert_eq!(matrix_poly.no_of_rows, 2);
        assert_eq!(matrix_poly.no_of_columns, mid_point);
        assert_eq!(
            matrix_poly.evaluation_rows[0],
            poly.evaluations[0..mid_point]
        );
        assert_eq!(
            matrix_poly.evaluation_rows[1],
            poly.evaluations[mid_point..end_point]
        );

        // Test if heighten works as intended
        matrix_poly.heighten();
        assert_eq!(matrix_poly.evaluation_rows[0], poly.evaluations[0..2]);
        assert_eq!(matrix_poly.evaluation_rows[1], poly.evaluations[2..4]);
        assert_eq!(matrix_poly.evaluation_rows[2], poly.evaluations[4..6]);
        assert_eq!(matrix_poly.evaluation_rows[3], poly.evaluations[6..8]);
    }

    pub fn vector_hadamard(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b.iter()).map(|(ai, bi)| ai * bi).collect()
    }

    #[test]
    fn test_matrix_polynomial_tensor_hadamard() {
        let mut rng = rand::thread_rng();
        let poly_a = DenseMultilinearExtension::<F>::rand(3, &mut rng);
        let matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        let poly_b = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let mut matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);

        // Reduce number of columns of b by half
        matrix_poly_b.heighten();

        // Perform tensor-hadamard product of a and b
        let matrix_poly_c = matrix_poly_a.tensor_hadamard_product(&matrix_poly_b);

        assert_eq!(matrix_poly_b.no_of_columns, matrix_poly_a.no_of_columns);
        assert_eq!(matrix_poly_c.no_of_columns, matrix_poly_a.no_of_columns);
        assert_eq!(
            matrix_poly_c.no_of_rows,
            matrix_poly_a.no_of_rows * matrix_poly_b.no_of_rows
        );

        for i in 0..matrix_poly_b.no_of_rows {
            let a0_bi = vector_hadamard(
                &matrix_poly_a.evaluation_rows[0],
                &matrix_poly_b.evaluation_rows[i],
            );
            let a1_bi = vector_hadamard(
                &matrix_poly_a.evaluation_rows[1],
                &matrix_poly_b.evaluation_rows[i],
            );
            let offset = matrix_poly_b.no_of_rows;
            assert_eq!(matrix_poly_c.evaluation_rows[i], a0_bi);
            assert_eq!(matrix_poly_c.evaluation_rows[i + offset], a1_bi);
        }
    }

    #[test]
    fn test_matrix_polynomial_collapse() {
        let mut rng = rand::thread_rng();
        let poly = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let mut matrix_poly = MatrixPolynomial::from_dense_mle(&poly);

        // Reduce number of columns by half
        matrix_poly.heighten();

        // Apply collapse function
        matrix_poly.collapse();

        assert_eq!(matrix_poly.no_of_columns, 1);
        assert_eq!(matrix_poly.no_of_rows, 4);
        assert_eq!(
            matrix_poly.evaluation_rows[0][0],
            poly.evaluations[0..4]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[1][0],
            poly.evaluations[4..8]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[2][0],
            poly.evaluations[8..12]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[3][0],
            poly.evaluations[12..16]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
    }

    #[test]
    fn test_matrix_polynomial_dot_product() {
        let mut rng = rand::thread_rng();
        let poly_a = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        let poly_b = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);

        let computed = matrix_poly_a.dot_product(&matrix_poly_b);
        let expected = poly_a
            .evaluations
            .iter()
            .zip(poly_b.iter())
            .fold(F::zero(), |acc, (a, b)| acc + a * b);
        assert_eq!(computed, expected);
    }
}

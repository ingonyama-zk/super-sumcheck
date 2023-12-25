#[cfg(test)]
use crate::data_structures::{linear_lagrange, linear_lagrange_list};
use ark_bls12_381::Fr as F;
use ark_ff::{Field, One};
use blake2::digest::typenum::assert_type;
use rand::Rng;

pub fn random_field_element<F: Field>() -> F {
    let mut rng = rand::thread_rng();
    let random_u128: u128 = rng.gen();
    F::from(random_u128)
}

//sanity test
#[test]
fn test1() {
    let t1: F = random_field_element();
    let t2: F = random_field_element();
    assert_eq!((t1 + t2) * (t1 - t2), t1 * t1 - t2 * t2)
}

//linear_lagrange struct test
#[test]
fn linear_lagrange_test() {
    let r1: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let r2: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let add_linear_lagrange = linear_lagrange::linear_lagrange_add(&r1, &r2);
    let sub_linear_lagrange = linear_lagrange::linear_lagrange_sub(&r1, &r2);
    assert_eq!(r1.odd + r2.odd, add_linear_lagrange.odd);
    assert_eq!(r1.even + r2.even, add_linear_lagrange.even);
    assert_eq!(r1.odd - r2.odd, sub_linear_lagrange.odd);
    assert_eq!(r1.even - r2.even, sub_linear_lagrange.even);
    println!("linear_lagrange Addition tests ok");
    let mut r3 = r1.clone();
    let alpha = random_field_element();
    let mul_linear_lagrange = r3.linear_lagrange_mul_challenge(alpha);
    assert_eq!(r3.even * (F::one() - alpha), mul_linear_lagrange.even);
    assert_eq!(r3.odd * alpha, mul_linear_lagrange.odd);
    println!("linear_lagrange multiplication tests ok");
    let mut list_lagrange = linear_lagrange_list::new(&2, &vec![r1, r2]);
    let mut acc_result = linear_lagrange_list::list_accumulator(&mut list_lagrange);
    assert_eq!(acc_result.odd, add_linear_lagrange.odd);
    assert_eq!(acc_result.even, add_linear_lagrange.even);
    println!("linear_lagrange_list operations ok");
}

#[test]
fn folding_test() {
    let r1: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let r2: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let r3: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let r4: linear_lagrange<F> =
        linear_lagrange::new(&random_field_element(), &random_field_element());
    let alpha: F = random_field_element();
    //create stryctyre of size 4
    let round_poly0 =
        linear_lagrange_list::new(&4, &vec![r1.clone(), r2.clone(), r3.clone(), r4.clone()]);
    let fold_poly = linear_lagrange_list::fold_list(round_poly0, alpha);
    let r12fold: linear_lagrange<F> = linear_lagrange {
        even: linear_lagrange::linear_lagrange_mul_challenge_and_add(&r1, alpha),
        odd: linear_lagrange::linear_lagrange_mul_challenge_and_add(&r2, alpha),
    };
    let r34fold: linear_lagrange<F> = linear_lagrange {
        even: linear_lagrange::linear_lagrange_mul_challenge_and_add(&r3, alpha),
        odd: linear_lagrange::linear_lagrange_mul_challenge_and_add(&r4, alpha),
    };
    assert_eq!(fold_poly.size, 2);
    assert_eq!(fold_poly.list[0].even, r12fold.even);
    assert_eq!(fold_poly.list[0].odd, r12fold.odd);
    assert_eq!(fold_poly.list[1].even, r34fold.even);
    assert_eq!(fold_poly.list[1].odd, r34fold.odd);
}


use num_traits::*;
use std::ops::{Add, Mul, Div, Neg, Sub, AddAssign, SubAssign, MulAssign, DivAssign};
use alga::general::*;

use polynomial::EuclideanDomain;

pub fn mod_inverse(num: i64, prime: i64) -> i64 {
        let mut a = prime;
        let mut b = num;
        let mut x = 1;
        let mut y = 0;
        while b != 0 {
                let t = b;
                let q = a / t;
                b = a - q*t;
                a = t;
                let t = x;
                x = y - q*t;
                y = t;
        }
        if y < 0 {
            y + prime
        } else {
            y
        }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct ModPElt {
    pub p: u32,
    pub val: i64,
}

impl ModPElt {
    pub fn legendre_symbol(&self) -> i64 {
        self.pow((self.p - 1) / 2).val
    }
    
    // Sourced roughly from https://rosettacode.org/wiki/Tonelli-Shanks_algorithm#Python
    pub fn sqrt(&self) -> Option<ModPElt> {
        if self.legendre_symbol() != 1 {
            return None;
        }

        let mut q = self.p - 1;
        let mut s = 0;
        while q % 2 == 0 {
            q /= 2;
            s += 1;
        }
        if s == 1 {
            return Some(self.pow((self.p + 1) / 4));
        }
        let mut z = (self.p as i64) - 1;
        for z_ in 2..self.p {
            if self.p - 1 == (ModPElt { val: z_ as i64, p: self.p }).legendre_symbol() as u32 {
                z = z_ as i64;
                break;
            }
        }

        let mut c = ModPElt { val: z, p: self.p }.pow(q);
        let mut r = self.pow((q + 1) / 2);
        let mut t = self.pow(q);
        let mut m = s;
        let mut t2;

        while (t - One::one()) != Zero::zero() {
            t2 = t * t;
            let mut i = m - 1;
            for i_ in 1..m {
                if t2 - One::one() == Zero::zero() {
                    i = i_;
                    break;
                }
                t2 = t2 * t2;
            }
            let b = c.pow(1 << (m - i - 1));
            r = r * b;
            c = b * b;
            t = t * c;
            m = i;
        }
        Some(r)
    }
}

impl std::fmt::Display for ModPElt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl std::cmp::PartialEq for ModPElt {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

impl Eq for ModPElt {}

impl Add for ModPElt {
    type Output = ModPElt;

    fn add(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val + other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        // TODO: Maybe this should use checked_add
        ModPElt {
            p,
            val: (self.val + other.val).rem_euclid(p as i64)
        }
    }
}

impl AddAssign for ModPElt {
    fn add_assign(&mut self, other: ModPElt) {
        *self = *self + other;
    }
}

impl Sub for ModPElt {
    type Output = ModPElt;

    fn sub(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val - other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            p,
            val: (self.val - other.val).rem_euclid(p as i64)
        }
    }
}

impl SubAssign for ModPElt {
    fn sub_assign(&mut self, other: ModPElt) {
        *self = *self - other;
    }
}

impl Mul for ModPElt {
    type Output = ModPElt;

    fn mul(self, other: ModPElt) -> ModPElt {
        if self.p == 0 && other.p == 0 { 
            return ModPElt {
                p: 0,
                val: self.val * other.val,
            };
        }
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            p,
            val: (self.val * other.val).rem_euclid(p as i64)
        }
    }
}

impl MulAssign for ModPElt {
    fn mul_assign(&mut self, other: ModPElt) {
        *self = *self * other;
    }
}

impl Div for ModPElt {
    type Output = ModPElt;

    fn div(self, other: ModPElt) -> ModPElt {
        self * (<Self as TwoSidedInverse<Multiplicative>>::two_sided_inverse(&other))
    }
}

impl DivAssign for ModPElt {
    fn div_assign(&mut self, other: ModPElt) {
        *self = *self / other;
    }
}

impl Neg for ModPElt {
    type Output = ModPElt;

    fn neg(self) -> ModPElt {
        if self.p == 0 {
            return ModPElt {
                p: self.p,
                val: -self.val,
            };
        }
        ModPElt {
            p: self.p,
            val: (-self.val).rem_euclid(self.p as i64)
        }
    }
}

impl One for ModPElt {
    fn one() -> Self {
        ModPElt {
            p: 0,
            val: 1
        }
    }
}

impl Zero for ModPElt {
    fn is_zero(&self) -> bool {
        self.val == 0
    }

    fn zero() -> Self {
        ModPElt {
            p: 0,
            val: 0,
        }
    }
}

impl AbstractMagma<Additive> for ModPElt {
    fn operate(&self, right: &Self) -> Self {
        *self + *right
    }
}

impl Identity<Additive> for ModPElt {
    fn identity() -> Self {
        ModPElt {
            p: 0,
            val: 0,
        }
    }
}

impl TwoSidedInverse<Additive> for ModPElt {
    fn two_sided_inverse(&self) -> Self {
        -*self
    }
}

impl AbstractQuasigroup<Additive> for ModPElt {}
impl AbstractLoop<Additive> for ModPElt {}
impl AbstractSemigroup<Additive> for ModPElt {}
impl AbstractMonoid<Additive> for ModPElt {}
impl AbstractGroup<Additive> for ModPElt {}
impl AbstractGroupAbelian<Additive> for ModPElt {}

impl AbstractMagma<Multiplicative> for ModPElt {
    fn operate(&self, right: &Self) -> Self {
        *self * *right
    }
}

impl Identity<Multiplicative> for ModPElt {
    fn identity() -> Self {
        ModPElt {
            p: 0,
            val: 1,
        }
    }
}

impl TwoSidedInverse<Multiplicative> for ModPElt {
    fn two_sided_inverse(&self) -> Self {
        ModPElt {
            p: self.p,
            val: mod_inverse(self.val, self.p as i64),
        }
    }
}

impl AbstractQuasigroup<Multiplicative> for ModPElt {}
impl AbstractLoop<Multiplicative> for ModPElt {}
impl AbstractSemigroup<Multiplicative> for ModPElt {}
impl AbstractMonoid<Multiplicative> for ModPElt {}
impl AbstractGroup<Multiplicative> for ModPElt {}
impl AbstractGroupAbelian<Multiplicative> for ModPElt {}

impl AbstractRing<Additive, Multiplicative> for ModPElt {}
impl AbstractRingCommutative<Additive, Multiplicative> for ModPElt {}
impl AbstractField<Additive, Multiplicative> for ModPElt {}


// Hacky
impl EuclideanDomain for ModPElt {
    fn modulus(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            val: 0,
            p
        }
    }

    fn gcd(self, other: Self) -> Self {
        let p = if self.p == 0 { other.p } else { self.p };
        ModPElt {
            val: 1,
            p
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_misc_pow() {
        let val = ModPElt { val: 2, p: 1000000 };
        assert!(val.pow(4).val == 16);
    }

    #[test]
    fn test_fp_sqrt() {
        let mut ct = 0;
        for x in [1023, 32, 1003, 329, 643, 1, 2, 0].iter() {
            for p in [1591, 1513, 2345, 53252, 99199].iter() {
                let val = ModPElt { val: *x, p: *p };
                match val.sqrt() {
                    Some(val2) => {ct += 1; assert_eq!(val2 * val2, val)},
                    _ => {}
                }
            }
        }
    }
}

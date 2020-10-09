
use derive_more::*;

use num_traits::PrimInt;

// use derive_more::{PartialEq, Add, Sub, Neg, AddAssign, SubAssign};

use alga::general::{Ring, ClosedDiv};

pub trait EuclideanDomain: Ring + ClosedDiv {
    fn modulus(self, other: Self) -> Self;
    fn gcd(self, other: Self) -> Self;
    fn pow(mut self, mut power: u32) -> Self {
        // https://en.wikipedia.org/wiki/Exponentiation_by_squaring
        if power == 0 {
            return Self::one();
        }
        let mut y = Self::one();
        while power > 1 {
            if power & 1 == 0 {
                self = self.clone() * self.clone();
                power >>= 1;
            } else {
                y = self.clone() * y;
                self = self.clone() * self.clone();
                power = (power - 1) >> 1;
            }
        }
        self * y
    }
    // Optional: Helpful when displaying and debugging
    fn is_positive(&self) -> Option<bool> {
        None
    }
    fn is_negative(&self) -> Option<bool> {
        None
    }
}

impl<T: Ring + ClosedDiv + PrimInt> EuclideanDomain for T {
    fn modulus(self, other: Self) -> Self {
        self % other
    }

    fn gcd(mut self, mut b: Self) -> Self {
        if self < b {
            std::mem::swap(&mut self, &mut b);
        }
        while !b.is_zero() {
            self = self.modulus(b);
            std::mem::swap(&mut self, &mut b);
        }
        self
    }

    fn is_positive(&self) -> Option<bool> {
        Some(self > &Self::zero())
    }

    fn is_negative(&self) -> Option<bool> {
        Some(self < &Self::zero())
    }
}

pub fn gcd<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    a.gcd(b)
}

/// A general quadratic polynomial
/// ax^2 + bx + c
#[derive(Debug, Clone, Copy, PartialEq, Add, Sub, Neg, AddAssign, SubAssign)]
pub struct QuadPoly<Int: EuclideanDomain> {
    pub a: Int,
    pub b: Int,
    pub c: Int,
}

impl<Int: EuclideanDomain> QuadPoly<Int> {
    pub fn degree(&self) -> usize {
        if !self.a.is_zero() {
            2
        } else if !self.b.is_zero() {
            1
        } else {
            0
        }
    }

    pub fn lc(&self) -> Int {
        if !self.a.is_zero() {
            self.a.clone()
        } else if !self.b.is_zero() {
            self.b.clone()
        } else {
            self.c.clone()
        }
    }

    #[allow(dead_code)]
    pub fn cont(&self) -> Int {
        gcd(self.a.clone(), gcd(self.b.clone(), self.c.clone()))
    }
    
    #[allow(dead_code)]
    pub fn is_zero(&self) -> bool {
        self.a.is_zero() && self.b.is_zero() && self.c.is_zero()
    }

    pub fn constant(val: Int) -> Self {
        QuadPoly {
            a: Int::zero(),
            b: Int::zero(),
            c: val,
        }
    }
}

impl<Int: EuclideanDomain> std::ops::Mul for QuadPoly<Int> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        // Only multiplies if the result is a quadratic polynomial
        match (self.degree(), other.degree()) {
            (_, 0) => { self * other.c },
            (0, _) => { other * self.c },
            (1, 1) => QuadPoly { a: self.b.clone() * other.b.clone(), b: self.b * other.c.clone() + self.c.clone() * other.b.clone(), c: self.c * other.c },
            _ => panic!("Invalid quadratic polynomial multiplication"),
        }
    }
}

impl<Int: EuclideanDomain> std::ops::Mul<Int> for QuadPoly<Int> {
    type Output = Self;

    fn mul(mut self, rhs: Int) -> Self::Output {
        self.a = self.a * rhs.clone();
        self.b = self.b * rhs.clone();
        self.c = self.c * rhs.clone();
        self
    }
}

impl<Int: EuclideanDomain> std::ops::Div<Int> for QuadPoly<Int> {
    type Output = Self;

    fn div(mut self, rhs: Int) -> Self::Output {
        self.a = self.a / rhs.clone();
        self.b = self.b / rhs.clone();
        self.c = self.c / rhs.clone();
        self
    }
}

pub fn lcm<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    // quick optimization
    if a == b {
        a
    } else {
        a.clone() * b.clone() / gcd(a, b)
    }
}

// Algorithm 3.1.2
pub fn poly_pseudo_div<Int: EuclideanDomain + std::ops::AddAssign + std::ops::SubAssign>(a_poly: QuadPoly<Int>, b_poly: QuadPoly<Int>) -> (QuadPoly<Int>, QuadPoly<Int>) {
    assert!(a_poly.degree() >= b_poly.degree());
    if b_poly.degree() == 0 {
        return (a_poly, QuadPoly::constant(Int::zero()));
    }


    let mut r = a_poly.clone();
    let mut q = QuadPoly {
        a: Int::zero(),
        b: Int::zero(),
        c: Int::zero(),
    };
    let mut e = a_poly.degree() - b_poly.degree() + 1;
    let d = b_poly.lc();

    while r.degree() >= b_poly.degree() {
        let x_degr_minus_degd = match r.degree() - b_poly.degree() {
            0 => QuadPoly { a: Int::zero(), b: Int::zero(), c: Int::one() },
            1 => QuadPoly { a: Int::zero(), b: Int::one(), c: Int::zero() },
            2 => QuadPoly { a: Int::one(), b: Int::zero(), c: Int::zero() },
            _ => unreachable!()
        };
        let s = x_degr_minus_degd * (r.lc());
        q = (q * d.clone()) + s.clone();
        r = (r * d.clone()) - s.clone() * b_poly.clone();
        if e != 0 {
            e = e - 1;
        }
    }

    (q * d.clone().pow(e as u32), r * d.clone().pow(e as u32))
}

// https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#B%C3%A9zout%27s_identity_and_extended_GCD_algorithm
pub fn poly_extended_gcd<Int: EuclideanDomain>(a_poly: QuadPoly<Int>, b_poly: QuadPoly<Int>) -> (QuadPoly<Int>, QuadPoly<Int>, QuadPoly<Int>) {
    assert!(a_poly.degree() >= b_poly.degree());
    let mut r_prev = a_poly;
    let mut r = b_poly;
    let mut s_prev = QuadPoly::constant(Int::one());
    let mut s = QuadPoly::constant(Int::zero());
    let mut t_prev = QuadPoly::constant(Int::zero());
    let mut t = QuadPoly::constant(Int::one());
    
    while r.degree() != 0 {
        let (q, _) = poly_pseudo_div(r_prev.clone(), r.clone());
        let d = r.lc();
        let e = r_prev.degree() - r.degree() + 1;
        let new_r = (r_prev.clone() * d.clone().pow(e as u32)) - q.clone() * r.clone();
        let new_s = (s_prev.clone() * d.clone().pow(e as u32)) - q.clone() * s.clone();
        let new_t = (t_prev.clone() * d.clone().pow(e as u32)) - q.clone() * t.clone();
        r_prev = r.clone();
        r = new_r;
        s_prev = s.clone();
        s = new_s;
        t_prev = t.clone();
        t = new_t;
    }

    // (u, v, gcd)
    (s, t, r)
}

lazy_static! {
    // Precomputations 1.7.2
    static ref Q11: [bool; 11] = {
        let mut table: [bool; 11] = [false; 11];
        for k in 0..=5 {
            table[k * k % 11] = true;
        }
        table
    };

    static ref Q63: [bool; 63] = {
        let mut table: [bool; 63] = [false; 63];
        for k in 0..=31 {
            table[k * k % 63] = true;
        }
        table
    };

    static ref Q64: [bool; 64] = {
        let mut table: [bool; 64] = [false; 64];
        for k in 0..=31 {
            table[k * k % 64] = true;
        }
        table
    };

    static ref Q65: [bool; 65] = {
        let mut table: [bool; 65] = [false; 65];
        for k in 0..=32 {
            table[k * k % 65] = true;
        }
        table
    };
}

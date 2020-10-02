
use num_traits::PrimInt;

use derive_more::*;
// use derive_more::{PartialEq, Add, Sub, Neg, AddAssign, SubAssign};

/// A general quadratic polynomial
/// ax^2 + bx + c
#[derive(Debug, Clone, Copy, PartialEq, Add, Sub, Neg, AddAssign, SubAssign)]
pub struct QuadPoly<Int: PrimInt> {
    pub a: Int,
    pub b: Int,
    pub c: Int,
}

impl<Int: PrimInt> QuadPoly<Int> {
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
            self.a
        } else if !self.b.is_zero() {
            self.b
        } else {
            self.c
        }
    }

    pub fn cont(&self) -> Int {
        gcd(self.a, gcd(self.b, self.c))
    }

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

impl<Int: PrimInt> std::ops::Mul for QuadPoly<Int> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        // Only multiplies if the result is a quadratic polynomial
        match (self.degree(), other.degree()) {
            (_, 0) => { self * other.c },
            (0, _) => { other * self.c },
            (1, 1) => QuadPoly { a: self.b * other.b, b: self.b * other.c + self.c * other.b, c: self.c * other.c },
            _ => panic!("Invalid quadratic polynomial multiplication"),
        }
    }
}

impl<Int: PrimInt> std::ops::Mul<Int> for QuadPoly<Int> {
    type Output = Self;

    fn mul(mut self, rhs: Int) -> Self::Output {
        self.a = self.a * rhs;
        self.b = self.b * rhs;
        self.c = self.c * rhs;
        self
    }
}

impl<Int: PrimInt> std::ops::Div<Int> for QuadPoly<Int> {
    type Output = Self;

    fn div(mut self, rhs: Int) -> Self::Output {
        self.a = self.a / rhs;
        self.b = self.b / rhs;
        self.c = self.c / rhs;
        self
    }
}

pub fn gcd<Int: PrimInt>(mut a: Int, mut b: Int) -> Int {
    if a < b {
        std::mem::swap(&mut a, &mut b);
    }
    while !b.is_zero() {
        a = a % b;
        std::mem::swap(&mut a, &mut b);
    }
    a
}

pub fn lcm<Int: PrimInt>(a: Int, b: Int) -> Int {
    // quick optimization
    if a == b {
        a
    } else {
        a * b / gcd(a, b)
    }
}

// Algorithm 3.1.2
pub fn poly_pseudo_div<Int: PrimInt + std::ops::AddAssign + std::ops::SubAssign>(a_poly: QuadPoly<Int>, b_poly: QuadPoly<Int>) -> (QuadPoly<Int>, QuadPoly<Int>) {
    assert!(a_poly.degree() >= b_poly.degree());
    if b_poly.degree() == 0 {
        return (a_poly, QuadPoly::constant(Int::zero()));
    }


    let mut r = a_poly;
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
        q = (q * d) + s;
        r = (r * d) - s * b_poly;
        if e != 0 {
            e = e - 1;
        }
    }

    (q * d.pow(e as u32), r * d.pow(e as u32))
}

// Algorithm 3.3.1
pub fn poly_gcd<Int: PrimInt + std::ops::AddAssign + std::ops::SubAssign>(mut a_poly: QuadPoly<Int>, mut b_poly: QuadPoly<Int>) -> QuadPoly<Int> {
    // 1. Initializations and reductions
    if b_poly.degree() > a_poly.degree() {
        std::mem::swap(&mut a_poly, &mut b_poly)
    }
    if b_poly.is_zero() {
        return a_poly;
    }
    let a = a_poly.cont();
    let b = b_poly.cont();
    let d = gcd(a, b);
    a_poly = a_poly / a;
    b_poly = b_poly / b;
    let mut g = Int::one();
    let mut h = Int::one();
    
    loop {
        // 2. Pseudo division
        let delta = a_poly.degree() - b_poly.degree();

        let (_q, r) = poly_pseudo_div(a_poly * b_poly.lc().pow(delta as u32 + 1), b_poly);

        if r.is_zero() {
            // 4. Terminate
            return (b_poly / b_poly.cont()) * d;
        }
        if r.degree() == 0 {
            // 4. Terminate
            return QuadPoly::constant(d / b_poly.cont())
        }

        // 3. Reduce remainder
        a_poly = b_poly;
        b_poly = r / (g * h.pow(delta as u32));
        g = a_poly.lc();
        if delta != 0 {
            h = g.pow(delta as u32) / h.pow(delta as u32 - 1);
        }
    }
}

// https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#B%C3%A9zout%27s_identity_and_extended_GCD_algorithm
pub fn poly_extended_gcd<Int: PrimInt + std::ops::AddAssign + std::ops::SubAssign + std::fmt::Debug>(a_poly: QuadPoly<Int>, b_poly: QuadPoly<Int>) -> (QuadPoly<Int>, QuadPoly<Int>, QuadPoly<Int>) {
    assert!(a_poly.degree() >= b_poly.degree());
    let mut r_prev = a_poly;
    let mut r = b_poly;
    let mut s_prev = QuadPoly::constant(Int::one());
    let mut s = QuadPoly::constant(Int::zero());
    let mut t_prev = QuadPoly::constant(Int::zero());
    let mut t = QuadPoly::constant(Int::one());
    
    // TODO: This should only work for "coprime" polynomials, this should be !r_prev.is_zero()
    // (or something like that)
    while r.degree() != 0 {
    // while !r.is_zero() {
        // dbg!(r_prev);
        // dbg!(r);
        let (q, _) = poly_pseudo_div(r_prev, r);
        let d = r.lc();
        let e = r_prev.degree() - r.degree() + 1;
        let new_r = (r_prev * d.pow(e as u32)) - q * r;
        let new_s = (s_prev * d.pow(e as u32)) - q * s;
        let new_t = (t_prev * d.pow(e as u32)) - q * t;
        r_prev = r;
        r = new_r;
        s_prev = s;
        s = new_s;
        t_prev = t;
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

// Algorithm 1.7.1
fn int_sqrt<Int: PrimInt>(val: Int) -> Int {
    let mut x = val;
    loop {
        let y = (x + val / x) >> 2;
        if y < x {
            x = y;
        } else {
            return x;
        }
    }
}

pub fn is_perfect_square<Int: PrimInt>(val: Int) -> Option<Int> {
    if Q64[(val % Int::from(64).unwrap()).to_usize().unwrap()] == false {
        return None;
    }
    let r = val % Int::from(45045).unwrap();
    if Q63[r.to_usize().unwrap() % 63] == false {
        return None;
    } else if Q65[r.to_usize().unwrap() % 65] == false {
        return None;
    } else if Q11[r.to_usize().unwrap() % 11] == false {
        return None;
    }
    let q = int_sqrt(val);
    if q * q != val {
        None
    } else {
        Some(q)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let a = QuadPoly {
            a: 1i32,
            b: -3,
            c: -10,
        };

        let b = QuadPoly {
            a: 0i32,
            b: 1,
            c: 2,
        };

        assert_eq!(poly_pseudo_div(a, b), (QuadPoly { a: 0, b: 1, c: -5 }, QuadPoly { a: 0, b: 0, c: 0 }));


        // (2x - 10) (x + 10)
        let a = QuadPoly {
            a: 2i32,
            b: 10,
            c: -100,
        };

        // (x + 10)(4 - x)
        let b = QuadPoly {
            a: -1i32,
            b: -6,
            c: 40,
        };

        let g = poly_gcd(a, b);

        assert!(g == QuadPoly { a: 0, b: 1, c: 10 } || g == QuadPoly { a: 0, b: -1, c: -10 });
    }
}


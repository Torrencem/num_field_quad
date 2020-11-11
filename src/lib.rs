
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate alga_derive;
extern crate derive_more;
extern crate polynomial;

use alga::general::{Identity, Additive, TwoSidedInverse, AbstractMagma, Multiplicative};

use num_traits::PrimInt;

use polynomial::{EuclideanDomain, Polynomial, extended_gcd, gcd, lcm};

pub mod mod_p;
use mod_p::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuadraticField<Int: EuclideanDomain> {
    pub c: Int,
}

impl<Int: EuclideanDomain> QuadraticField<Int> {
    // Assumes that c is not a perfect square
    pub fn from_c(c: Int) -> QuadraticField<Int> {
        // TODO: Specialization: c is a perfect square check

        QuadraticField { c }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct QFElement<Int: EuclideanDomain + Eq> {
    // The standard representation of the element
    pub a: Int,
    pub b: Int,
    pub d: Int,
    // The underlying field
    pub field: QuadraticField<Int>,
}

impl<Int: EuclideanDomain + Eq> PartialEq for QFElement<Int> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.field == other.field);
        self.a.clone() * other.d.clone() == other.a.clone() * self.d.clone()
            && self.b.clone() * other.d.clone() == other.b.clone() * self.d.clone()
    }
}

impl<Int: EuclideanDomain + Eq> Eq for QFElement<Int> { }

impl<Int: EuclideanDomain + Eq + std::fmt::Display> std::fmt::Display for QFElement<Int> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Write numerator
        if self.a == Int::zero() && self.b == Int::zero() {
            write!(f, "0")?;
        } else if self.a == Int::zero() {
            if let Some(true) = self.field.c.is_negative() {
                write!(f, "{}√({})", self.b, self.field.c)?;
            } else {
                write!(f, "{}√{}", self.b, self.field.c)?;
            }
        } else if self.b == Int::zero() {
            write!(f, "{}", self.a)?;
        } else {
            if self.d != Int::one() {
                write!(f, "(")?;
            }
            if let Some(true) = self.field.c.is_negative() {
                write!(f, "{} + {}√({})", self.a, self.b, self.field.c)?;
            } else {
                write!(f, "{} + {}√{}", self.a, self.b, self.field.c)?;
            }
            if self.d != Int::one() {
                write!(f, ")")?;
            }
        }
        if self.d != Int::one() {
            write!(f, " / {}", self.d)?;
        }
        Ok(())
    }
}

impl<Int: EuclideanDomain + Eq> QFElement<Int> {
    pub fn from_integer(int: Int, field: QuadraticField<Int>) -> QFElement<Int> {
        QFElement {
            a: int,
            b: Int::zero(),
            d: Int::one(),
            field,
        }
    }

    pub fn from_rational(a: Int, b: Int, field: QuadraticField<Int>) -> QFElement<Int> {
        QFElement {
            a,
            b: Int::zero(),
            d: b,
            field,
        }
    }

    pub fn from_parts(a0: Int, a1: Int, d: Int, field: QuadraticField<Int>) -> QFElement<Int> {
        QFElement {
            a: a0, b: a1, d, field,
        }
    }

    pub fn is_rational(&self) -> bool {
        self.b.is_zero()
    }

    // Find the multiplicative inverse of this element
    pub fn inverse(&self) -> Self
    where Int: std::fmt::Debug {
        let my_poly = Polynomial::new(vec![self.b.clone(), self.a.clone()]);
        let t = Polynomial::new(vec![self.field.c.clone(), Int::zero(), Int::one()]);
        let (_v, u, gcd) = extended_gcd(t, my_poly);
        assert!(gcd.degree() == 0);
        
        let b = u.data().get(1).cloned().unwrap_or(Int::zero());
        let c = u.data().get(0).cloned().unwrap_or(Int::zero());
        let tmp1 = QFElement {a: b * self.d.clone(), b: c * self.d.clone(), d: Int::one(), field: self.field.clone()};
        let tmp2 = self.clone() * tmp1.clone();

        QFElement {
            a: tmp1.a,
            b: tmp1.b,
            d: tmp2.a / tmp2.d,
            field: self.field.clone(),
        }.reduce()
    }

    pub fn reduce(mut self) -> Self {
        let g = gcd(self.a.clone(), gcd(self.b.clone(), self.d.clone()));
        self.a = self.a.clone() / g.clone();
        self.b = self.b.clone() / g.clone();
        self.d = self.d.clone() / g.clone();
        if let Some(true) = self.d.is_negative() {
            self.a = -self.a;
            self.b = -self.b;
            self.d = -self.d;
        }
        self
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Add for QFElement<Int> {
    type Output = QFElement<Int>;

    fn add(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        let new_d = lcm(self.d.clone(), other.d.clone());
        QFElement {
            a: self.a.clone() * new_d.clone() / self.d.clone() + other.a * new_d.clone() / other.d.clone(),
            b: self.b.clone() * new_d.clone() / self.d.clone() + other.b.clone() * new_d.clone() / other.d.clone(),
            d: new_d,
            field: self.field,
        }
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::AddAssign for QFElement<Int> {
    fn add_assign(&mut self, rhs: Self) {
        assert!(self.field == rhs.field);
        *self = self.clone() + rhs;
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Sub for QFElement<Int> {
    type Output = QFElement<Int>;

    fn sub(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        let new_d = lcm(self.d.clone(), other.d.clone());
        QFElement {
            a: self.a.clone() * new_d.clone() / self.d.clone() - other.a.clone() * new_d.clone() / other.d.clone(),
            b: self.b.clone() * new_d.clone() / self.d.clone() - other.b.clone() * new_d.clone() / other.d.clone(),
            d: new_d.clone(),
            field: self.field,
        }
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::SubAssign for QFElement<Int> {
    fn sub_assign(&mut self, rhs: Self) {
        assert!(self.field == rhs.field);
        *self = self.clone() - rhs;
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Mul for QFElement<Int> {
    type Output = QFElement<Int>;

    fn mul(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        QFElement {
            a: self.a.clone() * other.a.clone() + self.b.clone() * other.b.clone() * self.field.c.clone(),
            b: self.a.clone() * other.b.clone() + self.b.clone() * other.a,
            d: self.d * other.d,
            field: self.field.clone(),
        }.reduce()
    }
}

impl<Int: EuclideanDomain + Eq + std::fmt::Debug> std::ops::Div for QFElement<Int> {
    type Output = QFElement<Int>;

    fn div(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        self * other.inverse()
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Add<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn add(mut self, rhs: Int) -> Self::Output {
        self.a = self.a.clone() + self.d.clone() * rhs.clone();
        self
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Sub<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn sub(mut self, rhs: Int) -> Self::Output {
        self.a = self.a.clone() - self.d.clone() * rhs;
        self
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Mul<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn mul(mut self, rhs: Int) -> Self::Output {
        self.a = self.a * rhs.clone();
        self.b = self.b * rhs;
        self
    }
}

impl<Int: EuclideanDomain + Eq> std::ops::Div<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn div(mut self, rhs: Int) -> Self::Output {
        self.d = self.d * rhs;
        self
    }
}

impl<Int: EuclideanDomain + Eq> PartialEq<Int> for QFElement<Int> {
    fn eq(&self, other: &Int) -> bool {
        self.b.is_zero() && self.a.clone() / self.d.clone() == *other
    }
}

#[macro_export]
macro_rules! qfelement {
    (($a:expr) + ($b:expr)i @($c:expr)) => ({
        QFElement::from_parts($a, $b, 1, $c)
    });
    (($c:expr) ! ($a:expr)) => ({
        QFElement::from_parts($a, 0, 1, $c)
    });
    (($a:expr) + ($b:expr)sqrt($c:expr)) => ({
        QFElement::from_parts($a, $b, 1, QuadraticField::from_c($c))
    });
    (($a:expr) + sqrt($c:expr)) => ({
        QFElement::from_parts($a, 1, 1, QuadraticField::from_c($c))
    });
    (($a:expr)sqrt($c:expr)) => ({
        QFElement::from_parts(0, $a, 1, QuadraticField::from_c($c))
    });
    (sqrt($c:expr)) => ({
        QFElement::from_parts(0, 1, 1, QuadraticField::from_c($c))
    });
}

#[derive(Debug, Clone)]
pub enum CriticalPoints<Int: EuclideanDomain + Eq> {
    None,
    One(QFElement<Int>),
    Two(QFElement<Int>, QFElement<Int>),
}

/// Returns the critical points of the quotient of two quadratic polynomials in their field of
/// definition. 
pub fn critical_points<Int: EuclideanDomain + Eq>(a_poly: Polynomial<Int>, b_poly: Polynomial<Int>) -> CriticalPoints<Int> {
    let two = Int::one() + Int::one();
    let four = two.clone() + two.clone();
    let a = a_poly.data().get(2).cloned().unwrap_or(Int::zero());
    let b = a_poly.data().get(1).cloned().unwrap_or(Int::zero());
    let c = a_poly.data().get(0).cloned().unwrap_or(Int::zero());
    let d = b_poly.data().get(2).cloned().unwrap_or(Int::zero());
    let e = b_poly.data().get(1).cloned().unwrap_or(Int::zero());
    let f = b_poly.data().get(0).cloned().unwrap_or(Int::zero());

    if (a.clone() * e.clone() - b.clone() * d.clone()).is_zero() {
        // Our equation is actually a line
        let slope = two.clone() * (a.clone() * f.clone() - c.clone() * d.clone());
        let constant = b.clone() * f.clone() - c.clone() * e.clone();
        if slope.is_zero() {
            return CriticalPoints::None;
        }
        let crit_pt = QFElement::from_parts(-constant, Int::zero(), slope, QuadraticField::from_c(Int::one()))
            .reduce();

        return CriticalPoints::One(crit_pt);
    }

    // Everything under the square root sign
    // Uses https://www.wolframalpha.com/input/?i=d%2Fdx+%28%28ax%5E2+%2B+bx+%2B+c%29+%2F+%28dx%5E2+%2B+ex+%2B+f%29%29+%3D+0
    let discr = (two.clone() * a.clone() * f.clone() - two.clone() * c.clone() * d.clone()).pow(2) - four.clone() * (e.clone() * a.clone() - b.clone() * d.clone()) * (b.clone() * f.clone() - e.clone() * c.clone());
    let rest_of_numerator = -two.clone() * a.clone() * f.clone() + two.clone() * c.clone() * d.clone();
    let denom = two.clone() * (e.clone() * a.clone() - b.clone() * d.clone());

    let x_1 = QFElement::from_parts(rest_of_numerator.clone(), Int::one(), denom.clone(), QuadraticField::from_c(discr.clone()))
        .reduce();
    let x_2 = QFElement::from_parts(rest_of_numerator.clone(), -Int::one(), denom.clone(), QuadraticField::from_c(discr))
        .reduce();
    CriticalPoints::Two(x_1, x_2)
}

use derive_more::{Add, Sub, AddAssign, SubAssign};

#[derive(Clone, Debug, PartialEq, Eq, Alga, Add, AddAssign, Sub, SubAssign)]
#[alga_traits(Ring(Additive, Multiplicative), Where = "Int: EuclideanDomain")]
pub struct ZiElement<Int: PrimInt + EuclideanDomain + std::fmt::Debug> {
    pub inner: QFElement<Int>,
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> ZiElement<Int> {
    pub fn from(elt: QFElement<Int>) -> Self {
        assert!(elt.field.c == -Int::one());
        assert!(elt.d == Int::one());
        ZiElement {
            inner: elt,
        }
    }

    pub fn from_parts(a: Int, b: Int) -> Self {
        ZiElement::from(QFElement {
            a, b,
            field: QuadraticField::from_c(-Int::one()),
            d: Int::one(),
        })
    }

    pub fn is_zero(&self) -> bool {
        self.inner.a == Int::zero() && self.inner.b == Int::zero()
    }

    pub fn square_root(&self) -> Option<ZiElement<Int>> {
        // From formulae in https://de.wikipedia.org/wiki/Quadratwurzel#Definition
        // For |z|
        let z_norm_sq = self.inner.a * self.inner.a + self.inner.b + self.inner.b;
        let z_norm = match is_perfect_square(z_norm_sq) {
            Some(x) => x,
            None => return None,
        };

        let a_sq = (z_norm + self.inner.a) / (Int::from(2).unwrap());
        let a = match is_perfect_square(a_sq) {
            Some(x) => x,
            None => return None,
        };

        let b_sq = (z_norm - self.inner.a) / (Int::from(2).unwrap());
        let b = match is_perfect_square(b_sq) {
            Some(x) => x,
            None => return None,
        };

        Some(ZiElement::from_parts(a, (if self.inner.b >= Int::zero() { Int::one() } else { -Int::one()}) * b))
    }
}

// derive_more generates bizzare bounds for these impls, so we do them manually
impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> std::ops::Mul for ZiElement<Int> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        ZiElement { inner: self.inner * rhs.inner }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> std::ops::MulAssign for ZiElement<Int> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = ZiElement { inner: self.inner.clone() * rhs.inner };
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> Identity<Additive> for ZiElement<Int> {
    fn identity() -> Self {
        ZiElement {
            inner: QFElement::from_parts(
                Int::zero(), Int::zero(), Int::one(), QuadraticField::from_c(-Int::one())
                       ),
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> Identity<Multiplicative> for ZiElement<Int> {
    fn identity() -> Self {
        ZiElement {
            inner: QFElement::from_parts(
                Int::one(), Int::zero(), Int::one(), QuadraticField::from_c(-Int::one())
                       ),
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> num_traits::identities::Zero for ZiElement<Int> {
    fn zero() -> Self {
        <Self as Identity<Additive>>::identity()
    }

    fn is_zero(&self) -> bool {
        *self == <Self as Identity<Additive>>::identity()
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> num_traits::identities::One for ZiElement<Int> {
    fn one() -> Self {
        <Self as Identity<Multiplicative>>::identity()
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> TwoSidedInverse<Additive> for ZiElement<Int> {
    fn two_sided_inverse(&self) -> Self {
        ZiElement {
            inner: QFElement::from_parts(
                Int::zero() - self.inner.a.clone(), Int::zero() - self.inner.b.clone(), self.inner.d.clone(), self.inner.field.clone()
                       ),
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> std::ops::Neg for ZiElement<Int> 
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        <Self as TwoSidedInverse<Additive>>::two_sided_inverse(&self)
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> AbstractMagma<Additive> for ZiElement<Int> {
    fn operate(&self, right: &Self) -> Self {
        ZiElement {
            inner: self.inner.clone() + right.inner.clone(),
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> TwoSidedInverse<Multiplicative> for ZiElement<Int> {
    fn two_sided_inverse(&self) -> Self {
        <Self as Identity<Multiplicative>>::identity() / self.clone()
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> AbstractMagma<Multiplicative> for ZiElement<Int> {
    fn operate(&self, right: &Self) -> Self {
        ZiElement {
            inner: self.inner.clone() * right.inner.clone(),
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> std::ops::Div for ZiElement<Int> {
    type Output = Self;

    fn div(self, rhs: ZiElement<Int>) -> Self::Output {
        let two = Int::from(2).unwrap();
        let real_quotient = self.inner / rhs.inner;
        // We want to round real_quotient to the nearest ZiElement.
        let mut floor_a = real_quotient.a / real_quotient.d;
        let mut floor_b = real_quotient.b / real_quotient.d;
        // Check if we needed to round up not down
        let mod_a = real_quotient.a.modulus(real_quotient.d);
        let mod_b = real_quotient.a.modulus(real_quotient.d);
        if real_quotient.a < Int::zero() {
            if mod_a * two < real_quotient.d {
                floor_a -= Int::one();
            }
        } else if mod_a * two >= real_quotient.d {
            floor_a += Int::one();
        }
        if real_quotient.b < Int::zero() {
            if mod_b * two < real_quotient.d {
                floor_b -= Int::one();
            }
        } else if mod_b * two >= real_quotient.d {
            floor_b += Int::one();
        }
        ZiElement {
            inner: QFElement::from_parts(floor_a, floor_b, Int::one(), self.inner.field)
        }
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> std::ops::DivAssign for ZiElement<Int> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> EuclideanDomain for ZiElement<Int> {
    fn modulus(self, other: Self) -> Self {
        self.clone() - other.clone() * (self.clone() / other.clone())
    }

    fn gcd(mut self, mut other: Self) -> Self {
        // Euclidean algorithm
        while !other.is_zero() {
            self = self.clone().modulus(other.clone());
            std::mem::swap(&mut self, &mut other);
        }
        self
    }
}

impl<Int: EuclideanDomain + PrimInt + std::fmt::Debug> ZiElement<Int> {
    pub fn reduce_mod(&self, p: u32) -> ModPElt {
        dbg!(p);
        let i = ModPElt { val: p as i64 - 1, p }.sqrt().unwrap();
        let a = ModPElt { val: self.inner.a.to_i64().unwrap(), p };
        let b = ModPElt { val: self.inner.b.to_i64().unwrap(), p };
        a + b * i
    }
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
    fn test_macro_uses() {
        let qi = QuadraticField::from_c(-1);
        
        // 5 + 6i
        let val = qfelement!((5) + (6)i @ (qi));

        assert_eq!(val, QFElement::from_parts(5, 6, 1, qi));
        
        // 5
        let val = qfelement!((qi) ! (5));

        assert_eq!(val, QFElement::from_parts(5, 0, 1, qi));
        
        // -10 + 5i
        let val = qfelement!((-10) + (5)sqrt(-1));

        assert_eq!(val, QFElement::from_parts(-10, 5, 1, qi));
        
        // 2i
        let val = qfelement!((2)sqrt(-1));

        assert_eq!(val, QFElement::from_parts(0, 2, 1, qi));
    
        // i
        let val = qfelement!(sqrt(-1));
        
        assert_eq!(val, QFElement::from_parts(0, 1, 1, qi));

        // An example of creating an actual rational number
        
        // The golden ratio (1 + sqrt(5)/2
        let phi = qfelement!((1) + sqrt(5)) / 2;

        assert!(phi * phi - phi - 1 == 0);
    }

    fn test_mul_inverse_value<Int: EuclideanDomain + Eq + std::fmt::Debug>(val: QFElement<Int>) {
        assert_eq!(val.inverse().inverse(), val);
        assert_eq!(val.clone() * val.clone().inverse(), QFElement::from_parts(Int::one(), Int::zero(), Int::one(), val.field));
    }

    #[test]
    fn test_mul_inverse() {
        let vals = vec![
            qfelement!((10i64) + (-1022)sqrt(76)) / 45,
            qfelement!((-44) + (0)sqrt(3)) / 3,
            qfelement!((-7) + (11)sqrt(99)) / 24,
            qfelement!((0) + (2)sqrt(-94)) / 11,
            qfelement!((5) + (0)sqrt(-11)),
        ];

        for val in vals {
            println!("({})^-1 = {}", val, val.inverse());
            test_mul_inverse_value(val);
        }
    }

    #[test]
    fn test_critical_points() {
        // x = var('x')
        // K.<i> = NumberField(x^2 + 15900)
        // P.<x, y> = ProjectiveSpace(K, 1)
        //
        // A = x^2 + 10*x*y - 15*y^2
        // B = -2*x^2 + 5*x*y + 10*y^2
        //
        // Q = DynamicalSystem_projective([A, B])
        let a_poly = Polynomial::new(vec![-15i32, 10, 1]);
        let b_poly = Polynomial::new(vec![10, 5, -2]);

        let crit_pts = critical_points(a_poly, b_poly);

        println!("critical points are: {:?}", crit_pts);
        

        let a_poly = Polynomial::new(vec![1i32]);
        let b_poly = Polynomial::new(vec![0, 0, 1]);

        let crit_pts = critical_points(a_poly, b_poly);

        println!("critical points of (1/x^2) are: {:?}", crit_pts);
    }

    #[test]
    fn test_gcd() {
        let a = ZiElement::from(qfelement!((10) + (7)sqrt(-1)));
        let b = ZiElement::from(qfelement!((10) + (5)sqrt(-1)));

        println!("{}", gcd(a.clone() * b.clone(), a.clone()).inner);
    }
}

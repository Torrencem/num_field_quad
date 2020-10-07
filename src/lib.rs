
#[macro_use]
extern crate lazy_static;
extern crate derive_more;

mod utils;

use utils::*;
use num_traits::PrimInt;

pub trait MyPrimInt: PrimInt + std::ops::AddAssign + std::ops::SubAssign + std::fmt::Debug + std::ops::Neg<Output=Self> { }
impl<T: PrimInt + std::ops::AddAssign + std::ops::SubAssign + std::fmt::Debug + std::ops::Neg<Output=Self>> MyPrimInt for T { }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuadraticField<Int: MyPrimInt> {
    pub c: Int,
}

impl<Int: MyPrimInt> QuadraticField<Int> {
    // Returns None if c is a perfect square
    pub fn from_c(c: Int) -> Option<QuadraticField<Int>> {
        if c >= Int::zero() && utils::is_perfect_square(c).is_some() {
            None
        } else {
            Some(QuadraticField { c })
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QFElement<Int: MyPrimInt> {
    // The standard representation of the element
    a: Int,
    b: Int,
    d: Int,
    // The underlying field
    field: QuadraticField<Int>,
}

impl<Int: MyPrimInt + std::fmt::Display> std::fmt::Display for QFElement<Int> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO handle special cases like a0 or a1 being 0, d being 1 and c being -1
        write!(f, "({} + {}√{})/({})", self.a, self.b, self.field.c, self.d)
    }
}

impl<Int: MyPrimInt> QFElement<Int> {
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
    
    // Get the standard representation as defined in section 4.2.2.
    pub fn standard_representation(&self) -> (Int, Int, Int) {
        (self.a, self.b, self.d)
    }

    // Find the multiplicative inverse of this element
    pub fn inverse(&self) -> Self {
        let my_poly = QuadPoly { a: Int::zero(), b: self.a, c: self.b };
        let t = QuadPoly { a: Int::one(), b: Int::zero(), c: self.field.c };
        let (_v, u, gcd) = poly_extended_gcd(t, my_poly);
        if gcd.degree() != 0 {
            dbg!(t);
            dbg!(my_poly);
            dbg!(gcd);
        }
        assert!(gcd.degree() == 0);
        let tmp1 = QFElement {a: u.b * self.d, b: u.c * self.d, d: Int::one(), field: self.field};
        let tmp2 = *self * tmp1;
        assert_eq!(tmp2.b, Int::zero());
        QFElement {
            a: tmp1.a,
            b: tmp1.b,
            d: tmp2.a / tmp2.d,
            field: self.field,
        }.reduce()
    }

    pub fn reduce(mut self) -> Self {
        let g = gcd(self.a, gcd(self.b, self.d));
        self.a = self.a / g;
        self.b = self.b / g;
        self.d = self.d / g;
        if self.d < Int::zero() {
            self.a = -self.a;
            self.b = -self.b;
            self.d = -self.d;
        }
        self
    }
}

impl<Int: MyPrimInt> std::ops::Add for QFElement<Int> {
    type Output = QFElement<Int>;

    fn add(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        let new_d = lcm(self.d, other.d);
        QFElement {
            a: self.a * new_d / self.d + other.a * new_d / other.d,
            b: self.b * new_d / self.d + other.b * new_d / other.d,
            d: new_d,
            field: self.field,
        }
    }
}

impl<Int: MyPrimInt> std::ops::Sub for QFElement<Int> {
    type Output = QFElement<Int>;

    fn sub(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        let new_d = lcm(self.d, other.d);
        QFElement {
            a: self.a * new_d / self.d - other.a * new_d / other.d,
            b: self.b * new_d / self.d - other.b * new_d / other.d,
            d: new_d,
            field: self.field,
        }
    }
}

impl<Int: MyPrimInt> std::ops::Mul for QFElement<Int> {
    type Output = QFElement<Int>;

    fn mul(self, other: QFElement<Int>) -> Self::Output {
        assert!(self.field == other.field);
        QFElement {
            a: self.a * other.a + self.b * other.b * self.field.c,
            b: self.a * other.b + self.b * other.a,
            d: self.d * other.d,
            field: self.field,
        }.reduce()
    }
}

impl<Int: MyPrimInt> std::ops::Add<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn add(mut self, rhs: Int) -> Self::Output {
        self.a = self.a + self.d * rhs;
        self
    }
}

impl<Int: MyPrimInt> std::ops::Sub<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn sub(mut self, rhs: Int) -> Self::Output {
        self.a = self.a - self.d * rhs;
        self
    }
}

impl<Int: MyPrimInt> std::ops::Mul<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn mul(mut self, rhs: Int) -> Self::Output {
        self.a = self.a * rhs;
        self.b = self.b * rhs;
        self
    }
}

impl<Int: MyPrimInt> std::ops::Div<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn div(mut self, rhs: Int) -> Self::Output {
        self.d = self.d * rhs;
        self
    }
}

impl<Int: MyPrimInt> PartialEq<Int> for QFElement<Int> {
    fn eq(&self, other: &Int) -> bool {
        self.b.is_zero() && self.a / self.d == *other
    }
}

// TODO: This probably shouldn't use unwrap()
#[macro_export]
macro_rules! qfelement {
    (($a:expr) + ($b:expr)i @($c:expr)) => ({
        QFElement::from_parts($a, $b, 1, $c)
    });
    (($c:expr) ! ($a:expr)) => ({
        QFElement::from_parts($a, 0, 1, $c)
    });
    (($a:expr) + ($b:expr)sqrt($c:expr)) => ({
        QFElement::from_parts($a, $b, 1, QuadraticField::from_c($c).unwrap())
    });
    (($a:expr) + sqrt($c:expr)) => ({
        QFElement::from_parts($a, 1, 1, QuadraticField::from_c($c).unwrap())
    });
    (($a:expr)sqrt($c:expr)) => ({
        QFElement::from_parts(0, $a, 1, QuadraticField::from_c($c).unwrap())
    });
    (sqrt($c:expr)) => ({
        QFElement::from_parts(0, 1, 1, QuadraticField::from_c($c).unwrap())
    });
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_uses() {
        let qi = QuadraticField::from_c(-1).unwrap();
        
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

    fn test_mul_inverse_value<Int: MyPrimInt>(val: QFElement<Int>) {
        assert_eq!(val.inverse().inverse(), val);
        assert_eq!(val * val.inverse(), QFElement::from_parts(Int::one(), Int::zero(), Int::one(), val.field));
        
    }

    #[test]
    fn test_mul_inverse() {
        let vals = vec![
            qfelement!((10) + (-1022)sqrt(76)) / 45,
            qfelement!((-44) + (0)sqrt(3)) / 3,
            qfelement!((-7) + (11)sqrt(99)) / 24,
        ];

        for val in vals {
            test_mul_inverse_value(val);
        }
    }
}

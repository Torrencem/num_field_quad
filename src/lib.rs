
#[macro_use]
extern crate lazy_static;
extern crate derive_more;

mod utils;

use utils::*;

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
pub struct QFElement<Int: EuclideanDomain> {
    // The standard representation of the element
    a: Int,
    b: Int,
    d: Int,
    // The underlying field
    field: QuadraticField<Int>,
}

impl<Int: EuclideanDomain> PartialEq for QFElement<Int> {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.field == other.field);
        self.a.clone() * other.d.clone() == other.a.clone() * self.d.clone()
            && self.b.clone() * other.d.clone() == other.b.clone() * self.d.clone()
    }
}

impl<Int: EuclideanDomain> Eq for QFElement<Int> { }

impl<Int: EuclideanDomain + std::fmt::Display> std::fmt::Display for QFElement<Int> {
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

impl<Int: EuclideanDomain> QFElement<Int> {
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
    pub fn inverse(&self) -> Self {
        let my_poly = QuadPoly { a: Int::zero(), b: self.a.clone(), c: self.b.clone() };
        let t = QuadPoly { a: Int::one(), b: Int::zero(), c: self.field.c.clone() };
        let (_v, u, gcd) = poly_extended_gcd(t, my_poly);
        assert!(gcd.degree() == 0);

        let tmp1 = QFElement {a: u.b * self.d.clone(), b: u.c * self.d.clone(), d: Int::one(), field: self.field.clone()};
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

impl<Int: EuclideanDomain> std::ops::Add for QFElement<Int> {
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

impl<Int: EuclideanDomain> std::ops::Sub for QFElement<Int> {
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

impl<Int: EuclideanDomain> std::ops::Mul for QFElement<Int> {
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

impl<Int: EuclideanDomain> std::ops::Add<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn add(mut self, rhs: Int) -> Self::Output {
        self.a = self.a.clone() + self.d.clone() * rhs.clone();
        self
    }
}

impl<Int: EuclideanDomain> std::ops::Sub<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn sub(mut self, rhs: Int) -> Self::Output {
        self.a = self.a.clone() - self.d.clone() * rhs;
        self
    }
}

impl<Int: EuclideanDomain> std::ops::Mul<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn mul(mut self, rhs: Int) -> Self::Output {
        self.a = self.a * rhs.clone();
        self.b = self.b * rhs;
        self
    }
}

impl<Int: EuclideanDomain> std::ops::Div<Int> for QFElement<Int> {
    type Output = QFElement<Int>;

    fn div(mut self, rhs: Int) -> Self::Output {
        self.d = self.d * rhs;
        self
    }
}

impl<Int: EuclideanDomain> PartialEq<Int> for QFElement<Int> {
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

    fn test_mul_inverse_value<Int: EuclideanDomain + std::fmt::Debug>(val: QFElement<Int>) {
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
}

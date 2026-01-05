//! Utility for calculating the product of iterators while checking for overflow.
//!
//! The [`CheckedProduct`] trait is implemented for iterators of integer types, via those types
//! implementing [`CheckedMultiply`].

// NOTE patterned from https://github.com/elsirion/checked_sum as I didn't immediately find a
// published crate for this feature

use num_traits::One;

/// Iterator extension trait for calculating the product of numbers with overflow checking.
pub trait CheckedProduct<T> {
    /// Multiplies numbers in an iterator, checking for overflow.
    /// Returns `None` if overflow occurred.
    fn checked_product(self) -> Option<T>;
}

impl<T, I> CheckedProduct<T> for I
where
    T: CheckedMultiply + One,
    I: Iterator<Item = T>,
{
    fn checked_product(mut self) -> Option<T> {
        self.try_fold(T::one(), |acc, value| acc.checked_multiply(&value))
    }
}

/// Numeric type supporting overflow-checked multiplication.
pub trait CheckedMultiply: Sized {
    /// Multiplies two numbers checking for overflow, returns `None` if overflow occurred.
    fn checked_multiply(&self, other: &Self) -> Option<Self>;
}

macro_rules! impl_checked_multiply {
    ($($t:ty),*) => {
        $(
            impl CheckedMultiply for $t {
                fn checked_multiply(&self, other: &Self) -> Option<Self> {
                    <$t>::checked_mul(*self, *other)
                }
            }
        )*
    };
}

impl_checked_multiply!(u8, u16, u32, u64, u128, usize);
impl_checked_multiply!(i8, i16, i32, i64, i128, isize);

#[cfg(test)]
mod tests {
    use crate::checked_product::CheckedProduct;

    #[test]
    fn test_checked_product() {
        let values = vec![1u8, 2, 3, 4, 5];
        let maybe_product = values.into_iter().checked_product();
        assert_eq!(maybe_product, Some(2 * 3 * 4 * 5));
    }

    #[test]
    fn test_checked_product_empty_iterator() {
        let values: Vec<u64> = vec![];
        let maybe_product = values.into_iter().checked_product();
        assert_eq!(maybe_product, Some(1));
    }

    #[test]
    fn test_checked_product_overflow() {
        let values = vec![200u8, 2];
        let maybe_product = values.into_iter().checked_product();
        assert_eq!(maybe_product, None);

        let values = vec![2u8, 200];
        let maybe_product = values.into_iter().checked_product();
        assert_eq!(maybe_product, None);
    }
}

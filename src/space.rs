use std::{
    cmp,
    convert::TryFrom,
    ops::{Add, Range, Sub},
};
/// A limit agnostic representation of a contigous range.
///
/// `SIZED` when `true` defines a range which stores its `size` when `SIZED` is `false` it defines a
/// range which stores its `end`.
// The specific ordering between 2 spaces does not matter, only that an ordering can be made, this
// is why we derive the ordering over explictly implementing it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Space<T = u64, const SIZED: bool = true> {
    start: T,
    limit: T,
}
impl<const SIZED: bool, T: Copy> Space<T, SIZED> {
    /// Returns size/length of space.
    pub fn start(&self) -> T {
        self.start
    }
}
// Sized bounded space
// -----------------------------------------------------------------------------
use thiserror::Error;

/// Space construction error type
#[derive(Debug, PartialEq, Eq, Error, Clone, Copy, PartialOrd, Ord)]
pub enum SpaceError {
    /// When: The given `start` is less than zero.
    #[error("The given `start` is less than zero.")]
    Underflow,
    /// When: The given `start` plus the given `size` is greater than the maximum value for `T`.
    #[error("The given `start` plus the given `size` is greater than the maximum value for `T`.")]
    Overflow,
    /// When: The given `start` less than the given `end`.
    #[error("The given `start` less than the given `end`.")]
    Invalid,
}

impl<T: Ord + num::Zero + num::CheckedAdd> TryFrom<(T, T)> for Space<T, true> {
    type Error = SpaceError;
    fn try_from((start, size): (T, T)) -> Result<Self, Self::Error> {
        match start.checked_add(&size).is_some() {
            true if start >= T::zero() => Ok(Self { start, limit: size }),
            true => Err(Self::Error::Underflow),
            false => Err(Self::Error::Overflow),
        }
    }
}
impl<T: Copy + Ord + num::Zero + Sub<Output = T>> TryFrom<Range<T>> for Space<T, true> {
    type Error = SpaceError;
    fn try_from(Range { start, end }: Range<T>) -> Result<Self, Self::Error> {
        match end >= start {
            true if start >= T::zero() => Ok(Self {
                start,
                limit: end - start,
            }),
            true => Err(Self::Error::Underflow),
            false => Err(Self::Error::Invalid),
        }
    }
}
impl<T: Copy + Add<Output = T> + Ord> Space<T, true> {
    /// Returns size/length of space.
    pub fn size(&self) -> T {
        self.limit
    }
    /// Returns end of space.
    pub fn end(&self) -> T {
        self.start + self.limit
    }
    /// Similar to [std::ops::Range::contains()]
    pub fn contains(&self, x: &T) -> bool {
        (self.start()..self.end()).contains(x)
    }
    /// Returns true if the current space contains the space passed as a
    /// parameter.
    pub fn encompasses(&self, other: &Self) -> bool {
        self.start >= other.start && self.limit <= other.limit
    }
    /// Returns true if the regions overlap.
    pub fn overlaps(&self, other: &Self) -> bool {
        cmp::max(self.start, other.start) <= cmp::min(self.end(), other.end())
    }
}

// End bounded space
// -----------------------------------------------------------------------------

impl<T: Ord + num::Zero> TryFrom<(T, T)> for Space<T, false> {
    type Error = SpaceError;
    fn try_from((start, end): (T, T)) -> Result<Self, Self::Error> {
        match end >= start {
            true if start >= T::zero() => Ok(Self { start, limit: end }),
            true => Err(Self::Error::Underflow),
            false => Err(Self::Error::Invalid),
        }
    }
}
impl<T: Ord + num::Zero> TryFrom<Range<T>> for Space<T, false> {
    type Error = SpaceError;
    fn try_from(Range { start, end }: Range<T>) -> Result<Self, Self::Error> {
        Self::try_from((start, end))
    }
}
impl<T: Copy + Sub<Output = T> + Ord> Space<T, false> {
    /// Returns size/length of space.
    pub fn size(&self) -> T {
        self.limit - self.start
    }
    /// Returns end of space.
    pub fn end(&self) -> T {
        self.limit
    }
    /// Similar to [std::ops::Range::contains()]
    pub fn contains(&self, x: &T) -> bool {
        (self.start()..self.end()).contains(x)
    }
    /// Returns true if the current space contains the space passed as a
    /// parameter.
    pub fn encompasses(&self, other: &Self) -> bool {
        self.start >= other.start && self.limit <= other.limit
    }
    /// Returns true if the regions overlap.
    pub fn overlaps(&self, other: &Self) -> bool {
        cmp::max(self.start, other.start) <= cmp::min(self.end(), other.end())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_sized_overflow() {
        assert_eq!(
            Space::<_, true>::try_from((u64::max_value(), 0x100)),
            Err(SpaceError::Overflow)
        );
    }
    #[test]
    fn test_sized_underflow() {
        assert_eq!(
            Space::<_, true>::try_from((-100, 0x0)),
            Err(SpaceError::Underflow)
        );
    }
    #[test]
    fn test_ended_invalid() {
        assert_eq!(
            Space::<_, false>::try_from((100, 10)),
            Err(SpaceError::Invalid)
        );
    }
    #[test]
    fn test_ended_underflow() {
        assert_eq!(
            Space::<_, false>::try_from((-100, 0x0)),
            Err(SpaceError::Underflow)
        );
    }
}

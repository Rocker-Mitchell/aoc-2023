//! Framework of traits and utilities for Advent of Code.
//!
//! # Quick Start
//!
//! 1. Define your input type and implement [`ParseData`]:
//!
//! ```
//! # use aoc_framework::{DynamicResult, ParseData};
//! #
//! struct Lines(Vec<String>);
//!
//! impl ParseData for Lines {
//!     fn parse(input: &str) -> DynamicResult<Self> {
//!         Ok(Self(input.lines().map(String::from).collect()))
//!     }
//! }
//! ```
//!
//! 2. Implement [`Solution`] for your part:
//!
//! ```
//! # use aoc_framework::{DynamicResult, ParseData, PartOne, Solution};
//! #
//! # struct Lines(Vec<String>);
//! # impl ParseData for Lines {
//! #     fn parse(input: &str) -> DynamicResult<Self> {
//! #         Ok(Self(input.lines().map(String::from).collect()))
//! #     }
//! # }
//! #
//! struct Day01;
//!
//! impl Solution<PartOne> for Day01 {
//!     type Input = Lines;
//!     type Output = usize;
//!
//!     fn solve(input: &Self::Input) -> DynamicResult<usize> {
//!         Ok(input.0.len())
//!     }
//! }
//! ```
//!
//! 3. Use the [`runner`] module to execute your solution.
//!
//! # Examples
//!
//! ## Solution with `Input = str`
//!
//! ```
//! use aoc_framework::{DynamicResult, PartOne, Solution};
//!
//! struct Day02;
//!
//! impl Solution<PartOne> for Day02 {
//!     type Input = str;
//!     type Output = usize;
//!
//!     fn solve(input: &str) -> DynamicResult<usize> {
//!         Ok(input.lines().count())
//!     }
//! }
//! ```
//!
//! ## Solution with a custom `Input` struct
//!
//! ```
//! use aoc_framework::{DynamicResult, ParseData, PartOne, Solution};
//!
//! struct Numbers {
//!     values: Vec<u32>,
//! }
//!
//! impl ParseData for Numbers {
//!     fn parse(input: &str) -> DynamicResult<Self> {
//!         let values = input
//!             .lines()
//!             .map(|line| line.parse())
//!             .collect::<Result<Vec<_>, _>>()?;
//!         Ok(Numbers { values })
//!     }
//! }
//!
//! struct Day03;
//!
//! impl Solution<PartOne> for Day03 {
//!     type Input = Numbers;
//!     type Output = u32;
//!
//!     fn solve(input: &Numbers) -> DynamicResult<u32> {
//!         Ok(input.values.iter().sum())
//!     }
//! }
//! ```

#![warn(clippy::pedantic)]
#![warn(
    clippy::allow_attributes,
    clippy::allow_attributes_without_reason,
    clippy::branches_sharing_code,
    clippy::collection_is_never_read,
    clippy::equatable_if_let,
    clippy::needless_collect,
    clippy::needless_pass_by_ref_mut,
    clippy::option_if_let_else,
    clippy::set_contains_or_insert,
    clippy::suboptimal_flops,
    clippy::suspicious_operation_groupings,
    clippy::trait_duplication_in_bounds,
    clippy::type_repetition_in_bounds,
    clippy::use_self,
    clippy::useless_let_if_seq
)]
#![deny(
    clippy::expect_used,
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::unwrap_used
)]

use std::error::Error;
use std::fmt::Display;

pub mod parsing;
pub mod runner;

mod private {
    /// A private sealed trait used to prevent external implementations of public traits.
    ///
    /// This trait is part of the sealed trait pattern, which is a Rust idiom used to:
    /// - Prevent users outside of this crate from implementing certain public traits
    /// - Allow for future trait additions without breaking existing code
    /// - Maintain API stability while retaining implementation flexibility
    ///
    /// # Example
    ///
    /// This trait is typically used in conjunction with public traits:
    ///
    /// ```ignore
    /// pub trait PublicTrait: private::Sealed {}
    /// ```
    pub trait Sealed {}
}

/// A dynamically dispatched error, wrapped in a [`Box`].
pub type DynamicError = Box<dyn Error + Send + Sync + 'static>;
/// A result that can return a [`DynamicError`] as an error.
pub type DynamicResult<T> = Result<T, DynamicError>;

/// An enum to identify a solution part.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartKind {
    One,
    Two,
}

impl Display for PartKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::One => write!(f, "Part 1"),
            Self::Two => write!(f, "Part 2"),
        }
    }
}

/// A marker trait used to identify a part for a solution.
///
/// Types implementing this trait are used as generic parameters to [`Solution<P>`] to indicate
/// which part the solution implements.
pub trait Part: private::Sealed {
    /// Get the related [`PartKind`] for this part.
    fn kind() -> PartKind;
}

/// Indicates a [`Solution`] implements part one.
///
/// This zero-sized marker struct has no runtime impact.
pub struct PartOne;
impl private::Sealed for PartOne {}
impl Part for PartOne {
    fn kind() -> PartKind {
        PartKind::One
    }
}

/// Indicates a [`Solution`] implements part two.
///
/// This zero-sized marker struct has no runtime impact.
pub struct PartTwo;
impl private::Sealed for PartTwo {}
impl Part for PartTwo {
    fn kind() -> PartKind {
        PartKind::Two
    }
}

/// A generic trait for a solution that solve for a [`Part`].
///
/// It is expected solutions implement for the marker structs [`PartOne`] or [`PartTwo`].
pub trait Solution<P: Part> {
    /// The input data type passed to the solution.
    ///
    /// [`Solution::solve`] will accept a reference to this type, so consider avoiding reference
    /// nesting.
    ///
    /// For direct string input, set to `str`.
    type Input: ?Sized;

    /// The output data type returned from the solution.
    type Output: Display;

    /// Solve with the given input.
    ///
    /// # Errors
    ///
    /// A solution can encounter varying errors while solving, like invalid input or a logical
    /// error.
    /// It is returned as a dynamically dispatched error.
    ///
    /// # Returns
    ///
    /// A result from solving the input.
    fn solve(input: &Self::Input) -> DynamicResult<Self::Output>;
}

/// A trait for data structures that are created by parsing string input.
///
/// Solutions can be passed parsed data constructed through this trait by setting
/// [`Solution::Input`] to the implementing struct.
pub trait ParseData {
    /// Parse an input string into an instance of self.
    ///
    /// # Errors
    ///
    /// If parsing fails, the resulting error is returned as a dynamically dispatched error.
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized;
}

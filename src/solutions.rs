//! Solutions implemented for Advent of Code 2023.
//!
//! This module provides [`run_day`] to dynamically run a solution by its day.
//!
//! Steps to make a solution available to run:
//! 1. Make a submodule to hold the solution implementation.
//! 2. Have the submodule implement [`AdventOfCode2023<DAY>`] for its day as a [`SolutionRunner`].
//! 3. Import the submodule below `IMPORT SUBMODULES HERE`
//! 4. Add a match case to run [`AdventOfCode2023<DAY>`] for a day, below `MATCH SOLUTIONS HERE`:
//!
//! ```ignore
//! // matching for day 1
//! 1 => AdventOfCode2023::<1>::run(input, handler, timed),
//! ```

#![warn(clippy::dbg_macro, clippy::print_stderr, clippy::print_stdout)]

use aoc_framework::DynamicResult;
use aoc_framework::runner::{OutputHandler, SolutionRunner};
use thiserror::Error;

// --- IMPORT SUBMODULES HERE ---
mod day01;
mod day02;
mod day03;
mod day04;
mod day05;
mod day06;
mod day07;
mod day08;
mod day09;

/// A structure collecting solutions by day.
///
/// In a submodule, implement this as a [`SolutionRunner`] for the day.
///
/// Use [`#[solution_runner]`][aoc_framework::runner::solution_runner] for convenience:
///
/// ```ignore
/// // in a submodule "day01.rs"
/// use aoc_framework::runner::solution_runner;
/// use aoc_framework::{PartOne, Solution};
///
/// struct Day01;
/// impl Solution<PartOne> for Day01 {
///     /* ... */
/// }
///
/// #[solution_runner(name = "Day 1", part_one = Day01)]
/// impl super::AdventOfCode2023<1> {}
/// ```
struct AdventOfCode2023<const DAY: u8>;

/// A solution for a day is not available.
#[derive(Error, Debug)]
#[error("no solution available for day {0}")]
pub struct DayNotAvailable(u8);

/// Run a solution based on the day.
///
/// # Errors
///
/// If the solution for the given day is not available, a [`DayNotAvailable`] error is returned.
///
/// Any dynamically dispatched error from running the solution is propagated.
pub fn run_day(
    day: u8,
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()> {
    match day {
        // --- MATCH SOLUTIONS HERE ---
        1 => AdventOfCode2023::<1>::run(input, handler, timed),
        2 => AdventOfCode2023::<2>::run(input, handler, timed),
        3 => AdventOfCode2023::<3>::run(input, handler, timed),
        4 => AdventOfCode2023::<4>::run(input, handler, timed),
        5 => AdventOfCode2023::<5>::run(input, handler, timed),
        6 => AdventOfCode2023::<6>::run(input, handler, timed),
        7 => AdventOfCode2023::<7>::run(input, handler, timed),
        8 => AdventOfCode2023::<8>::run(input, handler, timed),
        9 => AdventOfCode2023::<9>::run(input, handler, timed),
        _ => Err(DayNotAvailable(day).into()),
    }
}

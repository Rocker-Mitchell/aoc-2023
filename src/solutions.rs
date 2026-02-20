//! Solutions implemented for Advent of Code 2023.
//!
//! This module provides [`run_day`] to dynamically run a solution by its day.
//!
//! Steps to make a solution available to run:
//! 1. Make a submodule to hold the solution implementation.
//! 2. Have the submodule implement [`AdventOfCode2023<DAY>`] for its day as a [`SolutionRunner`].
//! 3. Import the submodule below `IMPORT SUBMODULES HERE`
//! 4. Add a match arm to run [`AdventOfCode2023<DAY>`] for its day, below `MATCH SOLUTIONS HERE`:
//!
//! ```ignore
//! // support matching for day 1
//! match_solutions!(day, input, handler, timed; 1)
//! // add match arm for day 2
//! match_solutions!(day, input, handler, timed; 1, 2)
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
mod day10;
mod day11;
mod day12;
mod day13;
mod day14;
mod day15;
mod day16;
mod day17;
mod day18;
mod day19;
mod day20;
mod day21;
mod day22;
mod day23;
mod day24;

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

/// Emit a complete match block over `day` to run solutions with arms for the given day literals.
macro_rules! match_solutions {
    ($day_var:ident, $input:ident, $handler:ident, $timed:ident; $( $day:literal ),* $(,)? ) => {
        match $day_var {
            $(
                $day => AdventOfCode2023::<$day>::run($input, $handler, $timed),
            )*
            _ => Err(DayNotAvailable($day_var).into()),
        }
    };
}

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
    // --- MATCH SOLUTIONS HERE ---
    match_solutions!(
        day, input, handler, timed;
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24
    )
}

//! Functions and traits for running solutions.
//!
//! # Quick Start
//!
//! A structure or impl-block can be annotated with the [`#[solution_runner]`][solution_runner]
//! attribute macro with appropriate properties:
//!
//! ```
//! # use aoc_framework::runner::{solution_runner};
//! # use aoc_framework::{DynamicResult, PartOne, Solution};
//! #
//! struct Day01;
//!
//! impl Solution<PartOne> for Day01 {
//!     type Input = str;
//!     /* ... */
//! #    type Output = usize;
//! #    fn solve(_input: &Self::Input) -> DynamicResult<usize> {
//! #        Ok(0)
//! #    }
//! }
//!
//! #[solution_runner(name = "Day 1", part_one = Day01)]
//! struct Day01Runner;
//!
//! // or
//!
//! #[solution_runner(name = "Day 1", part_one = Day01)]
//! impl Day01 {}
//! ```

use std::fmt::Display;
use std::time::Duration;

use crate::{DynamicResult, ParseData, Part, PartKind, PartOne, PartTwo, Solution};

// re-export procedural macro
pub use aoc_framework_macros::solution_runner;

/// A trait for an output events handler.
///
/// When a solution runs, the steps of running the solution leads to events to output through a
/// handler as feedback and logging.
pub trait OutputHandler {
    /// Called to output the name of the solution, at the start of running the solution.
    fn solution_name(&mut self, name: &str);

    /// Called when the solution starts parsing input.
    fn parse_start(&mut self);

    /// Called when parsing input is finished.
    ///
    /// The duration taken to parse is optionally passed.
    fn parse_end(&mut self, duration_opt: Option<Duration>);

    /// Called when a solution part starts, with a [`PartKind`] to identify the part.
    fn part_start(&mut self, part: PartKind);

    /// Called when a part finishes to output the result, with a [`PartKind`] to identify the part.
    ///
    /// The duration taken to run the part is optionally passed.
    fn part_output(&mut self, part: PartKind, output: &dyn Display, duration_opt: Option<Duration>);
}

/// Measure the duration of an expression.
///
/// The macro evaluates the given expression once and returns a tuple of the expression's result and
/// the elapsed [`Duration`][std::time::Duration].
///
/// Note, if the expression has side effects or consumes variables, that will still be part of the
/// measured time.
///
/// # Returns
///
/// A tuple containing the result of the expression and its duration.
macro_rules! measure_duration {
    ($expr:expr) => {{
        let start = ::std::time::Instant::now();
        let result = $expr;
        let elapsed = start.elapsed();
        (result, elapsed)
    }};
}

/// A macro to optionally measure the duration of an expression.
///
/// This macro evaluates the given expression and returns a tuple containing the result of the
/// expression and an optional [`Duration`][std::time::Duration]. If the `$timed` flag evaluates to
/// `true`, the duration of the expression's evaluation is measured and included in the output.
/// If `$timed` evaluates to `false`, the duration will be `None`.
///
/// # Arguments
///
/// - `$expr`: The expression to evaluate and measure.
/// - `$timed`: A boolean flag indicating whether to measure the duration.
///
/// # Returns
///
/// A tuple containing the result of the expression and an optional duration:
/// - If `$timed` is `true`, the duration of the evaluation is included.
/// - If `$timed` is `false`, the duration is `None`.
macro_rules! measure_with_optional_duration {
    ($expr:expr, $timed:expr) => {{
        if $timed {
            let (result, duration) = measure_duration!($expr);
            (result, Some(duration))
        } else {
            ($expr, None)
        }
    }};
}

/// Run a solution part, outputting events through the handler.
///
/// # Arguments
///
/// - `input` - The input data to solve.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to solve then output the elapsed time to the handler.
///
/// # Errors
///
/// Any dynamically dispatched error from the solution is propagated.
fn run_part<S, P>(
    input: &S::Input,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()>
where
    P: Part,
    S: Solution<P>,
{
    let part = P::kind();
    handler.part_start(part);
    let (result, duration_opt) = measure_with_optional_duration!(S::solve(input), timed);
    let output = result?;
    handler.part_output(part, &output, duration_opt);
    Ok(())
}

/// Run a solution's parse step, outputting events through the handler.
///
/// # Arguments
///
/// - `input` - The input string to parse.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to parse then output the elapsed time to the handler.
///
/// # Errors
///
/// Any dynamically dispatched error from parsing is propagated.
fn run_parse<D: ParseData>(
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<D> {
    handler.parse_start();
    let (result, duration_opt) = measure_with_optional_duration!(D::parse(input), timed);
    let parsed = result?;
    handler.parse_end(duration_opt);
    Ok(parsed)
}

/// Run a solution that only implements part one and accepts string input.
///
/// # Arguments
///
/// - `name` - The solution's name to output.
/// - `input` - The input string to solve.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to solve then output the elapsed time to the handler.
///
/// # Errors
///
/// Any dynamically dispatched error from the solution is propagated.
pub fn solve_half_solution<S1>(
    name: &str,
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()>
where
    S1: Solution<PartOne, Input = str>,
{
    handler.solution_name(name);
    run_part::<S1, PartOne>(input, handler, timed)
}

/// Run a solution that implements both parts and accepts string input.
///
/// # Arguments
///
/// - `name` - The solution's name to output.
/// - `input` - The input string to solve.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to solve parts then output the elapsed times to the
///   handler.
///
/// # Errors
///
/// Any dynamically dispatched error from the solution parts is propagated.
pub fn solve_full_solution<S1, S2>(
    name: &str,
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()>
where
    S1: Solution<PartOne, Input = str>,
    S2: Solution<PartTwo, Input = str>,
{
    handler.solution_name(name);
    run_part::<S1, PartOne>(input, handler, timed)?;
    run_part::<S2, PartTwo>(input, handler, timed)
}

/// Run a solution that implements part one and has a parse data step for input.
///
/// # Arguments
///
/// - `name` - The solution's name to output.
/// - `input` - The input string to solve.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to parse data & solve then output the elapsed times to
///   the handler.
///
/// # Errors
///
/// Any dynamically dispatched error from parsing or the solution is propagated.
pub fn solve_parsed_half_solution<D, S1>(
    name: &str,
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()>
where
    D: ParseData,
    S1: Solution<PartOne, Input = D>,
{
    handler.solution_name(name);
    let parsed = run_parse::<D>(input, handler, timed)?;
    run_part::<S1, PartOne>(&parsed, handler, timed)
}

/// Run a solution that implements both parts and has a parse data step for input.
///
/// # Arguments
///
/// - `name` - The solution's name to output.
/// - `input` - The input string to solve.
/// - `handler` - The output handler to output events to.
/// - `timed` - A flag to measure the time to parse data & solve parts then output the elapsed times
///   to the handler.
///
/// # Errors
///
/// Any dynamically dispatched error from parsing or the solution parts is propagated.
pub fn solve_parsed_full_solution<D, S1, S2>(
    name: &str,
    input: &str,
    handler: &mut dyn OutputHandler,
    timed: bool,
) -> DynamicResult<()>
where
    D: ParseData,
    S1: Solution<PartOne, Input = D>,
    S2: Solution<PartTwo, Input = D>,
{
    handler.solution_name(name);
    let parsed = run_parse::<D>(input, handler, timed)?;
    run_part::<S1, PartOne>(&parsed, handler, timed)?;
    run_part::<S2, PartTwo>(&parsed, handler, timed)
}

/// A trait for solutions that can be run.
///
/// The trait can be implemented with the [`solution_runner`] attribute macro.
pub trait SolutionRunner {
    /// Run the solution.
    ///
    /// # Arguments
    ///
    /// - `input` - The input string to solve.
    /// - `handler` - The output handler to output events to.
    /// - `timed` - A flag to measure the time to process steps then output the elapsed times to the
    ///   handler.
    ///
    /// # Errors
    ///
    /// Any dynamically dispatched error from running the solution is propagated.
    fn run(input: &str, handler: &mut dyn OutputHandler, timed: bool) -> DynamicResult<()>;
}

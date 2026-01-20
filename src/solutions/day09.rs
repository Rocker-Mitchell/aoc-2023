use std::num::ParseIntError;
use std::str::FromStr;

use aoc_framework::parsing::{ParseContextError, parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;

#[solution_runner(
    name = "Day 9: Mirage Maintenance",
    parsed = Measurements,
    part_one = Day09,
    part_two = Day09
)]
impl super::AdventOfCode2023<9> {}

/*
Input is a report of measurements changing over time. Each line is a history of a value, separating
changes to the value with spaces.
*/

/// A history of changes to a value.
///
/// Values are observed to be signed and reach up to 8 digits.
#[derive(Debug)]
struct History(Vec<i32>);

#[derive(thiserror::Error, Debug)]
enum ParseHistoryError {
    #[error("failed to parse a history value")]
    ParseInt(#[from] ParseContextError<ParseIntError>),
}

impl FromStr for History {
    type Err = ParseHistoryError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let values = s
            .split_whitespace()
            .map(parse_with_context)
            .collect::<Result<_, _>>()?;
        Ok(Self(values))
    }
}

struct Measurements(Vec<History>);

impl ParseData for Measurements {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let measurements =
            parse_input_lines(input, |_, line| line.parse()).collect::<Result<_, _>>()?;
        Ok(Self(measurements))
    }
}

/*
For part 1, calculate a prediction of the next value for each history and return the sum.

To calculate a prediction, find the difference between values, and repeat calculating difference
layers from earlier differences until they are all zeros. Then the next value can be extrapolated
per layer, taking the last value and adding the predicted value of the lower layer (predicting 0 for
the last layer).
*/

/// Calculate a vector of differences from a sequence of values.
fn get_differences(values: &[i32]) -> Vec<i32> {
    values
        .windows(2)
        .map(|window| {
            window[1]
                .checked_sub(window[0])
                .expect("should not overflow calculating difference")
        })
        .collect()
}

/// Recursively predict the next value in a sequence.
fn predict_next_value(values: &[i32]) -> i32 {
    // base cases
    assert!(
        !values.is_empty(),
        "exhausted difference layers during recursion"
    );
    if values.iter().all(|v| *v == 0) {
        return 0;
    }

    let differences = get_differences(values);

    // recursively calculate next value of differences
    let next = predict_next_value(&differences);

    // predict with sum of last value and next difference
    values[values.len() - 1]
        .checked_add(next)
        .expect("should not overflow adding predicted difference to last value")
}

impl History {
    /// Predict the next value in the history.
    fn predict_next_value(&self) -> i32 {
        predict_next_value(&self.0)
    }
}

struct Day09;

impl Solution<PartOne> for Day09 {
    type Input = Measurements;
    type Output = i32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .0
            .iter()
            .map(History::predict_next_value)
            .checked_sum()
            .expect("should not overflow calculating sum");
        Ok(sum)
    }
}

/*
For part 2, calculate a prediction of the value before the first per each history and return the
sum.

Predictions involve the same difference layering but now extrapolate a layer by taking the first
value and subtracting the predicted value of the lower layer.
*/

/// Recursively predict the previous value of a sequence.
fn predict_previous_value(values: &[i32]) -> i32 {
    // base cases
    assert!(
        !values.is_empty(),
        "exhausted difference layers during recursion"
    );
    if values.iter().all(|v| *v == 0) {
        return 0;
    }

    let differences = get_differences(values);

    // recursively calculate previous value of differences
    let previous = predict_previous_value(&differences);

    // predict with difference of first value and previous difference
    values[0]
        .checked_sub(previous)
        .expect("should not overflow subtracting predicted difference from first value")
}

impl History {
    /// Predict the previous value of the history.
    fn predict_previous_value(&self) -> i32 {
        predict_previous_value(&self.0)
    }
}

impl Solution<PartTwo> for Day09 {
    type Input = Measurements;
    type Output = i32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .0
            .iter()
            .map(History::predict_previous_value)
            .checked_sum()
            .expect("should not overflow calculating sum");
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"0 3 6 9 12 15
1 3 6 10 15 21
10 13 16 21 30 45
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Measurements::parse(EXAMPLE_INPUT)?;
        let result = <Day09 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 114);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Measurements::parse(EXAMPLE_INPUT)?;
        let result = <Day09 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 2);
        Ok(())
    }
}

use std::cmp::PartialOrd;
use std::ops::{Add, Div, Mul, Sub};

use aoc_framework::parsing::{InputScanner, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};

use crate::checked_product::CheckedProduct;

#[solution_runner(name = "Day 6: Wait For It", parsed = RaceInput, part_one = Day06, part_two = Day06)]
impl super::AdventOfCode2023<6> {}

/*
Input describes times allowed for toy boat races and their distances to beat.

The first line describes times in milliseconds, the second distances in millimeters. Both contain
space-separated lists of numbers, with an equal count of numbers between lists. Times and distances
pair by list index.

For part 2, instead of space-separated lists, lines hold single, large numbers with some whitespace
separation to ignore.
*/

/// Data for a toy boat race, as interpreted for part 1.
#[derive(Debug)]
struct PartOneRaceData {
    /// The time allowed for the race.
    ///
    /// Observed 2 digit numbers from input, so this is sized for such.
    time: u8,

    /// The record distance to beat.
    ///
    /// Observed 4 digit numbers from input, so this is sized for such.
    distance: u16,
}

/// Data for a toy boat race, as interpreted for part 2.
struct PartTwoRaceData {
    /// The time allowed for the race.
    ///
    /// Observed a cumulative 8 digits from input, so this is sized for such.
    time: u32,

    /// The record distance to beat.
    ///
    /// Observed a cumulative 15 digits from input, so this is sized for such.
    distance: u64,
}

/// The input data for toy boat races.
struct RaceInput {
    /// The collection of races relevant to part one.
    part_one_races: Vec<PartOneRaceData>,
    /// The single race relevant to part two.
    part_two_race: PartTwoRaceData,
}

/// Errors when parsing input for [`RaceInput`].
#[derive(thiserror::Error, Debug)]
enum RaceInputParseError {
    #[error("expected a first line for times")]
    MissingFirstLineTimes,

    #[error("expected line for times to be prefixed with \"Time:\", found line: {0:?}")]
    ExpectedTimePrefix(String),

    #[error("expected a second line for distances")]
    MissingSecondLineDistances,

    #[error("expected line for distances to be prefixed with \"Distance:\", found line: {0:?}")]
    ExpectedDistancePrefix(String),

    #[error(
        "space-separated lists for times and distances are not of equal length: times length = {times_length}, distances length = {distances_length}"
    )]
    UnequalListLengths {
        times_length: usize,
        distances_length: usize,
    },
}

impl ParseData for RaceInput {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn remove_whitespace(string: &str) -> String {
            string.chars().filter(|c| !c.is_whitespace()).collect()
        }

        let mut scanner = InputScanner::new(input);

        let (times_list, large_time) = scanner
            .next_in_sequence(|_, line| -> DynamicResult<_> {
                let value = line
                    .strip_prefix("Time:")
                    .ok_or_else(|| RaceInputParseError::ExpectedTimePrefix(line.to_owned()))?;

                // parse space-separated numbers for part one
                let list: Vec<_> = value
                    .split_whitespace()
                    .map(parse_with_context)
                    .collect::<Result<_, _>>()?;

                // parse large number, ignoring whitespace, for part two
                let large_number_str = remove_whitespace(value);
                let large_number = parse_with_context(&large_number_str)?;

                Ok((list, large_number))
            })?
            .ok_or(RaceInputParseError::MissingFirstLineTimes)?;

        let (distances_list, large_distance) = scanner
            .next_in_sequence(|_, line| -> DynamicResult<_> {
                let value = line
                    .strip_prefix("Distance:")
                    .ok_or_else(|| RaceInputParseError::ExpectedDistancePrefix(line.to_owned()))?;

                // parse space-separated numbers for part one
                let list: Vec<_> = value
                    .split_whitespace()
                    .map(parse_with_context)
                    .collect::<Result<_, _>>()?;

                // parse large number, ignoring whitespace, for part two
                let large_number_str = remove_whitespace(value);
                let large_number = parse_with_context(&large_number_str)?;

                Ok((list, large_number))
            })?
            .ok_or(RaceInputParseError::MissingSecondLineDistances)?;

        if times_list.len() != distances_list.len() {
            return Err(RaceInputParseError::UnequalListLengths {
                times_length: times_list.len(),
                distances_length: distances_list.len(),
            }
            .into());
        }

        let part_one_races = times_list
            .into_iter()
            .zip(distances_list)
            .map(|(time, distance)| PartOneRaceData { time, distance })
            .collect();

        let part_two_race = PartTwoRaceData {
            time: large_time,
            distance: large_distance,
        };

        Ok(Self {
            part_one_races,
            part_two_race,
        })
    }
}

/*
For part 1, the toy boat used in the races has a button for charging. The boat must charge before it
can move, with speed affected by how long the charge button was held.

Charging factors into the race time. It's only allowed to charge at the start of a race.

Each millisecond charging the toy boat yields one millimeter per millisecond.

Calculate the counts of distinct milliseconds you can charge the toy boat to beat the distances,
then return the product of these amounts.
*/

/*
d = (1 [mm/ms] * t_charge) * (time - t_charge) = time * t_charge - t_charge^2
this is a quadratic equation, arching like a projectile curve
- if I find the smallest t_charge over the distance, the largest should mirror across the midpoint
  of the time
  - example w/ time 7 has center of 3.5, and smallest t_charge of 2: largest mirrors as 5
  - example w/ time 30 has center 15, and smallest t_charge of 11: largest mirrors as 19
- I should only need to search from 0 to floor(time/2) inclusively for a threshold t_charge
  - I can do binary search
*/

/// Trait for a time value to use in operations.
///
/// Implement the trait for the integer types representing times, like [`u8`].
trait TimeOps:
    Copy
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + PartialOrd
{
    /// Saturating integer subtraction.
    /// Computes `self - rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_subtract(self, rhs: Self) -> Self;

    /// Returns `true` if the integer is even, and `false` otherwise.
    fn is_even(self) -> bool;

    /// The representation of integer `0` in this type.
    fn zero() -> Self;

    /// The representation of integer `1` in this type.
    fn one() -> Self;

    /// The representation of integer `2` in this type.
    fn two() -> Self;
}

impl TimeOps for u8 {
    fn saturating_subtract(self, rhs: Self) -> Self {
        self.saturating_sub(rhs)
    }

    fn is_even(self) -> bool {
        self.is_multiple_of(2)
    }

    fn zero() -> Self {
        0
    }

    fn one() -> Self {
        1
    }

    fn two() -> Self {
        2
    }
}

/// Trait for a distance value to use in operations.
///
/// Implement the trait for the integer types representing distances, like [`u16`].
trait DistanceOps: Sized + Copy + PartialOrd {
    /// Checked integer multiplication.
    /// Computes `self * rhs`, returning `None` if overflow occurred.
    fn checked_multiply(self, rhs: Self) -> Option<Self>;
}

impl DistanceOps for u16 {
    fn checked_multiply(self, rhs: Self) -> Option<Self> {
        self.checked_mul(rhs)
    }
}

/// Calculate distance traveled from a charge time & total race time.
fn distance<T, D>(charge_time: T, total_time: T) -> D
where
    T: TimeOps,
    D: From<T> + DistanceOps,
{
    let remaining_time = total_time.saturating_subtract(charge_time);
    D::from(remaining_time)
        .checked_multiply(D::from(charge_time))
        .expect("should not have integer overflow when calculating distance")
}

/// Find the count of distinct winning charge times that can beat the record distance.
///
/// # Arguments
/// - `total_time` - The total time available in the race.
/// - `record_distance` - The record distance to beat.
fn count_distinct_winning_charges<T, D>(total_time: T, record_distance: D) -> T
where
    T: TimeOps,
    D: From<T> + DistanceOps,
{
    let half_time = total_time / T::two(); // truncate towards 0 for odd numbers

    // binary search for smallest charge time beating record distance, between 0 and half time
    let mut low = T::zero();
    let mut high = half_time;
    let mut smallest_charge_found = None;
    while low <= high {
        let mid = low + (high - low) / T::two();
        if distance::<T, D>(mid, total_time) > record_distance {
            smallest_charge_found = Some(mid);
            if mid == T::zero() {
                // prevent underflow when subtracting 1
                break;
            }
            high = mid - T::one();
        } else {
            low = mid + T::one();
        }
    }

    // if no smallest charge is found, there is no count, thus default to 0
    smallest_charge_found.map_or(T::zero(), |smallest_charge| {
        // count is double the distinct charge times from the smallest to half time, as the largest
        // charge time is mirrored across the halfway point
        let half_count = half_time - smallest_charge + T::one();
        let count = half_count * T::two();
        // if time is an even number, subtract 1 to handle half time counted twice in doubling
        if total_time.is_even() {
            count - T::one()
        } else {
            count
        }
    })
}

struct Day06;

impl Solution<PartOne> for Day06 {
    type Input = RaceInput;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let product = input
            .part_one_races
            .iter()
            .map(|race_data| count_distinct_winning_charges(race_data.time, race_data.distance))
            .map(Self::Output::from)
            .checked_product()
            .expect("should not have integer overflow calculating product");
        Ok(product)
    }
}

/*
For part 2, input now must handle the space-separated list of numbers by ignoring the spaces,
forming single, large numbers.

Now with input containing one race, return the unique count of charge times to beat the record
distance.
*/

impl TimeOps for u32 {
    fn saturating_subtract(self, rhs: Self) -> Self {
        self.saturating_sub(rhs)
    }

    fn is_even(self) -> bool {
        self.is_multiple_of(2)
    }

    fn zero() -> Self {
        0
    }

    fn one() -> Self {
        1
    }

    fn two() -> Self {
        2
    }
}

impl DistanceOps for u64 {
    fn checked_multiply(self, rhs: Self) -> Option<Self> {
        self.checked_mul(rhs)
    }
}

impl Solution<PartTwo> for Day06 {
    type Input = RaceInput;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let race_data = &input.part_two_race;
        let result = count_distinct_winning_charges(race_data.time, race_data.distance);
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = "Time:      7  15   30\nDistance:  9  40  200\n";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = RaceInput::parse(EXAMPLE_INPUT)?;
        let result = <Day06 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 288);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = RaceInput::parse(EXAMPLE_INPUT)?;
        let result = <Day06 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 71503);
        Ok(())
    }
}

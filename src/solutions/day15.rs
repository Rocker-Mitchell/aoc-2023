use std::borrow::ToOwned;
use std::collections::HashMap;
use std::str::FromStr;

use aoc_framework::parsing::parse_with_context;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;

use crate::checked_product::CheckedProduct;

#[solution_runner(
    name = "Day 15: Lens Library",
    parsed = InputSteps,
    part_one = Day15,
    part_two = Day15
)]
impl super::AdventOfCode2023<15> {}

/*
Input is a comma-separated list of steps.

> Input is expected to be one line.

Part 1 only has the string representation of steps relevant.
*/

#[derive(Debug)]
struct InputSteps(Vec<String>);

#[derive(thiserror::Error, Debug)]
enum ParseInputStringsError {
    #[error("expected one line in input")]
    ExpectedOneLine,
}

impl ParseData for InputSteps {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut lines = input.lines();
        let expected_line = lines
            .next()
            .ok_or(ParseInputStringsError::ExpectedOneLine)?;
        if lines.next().is_some() {
            return Err(ParseInputStringsError::ExpectedOneLine.into());
        }

        let strings = expected_line.split(',').map(ToOwned::to_owned).collect();
        Ok(Self(strings))
    }
}

/*
A hash algorithm is described to convert a string to a number 0-255. Initialize a current value with
0 then for each character in order:

1. Get its ASCII code
2. Increment current value with code
3. Multiply current value by 17
4. Modify current value to modulo of 256

For part 1, apply the algorithm to the string representation of the steps from input and return the
sum.
*/

/// Hashing algorithm as described in part 1.
fn hash_string(string: &str) -> u8 {
    let result = string.chars().fold(0u16, |acc, ch| {
        assert!(ch.is_ascii(), "non-ASCII character detected: {ch:?}");
        let ascii = ch as u16; // fits in u8
        ((acc + ascii) * 17) % 256
    });

    u8::try_from(result).expect("should be castable to u8 after modulo")
}

struct Day15;

impl Solution<PartOne> for Day15 {
    type Input = InputSteps;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .0
            .iter()
            .map(|s| Self::Output::from(hash_string(s)))
            .checked_sum()
            .expect("summing hashes should not overflow");
        Ok(sum)
    }
}

/*
For part 2, steps from input start with a sequence of letters as the label of a lens operated with,
and the hash **of the label** indicates a box operated on.

After the label is a character indicating the operation: `-` or `=`:
- A dash (`-`) operation must go to the box and remove the lens by label, if it is present. Then,
  move remaining lenses to the front of the box without changing order, removing gaps.
- An equals (`=`) operation will be followed by a digit for the lens focal length (1 to 9).
  - If there's already a lens in the box with matching label, swap in the new lens in-place.
  - Otherwise, add the lens to the end in the box.

A lens's focusing power is determined by the product of box index + 1, lens position
(one-indexed), and lens focal length.

After processing all steps, find the sum focusing power of lenses.
*/

/// A step's operation.
#[derive(Debug)]
enum StepOperation {
    /// Remove a lens by label.
    Remove,
    /// Insert a lens by label with the contained focal length.
    Insert(u8),
}

/// A step from input, formatted as the label of a lens and the step operation.
#[derive(Debug)]
struct Step(String, StepOperation);

#[derive(thiserror::Error, Debug)]
enum ParseStepError {
    #[error("no label detected (expected starting sequence of letters)")]
    NoLabel,

    #[error("no operation detected (no character after label found)")]
    NoOperation,

    #[error("invalid operation {0:?} (expected '-' or '=')")]
    InvalidOperation(char),

    #[error("no focal length detected (no digit after '=' found)")]
    NoFocalLength,

    #[error("unable to parse digit {0:?} for focal length")]
    InvalidFocalLength(char),
}

impl FromStr for Step {
    type Err = ParseStepError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();

        // extract label
        let mut label = String::new();
        while let Some(ch) = chars.next() {
            if ch.is_alphabetic() {
                label.push(ch);
            } else {
                // label ended
                if label.is_empty() {
                    return Err(ParseStepError::NoLabel);
                }

                // parse the operation
                match ch {
                    '-' => {
                        return Ok(Self(label, StepOperation::Remove));
                    }
                    '=' => {
                        // next character should be the focal length digit
                        match chars.next() {
                            Some(digit_ch) => match digit_ch.to_digit(10) {
                                Some(digit) => {
                                    let focal_length =
                                        u8::try_from(digit).expect("digit should fit in u8");
                                    return Ok(Self(label, StepOperation::Insert(focal_length)));
                                }
                                None => {
                                    return Err(ParseStepError::InvalidFocalLength(digit_ch));
                                }
                            },
                            None => {
                                return Err(ParseStepError::NoFocalLength);
                            }
                        }
                    }
                    _ => {
                        return Err(ParseStepError::InvalidOperation(ch));
                    }
                }
            }
        }

        // evaluate if we've exhausted the string without finding label or operation
        if label.is_empty() {
            Err(ParseStepError::NoLabel)
        } else {
            Err(ParseStepError::NoOperation)
        }
    }
}

#[derive(Debug, Clone, Default)]
struct LensBox {
    /// The ordered sequence of lenses by label.
    labels: Vec<String>,
    /// Mapping of the focal length of each lens in `labels`.
    focal_lengths: HashMap<String, u8>,
}

impl LensBox {
    /// Insert the labeled lens or replace an existing labeled lens.
    fn insert(&mut self, label: &str, focal_length: u8) {
        if let Some(value) = self.focal_lengths.get_mut(label) {
            *value = focal_length;
        } else {
            self.labels.push(label.to_owned());
            self.focal_lengths.insert(label.to_owned(), focal_length);
        }
    }

    /// Remove the labeled lens if contained.
    fn remove(&mut self, label: &str) {
        if self.focal_lengths.remove(label).is_some() {
            let old_len = self.labels.len();
            self.labels.retain(|l| l != label);
            assert_eq!(
                self.labels.len(),
                old_len - 1,
                "did not remove one lens from order as expected"
            );
        }
    }

    /// Calculate the focusing power contributed by the box, given its hash value.
    fn focusing_power(&self, box_hash: u8) -> u32 {
        let box_number = u32::from(box_hash) + 1;
        self.labels
            .iter()
            .enumerate()
            .map(|(index, label)| {
                let position = u32::try_from(index)
                    .expect("labels index should fit return type")
                    .checked_add(1)
                    .expect("offsetting index should not overflow");
                let focal_length = u32::from(
                    *self
                        .focal_lengths
                        .get(label)
                        .expect("label should have key in focal_lengths"),
                );

                [box_number, position, focal_length]
                    .into_iter()
                    .checked_product()
                    .expect("lens's focusing power product should not overflow")
            })
            .checked_sum()
            .expect("sum of focusing power in box should not overflow")
    }
}

impl Solution<PartTwo> for Day15 {
    type Input = InputSteps;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut boxes_map: HashMap<u8, LensBox> = HashMap::with_capacity(256);

        // walk through steps to modify the boxes
        for step_str in &input.0 {
            let step: Step = parse_with_context(step_str)?;

            // NOTE we don't want the hash of the full step, we want the label's hash!
            let lens_box = boxes_map.entry(hash_string(&step.0)).or_default();

            match step.1 {
                StepOperation::Insert(focal_length) => {
                    lens_box.insert(&step.0, focal_length);
                }
                StepOperation::Remove => {
                    lens_box.remove(&step.0);
                }
            }
        }

        let sum = boxes_map
            .into_iter()
            .map(|(box_hash, lens_box)| lens_box.focusing_power(box_hash))
            .checked_sum()
            .expect("summing boxes' focusing power should not overflow");
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calculates_hash() {
        let result = hash_string("HASH");
        assert_eq!(result, 52);
    }

    const EXAMPLE_INPUT: &str = "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7\n";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = InputSteps::parse(EXAMPLE_INPUT)?;
        let result = <Day15 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 1320);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = InputSteps::parse(EXAMPLE_INPUT)?;
        let result = <Day15 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 145);
        Ok(())
    }
}

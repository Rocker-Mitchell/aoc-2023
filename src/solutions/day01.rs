use aoc_framework::parsing::parse_lines_with_offset;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use regex::Regex;
use thiserror::Error;

#[solution_runner(name = "Day 1: Trebuchet?!", part_one = Day01, part_two = Day01)]
impl super::AdventOfCode2023<1> {}

#[derive(Error, Debug)]
enum Day01Error {
    #[error("No digits found in line")]
    NoDigitInLine,
    #[error("No digit or full named number in line")]
    NoNumberInLine,
}

/*
Input is a calibration document with special formatting.

For part 1, each line has a calibration value within. It requires combining the first and last
digit (in order) for a two-digit number.

> If there's only one digit in the line, that digit is both the first & last.

Calculate the sum of calibration values as the solution.
*/

type CalibrationValue = u8;

fn calibration_value(first_digit: u8, last_digit: u8) -> CalibrationValue {
    first_digit * 10 + last_digit
}

fn parse_calibration_value_by_digit(line: &str) -> Result<CalibrationValue, Day01Error> {
    let mut digits = line.chars().filter_map(|c| {
        c.to_digit(10)
            .map(|d| CalibrationValue::try_from(d).expect("should be base 10 integer (0 to 9)"))
    });

    let first_opt = digits.next();
    first_opt.map_or(Err(Day01Error::NoDigitInLine), |first_digit| {
        // if there's no separate last digit, use first as last
        let last_digit = digits.next_back().unwrap_or(first_digit);

        Ok(calibration_value(first_digit, last_digit))
    })
}

fn sum_calibration_values(values: impl Iterator<Item = CalibrationValue>) -> u16 {
    values
        .map(u16::from)
        .checked_sum()
        .expect("should not have integer overflow during summation")
}

struct Day01;

impl Solution<PartOne> for Day01 {
    type Input = str;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let values: Vec<CalibrationValue> =
            parse_lines_with_offset(input, 0, |line| Ok(parse_calibration_value_by_digit(line)?))
                .collect::<Result<_, _>>()?;
        let sum = sum_calibration_values(values.into_iter());
        Ok(sum)
    }
}

/*
Input is treated differently for part 2. Now, some digits are spelled out in english ("one", "two",
etc.). The solution must handle both digit chars and spelled out digits.

The solution is still the sum of calibration values.
*/

fn extract_calibration_digits_or_names(
    line: &str,
    re: &Regex,
) -> Result<(String, String), Day01Error> {
    let first_opt = re.find(line);
    first_opt.map_or(Err(Day01Error::NoNumberInLine), |first| {
        // with concern of overlaps, loop from last index backwards and test regex
        let last = {
            let mut last = None;
            for index in (0..line.len()).rev() {
                if let Some(m) = re.find_at(line, index)
                    && m.start() == index
                {
                    last = Some(m);
                    break;
                }
            }
            last.expect("should at least find first match if there isn't another later")
        };
        Ok((first.as_str().to_string(), last.as_str().to_string()))
    })
}

fn number_token_to_integer(token: &str) -> u8 {
    match token {
        "0" | "zero" => 0,
        "1" | "one" => 1,
        "2" | "two" => 2,
        "3" | "three" => 3,
        "4" | "four" => 4,
        "5" | "five" => 5,
        "6" | "six" => 6,
        "7" | "seven" => 7,
        "8" | "eight" => 8,
        "9" | "nine" => 9,
        other => panic!("tried to convert unrecognized token: {other:?}"),
    }
}

impl Solution<PartTwo> for Day01 {
    type Input = str;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // match on digit or full name
        const PATTERN: &str = r"\d|zero|one|two|three|four|five|six|seven|eight|nine";

        let re = Regex::new(PATTERN).expect("pattern should be valid");

        let values: Vec<CalibrationValue> = parse_lines_with_offset(input, 0, |line| {
            let (first, last) = extract_calibration_digits_or_names(line, &re)?;
            let first_digit = number_token_to_integer(&first);
            let last_digit = number_token_to_integer(&last);
            Ok(calibration_value(first_digit, last_digit))
        })
        .collect::<Result<_, _>>()?;

        let sum = sum_calibration_values(values.into_iter());
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT_ONE: &str = r"1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let result = <Day01 as Solution<PartOne>>::solve(EXAMPLE_INPUT_ONE)?;
        assert_eq!(result, 142);
        Ok(())
    }

    const EXAMPLE_INPUT_TWO: &str = r"two1nine
eightwothree
abcone2threexyz
xtwone3four
4nineeightseven2
zoneight234
7pqrstsixteen
";

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let result = <Day01 as Solution<PartTwo>>::solve(EXAMPLE_INPUT_TWO)?;
        assert_eq!(result, 281);
        Ok(())
    }
}

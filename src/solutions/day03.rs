use std::collections::{HashMap, HashSet};

use aoc_framework::parsing::parse_lines_with_offset;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use nalgebra::Point2;

#[solution_runner(name = "Day 3: Gear Ratios", parsed = Schematic, part_one = Day03, part_two = Day03)]
impl super::AdventOfCode2023<3> {}

#[derive(thiserror::Error, Debug)]
enum Day03Error {
    /// The length of the line does not match the first line's length.
    #[error("expected line length matching first line ({first_length}), found {found}")]
    MismatchedLineLength { first_length: usize, found: usize },
}

/*
Input is an engine schematic, formatted as a visual representation of the engine. Numbers are digits
defined in sequence (left-to-right), and any character other than `.` is a symbol.
*/

/// Integer type for x/y coordinates in schematic grid.
///
/// Observed dimensions of 140 from input, so is sized to hold such.
type Dimension = i16;

#[derive(Debug)]
struct SchematicSymbol {
    symbol: char,
    coords: Point2<Dimension>,
}

/// Type for part numbers in schematic.
///
/// Observed numbers with at most 3 digits from input, so is sized to hold such.
type PartNumber = u16;

#[derive(Debug)]
struct SchematicNumber {
    value: PartNumber,
    /// The coordinates of the starting/leftmost character of the number.
    start_coords: Point2<Dimension>,
    /// How many characters wide this number was in the schematic.
    ///
    /// Observed numbers with at most 3 digits from input, so is sized to hold literal `3`.
    width: u8,
}

impl SchematicNumber {
    fn new_from(digits: &str, start_coords: Point2<Dimension>) -> Self {
        let value = digits
            .parse()
            .expect("digits should be parsable as part number");
        Self {
            value,
            start_coords,
            width: u8::try_from(digits.len()).expect("digits length should fit within u8"),
        }
    }
}

struct Schematic {
    symbols: Vec<SchematicSymbol>,
    numbers: Vec<SchematicNumber>,
}

impl ParseData for Schematic {
    fn parse(input: &str) -> aoc_framework::DynamicResult<Self>
    where
        Self: Sized,
    {
        // TODO this need for line_idx makes me question if parse_lines_with_offset should pass the
        // index generally; callers can ignore it with `_`
        let mut line_idx: usize = 0;
        let mut first_line_length = None;
        let (symbols, numbers) = parse_lines_with_offset(input, 0, |line| {
            fn create_coords(char_idx: usize, line_idx: usize) -> Point2<Dimension> {
                let x = Dimension::try_from(char_idx)
                    .expect("largest character index from input should fit within dimension type");
                let y = Dimension::try_from(line_idx)
                    .expect("largest line index from input should fit within dimension type");
                Point2::new(x, y)
            }

            // reusable logic for ending digit sequence, as it has to be done during & after
            // iteration
            fn end_digit_sequence(
                found_digit_sequence: &mut bool,
                start_char_idx: usize,
                line_idx: usize,
                digit_sequence: &mut String,
                numbers: &mut Vec<SchematicNumber>,
            ) {
                if *found_digit_sequence {
                    let start_coords = create_coords(start_char_idx, line_idx);
                    let found_number = SchematicNumber::new_from(digit_sequence, start_coords);
                    numbers.push(found_number);

                    // reset for next number
                    digit_sequence.clear();
                    *found_digit_sequence = false;
                }
            }

            // require all line lengths match
            if let Some(expected_length) = first_line_length {
                if line.len() != expected_length {
                    return Err(Day03Error::MismatchedLineLength {
                        first_length: expected_length,
                        found: line.len(),
                    }
                    .into());
                }
            } else {
                first_line_length = Some(line.len());
            }

            let mut symbols = Vec::new();
            let mut numbers = Vec::new();

            let mut found_digit_sequence = false;
            let mut digit_sequence_start_idx = 0;
            let mut digit_sequence = String::new();

            for (char_idx, character) in line.chars().enumerate() {
                if character.is_ascii_digit() {
                    if !found_digit_sequence {
                        digit_sequence_start_idx = char_idx;
                        found_digit_sequence = true;
                    }
                    digit_sequence.push(character);
                } else {
                    end_digit_sequence(
                        &mut found_digit_sequence,
                        digit_sequence_start_idx,
                        line_idx,
                        &mut digit_sequence,
                        &mut numbers,
                    );

                    if character != '.' {
                        let coords = create_coords(char_idx, line_idx);
                        let found_symbol = SchematicSymbol {
                            symbol: character,
                            coords,
                        };
                        symbols.push(found_symbol);
                    }
                }
            }
            end_digit_sequence(
                &mut found_digit_sequence,
                digit_sequence_start_idx,
                line_idx,
                &mut digit_sequence,
                &mut numbers,
            );

            // tracking line index externally of parse lines function
            line_idx = line_idx.saturating_add(1);

            Ok((symbols, numbers))
        })
        .try_fold(
            (Vec::new(), Vec::new()),
            |(mut acc_symbols, mut acc_numbers),
             result|
             -> DynamicResult<(Vec<SchematicSymbol>, Vec<SchematicNumber>)> {
                let (symbols, numbers) = result?;
                acc_symbols.extend(symbols);
                acc_numbers.extend(numbers);
                Ok((acc_symbols, acc_numbers))
            },
        )?;

        Ok(Self { symbols, numbers })
    }
}

/*
For part 1, find the sum of all part numbers.

A part number is any number adjacent to a symbol, cardinal or diagonal.
*/

impl SchematicNumber {
    /// Generate coordinates around a number as points that are adjacent to the number.
    fn adjacent_points(&self) -> impl Iterator<Item = Point2<Dimension>> {
        // TODO should offsets have checked add/sub?
        let top_y = self.start_coords.y - 1;
        let bottom_y = self.start_coords.y + 1;
        let left_x = self.start_coords.x - 1;
        let right_x = self.start_coords.x + Dimension::from(self.width);

        let top_side = (left_x..right_x).map(move |x| Point2::new(x, top_y));
        let right_side = (top_y..bottom_y).map(move |y| Point2::new(right_x, y));
        let bottom_side = (left_x + 1..=right_x)
            .rev()
            .map(move |x| Point2::new(x, bottom_y));
        let left_side = (top_y + 1..=bottom_y)
            .rev()
            .map(move |y| Point2::new(left_x, y));

        top_side
            .chain(right_side)
            .chain(bottom_side)
            .chain(left_side)
    }
}

impl Schematic {
    fn find_part_numbers(&self) -> impl Iterator<Item = PartNumber> {
        // hash symbol coordinates for fast lookup
        let hashed_symbol_coords: HashSet<_> =
            self.symbols.iter().map(|s_sym| s_sym.coords).collect();

        self.numbers.iter().filter_map(move |s_num| {
            s_num
                .adjacent_points()
                .any(|point| hashed_symbol_coords.contains(&point))
                .then_some(s_num.value)
        })
    }
}

struct Day03;

impl Solution<PartOne> for Day03 {
    type Input = Schematic;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .find_part_numbers()
            .map(Self::Output::from)
            .checked_sum()
            .expect("should not have integer overflow during summation");
        Ok(sum)
    }
}

/*
For part 2, find the sum of all gear ratios.

A gear is a `*` symbol that is adjacent to exactly two part numbers. A gear ratio is calculated by
multiplying the two part numbers of the gear.
*/

/// Type for gear ratios in schematic.
///
/// With [`PartNumber`] expected to hold at most a 3 digit number, this is sized to hold a 6 digit
/// number (as its a multiple of two part numbers).
type GearRatio = u32;

impl Schematic {
    fn find_gear_ratios(&self) -> impl Iterator<Item = GearRatio> {
        // hash likely gear coordinates for fast lookup
        let hashed_gear_candidate_coords: HashSet<_> = self
            .symbols
            .iter()
            .filter_map(|s_sym| (s_sym.symbol == '*').then_some(s_sym.coords))
            .collect();

        let gears_with_number_values = self
            .numbers
            .iter()
            .flat_map(|s_num| {
                s_num.adjacent_points().filter_map(|point| {
                    hashed_gear_candidate_coords
                        .contains(&point)
                        .then_some((point, s_num.value))
                })
            })
            .fold(
                HashMap::<Point2<Dimension>, Vec<PartNumber>>::new(),
                |mut acc, (point, number_value)| {
                    let entry = acc.entry(point).or_insert(Vec::new());
                    // if we're under 2, track the number; if we're at 2, want to push so it's later
                    // considered invalid and skipped
                    if entry.len() <= 2 {
                        entry.push(number_value);
                    }
                    acc
                },
            );

        gears_with_number_values
            .into_iter()
            .filter_map(|(_point, number_values)| {
                (number_values.len() == 2).then(|| {
                    number_values
                        .iter()
                        .map(|&number_value| GearRatio::from(number_value))
                        .product()
                })
            })
    }
}

impl Solution<PartTwo> for Day03 {
    type Input = Schematic;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .find_gear_ratios()
            .checked_sum()
            .expect("should not have integer overflow during summation");
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"467..114..
...*......
..35..633.
......#...
617*......
.....+.58.
..592.....
......755.
...$.*....
.664.598..
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Schematic::parse(EXAMPLE_INPUT)?;
        let result = <Day03 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 4361);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Schematic::parse(EXAMPLE_INPUT)?;
        let result = <Day03 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 467_835);
        Ok(())
    }
}

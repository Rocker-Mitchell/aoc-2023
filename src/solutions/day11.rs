use std::collections::HashSet;
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::Point2;

#[solution_runner(
    name = "Day 11: Cosmic Expansion",
    parsed = InputImage,
    part_one = Day11,
    part_two = Day11
)]
impl super::AdventOfCode2023<11> {}

/*
Input is an image formatted into a character grid. There are `.` for empty space and `#` to
represent galaxies.
*/

/// The input observatory image, parsed from a character grid.
///
/// Dimensions reach 140 in observed input, so values are typed to hold at least that large a
/// number.
#[derive(Debug)]
struct InputImage {
    /// Positions of galaxies from the input.
    galaxies: Vec<Point2<u8>>,

    /// Columns/x-coordinates that do not contain galaxies.
    ///
    /// Tracked in an ascending sequence.
    empty_columns: Vec<u8>,
    /// Rows/y-coordinates that do not contain galaxies.
    ///
    /// Tracked in an ascending sequence.
    empty_rows: Vec<u8>,
}

/// An error when parsing input into [`InputImage`].
#[derive(thiserror::Error, Debug)]
enum ParseInputImageError {
    #[error("too many lines to represent y coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("unexpected character in input: {0:?}")]
    UnexpectedChar(char),
}

impl ParseData for InputImage {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let height =
            u8::try_from(input.lines().count()).map_err(ParseInputImageError::LineIndexOverflow)?;
        // use parse_input_lines to report which line fails if there's an error formatting char
        // count
        let line_widths: Vec<_> = parse_input_lines(input, |_, line| {
            u8::try_from(line.chars().count()).map_err(ParseInputImageError::CharIndexOverflow)
        })
        .collect::<Result<_, _>>()?;
        let width = line_widths.into_iter().max().unwrap_or(0);

        let grid: Vec<_> = parse_input_lines(input, |line_index, line| {
            let y = u8::try_from(line_index)
                .expect("would already raise error from calculating height");

            line.char_indices()
                .filter_map(|(char_index, c)| match c {
                    '#' => {
                        // track galaxy position
                        let x = u8::try_from(char_index)
                            .expect("would already raise error from calculating width");
                        Some(Ok(Point2::new(x, y)))
                    }
                    '.' => None, // ignore empty space
                    _ => Some(Err(ParseInputImageError::UnexpectedChar(c))),
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<_, _>>()?;
        let galaxies: Vec<_> = grid.into_iter().flatten().collect();

        let (used_columns, used_rows) = galaxies.iter().fold(
            (HashSet::new(), HashSet::new()),
            |(mut acc_columns, mut acc_rows), position| {
                acc_columns.insert(position.x);
                acc_rows.insert(position.y);
                (acc_columns, acc_rows)
            },
        );
        let empty_columns = (0..width).filter(|x| !used_columns.contains(x)).collect();
        let empty_rows = (0..height).filter(|y| !used_rows.contains(y)).collect();

        Ok(Self {
            galaxies,
            empty_columns,
            empty_rows,
        })
    }
}

/*
For part 1, factor for cosmic expansion then find the sum of lengths of shortest paths between
pairs of galaxies.

Cosmic expansion is applied by doubling all rows and columns that have no galaxies.

A path between galaxies is expected to be a number of steps across grid cells in cardinal directions
to end at the other galaxy.

> Manhattan distance should be appropriate for shortest path length.
*/

impl InputImage {
    /// Count the number of empty coordinate axes that come before a given galaxy position.
    ///
    /// # Returns
    ///
    /// A tuple of `(count_x, count_y)`.
    fn count_empty_coords_before(&self, position: Point2<u8>) -> (u8, u8) {
        /// With a sorted numbers slice of unique integers and a value that's not contained,
        /// determine the count of numbers in the slice less than the value.
        fn count_below(sorted_numbers: &[u8], value: u8) -> usize {
            match sorted_numbers.binary_search(&value) {
                Err(pos) => pos,
                Ok(_) => unreachable!(),
            }
        }

        let count_x = u8::try_from(count_below(&self.empty_columns, position.x))
            .expect("length of columns should already be within validated width");
        let count_y = u8::try_from(count_below(&self.empty_rows, position.y))
            .expect("length of rows should already be within validated height");

        (count_x, count_y)
    }

    /// Calculate positions of galaxies after applying cosmic expansion as described for part 1.
    fn part_one_expanded_galaxies(&self) -> Vec<Point2<u8>> {
        self.galaxies
            .iter()
            .map(|position| {
                // add the count of empty coordinates before position to effectively double each
                // empty coordinates' size as expansion
                let (offset_x, offset_y) = self.count_empty_coords_before(*position);
                let new_x = position
                    .x
                    .checked_add(offset_x)
                    .expect("offset of x should not overflow");
                let new_y = position
                    .y
                    .checked_add(offset_y)
                    .expect("offset of y should not overflow");

                Point2::new(new_x, new_y)
            })
            .collect()
    }
}

struct Day11;

impl Solution<PartOne> for Day11 {
    type Input = InputImage;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        /// Calculate the Manhattan distance between two positions.
        fn manhattan_distance(p1: Point2<u8>, p2: Point2<u8>) -> u16 {
            let dx = u16::from(p1.x.abs_diff(p2.x));
            let dy = u16::from(p1.y.abs_diff(p2.y));
            dx.checked_add(dy)
                .expect("manhattan distance calculation should not overflow")
        }

        let mut sum: Self::Output = 0;

        let expanded_galaxies = input.part_one_expanded_galaxies();
        // iterate unique pairs of galaxy positions
        for (index, a) in expanded_galaxies.iter().enumerate() {
            for b in &expanded_galaxies[index + 1..] {
                sum = sum
                    .checked_add(Self::Output::from(manhattan_distance(*a, *b)))
                    .expect("summing distances should not overflow");
            }
        }

        Ok(sum)
    }
}

/*
For part 2, cosmic expansion is significantly larger: every row/column without galaxies should be
replaced with 1,000,000 rows/columns.

Continue to calculate the sum of lengths of shortest paths between pairs of galaxies.
*/

impl InputImage {
    /// Calculate positions of galaxies after applying cosmic expansion as described for part 2.
    fn part_two_expanded_galaxies(&self) -> Vec<Point2<u32>> {
        self.galaxies
            .iter()
            .map(|position| {
                // the offset is the count of the empty coordinates before position multiplied by
                // 999,999 to have each empty coordinate effectively be multiplied by 1,000,000
                let (count_x, count_y) = self.count_empty_coords_before(*position);
                let offset_x = 999_999_u32 * u32::from(count_x);
                let offset_y = 999_999_u32 * u32::from(count_y);

                // shouldn't need to care about overflow; approximate max of 256e6 fits u32
                let new_x = u32::from(position.x) + offset_x;
                let new_y = u32::from(position.y) + offset_y;

                Point2::new(new_x, new_y)
            })
            .collect()
    }
}

impl Solution<PartTwo> for Day11 {
    type Input = InputImage;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        /// Calculate the Manhattan distance between two positions.
        fn manhattan_distance(p1: Point2<u32>, p2: Point2<u32>) -> u32 {
            let dx = p1.x.abs_diff(p2.x);
            let dy = p1.y.abs_diff(p2.y);
            dx.checked_add(dy)
                .expect("manhattan distance calculation should not overflow")
        }

        let mut sum: Self::Output = 0;

        let expanded_galaxies = input.part_two_expanded_galaxies();
        for (index, a) in expanded_galaxies.iter().enumerate() {
            for b in &expanded_galaxies[index + 1..] {
                sum = sum
                    .checked_add(Self::Output::from(manhattan_distance(*a, *b)))
                    .expect("summing distances should not overflow");
            }
        }

        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"...#......
.......#..
#.........
..........
......#...
.#........
.........#
..........
.......#..
#...#.....
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = InputImage::parse(EXAMPLE_INPUT)?;
        let result = <Day11 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 374);
        Ok(())
    }

    #[test]
    fn part_two_solves_two_galaxy_cases() -> DynamicResult<()> {
        {
            let horizontal_input = "#.#";
            let parsed = InputImage::parse(horizontal_input)?;
            let result = <Day11 as Solution<PartTwo>>::solve(&parsed)?;
            assert_eq!(result, 1_000_001, "failed horizontal case");
        };

        {
            let vertical_input = "#\n.\n.\n#";
            let parsed = InputImage::parse(vertical_input)?;
            let result = <Day11 as Solution<PartTwo>>::solve(&parsed)?;
            assert_eq!(result, 2_000_001, "failed vertical case");
        };

        {
            let combined_input = "#....\n.....\n....#";
            let parsed = InputImage::parse(combined_input)?;
            let result = <Day11 as Solution<PartTwo>>::solve(&parsed)?;
            assert_eq!(result, 4_000_002, "failed combined axes case");
        };

        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = InputImage::parse(EXAMPLE_INPUT)?;
        let result = <Day11 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 82_000_210);
        Ok(())
    }
}

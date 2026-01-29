use std::collections::{HashMap, HashSet};
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 14: Parabolic Reflector Dish",
    parsed = Platform,
    part_one = Day14,
    part_two = Day14
)]
impl super::AdventOfCode2023<14> {}

/*
Input is a character grid of rock placements on a platform: `O` for round rocks, `#` for cubed
rocks, and `.` for empty space.
*/

#[derive(Debug, Clone)]
struct Platform {
    /// The width of the platform, or the number of columns from the input character grid.
    width: i32,
    /// The length of the platform, or the number of rows from the input character grid.
    length: i32,
    /// Positions of round rocks on the platform.
    round_rocks: HashSet<Point2<i32>>,
    /// Positions of cubed rocks on the platform.
    cubed_rocks: HashSet<Point2<i32>>,
}

#[derive(thiserror::Error, Debug)]
enum ParsePlatformError {
    #[error("too many lines to represent y coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("expected grid width to be {expected} across rows, but found row width {found}")]
    UnequalGridWidth { expected: i32, found: i32 },

    #[error("invalid character in grid: {0:?}")]
    InvalidChar(char),
}

impl ParseData for Platform {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let length =
            i32::try_from(input.lines().count()).map_err(ParsePlatformError::LineIndexOverflow)?;
        let mut width_opt = None;
        let mut round_rocks = HashSet::new();
        let mut cubed_rocks = HashSet::new();

        parse_input_lines(input, |line_index, line| {
            let line_width = i32::try_from(line.chars().count())
                .map_err(ParsePlatformError::CharIndexOverflow)?;
            if let Some(expected_width) = width_opt {
                if line_width != expected_width {
                    return Err(ParsePlatformError::UnequalGridWidth {
                        expected: expected_width,
                        found: line_width,
                    });
                }
            } else {
                width_opt = Some(line_width);
            }

            let y =
                i32::try_from(line_index).expect("validated range conversion earlier for length");

            for (char_index, character) in line.char_indices() {
                let x = i32::try_from(char_index)
                    .expect("validated range conversion earlier for line_width");

                match character {
                    '.' => {} // ignore
                    'O' => {
                        round_rocks.insert(Point2::new(x, y));
                    }
                    '#' => {
                        cubed_rocks.insert(Point2::new(x, y));
                    }
                    _ => return Err(ParsePlatformError::InvalidChar(character)),
                }
            }
            Ok(())
        })
        .collect::<Result<(), _>>()?;

        Ok(Self {
            // there'd be no width if there were no lines to parse; default to 0
            width: width_opt.unwrap_or(0),
            length,
            round_rocks,
            cubed_rocks,
        })
    }
}

/*
The platform can shift angle to roll round rocks in a cardinal direction. Round rocks roll until
they are blocked by an obstruction, namely the platform edge, cubed rocks, or other obstructed round
rocks.

For part 1, tilt the platform to roll round rocks north, then calculate the total load on the north.

A round rock applies north load as the number of rows from that rock to the south edge (rock's row
inclusive). Cubed rocks don't apply.
*/

impl Platform {
    fn tilt_north(&mut self) {
        for x in 0..self.width {
            // scanning from north to south
            for y in 0..self.length {
                let point = Point2::new(x, y);

                // move any round rock
                if self.round_rocks.remove(&point) {
                    // move up until an obstruction is detected
                    for search_y in (-1..y).rev() {
                        let search_point = Point2::new(x, search_y);
                        if search_y < 0
                            || self.cubed_rocks.contains(&search_point)
                            || self.round_rocks.contains(&search_point)
                        {
                            let new_point = search_point + Vector2::y();
                            assert!(
                                self.round_rocks.insert(new_point),
                                "new point for round rock already contained"
                            );
                            break;
                        }
                    }
                }
            }
        }
    }

    fn north_load(&self) -> u32 {
        self.round_rocks
            .iter()
            .map(|rock_point| {
                let load = self.length - rock_point.y;
                u32::try_from(load).expect("load should be castable to unsigned")
            })
            .checked_sum()
            .expect("summing north load should not overflow")
    }
}

struct Day14;

impl Solution<PartOne> for Day14 {
    type Input = Platform;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut clone = input.clone();
        clone.tilt_north();
        Ok(clone.north_load())
    }
}

/*
The platform can "spin cycle", tilting four times: north, west, south, and finally east.

For part 2, cycle the platform 1,000,000,000 times and recalculate the total north load.
*/

#[derive(Debug, Clone, Copy)]
enum Direction {
    North,
    East,
    South,
    West,
}

impl Direction {
    fn to_vector2(self) -> Vector2<i32> {
        match self {
            Self::North => Vector2::y() * -1,
            Self::East => Vector2::x(),
            Self::South => Vector2::y(),
            Self::West => Vector2::x() * -1,
        }
    }
}

impl Platform {
    /// Get an iterator of positions on the platform that guarantees contiguous scans starting from
    /// `direction`'s edge.
    ///
    /// An outer loop is iterated of the perpendicular coordinate, then an inner loop is iterated of
    /// the parallel coordinate, and the inner loop starts from the `direction` edge and iterates to
    /// the opposite edge.
    fn iterate_points_from_edge(
        &self,
        edge_direction: Direction,
    ) -> Box<dyn Iterator<Item = Point2<i32>> + '_> {
        // inner coord loop is critical as it should start from the edge tilted toward/iterating
        // from
        match edge_direction {
            Direction::North => Box::new(
                (0..self.width).flat_map(|x| (0..self.length).map(move |y| Point2::new(x, y))),
            ),
            Direction::East => Box::new(
                (0..self.length)
                    .flat_map(|y| (0..self.width).rev().map(move |x| Point2::new(x, y))),
            ),
            Direction::South => Box::new(
                (0..self.width)
                    .flat_map(|x| (0..self.length).rev().map(move |y| Point2::new(x, y))),
            ),
            Direction::West => Box::new(
                (0..self.length).flat_map(|y| (0..self.width).map(move |x| Point2::new(x, y))),
            ),
        }
    }

    /// Get an iterator of points that start from the `point` exclusively, and continues in the
    /// `direction` up to after the edge of the platform inclusively (i.e. `y == -1` for North,
    /// `x == -1` for West, `y == self.length` for South, `x == self.width` for East).
    fn iterate_after_point_to_after_edge(
        &self,
        point: Point2<i32>,
        edge_direction: Direction,
    ) -> Box<dyn Iterator<Item = Point2<i32>> + '_> {
        match edge_direction {
            Direction::North => {
                let x = point.x;
                Box::new((-1..point.y).rev().map(move |y| Point2::new(x, y)))
            }
            Direction::East => {
                let y = point.y;
                Box::new((point.x + 1..=self.width).map(move |x| Point2::new(x, y)))
            }
            Direction::South => {
                let x = point.x;
                Box::new((point.y + 1..=self.length).map(move |y| Point2::new(x, y)))
            }
            Direction::West => {
                let y = point.y;
                Box::new((-1..point.x).rev().map(move |x| Point2::new(x, y)))
            }
        }
    }

    /// Tilt the platform to move round rocks toward the `direction`.
    fn tilt(&mut self, direction: Direction) {
        // iterate with contiguous scans from the direction edge to the opposite edge
        let area_points: Vec<_> = self.iterate_points_from_edge(direction).collect();
        for point in area_points {
            // move any round rock at the point
            if self.round_rocks.remove(&point) {
                // search from next to point to direction edge
                let search_sequence: Vec<_> = self
                    .iterate_after_point_to_after_edge(point, direction)
                    .collect();

                // the obstructing point can be a rock along the search sequence within the bounds,
                // or falls back to the last point in the sequence which should be just after an
                // edge
                let obstructing_point = search_sequence[..search_sequence.len() - 1]
                    .iter()
                    .find(|&search_point_ref| {
                        self.cubed_rocks.contains(search_point_ref)
                            || self.round_rocks.contains(search_point_ref)
                    })
                    .unwrap_or(&search_sequence[search_sequence.len() - 1]);

                // moving to point just before obstruction
                let new_point = obstructing_point - direction.to_vector2();
                assert!(
                    self.round_rocks.insert(new_point),
                    "new point for round rock already contained"
                );
            }
        }
    }

    /// Cycle through tilts of the platform.
    fn cycle(&mut self) {
        for direction in [
            Direction::North,
            Direction::West,
            Direction::South,
            Direction::East,
        ] {
            self.tilt(direction);
        }
    }
}

impl Solution<PartTwo> for Day14 {
    type Input = Platform;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut clone = input.clone();
        let mut seen = HashMap::new();

        let target: u32 = 1_000_000_000;
        for index in 0..target {
            let mut sorted_rock_coords: Vec<_> =
                clone.round_rocks.iter().map(|p| (p.x, p.y)).collect();
            sorted_rock_coords.sort_unstable();

            // thanks copilot for this technique to detect repeating cycle to factor out
            if let Some(previous_index) = seen.get(&sorted_rock_coords) {
                // this state has been seen before, a repeating cycle is detected;
                // project to how much iterations would remain if we take chunks of the cycle length
                // out of the target
                let cycle_length = index - previous_index;
                let remaining = (target - index) % cycle_length;

                for _ in 0..remaining {
                    clone.cycle();
                }
                return Ok(clone.north_load());
            }

            seen.insert(sorted_rock_coords, index);
            clone.cycle();
        }

        Ok(clone.north_load())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"O....#....
O.OO#....#
.....##...
OO.#O....O
.O.....O#.
O.#..O.#.#
..O..#O..O
.......O..
#....###..
#OO..#....
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Platform::parse(EXAMPLE_INPUT)?;
        let result = <Day14 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 136);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Platform::parse(EXAMPLE_INPUT)?;
        let result = <Day14 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 64);
        Ok(())
    }
}

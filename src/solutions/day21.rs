use std::collections::{HashMap, HashSet, VecDeque};
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 21: Step Counter",
    parsed = GardenMap,
    part_one = Day21,
    part_two = Day21
)]
impl super::AdventOfCode2023<21> {}

/*
Input is a character grid mapping garden plots: `S` for a start position, `.` for plots, `#` for
rocks. The start also acts as a plot.
*/

/// A map of garden plots.
#[derive(Debug)]
struct GardenMap {
    /// The number of columns in the map.
    width: i32,
    /// The number of rows in the map.
    height: i32,
    /// The positions of rocks in the map.
    rocks: HashSet<Point2<i32>>,
    /// The starting position in the map.
    start: Point2<i32>,
}

#[derive(thiserror::Error, Debug)]
enum ParseGardenMapError {
    #[error("too many lines to represent y-coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x-coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("expected grid width to be {expected} across rows, but found row width {found}")]
    UnequalGridWidth { expected: i32, found: i32 },

    #[error("invalid character in grid: {0:?}")]
    InvalidChar(char),

    #[error("found another start point after {first}: {second}")]
    MultipleStarts {
        first: Point2<i32>,
        second: Point2<i32>,
    },

    #[error("failed to find a start point")]
    MissingStart,
}

impl ParseData for GardenMap {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let height =
            i32::try_from(input.lines().count()).map_err(ParseGardenMapError::LineIndexOverflow)?;

        let mut width_opt = None;
        let mut start_opt = None;
        let mut rocks = HashSet::new();

        parse_input_lines(input, |line_index, line| {
            let line_width = i32::try_from(line.chars().count())
                .map_err(ParseGardenMapError::CharIndexOverflow)?;
            if let Some(expected_width) = width_opt {
                if line_width != expected_width {
                    return Err(ParseGardenMapError::UnequalGridWidth {
                        expected: expected_width,
                        found: line_width,
                    });
                }
            } else {
                width_opt = Some(line_width);
            }

            let y =
                i32::try_from(line_index).expect("validated range conversion earlier for height");

            for (ch_index, ch) in line.char_indices() {
                let x = i32::try_from(ch_index)
                    .expect("validated range conversion earlier for line_width");

                match ch {
                    '.' => {} // ignore
                    '#' => {
                        rocks.insert(Point2::new(x, y));
                    }
                    'S' => {
                        if let Some(existing_start) = start_opt {
                            return Err(ParseGardenMapError::MultipleStarts {
                                first: existing_start,
                                second: Point2::new(x, y),
                            });
                        }
                        start_opt = Some(Point2::new(x, y));
                    }
                    _ => return Err(ParseGardenMapError::InvalidChar(ch)),
                }
            }

            Ok(())
        })
        .collect::<Result<(), _>>()?;

        start_opt.map_or_else(
            || Err(ParseGardenMapError::MissingStart.into()),
            |start| {
                Ok(Self {
                    width: width_opt.unwrap_or(0),
                    height,
                    rocks,
                    start,
                })
            },
        )
    }
}

/*
Plots can be navigated cardinally as individual steps onto plots but not rocks. The path traveled
can be backtracked.

For part 1, count how many plots can be reached in exactly 64 steps.

> Paths to a plot should not be uniquely counted, only the ends of paths.
*/

fn is_even(value: u32) -> bool {
    (value & 1) == 0
}

impl GardenMap {
    /// Determine if a point is in the bounds of the map.
    fn point_in_bounds(&self, point: Point2<i32>) -> bool {
        point.x >= 0 && point.x < self.width && point.y >= 0 && point.y < self.height
    }

    fn distances_to_plots(&self) -> HashMap<Point2<i32>, u32> {
        // breadth-first search for shortest distances
        let mut queue = VecDeque::new();
        let mut visited = HashMap::new();

        queue.push_back((self.start, 0u32));
        visited.insert(self.start, 0u32);

        while let Some((point, distance)) = queue.pop_front() {
            let next_distance = distance + 1;
            // visit cardinal directions
            for neighbor in [
                Vector2::x(),
                Vector2::y(),
                Vector2::x() * -1,
                Vector2::y() * -1,
            ]
            .into_iter()
            .map(|direction| point + direction)
            {
                // filter for bounds, no rocks, and not visited
                if self.point_in_bounds(neighbor)
                    && !self.rocks.contains(&neighbor)
                    && !visited.contains_key(&neighbor)
                {
                    visited.insert(neighbor, next_distance);
                    queue.push_back((neighbor, next_distance));
                }
            }
        }

        visited
    }

    /// Count plots reached with exact steps as described in part 1.
    fn count_plots_from_exact_steps_part_one(&self, steps: u32) -> u32 {
        let count_evens = is_even(steps);
        let distances = self.distances_to_plots();
        distances
            .values()
            .filter(|v| is_even(**v) == count_evens && **v <= steps)
            .count()
            .try_into()
            .expect("count should fit u32")
    }
}

struct Day21;

impl Solution<PartOne> for Day21 {
    type Input = GardenMap;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(input.count_plots_from_exact_steps_part_one(64))
    }
}

/*
For part 2, scale up to 26501365 steps. Also, instead of bounding steps inside the map, assume the
map is one tile that repeats in directions infinitely (substituting repeating starts with plots).
*/

// referencing someone else's explanation to figure out the secret real puzzle context that the site
// doesn't actually tell you ugh: https://github.com/villuna/aoc23/wiki/A-Geometric-solution-to-advent-of-code-2023,-day-21

impl GardenMap {
    /// Count plots reached with exact steps as described in part 2.
    ///
    /// # Arguments
    ///
    /// Instead of accepting steps, this expects the number of whole map tile layers iterated,
    /// assuming the start is in the center of the map. Layer 0 is the map itself (1x1), layer 1
    /// adds a perimeter of map tiles around the original (3x3), layer 2 another perimeter around
    /// the former (5x5), etc.
    fn count_plots_from_exact_steps_part_two(&self, tile_layers: u32) -> u64 {
        let half_width = u32::try_from(self.width).expect("width should fit u32") / 2;
        let distances = self.distances_to_plots();

        // counts over the whole map
        let full_even = u64::try_from(distances.values().filter(|v| is_even(**v)).count())
            .expect("full_even count should fit u64");
        let full_odd = u64::try_from(distances.values().filter(|v| !is_even(**v)).count())
            .expect("full_odd count should fit u32");

        // counts over the outer corners when forming a diamond that touches the edges
        let outer_corners_even = u64::try_from(
            distances
                .values()
                .filter(|v| is_even(**v) && **v > half_width)
                .count(),
        )
        .expect("outer_corners_even should fit u64");
        let outer_corners_odd = u64::try_from(
            distances
                .values()
                .filter(|v| !is_even(**v) && **v > half_width)
                .count(),
        )
        .expect("outer_corners_odd count should fit u64");

        let tile_layers = u64::from(tile_layers);
        let total_full_odd = (tile_layers + 1)
            .checked_pow(2)
            .and_then(|tile_count| tile_count.checked_mul(full_odd))
            .expect("total count from full odd tiles should not overflow");
        let total_full_even = tile_layers
            .checked_pow(2)
            .and_then(|tile_count| tile_count.checked_mul(full_even))
            .expect("total count from full even tiles should not overflow");
        let total_corner_odd: u64 = (tile_layers + 1)
            .checked_mul(outer_corners_odd)
            .expect("total count from odd tile corners should not overflow");
        let total_corner_even: u64 = tile_layers
            .checked_mul(outer_corners_even)
            .expect("total count from even tile corners should not overflow");

        [total_full_odd, total_full_even, total_corner_even]
            .into_iter()
            .checked_sum()
            .and_then(|sum| sum.checked_sub(total_corner_odd))
            .expect("final count should not overflow")
    }
}

impl Solution<PartTwo> for Day21 {
    type Input = GardenMap;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let tile_layers = u32::try_from((26_501_365 - (input.width / 2)) / input.width)
            .expect("tile_layers should fit u32");
        Ok(input.count_plots_from_exact_steps_part_two(tile_layers))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"...........
.....###.#.
.###.##..#.
..#.#...#..
....#.#....
.##..S####.
.##..#...#.
.......##..
.##.#.####.
.##..##.##.
...........
";

    #[test]
    fn part_one_count_plots_from_1_step_for_example() -> DynamicResult<()> {
        let parsed = GardenMap::parse(EXAMPLE_INPUT)?;
        assert_eq!(parsed.count_plots_from_exact_steps_part_one(1), 2);
        Ok(())
    }

    #[test]
    fn part_one_count_plots_from_2_steps_for_example() -> DynamicResult<()> {
        let parsed = GardenMap::parse(EXAMPLE_INPUT)?;
        assert_eq!(parsed.count_plots_from_exact_steps_part_one(2), 4);
        Ok(())
    }

    #[test]
    fn part_one_count_plots_from_3_steps_for_example() -> DynamicResult<()> {
        let parsed = GardenMap::parse(EXAMPLE_INPUT)?;
        assert_eq!(parsed.count_plots_from_exact_steps_part_one(3), 6);
        Ok(())
    }

    #[test]
    fn part_one_count_plots_from_6_steps_for_example() -> DynamicResult<()> {
        let parsed = GardenMap::parse(EXAMPLE_INPUT)?;
        assert_eq!(parsed.count_plots_from_exact_steps_part_one(6), 16);
        Ok(())
    }
}

use std::collections::{HashMap, HashSet, VecDeque};
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 16: The Floor Will Be Lava",
    parsed = Contraption,
    part_one = Day16,
    part_two = Day16
)]
impl super::AdventOfCode2023<16> {}

/*
Input is a character grid of a contraption layout containing mirrors and splitters.

`.` is empty space, `/` & `\` are mirrors, and `|` & `-` are splitters. The multiple characters for
mirrors and splitter indicate its orientation.
*/

/// A mirror in the contraption.
#[derive(Debug, Clone, Copy)]
enum Mirror {
    /// Forward leaning, with ends in the top-right and bottom-left.
    Forward,
    /// Backward leaning, with ends in the top-left and bottom-right.
    Backward,
}

/// A splitter in the contraption.
#[derive(Debug, Clone, Copy)]
enum Splitter {
    /// Oriented vertically, with ends on the top and bottom.
    Vertical,
    /// Oriented horizontally, with ends on the left and right.
    Horizontal,
}

#[derive(Debug)]
struct Contraption {
    /// The number of columns in the contraption grid.
    width: i32,
    /// The number of rows in the contraption grid.
    height: i32,
    /// The mirrors in the contraption by position.
    mirrors: HashMap<Point2<i32>, Mirror>,
    /// The splitters in the contraption by position.
    splitters: HashMap<Point2<i32>, Splitter>,
}

#[derive(thiserror::Error, Debug)]
enum ParseContraptionError {
    #[error("too many lines to represent y-coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x-coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("expected grid width to be {expected} across rows, but found row width {found}")]
    UnequalGridWidth { expected: i32, found: i32 },

    #[error("invalid character in grid: {0:?}")]
    InvalidChar(char),
}

impl ParseData for Contraption {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let height = i32::try_from(input.lines().count())
            .map_err(ParseContraptionError::LineIndexOverflow)?;

        let mut width_opt = None;
        let mut mirrors = HashMap::new();
        let mut splitters = HashMap::new();

        parse_input_lines(input, |line_index, line| {
            let line_width = i32::try_from(line.chars().count())
                .map_err(ParseContraptionError::CharIndexOverflow)?;
            if let Some(expected_width) = width_opt {
                if line_width != expected_width {
                    return Err(ParseContraptionError::UnequalGridWidth {
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
                    '/' => {
                        mirrors.insert(Point2::new(x, y), Mirror::Forward);
                    }
                    '\\' => {
                        mirrors.insert(Point2::new(x, y), Mirror::Backward);
                    }
                    '|' => {
                        splitters.insert(Point2::new(x, y), Splitter::Vertical);
                    }
                    '-' => {
                        splitters.insert(Point2::new(x, y), Splitter::Horizontal);
                    }
                    _ => return Err(ParseContraptionError::InvalidChar(ch)),
                }
            }
            Ok(())
        })
        .collect::<Result<(), _>>()?;

        Ok(Self {
            width: width_opt.unwrap_or(0),
            height,
            mirrors,
            splitters,
        })
    }
}

/*
For part 1, a beam enters the contraption from the left into the top-left corner.

Mirrors reflect the beam 90 degrees, depending on the orientation (e.g. beam moving right reflects
up with `/` or down with `\`). Splitters generate beams out of its ends when the beam enters a flat
side (e.g. beam moving right splits up and down with `|`), otherwise behaves like empty space when
entering from one end (e.g. beam moving right continues through `-`). Beams don't interact with each
other.

A tile in the grid is energized if at least one beam passes through it (including where beams
reflect and split).

Determine how many tiles are energized.
*/

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum BeamDirection {
    Up,
    Right,
    Down,
    Left,
}

impl BeamDirection {
    fn to_vector2(self) -> Vector2<i32> {
        match self {
            Self::Up => Vector2::y() * -1,
            Self::Right => Vector2::x(),
            Self::Down => Vector2::y(),
            Self::Left => Vector2::x() * -1,
        }
    }
}

impl Mirror {
    // Get the direction reflected by the mirror.
    fn reflect(self, direction: BeamDirection) -> BeamDirection {
        match (self, direction) {
            (Self::Forward, BeamDirection::Up) | (Self::Backward, BeamDirection::Down) => {
                BeamDirection::Right
            }
            (Self::Forward, BeamDirection::Right) | (Self::Backward, BeamDirection::Left) => {
                BeamDirection::Up
            }
            (Self::Forward, BeamDirection::Down) | (Self::Backward, BeamDirection::Up) => {
                BeamDirection::Left
            }
            (Self::Forward, BeamDirection::Left) | (Self::Backward, BeamDirection::Right) => {
                BeamDirection::Down
            }
        }
    }
}

impl Splitter {
    /// Get new directions split from the splitter. If the direction does not create a split,
    /// returns `None`.
    fn split(self, direction: BeamDirection) -> Option<(BeamDirection, BeamDirection)> {
        match (self, direction) {
            (Self::Vertical, BeamDirection::Right | BeamDirection::Left) => {
                Some((BeamDirection::Up, BeamDirection::Down))
            }
            (Self::Horizontal, BeamDirection::Up | BeamDirection::Down) => {
                Some((BeamDirection::Right, BeamDirection::Left))
            }
            _ => None,
        }
    }
}

impl Contraption {
    /// Find if the point lies outside the bounds of this contraption.
    fn is_out_of_bounds(&self, point: Point2<i32>) -> bool {
        point.x < 0 || point.x >= self.width || point.y < 0 || point.y >= self.height
    }

    /// Find the number of tiles that have at least one beam pass through them, starting a beam from
    /// the given point and direction.
    fn energized_count(&self, start_point: Point2<i32>, start_direction: BeamDirection) -> usize {
        fn push_next(
            queue: &mut VecDeque<(Point2<i32>, BeamDirection)>,
            old_point: Point2<i32>,
            new_direction: BeamDirection,
        ) {
            let new_point = old_point + new_direction.to_vector2();
            queue.push_back((new_point, new_direction));
        }

        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back((start_point, start_direction));

        while let Some((point, direction)) = queue.pop_front() {
            // skip if
            // - point lies out of bounds
            // - beam was already encountered, suggesting a closed loop
            if !self.is_out_of_bounds(point) && visited.insert((point, direction)) {
                // evaluate tile to push next beam(s) to queue
                if let Some(mirror) = self.mirrors.get(&point) {
                    let new_direction = mirror.reflect(direction);
                    push_next(&mut queue, point, new_direction);
                } else if let Some(splitter) = self.splitters.get(&point)
                    && let Some((direction_one, direction_two)) = splitter.split(direction)
                {
                    push_next(&mut queue, point, direction_one);
                    push_next(&mut queue, point, direction_two);
                } else {
                    push_next(&mut queue, point, direction);
                }
            }
        }

        // count unique points of beams visited
        visited
            .into_iter()
            .map(|(point, _)| point)
            .collect::<HashSet<_>>()
            .len()
    }
}

struct Day16;

impl Solution<PartOne> for Day16 {
    type Input = Contraption;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let energized =
            Self::Output::try_from(input.energized_count(Point2::origin(), BeamDirection::Right))
                .expect("energized count should fit in output type");
        Ok(energized)
    }
}

/*
For part 2, determine the optimal beam entry point that yields the largest energized count, and
return that count.

Beams can enter any edge of the contraption in a direction away from that edge. So, corner tiles can
have beams enter from the two edges they touch.
*/

impl Solution<PartTwo> for Day16 {
    type Input = Contraption;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let horizontal_edges = (0..input.width).flat_map(|x| {
            [
                (Point2::new(x, 0), BeamDirection::Down),
                (Point2::new(x, input.height - 1), BeamDirection::Up),
            ]
        });
        let vertical_edges = (0..input.height).flat_map(|y| {
            [
                (Point2::new(0, y), BeamDirection::Right),
                (Point2::new(input.width - 1, y), BeamDirection::Left),
            ]
        });
        let beam_starts = horizontal_edges.chain(vertical_edges);

        let max_energized = Self::Output::try_from(
            beam_starts
                .map(|(point, direction)| input.energized_count(point, direction))
                .max()
                .expect("beam_starts should not be empty"),
        )
        .expect("energized count should fit in output type");
        Ok(max_energized)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r".|...\....
|.-.\.....
.....|-...
........|.
..........
.........\
..../.\\..
.-.-/..|..
.|....-|.\
..//.|....
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Contraption::parse(EXAMPLE_INPUT)?;
        let result = <Day16 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 46);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Contraption::parse(EXAMPLE_INPUT)?;
        let result = <Day16 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 51);
        Ok(())
    }
}

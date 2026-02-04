use std::num::ParseIntError;
use std::str::FromStr;

use aoc_framework::parsing::{ParseContextError, parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 18: Lavaduct Lagoon",
    parsed = DigPlan,
    part_one = Day18,
    part_two = Day18
)]
impl super::AdventOfCode2023<18> {}

/*
Input is a dig plan for a lagoon, as lines of dig instructions.

Each line has three properties, space separated:
1. A dig direction as seen from above: up (`U`), down (`D`), left (`L`), right (`R`)
2. A dig distance number
3. A hexadecimal color code in parentheses
*/

#[derive(Debug, Clone, Copy)]
enum Direction {
    Up,
    Down,
    Left,
    Right,
}

#[derive(thiserror::Error, Debug)]
enum ParseDirectionError {
    #[error("failed to parse a valid direction (\"U\", \"D\", \"L\", or \"R\")")]
    InvalidDirection,
}

impl FromStr for Direction {
    type Err = ParseDirectionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "U" => Ok(Self::Up),
            "D" => Ok(Self::Down),
            "L" => Ok(Self::Left),
            "R" => Ok(Self::Right),
            _ => Err(ParseDirectionError::InvalidDirection),
        }
    }
}

#[derive(Debug)]
struct DigInstruction {
    direction: Direction,
    distance: u64,
}

#[derive(thiserror::Error, Debug)]
enum DigInstructionFromHexColorCodeError {
    #[error("expected length like hex color code (7 characters)")]
    UnexpectedLength,

    #[error("expected hash symbol prefix")]
    ExpectedHashPrefix,

    #[error("failed to parse distance value from first 5 positions")]
    ParseDistanceError(#[source] ParseIntError),

    #[error(
        "failed to map last position to a direction (expected \"0\", \"1\", \"2\", or \"3\"): {0:?}"
    )]
    InvalidValueForDirection(String),
}

impl DigInstruction {
    /// Parse dig instructions from a hex color code formatted in a string, relevant to part 2.
    fn from_hex_color_code(code: &str) -> Result<Self, DigInstructionFromHexColorCodeError> {
        if code.len() != 7 {
            return Err(DigInstructionFromHexColorCodeError::UnexpectedLength);
        }

        if !code.starts_with('#') {
            return Err(DigInstructionFromHexColorCodeError::ExpectedHashPrefix);
        }

        let distance = u64::from_str_radix(&code[1..6], 16)
            .map_err(DigInstructionFromHexColorCodeError::ParseDistanceError)?;

        let direction = match &code[6..7] {
            "0" => Direction::Right,
            "1" => Direction::Down,
            "2" => Direction::Left,
            "3" => Direction::Up,
            other => {
                return Err(
                    DigInstructionFromHexColorCodeError::InvalidValueForDirection(other.to_owned()),
                );
            }
        };

        Ok(Self {
            direction,
            distance,
        })
    }
}

struct DigPlan {
    /// Dig instructions applicable to part 1.
    part_1: Vec<DigInstruction>,
    /// Dig instructions parsed from hex color codes, applicable to part 2.
    part_2: Vec<DigInstruction>,
}

#[derive(thiserror::Error, Debug)]
enum ParseDigPlanError {
    #[error(
        "expected exactly three parts, space separated, for direction, distance, and hex color code"
    )]
    ExpectedParts,

    #[error("expected parenthesis wrapping hex color code")]
    ExpectedParenthesisWrapColor,
}

impl ParseData for DigPlan {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut part_1 = Vec::new();
        let mut part_2 = Vec::new();

        parse_input_lines(input, |_, line| -> DynamicResult<_> {
            let parts: Vec<_> = line.split(' ').collect();
            if parts.len() != 3 {
                return Err(ParseDigPlanError::ExpectedParts.into());
            }

            let direction = parse_with_context(parts[0])?;

            let distance = parse_with_context(parts[1])?;

            part_1.push(DigInstruction {
                direction,
                distance,
            });

            if !parts[2].starts_with('(') || !parts[2].ends_with(')') {
                return Err(ParseDigPlanError::ExpectedParenthesisWrapColor.into());
            }
            let hex_color_code = &parts[2][1..parts[2].len() - 1];

            part_2.push(
                DigInstruction::from_hex_color_code(hex_color_code)
                    .map_err(|source| ParseContextError::new(source, hex_color_code))?,
            );

            Ok(())
        })
        .collect::<Result<(), _>>()?;

        Ok(Self { part_1, part_2 })
    }
}

/*
For part 1, The dig plan should result in a closed loop trench, ending where it started. The
interior of the loop will be dug out after. Determine the final area dug out.
*/

// checking online, suggestions included using the shoelace formula for interior, and initially it
// sounded like Pick's theorem applied to handle the border but it seems an equation that happens to
// look similar is needed (adding 1 instead of subtracting like the theorem does)

/// Apply the shoelace formula to a sequence of points forming a simple polygon to get its area.
///
/// It is expected the last point connects back to the first to form a closed loop.
fn shoelace_area(points: &[Point2<i64>]) -> u64 {
    // specifically the triangle formula: sum of x_i*y_j - x_j*y_i, then half of its absolute value
    let n = points.len();
    let mut sum: i64 = 0;
    for i in 0..n {
        // wrap index overflow back to start
        let j = (i + 1) % n;

        let p_i = &points[i];
        let p_j = &points[j];
        sum = p_i
            .x
            .checked_mul(p_j.y)
            .and_then(|left| {
                p_j.x
                    .checked_mul(p_i.y)
                    .and_then(|right| left.checked_sub(right))
            })
            .and_then(|diff| sum.checked_add(diff))
            .expect("shoelace area calculation should not overflow");
    }

    sum.unsigned_abs() / 2
}

impl Direction {
    fn to_vector2(self) -> Vector2<i64> {
        match self {
            Self::Up => Vector2::y() * -1,
            Self::Down => Vector2::y(),
            Self::Left => Vector2::x() * -1,
            Self::Right => Vector2::x(),
        }
    }
}

/// Get the cell positions dug to when following dig instructions.
///
/// The first position is the origin (0,0), and the second is the cell dug to after following
/// the first dig instruction. This continues to the position dug to after the second to last
/// instruction; the last is omitted as its instruction should close a loop back to the origin.
///
/// Digging creates a trench 1 unit wide, so the cells dug to are 1x1 unit in size.
fn dig_corners(instructions: &[DigInstruction]) -> Vec<Point2<i64>> {
    let mut corners = Vec::new();

    let mut current = Point2::origin();
    for instruction in instructions {
        corners.push(current);
        current += instruction.direction.to_vector2()
            * i64::try_from(instruction.distance).expect("dig distance should fit i64");
    }

    assert_eq!(
        current,
        Point2::origin(),
        "last instruction did not close loop"
    );

    corners
}

/// Get the perimeter area from following dig instructions.
///
/// Digging creates a trench 1 unit wide, which is considered for the area.
fn perimeter_area(instructions: &[DigInstruction]) -> u64 {
    instructions
        .iter()
        .map(|instruction| instruction.distance)
        .checked_sum()
        .expect("perimeter area sum should not overflow")
}

/// Calculate the total area of the space dug out by the dig instructions.
fn total_area(instructions: &[DigInstruction]) -> u64 {
    // NOTE the corners calculated are cell coords, not an exact boundary around the area; it's like
    // shoelace will adapt coords to top left of cells so any right and bottom edges don't get
    // correctly measured
    // - adding half the perimeter (round down) should approximately handle this
    // NOTE theoretically if there were no instructions, there'd still be the origin cell dug so add
    // 1 for the origin, it seems
    let corners = dig_corners(instructions);
    let area = shoelace_area(&corners);
    let perimeter = perimeter_area(instructions);
    area.checked_add(perimeter / 2)
        .and_then(|sum| sum.checked_add(1))
        .expect("total area calculation should not overflow")
}

struct Day18;

impl Solution<PartOne> for Day18 {
    type Input = DigPlan;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(total_area(&input.part_1))
    }
}

/*
For part 2, dig instructions are encoded in the color parameter. The first 5 hex positions hold
distance. The last position holds direction:

- `0` - right
- `1` - down
- `2` - left
- `3` - up

Recalculate the final area from these instructions.
*/

impl Solution<PartTwo> for Day18 {
    type Input = DigPlan;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(total_area(&input.part_2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"R 6 (#70c710)
D 5 (#0dc571)
L 2 (#5713f0)
D 2 (#d2c081)
R 2 (#59c680)
D 2 (#411b91)
L 5 (#8ceee2)
U 2 (#caa173)
L 1 (#1b58a2)
U 2 (#caa171)
R 2 (#7807d2)
U 3 (#a77fa3)
L 2 (#015232)
U 2 (#7a21e3)
";

    #[test]
    fn part_one_correct_perimeter_area_from_example() -> DynamicResult<()> {
        let parsed = DigPlan::parse(EXAMPLE_INPUT)?;
        assert_eq!(perimeter_area(&parsed.part_1), 38);
        Ok(())
    }

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = DigPlan::parse(EXAMPLE_INPUT)?;
        let result = <Day18 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 62);
        Ok(())
    }

    #[test]
    fn part_one_solves_rectangle() -> DynamicResult<()> {
        let parsed = DigPlan::parse(
            r"U 3 (#000000)
L 4 (#000000)
D 3 (#000000)
R 4 (#000000)",
        )?;
        let result = <Day18 as Solution<PartOne>>::solve(&parsed)?;
        // should be a 4 by 5 rectangle
        assert_eq!(result, 4 * 5);
        Ok(())
    }

    #[test]
    fn part_one_solves_rectangle_with_notch() -> DynamicResult<()> {
        let parsed = DigPlan::parse(
            r"D 2 (#000000)
L 2 (#000000)
U 1 (#000000)
L 4 (#000000)
D 1 (#000000)
L 2 (#000000)
U 2 (#000000)
R 8 (#000000)",
        )?;
        let result = <Day18 as Solution<PartOne>>::solve(&parsed)?;
        // should have a base 3 by 9 rectangle with notch on bottom edge 3 wide and 1 deep
        assert_eq!(result, 3 * 9 - 3);
        Ok(())
    }

    #[test]
    fn part_one_solves_rectangle_with_protrusion() -> DynamicResult<()> {
        let parsed = DigPlan::parse(
            r"U 3 (#000000)
R 3 (#000000)
D 1 (#000000)
R 2 (#000000)
D 1 (#000000)
L 2 (#000000)
D 1 (#000000)
L 3 (#000000)",
        )?;
        let result = <Day18 as Solution<PartOne>>::solve(&parsed)?;
        // should have base 4 by 4 rectangle with protrusion on right edge 2 wide and 2 deep
        assert_eq!(result, 4 * 4 + 2 * 2);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = DigPlan::parse(EXAMPLE_INPUT)?;
        let result = <Day18 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 952_408_144_115);
        Ok(())
    }
}

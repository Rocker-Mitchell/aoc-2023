use std::collections::{HashMap, HashSet};
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 10: Pipe Maze",
    parsed = InputGrid,
    part_one = Day10,
    part_two = Day10
)]
impl super::AdventOfCode2023<10> {}

/*
Input is a grid of pipes and an animal that enters the pipes.

Various characters are used for representation:

- `.` is a space clear of anything relevant.
- `|` and `-` are straight pipes connecting north-south and east-west respectively.
- `L`, `J`, `7`, `F` are 90 degree bends connecting north-east, north-west, south-west, and
  south-east respectively.
- `S` marks where the animal starts.
*/

/// An enum for the types of cells in the grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GridCell {
    Empty,
    Start,
    NorthSouth,
    EastWest,
    NorthEast,
    NorthWest,
    SouthWest,
    SouthEast,
}

/// An error creating a [`GridCell`] from a [`char`].
#[derive(thiserror::Error, Debug)]
enum GridCellFromCharError {
    #[error("character is invalid for a grid cell: {0:?}")]
    InvalidChar(char),
}

impl TryFrom<char> for GridCell {
    type Error = GridCellFromCharError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Self::Empty),
            'S' => Ok(Self::Start),
            '|' => Ok(Self::NorthSouth),
            '-' => Ok(Self::EastWest),
            'L' => Ok(Self::NorthEast),
            'J' => Ok(Self::NorthWest),
            '7' => Ok(Self::SouthWest),
            'F' => Ok(Self::SouthEast),
            _ => Err(GridCellFromCharError::InvalidChar(value)),
        }
    }
}

/// The grid formed by the input.
///
/// Dimensions reach 140 in input, so coordinates are typed to be large enough for such.
struct InputGrid {
    /// The width of the input grid.
    width: i16,
    /// The height of the input grid.
    height: i16,
    /// The cells in the grid mapped by their coordinates.
    cells: HashMap<Point2<i16>, GridCell>,
    /// The coordinates of the start in the grid.
    start: Point2<i16>,
}

/// An error with parsing a string into an [`InputGrid`].
#[derive(thiserror::Error, Debug)]
enum ParseInputGridError {
    #[error("too many lines to represent y coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("detected a second start after first (at {first_coords}): {second_coords}")]
    SecondStart {
        first_coords: Point2<i16>,
        second_coords: Point2<i16>,
    },

    #[error("input is missing a start")]
    MissingStart,
}

impl ParseData for InputGrid {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut tracked_start = None;

        let lines: Vec<_> = parse_input_lines(input, |line_index, line| -> DynamicResult<_> {
            let y = i16::try_from(line_index).map_err(ParseInputGridError::LineIndexOverflow)?;

            let mut pairs = Vec::new();
            for (char_index, character) in line.char_indices() {
                let x =
                    i16::try_from(char_index).map_err(ParseInputGridError::CharIndexOverflow)?;

                let cell = GridCell::try_from(character)?;

                // skip empty cells
                if cell != GridCell::Empty {
                    let coords = Point2::new(x, y);

                    // track where start is
                    if cell == GridCell::Start {
                        // expect only one start
                        if let Some(first_coords) = tracked_start {
                            return Err(ParseInputGridError::SecondStart {
                                first_coords,
                                second_coords: coords,
                            }
                            .into());
                        }

                        tracked_start = Some(coords);
                    }

                    pairs.push((coords, cell));
                }
            }
            Ok(pairs)
        })
        .collect::<Result<_, _>>()?;

        let start = tracked_start.ok_or(ParseInputGridError::MissingStart)?;

        let cells = lines.into_iter().flatten().collect();

        // determine width and height for part 2
        let height =
            i16::try_from(input.lines().count()).map_err(ParseInputGridError::LineIndexOverflow)?;
        let width = i16::try_from(
            input
                .lines()
                .map(|line| line.chars().count())
                .max()
                .expect("input should have at least one line"),
        )
        .map_err(ParseInputGridError::CharIndexOverflow)?;

        Ok(Self {
            width,
            height,
            cells,
            start,
        })
    }
}

/*
It is implied the animal's start also acts as one of the supported pipe variants, forming a closed
loop.

For part 1, determine the farthest grid cell for the animal to reach when following the pipe loop,
then return the number of steps to reach that cell.
*/

/// A cardinal direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    North,
    East,
    South,
    West,
}

const ALL_DIRECTIONS: &[Direction] = &[
    Direction::North,
    Direction::East,
    Direction::South,
    Direction::West,
];

impl Direction {
    /// Find the opposite direction to self.
    fn opposite(self) -> Self {
        match self {
            Self::North => Self::South,
            Self::East => Self::West,
            Self::South => Self::North,
            Self::West => Self::East,
        }
    }

    /// Create a [`Vector2`] for an offset reflecting the direction.
    fn into_vector(self) -> Vector2<i16> {
        match self {
            Self::North => Vector2::new(0, -1),
            Self::East => Vector2::new(1, 0),
            Self::South => Vector2::new(0, 1),
            Self::West => Vector2::new(-1, 0),
        }
    }
}

impl GridCell {
    /// Determine if the cell connects to a direction.
    fn connects_to(self, direction: Direction) -> bool {
        match direction {
            Direction::North => {
                self == Self::NorthSouth || self == Self::NorthEast || self == Self::NorthWest
            }
            Direction::East => {
                self == Self::EastWest || self == Self::NorthEast || self == Self::SouthEast
            }
            Direction::South => {
                self == Self::NorthSouth || self == Self::SouthWest || self == Self::SouthEast
            }
            Direction::West => {
                self == Self::EastWest || self == Self::NorthWest || self == Self::SouthWest
            }
        }
    }

    /// Get the directions this cell connects to. Either the cell is a pipe with 2 connections, or
    /// not a pipe so has `None` connections.
    fn connecting_directions(self) -> Option<[Direction; 2]> {
        match self {
            Self::NorthSouth => Some([Direction::North, Direction::South]),
            Self::EastWest => Some([Direction::East, Direction::West]),
            Self::NorthEast => Some([Direction::North, Direction::East]),
            Self::NorthWest => Some([Direction::North, Direction::West]),
            Self::SouthWest => Some([Direction::South, Direction::West]),
            Self::SouthEast => Some([Direction::South, Direction::East]),
            _ => None,
        }
    }
}

impl InputGrid {
    /// Get the cell at the coordinates, returning [`GridCell::Empty`] if there is nothing.
    fn get_cell(&self, coords: Point2<i16>) -> &GridCell {
        self.cells.get(&coords).unwrap_or(&GridCell::Empty)
    }

    /// Collect the coordinates of the cells forming the closed pipe loop from the start cell.
    fn get_pipe_loop(&self) -> HashSet<Point2<i16>> {
        // find the 2 expected cells that connect to start
        let start_connecting_coords_cells: Vec<_> = ALL_DIRECTIONS
            .iter()
            .filter_map(|direction| {
                let next_coords = self.start + direction.into_vector();
                let next_cell = self.get_cell(next_coords);
                (next_cell.connects_to(direction.opposite())).then_some((next_coords, next_cell))
            })
            .collect();
        assert_eq!(
            start_connecting_coords_cells.len(),
            2,
            "expected exactly 2 adjacent cells to connect to start"
        );

        // set up a search that starts at one of the start connections
        let mut search_coords_cell = start_connecting_coords_cells[0];
        // search for the other start connection
        let target_coords = start_connecting_coords_cells[1].0;

        let mut visited_coords = HashSet::new();
        // visit the start and search coords; we've not visited target yet as we're finding it
        visited_coords.insert(self.start);
        visited_coords.insert(search_coords_cell.0);

        loop {
            let possible_directions = search_coords_cell
                .1
                .connecting_directions()
                .expect("search cell should have connections available");
            let (next_direction, next_coords) = possible_directions
                .into_iter()
                .find_map(|direction| {
                    let next_coords = search_coords_cell.0 + direction.into_vector();
                    (!visited_coords.contains(&next_coords)).then_some((direction, next_coords))
                })
                .expect("search cell should connect to another cell not yet visited");

            visited_coords.insert(next_coords);

            // check if the pipe loop has closed, ending search
            if next_coords == target_coords {
                break;
            }

            // otherwise, set up the next search
            let next_cell = self.get_cell(next_coords);
            assert!(
                next_cell.connects_to(next_direction.opposite()),
                "a next cell does not connect back to the search cell"
            );
            search_coords_cell = (next_coords, next_cell);
        }

        visited_coords
    }
}

struct Day10;

impl Solution<PartOne> for Day10 {
    type Input = InputGrid;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let pipe_loop = input.get_pipe_loop();
        let loop_length = Self::Output::try_from(pipe_loop.len())
            .expect("length of loop should fit in output type");
        // steps to farthest cell is around half the length of the loop
        // - I think length should be even for a closed loop, no remainder to handle
        Ok(loop_length / 2)
    }
}

/*
For part 2, determine the number of cells enclosed by the pipe loop.
*/

impl InputGrid {
    /// Interpret what pipe cell could substitute the start's cell, forming necessary connections
    /// for the closed loop.
    fn start_as_pipe(&self) -> GridCell {
        let start_connecting_directions: Vec<_> = ALL_DIRECTIONS
            .iter()
            .filter(|direction| {
                let next_coords = self.start + direction.into_vector();
                let next_cell = self.get_cell(next_coords);
                next_cell.connects_to(direction.opposite())
            })
            .collect();
        assert_eq!(
            start_connecting_directions.len(),
            2,
            "expected exactly 2 adjacent cells to connect to start"
        );

        let d1 = *start_connecting_directions[0];
        let d2 = *start_connecting_directions[1];

        // TODO could I assume from the order of ALL_DIRECTIONS not both permutations per branch are
        // possible?
        match (d1, d2) {
            (Direction::North, Direction::South) | (Direction::South, Direction::North) => {
                GridCell::NorthSouth
            }
            (Direction::East, Direction::West) | (Direction::West, Direction::East) => {
                GridCell::EastWest
            }
            (Direction::North, Direction::East) | (Direction::East, Direction::North) => {
                GridCell::NorthEast
            }
            (Direction::North, Direction::West) | (Direction::West, Direction::North) => {
                GridCell::NorthWest
            }
            (Direction::South, Direction::West) | (Direction::West, Direction::South) => {
                GridCell::SouthWest
            }
            (Direction::South, Direction::East) | (Direction::East, Direction::South) => {
                GridCell::SouthEast
            }
            _ => {
                unreachable!();
            }
        }
    }
}

impl Solution<PartTwo> for Day10 {
    type Input = InputGrid;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        fn toggle_bool(b: &mut bool) {
            *b = !*b;
        }

        let pipe_loop = input.get_pipe_loop();

        let mut enclosed_count: Self::Output = 0;

        // scan across rows
        for y in 0..input.height {
            // track the state of scanning through enclosed space
            let mut enclosed_state = false;
            // track any time a horizontal line starts
            let mut last_line_start_cell = None;
            for x in 0..input.width {
                let coords = Point2::new(x, y);

                if pipe_loop.contains(&coords) {
                    let cell = {
                        let original_cell = input.get_cell(coords);
                        // need to interpret start cell as substitute pipe for boundary detection
                        if *original_cell == GridCell::Start {
                            input.start_as_pipe()
                        } else {
                            *original_cell
                        }
                    };

                    // determine if the pipe boundary is crossed, toggling enclosed state
                    if cell == GridCell::NorthSouth {
                        toggle_bool(&mut enclosed_state);
                    } else if cell == GridCell::NorthEast || cell == GridCell::SouthEast {
                        // track the beginning of a horizontal pipe line
                        last_line_start_cell = Some(cell);
                    } else if cell == GridCell::NorthWest || cell == GridCell::SouthWest {
                        let start_cell = last_line_start_cell.expect("should have tracked start of horizontal line before detecting end of line");

                        // the pipe boundary is crossed if the start and end cells of the horizontal
                        // line have opposing vertical connections
                        if cell.connects_to(Direction::North)
                            != start_cell.connects_to(Direction::North)
                        {
                            toggle_bool(&mut enclosed_state);
                        }

                        // stop tracking last start
                        last_line_start_cell = None;
                    }
                } else if enclosed_state {
                    enclosed_count = enclosed_count
                        .checked_add(1)
                        .expect("incrementing count should not overflow");
                }
            }
        }

        Ok(enclosed_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT_ONE: &str = r"7-F7-
.FJ|7
SJLL7
|F--J
LJ.LJ
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = InputGrid::parse(EXAMPLE_INPUT_ONE)?;
        let result = <Day10 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 8);
        Ok(())
    }

    const EXAMPLE_INPUT_TWO: &str = r".F----7F7F7F7F-7....
.|F--7||||||||FJ....
.||.FJ||||||||L7....
FJL7L7LJLJ||LJ.L-7..
L--J.L7...LJS7F-7L7.
....F-J..F7FJ|L7L7L7
....L7.F7||L7|.L7L7|
.....|FJLJ|FJ|F7|.LJ
....FJL-7.||.||||...
....L---J.LJ.LJLJ...
";

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = InputGrid::parse(EXAMPLE_INPUT_TWO)?;
        let result = <Day10 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 8);
        Ok(())
    }
}

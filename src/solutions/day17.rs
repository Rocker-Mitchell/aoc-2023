use std::collections::{BinaryHeap, HashMap};

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::DMatrix;

#[solution_runner(
    name = "Day 17: Clumsy Crucible",
    parsed = City,
    part_one = Day17,
    part_two = Day17
)]
impl super::AdventOfCode2023<17> {}

/*
Input is a character grid for heat loss moving through city blocks, represented with digits.
*/

#[derive(Debug)]
struct City(DMatrix<u8>);

#[derive(thiserror::Error, Debug)]
enum ParseCityError {
    #[error("invalid digit character: {0:?}")]
    InvalidDigit(char),

    #[error("expected grid width to be {expected} across rows, but found row width {found}")]
    UnequalGridWidth { expected: usize, found: usize },
}

impl ParseData for City {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut expected_width = None;
        let city_rows = parse_input_lines(input, |_, line| {
            let row = line
                .chars()
                .map(|ch| {
                    ch.to_digit(10)
                        .map_or(Err(ParseCityError::InvalidDigit(ch)), |digit| {
                            Ok(u8::try_from(digit).expect("digit is base 10"))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;

            if let Some(width) = expected_width {
                if row.len() != width {
                    return Err(ParseCityError::UnequalGridWidth {
                        expected: width,
                        found: row.len(),
                    });
                }
            } else {
                expected_width = Some(row.len());
            }

            Ok(row)
        })
        .collect::<Result<Vec<_>, _>>()?;

        let rows = city_rows.len();
        let cols = city_rows[0].len();
        let city_matrix = DMatrix::from_row_iterator(rows, cols, city_rows.into_iter().flatten());

        Ok(Self(city_matrix))
    }
}

/*
For part 1, the starting point is the top left block and the end the bottom right. Determine a path
through city blocks that minimizes heat loss and satisfies movement restrictions, and return the
heat loss found.

Heat loss is incurred when moving into a block, so the start does not count the heat loss of its
block.

At most 3 blocks can be moved to in a straight line before a 90 degree turn must be made. Reversing
direction is not allowed.
*/

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Direction {
    North,
    East,
    South,
    West,
}

impl Direction {
    /// Get the direction when turning left.
    fn to_left(self) -> Self {
        match self {
            Self::North => Self::West,
            Self::East => Self::North,
            Self::South => Self::East,
            Self::West => Self::South,
        }
    }

    /// Get the direction when turning right.
    fn to_right(self) -> Self {
        match self {
            Self::North => Self::East,
            Self::East => Self::South,
            Self::South => Self::West,
            Self::West => Self::North,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CityBlock {
    row: usize,
    col: usize,
}

impl CityBlock {
    fn to_matrix_index(self) -> (usize, usize) {
        (self.row, self.col)
    }

    /// Iterate to the neighboring city block in the `direction`. Returns `None` if an overflow of
    /// the underlying `usize` representation occurs.
    fn to_direction_checked(self, direction: Direction) -> Option<Self> {
        match direction {
            Direction::North => self
                .row
                .checked_sub(1)
                .map(|row| Self { row, col: self.col }),
            Direction::East => self
                .col
                .checked_add(1)
                .map(|col| Self { row: self.row, col }),
            Direction::South => self
                .row
                .checked_add(1)
                .map(|row| Self { row, col: self.col }),
            Direction::West => self
                .col
                .checked_sub(1)
                .map(|col| Self { row: self.row, col }),
        }
    }
}

/// The unique key of a state of traversing the city for heat loss.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct StateKey {
    block: CityBlock,
    /// From which direction the block was traversed to.
    from_direction: Option<Direction>,
    /// How many iterations in a straight line were traversed to this block.
    straight_len: u8,
}

/// The state of traversing through the city for heat loss.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct State {
    heat_loss: u32,
    key: StateKey,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // flip heat loss comparison for min-heap on it
        other
            .heat_loss
            .cmp(&self.heat_loss)
            .then_with(|| self.key.cmp(&other.key))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl City {
    /// Find minimal heat loss traveling from the top left to bottom right.
    ///
    /// # Arguments
    ///
    /// - `min_straight_len` - A minimum distance to travel straight before turning or reaching the
    ///   end.
    /// - `max_straight_len` - A maximum distance to travel straight before turning.
    fn min_heat_loss(&self, min_straight_len: u8, max_straight_len: u8) -> Option<u32> {
        let rows = self.0.nrows();
        let cols = self.0.ncols();
        let start = CityBlock { row: 0, col: 0 };
        let end = CityBlock {
            row: rows.saturating_sub(1),
            col: cols.saturating_sub(1),
        };

        // it's a Dijkstra's search problem

        let mut distances = HashMap::new();
        let mut heap = BinaryHeap::new();

        // init start position
        let start_key = StateKey {
            block: start,
            from_direction: None,
            straight_len: 0,
        };
        distances.insert(start_key, 0);
        heap.push(State {
            heat_loss: 0,
            key: start_key,
        });

        while let Some(State { heat_loss, key }) = heap.pop() {
            let StateKey {
                block,
                from_direction,
                straight_len,
            } = key;

            // need to have reached min straight length to consider as solution
            if block == end && straight_len >= min_straight_len {
                return Some(heat_loss);
            }

            if distances
                .get(&key)
                .is_some_and(|&existing_loss| heat_loss > existing_loss)
            {
                continue;
            }

            let neighbors = from_direction.map_or_else(
                || {
                    // travel in any direction
                    vec![
                        (Direction::North, 1),
                        (Direction::East, 1),
                        (Direction::South, 1),
                        (Direction::West, 1),
                    ]
                },
                |direction| {
                    if straight_len < min_straight_len {
                        // need to continue forward until min straight length met
                        vec![(direction, straight_len + 1)]
                    } else {
                        // travel forward, left, or right
                        vec![
                            (direction, straight_len + 1),
                            (direction.to_left(), 1),
                            (direction.to_right(), 1),
                        ]
                    }
                },
            );

            for (next_direction, next_straight_len) in neighbors {
                // filter for
                // - straight length within max
                // - next block in bounds (0 to matrix rows/cols)
                if next_straight_len <= max_straight_len
                    && let Some(next_block) = block.to_direction_checked(next_direction)
                    && next_block.row < rows
                    && next_block.col < cols
                {
                    let next_key = StateKey {
                        block: next_block,
                        from_direction: Some(next_direction),
                        straight_len: next_straight_len,
                    };

                    let next_heat_loss = heat_loss
                        .checked_add(self.0[next_block.to_matrix_index()].into())
                        .expect("adding heat loss should not overflow");

                    if distances
                        .get(&next_key)
                        .is_none_or(|&existing_loss| next_heat_loss < existing_loss)
                    {
                        distances.insert(next_key, next_heat_loss);
                        heap.push(State {
                            heat_loss: next_heat_loss,
                            key: next_key,
                        });
                    }
                }
            }
        }

        None
    }
}

struct Day17;

impl Solution<PartOne> for Day17 {
    type Input = City;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // part 1 restricts max straight length to 3, but no minimum
        let min_heat_loss = input
            .min_heat_loss(0, 3)
            .expect("expected a min heat loss to be found");
        Ok(min_heat_loss)
    }
}

/*
For part 2, now there is a minimum of 4 blocks and maximum 10 blocks to move in a straight line
before turning or ending. Recalculate the minimum heat loss.
*/

impl Solution<PartTwo> for Day17 {
    type Input = City;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // part 2 restricts straight length between 4 and 10
        let min_heat_loss = input
            .min_heat_loss(4, 10)
            .expect("expected a min heat loss to be found");
        Ok(min_heat_loss)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"2413432311323
3215453535623
3255245654254
3446585845452
4546657867536
1438598798454
4457876987766
3637877979653
4654967986887
4564679986453
1224686865563
2546548887735
4322674655533
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = City::parse(EXAMPLE_INPUT)?;
        let result = <Day17 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 102);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = City::parse(EXAMPLE_INPUT)?;
        let result = <Day17 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 94);
        Ok(())
    }

    #[test]
    fn part_two_solves_another_example() -> DynamicResult<()> {
        let parsed = City::parse(
            r"111111111111
999999999991
999999999991
999999999991
999999999991
",
        )?;
        let result = <Day17 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 71);
        Ok(())
    }
}

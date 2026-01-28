use aoc_framework::parsing::InputScanner;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::DMatrix;

#[solution_runner(
    name = "Day 13: Point of Incidence",
    parsed = InputGrids,
    part_one = Day13,
    part_two = Day13
)]
impl super::AdventOfCode2023<13> {}

/*
Input is character grids of ash (`.`) and rocks (`#`) separated by empty lines.
*/

/// A cell in a grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GridCell {
    Ash,
    Rock,
}

/// An error converting [`char`] to [`GridCell`].
#[derive(thiserror::Error, Debug)]
enum GridCellFromCharError {
    #[error("invalid character: {0:?}")]
    InvalidChar(char),
}

impl TryFrom<char> for GridCell {
    type Error = GridCellFromCharError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Self::Ash),
            '#' => Ok(Self::Rock),
            _ => Err(GridCellFromCharError::InvalidChar(value)),
        }
    }
}

/// A grid from input.
#[derive(Debug)]
struct Grid(DMatrix<GridCell>);

/// The input collection of grids.
struct InputGrids(Vec<Grid>);

#[derive(thiserror::Error, Debug)]
enum ParseInputGridsError {
    #[error("expected grid width to be {expected} across rows, but found row width {found}")]
    UnequalGridWidth { expected: usize, found: usize },
}

impl ParseData for InputGrids {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut scanner = InputScanner::new(input);

        let mut grids = Vec::new();

        while scanner.skip_empty().is_some() {
            let mut expected_width = None;
            let grid_rows = scanner.collect_sequence(|_, line| -> DynamicResult<_> {
                let row: Vec<_> = line
                    .chars()
                    .map(GridCell::try_from)
                    .collect::<Result<_, _>>()?;

                if let Some(width) = expected_width {
                    if row.len() != width {
                        return Err(ParseInputGridsError::UnequalGridWidth {
                            expected: width,
                            found: row.len(),
                        }
                        .into());
                    }
                } else {
                    expected_width = Some(row.len());
                }

                Ok(row)
            })?;

            let rows = grid_rows.len();
            let cols = grid_rows[0].len();
            let grid_matrix =
                DMatrix::from_row_iterator(rows, cols, grid_rows.into_iter().flatten());

            grids.push(Grid(grid_matrix));
        }

        Ok(Self(grids))
    }
}

/*
For part 1, locate patterns of reflection per grid.

A reflection involves a line to separate two rows or columns, and the halves on either side (limited
up to a boundary of the grid, so rows/columns outside the limit ignored) perfectly reflect across
the line.

Return the sum of the number of columns to the left of vertical line reflections and 100 times the
number of rows above horizontal line reflections.
*/

/// A reflection found in a grid and its numerical factor.
#[derive(Debug, PartialEq, Eq)]
enum ReflectionFactor {
    /// The number of columns to the left of a vertical reflection line.
    Columns(usize),
    /// The number of rows above a horizontal reflection line.
    Rows(usize),
}

impl Grid {
    /// Create an iterator of pairs of reflected indexes around a reflection line.
    ///
    /// Pairs are indexes to use to reflect across `reflection_line`; the first value is the smaller
    /// index and the second value the larger.
    ///
    /// The first pair starts immediately around the reflection line, returning
    /// `(reflection_line - 1, reflection_line)`. Following pairs will decrement the first value and
    /// increment the second value. Iteration ends with whichever comes first: the first value
    /// equaling `0` or the second value equaling `length - 1`.
    fn reflection_index_pairs(
        reflection_line: usize,
        length: usize,
    ) -> impl Iterator<Item = (usize, usize)> {
        (0..reflection_line).rev().zip(reflection_line..length)
    }

    /// Find if the grid contains a reflection across a vertical line and return the number of
    /// columns to the left of the reflection line. Returns `None` if no such reflection is found.
    fn columns_reflection_factor(&self) -> Option<ReflectionFactor> {
        let columns: Vec<_> = self.0.column_iter().collect();

        for reflection_line in 1..columns.len() {
            // all columns in reflection index pairs must match to be a valid reflection
            if Self::reflection_index_pairs(reflection_line, columns.len())
                .all(|(left_index, right_index)| columns[left_index] == columns[right_index])
            {
                return Some(ReflectionFactor::Columns(reflection_line));
            }
        }

        None
    }

    /// Find if the grid contains a reflection across a horizontal line and return the number of
    /// rows above the reflection line. Returns `None` if no such reflection is found.
    fn rows_reflection_factor(&self) -> Option<ReflectionFactor> {
        let rows: Vec<_> = self.0.row_iter().collect();

        for reflection_line in 1..rows.len() {
            // all rows in reflection index pairs must match to be a valid reflection
            if Self::reflection_index_pairs(reflection_line, rows.len())
                .all(|(top_index, bottom_index)| rows[top_index] == rows[bottom_index])
            {
                return Some(ReflectionFactor::Rows(reflection_line));
            }
        }

        None
    }

    /// Find if the grid contains a reflection and return its factor. Returns `None` if no such
    /// reflection is found.
    fn reflection_factor(&self) -> Option<ReflectionFactor> {
        self.columns_reflection_factor()
            .or_else(|| self.rows_reflection_factor())
    }
}

#[derive(thiserror::Error, Debug)]
enum Day13Error {
    #[error("grid number {} did not find a reflection", .0.saturating_add(1))]
    MissingReflection(usize),
}

/// Calculate the sum of factors with the given input and a function that resolves a grid to an
/// option of reflection factor (`None` to indicate no reflection found).
fn sum_factors<F>(input: &InputGrids, get_reflection_factor: F) -> Result<u32, Day13Error>
where
    F: Fn(&Grid) -> Option<ReflectionFactor>,
{
    let (sum_columns_factor, sum_rows_factor) = input.0.iter().enumerate().try_fold(
        (0u32, 0u32),
        |(acc_columns, acc_rows), (index, grid)| match get_reflection_factor(grid) {
            None => Err(Day13Error::MissingReflection(index)),
            Some(ReflectionFactor::Columns(factor)) => {
                let cast_factor =
                    u32::try_from(factor).expect("columns factor should fit in output type");
                Ok((
                    acc_columns
                        .checked_add(cast_factor)
                        .expect("adding columns factor should not overflow"),
                    acc_rows,
                ))
            }
            Some(ReflectionFactor::Rows(factor)) => {
                let cast_factor =
                    u32::try_from(factor).expect("rows factor should fit in output type");
                Ok((
                    acc_columns,
                    acc_rows
                        .checked_add(cast_factor)
                        .expect("adding rows factor should not overflow"),
                ))
            }
        },
    )?;

    Ok(sum_rows_factor
        .checked_mul(100)
        .and_then(|product| product.checked_add(sum_columns_factor))
        .expect("sum factors calculation should not overflow"))
}

struct Day13;

impl Solution<PartOne> for Day13 {
    type Input = InputGrids;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(sum_factors(input, Grid::reflection_factor)?)
    }
}

/*
For part 2, input grids are assumed to have one cell smudged/inverted that yields a different
reflection. Calculate the sum again with the new reflections found after smudges are corrected.

> Notable is how there is no guarantee that the old reflection will be intact or not with the smudge
> correction. This means the original reflection can be detected but **must be ignored**.
*/

// I was really getting caught out with handling original reflections when searching for smudge
// reflections; I though generating a mutated grid and getting reflection would have been enough.
// Friend's solution involved expecting to find the smudge cell in the area reflected, which avoids
// original reflections.

impl Grid {
    /// Count the number of mismatched items between iterable collections.
    ///
    /// This assumes both collections are of equal length.
    fn mismatch_count<T>(a: T, b: T) -> usize
    where
        T: IntoIterator,
        T::Item: PartialEq,
    {
        a.into_iter().zip(b).filter(|(x, y)| x != y).count()
    }

    /// Find if the grid contains a reflection across a vertical line and exactly one cell is
    /// smudged/inverted in the reflection, and return the number of columns to the left of the
    /// reflection line. Returns `None` if no such reflection is found.
    fn columns_smudge_reflection_factor(&self) -> Option<ReflectionFactor> {
        let columns: Vec<_> = self.0.column_iter().collect();

        for reflection_line in 1..columns.len() {
            let mut found_exactly_one_smudge = false;

            for (left_index, right_index) in
                Self::reflection_index_pairs(reflection_line, columns.len())
            {
                // evaluate the count of mismatched cells between reflection pairs
                let mismatch_count =
                    Self::mismatch_count(columns[left_index], columns[right_index]);
                match mismatch_count {
                    0 => {} // continue evaluating pairs
                    1 if !found_exactly_one_smudge => found_exactly_one_smudge = true,
                    _ => {
                        // more than one smudge found overall
                        // untrack any found smudge to flag failure
                        found_exactly_one_smudge = false;
                        break;
                    }
                }
            }

            if found_exactly_one_smudge {
                return Some(ReflectionFactor::Columns(reflection_line));
            }
        }

        None
    }

    /// Find if the grid contains a reflection across a horizontal line and exactly one cell is
    /// smudged/inverted in the reflection, and return the number of rows above the reflection line.
    /// Returns `None` if no such reflection is found.
    fn rows_smudge_reflection_factor(&self) -> Option<ReflectionFactor> {
        let rows: Vec<_> = self.0.row_iter().collect();

        for reflection_line in 1..rows.len() {
            let mut found_exactly_one_smudge = false;

            for (top_index, bottom_index) in
                Self::reflection_index_pairs(reflection_line, rows.len())
            {
                // evaluate the count of mismatched cells between reflection pairs
                let mismatch_count = Self::mismatch_count(rows[top_index], rows[bottom_index]);
                match mismatch_count {
                    0 => {} // continue evaluating pairs
                    1 if !found_exactly_one_smudge => found_exactly_one_smudge = true,
                    _ => {
                        // more than one smudge found overall
                        // untrack any found smudge to flag failure
                        found_exactly_one_smudge = false;
                        break;
                    }
                }
            }

            if found_exactly_one_smudge {
                return Some(ReflectionFactor::Rows(reflection_line));
            }
        }

        None
    }

    /// Find if the grid contains a reflection where exactly one cell is smudged/inverted in the
    /// reflection and return its factor. Returns `None` if no such reflection is found.
    fn smudge_reflection_factor(&self) -> Option<ReflectionFactor> {
        self.columns_smudge_reflection_factor()
            .or_else(|| self.rows_smudge_reflection_factor())
    }
}

impl Solution<PartTwo> for Day13 {
    type Input = InputGrids;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(sum_factors(input, Grid::smudge_reflection_factor)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = InputGrids::parse(EXAMPLE_INPUT)?;
        let result = <Day13 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 405);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = InputGrids::parse(EXAMPLE_INPUT)?;
        let result = <Day13 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 400);
        Ok(())
    }

    // Handle cases where the smudge reflection would be iterated to after the old one, in the same
    // axis.

    #[test]
    fn smudge_reflection_after_original_both_columns() -> DynamicResult<()> {
        let parsed = InputGrids::parse(
            r"..##
##..
...#
##..",
        )?;
        let grid = &parsed.0[0];
        assert_eq!(
            grid.reflection_factor(),
            Some(ReflectionFactor::Columns(1)),
            "original reflection does not match expectation"
        );
        assert_eq!(
            grid.smudge_reflection_factor(),
            Some(ReflectionFactor::Columns(3)),
            "new reflection after smudge does not match expectation"
        );
        Ok(())
    }

    #[test]
    fn smudge_reflection_after_original_both_rows() -> DynamicResult<()> {
        let parsed = InputGrids::parse(
            r"#.#.#
#.#.#
..###
..##.",
        )?;
        let grid = &parsed.0[0];
        assert_eq!(
            grid.reflection_factor(),
            Some(ReflectionFactor::Rows(1)),
            "original reflection does not match expectation"
        );
        assert_eq!(
            grid.smudge_reflection_factor(),
            Some(ReflectionFactor::Rows(3)),
            "new reflection after smudge does not match expectation"
        );
        Ok(())
    }
}

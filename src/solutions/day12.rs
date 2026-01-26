use std::collections::HashMap;

use aoc_framework::parsing::{parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;

#[solution_runner(
    name = "Day 12: Hot Springs",
    parsed = Reports,
    part_one = Day12,
    part_two = Day12
)]
impl super::AdventOfCode2023<12> {}

/*
Input is records of spring conditions. Each line formats a sequence of spring conditions as
operational (`.`), damaged (`#`), or unknown (`?`), then a space, then comma-separated values for
contiguous groups of damaged springs.
*/

/// A spring's condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum SpringCondition {
    /// An operational spring.
    Operational,
    /// A damaged spring.
    Damaged,
    /// A spring with an unknown condition.
    Unknown,
}

/// An error converting [`char`] to [`SpringCondition`].
#[derive(thiserror::Error, Debug)]
enum SpringConditionTryFromCharError {
    #[error("invalid character: {0:?}")]
    InvalidChar(char),
}

impl TryFrom<char> for SpringCondition {
    type Error = SpringConditionTryFromCharError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '.' => Ok(Self::Operational),
            '#' => Ok(Self::Damaged),
            '?' => Ok(Self::Unknown),
            _ => Err(SpringConditionTryFromCharError::InvalidChar(value)),
        }
    }
}

/// A report of spring conditions.
#[derive(Debug)]
struct SpringReport {
    /// The sequence of spring conditions.
    sequence: Vec<SpringCondition>,
    /// The sequence of expected contiguous sizes of damaged spring groups.
    damaged_group_sizes: Vec<u32>,
}

/// The parsed input of spring reports.
#[derive(Debug)]
struct Reports(Vec<SpringReport>);

/// An error parsing input into [`Reports`].
#[derive(thiserror::Error, Debug)]
enum ParseReportsError {
    #[error("expected a space (`' '`) to delimit spring sequence and damaged group sizes")]
    NoSpaceDelimiter,
}

impl ParseData for Reports {
    fn parse(input: &str) -> aoc_framework::DynamicResult<Self>
    where
        Self: Sized,
    {
        let reports = parse_input_lines(input, |_, line| -> DynamicResult<_> {
            let (sequence_str, damaged_groups_str) = line
                .split_once(' ')
                .ok_or(ParseReportsError::NoSpaceDelimiter)?;

            let sequence = sequence_str
                .chars()
                .map(SpringCondition::try_from)
                .collect::<Result<_, _>>()?;

            let damaged_group_sizes = damaged_groups_str
                .split(',')
                .map(parse_with_context)
                .collect::<Result<_, _>>()?;

            Ok(SpringReport {
                sequence,
                damaged_group_sizes,
            })
        })
        .collect::<Result<_, _>>()?;
        Ok(Self(reports))
    }
}

/*
For part 1, determine how many different arrangements of operational and broken springs from unknown
springs can satisfy the contiguous groups, then sum them together.
*/

/// The memoization key for memoizing [`SpringReport::recursive_count_permutations`].
#[derive(Debug, PartialEq, Eq, Hash)]
struct CountPermutationsMemoKey<'a> {
    /// The current spring condition passed. `None` should suggest iteration passed the end of the
    /// report sequence.
    current: Option<SpringCondition>,
    /// The remaining spring conditions sequence slice following `current`. `None` should suggest
    /// the remaining sequence was exhausted.
    remaining_sequence_slice: Option<&'a [SpringCondition]>,
    /// The remaining damaged group sizes slice. `None` should suggest the remaining sizes were
    /// exhausted.
    remaining_damaged_group_sizes_slice: Option<&'a [u32]>,
}

impl SpringReport {
    /// Recursively find how many permutations can be valid when substituting unknown spring
    /// conditions.
    ///
    /// # Arguments
    ///
    /// - `current` - The current spring condition to observe for iteration. If iteration passes end
    ///   of sequence, this should be `None`. This does not have to reflect the real sequence value,
    ///   which is useful for substituting unknown spring conditions.
    /// - `next_index` - The index into the sequence after `current`.
    /// - `damaged_group_sizes_index` - The index for the next damaged group size to pair with the
    ///   next found damaged springs group in the sequence range starting at `current`.
    /// - `memo` - A memoization of prior calculated results.
    fn recursive_count_permutations<'a>(
        &'a self,
        current: Option<SpringCondition>,
        next_index: usize,
        damaged_group_sizes_index: usize,
        memo: &mut HashMap<CountPermutationsMemoKey<'a>, u64>,
    ) -> u64 {
        // slice remainders from indexes; have exhausted remainders represented with `None`
        let remaining_sequence_slice_opt = self
            .sequence
            .get(next_index..)
            .filter(|slice| !slice.is_empty());
        let remaining_damaged_group_sizes_slice_opt = self
            .damaged_group_sizes
            .get(damaged_group_sizes_index..)
            .filter(|slice| !slice.is_empty());

        // return the cached result if there is one
        let memo_key = CountPermutationsMemoKey {
            current,
            remaining_sequence_slice: remaining_sequence_slice_opt,
            remaining_damaged_group_sizes_slice: remaining_damaged_group_sizes_slice_opt,
        };
        if let Some(&result) = memo.get(&memo_key) {
            return result;
        }

        let result = match current {
            None => {
                // exhausted sequence; result depends on if there are remaining damage group sizes
                // - if damage group sizes is exhausted then one permutation found, otherwise
                //   there's no permutation
                // - calculation should be cheap enough to skip caching; immediately return
                return (remaining_damaged_group_sizes_slice_opt.is_none()).into();
            }
            Some(SpringCondition::Operational) => {
                // iterate to after operational block and recurse from there
                let index_after_operational_group = remaining_sequence_slice_opt
                    .and_then(|slice| {
                        slice
                            .iter()
                            .position(|condition| *condition != SpringCondition::Operational)
                    })
                    .map_or_else(|| self.sequence.len(), |offset| next_index + offset);

                self.recursive_count_permutations(
                    self.sequence.get(index_after_operational_group).copied(),
                    index_after_operational_group + 1,
                    damaged_group_sizes_index,
                    memo,
                )
            }
            Some(SpringCondition::Damaged) => {
                self.damaged_group_sizes
                    .get(damaged_group_sizes_index)
                    .and_then(|&damaged_count| {
                        if damaged_count == 0 {
                            // expect non-zero group sizes
                            None
                        } else {
                            // factor in current being part of the count
                            Some(damaged_count - 1)
                        }
                    })
                    .map_or(0, |mut remaining_damaged_count| {
                        // iterate to consume remaining damaged count
                        let mut search_index = next_index;
                        while remaining_damaged_count > 0
                            && search_index < self.sequence.len()
                            && self.sequence[search_index] != SpringCondition::Operational
                        {
                            remaining_damaged_count -= 1;
                            search_index += 1;
                        }

                        // no permutation if the damaged count was not completely consumed or the
                        // searched spring is damaged (indicating a group bigger than expected)
                        if remaining_damaged_count > 0
                            || self.sequence.get(search_index).copied()
                                == Some(SpringCondition::Damaged)
                        {
                            0
                        } else {
                            // use recursion to process the remainder of the sequence
                            // - the spring condition at search index is determined at least not
                            //   damaged, but an unknown spring should be mapped to operational to
                            //   keep the damaged group valid
                            // - if the sequence is observed exhausted through search index, pass
                            //   current as None
                            self.recursive_count_permutations(
                                (search_index < self.sequence.len())
                                    .then_some(SpringCondition::Operational),
                                search_index + 1,
                                damaged_group_sizes_index + 1,
                                memo,
                            )
                        }
                    })
            }
            Some(SpringCondition::Unknown) => {
                // recursively check substituting the unknown spring with damaged and operational
                // conditions, yielding the sum result
                self.recursive_count_permutations(
                    Some(SpringCondition::Damaged),
                    next_index,
                    damaged_group_sizes_index,
                    memo,
                )
                .checked_add(self.recursive_count_permutations(
                    Some(SpringCondition::Operational),
                    next_index,
                    damaged_group_sizes_index,
                    memo,
                ))
                .expect("sum of branched permutations should not overflow")
            }
        };

        // cache the result and return
        memo.insert(memo_key, result);
        result
    }

    /// Find how many permutations can be valid when substituting unknown spring conditions.
    fn count_permutations<'a>(
        &'a self,
        memo: &mut HashMap<CountPermutationsMemoKey<'a>, u64>,
    ) -> u64 {
        self.recursive_count_permutations(self.sequence.first().copied(), 1, 0, memo)
    }
}

struct Day12;

impl Solution<PartOne> for Day12 {
    type Input = Reports;
    type Output = u64;

    fn solve(input: &Self::Input) -> aoc_framework::DynamicResult<Self::Output> {
        let mut memo = HashMap::new();
        let sum = input
            .0
            .iter()
            .map(|report| report.count_permutations(&mut memo))
            .checked_sum()
            .expect("summation should not overflow");
        Ok(sum)
    }
}

/*
For part 2, the records must be unfolded, then recalculate the different arrangements.

Unfolding involves appending 4 copies of the sequence to the original with unknown springs
separating the original and copies, and appending 4 copies of the damaged group sizes to the
original.
*/

impl SpringReport {
    /// Create an unfolded spring report from self.
    fn to_unfold(&self) -> Self {
        const REPETITIONS: usize = 5;

        let unfold_sequence = (0..REPETITIONS)
            .flat_map(|i| {
                let mut seq = self.sequence.clone();
                if i < REPETITIONS - 1 {
                    seq.push(SpringCondition::Unknown);
                }
                seq
            })
            .collect();

        let unfold_damaged_group_sizes = self
            .damaged_group_sizes
            .iter()
            .cycle()
            .take(self.damaged_group_sizes.len() * REPETITIONS)
            .copied()
            .collect();

        Self {
            sequence: unfold_sequence,
            damaged_group_sizes: unfold_damaged_group_sizes,
        }
    }
}

impl Solution<PartTwo> for Day12 {
    type Input = Reports;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // collecting unfolded reports should satisfy lifetime needed for memo
        let unfolded_reports: Vec<_> = input.0.iter().map(SpringReport::to_unfold).collect();
        let mut memo = HashMap::new();
        let sum = unfolded_reports
            .iter()
            .map(|report| report.count_permutations(&mut memo))
            .checked_sum()
            .expect("summation should not overflow");
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"???.### 1,1,3
.??..??...?##. 1,1,3
?#?#?#?#?#?#?#? 1,3,1,6
????.#...#... 4,1,1
????.######..#####. 1,6,5
?###???????? 3,2,1
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Reports::parse(EXAMPLE_INPUT)?;
        let result = <Day12 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 21);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Reports::parse(EXAMPLE_INPUT)?;
        let result = <Day12 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 525_152);
        Ok(())
    }
}

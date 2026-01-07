use std::collections::{HashSet, VecDeque};

use aoc_framework::parsing::{parse_lines_with_offset, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;

#[solution_runner(
    name = "Day 4: Scratchcards", parsed = ScratchcardTable, part_one = Day04, part_two = Day04
)]
impl super::AdventOfCode2023<4> {}

/*
Input is a table of scratchcards. Each line defines a scratchcard.

The format of a card includes a space-separated list of winning numbers and another
space-separated list of scratched numbers, separated by `|`.
*/

#[derive(thiserror::Error, Debug)]
enum Day04Error {
    /// Expected a colon delimiter splitting line.
    #[error("no colon found to separate card ID from numbers")]
    NoColonDelimiter,

    /// Expected a vertical bar delimiter splitting number lists.
    #[error("no vertical bar to separate winning numbers from scratched numbers")]
    NoVerticalBarDelimiter,

    /// An unexpected duplicate number was found in a number list. Contains the list as a string and
    /// the number that was in duplicate.
    #[error("unexpected duplicate number found in a number list ({0:?}): {1}")]
    DuplicateNumber(String, CardNumber),
}

/// The integer type for numbers on a scratchcard.
///
/// Observed at most 2 digits per number from input, so this is sized to hold such.
type CardNumber = u8;

/// The numbers of a scratchcard.
#[derive(Debug)]
struct Scratchcard {
    winning_numbers: HashSet<CardNumber>,
    scratched_numbers: HashSet<CardNumber>,
}

#[derive(Debug)]
struct ScratchcardTable(Vec<Scratchcard>);

impl ParseData for ScratchcardTable {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn parse_numbers(list: &str) -> DynamicResult<HashSet<CardNumber>> {
            let mut numbers = HashSet::new();

            for token in list.split_whitespace() {
                let value: CardNumber = parse_with_context(token)?;
                if !numbers.insert(value) {
                    return Err(Day04Error::DuplicateNumber(list.trim().to_owned(), value).into());
                }
            }

            Ok(numbers)
        }

        let cards = parse_lines_with_offset(input, 0, |_, line| {
            let (_, card_numbers_str) = line.split_once(':').ok_or(Day04Error::NoColonDelimiter)?;

            let (winning_numbers_str, scratched_numbers_str) = card_numbers_str
                .split_once('|')
                .ok_or(Day04Error::NoVerticalBarDelimiter)?;

            Ok(Scratchcard {
                winning_numbers: parse_numbers(winning_numbers_str)?,
                scratched_numbers: parse_numbers(scratched_numbers_str)?,
            })
        })
        .collect::<Result<_, _>>()?;
        Ok(Self(cards))
    }
}

/*
For part 1, find the total points across cards.

Determine points by comparing the intersection of numbers between the lists. The first match is
worth one point, and following matches double the point value.

> With this doubling behavior, I'd observe it's a power formula like `2^(x-1)`, which could also be
> a bit shift.
*/

/// The integer type for the points of a scratchcard.
///
/// Observed at most 10 winning numbers a card from input, so this is sized to hold at least 10 bits
/// (by the nature of the points calculation).
type Points = u16;

impl Scratchcard {
    fn match_count(&self) -> usize {
        self.winning_numbers
            .intersection(&self.scratched_numbers)
            .count()
    }

    fn points(&self) -> Points {
        let match_count = self.match_count();

        if match_count == 0 {
            0
        } else {
            // 2 ^ (matches - 1); one match is 1, two is 2, three is 4, four is 8, etc.
            1 << (match_count - 1)
        }
    }
}

struct Day04;

impl Solution<PartOne> for Day04 {
    type Input = ScratchcardTable;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let total = input
            .0
            .iter()
            .map(Scratchcard::points)
            .checked_sum()
            .expect("should not have integer overflow during summation");
        Ok(total)
    }
}

/*
For part 2, calculate total scratchcards, originals and copies generated.

For the amount of matches to winning numbers, that card wins copies of that many subsequent cards.
Example: for card 10 matching 5 numbers, it wins copies of cards 11 through 15.

Copied cards are subject to the same logic, referring to the same subsequent cards as its original.
Example: a copy of card 10 wins copies 11 through 15 like the previous example.

Copies won't be generated if the card to copy is not in the table (there's not enough subsequent
cards).
*/

impl Solution<PartTwo> for Day04 {
    type Input = ScratchcardTable;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut total_cards: Self::Output = 0;
        let mut copies_deque = VecDeque::new();
        let number_cards = input.0.len();
        for (card_index, card) in input.0.iter().enumerate() {
            // find amount of instances of card: the original we're currently processing plus copies
            // generated; pop the copies for next loop
            let instances = 1 + copies_deque.pop_front().unwrap_or(0);

            // sum total instances of cards processed
            total_cards = total_cards
                .checked_add(instances)
                .expect("should not have integer overflow during summation");

            // skip the following on the last loop
            if card_index < number_cards - 1 {
                // generate subsequent copies and add back to deque for next loop
                // - instances informs how many copies are made
                // - match_count dictates the range of subsequent cards copied
                let match_count = card.match_count();
                let copies_to_add = vec![instances; match_count];

                if !copies_to_add.is_empty() {
                    // mutate deque indexes up to the smaller index between collections
                    let split_idx = copies_to_add.len().min(copies_deque.len());
                    for (copy_index, &generated_copies) in
                        copies_to_add.iter().take(split_idx).enumerate()
                    {
                        copies_deque[copy_index] += generated_copies;
                    }

                    // extend deque with any remainder from copies to add
                    if copies_to_add.len() > split_idx {
                        copies_deque.extend(&copies_to_add[split_idx..]);
                    }
                }
            }
        }

        Ok(total_cards)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = ScratchcardTable::parse(EXAMPLE_INPUT)?;
        let result = <Day04 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 13);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = ScratchcardTable::parse(EXAMPLE_INPUT)?;
        let result = <Day04 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 30);
        Ok(())
    }
}

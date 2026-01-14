use std::collections::{BTreeMap, HashMap};
use std::str::FromStr;

use aoc_framework::parsing::{parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;

#[solution_runner(
    name = "Day 7: Camel Cards",
    parsed = InputHands,
    part_one = Day07,
    part_two = Day07
)]
impl super::AdventOfCode2023<7> {}

/*
Input is a line-separated list of hands of cards, a space, and corresponding bids.

Cards use single characters to label their value: `A`, `K`, `Q`, `J`, `T`, and digits `9` to `2`.
Hands are five cards in sequence.
*/

/// An enumeration of card values.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Card {
    // deriving Ord, variants are from smallest to largest
    Joker, // relevant to part 2
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
    Nine,
    Ten,
    Jack,
    Queen,
    King,
    Ace,
}

/// An error when converting a [`char`] to a [`Card`].
#[derive(thiserror::Error, Debug)]
enum CardTryFromCharError {
    #[error("unrecognized character")]
    UnrecognizedChar,
}

impl TryFrom<char> for Card {
    type Error = CardTryFromCharError;

    /// Parse a card value from a character, mapping `'J'` as [`Card::Jack`].
    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '2' => Ok(Self::Two),
            '3' => Ok(Self::Three),
            '4' => Ok(Self::Four),
            '5' => Ok(Self::Five),
            '6' => Ok(Self::Six),
            '7' => Ok(Self::Seven),
            '8' => Ok(Self::Eight),
            '9' => Ok(Self::Nine),
            'T' => Ok(Self::Ten),
            'J' => Ok(Self::Jack),
            'Q' => Ok(Self::Queen),
            'K' => Ok(Self::King),
            'A' => Ok(Self::Ace),
            _ => Err(CardTryFromCharError::UnrecognizedChar),
        }
    }
}

/// A hand of five [`Card`]s in sequence.
#[derive(Debug, Clone)]
struct Hand([Card; 5]);

/// An error when parsing a string into a [`Hand`].
#[derive(thiserror::Error, Debug)]
enum ParseHandError {
    #[error("expected exactly 5 characters")]
    InvalidLength,

    #[error("An invalid card character was parsed: {c:?}")]
    InvalidCardChar {
        c: char,
        source: CardTryFromCharError,
    },
}

impl FromStr for Hand {
    type Err = ParseHandError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let characters: Vec<char> = s.chars().take(6).collect();

        if characters.len() != 5 {
            return Err(ParseHandError::InvalidLength);
        }

        let cards: Vec<Card> = characters
            .into_iter()
            .map(|c| {
                Card::try_from(c).map_err(|source| ParseHandError::InvalidCardChar { c, source })
            })
            .collect::<Result<_, _>>()?;

        <[Card; 5]>::try_from(cards).map_or_else(|_| unreachable!(), |arr| Ok(Self(arr)))
    }
}

/// The integer type for a bid.
///
/// Observed a majority of 3 digit numbers and an instance of `1000` in input, so this is sized to
/// hold such.
type Bid = u16;

/// The input of [`Hand`]s with their corresponding bids.
struct InputHands(Vec<(Hand, Bid)>);

/// An error when parsing input into [`InputHands`].
#[derive(thiserror::Error, Debug)]
enum ParseInputHandsError {
    #[error("expected a space to separate hand from bid")]
    ExpectedSpaceSplitOnce,
}

impl ParseData for InputHands {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let lines = parse_input_lines(input, |_, line| -> DynamicResult<_> {
            let (hand_str, bid_str) = line
                .split_once(' ')
                .ok_or(ParseInputHandsError::ExpectedSpaceSplitOnce)?;
            let hand = parse_with_context(hand_str)?;
            let bid = parse_with_context(bid_str)?;
            Ok((hand, bid))
        })
        .collect::<Result<_, _>>()?;
        Ok(Self(lines))
    }
}

/*
For part 1, find the total winnings of the hands.

Each hand wins its bid multiplied by its rank among the hands, with the weakest hand at rank 1,
incrementing to the strongest.

Full details of comparing hands are on https://adventofcode.com/2023/day/7, but the priority is:

1. The hand type
  - Five of a kind
  - Four of a kind
  - Full house
  - Three of a kind
  - Two pair
  - One pair
  - High card

2. First card in hand, then second, etc.
*/

/// The type of a [`Hand`].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum HandType {
    // deriving Ord, variants are from smallest to largest
    HighCard,
    OnePair,
    TwoPair,
    ThreeKind,
    FullHouse,
    FourKind,
    FiveKind,
}

impl Hand {
    /// Calculate the frequency of cards in the hand, returning as a map of the card value to the
    /// count.
    fn get_card_counts(&self) -> HashMap<Card, u8> {
        let mut card_counts = HashMap::new();
        for card in self.0 {
            *card_counts.entry(card).or_insert(0) += 1;
        }
        card_counts
    }

    /// Get the largest count from card counts.
    ///
    /// If there are no entries in card counts, returns `None`.
    fn find_largest_count(card_counts: &HashMap<Card, u8>) -> Option<u8> {
        card_counts.values().copied().max()
    }

    /// Get the hand's type.
    fn get_hand_type(&self) -> HandType {
        if self.0.contains(&Card::Joker) {
            // relevant to part 2
            return self.joker_hand_type();
        }

        let card_counts = self.get_card_counts();

        match card_counts.len() {
            // with one unique card value, has to be five of a kind
            1 => HandType::FiveKind,
            2 => {
                let largest_count = Self::find_largest_count(&card_counts)
                    .expect("there should be two card counts to find largest of");
                if largest_count == 4 {
                    // one card value 4 times, another 1 time; has to be four of a kind
                    HandType::FourKind
                } else {
                    // only other case is one card value 3 times, another 2 times; has to be full
                    // house
                    HandType::FullHouse
                }
            }
            3 => {
                let largest_count = Self::find_largest_count(&card_counts)
                    .expect("there should be three card counts to find largest of");
                if largest_count == 3 {
                    // one card value 3 times, two card values 1 time each; has to be three of a
                    // kind
                    HandType::ThreeKind
                } else {
                    // only other case is two card values 2 times each, one card value 1 time; has
                    // to be two pair
                    HandType::TwoPair
                }
            }
            // could only have one card value 2 times and the rest unique, has to be one pair
            4 => HandType::OnePair,
            // with five different card values, has to be high card
            5 => HandType::HighCard,
            _ => unreachable!(),
        }
    }
}

impl PartialEq for Hand {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for Hand {}

impl PartialOrd for Hand {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Hand {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // compare by hand type first, then compare by card value from first index onward (default
        // of array comparison)
        self.get_hand_type()
            .cmp(&other.get_hand_type())
            .then(self.0.cmp(&other.0))
    }
}

struct Day07;

impl Solution<PartOne> for Day07 {
    type Input = InputHands;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // sort hands by constructing BTreeMap
        let sorted_hands: BTreeMap<_, _> = input.0.iter().cloned().collect();

        let total = sorted_hands
            .values()
            .enumerate()
            .map(|(index, &bid)| {
                let rank = Self::Output::try_from(index)
                    .expect("should not be iterating index larger than output type")
                    .checked_add(1)
                    .expect("should not overflow when calculating rank");
                rank.checked_mul(bid.into())
                    .expect("should not overflow when multiplying rank by bid")
            })
            .checked_sum()
            .expect("should not overflow when calculating sum");
        Ok(total)
    }
}

/*
For part 2, `J` is now a joker card.

When comparing card values, jokers are smaller than `2`. When determining hand types, jokers are a
wildcard to enable the strongest hand type possible.

Find the total winnings with the joker cards.
*/

impl Hand {
    /// Create a new hand where any [`Card::Jack`] are changed to [`Card::Joker`].
    fn to_jokers(&self) -> Self {
        let mut cards_copy = self.0;
        for card in &mut cards_copy {
            if *card == Card::Jack {
                *card = Card::Joker;
            }
        }
        Self(cards_copy)
    }

    /// Get the hand's type, using [`Card::Joker`] as wildcards.
    ///
    /// # Panics
    ///
    /// If the hand does not contain a [`Card::Joker`], the method panics.
    fn joker_hand_type(&self) -> HandType {
        let mut card_counts = self.get_card_counts();
        let joker_value = card_counts.remove(&Card::Joker);

        joker_value.map_or_else(
            || {
                panic!("expected at least one joker in hand");
            },
            |joker_count| {
                let largest_non_joker_count = Self::find_largest_count(&card_counts).unwrap_or(0);

                let largest_possible_count = joker_count + largest_non_joker_count;
                match largest_possible_count {
                    // can build to five of a kind
                    5 => HandType::FiveKind,
                    // can build to four of a kind
                    4 => HandType::FourKind,
                    3 => {
                        // if there's one joker and remaining cards are two pair (which would mean
                        // only 2 unique count entries), can build a full house;
                        // otherwise there's too many single count cards, can build to three of a
                        // kind
                        if joker_count == 1 && card_counts.len() == 2 {
                            HandType::FullHouse
                        } else {
                            HandType::ThreeKind
                        }
                    }
                    // largest non-joker count would have to be 1, can build one pair
                    2 => HandType::OnePair,
                    _ => unreachable!(),
                }
            },
        )
    }
}

impl Solution<PartTwo> for Day07 {
    type Input = InputHands;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // Convert hands to hold jokers then collect for sorting
        let sorted_hands: BTreeMap<_, _> = input
            .0
            .iter()
            .map(|(hand, bid)| (hand.to_jokers(), *bid))
            .collect();

        let total = sorted_hands
            .values()
            .enumerate()
            .map(|(index, &bid)| {
                let rank = Self::Output::try_from(index)
                    .expect("should not be iterating index larger than output type")
                    .checked_add(1)
                    .expect("should not overflow when calculating rank");
                rank.checked_mul(bid.into())
                    .expect("should not overflow when multiplying rank by bid")
            })
            .checked_sum()
            .expect("should not overflow when calculating sum");
        Ok(total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"32T3K 765
T55J5 684
KK677 28
KTJJT 220
QQQJA 483
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = InputHands::parse(EXAMPLE_INPUT)?;
        let result = <Day07 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 6440);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = InputHands::parse(EXAMPLE_INPUT)?;
        let result = <Day07 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 5905);
        Ok(())
    }
}

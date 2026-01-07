use std::cmp;

use aoc_framework::parsing::{parse_lines_with_offset, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use regex::Regex;

use crate::checked_product::CheckedProduct;

#[solution_runner(name = "Day 2: Cube Conundrum", parsed = Games, part_one = Day02, part_two = Day02)]
impl super::AdventOfCode2023<2> {}

#[derive(thiserror::Error, Debug)]
enum Day02Error {
    /// Expected colon delimiter splitting line.
    #[error("no colon found to separate game ID from subsets")]
    NoColonDelimiter,

    /// Game ID not formatted as expected. Tuple contains the source string to report in the error
    /// message.
    #[error("failed to detect game ID: expected pattern \"Game [id]\", found {0:?}")]
    NotGameId(String),

    /// Count and color not formatted as expected. Tuple contains the source string to report in the
    /// error message.
    #[error("failed to detect count and color: expected pattern \"[count] [color]\", found {0:?}")]
    NotCountColor(String),

    /// Found an unexpected color name. Tuple contains the source string to report in the error
    /// message.
    #[error("color not supported: {0:?}")]
    UnsupportedColor(String),

    /// A duplicate color was specified in subset. Tuple contains the source subset string to report
    /// in the error message.
    #[error("duplicate color found in subset: {0:?}")]
    DuplicateColorInSubset(String),
}

/*
Input is a record of games. The game uses a bag and several colored cubes of red, green, or blue. A
game has a secret number of cubes in the bag, and has rounds where handfuls of cubes are pulled out
to see then put back in the bag.

The input format involves a game ID and a semicolon-separated list of subsets
of colored cubes revealed. A subset is a comma separated list of counts of cubes and their color.
*/

type CubeCount = u8;

/// A collection of cube counts by colors red, green, and blue.
#[derive(Debug)]
struct ColoredCubeCounts {
    red: CubeCount,
    green: CubeCount,
    blue: CubeCount,
}

struct ColoredCubeCountsParser {
    /// Regex for capturing count & color.
    count_color_re: Regex,
}

impl ColoredCubeCountsParser {
    const COUNT_COLOR_PATTERN: &str = r"(\d+) (\w+)";

    fn new() -> Self {
        let count_color_re =
            Regex::new(Self::COUNT_COLOR_PATTERN).expect("pattern should be valid");
        Self { count_color_re }
    }

    fn parse(&self, subset: &str) -> DynamicResult<ColoredCubeCounts> {
        let mut red_count = None;
        let mut green_count = None;
        let mut blue_count = None;

        for count_str in subset.split(',').map(str::trim) {
            let count_color_captures = self
                .count_color_re
                .captures(count_str)
                .ok_or_else(|| Day02Error::NotCountColor(count_str.to_owned()))?;
            let count_match = count_color_captures
                .get(1)
                .expect("count should be in capture group 1");
            let color_match = count_color_captures
                .get(2)
                .expect("color should be in capture group 2");

            let parse_count = || parse_with_context::<CubeCount>(count_match.as_str());
            let duplicate_error = || Day02Error::DuplicateColorInSubset(subset.to_owned());

            match color_match.as_str() {
                "red" => {
                    if red_count.is_some() {
                        return Err(duplicate_error().into());
                    }
                    red_count = Some(parse_count()?);
                }
                "green" => {
                    if green_count.is_some() {
                        return Err(duplicate_error().into());
                    }
                    green_count = Some(parse_count()?);
                }
                "blue" => {
                    if blue_count.is_some() {
                        return Err(duplicate_error().into());
                    }
                    blue_count = Some(parse_count()?);
                }
                other => {
                    return Err(Day02Error::UnsupportedColor(other.to_owned()).into());
                }
            }
        }

        Ok(ColoredCubeCounts {
            red: red_count.unwrap_or(0),
            green: green_count.unwrap_or(0),
            blue: blue_count.unwrap_or(0),
        })
    }
}

type GameId = u8;

/// Information about a game, including the game ID and subsets of [`ColoredCubeCounts`] that have
/// been observed from the bag.
#[derive(Debug)]
struct GameData {
    id: GameId,
    subsets: Vec<ColoredCubeCounts>,
}

struct GameDataParser {
    /// Regex for capturing game ID.
    id_re: Regex,
    colored_cube_counts_parser: ColoredCubeCountsParser,
}

impl GameDataParser {
    const ID_PATTERN: &str = r"Game (\d+)";

    fn new() -> Self {
        let id_re = Regex::new(Self::ID_PATTERN).expect("pattern should be valid");
        let colored_cube_counts_parser = ColoredCubeCountsParser::new();
        Self {
            id_re,
            colored_cube_counts_parser,
        }
    }

    fn parse(&self, line: &str) -> DynamicResult<GameData> {
        let (game_id_str, subsets_str) =
            line.split_once(':').ok_or(Day02Error::NoColonDelimiter)?;

        let id_captures = self
            .id_re
            .captures(game_id_str)
            .ok_or(Day02Error::NotGameId(game_id_str.to_owned()))?;
        let id_match = id_captures.get(1).expect("ID should be in capture group 1");
        let id = parse_with_context(id_match.as_str())?;

        let subsets = subsets_str
            .split(';')
            .map(|subset| self.colored_cube_counts_parser.parse(subset))
            .collect::<Result<_, _>>()?;

        Ok(GameData { id, subsets })
    }
}

struct Games(Vec<GameData>);

impl ParseData for Games {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let game_data_parser = GameDataParser::new();
        let games = parse_lines_with_offset(input, 0, |_, line| game_data_parser.parse(line))
            .collect::<Result<_, _>>()?;
        Ok(Self(games))
    }
}

/*
For part 1, test each game for being possible with 12 red, 13 green, & 14 blue cubes in the bag.
Then, sum together the IDs of the possible games.
*/

/// Determine if a game's subset of observed cubes is possible under the given limit on what cubes
/// would be in the bag.
fn is_possible_game(subsets: &[ColoredCubeCounts], limit: &ColoredCubeCounts) -> bool {
    subsets.iter().all(|counts| {
        counts.red <= limit.red && counts.green <= limit.green && counts.blue <= limit.blue
    })
}

struct Day02;

impl Solution<PartOne> for Day02 {
    type Input = Games;
    type Output = u16;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        const LIMIT: ColoredCubeCounts = ColoredCubeCounts {
            red: 12,
            green: 13,
            blue: 14,
        };
        let sum_ids = input
            .0
            .iter()
            .filter(|&game_data| is_possible_game(&game_data.subsets, &LIMIT))
            .map(|game_data| Self::Output::from(game_data.id))
            .checked_sum()
            .expect("should not have integer overflow during summation");
        Ok(sum_ids)
    }
}

/*
For part 2, for each game determine the minimum cubes needed in the bag for the subsets to be
possible. Then, calculate the power of minimum cubes as the product of each color. Finally, sum the
powers.
*/

/// Find maximum cubes by color needed to satisfy subsets then multiply maximums together as the
/// power of the minimum cubes needed.
fn minimum_cubes_power(subsets: &[ColoredCubeCounts]) -> u16 {
    let mut red_max = 0;
    let mut green_max = 0;
    let mut blue_max = 0;

    for counts in subsets {
        red_max = cmp::max(red_max, counts.red);
        green_max = cmp::max(green_max, counts.green);
        blue_max = cmp::max(blue_max, counts.blue);
    }

    [red_max, green_max, blue_max]
        .into_iter()
        .map(u16::from)
        .checked_product()
        .expect("should not have integer overflow from product")
}

impl Solution<PartTwo> for Day02 {
    type Input = Games;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum_powers = input
            .0
            .iter()
            .map(|game_data| Self::Output::from(minimum_cubes_power(&game_data.subsets)))
            .checked_sum()
            .expect("should not have integer overflow during summation");
        Ok(sum_powers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Games::parse(EXAMPLE_INPUT)?;
        let result = <Day02 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 8);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Games::parse(EXAMPLE_INPUT)?;
        let result = <Day02 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 2286);
        Ok(())
    }
}

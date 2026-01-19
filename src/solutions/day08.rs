use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use aoc_framework::parsing::{InputScanner, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};

#[solution_runner(
    name = "Day 8: Haunted Wasteland",
    parsed = MapDocuments,
    part_one = Day08,
    part_two = Day08
)]
impl super::AdventOfCode2023<8> {}

/*
Input is map documents, containing instructions for directions of travel, an empty line, and a
network of labeled nodes.

The directions line is a sequence of `R` and `L` characters, for right and left respectively.

The network of nodes has each line define a start node, `" = "`, and wrapped in `()` a
`", "`-separated tuple of nodes. The first node in the tuple is reached by traveling left, and the
second right.

> Node labels are three characters long.
*/

/// A direction of travel through the node network.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Left,
    Right,
}

/// An error when converting [`char`] to [`Direction`].
#[derive(thiserror::Error, Debug)]
enum DirectionCharError {
    #[error("unrecognized character")]
    UnrecognizedChar,
}

impl TryFrom<char> for Direction {
    type Error = DirectionCharError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            'L' => Ok(Self::Left),
            'R' => Ok(Self::Right),
            _ => Err(DirectionCharError::UnrecognizedChar),
        }
    }
}

/// A node from input, containing the 3 character label of the node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Node([char; 3]);

/// An error parsing a [`Node`] from a string.
#[derive(thiserror::Error, Debug)]
enum ParseNodeError {
    #[error("expected exactly 3 characters")]
    InvalidLength,
}

impl FromStr for Node {
    type Err = ParseNodeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let characters: Vec<char> = s.chars().take(4).collect();

        if characters.len() != 3 {
            return Err(ParseNodeError::InvalidLength);
        }

        <[char; 3]>::try_from(characters).map_or_else(|_| unreachable!(), |arr| Ok(Self(arr)))
    }
}

/// The input of map document data, containing a direction sequence and connections of nodes.
#[derive(Debug)]
struct MapDocuments {
    /// A sequence of directions.
    directions: Vec<Direction>,
    /// A network of labeled nodes as a map, where keys are source nodes and values are pairs of
    /// connected nodes with the first connecting to the left and the second to the right.
    network: HashMap<Node, (Node, Node)>,
}

/// An error parsing [`MapDocuments`] from input.
#[derive(thiserror::Error, Debug)]
enum ParseMapDocumentsError {
    #[error("expected first line for directions")]
    NoDirections,

    #[error("no directions were parsed")]
    EmptyDirections,

    #[error("expected a block of lines of node connections for a network, after directions")]
    NoNetwork,

    #[error("expected \" = \" to delimit source label from connections")]
    ExpectedEqualDelimiter,

    #[error("expected parenthesis wrapping connections")]
    ExpectedParenthesisWrap,

    #[error("expected \", \" to delimit the connections")]
    ExpectedConnectionDelimiter,
}

impl ParseData for MapDocuments {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut scanner = InputScanner::new(input);

        let directions: Vec<_> = scanner
            .next_in_sequence(|_, line| {
                line.chars()
                    .map(Direction::try_from)
                    .collect::<Result<_, _>>()
            })?
            .ok_or(ParseMapDocumentsError::NoDirections)?;

        if directions.is_empty() {
            return Err(ParseMapDocumentsError::EmptyDirections.into());
        }

        scanner
            .skip_empty()
            .ok_or(ParseMapDocumentsError::NoNetwork)?;

        let network = scanner
            .collect_sequence(|_, line| -> DynamicResult<_> {
                let (source_label, connections) = line
                    .split_once(" = ")
                    .ok_or(ParseMapDocumentsError::ExpectedEqualDelimiter)?;
                let source_node: Node = parse_with_context(source_label)?;

                if !connections.starts_with('(') || !connections.ends_with(')') {
                    return Err(ParseMapDocumentsError::ExpectedParenthesisWrap.into());
                }

                let (left_label, right_label) = connections[1..connections.len() - 1]
                    .split_once(", ")
                    .ok_or(ParseMapDocumentsError::ExpectedConnectionDelimiter)?;

                let left_node: Node = parse_with_context(left_label)?;
                let right_node: Node = parse_with_context(right_label)?;

                Ok((source_node, (left_node, right_node)))
            })?
            .into_iter()
            .collect();

        Ok(Self {
            directions,
            network,
        })
    }
}

/*
For part 1, follow the directions to travel from node `AAA` to `ZZZ`. The direction sequence can
repeat as many times as necessary.

Return how many steps are required to reach `ZZZ`.
*/

impl MapDocuments {
    /// Get a cyclical iterator of directions, as a pair of the direction index and the
    /// [`Direction`].
    fn get_directions_cycle(&self) -> impl Iterator<Item = (usize, &Direction)> {
        self.directions.iter().enumerate().cycle()
    }

    /// Try to get the next node with a current node and direction. If the current node has no
    /// connections, returns `None`.
    fn next_node(&self, current: &Node, direction: Direction) -> Option<Node> {
        self.network
            .get(current)
            .map(|connections| match direction {
                Direction::Left => connections.0,
                Direction::Right => connections.1,
            })
    }
}

struct Day08;

impl Solution<PartOne> for Day08 {
    type Input = MapDocuments;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut directions_cycle = input.get_directions_cycle();

        let mut visited = HashSet::new();

        let mut current_node = *input
            .network
            .keys()
            .find(|n| n.0 == ['A', 'A', 'A'])
            .expect("input should contain AAA source node label to start from");

        let mut steps: Self::Output = 0;
        while current_node.0 != ['Z', 'Z', 'Z'] {
            let (direction_idx, direction) = directions_cycle
                .next()
                .expect("cycle iterator should always have next value");

            assert!(
                visited.insert((current_node, direction_idx)),
                "circular path detected: current_node = {current_node:?}, direction_idx = {direction_idx}"
            );

            if let Some(next_node) = input.next_node(&current_node, *direction) {
                current_node = next_node;

                steps = steps
                    .checked_add(1)
                    .expect("should not overflow when incrementing steps");
            } else {
                // dead end
                panic!("failed to find connections from node: {current_node:?}");
            }
        }

        Ok(steps)
    }
}

/*
For part 2, now all nodes that end in `A` are start nodes and must be traversed simultaneously until
all paths reach nodes that end in `Z`. Still return how many steps are necessary.
*/

impl Node {
    /// Get the last character in the node label.
    fn last_char(&self) -> char {
        self.0[2]
    }
}

impl MapDocuments {
    /// Count how many steps through directions it will take for some starting node to reach a node
    /// satisfying the predicate.
    fn steps_to<P>(&self, start_node: &Node, mut predicate: P) -> u32
    where
        P: FnMut(&Node) -> bool,
    {
        let mut directions_cycle = self.get_directions_cycle();

        let mut current_node = *start_node;
        let mut steps: u32 = 0;

        while !predicate(&current_node) {
            let (_, direction) = directions_cycle
                .next()
                .expect("cycle iterator should always have next value");

            if let Some(next_node) = self.next_node(&current_node, *direction) {
                current_node = next_node;
                steps = steps
                    .checked_add(1)
                    .expect("should not overflow when incrementing steps");
            } else {
                // dead end
                panic!("failed to find connections from node: {current_node:?}");
            }
        }

        steps
    }
}

fn least_common_multiple(numbers: &[u32]) -> u64 {
    fn greatest_common_divisor(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            greatest_common_divisor(b, a % b)
        }
    }

    if numbers.is_empty() {
        return 0;
    }

    let mut result = u64::from(numbers[0]);
    for &num in &numbers[1..] {
        let large_num = u64::from(num);
        result = result
            .checked_mul(large_num)
            .expect("should not overflow when multiplying")
            .checked_div(greatest_common_divisor(result, large_num))
            .expect("should not divide by 0");
    }
    result
}

impl Solution<PartTwo> for Day08 {
    type Input = MapDocuments;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // others online found a pattern in the data following the assertion:
        // > for any start node (A), the number of steps to reach a first end node along the path
        // > (A to Z) will be the same number of steps between each following end node (Z to Z)
        // that leads to a least common multiple from these steps/intervals being calculable and the
        // solution

        let start_nodes: Vec<Node> = input
            .network
            .keys()
            .filter(|node| node.last_char() == 'A')
            .copied()
            .collect();
        assert!(
            !start_nodes.is_empty(),
            "input should contain source nodes ending in \"A\" to start from"
        );

        let end_intervals: Vec<_> = start_nodes
            .into_iter()
            .map(|node| input.steps_to(&node, |n| n.last_char() == 'Z'))
            .collect();

        Ok(least_common_multiple(&end_intervals))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT_ONE: &str = r"LLR

AAA = (BBB, BBB)
BBB = (AAA, ZZZ)
ZZZ = (ZZZ, ZZZ)
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = MapDocuments::parse(EXAMPLE_INPUT_ONE)?;
        let result = <Day08 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 6);
        Ok(())
    }

    const EXAMPLE_INPUT_TWO: &str = r"LR

11A = (11B, XXX)
11B = (XXX, 11Z)
11Z = (11B, XXX)
22A = (22B, XXX)
22B = (22C, 22C)
22C = (22Z, 22Z)
22Z = (22B, 22B)
XXX = (XXX, XXX)
";

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = MapDocuments::parse(EXAMPLE_INPUT_TWO)?;
        let result = <Day08 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 6);
        Ok(())
    }
}

use std::collections::HashMap;
use std::num::ParseIntError;
use std::str::FromStr;

use aoc_framework::parsing::{InputScanner, ParseContextError, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use regex::Regex;

use crate::checked_product::CheckedProduct;

#[solution_runner(name = "Day 19: Aplenty", parsed = System, part_one = Day19, part_two = Day19)]
impl super::AdventOfCode2023<19> {}

/*
Input is a system described with a collection of workflows for evaluating parts, an empty line, and
a collection of parts' ratings.

Ratings for a part are defined in a line, with curly braces wrapping a comma-separated list of
key-value pairs separated with `=`. Keys are a part category, and values are number ratings in that
category. Part categories are `x`, `m`, `a`, and `s`.

A workflow is defined in a single line, with a name followed by curly braces wrapping its
comma-separated rules. Most rules can be formatted as a part category to compare, a comparison
operator (`>` or `<`), a number to compare against, `:`, and a name of another workflow to redirect
to. Alternatively, the redirect workflow name can be one of the reserved names `R` or `A` to mark a
rejection or acceptance. The last rule omits condition information and only provides a redirect
workflow name, `R`, or `A`.
*/

// -- Structures --

#[derive(Debug, Clone, Copy)]
enum PartCategory {
    X,
    M,
    A,
    S,
}

#[derive(Debug, Clone, Copy)]
struct PartRatings {
    x: u32,
    m: u32,
    a: u32,
    s: u32,
}

impl PartRatings {
    /// Get a part's rating for a category.
    fn get_rating(&self, category: PartCategory) -> u32 {
        match category {
            PartCategory::X => self.x,
            PartCategory::M => self.m,
            PartCategory::A => self.a,
            PartCategory::S => self.s,
        }
    }
}

/// A result of running a workflow.
#[derive(Debug, PartialEq, Eq)]
enum WorkflowResult {
    Accepted,
    Rejected,
    /// Redirect to another workflow to continue. Contains the name of the workflow.
    Redirect(String),
}

#[derive(Debug, PartialEq, Eq)]
enum ConditionalOperation {
    GreaterThan,
    LessThan,
}

/// A conditional rule in a workflow.
#[derive(Debug)]
struct ConditionalRule {
    category: PartCategory,
    operation: ConditionalOperation,
    value: u32,
    result: WorkflowResult,
}

#[derive(Debug)]
struct WorkflowRules {
    /// The sequence of conditional rules processed in the workflow.
    rules: Vec<ConditionalRule>,
    /// The last rule's result, as it doesn't have a condition to check.
    last_rule_result: WorkflowResult,
}

#[derive(Debug)]
struct System {
    workflows: HashMap<String, WorkflowRules>,
    parts_ratings: Vec<PartRatings>,
}

// -- Parsing --

#[derive(thiserror::Error, Debug)]
enum WorkflowResultTryFromStringError {
    #[error("expected alphabetic characters in workflow name")]
    ExpectedAlphabetic,
}

impl TryFrom<&str> for WorkflowResult {
    type Error = WorkflowResultTryFromStringError;

    /// Converts a string to a workflow result.
    ///
    /// Expects one of the special names (`A` or `R`), or an alphabetic workflow name for
    /// redirection.
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "A" => Ok(Self::Accepted),
            "R" => Ok(Self::Rejected),
            name => name
                .chars()
                .all(char::is_alphabetic)
                .then(|| Self::Redirect(name.to_owned()))
                .ok_or(WorkflowResultTryFromStringError::ExpectedAlphabetic),
        }
    }
}

#[derive(thiserror::Error, Debug)]
enum ParseConditionalRuleError {
    #[error(
        "string not in valid format for conditional rule\nexpected category (`x`, `m`, `a`, `s`), operation (`>`, `<`), positive integer, `:`, and alphabetic result name"
    )]
    InvalidFormat,
}

struct ConditionalRuleParser {
    re: Regex,
}

impl ConditionalRuleParser {
    fn new() -> Self {
        let re = Regex::new(r"^([xmas])(>|<)(\d+):([a-zA-Z]+)$")
            .expect("regex should successfully build");
        Self { re }
    }

    /// Parse a string as a conditional rule.
    ///
    /// The format expected is a category (`x`, `m`, `a`, or `s`), an operation (`>` or `<`), an
    /// unsigned integer, `:`, and an alphabetic result name.
    fn parse(&self, s: &str) -> Result<ConditionalRule, ParseConditionalRuleError> {
        let (_, [category_str, operation_str, value_str, result_str]) = self
            .re
            .captures(s)
            .ok_or(ParseConditionalRuleError::InvalidFormat)?
            .extract();

        let category = match category_str {
            "x" => PartCategory::X,
            "m" => PartCategory::M,
            "a" => PartCategory::A,
            "s" => PartCategory::S,
            _ => unreachable!(),
        };

        let operation = match operation_str {
            ">" => ConditionalOperation::GreaterThan,
            "<" => ConditionalOperation::LessThan,
            _ => unreachable!(),
        };

        let value = value_str
            .parse()
            .expect("regex pattern should assert digits in string");

        let result = WorkflowResult::try_from(result_str)
            .expect("regex pattern should assert alphabetic characters");

        Ok(ConditionalRule {
            category,
            operation,
            value,
            result,
        })
    }
}

#[derive(thiserror::Error, Debug)]
enum ParseWorkflowRulesError {
    #[error("expected curly braces wrapping the workflow rules")]
    ExpectedWrappingCurlyBraces,

    #[error("expected at least one rule")]
    ExpectedNonEmpty,

    #[error("failed to parse a conditional rule in the workflow")]
    ParseConditionalRuleError(#[from] ParseContextError<ParseConditionalRuleError>),

    #[error("failed to parse last rule")]
    ParseLastRuleError(#[from] ParseContextError<WorkflowResultTryFromStringError>),
}

impl FromStr for WorkflowRules {
    type Err = ParseWorkflowRulesError;

    /// Parse a string format of a workflow's sequence of rules.
    ///
    /// It is expected the rules are wrapped in curly braces (`{`, `}`), rules are separated with
    /// commas, all but the last rule format as conditional rules, and the last rule is an
    /// alphabetic workflow name or a special name (`A` or `R`).
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.starts_with('{') || !s.ends_with('}') {
            return Err(ParseWorkflowRulesError::ExpectedWrappingCurlyBraces);
        }

        let mut rules_sequence: Vec<_> = s[1..s.len() - 1].split(',').collect();

        // extract last rule to parse separately
        let last_rule = rules_sequence
            .pop()
            .ok_or(ParseWorkflowRulesError::ExpectedNonEmpty)?;

        let rule_parser = ConditionalRuleParser::new();
        let rules: Vec<_> = rules_sequence
            .into_iter()
            .map(|rule| {
                rule_parser
                    .parse(rule)
                    .map_err(|source| ParseContextError::new(source, rule))
            })
            .collect::<Result<_, _>>()?;

        let last_rule_result = WorkflowResult::try_from(last_rule)
            .map_err(|source| ParseContextError::new(source, last_rule))?;

        Ok(Self {
            rules,
            last_rule_result,
        })
    }
}

#[derive(thiserror::Error, Debug)]
enum ParsePartRatingsError {
    #[error("expected curly braces wrapping the ratings")]
    ExpectedWrappingCurlyBraces,

    #[error("expected equals sign to separate a key-value pair: {0:?}")]
    ExpectedEqualsDelimiter(String),

    #[error("expected key \"x\" in ratings")]
    ExpectedKeyX,

    #[error("expected key \"m\" in ratings")]
    ExpectedKeyM,

    #[error("expected key \"a\" in ratings")]
    ExpectedKeyA,

    #[error("expected key \"s\" in ratings")]
    ExpectedKeyS,

    #[error("failed to parse value")]
    ParseValueError(#[from] ParseContextError<ParseIntError>),
}

impl FromStr for PartRatings {
    type Err = ParsePartRatingsError;

    /// Parse a string format of part ratings.
    ///
    /// It is expected the ratings are wrapped in curly braces (`{`, `}`), comma-separates key `=`
    /// value pairs, and that the keys `x`, `m`, `a`, & `s` are present.
    /// Values are expected to be unsigned integers.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn get_value(
            pairs: &[(&str, &str)],
            key: &str,
            key_error: ParsePartRatingsError,
        ) -> Result<u32, ParsePartRatingsError> {
            let value = pairs
                .iter()
                .find_map(|&(k, v)| (k == key).then_some(v))
                .ok_or(key_error)?;
            parse_with_context(value).map_err(std::convert::Into::into)
        }

        if !s.starts_with('{') || !s.ends_with('}') {
            return Err(ParsePartRatingsError::ExpectedWrappingCurlyBraces);
        }
        let ratings = &s[1..s.len() - 1];

        let pairs: Vec<_> = ratings
            .split(',')
            .map(|p| {
                p.split_once('=')
                    .ok_or_else(|| ParsePartRatingsError::ExpectedEqualsDelimiter(p.to_owned()))
            })
            .collect::<Result<_, _>>()?;

        let x = get_value(&pairs, "x", ParsePartRatingsError::ExpectedKeyX)?;

        let m = get_value(&pairs, "m", ParsePartRatingsError::ExpectedKeyM)?;

        let a = get_value(&pairs, "a", ParsePartRatingsError::ExpectedKeyA)?;

        let s = get_value(&pairs, "s", ParsePartRatingsError::ExpectedKeyS)?;

        Ok(Self { x, m, a, s })
    }
}

#[derive(thiserror::Error, Debug)]
enum ParseSystemError {
    #[error("expected workflow rules starting with a curly brace ({:?})", '{')]
    MissingWorkflowRulesStart,

    #[error("expected workflow name to be alphabetic: {0:?}")]
    ExpectedAlphabeticWorkflowName(String),

    #[error("expected workflow name to not match a special workflow result name: {0:?}")]
    WorkflowNameIsSpecialWorkflowResultName(String),
}

impl ParseData for System {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut scanner = InputScanner::new(input);

        let workflows = scanner
            .collect_sequence(|_, line| -> DynamicResult<_> {
                let (rules_start_idx, _) = line
                    .char_indices()
                    .find(|&(_, ch)| ch == '{')
                    .ok_or(ParseSystemError::MissingWorkflowRulesStart)?;
                let (name_str, rules_str) = line.split_at(rules_start_idx);

                let name = match WorkflowResult::try_from(name_str) {
                    Ok(WorkflowResult::Redirect(nm)) => nm,
                    Err(WorkflowResultTryFromStringError::ExpectedAlphabetic) => {
                        return Err(ParseSystemError::ExpectedAlphabeticWorkflowName(
                            name_str.to_owned(),
                        )
                        .into());
                    }
                    Ok(_) => {
                        return Err(ParseSystemError::WorkflowNameIsSpecialWorkflowResultName(
                            name_str.to_owned(),
                        )
                        .into());
                    }
                };

                let rules: WorkflowRules = rules_str.parse()?;

                Ok((name, rules))
            })?
            .into_iter()
            .collect();

        scanner.skip_empty();

        let parts_ratings = scanner.collect_sequence(|_, line| line.parse())?;

        Ok(Self {
            workflows,
            parts_ratings,
        })
    }
}

/*
For part 1, process each parts' ratings by starting with the workflow named `in`. The first rule
that a part satisfies in a workflow should lead to redirecting to another workflow to continue
processing, or result in the part being rejected or accepted. Collect all accepted parts and sum the
ratings of the parts together.
*/

impl ConditionalRule {
    /// Process a part's ratings to determine if this rule yields a result.
    ///
    /// If the part satisfies the rule, returns `Some` containing the result.
    /// Otherwise returns `None`.
    fn process(&self, part_ratings: &PartRatings) -> Option<&WorkflowResult> {
        let rating = part_ratings.get_rating(self.category);
        let success = match self.operation {
            ConditionalOperation::GreaterThan => rating > self.value,
            ConditionalOperation::LessThan => rating < self.value,
        };
        success.then_some(&self.result)
    }
}

impl WorkflowRules {
    /// Process a part's ratings to determine a result from workflow rules.
    ///
    /// The first rule that is satisfied will have its result returned.
    fn process(&self, part_ratings: &PartRatings) -> &WorkflowResult {
        self.rules
            .iter()
            .find_map(|r| r.process(part_ratings))
            .unwrap_or(&self.last_rule_result)
    }
}

/// Determine the final result of a part processed through workflows.
fn find_part_result<'a>(
    workflows: &'a HashMap<String, WorkflowRules>,
    starting_workflow_name: &str,
    part_ratings: &PartRatings,
) -> &'a WorkflowResult {
    let mut current_name = starting_workflow_name.to_owned();
    loop {
        let workflow = workflows
            .get(&current_name)
            .expect("workflow name should be in workflows");
        let result = workflow.process(part_ratings);
        match result {
            WorkflowResult::Redirect(name) => {
                current_name = name.clone();
            }
            _ => return result,
        }
    }
}

impl PartRatings {
    /// Calculate the sum of all ratings.
    fn sum(&self) -> u32 {
        [self.x, self.m, self.a, self.s]
            .into_iter()
            .checked_sum()
            .expect("sum of part's ratings should not overflow")
    }
}

struct Day19;

impl Solution<PartOne> for Day19 {
    type Input = System;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let sum = input
            .parts_ratings
            .iter()
            .filter(|&pr| *find_part_result(&input.workflows, "in", pr) == WorkflowResult::Accepted)
            .map(PartRatings::sum)
            .checked_sum()
            .expect("sum of part sums should not overflow");
        Ok(sum)
    }
}

/*
For part 2, part ratings are confirmed to be in the range 1 to 4000 (inclusive). Calculate across
all distinct combinations of ratings how many would be accepted by the input workflows.
*/

impl PartRatings {
    /// Construct a new part ratings instance from self with the `category` set to `value`.
    fn with_category(self, category: PartCategory, value: u32) -> Self {
        match category {
            PartCategory::X => Self { x: value, ..self },
            PartCategory::M => Self { m: value, ..self },
            PartCategory::A => Self { a: value, ..self },
            PartCategory::S => Self { s: value, ..self },
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct PartRatingsRange {
    /// Inclusive minimum of range.
    min: PartRatings,
    /// Exclusive maximum of range.
    exclusive_max: PartRatings,
}

impl PartRatingsRange {
    /// Construct a range with all ratings categories set to the inclusive minimum and exclusive
    /// maximum.
    fn from(min: u32, exclusive_max: u32) -> Self {
        Self {
            min: PartRatings {
                x: min,
                m: min,
                a: min,
                s: min,
            },
            exclusive_max: PartRatings {
                x: exclusive_max,
                m: exclusive_max,
                a: exclusive_max,
                s: exclusive_max,
            },
        }
    }

    /// Count distinct combinations within this range.
    fn count_distinct(&self) -> u64 {
        // should be product of differences
        [
            self.exclusive_max
                .x
                .checked_sub(self.min.x)
                .expect("difference of `x` range should not overflow"),
            self.exclusive_max
                .m
                .checked_sub(self.min.m)
                .expect("difference of `m` range should not overflow"),
            self.exclusive_max
                .a
                .checked_sub(self.min.a)
                .expect("difference of `a` range should not overflow"),
            self.exclusive_max
                .s
                .checked_sub(self.min.s)
                .expect("difference of `s` range should not overflow"),
        ]
        .into_iter()
        .map(u64::from)
        .checked_product()
        .expect("product of property range counts should not overflow")
    }
}

impl ConditionalRule {
    /// Split a ratings range by this rule, returning (passing, failing) ranges.
    ///
    /// The passing range satisfies this rule and should be evaluated with this rule's result.
    ///
    /// If `range` would not be split by this rule, either of the passing or failing ranges will
    /// be `None` with the other matching `range`.
    fn split_range(
        &self,
        range: PartRatingsRange,
    ) -> (Option<PartRatingsRange>, Option<PartRatingsRange>) {
        let (min_value, exclusive_max_value) = match self.category {
            PartCategory::X => (range.min.x, range.exclusive_max.x),
            PartCategory::M => (range.min.m, range.exclusive_max.m),
            PartCategory::A => (range.min.a, range.exclusive_max.a),
            PartCategory::S => (range.min.s, range.exclusive_max.s),
        };
        let max_value = exclusive_max_value.saturating_sub(1);

        match self.operation {
            ConditionalOperation::GreaterThan => {
                if max_value <= self.value {
                    // no passing range
                    return (None, Some(range));
                } else if min_value > self.value {
                    // no failing range
                    return (Some(range), None);
                }

                let split_point = self.value + 1;
                (
                    // passing
                    Some(PartRatingsRange {
                        min: range.min.with_category(self.category, split_point),
                        exclusive_max: range
                            .exclusive_max
                            .with_category(self.category, exclusive_max_value),
                    }),
                    // failing
                    Some(PartRatingsRange {
                        min: range.min.with_category(self.category, min_value),
                        exclusive_max: range
                            .exclusive_max
                            .with_category(self.category, split_point),
                    }),
                )
            }
            ConditionalOperation::LessThan => {
                if min_value >= self.value {
                    // no passing range
                    return (None, Some(range));
                } else if max_value < self.value {
                    // no failing range
                    return (Some(range), None);
                }

                // rule's value is the split point
                (
                    // passing
                    Some(PartRatingsRange {
                        min: range.min.with_category(self.category, min_value),
                        exclusive_max: range.exclusive_max.with_category(self.category, self.value),
                    }),
                    // failing
                    Some(PartRatingsRange {
                        min: range.min.with_category(self.category, self.value),
                        exclusive_max: range
                            .exclusive_max
                            .with_category(self.category, exclusive_max_value),
                    }),
                )
            }
        }
    }
}

/// Count the number of accepted parts by workflows (from starting workflow name) given a ratings
/// range.
fn count_accepted_parts_range(
    workflows: &HashMap<String, WorkflowRules>,
    starting_workflow_name: &str,
    range: PartRatingsRange,
) -> u64 {
    fn count_from_result(
        workflows: &HashMap<String, WorkflowRules>,
        result: &WorkflowResult,
        range: &PartRatingsRange,
    ) -> u64 {
        match result {
            WorkflowResult::Accepted => range.count_distinct(),
            WorkflowResult::Rejected => 0,
            // recursively count with a redirected workflow
            WorkflowResult::Redirect(name) => count_accepted_parts_range(workflows, name, *range),
        }
    }

    let current_workflow = workflows
        .get(starting_workflow_name)
        .expect("workflow name should be in workflows");
    let mut count: u64 = 0;
    let mut current_range = range;

    for rule in &current_workflow.rules {
        let (passing, failing) = rule.split_range(current_range);

        if let Some(passing_range) = passing {
            count = count
                .checked_add(count_from_result(workflows, &rule.result, &passing_range))
                .expect("counting accepted parts should not overflow");
        }

        if let Some(failing_range) = failing {
            // continue to next rule with the failing range
            current_range = failing_range;
        } else {
            // no more range to evaluate
            return count;
        }
    }

    // any remaining range is processed by last rule result
    count
        .checked_add(count_from_result(
            workflows,
            &current_workflow.last_rule_result,
            &current_range,
        ))
        .expect("counting accepted parts should not overflow")
}

impl Solution<PartTwo> for Day19 {
    type Input = System;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(count_accepted_parts_range(
            &input.workflows,
            "in",
            PartRatingsRange::from(1, 4001),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"px{a<2006:qkq,m>2090:A,rfg}
pv{a>1716:R,A}
lnx{m>1548:A,A}
rfg{s<537:gd,x>2440:R,A}
qs{s>3448:A,lnx}
qkq{x<1416:A,crn}
crn{x>2662:A,R}
in{s<1351:px,qqz}
qqz{s>2770:qs,m<1801:hdj,R}
gd{a>3333:R,R}
hdj{m>838:A,pv}

{x=787,m=2655,a=1222,s=2876}
{x=1679,m=44,a=2067,s=496}
{x=2036,m=264,a=79,s=2244}
{x=2461,m=1339,a=466,s=291}
{x=2127,m=1623,a=2188,s=1013}
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = System::parse(EXAMPLE_INPUT)?;
        let result = <Day19 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 19114);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = System::parse(EXAMPLE_INPUT)?;
        let result = <Day19 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 167_409_079_868_000);
        Ok(())
    }
}

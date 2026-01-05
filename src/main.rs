#![warn(clippy::pedantic)]
#![warn(
    clippy::allow_attributes,
    clippy::allow_attributes_without_reason,
    clippy::branches_sharing_code,
    clippy::collection_is_never_read,
    clippy::equatable_if_let,
    clippy::needless_collect,
    clippy::needless_pass_by_ref_mut,
    clippy::option_if_let_else,
    clippy::set_contains_or_insert,
    clippy::suboptimal_flops,
    clippy::suspicious_operation_groupings,
    clippy::trait_duplication_in_bounds,
    clippy::type_repetition_in_bounds,
    clippy::use_self,
    clippy::useless_let_if_seq
)]
#![deny(clippy::unwrap_used)]

use std::fmt::Display;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Error, Result};
use aoc_framework::PartKind;
use aoc_framework::runner::OutputHandler;
use clap::{ArgAction, Parser};

mod checked_product;
mod solutions;

/// Advent of Code 2023 puzzle solver.
#[derive(Parser, Debug)]
struct Cli {
    /// The day's solution to run (e.g. 1, 2, etc).
    day: u8,

    /// Sets an alternative input file to use over default input.
    #[arg(short, long, value_name = "FILE")]
    input: Option<PathBuf>,

    /// Measure and print the durations of parsing and solving parts.
    #[arg(short, long, action = ArgAction::SetTrue)]
    timed: bool,

    /// Minimum duration (in milliseconds) required to print timing.
    /// 0 = always print.
    #[arg(long, value_name = "NUMBER", default_value_t)]
    min_timing_ms: u64,
}

/// Read the default input file for a day to a string.
fn get_default_input(day: u8) -> Result<String> {
    let filename = format!("day{day:02}.txt");
    let path = PathBuf::from("inputs").join(filename);

    fs::read_to_string(&path).with_context(|| {
        format!(
            "default input file missing: {}\n\n\
            please create the file or provide the input file argument",
            path.display()
        )
    })
}

/// Read the given input file to a string.
fn get_input(input_file: &PathBuf) -> Result<String> {
    fs::read_to_string(input_file)
        .with_context(|| format!("could not read input file at: {}", input_file.display()))
}

struct CliOutputHandler {
    /// A minimum duration to filter any outputs of duration by.
    min_duration: Duration,
}

impl CliOutputHandler {
    fn new(min_duration: Duration) -> Self {
        Self { min_duration }
    }

    fn format_duration(duration: Duration) -> String {
        const ONE_SECOND: Duration = Duration::from_secs(1);
        const ONE_MILLISECOND: Duration = Duration::from_millis(1);
        const ONE_MICROSECOND: Duration = Duration::from_micros(1);
        const DECIMAL_PLACES: usize = 3;

        if duration >= ONE_SECOND {
            format!("{:.*} seconds", DECIMAL_PLACES, duration.as_secs_f32())
        } else {
            let nanos = duration.subsec_nanos();
            if duration >= ONE_MILLISECOND {
                format!("{:.*} milliseconds", DECIMAL_PLACES, f64::from(nanos) / 1e6)
            } else if duration >= ONE_MICROSECOND {
                format!("{:.*} microseconds", DECIMAL_PLACES, f64::from(nanos) / 1e3)
            } else {
                format!("{nanos} nanoseconds")
            }
        }
    }

    /// Convert an optional duration into a formatted duration, filtering out if the duration is
    /// shorter than the minimum duration.
    fn format_optional_duration_above_min(&self, duration: Option<Duration>) -> Option<String> {
        duration
            .filter(|d| *d >= self.min_duration)
            .map(Self::format_duration)
    }
}

impl OutputHandler for CliOutputHandler {
    fn solution_name(&mut self, name: &str) {
        println!("= {name} =");
    }

    fn parse_start(&mut self) {
        // do nothing
    }

    fn parse_end(&mut self, duration_opt: Option<Duration>) {
        if let Some(formatted_duration) = self.format_optional_duration_above_min(duration_opt) {
            println!("Input parsed in {formatted_duration}");
        }
    }

    fn part_start(&mut self, part: PartKind) {
        println!("-- {part} --");
    }

    fn part_output(
        &mut self,
        _part: PartKind,
        output: &dyn Display,
        duration_opt: Option<Duration>,
    ) {
        if let Some(formatted_duration) = self.format_optional_duration_above_min(duration_opt) {
            println!("{output} ({formatted_duration})");
        } else {
            println!("{output}");
        }
    }
}

fn main() -> Result<()> {
    let args = Cli::parse();
    let input_str = args.input.map_or_else(
        || get_default_input(args.day),
        |input_file| get_input(&input_file),
    )?;
    let mut handler = CliOutputHandler::new(Duration::from_millis(args.min_timing_ms));
    solutions::run_day(args.day, &input_str, &mut handler, args.timed).map_err(|dyn_error| {
        let anyhow_error = Error::from_boxed(dyn_error);
        anyhow_error.context("failed to run solution")
    })
}

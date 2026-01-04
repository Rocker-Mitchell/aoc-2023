//! Utility functions and errors for parsing input.

use std::str::FromStr;

use thiserror::Error;

use crate::{DynamicError, DynamicResult};

/// A string parsing error with context of the string that was being parsed.
#[derive(Error, Debug)]
#[error("failed to parse string: {string:?}")]
pub struct ParseContextError<E>
where
    E: std::error::Error,
{
    /// The string that was being parsed.
    string: String,
    source: E,
}

/// Parse a string slice into another type.
///
/// This wraps [`str::parse`] and maps errors to [`ParseContextError`].
///
/// # Errors
///
/// Will return a [`ParseContextError`] with the given string as context and
/// [`F::Err`][FromStr::Err] as the source if it's not possible to parse the string into the desired
/// type.
pub fn parse_with_context<F>(string: &str) -> Result<F, ParseContextError<F::Err>>
where
    F: FromStr,
    F::Err: std::error::Error,
{
    string.parse::<F>().map_err(|source| ParseContextError {
        string: string.to_string(),
        source,
    })
}

/// A line in an input string caused a parsing error.
#[derive(Error, Debug)]
#[error("failure parsing line {}", .line_index.saturating_add(1))]
pub struct InvalidLine {
    /// The line index, zero based.
    /// This will be formatted to a one-based number for display.
    line_index: usize,
    source: DynamicError,
}

/// Parse lines with a closure, mapping any line's dynamic error with an [`InvalidLine`].
///
/// # Arguments
/// - `input` - The input string to parse.
/// - `offset` - An offset to add to the line index for [`InvalidLine`] errors. Useful when parsing
///   a later slice of input and errors should have any reported line index reflect the offset line
///   position from the original input. Set to `0` if no offset is needed.
/// - `parser` - A closure that takes a line string and returns a [`DynamicResult`].
///
/// # Errors
///
/// If parsing a line fails, an [`InvalidLine`] error is returned, sourcing the original error.
///
/// # Returns
///
/// An iterable of parsing results for each line.
pub fn parse_lines_with_offset<T, F>(
    input: &str,
    offset: usize,
    mut parser: F,
) -> impl Iterator<Item = Result<T, InvalidLine>>
where
    F: FnMut(&str) -> DynamicResult<T>,
{
    input.lines().enumerate().map(move |(index, line)| {
        parser(line).map_err(|source| InvalidLine {
            line_index: index.saturating_add(offset),
            source,
        })
    })
}

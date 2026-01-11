//! Utility functions and errors for parsing input.

use std::iter::{Enumerate, Peekable};
use std::str::{FromStr, Lines};

use thiserror::Error;

use crate::DynamicError;

/// A string parsing error with context of the string that was being parsed.
#[derive(Error, Debug)]
#[error("failed to parse string: {string:?}")]
pub struct ParseContextError<E>
where
    E: std::error::Error,
{
    /// The string that was being parsed.
    pub string: String,
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
    pub line_index: usize,
    source: DynamicError,
}

impl InvalidLine {
    /// Create an invalid line error with an error that can be converted to a [`DynamicError`] and a
    /// line index.
    fn new<E>(error: E, line_index: usize) -> Self
    where
        E: Into<DynamicError>,
    {
        Self {
            line_index,
            source: error.into(),
        }
    }
}

/// Parse input lines to an iterator of results.
///
/// # Arguments
/// - `input` - The input string to parse.
/// - `parser` - A closure that takes a line's index and string, returning a result.
///
/// # Errors
///
/// If parsing a line fails, its error is tracked as the source of an [`InvalidLine`] error.
///
/// # Returns
///
/// An iterator of parsing results for each line.
pub fn parse_input_lines<T, F, E>(
    input: &str,
    mut parser: F,
) -> impl Iterator<Item = Result<T, InvalidLine>>
where
    F: FnMut(usize, &str) -> Result<T, E>,
    E: Into<DynamicError>,
{
    input
        .lines()
        .enumerate()
        .map(move |(index, line)| parser(index, line).map_err(|e| InvalidLine::new(e, index)))
}

/// A utility to scan through lines of input, supporting processing of individual lines or blocks
/// separated by empty lines.
pub struct InputScanner<'a> {
    lines: Peekable<Enumerate<Lines<'a>>>,
}

impl<'a> InputScanner<'a> {
    /// Create a scanner from an input string.
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
            lines: input.lines().enumerate().peekable(),
        }
    }

    fn is_empty_line(line: &str) -> bool {
        line.trim().is_empty()
    }

    /// Advances past any empty or whitespace-only lines.
    ///
    /// The next non-empty line encountered will _not_ be consumed. Only empty lines are consumed.
    ///
    /// # Returns
    ///
    /// The line index and string of the next non-empty line is returned in a tuple in a `Some`.
    /// If all remaining lines were empty or there are no more lines to scan, returns `None`.
    pub fn skip_empty(&mut self) -> Option<(usize, &'a str)> {
        while let Some(&(index, line)) = self.lines.peek() {
            if Self::is_empty_line(line) {
                // consume the line
                self.lines.next();
            } else {
                return Some((index, line));
            }
        }
        None
    }

    /// Skip any number of empty lines then consume & parse the next line.
    ///
    /// Useful for scanning the first line of a block.
    ///
    /// # Arguments
    /// - `parser` - A closure that takes a line's index and string, returning a result.
    ///
    /// # Errors
    ///
    /// If parsing fails, its error is tracked as the source of an [`InvalidLine`] error.
    ///
    /// # Returns
    ///
    /// Returns `Some` containing the successful result of parsing.
    /// If the remaining lines scanned were empty or there are no more lines to scan, returns
    /// `None`.
    pub fn next_item<T, F, E>(&mut self, mut parser: F) -> Result<Option<T>, InvalidLine>
    where
        F: FnMut(usize, &str) -> Result<T, E>,
        E: Into<DynamicError>,
    {
        if let Some((index, line)) = self.skip_empty() {
            // consume the line
            self.lines.next();

            return parser(index, line)
                .map(Some)
                .map_err(|e| InvalidLine::new(e, index));
        }
        Ok(None)
    }

    /// Consume and parse the next line _only_ if it is not empty.
    ///
    /// If the next line is empty, the line will not be consumed.
    /// Useful for detecting the end of a block.
    ///
    /// # Arguments
    /// - `parser` - A closure that takes a line's index and string, returning a result.
    ///
    /// # Errors
    ///
    /// If parsing fails, its error is tracked as the source of an [`InvalidLine`] error.
    ///
    /// # Returns
    ///
    /// Returns `Some` containing the successful result of parsing.
    /// If the next line was empty or there are no more lines to scan, returns `None`.
    pub fn next_in_sequence<T, F, E>(&mut self, mut parser: F) -> Result<Option<T>, InvalidLine>
    where
        F: FnMut(usize, &str) -> Result<T, E>,
        E: Into<DynamicError>,
    {
        if let Some(&(index, line)) = self.lines.peek() {
            if Self::is_empty_line(line) {
                return Ok(None);
            }
            // consume the line after confirming it's valid
            self.lines.next();

            return parser(index, line)
                .map(Some)
                .map_err(|e| InvalidLine::new(e, index));
        }
        Ok(None)
    }

    /// Parse a sequence of non-empty lines, collecting into a vector.
    ///
    /// Parsing stops after an empty line is found, but does _not_ consume the empty line.
    ///
    /// # Errors
    ///
    /// If parsing a line fails, its error is tracked as the source of an [`InvalidLine`] error.
    ///
    /// # Returns
    ///
    /// Returns a vector of items parsed.
    /// If the next line was empty or there are no more lines to scan, vector will be empty.
    pub fn collect_sequence<T, F, E>(&mut self, mut parser: F) -> Result<Vec<T>, InvalidLine>
    where
        F: FnMut(usize, &str) -> Result<T, E>,
        E: Into<DynamicError>,
    {
        let mut results = Vec::new();
        while let Some(&(index, line)) = self.lines.peek() {
            if Self::is_empty_line(line) {
                break;
            }
            // consume the line after confirming it's valid
            self.lines.next();

            let item = parser(index, line).map_err(|e| InvalidLine::new(e, index))?;
            results.push(item);
        }
        Ok(results)
    }
}

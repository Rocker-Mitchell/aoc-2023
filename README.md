# Advent of Code 2023

My solution code to solve 2023's Advent of Code puzzles.

## Usage

Install Rust and run with Cargo:

```sh
# run a day's solution with default input file (./inputs/day01.txt)
cargo run --release -- 1

# use an alternate input file
cargo run --release -- 1 --input inputs/my-file.txt

# measure the time to parse and run parts
cargo run --release -- 1 --timed

# set minimum timing to print to 100 milliseconds
cargo run --release -- 1 --timed --min-timing-ms 100

# show usage
cargo run --release -- --help
```

### Inputs

Default input files are looked up relative to the current directory in an
`inputs/` directory with the naming pattern `day{dd}.txt` (ex:
`inputs/day03.txt`).
This repository intentionally ignores the `inputs/` directory in `.gitignore`
to avoid committing your personal puzzle inputs.

If the default file is missing, the CLI prints an error telling you which file
to create or you can provide `--input` to use an alternative file.

## Development

Useful commands:

```sh
# run all unit tests in the workspace
cargo test --workspace -- --test --no-capture

# run clippy for linting
cargo clippy --workspace --all-targets

# check formatting
cargo fmt --check
```

### Project Layout

- aoc-framework: library providing traits and utilities for implementing and
  running solutions.
- aoc-framework-macros: procedural macros for aoc-framework, which are
  re-exported.
- src: CLI binary and solution implementations.

use aoc_framework::parsing::{InputScanner, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};

#[solution_runner(
    name = "Day 5: If You Give A Seed A Fertilizer",
    parsed = Almanac,
    part_one = Day05,
    part_two = Day05
)]
impl super::AdventOfCode2023<5> {}

/*
Input is an almanac. It is formatted as multiple blocks separated by empty lines.

The first block is a `seeds: ` line with a space-separated list of numbers.

Following are blocks of maps for converting numbers from a source category to destination category
- `seed-to-soil map: ` converts seed number to soil number
- `soil-to-fertilizer map: ` for soil to fertilizer
- `fertilizer-to-water map: ` ...
- `water-to_light map: ` ...
- `light-to-temperature map: ` ...
- `temperature-to-humidity map: ` ...
- `humidity-to-location map: ` ...

> The order maps are defined has one's destination feed to the next's source.

A map defines ranges for conversion below the map name. Lines contain three numbers: the destination
range start, the source range start, and the range length.

Any source numbers outside ranges map one-to-one as the destination number.
*/

/// The integer type for numbers in the almanac.
///
/// Observed 10 digit numbers in input, so this should be sized to fit such.
type AlmanacNumber = u32;

/// The integer type for calculated offsets between [`AlmanacNumber`].
///
/// This is signed as offsets can be forward or backward, and is sized to handle the possible scale
/// of a difference.
type AlmanacNumberOffset = i64;

/// A mapped range of numbers.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct AlmanacMapRange {
    // order of props relevant when deriving Ord
    /// The start of the source range, inclusive.
    source_start: AlmanacNumber,

    /// The length of the range.
    length: AlmanacNumber,

    /// The start of the destination range, inclusive.
    destination_start: AlmanacNumber,
}

/// An error related to operations with an [`AlmanacMapRange`].
#[derive(thiserror::Error, Debug)]
enum AlmanacMapRangeError {
    /// A map range has a length of 0. Displays the associated destination & source starts to locate
    /// in input.
    #[error(
        "range length must be > 0 (destination_start = {destination_start}, source_start = {source_start})"
    )]
    EmptyRangeLen {
        destination_start: AlmanacNumber,
        source_start: AlmanacNumber,
    },

    /// Integer overflow occurred when calculating the offset from the given destination & source
    /// starts.
    #[error(
        "offset overflow when computing destination_start - source_start (destination_start = {destination_start}, source_start = {source_start})"
    )]
    OffsetOverflow {
        destination_start: AlmanacNumber,
        source_start: AlmanacNumber,
    },

    /// Integer overflow occurred when calculating a map range's source end with the given start &
    /// length.
    #[error(
        "source end overflow when calculating start + length - 1 (start = {start}, length = {length}"
    )]
    SourceEndOverflow {
        start: AlmanacNumber,
        length: AlmanacNumber,
    },
}

impl AlmanacMapRange {
    /// Create a map range with the given destination start, source start, and range length.
    fn new(
        destination_start: AlmanacNumber,
        source_start: AlmanacNumber,
        range_len: AlmanacNumber,
    ) -> Result<Self, AlmanacMapRangeError> {
        if range_len == 0 {
            return Err(AlmanacMapRangeError::EmptyRangeLen {
                destination_start,
                source_start,
            });
        }

        Ok(Self {
            source_start,
            length: range_len,
            destination_start,
        })
    }

    /// The offset of the source range to the destination range.
    fn offset(&self) -> Result<AlmanacNumberOffset, AlmanacMapRangeError> {
        AlmanacNumberOffset::from(self.destination_start)
            .checked_sub(self.source_start.into())
            .ok_or(AlmanacMapRangeError::OffsetOverflow {
                destination_start: self.destination_start,
                source_start: self.source_start,
            })
    }

    /// The end of the source range, inclusive.
    fn source_end(&self) -> Result<AlmanacNumber, AlmanacMapRangeError> {
        // length should be confirmed > 0 already
        self.source_start.checked_add(self.length - 1).ok_or(
            AlmanacMapRangeError::SourceEndOverflow {
                start: self.source_start,
                length: self.length,
            },
        )
    }

    /// Try to map an almanac number with this map range.
    /// If the number is out of range, returns `None`.
    fn try_map_number(&self, source_number: AlmanacNumber) -> Option<AlmanacNumber> {
        // NOTE I want to raise errors if the reason is from closely related data sourced from
        // parsed input, panic otherwise; this is a calculation on possibly unrelated/distant data,
        // so prefer panics
        if source_number < self.source_start
            || source_number
                > self
                    .source_end()
                    .expect("source end should be available for calculations")
        {
            return None;
        }

        let offset = self
            .offset()
            .expect("offset should be available for calculations");
        let dest_number = offset
            .checked_add(source_number.into())
            .expect("offsetting a number should not have integer overflow");
        Some(
            AlmanacNumber::try_from(dest_number)
                .expect("casting offset number to almanac number should not fail"),
        )
    }
}

/// A mapping of source numbers to destination numbers.
///
/// Contains a sorted collection of mapping ranges used for calculating offset destination numbers.
struct AlmanacMap(Vec<AlmanacMapRange>);

impl AlmanacMap {
    /// Create a map from an iterator of mapping ranges: a collection of tuples containing
    /// `(destination_start, source_start, range_len)`.
    fn from_ranges<I>(ranges: I) -> Result<Self, AlmanacMapRangeError>
    where
        I: IntoIterator<Item = (AlmanacNumber, AlmanacNumber, AlmanacNumber)>,
    {
        let mut ranges_vec: Vec<_> = ranges
            .into_iter()
            .map(|(destination_start, source_start, range_len)| {
                AlmanacMapRange::new(destination_start, source_start, range_len)
            })
            .collect::<Result<_, _>>()?;
        // sort ranges for part 2
        ranges_vec.sort();
        Ok(Self(ranges_vec))
    }

    /// Map a source number to a destination number.
    fn map_number(&self, source_number: AlmanacNumber) -> AlmanacNumber {
        // find a range that maps the number
        for range in &self.0 {
            if let Some(dest_number) = range.try_map_number(source_number) {
                return dest_number;
            }
        }
        // no range affects this number, return as-is
        source_number
    }
}

struct Almanac {
    /// Seed numbers parsed from input.
    seed_numbers: Vec<AlmanacNumber>,
    /// The sequence of maps for number conversions.
    ///
    /// The sequence of maps goes:
    ///
    /// 1. seed to soil
    /// 2. soil to fertilizer
    /// 3. fertilizer to water
    /// 4. water to light
    /// 5. light to temperature
    /// 6. temperature to humidity
    /// 7. humidity to location
    maps: [AlmanacMap; 7],
}

#[derive(thiserror::Error, Debug)]
enum AlmanacParseError {
    #[error("expected block for seeds")]
    MissingSeedsBlock,

    #[error("expected seeds line to start with \"seeds: \"")]
    MissingSeedsPrefix,

    /// A map block is missing, with the name for the block.
    #[error("expected block for {name} map")]
    MissingMapBlock { name: String },

    /// Expected a header line in a map block, with the found line.
    #[error("expected header line for map block: {0:?}")]
    ExpectedMapHeader(String),

    /// Expected a line formatted with three numbers for a range, with the found line.
    #[error("expected three space-separated numbers as a map range, found: {0:?}")]
    ExpectedRangeFormat(String),
}

impl ParseData for Almanac {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn parse_map(scanner: &mut InputScanner, map_name: &str) -> DynamicResult<AlmanacMap> {
            // expect header with map name
            let header_opt = scanner.next_item(|_, line| {
                let header = format!("{map_name} map:");
                if !line.contains(&header) {
                    return Err(AlmanacParseError::ExpectedMapHeader(header));
                }
                Ok(())
            })?;
            if header_opt.is_none() {
                return Err(AlmanacParseError::MissingMapBlock {
                    name: map_name.to_owned(),
                }
                .into());
            }

            let ranges = scanner.collect_sequence(|_, line| -> DynamicResult<_> {
                let values: Vec<_> = line.split_whitespace().collect();

                if values.len() != 3 {
                    return Err(AlmanacParseError::ExpectedRangeFormat(line.to_owned()).into());
                }

                let destination_start: AlmanacNumber = parse_with_context(values[0])?;
                let source_start: AlmanacNumber = parse_with_context(values[1])?;
                let range_len: AlmanacNumber = parse_with_context(values[2])?;

                Ok((destination_start, source_start, range_len))
            })?;

            Ok(AlmanacMap::from_ranges(ranges)?)
        }

        let mut scanner = InputScanner::new(input);

        let seed_numbers = scanner
            .next_in_sequence(|_, line| -> DynamicResult<_> {
                let seeds_list = line
                    .strip_prefix("seeds: ")
                    .ok_or(AlmanacParseError::MissingSeedsPrefix)?;
                let seed_numbers = seeds_list
                    .split_whitespace()
                    .map(parse_with_context)
                    .collect::<Result<_, _>>()?;
                Ok(seed_numbers)
            })?
            .ok_or(AlmanacParseError::MissingSeedsBlock)?;
        // TODO require even length for part 2?

        let seed_to_soil = parse_map(&mut scanner, "seed-to-soil")?;
        let soil_to_fertilizer = parse_map(&mut scanner, "soil-to-fertilizer")?;
        let fertilizer_to_water = parse_map(&mut scanner, "fertilizer-to-water")?;
        let water_to_light = parse_map(&mut scanner, "water-to-light")?;
        let light_to_temperature = parse_map(&mut scanner, "light-to-temperature")?;
        let temperature_to_humidity = parse_map(&mut scanner, "temperature-to-humidity")?;
        let humidity_to_location = parse_map(&mut scanner, "humidity-to-location")?;

        let maps = [
            seed_to_soil,
            soil_to_fertilizer,
            fertilizer_to_water,
            water_to_light,
            light_to_temperature,
            temperature_to_humidity,
            humidity_to_location,
        ];

        Ok(Self { seed_numbers, maps })
    }
}

/*
For part 1, find the location numbers for each seed number and return the smallest number.
*/

impl Almanac {
    /// Process the full sequence of maps to find the location number of a seed number.
    fn full_map_number(&self, seed_number: AlmanacNumber) -> AlmanacNumber {
        self.maps
            .iter()
            .fold(seed_number, |acc, map| map.map_number(acc))
    }
}

struct Day05;

impl Solution<PartOne> for Day05 {
    type Input = Almanac;
    type Output = AlmanacNumber;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(input
            .seed_numbers
            .iter()
            .map(|&sn| input.full_map_number(sn))
            .min()
            .expect("input should have seeds to map"))
    }
}

/*
For part 2, the seed numbers are now considered ranges of seeds by pairing every two numbers (even
length list) as the start of the range and the length.

Find the smallest location number as before.
*/

// so caching is not the solution, optimization problem is the size of seed ranges generating too
// many seeds
// - friend never converted seed range to seeds, he interprets how to translate a source range
//   through a map
//   - if a source range slots nicely within a map range, just offset the range start; if its wholly
//     outside any ranges, no change
//   - source range overlapping map ranges leads to generating new ranges, for however many map
//     ranges are touched (and source start to be mapped) and any gaps between

/// A definition of a number range.
struct NumberRange {
    /// The start of the range, inclusive.
    start: AlmanacNumber,
    /// The length of the range.
    length: AlmanacNumber,
}

impl NumberRange {
    /// The end of the range, inclusive.
    fn end(&self) -> AlmanacNumber {
        // TODO check overflows?
        self.length - 1 + self.start
    }
}

impl AlmanacMap {
    /// Map a source range into destination range(s).
    ///
    /// Depending on how the source range overlaps with map ranges, many destination ranges can be
    /// generated.
    fn map_range(&self, source_range: &NumberRange) -> Vec<NumberRange> {
        let mut dest_ranges = Vec::new();

        // track where a gap starts after processing a map range during iteration; init to source
        // start
        let mut gap_start = source_range.start;
        // iterate (assumed ordered) map ranges
        for map_range in &self.0 {
            let map_range_source_end = map_range
                .source_end()
                .expect("source end should be available for calculations");

            if source_range.start > map_range_source_end {
                // map range doesn't affect source range, skip
                continue;
            }

            if source_range.end() < map_range.source_start {
                // the remaining source range doesn't get affected by this map range or subsequent
                // ranges, break out of loop
                break;
            }

            if source_range.start < map_range.source_start {
                // need to generate 1:1 destination range from gap start to map range start
                // - map range start is exclusive for this gap, so length is difference
                let gap_length = map_range.source_start - gap_start;
                if gap_length > 0 {
                    dest_ranges.push(NumberRange {
                        start: gap_start,
                        length: gap_length,
                    });
                }
            }

            // determine the range intersecting the source range & map range
            let intersect_start = source_range.start.max(map_range.source_start);
            let intersect_end = source_range.end().min(map_range_source_end);
            // with start & end inclusive, length is difference plus 1
            let intersect_length = intersect_end - intersect_start + 1;

            // create a destination range by mapping the intersection start
            let dest_start = map_range
                .try_map_number(intersect_start)
                .expect("intersection start should be within map range");
            dest_ranges.push(NumberRange {
                start: dest_start,
                length: intersect_length,
            });

            // setup next gap start
            gap_start = intersect_end + 1;
        }

        // any remaining gap from the gap start to source end should generate a 1:1 destination
        // range
        let gap_length = source_range
            .length
            .saturating_sub(gap_start - source_range.start);
        if gap_length > 0 {
            dest_ranges.push(NumberRange {
                start: gap_start,
                length: gap_length,
            });
        }

        dest_ranges
    }
}

impl Almanac {
    /// Interpret the seed numbers as pairs of range start & length, structured into a collection of
    /// [`NumberRange`].
    fn seeds_as_ranges(&self) -> impl Iterator<Item = NumberRange> {
        self.seed_numbers.chunks_exact(2).map(|seed_range| {
            let start = seed_range[0];
            let length = seed_range[1];
            NumberRange { start, length }
        })
    }

    /// Process the full sequence of maps to convert a seed range to location range(s).
    fn full_map_range(&self, seed_range: NumberRange) -> Vec<NumberRange> {
        self.maps.iter().fold(vec![seed_range], |acc, map| {
            acc.iter()
                .flat_map(|source_range| map.map_range(source_range))
                .collect()
        })
    }
}

impl Solution<PartTwo> for Day05 {
    type Input = Almanac;
    type Output = AlmanacNumber;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        Ok(input
            .seeds_as_ranges()
            .flat_map(|sr| input.full_map_range(sr))
            .map(|range| range.start)
            .min()
            .expect("input should have seeds to map"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"seeds: 79 14 55 13

seed-to-soil map:
50 98 2
52 50 48

soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

water-to-light map:
88 18 7
18 25 70

light-to-temperature map:
45 77 23
81 45 19
68 64 13

temperature-to-humidity map:
0 69 1
1 0 69

humidity-to-location map:
60 56 37
56 93 4
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Almanac::parse(EXAMPLE_INPUT)?;
        let result = <Day05 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 35);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Almanac::parse(EXAMPLE_INPUT)?;
        let result = <Day05 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 46);
        Ok(())
    }
}

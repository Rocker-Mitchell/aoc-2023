use std::collections::{HashMap, HashSet};
use std::num::TryFromIntError;

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use nalgebra::{Point2, Vector2};

#[solution_runner(
    name = "Day 23: A Long Walk", parsed = Trails, part_one = Day23, part_two = Day23
)]
impl super::AdventOfCode2023<23> {}

/*
Input is a character grid of trails. `.` for paths, `#` for forest, and directions for slopes (`^`,
`>`, `v`, `<`). One path is on the top row as the start, and one on the bottom row as the end.
*/

#[derive(Debug, Clone, Copy)]
enum Direction {
    Up,
    Right,
    Down,
    Left,
}

#[derive(Debug)]
struct Trails {
    /// The start position on the top row.
    start: Point2<i32>,
    /// The end position on the bottom row.
    end: Point2<i32>,
    /// Coordinates of paths.
    ///
    /// This excludes the start and end positions.
    paths: HashSet<Point2<i32>>,
    /// Coordinates of slopes mapping their direction.
    slopes: HashMap<Point2<i32>, Direction>,
}

#[derive(thiserror::Error, Debug)]
enum ParseTrailsError {
    #[error("too many lines to represent y-coordinate")]
    LineIndexOverflow(#[source] TryFromIntError),

    #[error("too many characters to represent x-coordinate")]
    CharIndexOverflow(#[source] TryFromIntError),

    #[error("invalid character in grid: {0:?}")]
    InvalidChar(char),

    #[error("failed to find single start path in top row")]
    MissingStart,

    #[error("multiple paths detected in top row, expected exactly one for start")]
    MultipleStarts,

    #[error("failed to find single end path in bottom row")]
    MissingEnd,

    #[error("multiple paths detected in bottom row, expected exactly one for end")]
    MultipleEnds,
}

impl ParseData for Trails {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn get_path_char_indices(line: &str) -> Vec<usize> {
            line.char_indices()
                .filter(|(_, ch)| *ch == '.')
                .map(|(index, _)| index)
                .collect()
        }

        fn char_index_to_x(index: usize) -> Result<i32, ParseTrailsError> {
            i32::try_from(index).map_err(ParseTrailsError::CharIndexOverflow)
        }

        let last_index = input.lines().count().saturating_sub(1);

        let mut start_opt = None;
        let mut end_opt = None;
        let mut paths = HashSet::new();
        let mut slopes = HashMap::new();

        parse_input_lines(input, |line_index, line| {
            let y = i32::try_from(line_index).map_err(ParseTrailsError::LineIndexOverflow)?;

            if line_index == 0 {
                let path_indices = get_path_char_indices(line);
                match path_indices.as_slice() {
                    &[ch_index] => {
                        let x = char_index_to_x(ch_index)?;
                        start_opt = Some(Point2::new(x, y));
                        Ok(())
                    }
                    [] => Err(ParseTrailsError::MissingStart),
                    _ => Err(ParseTrailsError::MultipleStarts),
                }
            } else if line_index == last_index {
                let path_indices = get_path_char_indices(line);
                match path_indices.as_slice() {
                    &[ch_index] => {
                        let x = char_index_to_x(ch_index)?;
                        end_opt = Some(Point2::new(x, y));
                        Ok(())
                    }
                    [] => Err(ParseTrailsError::MissingEnd),
                    _ => Err(ParseTrailsError::MultipleEnds),
                }
            } else {
                for (ch_index, ch) in line.char_indices() {
                    let x = char_index_to_x(ch_index)?;

                    match ch {
                        '#' => {} // do nothing
                        '.' => {
                            paths.insert(Point2::new(x, y));
                        }
                        '^' => {
                            slopes.insert(Point2::new(x, y), Direction::Up);
                        }
                        '>' => {
                            slopes.insert(Point2::new(x, y), Direction::Right);
                        }
                        'v' => {
                            slopes.insert(Point2::new(x, y), Direction::Down);
                        }
                        '<' => {
                            slopes.insert(Point2::new(x, y), Direction::Left);
                        }
                        _ => return Err(ParseTrailsError::InvalidChar(ch)),
                    }
                }
                Ok(())
            }
        })
        .collect::<Result<(), _>>()?;

        Ok(Self {
            start: start_opt.ok_or(ParseTrailsError::MissingStart)?,
            end: end_opt.ok_or(ParseTrailsError::MissingEnd)?,
            paths,
            slopes,
        })
    }
}

/*
Slopes can only be traveled along their direction. Avoid traversing the same coordinate twice for a
hike.

> Movement likely limited to cardinal directions.

For part 1, find the length of the longest hike possible from start to end.
*/

impl Direction {
    fn to_vector2(self) -> Vector2<i32> {
        match self {
            Self::Up => Vector2::y() * -1,
            Self::Right => Vector2::x(),
            Self::Down => Vector2::y(),
            Self::Left => Vector2::x() * -1,
        }
    }
}

impl Trails {
    /// Recursively determine a maximum distance to the end from the given point and a collection of
    /// points already visited (which should not be traversed over).
    ///
    /// If there is no valid path to end, returns `None`.
    fn recursive_max_distance_to_end(
        &self,
        point: Point2<i32>,
        visited: &mut HashSet<Point2<i32>>,
    ) -> Option<u32> {
        // DFS through recursion
        if visited.contains(&point) {
            // invalid from traversing to a visited point
            None
        } else if point == self.end {
            // base case
            Some(0)
        } else if point == self.start || self.paths.contains(&point) {
            visited.insert(point);

            // explore all directions for maximum among them
            let neighbor_max_dist = [
                Vector2::x(),
                Vector2::y(),
                Vector2::x() * -1,
                Vector2::y() * -1,
            ]
            .into_iter()
            .filter_map(|offset| {
                let neighbor = point + offset;
                self.recursive_max_distance_to_end(neighbor, visited)
            })
            .max();

            visited.remove(&point);

            // add 1 for our distance to that maximum
            neighbor_max_dist.map(|dist| {
                dist.checked_add(1)
                    .expect("incrementing distance should not overflow")
            })
        } else if let Some(direction) = self.slopes.get(&point) {
            visited.insert(point);

            // can only explore in direction of slope
            let neighbor_max_dist =
                self.recursive_max_distance_to_end(point + direction.to_vector2(), visited);

            visited.remove(&point);

            // add 1 for our distance
            neighbor_max_dist.map(|dist| {
                dist.checked_add(1)
                    .expect("incrementing distance should not overflow")
            })
        } else {
            // not a valid point
            None
        }
    }

    /// Find the maximum distance from start to end.
    ///
    /// If there is no valid path, returns `None`
    fn max_distance(&self) -> Option<u32> {
        let mut visited = HashSet::new();
        self.recursive_max_distance_to_end(self.start, &mut visited)
    }
}

struct Day23;

impl Solution<PartOne> for Day23 {
    type Input = Trails;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let max = input.max_distance();
        Ok(max.expect("path to end should exist"))
    }
}

/*
For part 2, treat slopes like paths (no restriction in direction traversed) and recalculate longest
length hike.
*/

impl Trails {
    /// Collect a map of the start point & intersection points to lists of squashed paths to each
    /// other and the end point. Squashed path data contains the length of the squashed path and its
    /// end point.
    fn build_squashed_paths_map_ignoring_slope_directions(
        &self,
    ) -> HashMap<Point2<i32>, Vec<(u32, Point2<i32>)>> {
        let directions = [
            Direction::Up,
            Direction::Right,
            Direction::Down,
            Direction::Left,
        ];

        // collect paths, slopes, and start/end as points traversable
        let traversal_points: HashSet<&Point2<i32>> = self
            .slopes
            .keys()
            .chain(self.paths.iter())
            .chain([&self.start, &self.end])
            .collect();

        // collect points forming intersections, or have more than 2 neighbors
        let intersection_neighbors: HashMap<&Point2<i32>, Vec<Point2<i32>>> = traversal_points
            .iter()
            .filter_map(|&point| {
                let neighbors: Vec<Point2<i32>> = directions
                    .iter()
                    .filter_map(|direction| {
                        let neighbor = point + direction.to_vector2();
                        traversal_points.contains(&neighbor).then_some(neighbor)
                    })
                    .collect();
                (neighbors.len() > 2).then_some((point, neighbors))
            })
            .collect();

        // critical points to detect are intersections + start & end
        let critical_points: HashSet<&Point2<i32>> = intersection_neighbors
            .keys()
            .copied()
            .chain([&self.start, &self.end])
            .collect();

        let mut squashed_paths: HashMap<Point2<i32>, Vec<(u32, Point2<i32>)>> =
            intersection_neighbors
                .into_iter()
                .map(|(&point, neighbors)| {
                    let paths_out = neighbors
                        .into_iter()
                        .map(|neighbor| {
                            let mut visited: HashSet<Point2<i32>> = HashSet::new();
                            visited.insert(point);
                            let mut current = neighbor;
                            while !critical_points.contains(&current) {
                                // iterate to next expected single neighbor not visited, until a
                                // critical point is reached
                                let next_neighbors: Vec<Point2<i32>> = directions
                                    .iter()
                                    .filter_map(|direction| {
                                        let next = current + direction.to_vector2();
                                        (traversal_points.contains(&next)
                                            && !visited.contains(&next))
                                        .then_some(next)
                                    })
                                    .collect();
                                assert_eq!(
                                    next_neighbors.len(),
                                    1,
                                    "expected one point next while walking squash-able path"
                                );

                                visited.insert(current);
                                current = next_neighbors[0];
                            }

                            let distance = u32::try_from(visited.len())
                                .expect("squashed path length should fit u32");
                            (distance, current)
                        })
                        .collect();

                    (point, paths_out)
                })
                .collect();

        // find the path leading to start, then insert entry for a path from start
        let (point_reaching_start, path_dist_to_start) = squashed_paths
            .iter()
            .find_map(|(point, paths_out)| {
                paths_out.iter().find_map(|(path_dist, path_end)| {
                    (*path_end == self.start).then_some((*point, *path_dist))
                })
            })
            .expect("squashed paths should have reached start");
        squashed_paths.insert(self.start, vec![(path_dist_to_start, point_reaching_start)]);

        squashed_paths
    }

    /// Find the maximum distance from start to end, treating slopes as paths.
    fn max_distance_ignoring_slope_directions(&self) -> u32 {
        /// Stack entry holding (current point, visited, distance reached)
        type StackData<'a> = (&'a Point2<i32>, HashSet<&'a Point2<i32>>, u32);

        let squashed_paths = self.build_squashed_paths_map_ignoring_slope_directions();

        // prefer iterative DFS to avoid stack overflow
        let mut stack: Vec<StackData> = Vec::new();
        stack.push((&self.start, HashSet::new(), 0));
        let mut max = None;

        while let Some((point, mut visited, dist)) = stack.pop() {
            if visited.contains(&point) {
                continue;
            }

            if *point == self.end {
                // track larger for maximum
                max = Some(max.unwrap_or(0).max(dist));
                continue;
            }

            if let Some(paths_out) = squashed_paths.get(point) {
                // visit current point then iterate stack for each path out
                visited.insert(point);
                for (path_dist, path_end) in paths_out {
                    // I'm too dumb and recursion-pilled to have a more optimal way to handle state
                    // than this costly cloning of the visited set per iteration
                    stack.push((
                        path_end,
                        visited.clone(),
                        dist.checked_add(*path_dist)
                            .expect("incrementing distance should not overflow"),
                    ));
                }
            }
        }

        max.expect("path to end should have been found")
    }
}

impl Solution<PartTwo> for Day23 {
    type Input = Trails;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        // NOTE part 2 complexity caused stack overflow with recursive approach, using separate
        // method with iterative approach
        // - this still takes ~7 seconds to run!
        Ok(input.max_distance_ignoring_slope_directions())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"#.#####################
#.......#########...###
#######.#########.#.###
###.....#.>.>.###.#.###
###v#####.#v#.###.#.###
###.>...#.#.#.....#...#
###v###.#.#.#########.#
###...#.#.#.......#...#
#####.#.#.#######.#.###
#.....#.#.#.......#...#
#.#####.#.#.#########v#
#.#...#...#...###...>.#
#.#.#v#######v###.###v#
#...#.>.#...>.>.#.###.#
#####v#.#.###v#.#.###.#
#.....#...#...#.#.#...#
#.#########.###.#.#.###
#...###...#...#...#.###
###.###.#.###v#####v###
#...#...#.#.>.>.#.>.###
#.###.###.#.###.#.#v###
#.....###...###...#...#
#####################.#
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Trails::parse(EXAMPLE_INPUT)?;
        let result = <Day23 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 94);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Trails::parse(EXAMPLE_INPUT)?;
        let result = <Day23 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 154);
        Ok(())
    }
}

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap, HashSet};
use std::hash::Hash;

use aoc_framework::parsing::{ParseContextError, parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use checked_sum::CheckedSum;
use nalgebra::{Point3, Vector3};

#[solution_runner(
    name = "Day 22: Sand Slabs",
    parsed = BrickSpace,
    part_one = Day22,
    part_two = Day22
)]
impl super::AdventOfCode2023<22> {}

/*
Input is a list of coordinates for bricks in 3D space. A line separates two `x,y,z` coordinates with
`~`, where the coordinates define the ends of a brick.

> Coordinates should have all bricks above z=0.

> Bricks are in axis-aligned straight lines, so assume coordinate ends have at least 2 components
> equal.
*/

/// A brick defined as an Axis-Aligned Bounding Box.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Brick {
    /// The minimum bound.
    min: Point3<i32>,
    /// The maximum bound.
    max: Point3<i32>,
}

impl Ord for Brick {
    fn cmp(&self, other: &Self) -> Ordering {
        // first sort by min z, then max z, then other components (min then max)
        self.min
            .z
            .cmp(&other.min.z)
            .then(self.max.z.cmp(&other.max.z))
            .then(self.min.y.cmp(&other.min.y))
            .then(self.max.y.cmp(&other.max.y))
            .then(self.min.x.cmp(&other.min.x))
            .then(self.max.x.cmp(&other.max.x))
    }
}

impl PartialOrd for Brick {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Brick {
    /// Construct a brick from coordinates of its ends.
    fn new(start: Point3<i32>, end: Point3<i32>) -> Self {
        Self {
            min: Point3::new(start.x.min(end.x), start.y.min(end.y), start.z.min(end.z)),
            max: Point3::new(start.x.max(end.x), start.y.max(end.y), start.z.max(end.z)),
        }
    }
}

/// A collection of bricks in three-dimensional space.
///
/// Tracks an ordered collection of bricks.
#[derive(Debug)]
struct BrickSpace(BTreeSet<Brick>);

#[derive(thiserror::Error, Debug)]
enum ParseBrickSpaceError {
    #[error("expected '~' to delimit brick end coordinates")]
    MissingTildeDelimiter,

    #[error("expected three components, comma separated, to describe a coordinate")]
    ExpectedThreeComponents,
}

impl ParseData for BrickSpace {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn parse_point3(coords: &str) -> DynamicResult<Point3<i32>> {
            let components: Vec<&str> = coords.split(',').collect();
            match components.as_slice() {
                &[x_str, y_str, z_str] => {
                    let x = parse_with_context(x_str)?;
                    let y = parse_with_context(y_str)?;
                    let z = parse_with_context(z_str)?;
                    Ok(Point3::new(x, y, z))
                }
                _ => Err(ParseContextError::new(
                    ParseBrickSpaceError::ExpectedThreeComponents,
                    coords,
                )
                .into()),
            }
        }

        let bricks = parse_input_lines(input, |_, line| -> DynamicResult<_> {
            let (start_str, end_str) = line
                .split_once('~')
                .ok_or(ParseBrickSpaceError::MissingTildeDelimiter)?;

            let start = parse_point3(start_str)?;
            let end = parse_point3(end_str)?;

            Ok(Brick::new(start, end))
        })
        .collect::<Result<_, _>>()?;

        Ok(Self(bricks))
    }
}

/*
Input has not settled the bricks yet, which must be done first. Bricks will fall to z=0 as the
ground; bricks can't be in the ground, so the lowest they can settle is z=1. Bricks don't rotate to
settle. Bricks don't occupy the same coordinate, so will settle on top of what's below.

For part 1, determine the count of bricks that could be individually removed without re-settling
bricks above.
*/

impl Brick {
    /// Determine if two bricks intersect in space.
    fn intersects(&self, other: &Self) -> bool {
        self.min.x <= other.max.x
            && self.max.x >= other.min.x
            && self.min.y <= other.max.y
            && self.max.y >= other.min.y
            && self.min.z <= other.max.z
            && self.max.z >= other.min.z
    }

    /// Produce a brick moved from self by `delta`.
    fn to_moved(self, delta: Vector3<i32>) -> Self {
        Self {
            min: self.min + delta,
            max: self.max + delta,
        }
    }
}

impl BrickSpace {
    /// Produce a collection of bricks from self that are settled to ground.
    fn to_settled(&self) -> Self {
        let delta_down = Vector3::z() * -1;
        let delta_up = Vector3::z();

        let mut new_bricks: BTreeSet<Brick> = BTreeSet::new();

        // iterate bricks, which should be ordered by lowest z
        for mut brick in self.0.iter().copied() {
            // move brick down while there's no intersection or it's above the ground
            while new_bricks.iter().all(|nb| !nb.intersects(&brick)) && brick.min.z > 0 {
                brick = brick.to_moved(delta_down);
            }
            // now that brick reached a bad spot, move up as final settled position
            new_bricks.insert(brick.to_moved(delta_up));
        }

        Self(new_bricks)
    }

    /// Count the number of bricks that could individually be removed without having to resettle
    /// other bricks to ground.
    fn count_removable(&self) -> u32 {
        let delta_up = Vector3::z();
        let delta_down = Vector3::z() * -1;

        let mut count = 0u32;

        // iterate bricks from bottom up
        'brick_eval: for brick in &self.0 {
            // find other bricks intersecting with space above
            let brick_up = brick.to_moved(delta_up);
            for brick_above in self.0.iter().filter(|b| {
                // NB don't evaluate self for intersect
                *b != brick && b.intersects(&brick_up)
            }) {
                // check if the above brick has another besides the original below it
                let brick_down = brick_above.to_moved(delta_down);
                if self
                    .0
                    .iter()
                    .filter(|b| {
                        // NB don't evaluate self for intersect
                        *b != brick_above && *b != brick
                    })
                    .all(|b| !b.intersects(&brick_down))
                {
                    // brick_above is only supported by the original; don't count
                    continue 'brick_eval;
                }
            }

            count = count
                .checked_add(1)
                .expect("incrementing count should not overflow");
        }

        count
    }
}

struct Day22;

impl Solution<PartOne> for Day22 {
    type Input = BrickSpace;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let settled = input.to_settled();
        Ok(settled.count_removable())
    }
}

/*
For part 2, for each brick determine how many bricks would fall on removal and return the sum.
*/

/// A queue that contains unique items and pops by minimum order.
struct UniqueMinPriorityQueue<T: Ord + Hash + Eq> {
    heap: BinaryHeap<Reverse<T>>,
    set: HashSet<T>,
}

impl<T: Ord + Hash + Eq + Clone> UniqueMinPriorityQueue<T> {
    fn new() -> Self {
        Self {
            heap: BinaryHeap::new(),
            set: HashSet::new(),
        }
    }

    fn push(&mut self, item: T) {
        // must be new addition to set before pushing to heap
        if self.set.insert(item.clone()) {
            self.heap.push(Reverse(item));
        }
    }

    fn pop(&mut self) -> Option<T> {
        let popped_rev = self.heap.pop()?;
        let item = popped_rev.0;
        self.set.remove(&item);
        Some(item)
    }
}

impl<T: Ord + Hash + Clone> Extend<T> for UniqueMinPriorityQueue<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }
}

impl BrickSpace {
    /// Count the sum of bricks that would drop from removing each brick individually.
    fn count_bricks_droppable(&self) -> u32 {
        let delta_up = Vector3::z();
        let delta_down = Vector3::z() * -1;

        let mut dependents: HashMap<&Brick, HashSet<&Brick>> = HashMap::new();
        let mut dependencies: HashMap<&Brick, HashSet<&Brick>> = HashMap::new();
        for brick in &self.0 {
            // track bricks above as dependents
            let brick_up = brick.to_moved(delta_up);
            let bricks_above = self
                .0
                .iter()
                .filter(|b| {
                    // NB don't evaluate self for intersect
                    *b != brick && b.intersects(&brick_up)
                })
                .collect();
            dependents.insert(brick, bricks_above);

            // track bricks below as dependencies
            let brick_down = brick.to_moved(delta_down);
            let bricks_below = self
                .0
                .iter()
                .filter(|b| {
                    // NB don't evaluate self for intersect
                    *b != brick && b.intersects(&brick_down)
                })
                .collect();
            dependencies.insert(brick, bricks_below);
        }

        self.0
            .iter()
            .map(|brick| {
                // initialize a collection of unstable bricks with the brick to remove
                let mut unstable_bricks: HashSet<&Brick> = HashSet::new();
                unstable_bricks.insert(brick);

                // evaluate a chain of dependents, iterate by minimum order/lowest z, avoid tracking
                // duplicates
                let mut queue: UniqueMinPriorityQueue<&Brick> = UniqueMinPriorityQueue::new();
                queue.extend(dependents[brick].iter().copied());
                while let Some(brick_to_check) = queue.pop() {
                    // check if all dependencies are unstable
                    if dependencies[brick_to_check].is_subset(&unstable_bricks) {
                        // track as unstable, push dependents for evaluation
                        unstable_bricks.insert(brick_to_check);
                        queue.extend(dependents[brick_to_check].iter().copied());
                    }
                }

                // subtract the one brick initially removed for a count
                u32::try_from(unstable_bricks.len())
                    .expect("count of unstable bricks should fit u32")
                    - 1
            })
            .checked_sum()
            .expect("sum of counts should not overflow")
    }
}

impl Solution<PartTwo> for Day22 {
    type Input = BrickSpace;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let settled = input.to_settled();
        Ok(settled.count_bricks_droppable())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT: &str = r"1,0,1~1,2,1
0,0,2~2,0,2
0,2,3~2,2,3
0,0,4~0,2,4
2,0,5~2,2,5
0,1,6~2,1,6
1,1,8~1,1,9
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = BrickSpace::parse(EXAMPLE_INPUT)?;
        let result = <Day22 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 5);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = BrickSpace::parse(EXAMPLE_INPUT)?;
        let result = <Day22 as Solution<PartTwo>>::solve(&parsed)?;
        assert_eq!(result, 7);
        Ok(())
    }
}

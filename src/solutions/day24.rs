use aoc_framework::parsing::{ParseContextError, parse_input_lines, parse_with_context};
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};
use float_eq::{assert_float_ne, float_eq};
use nalgebra::{Point2, Point3, Vector3};

#[solution_runner(
    name = "Day 24: Never Tell Me The Odds",
    parsed = Hailstones,
    part_one = Day24,
    part_two = Day24
)]
impl super::AdventOfCode2023<24> {}

/*
Input is a collection of hailstone linear trajectories. A trajectory is formatted as 3 components
for position (comma-space separated), ` @ `, and 3 components for velocity (comma-space separated).

Consider velocities to be in units per nanosecond.
*/

#[derive(Debug)]
struct Trajectory {
    start_position: Point3<f64>,
    velocity: Vector3<f64>,
}

#[derive(Debug)]
struct Hailstones(Vec<Trajectory>);

#[derive(thiserror::Error, Debug)]
enum ParseHailstonesError {
    #[error("expected '@' to delimit position and velocity")]
    MissingAtDelimiter,

    #[error("expected 3 number components, comma separated")]
    ExpectedThreeComponents,
}

impl ParseData for Hailstones {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        fn parse_components(s: &str) -> DynamicResult<(f64, f64, f64)> {
            let components: Vec<_> = s.split(',').collect();

            match components.as_slice() {
                &[x_str, y_str, z_str] => {
                    let x = parse_with_context(x_str.trim())?;
                    let y = parse_with_context(y_str.trim())?;
                    let z = parse_with_context(z_str.trim())?;
                    Ok((x, y, z))
                }
                _ => Err(
                    ParseContextError::new(ParseHailstonesError::ExpectedThreeComponents, s).into(),
                ),
            }
        }

        let trajectories = parse_input_lines(input, |_, line| -> DynamicResult<_> {
            let (position_str, velocity_str) = line
                .split_once('@')
                .ok_or(ParseHailstonesError::MissingAtDelimiter)?;

            let pc = parse_components(position_str)?;
            let start_position = Point3::new(pc.0, pc.1, pc.2);

            let vc = parse_components(velocity_str)?;
            let velocity = Vector3::new(vc.0, vc.1, vc.2);

            Ok(Trajectory {
                start_position,
                velocity,
            })
        })
        .collect::<Result<_, _>>()?;

        Ok(Self(trajectories))
    }
}

/*
For part 1, estimate collisions by observing a test area in x-y axes and trajectory paths moving
forward in time. Return the count of paths that intersect within the test area.

> The test area to use is from 200,000,000,000,000 to 400,000,000,000,000 in both axes.
*/

/// Axis-Aligned Bounding Box in 2D space.
struct AABB2 {
    min: Point2<f64>,
    max: Point2<f64>,
}

impl AABB2 {
    /// Create with the minimum components matching `min` and the maximum components matching `max`.
    fn from_min_max(min: f64, max: f64) -> Self {
        assert!(max >= min, "maximum {max} is below minimum {min}");
        Self {
            min: Point2::new(min, min),
            max: Point2::new(max, max),
        }
    }

    /// Check a point is contained in bounds.
    fn contains(&self, point: Point2<f64>) -> bool {
        self.min.x <= point.x
            && point.x <= self.max.x
            && self.min.y <= point.y
            && point.y <= self.max.y
    }
}

impl Trajectory {
    /// Calculate the time to reach a given component target position from the start position and
    /// velocity of a trajectory.
    fn time_to_target(target: f64, start_position: f64, velocity: f64) -> f64 {
        // target = velocity * time + start_position => time = (target - start_position) / velocity
        // NOTE largest target expected would be 4e14, while f64 precision integer should handle
        // 2^53 ~= 9e15
        assert_float_ne!(
            velocity,
            0.0,
            abs <= 0.000_01,
            "zero velocity can't guarantee target is reachable"
        );
        (target - start_position) / velocity
    }

    /// Calculate the time to reach the given `x` position.
    fn time_to_x(&self, x: f64) -> f64 {
        Self::time_to_target(x, self.start_position.x, self.velocity.x)
    }

    /// Calculate the time to reach the given `y` position.
    fn time_to_y(&self, y: f64) -> f64 {
        Self::time_to_target(y, self.start_position.y, self.velocity.y)
    }

    /// Check this trajectory intersects an area in the x and y axes.
    fn intersects_xy_area(&self, area: &AABB2) -> bool {
        let x_time_start = self.time_to_x(area.min.x);
        let x_time_end = self.time_to_x(area.max.x);

        let y_time_start = self.time_to_y(area.min.y);
        let y_time_end = self.time_to_y(area.max.y);

        // filter out negative times for minimums
        let x_time_min = x_time_start.min(x_time_end).max(0.0);
        let y_time_min = y_time_start.min(y_time_end).max(0.0);

        let x_time_max = x_time_start.max(x_time_end);
        let y_time_max = y_time_start.max(y_time_end);

        // check maximums are non-negative and there is an overlap in x-y time ranges
        x_time_max >= 0.0
            && y_time_max >= 0.0
            && x_time_min <= y_time_max
            && x_time_max >= y_time_min
    }

    /// Calculate the coefficients (m, b) for the slope-intercept formula (`y = m * x + b`) of the
    /// trajectory path in x-y coordinate space.
    fn xy_slope_intercept(&self) -> (f64, f64) {
        let m = self.velocity.y / self.velocity.x;
        let b = m.mul_add(-self.start_position.x, self.start_position.y);
        (m, b)
    }

    /// Determine if a component's target position is a future position from the start position and
    /// velocity of a trajectory.
    fn target_in_future(target: f64, start_position: f64, velocity: f64) -> bool {
        assert_float_ne!(
            velocity,
            0.0,
            abs <= 0.000_01,
            "zero velocity can't guarantee target is reachable"
        );
        (target - start_position) * velocity > 0.0
    }

    /// Determine if a given `x` position is in the future of this trajectory.
    fn in_future_x(&self, x: f64) -> bool {
        Self::target_in_future(x, self.start_position.x, self.velocity.x)
    }

    /// Determine if a given `y` position is in the future of this trajectory.
    fn in_future_y(&self, y: f64) -> bool {
        Self::target_in_future(y, self.start_position.y, self.velocity.y)
    }

    /// Find the x-y axes intersection of two trajectory paths, if they intersect.
    fn intersect_xy(&self, other: &Self) -> Option<Point2<f64>> {
        fn intersect_in_future(trajectory: &Trajectory, intersect: Point2<f64>) -> bool {
            // prioritize checking axis with non-zero velocity
            if float_eq!(trajectory.velocity.x, 0.0, abs <= 0.000_01) {
                trajectory.in_future_y(intersect.y)
            } else {
                trajectory.in_future_x(intersect.x)
            }
        }

        let (m_self, b_self) = self.xy_slope_intercept();
        let (m_other, b_other) = other.xy_slope_intercept();

        if float_eq!(m_self, m_other, abs <= 0.000_01) {
            // parallel paths, no intersection
            return None;
        }

        // substitute slope-intercept formula's y to have both paths equal to
        // solve x = (b_2 - b_1) / (m_1 - m_2)
        let x = (b_other - b_self) / (m_self - m_other);
        let y = x.mul_add(m_self, b_self);
        let intersect = Point2::new(x, y);

        // filter out intersection in a past of a trajectory
        (intersect_in_future(self, intersect) && intersect_in_future(other, intersect))
            .then_some(intersect)
    }
}

impl Hailstones {
    fn count_pairs_intersect_in_xy_area(&self, area: &AABB2) -> u32 {
        // filter for trajectories that intersect the area
        let candidates: Vec<_> = self
            .0
            .iter()
            .filter(|t| t.intersects_xy_area(area))
            .collect();
        let n = candidates.len();

        let mut count: u32 = 0;
        for i in 0..n {
            for j in i + 1..n {
                if let Some(intersect) = candidates[i].intersect_xy(candidates[j])
                    && area.contains(intersect)
                {
                    count = count
                        .checked_add(1)
                        .expect("incrementing count should not overflow");
                }
            }
        }

        count
    }
}

struct Day24;

impl Solution<PartOne> for Day24 {
    type Input = Hailstones;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let test_area = AABB2::from_min_max(200_000_000_000_000.0, 400_000_000_000_000.0);
        Ok(input.count_pairs_intersect_in_xy_area(&test_area))
    }
}

/*
For part 2, find a rock trajectory to throw that directly collides with all hailstones; no
limitation to start position or velocity, and the collisions will not slow or deviate the rock.
Return the sum of start position components for this rock.
*/

/*
https://www.reddit.com/r/adventofcode/comments/18pnycy/comment/kxqjg33/

idea is to reinterpret relative to one hailstone, treat its current position as an origin

formatting positions and velocities relative to hailstone i
- hailstone j
pij = p_j - p_i
vij = v_j - v_i
- hailstone k
pik = p_k - p_i
vik = v_k - v_i

with times to collide with relevant hailstone (t_j, t_k), relative collisions are:
pij + t_j * vij
pik + t_k * vik
collision for hailstone i at relative origin

collisions must form line, so collisions sans origin must be colinear and cross product will be 0
    (pij + t_j * vij) x (pik + t_k * vik) = 0
=>  (pij x pik) + t_j * (vij x pik) + t_k * (pij x vik) + t_j * t_k * (vij x vik) = 0

with rule involving dot products: (a x b) * a = (a x b) * b = 0
- using vik
    (pij x pik) * vik + t_j * (vij x pik) * vik = 0
=>  t_j = -((pij x pik) * vik) / ((vij x pik) * vik)
- using vij
    t_k = -((pij x pik) * vij) / ((pij x vik) * vij)

absolute coordinates can be calculated with times, then determine rock's components
c_j = p_j + t_j * v_j
c_k = p_k + t_k * v_k
v_r = (c_k - c_j) / (t_k - t_j)
p_r = c_j - t_j * v_r
*/

impl Hailstones {
    fn find_trajectory_colliding_hailstones(&self) -> Trajectory {
        // pick out three trajectories
        let hailstones: Vec<_> = self.0.iter().take(3).collect();
        assert_eq!(
            hailstones.len(),
            3,
            "not enough trajectories to calculate with"
        );

        // interpret second & third trajectories relative to first
        let p_01 = hailstones[1].start_position - hailstones[0].start_position;
        let v_01 = hailstones[1].velocity - hailstones[0].velocity;
        let p_02 = hailstones[2].start_position - hailstones[0].start_position;
        let v_02 = hailstones[2].velocity - hailstones[0].velocity;

        // calculate collision times for second & third
        let t_1 = -p_01.cross(&p_02).dot(&v_02) / v_01.cross(&p_02).dot(&v_02);
        let t_2 = -p_01.cross(&p_02).dot(&v_01) / p_01.cross(&v_02).dot(&v_01);

        // calculate collision points for second & third in absolute coords
        let c_1 = hailstones[1].start_position + t_1 * hailstones[1].velocity;
        let c_2 = hailstones[2].start_position + t_2 * hailstones[2].velocity;

        // calculate trajectory through collision points & times
        let velocity = (c_2 - c_1) / (t_2 - t_1);
        let start_position = c_1 - t_1 * velocity;

        Trajectory {
            start_position,
            velocity,
        }
    }
}

impl Solution<PartTwo> for Day24 {
    type Input = Hailstones;
    type Output = f64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let rock_trajectory = input.find_trajectory_colliding_hailstones();
        let sum = rock_trajectory.start_position.x
            + rock_trajectory.start_position.y
            + rock_trajectory.start_position.z;
        Ok(sum)
    }
}

#[cfg(test)]
mod tests {
    use float_eq::assert_float_eq;

    use super::*;

    const EXAMPLE_INPUT: &str = r"19, 13, 30 @ -2,  1, -2
18, 19, 22 @ -1, -1, -2
20, 25, 34 @ -2, -2, -4
12, 31, 28 @ -1, -2, -1
20, 19, 15 @  1, -5, -3
";

    #[test]
    fn trajectory_intersect_xy_finds_an_intersection() {
        let a = Trajectory {
            start_position: Point3::new(19.0, 13.0, 30.0),
            velocity: Vector3::new(-2.0, 1.0, -2.0),
        };
        let b = Trajectory {
            start_position: Point3::new(18.0, 19.0, 22.0),
            velocity: Vector3::new(-1.0, -1.0, -2.0),
        };

        let intersect_opt = a.intersect_xy(&b);

        assert!(intersect_opt.is_some(), "no intersection found");
        if let Some(intersect) = intersect_opt {
            assert_float_eq!(intersect.x, 14.333, abs <= 0.001, "x component mismatch");
            assert_float_eq!(intersect.y, 15.333, abs <= 0.001, "y component mismatch");
        }
    }

    #[test]
    fn count_pairs_intersect_in_xy_area_solves_example() -> DynamicResult<()> {
        let parsed = Hailstones::parse(EXAMPLE_INPUT)?;
        let test_area = AABB2::from_min_max(7.0, 27.0);
        assert_eq!(parsed.count_pairs_intersect_in_xy_area(&test_area), 2);
        Ok(())
    }

    #[test]
    fn part_two_solves_example() -> DynamicResult<()> {
        let parsed = Hailstones::parse(EXAMPLE_INPUT)?;
        let result = <Day24 as Solution<PartTwo>>::solve(&parsed)?;
        assert_float_eq!(result, 47.0, abs <= 0.000_01);
        Ok(())
    }
}

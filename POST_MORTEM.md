Notes and takeaways from iterating from my [AoC 2025 Post Mortem](https://github.com/Rocker-Mitchell/aoc-2025/blob/main/POST_MORTEM.md)

The changes to the library module felt much better:

- The redesigned traits for solutions is so much better
  - A single core interface for a solution keeps consistency and is clear
  - Distinguishing the solution trait with a generic type (expecting a sealed type) and inner type properties makes the trait flexible for its context (first vs second part, parsed input vs raw string handling)
    - Wasn't hard to leverage trait bounds to write solution runners for the different solution contexts

- Dropping the effort to make a catch-all parse error struct in favor of a parsing module worked out
  - I could focus on the parsing utilities having their own specific errors (like parsing lines returning an `InvalidLine` error), and anything more specific could be owned by the individual implementations
  - I was able to make errors in the nature of parsing strings to numbers generalized to work with anything implementing `FromStr` with a error tracking the context of the given string; this enabled writing my own structs implementing `FromStr` to be compatible
    - Though for single characters to enum variants, `From<char>` felt logically more appropriate that string parsing
      > [! NOTE]
      > Consider a parsing utility for `From<T>`, or especially `From<char>`, that can return error with context
    - _I have wondered if the deliverable for string parsing with context should have been an inheritable trait instead of a generic function._ The tradeoff would be losing the explicit function import to an implicitly needed trait import, but I'd call a method on a variable instead of passing as a parameter.
  - Partway through, I found my idea to have the line parsing function handle offset to deal with variable parsing patterns poor. It took some back and forth with an LLM to develop an `InputScanner` that I could internally manage line index information with, which has been easy to use.
  - The development of `InputScanner` revealed a new idea for handling errors returned in implemented solutions: a generic type with a trait bound that expects the error type to be convertible to something concrete, like a boxed dynamic error. In implemented solutions, it meant cases where the errors returned all matched type that I didn't need some overhead to convert to a boxed error, which was nice. It also doesn't stop me from returning boxed errors when I need to return multiple types, as a boxed error technically can be converted to a boxed error.
    > [! NOTE]
    > It might be worth changing the solution result types (and other similar error type boundaries in library) from a concrete boxed dynamic error by leveraging trait bounds, either to propagate type or expect it will convert to a boxed error where needed
  - _I didn't figure out a good solution to specifically service parsing character grids._ It would be lovely to add this to the library parsers, handling checks of consistent width across lines and other such error cases, but the output is the trouble. Sometimes I didn't need to track the whole data as a sparse collection was appropriate, or needing to track the bounds of the input grid varied, or differences in what integer types to use for coordinates. I don't want to lock down the output to some specific crate either like an nalgebra matrix.
    - Also, I'd probably need a duplicate implementation within `InputScanner`, as Day 13 involved multiple grids separated by empty lines; that would be a trick to DRY

- The runner code came out pleasantly
  - Turned out not that hard to make a procedural macro, which made it very brief and clear how an implemented solution runner was configured; it did require making a workspace as procedural macros are their own crate type
  - Figuring out trait bounds with the new solution trait & parse trait makes the background work of running solutions feel organized and flexible, love it!
  - _There is a pain that rustfmt doesn't handle line wrapping the macro._ As I understand, procedural macros might parse in a way that is whitespace sensitive, so formatting never attempts to touch procedural macro calls. Maybe there's nothing for this.

- With more exposure to `FromStr`, I think my intent of the `ParseData` trait is redundant as `FromStr` conceptually does the same, with a benefit that an implementation can set the type of the error instead of converting to a concrete type expected by the trait. Making that error type be a boxed error could work in implementations that need it.
  > [! NOTE]
  > Consider replacing the use of `ParseData` with `FromStr`, which would involve more trait bounds to handle the error type

---

For actual implementations, I've got some observations for these puzzles & 2025's:

- Micromanaging number types isn't clean. If there isn't some explicit mention of the range of a number, it's not that valuable to manually evaluate the expected range and pick the smallest integer type over using `u32`/`i32` as the baseline.
  > [! NOTE]
  > Prefer 32-bit sizes for parsed numbers, especially if there's no hard-defined range and there's no errors from `FromStr`. If overflows occur, conversions to 64-bit sizes at the overflowing operations is fine. Not converting a `usize` for a solution's result is fine.
  - Micromanaged number types lead to a lot of in-between steps to convert to larger sizes for math, which is easier to have the numbers all the same type at the start
  - On Day 6 I ran into a problem that ties to managing number types: generalized functions. It's not ergonomic to try to make a mathematical function reusable for `u8` to `u64`, as that led to using a variety of standard library traits for math operations to bound on, but also implementing some of my own traits to cover interfaces I couldn't get with the standard library (checked & saturated operations, is even, a few literal values).

- I really do want to avoid overflows as that can cause miscalculations, so I lean on checked operations to properly diagnose when a miscalculation would be from such. But it's so verbose with the method calls and adding `.except()` each time for a panic message, and I miss out on operations like `+=`.
  - It has led to using the `checked_sum` crate for summing collections, but then discovering there's no published counterpart for product and implementing my own. I wouldn't need either if I could automatically panic on overflow.
  - Quick research suggests rust can automatically panic on overflows, but it might be configured to only do that for debug builds. I think I'd want release/test builds to also have this behavior.
    > [! NOTE]
    > Configure projects to assert overflow checks, removing need to explicitly write code to catch such errors
    - it looks like in the Toml under `[profile.release]`, adding `overflow-checks = true` will apply to release builds

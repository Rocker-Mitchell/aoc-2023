//! Procedural macros for the `aoc-framework` crate.

use proc_macro::TokenStream;
use quote::quote;
use syn::{Error, Expr, Item, ItemImpl, ItemStruct, Type, parse_macro_input};

/// Procedural macro attribute that generates a `SolutionRunner` implementation.
///
/// This macro automates the implementation of the `SolutionRunner` trait for Advent of Code
/// solutions, routing to the appropriate solver function based on which solution types are
/// provided.
///
/// # Properties
///
/// - `name` (required): An expression that evaluates to `&str`, representing the solution's
///   display name.
///   Can be a string literal or a constant.
///
/// - `part_one` (required): The type implementing `Solution<PartOne>` for solving part one.
///
/// - `part_two` (optional): The type implementing `Solution<PartTwo>` for solving part two.
///   If omitted, only part one will be solved.
///
/// - `parsed` (optional): A type that implements `ParseData`, used to parse input before solving.
///   If omitted, the unparsed input string is passed directly to solvers.
///
/// # Errors
///
/// Returns a compile error if:
/// - Applied to anything other than a struct or impl block
/// - Required properties (`name`, `part_one`) are missing
/// - Any property is specified more than once
/// - An unsupported property is provided
///
/// # Examples
///
///
/// ## With `part_one`
///
/// With a struct `Day01` implementing `Solution<PartOne>`:
///
/// ```ignore
/// #[solution_runner(name = "Day 1", part_one = Day01)]
/// struct Day01Runner;
/// ```
///
/// ## With `part_two`
///
/// With structs `Day02Part1` implementing `Solution<PartOne>` & `Day02Part2` implementing
/// `Solution<PartTwo>` and a struct `AdventOfCodeSolutions<const DAY: u8>` for solutions to run:
///
/// ```ignore
/// const NAME02: &str = "Day 2";
/// #[solution_runner(name = NAME02, part_one = Day02Part1, part_two = Day02Part2)]
/// impl AdventOfCodeSolutions<2> {}
/// ```
///
/// ## With `parsed`
///
/// With a struct `Day03Parsed` implementing `ParseData` and a struct `Day03` implementing both
/// `Solution<PartOne>` & `Solution<PartTwo>`:
///
/// ```ignore
/// #[solution_runner(name = "Day 3", parsed = Day03Parsed, part_one = Day03, part_two = Day03)]
/// struct Day03;
/// ```
#[proc_macro_attribute]
pub fn solution_runner(args: TokenStream, input: TokenStream) -> TokenStream {
    // The expression to use as a solution name; should resolve to string slice
    let mut name_expr_opt: Option<Expr> = None;
    // The type to use for a `ParseData` generic parameter
    let mut parsed_ty_opt: Option<Type> = None;
    // The type to use for a `Solution<PartOne>` generic parameter
    let mut part_one_ty_opt: Option<Type> = None;
    // The type to use for a `Solution<PartTwo>` generic parameter
    let mut part_two_ty_opt: Option<Type> = None;

    let solution_runner_parser = syn::meta::parser(|meta| {
        // check for expected property keys, track value, error if a duplicate key appears
        if meta.path.is_ident("name") {
            if name_expr_opt.is_some() {
                return Err(meta.error("duplicate 'name' property"));
            }
            name_expr_opt = Some(meta.value()?.parse()?);
            Ok(())
        } else if meta.path.is_ident("parsed") {
            if parsed_ty_opt.is_some() {
                return Err(meta.error("duplicate 'parsed' property"));
            }
            parsed_ty_opt = Some(meta.value()?.parse()?);
            Ok(())
        } else if meta.path.is_ident("part_one") {
            if part_one_ty_opt.is_some() {
                return Err(meta.error("duplicate 'part_one' property"));
            }
            part_one_ty_opt = Some(meta.value()?.parse()?);
            Ok(())
        } else if meta.path.is_ident("part_two") {
            if part_two_ty_opt.is_some() {
                return Err(meta.error("duplicate 'part_two' property"));
            }
            part_two_ty_opt = Some(meta.value()?.parse()?);
            Ok(())
        } else {
            Err(meta.error("unsupported solution runner property"))
        }
    });
    parse_macro_input!(args with solution_runner_parser);

    // enforce required properties
    let name_expr: Expr = match name_expr_opt {
        Some(value) => value,
        None => {
            return Error::new(
                proc_macro2::Span::call_site(),
                "missing required property: 'name'",
            )
            .to_compile_error()
            .into();
        }
    };
    let part_one_ty: Type = match part_one_ty_opt {
        Some(value) => value,
        None => {
            return Error::new(
                proc_macro2::Span::call_site(),
                "missing required property: 'part_one'",
            )
            .to_compile_error()
            .into();
        }
    };

    let solve_function_call = match (parsed_ty_opt, part_two_ty_opt) {
        (None, None) => {
            quote! {
                aoc_framework::runner::solve_half_solution::<#part_one_ty>(
                    #name_expr,
                    input,
                    handler,
                    timed
                )
            }
        }
        (None, Some(part_two_ty)) => {
            quote! {
                aoc_framework::runner::solve_full_solution::<#part_one_ty, #part_two_ty>(
                    #name_expr,
                    input,
                    handler,
                    timed
                )
            }
        }
        (Some(parsed_ty), None) => {
            quote! {
                aoc_framework::runner::solve_parsed_half_solution::<#parsed_ty, #part_one_ty>(
                    #name_expr,
                    input,
                    handler,
                    timed
                )
            }
        }
        (Some(parsed_ty), Some(part_two_ty)) => {
            quote! {
                aoc_framework::runner::solve_parsed_full_solution::<
                    #parsed_ty,
                    #part_one_ty,
                    #part_two_ty
                >(#name_expr, input, handler, timed)
            }
        }
    };

    let original_input = input.clone(); // clone before macro consumes input
    let item = parse_macro_input!(input as Item);

    let impl_solution_runner_block = match item {
        Item::Struct(ItemStruct { ident, .. }) => {
            // extracted struct name through `ident`
            quote! {
                impl aoc_framework::runner::SolutionRunner for #ident {
                    fn run(
                        input: &str,
                        handler: &mut dyn aoc_framework::runner::OutputHandler,
                        timed: bool
                    ) -> aoc_framework::DynamicResult<()> {
                        #solve_function_call
                    }
                }
            }
        }
        Item::Impl(ItemImpl { self_ty, .. }) => {
            // extracted type from impl block through `self_ty`
            quote! {
                impl aoc_framework::runner::SolutionRunner for #self_ty {
                    fn run(
                        input: &str,
                        handler: &mut dyn aoc_framework::runner::OutputHandler,
                        timed: bool
                    ) -> aoc_framework::DynamicResult<()> {
                        #solve_function_call
                    }
                }
            }
        }
        _ => {
            return Error::new(
                proc_macro2::Span::call_site(),
                "the #[solution_runner] macro can only be applied to a struct or an impl block",
            )
            .to_compile_error()
            .into();
        }
    };

    let input_ts = proc_macro2::TokenStream::from(original_input);
    TokenStream::from(quote! {
        #input_ts
        #impl_solution_runner_block
    })
}

use std::collections::{HashMap, VecDeque};

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, PartTwo, Solution};

#[solution_runner(
    name = "Day 20: Pulse Propagation",
    parsed = ModuleManager,
    part_one = Day20,
    part_two = Day20
)]
impl super::AdventOfCode2023<20> {}

/*
Modules can pulse *high* or *low* to destination modules.

A flip-flop module stores an on/off state, starting off. It ignores high pulses, but on a low pulse
toggles its state. If it toggles on it sends a high pulse, and off a low pulse.

A conjunction module remembers pulses received from all connections to it, initializing with low
pulses. It sends a pulse after receiving & updating the stored value: if all inputs are high then it
sends low, otherwise sends high.

A single untyped module with name "broadcaster" is expected as a broadcast module, propagating any
pulse received.

Input is a configuration of modules. Each line defines a module name, an arrow (" -> "), and a
comma-space-separated list of destination module names. The module name before the arrow is preceded
by a symbol for a module type if applicable:

- `%` - a flip-flop module
- `&` - a conjunction module
*/

trait Module {
    /// Send a pulse to this module from a source module by name.
    ///
    /// This module may change state and/or send its own pulse out in response.
    fn receive_pulse(&mut self, pulse: bool, source: &str) -> Option<bool>;
}

/// A module tracking an on/off state.
#[derive(Debug, Default, Clone)]
struct FlipFlopModule(bool);

impl Module for FlipFlopModule {
    fn receive_pulse(&mut self, pulse: bool, _source: &str) -> Option<bool> {
        // do nothing on high pulse
        if pulse {
            return None;
        }

        // toggle state and return new state
        self.0 = !self.0;
        Some(self.0)
    }
}

/// A module tracking previously received pulses from module sources.
#[derive(Debug, Default, Clone)]
struct ConjunctionModule(HashMap<String, bool>);

impl ConjunctionModule {
    /// Set inputs for the module to support, clearing any prior tracked inputs and initializing
    /// tracked pulse values to false.
    ///
    /// This module must have inputs assigned before receiving pulses, as it will panic on receiving
    /// from unexpected sources.
    fn set_inputs(&mut self, inputs: &[&str]) {
        self.0.clear();
        for source in inputs.iter().map(|s| (*s).to_string()) {
            self.0.insert(source, false);
        }
    }
}

impl Module for ConjunctionModule {
    /// Send a pulse to this module from a source module by name.
    ///
    /// # Panics
    ///
    /// Panics if the source module name is not an expected input of this module.
    fn receive_pulse(&mut self, pulse: bool, source: &str) -> Option<bool> {
        if let Some(value) = self.0.get_mut(source) {
            *value = pulse;
        } else {
            panic!(
                "expected source module name {source:?} in supported inputs: {:?}",
                self.0.keys().collect::<Vec<_>>()
            )
        }

        // return pulse based on inputs like a NAND gate
        if self.0.values().all(|&value| value) {
            Some(false)
        } else {
            Some(true)
        }
    }
}

/// An enumeration of module states by type.
#[derive(Debug, Clone)]
enum ModuleState {
    FlipFlop(FlipFlopModule),
    Conjunction(ConjunctionModule),
}

impl Module for ModuleState {
    fn receive_pulse(&mut self, pulse: bool, source: &str) -> Option<bool> {
        match self {
            Self::FlipFlop(fm) => fm.receive_pulse(pulse, source),
            Self::Conjunction(cm) => cm.receive_pulse(pulse, source),
        }
    }
}

#[derive(Debug, Clone)]
struct ModuleManager {
    /// The mapping of module name to data tied to that module:
    /// - Its destination module name list.
    /// - Its module state.
    connections: HashMap<String, (Vec<String>, Option<ModuleState>)>,
}

impl ModuleManager {
    /// The expected name of the broadcaster module.
    const BROADCASTER_NAME: &str = "broadcaster";

    /// Sync all conjunction module states in self to have their expected inputs set.
    fn sync_conjunction_inputs(&mut self) {
        // NOTE working around borrows of self with owned String

        // collect names of conjunction modules
        let conjunction_names: Vec<String> = self
            .connections
            .iter()
            .filter_map(|(name, (_, state))| {
                state.as_ref().and_then(|ms| match ms {
                    ModuleState::Conjunction(_) => Some(name.clone()),
                    ModuleState::FlipFlop(_) => None,
                })
            })
            .collect();

        // collect inputs of each module
        let mut inputs_map: HashMap<String, Vec<String>> = HashMap::new();
        for (source, (dest, _)) in &self.connections {
            for target in &conjunction_names {
                if dest.contains(target) {
                    inputs_map
                        .entry(target.clone())
                        .or_default()
                        .push(source.clone());
                }
            }
        }

        // set inputs on conjunction module states
        for (name, inputs) in inputs_map {
            if let Some((_, Some(ModuleState::Conjunction(conjunction_module)))) =
                self.connections.get_mut(&name)
            {
                let str_inputs: Vec<&str> =
                    inputs.iter().map(std::string::String::as_str).collect();
                conjunction_module.set_inputs(&str_inputs);
            }
        }
    }
}

#[derive(thiserror::Error, Debug)]
enum ParseModuleManagerError {
    #[error("expected arrow delimiter (\" -> \") separating module name and destination modules")]
    MissingArrowDelimiter,
}

impl ParseData for ModuleManager {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let connections: HashMap<_, _> =
            parse_input_lines(input, |_, line| -> Result<_, ParseModuleManagerError> {
                let (name, destinations_list) = line
                    .split_once(" -> ")
                    .ok_or(ParseModuleManagerError::MissingArrowDelimiter)?;

                let destinations: Vec<_> = destinations_list
                    .split(", ")
                    .map(std::string::ToString::to_string)
                    .collect();

                if let Some(flip_flop_name) = name.strip_prefix('%') {
                    Ok((
                        flip_flop_name.to_string(),
                        (
                            destinations,
                            Some(ModuleState::FlipFlop(FlipFlopModule::default())),
                        ),
                    ))
                } else if let Some(conjunction_name) = name.strip_prefix('&') {
                    Ok((
                        conjunction_name.to_string(),
                        (
                            destinations,
                            Some(ModuleState::Conjunction(ConjunctionModule::default())),
                        ),
                    ))
                } else {
                    Ok((name.to_string(), (destinations, None)))
                }
            })
            .collect::<Result<_, _>>()?;

        let mut manager = Self { connections };
        manager.sync_conjunction_inputs();

        Ok(manager)
    }
}

/*
A button is connected to send a low pulse to the broadcaster module. Pulses must finish processing
before pressing the button again. Pulses are processed in the order they are sent.

For part 1, push the button 1000 times, count how many pulses were sent through the module
connections (including the button pulses) separately by high pulses and low pulses, and multiply the
high and low counts together.
*/

impl ModuleManager {
    /// Send a low pulse into the broadcast module, mutating module states. Returns the sequence of
    /// pulses processed through module connections as a vector of
    /// (source name, pulse value, target name).
    fn send_low_pulse(&mut self) -> Vec<(String, bool, String)> {
        let mut pulses_processed: Vec<(String, bool, String)> = Vec::new();

        // queue (source, pulse, target) to process FIFO order
        // - store owned String to not borrow self into following iterations
        let mut queue: VecDeque<(String, bool, String)> = VecDeque::new();
        // init low pulse to broadcaster
        queue.push_back((String::new(), false, Self::BROADCASTER_NAME.to_string()));

        while let Some(next) = queue.pop_front() {
            pulses_processed.push(next.clone());
            let (source, pulse, target) = next;

            if let Some((dest, state_opt)) = self.connections.get_mut(&target) {
                match state_opt {
                    None => {
                        // propagate pulse to destinations
                        for dest_name in dest {
                            queue.push_back((target.clone(), pulse, dest_name.clone()));
                        }
                    }
                    Some(state) => {
                        // send pulse into module's state, and send any output to destinations
                        if let Some(output) = state.receive_pulse(pulse, source.as_str()) {
                            for dest_name in dest {
                                queue.push_back((target.clone(), output, dest_name.clone()));
                            }
                        }
                    }
                }
            }
        }

        pulses_processed
    }
}

struct Day20;

impl Solution<PartOne> for Day20 {
    type Input = ModuleManager;
    type Output = u32;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let mut manager = input.clone();
        let mut low_count: Self::Output = 0;
        let mut high_count: Self::Output = 0;
        // NOTE I had a thought that cycle detection like in day 14 might have been needed for
        // optimization, but this seems to take less than a second with given input
        for _ in 0..1000 {
            let pulses = manager.send_low_pulse();
            for (_, pulse_value, _) in pulses {
                if pulse_value {
                    high_count = high_count
                        .checked_add(1)
                        .expect("incrementing high count should not overflow");
                } else {
                    low_count = low_count
                        .checked_add(1)
                        .expect("incrementing low count should not overflow");
                }
            }
        }
        let product = low_count
            .checked_mul(high_count)
            .expect("product of counts should not overflow");
        Ok(product)
    }
}

/*
For part 2, find the minimum button presses needed to eventually have a module "rx" receive a single
low pulse.
*/

/*
Referencing an explanation to figure out part 2: https://advent-of-code.xavd.id/writeups/2023/day/20/

This requires analyzing my input connections for a pre-designed structure:
- a single conjunction module connects to rx
- 4 conjunction modules connect to the single module
- the 4 modules have single source connections, acting as inverters
So the 4 modules must all receive a low pulse/send a high pulse in the same button cycle for rx to
get a low pulse.

Assuming that the 4 modules are connected with isolated subgraphs, the subgraphs likely loop in
their state. Find the Least Common Multiple among the loops.

I can copy code from Day 8 for LCM.
*/

impl ModuleManager {
    /// The expected name of the "rx" module.
    const RX_NAME: &str = "rx";

    /// Get the expected set of conjunction modules configured as inverters that are dependencies to
    /// a single conjunction source to the "rx" module.
    fn get_rx_source_inverters(&self) -> Vec<String> {
        // find the single source of rx
        let parent_list: Vec<_> = self
            .connections
            .iter()
            .filter_map(|(name, (dest, _))| {
                dest.contains(&Self::RX_NAME.to_string()).then_some(name)
            })
            .collect();
        let parent = match parent_list.len() {
            1 => parent_list[0],
            0 => panic!("no module connects to rx module"),
            _ => panic!("multiple modules connect to rx module: {parent_list:?}"),
        };

        // expect single source is a conjunction module, and find the dependencies of this source
        let (_, parent_state) = self
            .connections
            .get(parent)
            .expect("name key provided from filter of connections");
        let inverter_list: Vec<_> = match parent_state {
            Some(ModuleState::Conjunction(parent_conjunction_module)) => {
                parent_conjunction_module.0.keys().collect()
            }
            _ => panic!("parent module of rx module is not a conjunction module"),
        };
        assert!(
            !inverter_list.is_empty(),
            "no dependencies found for the parent conjunction module of rx module"
        );

        // confirm the dependencies are single connection conjunction modules
        for &name in &inverter_list {
            if let Some((_, state)) = self.connections.get(name) {
                match state {
                    Some(ModuleState::Conjunction(conjunction_module)) => {
                        match conjunction_module.0.len() {
                            1 => {} // do nothing
                            0 => panic!("conjunction module {name:?} has no sources to invert"),
                            _ => panic!(
                                "conjunction module {name:?} has too many sources to be an inverter: {:?}",
                                conjunction_module.0.keys().collect::<Vec<_>>()
                            ),
                        }
                    }
                    _ => panic!("module {name:?} is not a conjunction module"),
                }
            } else {
                panic!("no module data found for inverter module name: {name:?}");
            }
        }

        inverter_list.into_iter().cloned().collect()
    }
}

fn least_common_multiple(numbers: &[u32]) -> u64 {
    fn greatest_common_divisor(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            greatest_common_divisor(b, a % b)
        }
    }

    if numbers.is_empty() {
        return 0;
    }

    let mut result = u64::from(numbers[0]);
    for num in numbers[1..].iter().map(|&num| u64::from(num)) {
        result = result
            .checked_mul(num)
            .and_then(|product| product.checked_div(greatest_common_divisor(result, num)))
            .expect("calculating least common multiple should not overflow");
    }
    result
}

impl Solution<PartTwo> for Day20 {
    type Input = ModuleManager;
    type Output = u64;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let inverters = input.get_rx_source_inverters();
        // start each inverter's minimum count as 0 to say no count is found yet
        let mut inverter_min_counts: HashMap<String, u32> =
            inverters.into_iter().map(|name| (name, 0)).collect();

        let mut manager = input.clone();
        let mut count = 0u32;
        while inverter_min_counts.values().any(|v| *v == 0) {
            let pulses = manager.send_low_pulse();
            count = count
                .checked_add(1)
                .expect("incrementing count should not overflow");

            let inverters_without_count: Vec<_> = inverter_min_counts
                .iter()
                .filter(|&(_, min_count)| *min_count == 0)
                .map(|(name, _)| name.clone())
                .collect();
            for name in inverters_without_count {
                if pulses
                    .iter()
                    .any(|(source, pulse_value, _)| *source == name && *pulse_value)
                {
                    inverter_min_counts.insert(name, count);
                }
            }
        }

        let min_counts: Vec<_> = inverter_min_counts.values().copied().collect();
        Ok(least_common_multiple(&min_counts))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_INPUT_ONE: &str = r"broadcaster -> a, b, c
%a -> b
%b -> c
%c -> inv
&inv -> a
";

    #[test]
    fn part_one_solves_example_one() -> DynamicResult<()> {
        let parsed = ModuleManager::parse(EXAMPLE_INPUT_ONE)?;
        let result = <Day20 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 32_000_000);
        Ok(())
    }

    const EXAMPLE_INPUT_TWO: &str = r"broadcaster -> a
%a -> inv, con
&inv -> b
%b -> con
&con -> output
";

    #[test]
    fn part_one_solves_example_two() -> DynamicResult<()> {
        let parsed = ModuleManager::parse(EXAMPLE_INPUT_TWO)?;
        let result = <Day20 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 11_687_500);
        Ok(())
    }
}

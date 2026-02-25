use std::collections::{HashMap, HashSet, VecDeque};

use aoc_framework::parsing::parse_input_lines;
use aoc_framework::runner::solution_runner;
use aoc_framework::{DynamicResult, ParseData, PartOne, Solution};
use petgraph::Undirected;
use petgraph::algo::kosaraju_scc;
use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::prelude::{StableGraph, StableUnGraph};

#[solution_runner(name = "Day 25: Snowverload", parsed = Wiring, part_one = Day25)]
impl super::AdventOfCode2023<25> {}

/*
Input is a wiring diagram of components. Each line formats a name, `: `, and a space separated list
of other names connected.

> Connections are undirected. Input should not redundantly specify connections.
*/

/// A collection of components connected with undirected wires.
#[derive(Debug)]
struct Wiring {
    /// A graph of components and wires connecting.
    ///
    /// Nodes hold names of components, and edges hold count of wires connecting.
    graph: StableUnGraph<String, u32>,
}

#[derive(thiserror::Error, Debug)]
enum ParseWiringError {
    #[error("expected a colon (':') to delimit source name from connections")]
    MissingColonDelimiter,
}

impl ParseData for Wiring {
    fn parse(input: &str) -> DynamicResult<Self>
    where
        Self: Sized,
    {
        let mut graph: StableGraph<String, u32, Undirected> = StableGraph::default();
        let mut names_map: HashMap<String, NodeIndex> = HashMap::new();

        parse_input_lines(input, |_, line| -> Result<_, ParseWiringError> {
            let (source, connections_list) = line
                .split_once(':')
                .ok_or(ParseWiringError::MissingColonDelimiter)?;
            let connections: Vec<_> = connections_list
                .split(' ')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect();

            // add any component names not in the graph/map yet
            for &name in connections.iter().chain([source].iter()) {
                names_map
                    .entry(name.to_string())
                    .or_insert_with(|| graph.add_node(name.to_string()));
            }

            // add edges of 1 wire from source to connections
            let source_node = names_map[source];
            for destination in connections {
                let destination_node = names_map[destination];
                // avoid parallel/duplicate edges by using update_edge
                graph.update_edge(source_node, destination_node, 1);
            }

            Ok(())
        })
        .collect::<Result<(), _>>()?;

        Ok(Self { graph })
    }
}

/*
For part 1, determine three wires to disconnect to modify the component connections into two
separate groups, then return the product of the sizes of the groups.
*/

/*
implementing Betweenness Centrality of edges to find edges to cut
*/

/// Find the edge betweenness values of a graph, or the frequency of an edge being used in all
/// shortest paths between all nodes.
fn edge_betweenness<N, E>(graph: &StableUnGraph<N, E>) -> HashMap<EdgeIndex, usize> {
    let mut betweenness: HashMap<EdgeIndex, usize> = HashMap::new();

    for node in graph.node_indices() {
        // BFS shortest paths to other nodes
        let mut queue = VecDeque::from([(node, vec![node])]);
        let mut visited: HashSet<NodeIndex> = HashSet::new();
        while let Some((current, path)) = queue.pop_front() {
            if visited.insert(current) {
                // add edges used in path for frequencies
                for pair in path.windows(2) {
                    if let Some(edge) = graph.find_edge(pair[0], pair[1]) {
                        betweenness
                            .entry(edge)
                            .and_modify(|frequency| {
                                *frequency = frequency
                                    .checked_add(1)
                                    .expect("incrementing edge frequency should not overflow");
                            })
                            .or_insert(1);
                    }
                }

                // explore unvisited neighbors
                for next in graph.neighbors(current).filter(|n| !visited.contains(n)) {
                    let mut next_path = path.clone();
                    next_path.push(next);
                    queue.push_back((next, next_path));
                }
            }
        }
    }

    betweenness
}

impl Wiring {
    fn partition_sizes_from_betweenness(&self) -> (usize, usize) {
        let betweenness = edge_betweenness(&self.graph);

        // the expected 3 cuts should be the top 3 frequencies from betweenness
        let mut edge_frequencies: Vec<_> = betweenness.iter().collect();
        edge_frequencies.sort_by(|a, b| b.1.cmp(a.1));
        let cuts = &edge_frequencies[0..3];

        let mut cut_graph = self.graph.clone();
        for &(edge, _) in cuts {
            cut_graph.remove_edge(*edge);
        }

        let connected_components = kosaraju_scc(&cut_graph);
        assert_eq!(
            connected_components.len(),
            2,
            "expected partition into 2 connected components after cuts"
        );
        (connected_components[0].len(), connected_components[1].len())
    }
}

struct Day25;

impl Solution<PartOne> for Day25 {
    type Input = Wiring;
    type Output = usize;

    fn solve(input: &Self::Input) -> DynamicResult<Self::Output> {
        let (first, second) = input.partition_sizes_from_betweenness();
        Ok(first
            .checked_mul(second)
            .expect("product should not overflow"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub const EXAMPLE_INPUT: &str = r"jqt: rhn xhk nvd
rsh: frs pzl lsr
xhk: hfx
cmg: qnr nvd lhk bvb
rhn: xhk bvb hfx
bvb: xhk hfx
pzl: lsr hfx nvd
qnr: nvd
ntq: jqt hfx bvb xhk
nvd: lhk
lsr: lhk
rzs: qnr cmg lsr rsh
frs: qnr lhk lsr
";

    #[test]
    fn part_one_solves_example() -> DynamicResult<()> {
        let parsed = Wiring::parse(EXAMPLE_INPUT)?;
        let result = <Day25 as Solution<PartOne>>::solve(&parsed)?;
        assert_eq!(result, 54);
        Ok(())
    }
}

#[cfg(test)]
mod min_cut {
    use std::collections::HashSet;

    use aoc_framework::{DynamicResult, ParseData};
    use checked_sum::CheckedSum;
    use petgraph::Direction::Incoming;
    use petgraph::graph::NodeIndex;
    use petgraph::prelude::StableUnGraph;
    use petgraph::visit::EdgeRef;

    use super::Wiring;
    use super::tests::EXAMPLE_INPUT;

    /*
    https://blog.thomasjungblut.com/graph/mincut/mincut/
    implementing the Stoer-Wagner algorithm for minimum cut

    Turns out this was not performant enough to run on the full input. But it was hard to work out
    for me, so I'm keeping it for posterity.
    */

    fn find_edge_weight<N, E>(
        graph: &StableUnGraph<N, E>,
        a: NodeIndex,
        b: NodeIndex,
    ) -> Option<&E> {
        graph.find_edge(a, b).and_then(|e| graph.edge_weight(e))
    }

    fn find_edge_weight_mut<N, E>(
        graph: &mut StableUnGraph<N, E>,
        a: NodeIndex,
        b: NodeIndex,
    ) -> Option<&mut E> {
        graph.find_edge(a, b).and_then(|e| graph.edge_weight_mut(e))
    }

    /// Nodes `s` and `t` found in a minimum cut phase, with the cut weight of `t`.
    #[derive(Debug, Clone, Copy)]
    struct CutOfThePhase {
        s: NodeIndex,
        t: NodeIndex,
        cut_weight: u32,
    }

    /// Calculate a minimum cut phase from the given graph via maximum adjacency search.
    fn max_adjacency_search<N>(graph: &StableUnGraph<N, u32>) -> CutOfThePhase {
        assert!(
            graph.node_count() >= 2,
            "need at least 2 nodes in graph for search, found {} components",
            graph.node_count()
        );

        // randomly pick start node, process through the remainder
        let mut id_iter = graph.node_indices();
        let start = id_iter.next().expect("asserted non-empty graph");
        let mut found = vec![start];
        let mut candidates: HashSet<_> = id_iter.collect();
        let mut last_cut_weight = u32::MIN;

        while !candidates.is_empty() {
            let mut max_next_opt: Option<NodeIndex> = None;
            let mut max_weight = u32::MIN;
            for next in &candidates {
                let weight_sum = found
                    .iter()
                    .filter_map(|f| find_edge_weight(graph, *next, *f).copied())
                    .checked_sum()
                    .expect("sum of weights should not overflow");

                if weight_sum > max_weight {
                    max_next_opt = Some(*next);
                    max_weight = weight_sum;
                }
            }

            if let Some(max_next) = max_next_opt {
                candidates.remove(&max_next);
                found.push(max_next);
                last_cut_weight = max_weight;
            }
        }

        let n = found.len();
        CutOfThePhase {
            s: found[n - 2],
            t: found[n - 1],
            cut_weight: last_cut_weight,
        }
    }

    /// Create a new graph by merging a found minimum cut for a given graph, which merges `t` into `s`.
    fn merge_from_cut<N>(graph: &mut StableUnGraph<N, u32>, cut: CutOfThePhase) {
        // move edges before removing node
        // NOTE collecting owned data to avoid borrows of graph
        let neighbors: Vec<_> = graph
            .edges_directed(cut.t, Incoming)
            .filter(|&e| e.source() != cut.s)
            .map(|e| (e.source(), *e.weight()))
            .collect();
        for (neighbor, neighbor_weight) in neighbors {
            // add weight to an existing edge, or create a new edge with weight
            if let Some(existing_weight) = find_edge_weight_mut(graph, neighbor, cut.s) {
                *existing_weight = existing_weight
                    .checked_add(neighbor_weight)
                    .expect("incrementing weight should not overflow");
            } else {
                graph.add_edge(neighbor, cut.s, neighbor_weight);
            }
        }

        graph.remove_node(cut.t);
    }

    pub fn partition_sizes_from_min_cut<N>(graph: &StableUnGraph<N, u32>) -> (usize, usize)
    where
        N: Clone,
    {
        let mut graph_clone = graph.clone();

        let mut current_partition = HashSet::new();
        let mut current_best_partition = HashSet::new();
        let mut current_best_cut_weight: Option<u32> = None;

        while graph_clone.node_count() > 1 {
            let cut = max_adjacency_search(&graph_clone);
            current_partition.insert(cut.t);
            if current_best_cut_weight.is_none_or(|best| cut.cut_weight < best) {
                current_best_cut_weight = Some(cut.cut_weight);
                current_best_partition.clone_from(&current_partition);
            }
            merge_from_cut(&mut graph_clone, cut);
        }

        let partition_size = current_best_partition.len();
        (partition_size, graph.node_count() - partition_size)
    }

    #[test]
    fn min_cut_solves_example() -> DynamicResult<()> {
        let parsed = Wiring::parse(EXAMPLE_INPUT)?;
        let (first, second) = partition_sizes_from_min_cut(&parsed.graph);
        assert_eq!(first * second, 54);
        Ok(())
    }
}

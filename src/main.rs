#![feature(impl_trait_in_fn_trait_return)]

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{anyhow, bail};
use clap::{Parser, ValueEnum};
use graphviz_rust::dot_structures::{self, Graph};

mod executions;
pub use executions::*;
use itertools::Itertools;
mod fenwick;
mod iter;
mod relations;

#[derive(Parser)]
struct App {
    graph: PathBuf,
    /// The consistency model to use. Possible values are `sc`, `tso`, `rlx`,
    /// and `custom`.
    #[clap(short, long, default_value = "sc")]
    mode: Mode,
    /// Whether to skip the naive consistency check.
    #[clap(short, long, default_value = "false")]
    no_naive: bool,
    /// Whether to print results as JSON, cannot be used with naive enabled.
    #[clap(short = 'M', long, default_value = "false")]
    machine_readable: bool,
}

#[derive(ValueEnum, Clone)]
enum Mode {
    Sc,
    Tso,
    #[clap(name = "rlx")]
    Relaxed,
    Custom,
}

fn main() -> anyhow::Result<()> {
    let app = App::parse();
    let input_string = fs::read_to_string(&app.graph)?
        .split('\n')
        .filter(|s| !s.ends_with("[label=\"po\"];"))
        .join("\n");
    let graph = graphviz_rust::parse(&input_string).map_err(|e| anyhow!(e))?;
    let Graph::DiGraph { stmts, .. } = graph else {
        bail!("Graph is not a digraph");
    };

    if !app.no_naive && app.machine_readable {
        bail!("Cannot use both naive and machine readable together")
    }

    let mut events: Vec<Vec<(usize, Event)>> = Vec::new();
    let mut rf_edges = Vec::new();
    let mut max_location = 0;

    'stmts_loop: for stmt in stmts {
        match stmt {
            dot_structures::Stmt::Node(node) => {
                let mut thread_num = 0;
                let mut idx = 0;
                let mut event = Event {
                    location: 0,
                    event_type: EventType::Read,
                };
                for attr in node.attributes {
                    let dot_structures::Id::Plain(key) = attr.0 else {
                        continue;
                    };
                    let dot_structures::Id::Plain(value) = attr.1 else {
                        continue;
                    };

                    match key.as_str() {
                        "type" => event.event_type = value.parse()?,
                        "loc" => event.location = value.parse()?,
                        "th" => thread_num = value.parse()?,
                        "idx" => idx = value.parse()?,
                        _ => {}
                    }
                }
                if let Some(thread) = events.get_mut(thread_num) {
                    thread.push((idx, event));
                } else {
                    events.resize(thread_num + 1, Vec::new());
                    events[thread_num].push((idx, event));
                }
                max_location = max_location.max(event.location);
            }
            dot_structures::Stmt::Edge(edge) => {
                let mut from_th = 0;
                let mut from_idx = 0;
                let mut to_th = 0;
                let mut to_idx = 0;
                for attr in edge.attributes {
                    let dot_structures::Id::Plain(key) = attr.0 else {
                        continue;
                    };
                    let value = match attr.1 {
                        dot_structures::Id::Plain(value) => value,
                        dot_structures::Id::Escaped(value)
                            if value.starts_with("\"") && value.ends_with("\"") =>
                        {
                            value[1..value.len() - 1].into()
                        }
                        _ => continue,
                    };

                    match key.as_str() {
                        "label" if value != "rf" => continue 'stmts_loop,
                        "from_th" => from_th = value.parse()?,
                        "from_idx" => from_idx = value.parse()?,
                        "to_th" => to_th = value.parse()?,
                        "to_idx" => to_idx = value.parse()?,
                        _ => {}
                    }
                }
                rf_edges.push(((from_th + 1, from_idx), (to_th + 1, to_idx)));
            }
            _ => bail!("Unsupported statement"),
        }
    }

    let mut sorted_events: Vec<Vec<Event>> = Vec::new();
    for mut thread in events {
        thread.sort_by_key(|&(i, _)| i);
        sorted_events.push(thread.into_iter().map(|(_, e)| e).collect());
    }

    let mut exec = NaiveExecution::new(&sorted_events, max_location + 1);
    for (from, to) in rf_edges {
        exec.add_rf(exec.to_event_id(from), exec.to_event_id(to));
    }
    exec.close_rf();

    match app.mode {
        Mode::Sc => exec = exec.with_sc(),
        Mode::Tso => exec = exec.with_tso(),
        Mode::Relaxed => exec = exec.with_relaxed(),
        Mode::Custom => todo!(),
    }

    let mut linearization_checked = 0;
    if app.no_naive {
        if !app.machine_readable {
            println!("Skipping naive consistency check");
        }
    } else {
        println!("Running naive consistency check...");
        let start = Instant::now();
        let is_consistent = exec.is_totally_consistent();
        let elapsed = start.elapsed();
        linearization_checked = exec.linearizations_checked();
        println!("Naive consistency check took {} ms", elapsed.as_millis());
        match is_consistent {
            Some(result) => println!("Naive consistency check result: {result}"),
            None => println!("Naive consistency check result: No result"),
        };
        println!("Checked {linearization_checked} linearization(s)\n");
    }

    if !app.machine_readable {
        println!("Running consistency check with saturation...");
    }
    let start = Instant::now();
    let mut exec = SaturatingExecution::from(exec);
    let is_consistent = exec.is_totally_consistent();
    let elapsed = start.elapsed();
    linearization_checked = exec.linearizations_checked() - linearization_checked;
    if !app.machine_readable {
        println!(
            "Consistency check with saturation took {} ms",
            elapsed.as_millis()
        );
        match is_consistent {
            Some(result) => println!("Consistency check with saturation result: {result}"),
            None => println!("Consistency check with saturation result: No result"),
        };
        println!("Checked {linearization_checked} linearization(s)");
        println!("Inserted {} edge(s) with saturation", exec.edges_inserted());
    } else {
        let is_consistent_bool = is_consistent.is_some();
        let edges_inserted = exec.edges_inserted();
        println!("{{\"consistent\": {is_consistent_bool}, \"checked_linearizations\": {linearization_checked}, \"saturation_inserted_edges\": {edges_inserted}}}");
    }

    Ok(())
}

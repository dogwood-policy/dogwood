//! `partitioned`: the export of the `dogwood_lean_bridge` library, with the crate's own temporal
//! engine run partitioned by the event schema's universal symmetric pins
//! (`AuthorizerBuilder::partition_temporal`): each trace's `Authorizer` keeps one monitor per
//! pinned key and evaluates the non-relativized leaves within it. The conformance harness
//! compares those verdicts with the specification's as it does the default export's. See the
//! library for the command line.

fn main() {
    dogwood_lean_bridge::main_with(Some(&|_, _| {
        Box::new(dogwood_language::InMemoryTemporalEngine::new())
    }));
}

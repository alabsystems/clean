// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linker-measured reachability of the dependency-closed replay.
//!
//! This binary calls ONLY [`recheck_closed`]. Built without optimisation
//! (no inlining) and linked with dead-code stripping (the default for an
//! executable), its symbol table is the set of functions the replay can
//! reach through any static call, vtable or function pointer — the ground
//! truth `every_by_name_reference_the_replay_can_reach_is_gated_or_explained`
//! over-approximates from source. `scripts/replay_reachability_census.sh`
//! builds it and compares the two.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::recheck_closed::{recheck_closed, ClosedRecheckOptions};
use std::collections::BTreeSet;

fn main() {
    let env = Environment::default();
    let targets: BTreeSet<Name> = std::env::args()
        .skip(1)
        .map(|s| Name::from_string(&s))
        .collect();
    let run = recheck_closed(&env, &targets, &ClosedRecheckOptions::default());
    println!("{}", run.report.verdict_sentence());
}

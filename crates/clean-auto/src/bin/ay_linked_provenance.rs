// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Emit AY build identity from the library actually linked into this process.

use clean_auto::bridge::ay_contract::linked_ay_provenance;
use serde::Serialize;

#[derive(Serialize)]
struct LinkedAyProvenanceOutput {
    revision_kind: &'static str,
    revision: &'static str,
}

fn main() -> anyhow::Result<()> {
    let linked = linked_ay_provenance();
    let output = LinkedAyProvenanceOutput {
        revision_kind: linked.revision_kind,
        revision: linked.revision,
    };
    serde_json::to_writer(std::io::stdout(), &output)?;
    println!();
    Ok(())
}

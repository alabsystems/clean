// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Emit AY build identity from the library actually linked into this process.

#[cfg(not(target_arch = "wasm32"))]
use clean_auto::bridge::ay_contract::linked_ay_provenance;
#[cfg(not(target_arch = "wasm32"))]
use serde::Serialize;

#[cfg(not(target_arch = "wasm32"))]
#[derive(Serialize)]
struct LinkedAyProvenanceOutput {
    revision_kind: &'static str,
    revision: &'static str,
}

// wasm32 links no AY library, so there is no provenance to emit.
#[cfg(target_arch = "wasm32")]
fn main() {
    eprintln!("ay_linked_provenance is unavailable on wasm");
}

#[cfg(not(target_arch = "wasm32"))]
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

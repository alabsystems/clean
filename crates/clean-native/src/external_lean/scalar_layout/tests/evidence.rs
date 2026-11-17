// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional raw qualification artifacts. These files are observations only;
//! no production API reads them or accepts them as custody/layout evidence.

use super::{CheckedScalarLayoutFacts, ExternalLeanProgram};
use serde_json::json;
pub(super) fn retain(
    program: &ExternalLeanProgram,
    facts: &CheckedScalarLayoutFacts<'_>,
    label: &str,
) {
    let Ok(directory) = std::env::var("CLEAN_SCALAR_LAYOUT_EVIDENCE_DIR") else {
        return;
    };
    let directory = std::path::PathBuf::from(directory)
        .join(program.world().tag())
        .join(label);
    std::fs::create_dir_all(&directory).unwrap();
    // Preserve actual primary source/artifact bytes while the owned snapshot
    // lives. Imported SDK originals remain at their separately hashed paths.
    for suffix in [
        "lean",
        "olean",
        "olean.private",
        "olean.server",
        "ir",
        "ir.sig",
        "ilean",
    ] {
        let name = format!("Layout.{suffix}");
        let input = program.custody._snapshot.path().join(&name);
        if input.try_exists().unwrap() {
            std::fs::copy(input, directory.join(name)).unwrap();
        }
    }
    let capture = facts.source_capture();
    let inputs: Vec<_> = program
        .inputs()
        .iter()
        .map(|input| json!({"path":input.path,"sha256":input.sha256,"bytes":input.bytes}))
        .collect();
    let data = json!({
        "world":program.world().tag(),"source_root":facts.root(),"snapshot_root":program.custody._snapshot.path(),
        "inputs":inputs,"visited_recursors":facts.visited_recursors(),
        "capture_roots":capture.roots(),"capture_members":capture.members(),
        "capture_before":capture.before(),"capture_after":capture.after(),
        "original_runtime_attributes":capture.members().iter().map(|name|json!({"name":name,"extern":program.env.get_extern(name),"csimp":clean_kernel::env::csimp::rules_for(&program.env,Some(name)),"staged":program.env.is_staged_header(name)})).collect::<Vec<_>>(),
        "kernel_theory":format!("{:?}",program.env.kernel_theory()),
        "capture_digest":capture.snapshot_blake3(),"replay":facts.replay_verdict(),
        "replay_members":facts.replay.members(),
        "context_members":facts.context.dependency_names().collect::<Vec<_>>(),
        "global_errors":program.source_capture().errors,
        "global_row_failures":program.source_capture().row_failures.iter().map(|r|json!({"phase":r.phase,"name":r.name,"reason":r.reason})).collect::<Vec<_>>(),
        "global_digest":program.source_capture().snapshot_blake3,
        "native_calls":0,
    });
    serde_json::to_writer(
        std::fs::File::create(directory.join("observations.json")).unwrap(),
        &data,
    )
    .unwrap();
}

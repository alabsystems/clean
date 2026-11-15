// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Run the public handoff on the unchanged measured-world matcher fixture.
//! Requires the official v4.35 SDK selected by ELAN_HOME. This is a small
//! general compiler control, not Veil Ring or a binary proof.

use clean_compiler::cli::EmitFormat;
use clean_kernel::{LeanWorld, Name};
use clean_native::external_lean::{ExternalLeanInput, ExternalLeanProgram};
use std::path::Path;
use std::process::Command;

fn main() -> anyhow::Result<()> {
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.35.0/matcher-metadata/MatcherParity.lean");
    let module = Name::from_string("MatcherParity");
    // Reuse the unchanged fixture producer's exact typed dependency roots;
    // the constructor still recompiles the original source and reconciles
    // its actual output imports against the owned artifact closure.
    let imports: Vec<_> =
        clean_olean::parse_typed_imports(&std::fs::read(file.with_extension("olean"))?)?
            .into_iter()
            .map(|import| import.module_name)
            .collect();
    let program = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &file,
        module: &module,
        imports: &imports,
        search_paths: &[],
        world: LeanWorld::Lean435,
    })?;
    let root = Name::from_string("MatcherParity.chooseOverlap");
    let replayed = program.inspect_owned_declaration(&root)?;
    println!("world={} source=unchanged-MatcherParity route=owned-source/imports/kernel-replay root={} admitted={} families={} axioms={} trust-markers={}; frontend TCB explicit; native not yet selected",
        program.world().tag(), replayed.constant().name,
        replayed.replay_verdict().constants_admitted,
        replayed.replay_verdict().families_replayed,
        replayed.replay_verdict().imported_axioms.len(),
        replayed.replay_verdict().trust_markers.len());
    let selected = program.select(&root, 0)?;
    let c = selected.emit(EmitFormat::C)?;
    let dir = tempfile::tempdir()?;
    let driver = "int main(void) { const unsigned expected[2][2] = {{1,1},{2,3}}; for (unsigned a=0;a<2;++a) for (unsigned b=0;b<2;++b) { clean_obj* result = l_MatcherParity_chooseOverlap(clean_box(a),clean_box(b)); if (clean_unbox_uint64(result) != expected[a][b]) return 1; } return 0; }";
    let binary = clean_native::native_build::build_extract_executable(dir.path(), "", &c, driver)?;
    let status = Command::new(binary).status()?;
    anyhow::ensure!(status.success(), "C matcher control failed: {status}");
    println!("world={} source=unchanged-MatcherParity route=general-LCNF/L5IR/C cases=4 passed; experimental/unverified; no binary proof; not Veil Ring", program.world().tag());
    #[cfg(feature = "trust-ir-backend")]
    {
        let ir = selected.emit(EmitFormat::Trustir)?;
        anyhow::ensure!(
            ir.contains("fn @MatcherParity.chooseOverlap("),
            "missing selected TrustIR declaration"
        );
        let object = dir.path().join("matcher.o");
        selected.emit_object(&object)?;
        println!("world={} route=ExternCalls/checked-object bytes={}; clean-compiler-unvalidated; object only", program.world().tag(), object.metadata()?.len());
    }
    Ok(())
}

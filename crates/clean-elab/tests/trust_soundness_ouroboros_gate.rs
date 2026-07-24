// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! # Ouroboros gate — the Trust toolchain re-verifies its own prover's soundness.
//!
//! `proofs/trust-soundness/*.lean` is a growing machine-checked proof that Trust's
//! discharge engine (trust-mc's CHC encoding + ay) is SOUND: `∀ program. verifier
//! says PROVED ⟹ the program is actually safe`. It turns the 8 hand-found
//! false-proofs (2026-06-19 soundness sweep) into a class that cannot exist by
//! construction.
//!
//! This test drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`, the
//! mandatory kernel check), so the soundness proof is CONTINUOUSLY re-verified on
//! every `cargo test` of the Trust toolchain. That closes the self-applying loop:
//! the prover (clean, a first-party Trust component) re-proves the soundness of the
//! verifier (trust-mc) on every build. If a proof ever stops kernel-checking, this
//! gate goes red.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_parser::parse_file;
use std::path::Path;

/// Drive the real `clean check` pipeline over one source file. Returns the number
/// of declarations kernel-checked, or Err with the first failure message.
fn kernel_check_file(source: &str) -> Result<usize, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let count = decls.len();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(count)
}

#[test]
fn trust_discharge_soundness_proofs_kernel_check() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/trust-soundness");
    let entries = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("trust-soundness proof corpus {dir:?} not found: {e}"));

    let mut files = 0usize;
    let mut declarations = 0usize;
    for entry in entries {
        let path = entry.expect("readable dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        files += 1;
        let source =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path:?}: {e}"));
        match kernel_check_file(&source) {
            Ok(n) => declarations += n,
            Err(e) => panic!(
                "OUROBOROS GATE BROKEN: the soundness proof {path:?} no longer kernel-checks — \
                 Trust's machine-checked proof of its own discharge soundness has regressed:\n{e}"
            ),
        }
    }

    assert!(
        files >= 6,
        "expected the trust-soundness proof corpus (>= 6 files), found {files} in {dir:?}"
    );
    assert!(
        declarations >= 40,
        "expected many kernel-checked declarations across the corpus, got {declarations}"
    );
    eprintln!(
        "ouroboros gate GREEN: {files} proof files, {declarations} declarations kernel-checked \
         — the verifier's soundness proof holds."
    );
}

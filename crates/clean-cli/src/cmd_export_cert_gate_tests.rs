// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean export-cert` over a separately built module (module-trust,
//! 2026-09-26). Measured on `ff6c33c2c`: `export-cert` loaded imports with
//! no `ImportedConeGate`, so a theorem citing a tampered artifact was exported
//! into a bundle with exit 0 — `theorem k1_false : (0 : Nat) = 1` through a
//! type-swapped lemma, through a lemma turned axiom, and a true statement
//! through a lemma whose proof term was flipped. Every attack first shows the
//! same file exporting against the GENUINE artifact.

use super::*;
use crate::check_import_gate::tests::{
    build_lib, consumer, payload, zero_add, CITE_FALSE, CITE_TRUE, LIB,
};

fn export(main: &Path) -> (anyhow::Result<()>, PathBuf) {
    let out = main.with_extension("cleancert");
    let result = handle_export_cert_command(ExportCertArgs {
        file: main.to_path_buf(),
        out: out.clone(),
        json_report: None,
        include_axioms: false,
        allow_empty: false,
    });
    (result, out)
}

fn assert_refused(main: &Path, what: &str) {
    let (result, out) = export(main);
    let err = result.expect_err(what);
    assert!(
        err.to_string().contains("declaration(s) failed"),
        "{what}: {err}"
    );
    assert!(!out.exists(), "{what}: a refused run writes no bundle");
}

#[test]
fn a_citation_of_a_genuine_artifact_exports() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let main = consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    let (result, out) = export(&main);
    result.expect("genuine citation exports");
    assert!(out.exists());
}

#[test]
fn a_false_theorem_through_a_type_swapped_artifact_is_not_exported() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let false_type = payload(&donor).1.constants[0].type_.clone();
    let main = consumer(tmp.path(), "t", &lib, CITE_FALSE, |p| {
        zero_add(p).type_ = false_type;
    });
    assert_refused(&main, "k1_false : 0 = 1 through a swapped type");
}

#[test]
fn a_citation_of_a_lemma_whose_proof_term_was_flipped_is_not_exported() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(
        tmp.path(),
        "donor",
        "theorem K1Lib.zero_add' (n : Nat) : n = n := rfl\n",
    );
    let wrong = payload(&donor).1.constants[0].value.clone();
    assert!(wrong.is_some(), "donor carries a proof term");
    let main = consumer(tmp.path(), "t", &lib, CITE_TRUE, |p| {
        zero_add(p).value = wrong;
    });
    assert_refused(&main, "flipped proof term");
}

#[test]
fn a_false_theorem_through_a_lemma_turned_axiom_is_not_exported() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let axiom = payload(&donor).1.constants[0].clone();
    let main = consumer(tmp.path(), "t", &lib, CITE_FALSE, |p| {
        *zero_add(p) = axiom;
    });
    assert_refused(&main, "imported axiom");
}

// ── round 27: an artifact that is not the build of its source ─────────────────

#[test]
fn a_value_swapped_artifact_next_to_its_source_is_not_exported() {
    use crate::import_binding::tests::{
        rewrite_payload, set_v, sourced_dependency, value_one, CITE_V0, CITE_V1, DEF_LIB,
    };
    let tmp = tempfile::tempdir().expect("tmp");
    // Control: the true statement exports over the genuine artifact.
    let (main, _) = sourced_dependency(tmp.path(), "q0", DEF_LIB, CITE_V0);
    let (result, out) = export(&main);
    result.expect("genuine citation exports");
    assert!(out.exists());
    // Measured on d0789d05f: exit 0 and a bundle of `K1Lib.v = 1`.
    let one = value_one(tmp.path());
    let (main, artifact) = sourced_dependency(tmp.path(), "q", DEF_LIB, CITE_V1);
    rewrite_payload(&artifact, |p| set_v(p, one));
    assert_refused(&main, "K1Lib.v = 1 over a rewritten value");
}

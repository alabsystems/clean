// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` citing a separately built module (module-trust,
//! `reports/2026-09-24-module-trust.md`). Measured on `7369eb6fd` before the
//! gate: every tampered artifact below let the citing file report
//! `1 passed, 0 failed`, exit 0 — including `theorem k1_false : (0 : Nat) = 1`.
//!
//! The library is built by `clean lake build` into a Lean Lake layout
//! (`.lake/build/lib/lean/K1Lib.olean`) of a project that holds NO `K1Lib`
//! source, so the import can only resolve to the artifact.

use crate::cmd_core::{collect_check_outcome, FileCheckOutcome};
use clean_kernel::cli::{PreludeMode, DEFAULT_DECL_BUDGET};
use clean_kernel::Name;
use clean_lake::{BuildContext, Workspace};
use clean_olean::payload::{decode_clean_payload, encode_clean_payload, CleanPayload};
use std::fs;
use std::path::{Path, PathBuf};

pub(crate) const LIB: &str = "theorem K1Lib.zero_add' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun k => 0 + k = k) rfl (fun k ih => congrArg Nat.succ ih) n
";
pub(crate) const CITE_TRUE: &str = "import K1Lib

theorem k1_uses (m : Nat) : 0 + (0 + m) = m :=
  Eq.trans (K1Lib.zero_add' (0 + m)) (K1Lib.zero_add' m)
";
pub(crate) const CITE_FALSE: &str = "import K1Lib

theorem k1_false : (0 : Nat) = 1 := K1Lib.zero_add' 0
";

fn lakefile(dir: &Path, roots: &[&str]) {
    let roots = roots
        .iter()
        .map(|r| format!("\"{r}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(
        dir.join("lakefile.toml"),
        format!("name = \"k1\"\n\n[[lean_lib]]\nname = \"K1\"\nroots = [{roots}]\n"),
    )
    .expect("lakefile");
}

/// Build `K1Lib` from `source` in its own project and return the artifact.
pub(crate) fn build_lib(root: &Path, tag: &str, source: &str) -> PathBuf {
    let dir = root.join(tag);
    fs::create_dir_all(&dir).expect("dir");
    lakefile(&dir, &["K1Lib"]);
    fs::write(dir.join("K1Lib.lean"), source).expect("source");
    // Held while building: elaborating a fixture bumps the process-wide
    // sorry / kernel-failure counters that a `check` or `export-cert` running
    // on another test thread reads between its reset and its verdict.
    let _serialised = crate::cmd_core::check_file_lock();
    let result = BuildContext::new(Workspace::load(&dir).expect("ws"))
        .build_all()
        .expect("build");
    assert!(result.failed.is_empty(), "{tag}: {result:?}");
    dir.join(".lake/build/lib/K1Lib.olean")
}

pub(crate) fn payload(path: &Path) -> (Vec<u8>, CleanPayload) {
    let bytes = fs::read(path).expect("artifact");
    let payload = decode_clean_payload(&bytes)
        .expect("decode")
        .expect("payload");
    (bytes, payload)
}

/// A consumer project holding only the artifact (possibly rewritten by
/// `edit`) and the citing file; returns the citing file's path.
pub(crate) fn consumer(
    root: &Path,
    tag: &str,
    artifact: &Path,
    cite: &str,
    edit: impl FnOnce(&mut CleanPayload),
) -> PathBuf {
    let dir = root.join(tag);
    let lib = dir.join(".lake/build/lib/lean");
    fs::create_dir_all(&lib).expect("lib dir");
    lakefile(&dir, &["Main"]);
    let (bytes, mut p) = payload(artifact);
    edit(&mut p);
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(encode_clean_payload(&p).expect("encode"));
    fs::write(lib.join("K1Lib.olean"), out).expect("artifact");
    let main = dir.join("Main.lean");
    fs::write(&main, cite).expect("main");
    main
}

fn check(path: &Path, allow_sorry: bool) -> FileCheckOutcome {
    collect_check_outcome(
        path,
        false,
        allow_sorry,
        PreludeMode::Builtin,
        true,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .expect("the check pipeline itself runs")
    .0
}

pub(crate) fn zero_add(p: &mut CleanPayload) -> &mut clean_kernel::ConstantInfo {
    let n = Name::from_string("K1Lib.zero_add'");
    p.constants
        .iter_mut()
        .find(|c| c.name == n)
        .expect("constant")
}

fn assert_not_credited(outcome: &FileCheckOutcome, what: &str) {
    assert_eq!(outcome.success_count, 0, "{what}: {outcome:#?}");
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|f| f.contains("cited closure not credited")),
        "{what}: {outcome:#?}"
    );
}

#[test]
fn a_genuine_artifact_is_cited_and_credited() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let main = consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    let outcome = check(&main, false);
    assert_eq!(outcome.success_count, 1, "{outcome:#?}");
    assert!(outcome.trust_failures.is_empty(), "{outcome:#?}");
}

#[test]
fn a_false_theorem_through_a_type_swapped_artifact_is_not_credited() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let false_type = payload(&donor).1.constants[0].type_.clone();
    // Control: against the genuine artifact the false theorem does not even
    // elaborate.
    let genuine = check(&consumer(tmp.path(), "g", &lib, CITE_FALSE, |_| {}), false);
    assert_eq!(genuine.success_count, 0);
    let main = consumer(tmp.path(), "t", &lib, CITE_FALSE, |p| {
        zero_add(p).type_ = false_type;
    });
    assert_not_credited(&check(&main, false), "k1_false : 0 = 1");
}

#[test]
fn a_citation_of_a_lemma_whose_proof_became_sorry_is_not_credited() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let sorry = {
        let env = clean_kernel::Environment::with_prelude();
        let decls =
            clean_parser::parse_file("theorem K1Lib.zero_add' (n : Nat) : 0 + n = n := sorry\n")
                .expect("parse");
        match clean_elab::ElabCtx::new(&env)
            .elab_decl(&decls[0])
            .expect("elab")
        {
            clean_elab::ElabResult::Theorem { proof, .. } => proof,
            other => panic!("{other:?}"),
        }
    };
    let main = consumer(tmp.path(), "t", &lib, CITE_TRUE, |p| {
        zero_add(p).value = Some(sorry);
    });
    // Refused before the gate runs: the citing theorem's own trust verdict is
    // its constant closure's (2026-09-28), and that closure reaches `sorryAx`
    // through the imported lemma — so the row is a sorry use, named through
    // the lemma it came from.
    let outcome = check(&main, false);
    assert_eq!(outcome.success_count, 0, "{outcome:#?}");
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|f| f.starts_with("k1_uses: declaration uses")
                && f.contains("sorry")
                && f.contains("(through K1Lib.zero_add')")),
        "sorry in the cited closure: {outcome:#?}"
    );
    assert_eq!(outcome.sorry_axioms, 1, "{outcome:#?}");
}

#[test]
fn a_citation_of_a_theorem_turned_axiom_is_not_credited() {
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
    let outcome = check(&main, false);
    assert_not_credited(&outcome, "imported axiom");
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|f| f.contains("imported axiom(s) K1Lib.zero_add'")),
        "{outcome:#?}"
    );
}

#[test]
fn a_theorem_citing_an_in_file_sorry_is_not_credited() {
    // A sorry one declaration away is not laundered by citing it: `b` rests on
    // `a`, and `a` on `sorryAx`.
    let tmp = tempfile::tempdir().expect("tmp");
    let path = tmp.path().join("Chain.lean");
    fs::write(
        &path,
        "theorem a_s : (1 : Nat) = 1 := sorry\n\ntheorem b_s : (1 : Nat) = 1 := a_s\n",
    )
    .expect("write");
    let outcome = check(&path, false);
    assert_eq!(outcome.success_count, 0, "{outcome:#?}");
    // Since 2026-09-28 the declaration's own trust verdict is its constant
    // closure's, so `b_s` is refused as a sorry use — through `a_s` — before
    // the gate runs.
    assert!(
        outcome.trust_failures.iter().any(|f| {
            f.starts_with("b_s: declaration uses") && f.contains("sorry (through a_s)")
        }),
        "{outcome:#?}"
    );
    assert_eq!(
        outcome.sorry_axioms, 2,
        "both declarations use sorry: {outcome:#?}"
    );
    // `--allow-sorry` waives it, as it waives `a_s`'s own sorry.
    assert_eq!(check(&path, true).success_count, 2);
}

#[test]
fn a_citation_of_an_imported_axiom_named_proof_irrel_is_not_credited() {
    // Module-trust verification, 2026-09-25: the gate exempted an imported
    // axiom by NAME when the name was on the foundational list, so a
    // dependency declaring `axiom proofIrrel : (0 : Nat) = 1` let this file
    // report `1 passed`, exit 0. Only the base's own declaration is given.
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", "axiom proofIrrel : (0 : Nat) = 1\n");
    let main = consumer(
        tmp.path(),
        "t",
        &lib,
        "import K1Lib\n\ntheorem fa_false : (0 : Nat) = 1 := proofIrrel\n",
        |_| {},
    );
    let outcome = check(&main, false);
    assert_not_credited(&outcome, "imported proofIrrel");
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|f| f.contains("imported axiom(s) proofIrrel")),
        "{outcome:#?}"
    );
}

// ---------------------------------------------------------------------------
// KR1 increment 3 (`docs/DECISIONS.md` R143): probe K1 through the reference
// entry, the door Certified evidence goes through. Trust's proven-core plan
// (§9, increment 3) asks that "a cross-module island citation passes, and
// K1's tampered-lemma mutation M3 exits non-zero". The positive half is the
// separately built `K1Lib` admitted declaration by declaration through
// `ReferenceKernel` (`clean_olean::payload_entry::admit_payload`) and
// `k1_uses` checked over it; M3 is the same with the payload's
// `K1Lib.zero_add'` stated `0 + n = n + 1` over the original proof.
// ---------------------------------------------------------------------------

/// Elaborate the one theorem in `source` (no `import` line) against `env`.
fn elab_theorem(env: &clean_kernel::Environment, source: &str) -> clean_kernel::Declaration {
    let decls = clean_parser::parse_file(source).expect("parse");
    match clean_elab::ElabCtx::new(env)
        .elab_decl(&decls[0])
        .expect("elab")
    {
        clean_elab::ElabResult::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => clean_kernel::Declaration::Theorem {
            name,
            level_params: universe_params,
            type_: ty,
            value: proof,
        },
        other => panic!("{other:?}"),
    }
}

fn strip_import(source: &str) -> &str {
    source
        .strip_prefix("import K1Lib\n")
        .expect("the citing file imports K1Lib")
}

fn entry() -> clean_kernel::ReferenceKernel {
    clean_kernel::ReferenceKernel::new(clean_kernel::Environment::with_prelude())
        .expect("with_prelude is a base")
}

#[test]
fn a_cross_module_citation_passes_through_the_reference_entry() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let (_, p) = payload(&lib);
    let mut k = entry();
    let tokens = clean_olean::payload_entry::admit_payload(&mut k, &p)
        .expect("the genuine K1Lib is admitted through the entry");
    assert_eq!(tokens.len(), 1, "one declaration: {tokens:?}");
    let uses = elab_theorem(k.environment(), strip_import(CITE_TRUE));
    let token = k
        .add_checked(uses)
        .expect("k1_uses, citing the separately built lemma, is accepted");
    assert_eq!(token.theory_id(), clean_kernel::TheoryId::LeanReferenceV1);
    // And the same file through `clean check`'s own verdict (exit 0).
    let main = consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    crate::cmd_core::check_file(&main, false, false, PreludeMode::Builtin)
        .expect("clean check of the citing file passes");
}

#[test]
fn k1_mutation_m3_is_refused_through_the_reference_entry_and_by_clean_check() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let false_type = payload(&donor).1.constants[0].type_.clone();
    let (_, mut tampered) = payload(&lib);
    zero_add(&mut tampered).type_ = false_type.clone();

    // The entry: the tampered lemma is refused by the kernel (its proof does
    // not prove the stated type), so nothing of it enters.
    let mut k = entry();
    match clean_olean::payload_entry::admit_payload(&mut k, &tampered) {
        // The kernel's type mismatch; the entry names it `TheoryExclusion`
        // when the term's δ-closure reaches a reducer Lean's profile excludes
        // (here `NotDifferentiallyChecked`). Either way it is a refusal.
        Err(clean_olean::payload_entry::PayloadAdmission::Refused {
            decl,
            refusal:
                clean_kernel::ReferenceRefusal::Kernel(_)
                | clean_kernel::ReferenceRefusal::TheoryExclusion(_),
        }) => assert_eq!(decl, Name::from_string("K1Lib.zero_add'")),
        other => panic!("M3: expected the kernel's refusal of K1Lib.zero_add', got {other:?}"),
    }
    let zero_add_name = Name::from_string("K1Lib.zero_add'");
    assert!(k.environment().get_const(&zero_add_name).is_none());
    // `k1_false`, elaborated where the tampered statement is believed, is
    // then refused through the entry: it cites a constant that never entered.
    let mut believer = clean_kernel::Environment::with_prelude();
    believer
        .add_decl(clean_kernel::Declaration::Axiom {
            name: zero_add_name.clone(),
            level_params: vec![],
            type_: false_type.clone(),
        })
        .expect("the tampered statement, believed");
    let k1_false = elab_theorem(&believer, strip_import(CITE_FALSE));
    // The refusal is the kernel's, for the one constant that never entered
    // (not some other error that happens to fire first).
    match k.add_checked(k1_false.clone()) {
        Err(clean_kernel::ReferenceRefusal::Kernel(e)) => assert!(
            e.to_string().contains("K1Lib.zero_add'"),
            "k1_false: the kernel's refusal names the missing lemma: {e}"
        ),
        other => panic!("k1_false : 0 = 1: expected the kernel's refusal, got {other:?}"),
    }
    // A payload that turned the lemma into an axiom at the false statement
    // is refused by the Ax0 rule.
    let mut as_axiom = tampered.clone();
    {
        let c = zero_add(&mut as_axiom);
        c.kind = clean_kernel::ConstantKind::Axiom;
        c.value = None;
    }
    let mut k2 = entry();
    match clean_olean::payload_entry::admit_payload(&mut k2, &as_axiom) {
        Err(clean_olean::payload_entry::PayloadAdmission::Refused {
            refusal: clean_kernel::ReferenceRefusal::OutsideAx0 { reached, .. },
            ..
        }) => assert_eq!(reached, zero_add_name),
        other => panic!("theorem turned axiom: expected OutsideAx0, got {other:?}"),
    }

    // `clean check` of the M3 file: the verdict is a failure (non-zero exit).
    let main = consumer(tmp.path(), "m3", &lib, CITE_FALSE, |p| {
        zero_add(p).type_ = false_type;
    });
    let verdict = crate::cmd_core::check_file(&main, false, false, PreludeMode::Builtin);
    assert!(verdict.is_err(), "M3 must exit non-zero: {verdict:?}");
}

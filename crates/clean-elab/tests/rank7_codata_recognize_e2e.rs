// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rank-7 B3: a REAL elaborated `codef` survives validated recognition.
//!
//! The must-refuse battery for `recognize_codata_corec` lives beside the
//! recognizer in clean-compiler and builds its environments by hand, because
//! the adversarial cases (a forged origin, a tampered corecursor, a valueless
//! constant wearing the right name) are exactly what the elaborator will not
//! produce.
//!
//! That battery has one blind spot, and this file exists to close it: its
//! positive case asserts the recognizer accepts an environment built from the
//! test's OWN assumptions about the generated shape. If those assumptions were
//! wrong — if the generator named its slots differently, say — the recognizer
//! would decline every genuine `codef` in the world and the battery would
//! still be green, because it would be wrong in exactly the same direction.
//!
//! So this test drives the real thing: elaborate a `codata`/`codef` pair
//! through the same path `clean check` uses, pull the generated definition's
//! stored value straight out of the environment, and require the recognizer to
//! accept it. A self-consistent battery plus one real specimen is the pair
//! that actually means something.

use clean_compiler::to_lcnf::codata_recognize::recognize_codata_corec;
use clean_elab::elaborate_decl_and_register;
use clean_kernel::{CodataLane, Environment, Name};
use clean_parser::parse_file;

fn elab(src: &str) -> Environment {
    let mut env = Environment::with_prelude();
    for (i, decl) in parse_file(src)
        .expect("fixture must parse")
        .iter()
        .enumerate()
    {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} must elaborate: {e:?}"));
    }
    env
}

const INDEXED: &str = r#"
codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)
"#;

const PLAIN: &str = r#"
codata St : Type where
  head : Nat
  tail : St

codef ones : St where
  head := 1
  tail := ones
"#;

/// The indexed lane: a real `codef` is recognized, and every re-derived fact
/// matches the declaration it came from.
#[test]
fn real_indexed_codef_is_recognized() {
    let env = elab(INDEXED);
    let name = Name::from_string("doubler");
    let value = env
        .get_const(&name)
        .and_then(|info| info.value.clone())
        .expect("`doubler` must be registered with a stored value");

    let got = recognize_codata_corec(&env, &name, &value)
        .expect("a genuinely elaborated indexed codef must be recognized");

    assert_eq!(got.carrier, Name::from_string("IS2"));
    assert_eq!(got.corec, Name::from_string("IS2.corec"));
    assert_eq!(
        got.lane,
        CodataLane::Indexed,
        "IS2 is declared with an index, so the lane must be re-derived as Indexed"
    );
    assert_eq!(
        got.slot_count, 2,
        "IS2 declares two fields (val, next), so the canonical body supplies \
         two slot lambdas; got slots={}",
        got.slot_count
    );
}

/// The plain (unindexed) lane, so the lane cross-check is exercised in both
/// directions rather than only on the shape the indexed fixture happens to have.
#[test]
fn real_plain_codef_is_recognized() {
    let env = elab(PLAIN);
    let name = Name::from_string("ones");
    let value = env
        .get_const(&name)
        .and_then(|info| info.value.clone())
        .expect("`ones` must be registered with a stored value");

    let got = recognize_codata_corec(&env, &name, &value)
        .expect("a genuinely elaborated plain codef must be recognized");

    assert_eq!(got.carrier, Name::from_string("St"));
    assert_eq!(got.lane, CodataLane::Plain);
    assert_eq!(got.slot_count, 2);
}

/// An ordinary definition in the SAME environment is refused.
///
/// This is the real-world form of the battery's central refusal: the
/// environment genuinely contains generated codata, so the recognizer cannot
/// pass by being uniformly permissive.
#[test]
fn an_ordinary_definition_alongside_codata_is_refused() {
    let env = elab(&format!(
        "{INDEXED}\ndef plainOldDef (x : Nat) : Nat := x\n"
    ));
    let name = Name::from_string("plainOldDef");
    let value = env
        .get_const(&name)
        .and_then(|info| info.value.clone())
        .expect("`plainOldDef` must be registered");

    assert!(
        recognize_codata_corec(&env, &name, &value).is_none(),
        "an ordinary definition must never be recognized as codata, even in an \
         environment that does contain generated codata"
    );
}

// ── the chain, end to end ──

/// A `codef` whose depth-k observations the KERNEL proves, lowered to
/// ExtractionIR and executed by the reference interpreter.
///
/// This is the first point where rank 7's stages 1-3 connect on a real
/// declaration: source elaborates → recognition validates → lowering produces
/// IR → the lazy interpreter runs it. The `rfl` theorems below are checked by
/// the real kernel during elaboration (`elab` panics if any fails), so the
/// expected values are not this test's opinion — they are the source's proved
/// behavior. The interpreter then has to reproduce them from the IR alone.
///
/// What this is: a DIFFERENTIAL at the depths run. What it is not: a proof
/// over all depths. That is B7, and it does not exist.
#[test]
fn the_chain_connects_source_to_interpreter() {
    const SRC: &str = r#"
codata St : Type where
  head : Nat
  tail : St

codef count (n : Nat) : St where
  head := n
  tail := count (Nat.succ n)

theorem c0 : St.head (count 5) = 5 := rfl
theorem c1 : St.head (St.tail (count 5)) = 6 := rfl
theorem c2 : St.head (St.tail (St.tail (count 5))) = 7 := rfl
"#;
    let env = elab(SRC);
    let name = Name::from_string("count");
    let value = env
        .get_const(&name)
        .and_then(|info| info.value.clone())
        .expect("`count` must be registered");

    // Stage 2: validated recognition.
    let rec =
        recognize_codata_corec(&env, &name, &value).expect("a real plain codef must be recognized");
    assert_eq!(rec.lane, CodataLane::Plain);
    assert_eq!(rec.param_count, 1, "`count` declares one parameter");

    // Stage 3: lowering into ExtractionIR.
    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec)
        .expect("the plain lane must lower");

    // Execute: the interpreter must reproduce the kernel-PROVED observations
    // (c0/c1/c2 above), parameterised by `n := 5`.
    for (k, want) in [(0u64, 5u64), (1, 6), (2, 7)] {
        let got = clean_compiler::extraction_ir::eval_nth(&ir, k, &[5]).expect("no black hole");
        assert_eq!(
            got, want,
            "depth {k}: interpreter disagrees with the kernel-proved value"
        );
    }

    // And it keeps counting past the proved depths.
    for k in 0..12u64 {
        assert_eq!(
            clean_compiler::extraction_ir::eval_nth(&ir, k, &[5]).expect("no black hole"),
            5 + k
        );
    }
}

/// The INDEXED width-1 target, end to end.
///
/// This is the declaration the ladder actually names for rank 7: an index that
/// MOVES (`next : IS2 (Nat.succ n)`), real state, first-order observation. The
/// fixture at tests/fixtures/codata/is2_indexed_stream.lean proves its depth-k
/// observations by rfl; those same values must come back out of the lazy
/// interpreter after recognition and lowering.
///
/// The index advance is the part that had to be read from the carrier's `tgtF`
/// descriptor rather than from the corecursor application, so it is checked
/// independently below.
#[test]
fn the_indexed_chain_connects_source_to_interpreter() {
    const SRC: &str = r#"
codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)

def IS2.nth : Nat → (n : Nat) → IS2 n → Nat :=
  Nat.rec (motive := fun _ => (n : Nat) → IS2 n → Nat)
    (fun n s => IS2.val s)
    (fun _ ih n s => ih (Nat.succ n) (IS2.next s))

theorem nth_d0 : IS2.nth 0 0 (doubler 0 1) = 1 := rfl
theorem nth_d1 : IS2.nth 1 0 (doubler 0 1) = 2 := rfl
theorem nth_d2 : IS2.nth 2 0 (doubler 0 1) = 4 := rfl
theorem nth_d3 : IS2.nth 3 0 (doubler 0 1) = 8 := rfl
"#;
    let env = elab(SRC);
    let name = Name::from_string("doubler");
    let value = env
        .get_const(&name)
        .and_then(|info| info.value.clone())
        .expect("`doubler` must be registered");

    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    assert_eq!(rec.lane, CodataLane::Indexed);
    assert_eq!(rec.param_count, 2, "`doubler` declares n and acc");

    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec)
        .expect("the indexed lane must lower");

    // params are (n := 0, acc := 1), matching `doubler 0 1` in the theorems.
    for (k, want) in [(0u64, 1u64), (1, 2), (2, 4), (3, 8)] {
        let got = clean_compiler::extraction_ir::eval_nth(&ir, k, &[0, 1]).expect("no black hole");
        assert_eq!(
            got, want,
            "depth {k}: interpreter disagrees with the kernel-proved value"
        );
    }
    // Past the proved depths, doubling continues.
    for k in 0..16u64 {
        assert_eq!(
            clean_compiler::extraction_ir::eval_nth(&ir, k, &[0, 1]).expect("no black hole"),
            1u64 << k
        );
    }
}

/// The index really advances, read out of `tgtF`.
///
/// Observing state slot 0 (the index) rather than the value tracks `n₀ + k`.
/// This is checked separately because the index step is the one piece that came
/// from a DIFFERENT constant than the corecursor application, so a lowering
/// that dropped it entirely would still pass the observation test above for a
/// stream whose value happens not to read the index.
#[test]
fn the_lowered_index_advances() {
    let env = elab(INDEXED);
    let name = Name::from_string("doubler");
    let value = env
        .get_const(&name)
        .and_then(|i| i.value.clone())
        .expect("registered");
    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    let mut ir =
        clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec).expect("lowers");
    // Re-point the observation at the index slot.
    ir.observe = clean_compiler::extraction_ir::Op::State(0);
    for k in 0..8u64 {
        assert_eq!(
            clean_compiler::extraction_ir::eval_nth(&ir, k, &[7, 1]).expect("no black hole"),
            7 + k,
            "the index must advance by one per layer"
        );
    }
}

// ── the seam: lowering output feeds emission input ──

/// Compile and run an emitted program, returning stdout lines.
fn compile_and_run(src: &str, stem: &str) -> Option<Vec<String>> {
    use std::process::Command;
    let dir = tempfile::tempdir().expect("tempdir");
    let src_path = dir.path().join(format!("{stem}.rs"));
    let bin_path = dir.path().join(stem);
    std::fs::write(&src_path, src).expect("write");
    let out = Command::new("rustc")
        .args(["--edition=2021", "-O", "-o"])
        .arg(&bin_path)
        .arg(&src_path)
        .output()
        .ok()?;
    assert!(
        out.status.success(),
        "emitted program must compile:\n{}\n--- src ---\n{src}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = Command::new(&bin_path).output().expect("run");
    assert!(
        run.status.success(),
        "emitted program must run cleanly:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    Some(
        String::from_utf8_lossy(&run.stdout)
            .lines()
            .map(str::to_string)
            .collect(),
    )
}

/// THE SEAM: the IR the LOWERING produced is the IR the EMITTER compiles.
///
/// This test exists because an adversarial review established that the
/// "end to end" claim was not mechanically backed. Every emitter test fed
/// `emit_program` a `Corec` written by hand in the test file, and
/// `lower_recognized`'s output was only ever handed to the interpreter. The
/// two halves of the chain were joined by the author retyping the IR.
///
/// The review's demonstration: replacing `lower_recognized`'s body with `None`
/// left every emitter test green, and deleting the emitter left every chain
/// test green. Neither half's failure was observable from the other, so
/// "source → recognition → IR → emitted Rust → binary stdout" described a path
/// no test walked.
///
/// Here the binary's stdout is produced from IR that came out of the lowering,
/// and compared against values the KERNEL proved about the source. Break any
/// stage — recognition, lowering, emission — and this goes red.
#[test]
fn the_lowered_ir_is_what_the_emitter_compiles() {
    const SRC: &str = r#"
codata St : Type where
  head : Nat
  tail : St

codef count (n : Nat) : St where
  head := n
  tail := count (Nat.succ n)

theorem k0 : St.head (count 5) = 5 := rfl
theorem k1 : St.head (St.tail (count 5)) = 6 := rfl
theorem k2 : St.head (St.tail (St.tail (count 5))) = 7 := rfl
"#;
    let env = elab(SRC);
    let name = Name::from_string("count");
    let value = env
        .get_const(&name)
        .and_then(|i| i.value.clone())
        .expect("registered");

    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec).expect("lowers");

    // The emitted source is generated FROM the lowered IR -- not from a
    // hand-written copy of it.
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&ir, &[5], 8);
    let Some(lines) = compile_and_run(&src, "seam_count") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };

    // Kernel-proved prefix (k0/k1/k2 above), then the continuation.
    assert_eq!(&lines[0..3], &["5", "6", "7"]);
    for (k, line) in lines.iter().enumerate() {
        assert_eq!(line.parse::<u64>().expect("numeric"), 5 + k as u64);
    }
}

/// The same seam for the INDEXED lane, whose index step comes from `tgtF`.
///
/// Pinned separately because the index step is read from a different constant
/// than everything else, and because the observation here never reads the
/// index — so an index dropped entirely would be invisible without this.
#[test]
fn the_lowered_indexed_ir_is_what_the_emitter_compiles() {
    let env = elab(INDEXED);
    let name = Name::from_string("doubler");
    let value = env
        .get_const(&name)
        .and_then(|i| i.value.clone())
        .expect("registered");
    let rec = recognize_codata_corec(&env, &name, &value).expect("recognized");
    let ir = clean_compiler::extraction_ir::lower::lower_recognized(&env, &rec).expect("lowers");

    // Observation: the kernel-proved doubling, from lowered IR.
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&ir, &[0, 1], 8);
    let Some(lines) = compile_and_run(&src, "seam_doubler") else {
        eprintln!("rustc unavailable — skipping execution check");
        return;
    };
    assert_eq!(&lines[0..4], &["1", "2", "4", "8"]);

    // Index: re-point the observation at the index slot, so a dropped or
    // mis-wired index step cannot hide behind an observation that ignores it.
    let mut idx_ir = ir;
    idx_ir.observe = clean_compiler::extraction_ir::Op::State(0);
    let src = clean_compiler::extraction_ir::emit_rust::emit_program(&idx_ir, &[7, 1], 6);
    let Some(lines) = compile_and_run(&src, "seam_index") else {
        return;
    };
    assert_eq!(lines, vec!["7", "8", "9", "10", "11", "12"]);
}

/// A hand-written carrier that impersonates codata is REFUSED.
///
/// This is the adversarial review's finding 6, reproduced verbatim, and it is
/// not hypothetical: every declaration below elaborates, `codef bad` is
/// accepted, and it MINTS a real CodataOrigin `(Plain, "Evil", [valF, nextF])`.
/// Before carrier provenance the recognizer then accepted it — measured, by
/// removing the gate: `RECOGNIZED bad: true`.
///
/// The hole was that `codef` required only that the carrier own a `<C>.corec`
/// with the right recorded parameter names; it never required the `codata`
/// command to have run. B3b's canonical-body replay did not close it either,
/// because the replay checks the head constant's name and that the descriptors
/// are mentioned — all hand-suppliable, as this source does.
///
/// That made recognition breakable from SOURCE, which is exactly the rule the
/// module exists to enforce: `C.corec` is a user-derivable name.
#[test]
fn a_handwritten_carrier_impersonating_codata_is_refused() {
    const EVIL: &str = r#"
def Evil : Type := Nat
def Evil.shapeF : Nat := 0
def Evil.posF : Nat := 0
def Evil.tgtF : Nat := 0
def Codata.ucorec (a b c : Nat) : Nat := a
def Evil.corec {S : Type} (valF : S → Nat) (nextF : S → S) (s : S) : Evil :=
  Codata.ucorec Evil.shapeF Evil.posF Evil.tgtF

codef bad (s : Nat) : Evil where
  val := s
  next := bad (Nat.succ s)
"#;
    let env = elab(EVIL);

    // The impersonation really does get this far: `bad` registers and carries
    // an origin. If either of these ever stops holding, this test has stopped
    // testing what it claims and the assertions below become vacuous.
    let value = env
        .get_const(&Name::from_string("bad"))
        .and_then(|i| i.value.clone())
        .expect("the impersonation elaborates — otherwise this test is vacuous");
    assert!(
        env.get_codata_origin(&Name::from_string("bad")).is_some(),
        "the impersonation mints an origin — otherwise this test is vacuous"
    );

    // And is refused anyway, because `Evil` was never generated by `codata`.
    assert!(
        !env.is_codata_carrier(&Name::from_string("Evil")),
        "`Evil` was never produced by the codata command"
    );
    assert!(
        recognize_codata_corec(&env, &Name::from_string("bad"), &value).is_none(),
        "a hand-written carrier must never be recognized as generated codata"
    );
}

/// The provenance mark is actually SET for real codata — otherwise the gate
/// above would be closing by rejecting everything.
#[test]
fn the_codata_command_marks_its_carrier() {
    let env = elab(INDEXED);
    assert!(
        env.is_codata_carrier(&Name::from_string("IS2")),
        "the codata command must mark the carriers it generates"
    );
    assert!(
        !env.is_codata_carrier(&Name::from_string("Nat")),
        "an ordinary prelude type must not be marked"
    );
}

// ── B7: the observational soundness artifact ──

/// The observational theorem holds, with an EMPTY axiom closure.
///
/// This is rank 7's actual claim, at width 1:
///
/// ```text
/// ∀ k n acc, IS2.nth k n (doubler n acc) = IRCorec.nthFrom doublerIR k n acc
/// ```
///
/// — for EVERY finite depth, observing the source k layers equals decoding k
/// forced target layers. Not a differential at sampled depths; a statement
/// about all of them, proved by induction with each step discharged by a
/// definitional lemma.
///
/// The axiom-closure assertion is the part that makes "proved" sayable under
/// this project's rules: a theorem whose closure escaped the foundational set
/// would be a formalization, not a proof.
#[test]
fn b7_observational_soundness_is_proved_with_empty_axiom_closure() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/is2_extraction_soundness.lean");
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("B7 fixture must exist at {}: {e}", path.display()));
    let env = elab(&src);

    let thm = Name::from_string("doubler_extraction_observationally_correct");
    assert!(
        env.get_const(&thm).is_some(),
        "the observational theorem must be registered"
    );
    let deps = env
        .axiom_deps(&thm)
        .unwrap_or_else(|| panic!("{thm} must be registered"));
    assert!(
        deps.is_empty(),
        "the observational theorem must have an EMPTY axiom closure — \
         anything else means this is a formalization, not a proof; got {deps:?}"
    );
}

/// The observational theorem is NOT vacuous: a wrong emitted term breaks it.
///
/// A theorem relating source to target is worthless if it holds regardless of
/// what the target actually is — and this rung is unusually exposed to that,
/// because `iM_bisim_of_eq` already makes tower agreement BE equality in this
/// model, so a carelessly stated version collapses to reflexivity.
///
/// The negative-control fixture is byte-identical except that the emitted step
/// is `succ acc` where the source doubles. It MUST fail to check. If it ever
/// starts passing, the positive theorem has stopped saying anything about the
/// term it names.
#[test]
fn b7_soundness_theorem_is_not_vacuous() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/is2_extraction_soundness_MUST_FAIL.lean");
    let src = std::fs::read_to_string(&path).expect("negative control must exist");

    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("the mutant must still PARSE");
    let mut failed = false;
    for d in &decls {
        if elaborate_decl_and_register(&mut env, d).is_err() {
            failed = true;
        }
    }
    assert!(
        failed,
        "the observational theorem must NOT hold for a wrong emitted term — \
         if this passes, the theorem is vacuous"
    );
}

/// WIDTH: the same certificate for a structurally different chain.
///
/// `count` is unindexed with a single state slot, where `doubler` is indexed
/// with two — so this exercises the IR model and the induction pattern on a
/// shape the first chain did not. The ladder's doctrine is one complete
/// width-one chain first, then width; this is the second chain.
///
/// Same two gates as the first: an EMPTY axiom closure (so "proved" is
/// sayable), and a negative control that must fail.
#[test]
fn b7_plain_lane_soundness_is_proved_with_empty_axiom_closure() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/st_extraction_soundness.lean");
    let src = std::fs::read_to_string(&path).expect("plain-lane B7 fixture must exist");
    let env = elab(&src);

    let thm = Name::from_string("count_extraction_observationally_correct");
    let deps = env
        .axiom_deps(&thm)
        .unwrap_or_else(|| panic!("{thm} must be registered"));
    assert!(
        deps.is_empty(),
        "the plain-lane observational theorem must have an EMPTY axiom \
         closure; got {deps:?}"
    );
}

/// The plain-lane theorem is not vacuous either.
///
/// The control doubles where the source increments. It must fail to check.
#[test]
fn b7_plain_lane_theorem_is_not_vacuous() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/st_extraction_soundness_MUST_FAIL.lean");
    let src = std::fs::read_to_string(&path).expect("negative control must exist");
    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("the mutant must still PARSE");
    let mut failed = false;
    for d in &decls {
        if elaborate_decl_and_register(&mut env, d).is_err() {
            failed = true;
        }
    }
    assert!(
        failed,
        "a wrong emitted term must break the plain-lane theorem — \
         if this passes, the theorem is vacuous"
    );
}

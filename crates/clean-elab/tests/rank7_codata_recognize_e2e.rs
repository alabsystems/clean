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

// Keep the independently proved B7 observational artifacts in a focused child
// module so this end-to-end integration test remains below the 500-line quality
// boundary without weakening any test or assertion.
#[path = "rank7_codata_recognize_e2e/b7.rs"]
mod b7;

// The lowering-to-emission seam, moved out for the same reason.
#[path = "rank7_codata_recognize_e2e/seam.rs"]
mod seam;

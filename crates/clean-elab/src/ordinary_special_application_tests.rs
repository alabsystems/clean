// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual Lean30/35 source controls for application shortcuts. Empty-recursion
//! positives use the observed noncomputable form to test kernel elaboration;
//! their original code generator refusals remain in the observation report.

use super::{assert_all_ok, elab_file_prelude};
use clean_kernel::Name;

#[test]
fn special_applications_preserve_declared_argument_slots() {
    let mut mismatches = Vec::new();
    for (label, setup_names, source) in [
        ("do-pure-at-invalid", &[][..], "def probe : Option Nat := do\n  @pure 1\n"),
        ("do-pure-named-invalid", &[][..], "def probe : Option Nat := do\n  pure (missing := 1)\n"),
        ("empty-motive-EmptyArg-casesOn-major-only", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.casesOn x\n"),
        ("empty-motive-EmptyArg-rec-major-only", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.rec x\n"),
        ("empty-motive-EmptyArg-recOn-major-only", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.recOn x\n"),
        ("empty-motive-EmptyPropArg-casesOn-major-only", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.casesOn x\n"),
        ("empty-motive-EmptyPropArg-rec-major-only", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.rec x\n"),
        ("empty-motive-EmptyPropArg-recOn-major-only", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.recOn x\n"),
        ("eq-at-literal-left", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Eq { x := 1 } p\n"),
        ("eq-at-literal-right", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Eq p { x := 1 }\n"),
        ("ne-at-literal-left", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Ne { x := 1 } p\n"),
        ("ne-at-literal-right", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Ne p { x := 1 }\n"),
        ("aux-EmptyParamArg-rec-major-only", &["EmptyParamArg"][..], "inductive EmptyParamArg (α : Type) : Type\nnoncomputable def probe (x : EmptyParamArg Nat) : Nat := EmptyParamArg.rec x\n"),
        ("aux-EmptyParamPropArg-rec-major-only", &["EmptyParamPropArg"][..], "inductive EmptyParamPropArg (α : Type) : Prop\nnoncomputable def probe (x : EmptyParamPropArg Nat) : Nat := EmptyParamPropArg.rec x\n"),
        ("dot-EmptyArg-casesOn-invalid-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.casesOn 1\n"),
        ("dot-EmptyArg-rec-invalid-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.rec 1\n"),
        ("dot-EmptyArg-recOn-invalid-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.recOn 1\n"),
        ("dot-EmptyPropArg-casesOn-invalid-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.casesOn 1\n"),
        ("dot-EmptyPropArg-rec-invalid-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.rec 1\n"),
        ("dot-EmptyPropArg-recOn-invalid-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.recOn 1\n"),
        ("casesOn-composite-dependent-negative", &[][..], "def probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.casesOn (Bool.not b) x x\n"),
        ("composite-dependent-rec-negative", &[][..], "def probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.rec x x (Bool.not b)\n"),
        ("composite-dependent-recOn-negative", &[][..], "def probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.recOn (Bool.not b) x x\n"),
        ("defeq-composite-major-negative", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.casesOn (Bool.not (reviewId b)) x x\n"),
        ("tail-at-invalid", &["namedTail"][..], "def namedTail (n : Nat) : {α : Type} → α → α := fun {α} x => x\ndef probe : Nat := @namedTail (n := 1) 2\n"),
    ] {
        let (env, results) = elab_file_prelude(source);
        assert_eq!(results.len(), setup_names.len() + 1, "{label}: exact parse count");
        assert_all_ok(&results[..results.len() - 1], label);
        for &name in setup_names {
            assert!(env.get_const(&Name::from_string(name)).is_some(), "{label}: setup `{name}`");
        }
        if !results.last().is_some_and(Result::is_err)
            || env.get_const(&Name::from_string("probe")).is_some()
        {
            mismatches.push(format!("{label}: expected refusal and absent probe, got {results:?}"));
        }
    }
    assert!(
        mismatches.is_empty(),
        "actual Lean refusals: {mismatches:#?}"
    );
}

#[test]
fn special_applications_preserve_explicit_hole_and_dot_consumers() {
    let mut mismatches = Vec::new();
    for (label, setup_names, source) in [
        ("do-pure-at-proper", &[][..], "def probe : Option Nat := do\n  @pure Option _ Nat 1\n"),
        ("do-pure-ordinary", &[][..], "def probe : Option Nat := do\n  pure 1\n"),
        ("empty-motive-EmptyArg-rec-at", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := @EmptyArg.rec (fun _ => Nat) x\n"),
        ("empty-motive-EmptyArg-rec-motive-explicit", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.rec (fun _ => Nat) x\n"),
        ("empty-motive-EmptyArg-rec-motive-hole", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.rec _ x\n"),
        ("empty-motive-EmptyPropArg-rec-at", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := @EmptyPropArg.rec (fun _ => Nat) x\n"),
        ("empty-motive-EmptyPropArg-rec-motive-explicit", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.rec (fun _ => Nat) x\n"),
        ("empty-motive-EmptyPropArg-rec-motive-hole", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.rec _ x\n"),
        ("eq-at-proper", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Eq EqPoint { x := 1 } p\n"),
        ("eq-ordinary", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := Eq { x := 1 } p\n"),
        ("inherited-parent-qualified-positive", &["Parent", "Child"][..], "class Parent (α : Type) where\n  count : Nat\nclass Child (α : Type) extends Parent α where\n  flag : Bool\ndef probe [Child Nat] : Nat := Parent.count Nat\n"),
        ("ne-at-proper", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := @Ne EqPoint { x := 1 } p\n"),
        ("ne-ordinary", &["EqPoint"][..], "structure EqPoint where\n  x : Nat\ndef probe (p : EqPoint) : Prop := Ne { x := 1 } p\n"),
        ("aux-EmptyArg-casesOn-hole", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.casesOn _ x\n"),
        ("aux-EmptyArg-recOn-hole", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := EmptyArg.recOn _ x\n"),
        ("aux-EmptyParamArg-rec-hole", &["EmptyParamArg"][..], "inductive EmptyParamArg (α : Type) : Type\nnoncomputable def probe (x : EmptyParamArg Nat) : Nat := EmptyParamArg.rec _ x\n"),
        ("aux-EmptyParamPropArg-rec-hole", &["EmptyParamPropArg"][..], "inductive EmptyParamPropArg (α : Type) : Prop\nnoncomputable def probe (x : EmptyParamPropArg Nat) : Nat := EmptyParamPropArg.rec _ x\n"),
        ("aux-EmptyPropArg-casesOn-hole", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.casesOn _ x\n"),
        ("aux-EmptyPropArg-recOn-hole", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := EmptyPropArg.recOn _ x\n"),
        ("dot-EmptyArg-casesOn-function-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.casesOn (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyArg-casesOn-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.casesOn (fun _ => Nat)\n"),
        ("dot-EmptyArg-rec-function-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.rec (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyArg-rec-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.rec (fun _ => Nat)\n"),
        ("dot-EmptyArg-recOn-function-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.recOn (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyArg-recOn-motive", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.recOn (fun _ => Nat)\n"),
        ("dot-EmptyPropArg-casesOn-function-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.casesOn (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyPropArg-casesOn-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.casesOn (fun _ => Nat)\n"),
        ("dot-EmptyPropArg-rec-function-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.rec (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyPropArg-rec-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.rec (fun _ => Nat)\n"),
        ("dot-EmptyPropArg-recOn-function-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.recOn (fun _ => Nat → Nat) 1\n"),
        ("dot-EmptyPropArg-recOn-motive", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.recOn (fun _ => Nat)\n"),
        ("empty-motive-EmptyArg-rec-dot", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.rec\n"),
        ("empty-motive-EmptyPropArg-rec-dot", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.rec\n"),
        ("aux-EmptyArg-casesOn-dot", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.casesOn\n"),
        ("aux-EmptyArg-recOn-dot", &["EmptyArg"][..], "inductive EmptyArg : Type\nnoncomputable def probe (x : EmptyArg) : Nat := x.recOn\n"),
        ("aux-EmptyParamArg-rec-dot", &["EmptyParamArg"][..], "inductive EmptyParamArg (α : Type) : Type\nnoncomputable def probe (x : EmptyParamArg Nat) : Nat := x.rec\n"),
        ("aux-EmptyParamPropArg-rec-dot", &["EmptyParamPropArg"][..], "inductive EmptyParamPropArg (α : Type) : Prop\nnoncomputable def probe (x : EmptyParamPropArg Nat) : Nat := x.rec\n"),
        ("aux-EmptyPropArg-casesOn-dot", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.casesOn\n"),
        ("aux-EmptyPropArg-recOn-dot", &["EmptyPropArg"][..], "inductive EmptyPropArg : Prop\nnoncomputable def probe (x : EmptyPropArg) : Nat := x.recOn\n"),
        ("casesOn-struct-major", &["ReviewPoint"][..], "structure ReviewPoint where\n  n : Nat\n\ndef probe : Nat := ReviewPoint.casesOn { n := 1 } (fun n => n)\n"),
        ("casesOn-struct-major-typed-control", &["ReviewPoint"][..], "structure ReviewPoint where\n  n : Nat\n\ndef probe : Nat := ReviewPoint.casesOn ({ n := 1 } : ReviewPoint) (fun n => n)\n"),
        ("casesOn-if-major", &[][..], "def probe : Bool := Nat.casesOn (if true then 0 else 1) true (fun _ => false)\n"),
        ("casesOn-composite-dependent-explicit-control", &[][..], "def probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.casesOn (motive := fun _ => P (Bool.not b)) (Bool.not b) x x\n"),
        ("composite-dependent-positive", &[][..], "def probe (P : Bool → Type) (b : Bool) (x : P false) (y : P true) : P (Bool.not b) :=\n  Bool.casesOn (Bool.not b) x y\n"),
        ("defeq-all-occurrences-positive", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Bool → Type) (b : Bool)\n    (xf : P false false) (xt : P true true) :\n    P (Bool.not b) (Bool.not (reviewId b)) :=\n  Bool.casesOn (Bool.not (reviewId b)) xf xt\n"),
        ("defeq-binder-depth-positive", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Nat → Type) (b : Bool)\n    (xf : (n : Nat) → P false n) (xt : (n : Nat) → P true n) :\n    (n : Nat) → P (Bool.not b) n :=\n  Bool.casesOn (Bool.not (reviewId b)) xf xt\n"),
        ("defeq-composite-major-explicit-control", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Type) (b : Bool) (x : P (Bool.not b)) : P (Bool.not b) :=\n  Bool.casesOn (motive := fun _ => P (Bool.not b)) (Bool.not (reviewId b)) x x\n"),
        ("defeq-composite-major-positive", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Type) (b : Bool) (xf : P false) (xt : P true) : P (Bool.not b) :=\n  Bool.casesOn (Bool.not (reviewId b)) xf xt\n"),
        ("defeq-let-head-positive", &["reviewId"][..], "def reviewId (b : Bool) : Bool := b\n\ndef probe (P : Bool → Type) (b : Bool) (xf : P false) (xt : P true) : P (Bool.not b) :=\n  Bool.casesOn (let f : Bool → Bool := Bool.not; f (reviewId b)) xf xt\n"),
        ("tail-at-proper", &["namedTail"][..], "def namedTail (n : Nat) : {α : Type} → α → α := fun {α} x => x\ndef probe : Nat := @namedTail (n := 1) Nat 2\n"),
        ("tail-ordinary", &["namedTail"][..], "def namedTail (n : Nat) : {α : Type} → α → α := fun {α} x => x\ndef probe : Nat := namedTail (n := 1) 2\n"),
        ("tail-strict-ordinary", &["namedTail"][..], "def namedTail (n : Nat) : ⦃α : Type⦄ → α → α := fun ⦃α⦄ x => x\ndef probe : Nat := namedTail (n := 1) 2\n"),
        ("tail-strict-partial", &["namedTail"][..], "def namedTail (n : Nat) : ⦃α : Type⦄ → α → α := fun ⦃α⦄ x => x\ndef probe : ⦃α : Type⦄ → α → α := namedTail (n := 1)\n"),
    ] {
        let (env, results) = elab_file_prelude(source);
        assert_eq!(results.len(), setup_names.len() + 1, "{label}: exact parse count");
        assert_all_ok(&results[..results.len() - 1], label);
        for &name in setup_names {
            assert!(env.get_const(&Name::from_string(name)).is_some(), "{label}: setup `{name}`");
        }
        let probe = Name::from_string("probe");
        if env.get_const(&probe).is_none() {
            mismatches.push(format!("{label}: expected checked probe, got {results:?}"));
            continue;
        }
        assert_all_ok(&results, label);
        assert!(env.axiom_deps(&probe).expect("checked probe axiom closure").is_empty(), "{label}");
        assert!(env.trust_marker_deps(&probe).expect("checked probe trust closure").is_empty(), "{label}");
    }
    assert!(
        mismatches.is_empty(),
        "actual Lean positive consumers: {mismatches:#?}"
    );
}

/// Pinned Lean 4.30.0-rc2 and 4.35.0 accept the source below (exit 0 in
/// `reports/implicit-positional-arguments-2026-11-06/special-application-oracles/results.json`).
/// Clean refuses it today, so it is pinned as a refusal that names the
/// current cause. Once it elaborates this fails, and it belongs back in
/// `special_applications_preserve_explicit_hole_and_dot_consumers`, where the
/// eight bare `x.rec` / `x.casesOn` / `x.recOn` definition bodies of the same
/// oracle run went once `elab_def_body` handed the declared result to
/// `elab_dot_elim.rs` (FRONTEND_CLASS_LEDGER class 112).
///
/// * `c.count` through a class parent whose parameter is explicit in the
///   projection (`Parent.count : (α : Type) → [Parent α] → Nat`): Lean's
///   `anyNamedArgDependsOnCurrent` turns that explicit `α` into a hole once
///   the receiver is passed as the named `self`. Main's application does not,
///   so it leaves `Type → Nat`.
#[test]
fn special_application_known_gaps_stay_refused_by_name() {
    for (label, setup_names, source) in [
        ("inherited-dot-positive", &["Parent", "Child"][..], "class Parent (α : Type) where\n  count : Nat\nclass Child (α : Type) extends Parent α where\n  flag : Bool\ndef probe (c : Child Nat) : Nat := c.count\n"),
    ] {
        let (env, results) = elab_file_prelude(source);
        assert_eq!(results.len(), setup_names.len() + 1, "{label}: exact parse count");
        assert_all_ok(&results[..results.len() - 1], label);
        for &name in setup_names {
            assert!(env.get_const(&Name::from_string(name)).is_some(), "{label}: setup `{name}`");
        }
        let error = match results.last() {
            Some(Err(error)) => format!("{error:?}"),
            other => panic!("{label}: the known gap closed, move it to the positives: {other:?}"),
        };
        let cause = "actual: \"Type -> Nat\"";
        assert!(error.contains(cause), "{label}: {error}");
        assert!(env.get_const(&Name::from_string("probe")).is_none(), "{label}");
    }
}

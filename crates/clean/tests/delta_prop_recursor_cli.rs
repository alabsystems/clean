// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` on a family that is a `Prop` only up to whnf
//! (`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`, item
//! `kernel-result-sort-whnf-elim`, P0).
//!
//! ```lean
//! def MyProp : Type := Prop
//! inductive B : MyProp | t | f
//! def toBool (b : B) : Bool := B.rec (motive := fun _ => Bool) true false b
//! theorem tf : B.t = B.f := rfl
//! theorem bad : False := Bool.noConfusion (congrArg toBool tf)
//! ```
//!
//! Measured 2026-10-16 with the integration base's release binary (`clean
//! check`, d693e7d88): "5 passed, 0 failed", `sorry_axioms 0` — Clean PROVED
//! `False`. The kernel read `B`'s syntactic head `MyProp`, not its result level
//! up to whnf, and granted `B.rec` a motive universe; proof irrelevance, which
//! does whnf, made `B.t ≡ B.f`.
//!
//! Pinned Lean (4.8.0 and v4.30.0-rc2, run on these exact files) refuses every
//! negative here at `toBool`: `B.rec`'s motive is `B → Prop`, so `fun _ =>
//! Bool` is a type mismatch, and `@B.rec.{1}` has "too many explicit universe
//! levels". That is the reason Clean must refuse for. `tf` holds in both
//! (proof irrelevance; Lean reports no error on it). Lean's `inductive`
//! command also reports an error on `B` itself, in its auxiliary
//! constructions (`B.casesOn` universe count in 4.8.0, `B.ctorIdx` in
//! v4.30.0-rc2), after its kernel ADMITTED the block with a `Prop`-only
//! `B.rec`; Clean admits the same block and its kernel generates the same
//! `B.rec` (`docs/DECISIONS.md` R37).
//!
//! Positive controls Lean accepts with exit 0: an ordinary `inductive C :
//! Prop` eliminated into `Prop`, and a δ-`Type` family
//! (`def MyType : Type 1 := Type; inductive D : MyType`) eliminated into
//! `Bool`.

#![cfg(unix)]

use std::path::PathBuf;
use std::process::Command;

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `clean check <file>`: (exit status success, combined stdout + stderr).
fn check(name: &str, source: &str) -> (bool, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join(name);
    std::fs::write(&file, source).expect("write the program");
    let output = Command::new(clean_path())
        .arg("check")
        .arg(&file)
        .output()
        .expect("spawn `clean check`");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), text)
}

/// The error line `clean check` prints for declaration `decl`, if any.
fn error_for<'a>(text: &'a str, decl: &str) -> Option<&'a str> {
    let prefix = format!("✗ {decl}: ");
    text.lines()
        .map(str::trim_start)
        .find(|line| line.starts_with(&prefix))
}

const DELTA_PROP: &str = "\
def MyProp : Type := Prop

inductive B : MyProp
  | t
  | f

def toBool (b : B) : Bool := B.rec (motive := fun _ => Bool) true false b

theorem tf : B.t = B.f := rfl

theorem bad : False := Bool.noConfusion (congrArg toBool tf)

#print axioms bad
";

/// [`DELTA_PROP`] with `B` an ordinary `Prop` family (`inductive B : Prop`),
/// every line where it was. Pinned Lean refuses `toBool` here exactly as it
/// does in `DELTA_PROP` (`Bool : Type` where `Prop` is expected).
fn delta_prop_twin() -> String {
    DELTA_PROP.replace("inductive B : MyProp", "inductive B : Prop")
}

const DELTA_PROP_NOMATCH: &str = "\
def MyProp : Type := Prop
inductive B : MyProp
  | t
  | f
theorem tf : B.t = B.f := rfl
theorem bad : False := nomatch (congrArg (fun b => B.rec (motive := fun _ => Bool) true false b) tf : true = false)
";

const DELTA_PROP_EXPLICIT_LEVEL: &str = "\
def MyProp : Type := Prop

inductive B : MyProp
  | t
  | f

def toBool (b : B) : Bool := @B.rec.{1} (fun _ => Bool) true false b

theorem tf : B.t = B.f := rfl

theorem bad : False := Bool.noConfusion (congrArg toBool tf)
";

const PROP_CONTROL: &str = "\
inductive C : Prop
  | a
  | b

theorem c_elim (c : C) : True := C.rec (motive := fun _ => True) True.intro True.intro c

theorem c_irrel : C.a = C.b := rfl
";

const DELTA_TYPE_CONTROL: &str = "\
def MyType : Type 1 := Type

inductive D : MyType
  | a
  | b

noncomputable def toBoolD (d : D) : Bool := D.rec (motive := fun _ => Bool) true false d

example : toBoolD D.a = true := rfl
example : D.a ≠ D.b := fun h => Bool.noConfusion (congrArg toBoolD h)

#check @D.rec
#check @D.noConfusion
";

/// The family is admitted, `B.t = B.f` holds by proof irrelevance, and the
/// elimination into `Bool` is refused, so `bad` never checks.
fn assert_refused_at_the_recursor(text: &str, to_bool_needles: &[&str]) {
    for admitted in ["MyProp", "B", "tf"] {
        assert!(
            error_for(text, admitted).is_none(),
            "`{admitted}` must be admitted, as Lean's kernel admits it:\n{text}"
        );
    }
    let to_bool = error_for(text, "toBool")
        .unwrap_or_else(|| panic!("`toBool` must be refused (B.rec is Prop-only):\n{text}"));
    for needle in to_bool_needles {
        assert!(
            to_bool.contains(needle),
            "`toBool` refused without `{needle}`: {to_bool}\n{text}"
        );
    }
    assert!(
        error_for(text, "bad").is_some(),
        "`bad : False` must not check:\n{text}"
    );
}

/// The refusal is the one an ordinary `Prop` family gets: `clean check`'s
/// report on `toBool` is byte-identical to its report on the twin where `B`
/// is declared `: Prop` outright (measured 2026-10-16: "Type mismatch: …
/// cannot unify a function type with an application: … -> Type vs … B.t", the
/// motive `fun _ => Bool` against `B → Prop`). Before the fix `toBool`, `tf`
/// and `bad` all checked.
#[test]
fn delta_prop_false_derivation_is_refused_at_the_recursor() {
    let (ok, text) = check("DeltaProp.lean", DELTA_PROP);
    assert!(!ok, "clean check must fail:\n{text}");
    assert_refused_at_the_recursor(&text, &["B.t", "-> Type"]);
    let (twin_ok, twin) = check("DeltaPropTwin.lean", &delta_prop_twin());
    assert!(!twin_ok, "the ordinary Prop twin must fail too:\n{twin}");
    assert_eq!(
        error_for(&text, "toBool"),
        error_for(&twin, "toBool"),
        "a δ-Prop family's recursor must refuse exactly as a Prop family's does"
    );
}

#[test]
fn delta_prop_explicit_universe_is_refused_as_too_many_levels() {
    let (ok, text) = check("DeltaProp3.lean", DELTA_PROP_EXPLICIT_LEVEL);
    assert!(!ok, "clean check must fail:\n{text}");
    assert_refused_at_the_recursor(
        &text,
        &["Universe level count mismatch for B.rec: expected 0, got 1"],
    );
}

#[test]
fn delta_prop_nomatch_variant_is_refused() {
    let (ok, text) = check("DeltaProp2.lean", DELTA_PROP_NOMATCH);
    assert!(!ok, "clean check must fail:\n{text}");
    for admitted in ["MyProp", "B", "tf"] {
        assert!(
            error_for(&text, admitted).is_none(),
            "`{admitted}`:\n{text}"
        );
    }
    assert!(error_for(&text, "bad").is_some(), "`bad : False`:\n{text}");
}

#[test]
fn prop_and_delta_type_controls_check_as_in_lean() {
    for (name, source) in [
        ("PropControl.lean", PROP_CONTROL),
        ("DeltaTypeControl.lean", DELTA_TYPE_CONTROL),
    ] {
        let (ok, text) = check(name, source);
        assert!(ok, "{name}: pinned Lean accepts it (exit 0):\n{text}");
    }
}

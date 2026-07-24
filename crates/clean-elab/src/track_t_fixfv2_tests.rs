// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track T (FIX-FV Part 2) regressions: the CONSTRUCTION / pattern direction
//! of nested-inductive aux mirrors, driven through `clean check`.
//!
//! A nested inductive `Value` with a `List Value` field is lowered to a mutual
//! block `Value` + an auxiliary mirror `Value._List`; the field is stored at
//! type `Value._List`. Part 1 fixed the READ direction (`Value._List ->
//! List Value` via `toContainer` in dot-notation). This track fixes the
//! PATTERN direction: a sub-pattern like `| .aggregate [] =>` or
//! `| .aggregate (x :: xs) =>` binds the field at `Value._List`, so the inner
//! `List.nil` / `List.cons` constructor must be remapped onto the mirrored aux
//! constructor (`Value._List.nil` / `Value._List.cons`), and the nested
//! `casesOn` must supply motives/minors POSITIONALLY over the whole mutual
//! block (not assuming the field is the primary member).
//!
//! Soundness bar (mirrors `track_r_basic_tests`): every synthesized definition
//! must `infer_type` against its declared type AND have an EMPTY axiom closure
//! — no `sorry`, no faked axiom. A do-block match with a nested aux sub-pattern
//! must NOT inject a synthetic `sorry` into the dead aux-minor / inner-fallback
//! branches: the do-match's trailing `| _ => …` catch-all is threaded as the
//! real fallback.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code` into a fresh prelude env,
/// asserting each elaborates without error (mirrors the `clean check` path).
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!(
                "decl {i} fell through to RawDecl (parser error recovery): content={content:?}, span={span:?}"
            );
        }
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// Assert a constant is registered, its value kernel-checks (`infer_type`
/// succeeds and is def-eq to the declared type), and its axiom closure contains
/// NO `sorry`/synthetic axiom — proving the lowered nested `casesOn` is
/// genuinely sound. Pure (non-monadic) definitions must have an EMPTY closure;
/// monadic definitions legitimately depend on prelude monad axioms (`Except`,
/// `Bind.bind`, …) since clean's builtin prelude registers them as axioms — the
/// soundness invariant for THIS track is the absence of any `sorry`, never the
/// absence of those prelude primitives.
fn assert_no_sorry_const(env: &Environment, name: &str, allow_prelude_axioms: bool) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));

    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );

    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();

    // No `sorry`/synthetic-sorry under any name, ever.
    let has_sorry = dep_names
        .iter()
        .any(|d| d.contains("sorry") || d.contains("sorryAx"));
    assert!(
        !has_sorry,
        "{name} must NOT depend on any `sorry` axiom, got {dep_names:?}"
    );

    if !allow_prelude_axioms {
        assert!(
            dep_names.is_empty(),
            "{name} must have an EMPTY axiom closure (pure def), got {dep_names:?}"
        );
    }
}

/// Pure (non-monadic) definition: empty axiom closure required.
fn assert_sound_const(env: &Environment, name: &str) {
    assert_no_sorry_const(env, name, false);
}

/// Monadic definition: prelude monad axioms allowed, but never a `sorry`.
fn assert_no_sorry_monadic(env: &Environment, name: &str) {
    assert_no_sorry_const(env, name, true);
}

/// The minimal `Value` mutual-block prelude shared by the tests: a nested
/// inductive with a `List Value` field, lowering to `Value` + `Value._List`.
const VALUE_PRELUDE: &str = r#"
inductive Value where
  | int    : Nat -> Value
  | ptr    : Nat -> Value
  | aggregate : List Value -> Value
  | nullPtr : Value
  deriving Repr
"#;

/// PLAIN match with a nested empty-list sub-pattern `| .aggregate [] =>` and a
/// non-empty `| .aggregate (_ :: _) =>`. Was:
/// `NotImplemented("match arm pattern: nested constructor List.cons does not
/// belong to field type Value._List")`.
#[test]
fn test_plain_match_aggregate_nil_and_cons_subpatterns() {
    let env = elab_all(&format!(
        r#"{VALUE_PRELUDE}
def isEmptyAgg (v : Value) : Bool :=
  match v with
  | .aggregate [] => true
  | .aggregate (_ :: _) => false
  | _ => false
"#
    ));
    assert_sound_const(&env, "isEmptyAgg");
}

/// PLAIN match binding the head/tail of a nested cons sub-pattern, reconstructing
/// through the aux constructor (`Value._List.cons head tail`).
#[test]
fn test_plain_match_aggregate_cons_binds_head_tail() {
    let env = elab_all(&format!(
        r#"{VALUE_PRELUDE}
def headOrSelf (v : Value) : Value :=
  match v with
  | .aggregate (x :: _) => x
  | _ => v
"#
    ));
    assert_sound_const(&env, "headOrSelf");
}

/// DO-block match with a nested empty-list sub-pattern, exactly the shape of
/// `TrustIr.semPtrFromParts` (`do { let m ← lookup …; match m with
/// | .aggregate [] => do … | _ => … }`). Was:
/// `NotImplemented("do-match arm pattern: nested constructor List.nil does not
/// belong to field type Value._List")`. The fix must NOT inject a `sorry` into
/// the inner-fallback / dead aux-minor branches — the trailing `| _ => …`
/// catch-all is threaded through.
#[test]
fn test_do_match_aggregate_nil_subpattern_no_sorry() {
    let env = elab_all(&format!(
        r#"{VALUE_PRELUDE}
abbrev M := Except String
def lookup (v : Value) : M Value := Except.ok v
def classify (v : Value) : M Bool := do
  let w <- lookup v
  match w with
  | .aggregate [] => Except.ok true
  | _ => Except.ok false
"#
    ));
    assert_no_sorry_monadic(&env, "classify");
}

/// DO-block match nested two levels deep, the `semPtrFromParts` core: outer
/// `match meta with | .aggregate [] => do { let data ← …; match data with
/// | .ptr a => … | .nullPtr => … | _ => … } | _ => …`.
#[test]
fn test_do_match_nested_aggregate_then_ptr_no_sorry() {
    let env = elab_all(&format!(
        r#"{VALUE_PRELUDE}
abbrev M := Except String
def lookup (v : Value) : M Value := Except.ok v
def bind1 (n : Nat) : M Nat := Except.ok n
def fail (s : String) : M Nat := Except.error s
def fromParts (meta data : Value) : M Nat := do
  let m <- lookup meta
  match m with
  | .aggregate [] => do
      let d <- lookup data
      match d with
      | .ptr a   => bind1 a
      | .nullPtr => bind1 0
      | _        => fail "data not ptr"
  | _ => fail "meta not unit"
"#
    ));
    assert_no_sorry_monadic(&env, "fromParts");
}

/// Construction direction round-trip: matching a nested cons and rebuilding the
/// SAME aggregate (`| .aggregate xs => .aggregate xs`), plus a fresh literal
/// list construction (`.aggregate [.int 1]`). Both exercise the
/// `List Value -> Value._List` construction path.
#[test]
fn test_aggregate_construction_roundtrip_and_literal() {
    let env = elab_all(&format!(
        r#"{VALUE_PRELUDE}
def reAgg (v : Value) : Value :=
  match v with
  | .aggregate xs => .aggregate xs
  | _ => v
def litAgg : Value := .aggregate [.int 1, .int 2]
def emptyAgg : Value := .aggregate []
"#
    ));
    assert_sound_const(&env, "reAgg");
    assert_sound_const(&env, "litAgg");
    assert_sound_const(&env, "emptyAgg");
}

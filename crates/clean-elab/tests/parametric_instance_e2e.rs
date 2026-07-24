// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B26 — parametric / recursive instances**
//! (`docs/plans/GAP_SWEEP_2026-07-09.md`, `classes_instances/p10`).
//!
//! A parametric instance `instance [C a] : C (List a)` used to die at
//! registration with **"Declaration contains free variables"**: the
//! instance-implicit premise `[C a]` auto-binds the type variable `a`, but the
//! instance elaboration abstracted only the *explicit* binders into the
//! definition's telescope and never took the auto-bound implicit `a`, so the
//! registered term still carried `a` as a free fvar.
//!
//! Ground truth: Lean `src/Lean/Elab/Instance.lean` — the instance's local
//! context (type params + instance-implicit binders) is abstracted into a
//! Pi/Lam telescope over the value before it is added to the environment, so
//! `instance [C a] : C (List a)` registers with shape
//! `{a} → [C a] → C (List a)` and no free variables. The fix mirrors the
//! `def`/`theorem` discipline: abstract the explicit binders, then
//! `wrap_with_auto_implicits` closes the auto-bound `a` OUTSIDE them (its type
//! `C a` references `a`).
//!
//! These drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict. Every
//! accept is a `:= rfl` VALUE pin (kernel-certified) with an EMPTY domain-axiom
//! closure; every wrong-value / missing-premise witness must REJECT LOUD.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the environment and elaboration
/// results (one per surface decl) or the first error.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn expect_pass(source: &str) -> (Environment, Vec<ElabResult>) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"))
}

fn expect_fail(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("file must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => e,
    }
}

fn is_registered(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

/// A value pin is not vacuous only if its transitive axiom closure is empty —
/// the parametric resolution must bottom out in real definitions, never in
/// axioms or `sorry`.
fn assert_empty_axiom_closure(env: &Environment, name: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"));
    assert!(
        deps.is_empty(),
        "{name} must have an EMPTY axiom closure, got {deps:?}"
    );
}

/// A class with one method + a ground instance for `Nat`.
const PREAMBLE: &str = "\
class C (a : Type) where\n\
  op : a → Nat\n\n\
instance : C Nat where\n\
  op := fun _ => 7\n";

// ═══════════════════════════════════════════════════════════════════════════
// (1) The B26 target: `instance [C a] : C (List a)` registers with no free vars
// ═══════════════════════════════════════════════════════════════════════════

/// The long-form parametric instance registers as a constant AND an instance.
/// Before B26 this died: "Declaration instC contains free variables".
#[test]
fn b26_parametric_instance_registers() {
    let src = format!("{PREAMBLE}\ninstance [C a] : C (List a) where\n  op := fun _ => 0\n");
    let (env, results) = expect_pass(&src);

    assert!(
        is_registered(&env, "instC"),
        "the parametric instance must register (base name instC)"
    );
    assert!(
        env.is_instance(&Name::from_string("instC")),
        "the parametric instance must be entered in the instance table"
    );

    // The registered type/value must be CLOSED — the auto-bound `a` and the
    // `[C a]` premise are abstracted into the telescope, no free fvars leak.
    let inst = results
        .iter()
        .rev()
        .find_map(|r| match r {
            ElabResult::Instance { ty, val, .. } => Some((ty, val)),
            _ => None,
        })
        .expect("last decl is an instance");
    assert!(
        !inst.0.has_fvar_quick(),
        "instance TYPE must have no free variables (got {:?})",
        inst.0
    );
    assert!(
        !inst.1.has_fvar_quick(),
        "instance VALUE must have no free variables (got {:?})",
        inst.1
    );
}

/// A downstream `C (List Nat)` goal SYNTHESIZES the parametric instance:
/// `C.op ([] : List Nat)` resolves `instC` at `a := Nat`, discharging the
/// `[C Nat]` premise from the ground instance. Value pin: it computes to `7`.
#[test]
fn b26_parametric_instance_resolves_and_computes() {
    let src = format!(
        "{PREAMBLE}\n\
         instance [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         theorem pin : C.op ([] : List Nat) = 7 := rfl\n"
    );
    let (env, _) = expect_pass(&src);
    assert!(is_registered(&env, "pin"));
    // Kernel-certified value pin bottoms out in real defs (op body, ground inst).
    assert_empty_axiom_closure(&env, "pin");
}

/// A WRONG value pin must REJECT: the resolved `op` body returns `7`, so
/// `= 8 := rfl` is a kernel type-mismatch, not a silent accept.
#[test]
fn b26_wrong_value_pin_rejects() {
    let src = format!(
        "{PREAMBLE}\n\
         instance [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         theorem bad : C.op ([] : List Nat) = 8 := rfl\n"
    );
    let err = expect_fail(&src);
    assert!(
        err.contains("mismatch") || err.contains("Mismatch"),
        "wrong pin must reject as a type mismatch, got: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (2) Short-form parametric instance `:= ⟨…⟩`
// ═══════════════════════════════════════════════════════════════════════════

/// The short-form (`:= ⟨fun _ => 7⟩`) parametric instance path is closed over
/// its telescope too — same fix, the short-form path.
#[test]
fn b26_short_form_parametric_registers_and_computes() {
    let src = format!(
        "{PREAMBLE}\n\
         instance [C a] : C (List a) := ⟨fun _ => 7⟩\n\n\
         theorem pin : C.op ([] : List Nat) = 7 := rfl\n"
    );
    let (env, _) = expect_pass(&src);
    assert!(is_registered(&env, "instC"));
    assert!(env.is_instance(&Name::from_string("instC")));
    assert_empty_axiom_closure(&env, "pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// (3) Recursive resolution through the parametric instance
// ═══════════════════════════════════════════════════════════════════════════

/// `C (List (List Nat))` resolves recursively: the parametric instance's
/// premise `[C (List Nat)]` is itself discharged by the parametric instance,
/// bottoming out at the `C Nat` ground instance. Value pin computes to `7`.
#[test]
fn b26_recursive_nested_resolution() {
    let src = format!(
        "{PREAMBLE}\n\
         instance [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         theorem pin : C.op ([] : List (List Nat)) = 7 := rfl\n"
    );
    let (env, _) = expect_pass(&src);
    assert_empty_axiom_closure(&env, "pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// (4) Explicit-type-param spelling `instance {a : Type} [C a] : C (List a)`
// ═══════════════════════════════════════════════════════════════════════════

/// The explicit `{a : Type}` spelling (where `a` is a declared binder, not
/// auto-bound) registers and resolves identically — the explicit-binder
/// abstraction and the auto-implicit close compose.
#[test]
fn b26_explicit_type_param_spelling() {
    let src = format!(
        "{PREAMBLE}\n\
         instance {{a : Type}} [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         theorem pin : C.op ([] : List Nat) = 7 := rfl\n"
    );
    let (env, _) = expect_pass(&src);
    assert!(env.is_instance(&Name::from_string("instC")));
    assert_empty_axiom_closure(&env, "pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// (5) Loud negative — genuinely missing premise
// ═══════════════════════════════════════════════════════════════════════════

/// The premise `[C a]` is GENUINELY discharged, not ignored: with no
/// `instance : C Bool`, a `C (List Bool)` goal cannot solve its `[C Bool]`
/// premise, so it FAILS LOUD (`failed to synthesize instance`) — never a
/// silent accept masking the missing premise.
#[test]
fn b26_missing_premise_fails_loud() {
    let src = format!(
        "{PREAMBLE}\n\
         instance [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         def bad : Nat := C.op ([] : List Bool)\n"
    );
    let err = expect_fail(&src);
    assert!(
        err.contains("synthesize") && err.contains("C (List"),
        "missing-premise goal must fail with a loud synthesis error naming \
         `C (List Bool)`, got: {err}"
    );
}

/// Control: adding the missing `instance : C Bool` makes the SAME goal succeed
/// — proving the negative above was the premise, not an unrelated failure.
#[test]
fn b26_missing_premise_control_supplying_it_resolves() {
    let src = format!(
        "{PREAMBLE}\n\
         instance : C Bool where\n  op := fun _ => 9\n\n\
         instance [C a] : C (List a) where\n  op := fun _ => 7\n\n\
         theorem pin : C.op ([] : List Bool) = 7 := rfl\n"
    );
    let (env, _) = expect_pass(&src);
    assert_empty_axiom_closure(&env, "pin");
}

// ═══════════════════════════════════════════════════════════════════════════
// (6) Regression — ground (non-parametric) instances still register + resolve
// ═══════════════════════════════════════════════════════════════════════════

/// A ground instance with an EMPTY binder telescope (the common case) is
/// unaffected: no explicit binders, no auto-implicits, closes to itself.
#[test]
fn b26_ground_instance_regression() {
    let src = format!("{PREAMBLE}\ntheorem pin : C.op (3 : Nat) = 7 := rfl\n");
    let (env, _) = expect_pass(&src);
    assert!(env.is_instance(&Name::from_string("instCNat")));
    assert_empty_axiom_closure(&env, "pin");
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression pin — a numeric literal in an OPEN-carrier slot must default to
//! `Nat` (Lean's `@[default_instance] instOfNatNat` semantics), never to
//! whichever `OfNat` instance happens to sit first in class-table order.
//!
//! ## The regression (trust-ir bridge prelude; clean 4cc40389d "sweep B12")
//!
//! Elaborating `0 ≤ v` / `0 = v` (`v : Int`) reaches the literal FIRST, while
//! the shared carrier `?α` is still an unassigned metavariable. The literal
//! lane (`infer/coercion.rs::elab_nat_literal_with_expected`) built the goal
//! `OfNat ?α 0` and eagerly committed the first instance in candidate order,
//! pinning `?α` to that instance's carrier:
//!
//! * pre-B12 (within-tier append + ascending-index tiebreak) the
//!   FIRST-registered instance won — `instOfNatNat` — matching Lean's
//!   default-instance OUTCOME by registration-order luck. `?α := Nat`, and
//!   the downstream `elab_app_with_int_coercion` recovery lane ("operand-0
//!   of `0 ≤ a`") repaired the `Int` operand.
//! * post-B12 (Lean-faithful most-recent-first within a priority tier — the
//!   kernel `register_instance` prepend) the LAST-registered instance won.
//!   In trust-clean's bridge-gate environment that is `instOfNatFloat`
//!   (Float imports late in the Lean-core `Init` closure): `?α := Float`,
//!   `v : Int` mismatched, and BOTH bridge-prelude decls (`wrap_eq_self`,
//!   `ok_wrap_eq` — each carries `(h0 : 0 ≤ v)`) died with
//!   `TypeMismatch { expected: Const(Float), actual: "const mismatch:
//!   Int vs Float" }` (`bridge_gate_default_on` → `PreludeFailed`).
//!
//! Real Lean never runs this race: a numeric literal whose type is still a
//! metavariable is POSTPONED and resolved by the `@[default_instance]`
//! mechanism — Lean core's only default `OfNat` instance is `instOfNatNat`,
//! so the literal defaults to `Nat` regardless of instance-table order. The
//! fix (coercion.rs Step 0) encodes exactly that at the literal seam, leaving
//! B12's most-recent-first ordering fully in force for determined
//! (ground-carrier) goals.
//!
//! ## How this file recreates the import-shaped table natively
//!
//! The bridge hits Float because the imported `Init` closure registers
//! `instOfNatFloat` last. Natively we reproduce the same shape by
//! registering one more same-priority `OfNat` instance (UInt8-carrier, fresh
//! name) AFTER `with_prelude()` — under most-recent-first it sits in front of
//! `instOfNatNat`, exactly like `instOfNatFloat` does under import. Without
//! the Step-0 default, `0 ≤ v` then pins `?α := UInt8` and fails with
//! "const mismatch: Int vs UInt8" — the bridge failure, minus the `.olean`
//! machinery. RED at 36dd3d6ff; GREEN with the open-carrier Nat default.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::{Declaration, Environment, KernelClassInfo, KernelInstanceInfo};
use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_parser::parse_file;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Mirror the import lane: register a LATE same-priority `OfNat` instance
/// with a non-`Nat` carrier, exactly as the Lean-core `Init` closure leaves
/// `instOfNatFloat` as the most recently registered `OfNat` instance.
///
/// `probeInstOfNatUInt8 : (n : Nat) → OfNat UInt8 n
///    := fun n => OfNat.mk UInt8 n (UInt8.ofNat n)`
///
/// The declaration is fully kernel-checked (`add_decl`), so the probe adds no
/// trust debt; `register_instance` then places it in `instOfNatNat`'s own
/// priority tier (100), where the within-tier order — the exact subject of
/// this pin — decides who captures an open `OfNat ?α n` goal.
fn register_late_non_nat_ofnat(env: &mut Environment) {
    // The native prelude registers `instOfNatNat` (and the UInt instances)
    // WITHOUT marking `OfNat` as a class, so the literal lane's Step-1 search
    // (`is_class(OfNat)`) never runs natively and the open-carrier race is
    // invisible. The `.olean` import lane DOES register the class (see
    // clean-olean `load_register.rs` — `register_class(KernelClassInfo {..})`
    // before `register_instance`), which is why the bridge env hits it.
    // Mirror the import lane exactly.
    if !env.is_class(&Name::from_string("OfNat")) {
        env.register_class(KernelClassInfo {
            name: Name::from_string("OfNat"),
            num_params: 2,
            out_params: Vec::new(),
            semi_out_params: Vec::new(),
        });
    }

    let nat = c("Nat");
    let uint8 = c("UInt8");
    let ofnat = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
    let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);

    // (n : Nat) → OfNat UInt8 n
    let inst_type = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(Expr::app(ofnat, uint8.clone()), Expr::bvar(0)),
    );
    // fun n => OfNat.mk UInt8 n (UInt8.ofNat n)
    let inst_value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(
            Expr::app(Expr::app(ofnat_mk, uint8), Expr::bvar(0)),
            Expr::app(c("UInt8.ofNat"), Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("probeInstOfNatUInt8"),
        level_params: vec![],
        type_: inst_type,
        value: inst_value,
        is_reducible: true,
    })
    .expect("probe OfNat instance must kernel-check against the native prelude");
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("probeInstOfNatUInt8"),
        class_name: Name::from_string("OfNat"),
        priority: 100,
        type_: None,
        value: None,
    });
}

/// Drive the real file pipeline against a native prelude env whose `OfNat`
/// table is import-shaped (a non-`Nat` carrier registered most recently).
fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut env = Environment::with_prelude();
    register_late_non_nat_ofnat(&mut env);
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn expect_pass(source: &str) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"));
}

/// The exact spelling of the regressed trust-ir bridge prelude
/// (`wrap_eq_self` / `ok_wrap_eq` both carry `(h0 : 0 ≤ v)`): the literal
/// elaborates while the shared `LE.le` carrier is still an open metavariable
/// and must default to `Nat` (the Int recovery lane then repairs) — not be
/// captured by the most-recently-registered `OfNat` carrier.
#[test]
fn literal_first_le_int_operand_elaborates() {
    expect_pass("theorem probe_le (m v : Int) (h0 : 0 ≤ v) (h1 : v < m) : 0 ≤ v := h0");
}

/// Same seam through `Eq` — the other homogeneous binop the recovery lane
/// covers (`LE.le`/`Eq : α → α → …`).
#[test]
fn literal_first_eq_int_operand_elaborates() {
    expect_pass("theorem probe_eq (v : Int) (h : 0 = v) : 0 = v := h");
}

/// Controls: GROUND-carrier literals still resolve through the ordinary
/// instance search — B12's most-recent-first ordering is untouched there,
/// including the late-registered probe instance winning its OWN carrier.
#[test]
fn ground_carrier_literal_unaffected() {
    expect_pass("def ground_nat : Nat := 2\ndef ground_int : Int := 2\ndef ground_u8 : UInt8 := 2");
}

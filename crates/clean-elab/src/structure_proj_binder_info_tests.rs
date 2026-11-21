// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure-projection PARAMETER BINDER INFOS — Lean 4's `mkProjections`.
//!
//! A plain `structure`'s generated projection used to KEEP the parameters'
//! declared binder infos, so `structure Pair (α β : Type)` produced
//! `Pair.fst : (α : Type) → (β : Type) → Pair α β → α` where Lean produces
//! `{α β : Type} → Pair α β → α`. Dot notation hid it — `p.fst` emits a kernel
//! `Expr::Proj` and never touches the constant's binders — so the divergence
//! only surfaced when the projection was applied in PREFIX form, where the
//! first explicit argument landed in the *parameter* slot:
//!
//! ```text
//! def f (p : Pair Nat Bool) : Nat := Pair.fst p
//!   ⇒ Type mismatch: expected Type, got cannot unify expressions of
//!     different shape: Discriminant(4) vs Discriminant(2)     -- App vs Sort
//! ```
//!
//! In `Mathlib/Logic/Unique.lean` that is the whole file's root failure. Line
//! 109 is `instance (priority := 100) : Inhabited α := toInhabited ‹Unique α›`
//! — a prefix application of the `extends Inhabited α` parent projection — and
//! it took down every declaration that later needed `Inhabited α`.
//!
//! GROUND TRUTH, re-measured against the pinned `lean` v4.30.0-rc2 binary with
//! `set_option pp.parens true`:
//!
//! ```text
//! structure S1 (α : Type) (β : Type)     ⇒  @S1.f : {α β : Type} → S1 α β → α
//! structure S2 {α : Type}                ⇒  @S2.h : {α : Type} → S2 → α
//! structure S4 ⦃α : Type⦄                ⇒  @S4.f : {α : Type} → S4 → α
//! structure S3 (α : Type) [Inhabited α]  ⇒  @S3.k : {α : Type} → [inst : Inhabited α] → S3 α → α
//! structure P1 (α : Type) extends S1 α α ⇒  @P1.toS1 : {α : Type} → P1 α → S1 α α
//! class     C1 (α : Type)                ⇒  @C1.m : {α : Type} → [self : C1 α] → α
//! class     C2 (α : Type) [Inhabited α]  ⇒  @C2.n : {α : Type} → {inst : Inhabited α} → [self : C2 α] → α
//! ```
//!
//! The examples have parameters determined by explicit arguments or the result
//! range. A class field whose carrier is unused, such as `C.n : Nat`, keeps
//! that carrier explicit: instance-implicit self alone does not infer it.
//! Class instance parameters become `{inst}`; structures keep `[inst]`.
//! Self is explicit for a structure and instance-implicit for a class.
//!
//! The CONSTRUCTOR is a separate constant and is NOT asserted here beyond the
//! shape it already had: Clean makes ctor params unconditionally implicit,
//! while Lean keeps an instance-implicit ctor param instance-implicit
//! (`@S3.mk : {α : Type} → [inst : Inhabited α] → α → S3 α`). That residual is
//! recorded, not fixed, by this change.

use crate::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Elaborate `source` into a fresh prelude environment, asserting every
/// declaration lands.
fn env_of(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture source must parse");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed)
            .unwrap_or_else(|e| panic!("declaration must elaborate: {e:?}"));
    }
    env
}

/// Elaborate `source`, returning the per-declaration results without asserting.
/// Used by the negative controls, where a declaration is EXPECTED to fail.
fn try_env_of(source: &str) -> (Environment, Vec<Result<(), String>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture source must parse");
    let mut out = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        out.push(
            elaborate_decl_and_register(&mut env, &processed)
                .map(|_| ())
                .map_err(|e| format!("{e:?}")),
        );
    }
    (env, out)
}

/// The binder infos of a constant's leading `Pi` spine, outermost first.
fn binder_spine(env: &Environment, name: &str) -> Vec<BinderInfo> {
    let ty = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"))
        .type_
        .clone();
    let mut out = Vec::new();
    let mut cur: Expr = ty;
    while let ExprKind::Pi(bd, _, body) = cur.kind() {
        out.push(bd.info);
        cur = body.as_ref().clone();
    }
    out
}

const PAIR: &str = "\
structure Pair (α : Type) (β : Type) where
  fst : α
  snd : β
";

#[test]
fn test_structure_projection_explicit_params_become_implicit() {
    let env = env_of(PAIR);
    // `@Pair.fst : {α β : Type} → Pair α β → α`
    assert_eq!(
        binder_spine(&env, "Pair.fst"),
        vec![
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::Default
        ],
        "structure params are implicit in the projection and `self` stays explicit"
    );
    assert_eq!(
        binder_spine(&env, "Pair.snd")[..2],
        [BinderInfo::Implicit, BinderInfo::Implicit]
    );
}

#[test]
fn test_structure_projection_strict_implicit_param_becomes_implicit() {
    let env = env_of(
        "\
structure Strict ⦃α : Type⦄ where
  f : α
",
    );
    assert_eq!(
        binder_spine(&env, "Strict.f"),
        vec![BinderInfo::Implicit, BinderInfo::Default],
        "a strict-implicit param is `{{α}}` in the projection (Lean @S4.f)"
    );
}

#[test]
fn test_structure_projection_instance_param_stays_instance_implicit() {
    let env = env_of(
        "\
structure WithInh (α : Type) [Inhabited α] where
  k : α
",
    );
    // Lean: `@S3.k : {α : Type} → [inst : Inhabited α] → S3 α → α`.
    // This is the ONE parameter kind a plain structure does NOT flatten to
    // implicit, and it is what separates `StructureKind::Structure` from
    // `StructureKind::Class` after this fix.
    assert_eq!(
        binder_spine(&env, "WithInh.k"),
        vec![
            BinderInfo::Implicit,
            BinderInfo::InstImplicit,
            BinderInfo::Default
        ]
    );
}

#[test]
fn test_class_projection_flattens_instance_param_to_implicit() {
    let env = env_of(
        "\
class WithInst (α : Type) [Inhabited α] where
  w : α
",
    );
    // Lean: `@C2.n : {α : Type} → {inst : Inhabited α} → [self : C2 α] → α`.
    // Control for the test above: the class arm is UNCHANGED by this fix, so if
    // the two ever collapse into one rule, this test goes red.
    assert_eq!(
        binder_spine(&env, "WithInst.w"),
        vec![
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::InstImplicit
        ]
    );
}

#[test]
fn test_class_projection_unused_carrier_stays_explicit() {
    let env = env_of(
        "class Count (α : Type) where\n  count : Nat\n\
         def readCount [Count Nat] : Nat := Count.count Nat\n",
    );
    assert_eq!(
        binder_spine(&env, "Count.count"),
        vec![BinderInfo::Default, BinderInfo::InstImplicit],
        "the implicit dictionary alone does not determine a carrier unused by the field"
    );
    assert!(env
        .axiom_deps(&Name::from_string("readCount"))
        .expect("registered checked consumer")
        .is_empty());
}

#[test]
fn test_class_projection_parameter_inference_uses_later_explicit_parameter() {
    let env = env_of("class Tagged (α : Type) (tag : α) where\n  count : Nat\n");
    assert_eq!(
        binder_spine(&env, "Tagged.count"),
        vec![
            BinderInfo::Implicit,
            BinderInfo::Default,
            BinderInfo::InstImplicit
        ],
        "the unused tag stays explicit and then determines its carrier"
    );
}

#[test]
fn test_class_projection_unused_out_parameter_stays_implicit() {
    for annotation in ["outParam Type", "(outParam Type)", "((outParam Type))"] {
        let env = env_of(&format!(
            "class CountOut (α : {annotation}) where\n  count : Nat\n\
             def readCountOut [CountOut Nat] : Nat := CountOut.count\n"
        ));
        assert_eq!(
            binder_spine(&env, "CountOut.count"),
            vec![BinderInfo::Implicit, BinderInfo::InstImplicit],
            "mkProjections preserves the outParam annotation before inference: {annotation}"
        );
        assert!(env
            .axiom_deps(&Name::from_string("readCountOut"))
            .expect("registered checked caller")
            .is_empty());
    }
}

#[test]
fn test_parent_projection_params_become_implicit() {
    let env = env_of(
        "\
universe u
structure MyBase (α : Sort u) where
  d : α
structure MyExt (α : Sort u) extends MyBase α where
  uniq : ∀ a : α, a = d
",
    );
    // Lean: `@P1.toS1 : {α : Type} → P1 α → S1 α α`. The parent subobject is
    // field 0 and goes through the same loop, so one rule covers both.
    assert_eq!(
        binder_spine(&env, "MyExt.toMyBase"),
        vec![BinderInfo::Implicit, BinderInfo::Default]
    );
}

#[test]
fn test_projection_applied_in_prefix_form_elaborates() {
    // The reproduction, one line long. Before the fix this failed with
    // "expected Type, got cannot unify expressions of different shape:
    // Discriminant(4) vs Discriminant(2)" — `p` bound to the `α` slot.
    let source = format!("{PAIR}\ndef f (p : Pair Nat Bool) : Nat := Pair.fst p\n");
    let (_, results) = try_env_of(&source);
    assert!(
        results.iter().all(Result::is_ok),
        "prefix-applied projection must elaborate: {results:?}"
    );
}

#[test]
fn test_projection_dot_notation_still_elaborates() {
    // The control that must not move: dot notation emits a kernel `Expr::Proj`
    // and never reads the constant's binder infos, so it passed BEFORE the fix
    // too. It is here so a future change that "fixes" prefix application by
    // touching the dot path is caught.
    let source = format!("{PAIR}\ndef f (p : Pair Nat Bool) : Nat := p.fst\n");
    let (_, results) = try_env_of(&source);
    assert!(
        results.iter().all(Result::is_ok),
        "dot-notation projection must elaborate: {results:?}"
    );
}

#[test]
fn test_projection_requires_at_for_positional_type_args() {
    for (head, accepted) in [("Pair.fst", false), ("@Pair.fst", true)] {
        let source = format!("{PAIR}\ndef f (p : Pair Nat Bool) : Nat := {head} Nat Bool p\n");
        let (_, results) = try_env_of(&source);
        assert_eq!(
            results.iter().all(Result::is_ok),
            accepted,
            "{head}: {results:?}"
        );
    }
}

#[test]
fn test_projection_type_args_require_explicit_at() {
    // Both actual Lean30/35 reject the original unmarked call. Preserve that
    // source as a negative control alongside the accepted explicit twin.
    let source = format!("{PAIR}\ndef f (p : Pair Nat Bool) : Nat := Pair.fst Nat Bool p\n");
    let (env, results) = try_env_of(&source);
    assert!(results.first().is_some_and(Result::is_ok));
    assert!(
        results.last().is_some_and(Result::is_err),
        "ordinary type arguments must not fill implicit slots: {results:?}"
    );
    assert!(env.get_const(&Name::from_string("f")).is_none());

    let source = format!("{PAIR}\ndef f (p : Pair Nat Bool) : Nat := @Pair.fst Nat Bool p\n");
    let env = env_of(&source);
    assert!(
        env.axiom_deps(&Name::from_string("f"))
            .expect("registered checked explicit caller")
            .is_empty(),
        "the explicit caller has no axiom-backed replacement"
    );
}

#[test]
fn test_parent_projection_prefix_application_is_the_unique_root() {
    // `Mathlib/Logic/Unique.lean:109` — `instance (priority := 100) :
    // Inhabited α := toInhabited ‹Unique α›` — reduced to its load-bearing
    // shape: a PREFIX application of the `extends` parent projection. That one
    // line is the root of the whole file's failure set; every later
    // `failed to synthesize instance Inhabited for goal Inhabited.{?u} α` in
    // `Logic/Unique.lean` is downstream of the instance it did not register.
    //
    // Measured through `clean check` at c41d2dcf5 on the full `variable`-based
    // form, which reports it verbatim:
    //   ✗ MyUniq: elaboration error at line 11: Type mismatch: expected
    //     Sort ?u_2, got cannot unify expressions of different shape:
    //     Discriminant(4) vs Discriminant(2)
    //   ✗ MyUniq.eq_default: failed to synthesize instance Inhabited for goal
    //     App(Const(Inhabited, [Param(?u_2)]), FVar(FVarId(0)))
    // The `variable`-based spelling does NOT reproduce through
    // `elaborate_decl_and_register` (the section binders are not applied on
    // this path), so the binder-explicit spelling below is what carries the
    // regression here — it is mutation-proved red against the pre-fix rule.
    let source = "\
universe u

structure MyUniq (α : Sort u) extends Inhabited α where
  uniq : ∀ a : α, a = default

def inhOfUniq {α : Sort u} (h : MyUniq α) : Inhabited α :=
  MyUniq.toInhabited h
";
    let (_, results) = try_env_of(source);
    assert!(
        results.iter().all(Result::is_ok),
        "the Unique.lean root shape must elaborate: {results:?}"
    );
}

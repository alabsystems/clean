// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Lean 4's binder-annotation-update form of `variable`** — `variable (P Q a b)`
//! / `variable {P Q}`, written with NO type ascription.
//!
//! A bracketed `variable` binder with no `: T` is not a declaration. It re-binds
//! ALREADY-DECLARED section variables at a new binder annotation, keeping their
//! declared type and their position in the telescope (lean4
//! `src/Lean/Elab/Command.lean`, `replaceBinderAnnotation`).
//!
//! Clean used to append them as BRAND-NEW variables whose type was a fresh
//! metavariable (`infer/elab_variable.rs`, "Untyped variable binder: create a
//! fresh sort metavariable"). Two things then went wrong at once for every
//! declaration in the governed block:
//!
//! 1. the telescope carried the variable TWICE (`{P : Prop}` and `(P : ?m)`),
//!    which surfaces as `fvar mismatch: FVarId(2) vs FVarId(11)`; and
//! 2. the surviving occurrence's type was an unresolved metavariable, which
//!    the elaborator's type tests print as a tagged FVar
//!    (`MetaState::META_FVAR_TAG = 1 << 63`, so `FVarId(9223372036854775808)`
//!    is `?m.0`).
//!
//! Verbatim pre-fix errors from the committed Mathlib source-elaboration
//! report (`reports/source-elab/srcelab-2026-08-23-g14a1e99a9.json`,
//! `Mathlib/Logic/Basic.lean`), all inside the block governed by lines
//! 874/929:
//!
//! ```text
//! ite_apply:          Type mismatch: expected conditional guard of type Bool or Prop,
//!                     got FVar(FVarId(9223372036854775808))
//! ite_and:            Tactic failed: type mismatch: expected Prop,
//!                     got FVar(FVarId(9223372036854775808))
//! ite_prop_iff_or:    Type mismatch: expected conditional guard of type Bool or Prop,
//!                     got FVar(FVarId(9223372036854775812))
//! dite_dite_comm:     Type mismatch: expected FVar(FVarId(2)),
//!                     got fvar mismatch: FVarId(11) vs FVarId(2)
//! ```
//!
//! Ground truth for the fixture below, measured with lean 4.33.1 on this
//! machine, 2026-08-23:
//!
//! ```text
//! bavu_explicit : ∀ (P : Prop) [Decidable P] (a : Nat), P → P ∧ a = a
//! bavu_ite      : ∀ (P : Prop) [inst : Decidable P] (a b : Nat),
//!                   (if P then a else b) = if P then a else b
//! bavu_implicit : ∀ {P : Prop} [Decidable P] (a : Nat), P → P ∧ a = a
//! bavu_inner    : ∀ (P : Prop), P → P
//! bavu_outer    : ∀ {P : Prop}, P → P
//! ```
//!
//! This drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a verdict here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Drive the real file pipeline. Returns the environment or the first error.
fn elaborate_file(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let _: ElabResult =
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(env)
}

fn fixture() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/section_variables/binder_annotation_update.lean");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// The leading `Pi` telescope of `ty`, as `(binder-info, domain)` pairs.
fn telescope(ty: &Expr) -> Vec<(BinderInfo, Expr)> {
    let mut out = Vec::new();
    let mut cur = ty.clone();
    while let ExprKind::Pi(bd, dom, body) = cur.kind() {
        out.push((bd.info, dom.as_ref().clone()));
        cur = body.as_ref().clone();
    }
    out
}

fn type_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"))
        .type_
        .clone()
}

/// No binder domain anywhere in `ty` may be a metavariable.
///
/// The elaborator encodes metavariables as FVars with the top bit set
/// (`MetaState::META_FVAR_TAG = 1 << 63`), so a `?m` that leaked into a
/// registered signature is exactly an `FVar` with id >= 2^63.
fn assert_no_meta_fvar(ty: &Expr, who: &str) {
    const META_FVAR_TAG: u64 = 1 << 63;
    let printed = format!("{ty:?}");
    for cap in printed.split("FVarId(").skip(1) {
        let digits: String = cap.chars().take_while(char::is_ascii_digit).collect();
        if let Ok(id) = digits.parse::<u64>() {
            assert!(
                id < META_FVAR_TAG,
                "`{who}` kept an unresolved metavariable (FVarId({id}) >= 1<<63) \
                 in its registered type: {printed}"
            );
        }
    }
}

/// `variable (P Q a b)` re-binds the DECLARED `P`/`a` as explicit; it does not
/// mint two more variables typed by a metavariable.
#[test]
fn binder_annotation_update_rebinds_declared_variables() {
    let env =
        elaborate_file(&fixture()).unwrap_or_else(|e| panic!("fixture must fully check, got: {e}"));

    let ty = type_of(&env, "bavu_explicit");
    assert_no_meta_fvar(&ty, "bavu_explicit");
    let tele = telescope(&ty);

    // ∀ (P : Prop) [Decidable P] (a : Nat), P → P ∧ a = a
    assert_eq!(
        tele.len(),
        4,
        "expected 4 leading binders (P, [Decidable P], a, h), got {}: {ty:?}",
        tele.len()
    );
    assert_eq!(
        tele[0].0,
        BinderInfo::Default,
        "`variable (P Q a b)` must make the DECLARED `P` explicit, got {:?}",
        tele[0].0
    );
    assert!(
        matches!(tele[0].1.kind(), ExprKind::Sort(l) if l.normalize() == clean_kernel::Level::Zero),
        "`P` must keep its DECLARED type `Prop`, got {:?}",
        tele[0].1
    );
    assert_eq!(
        tele[1].0,
        BinderInfo::InstImplicit,
        "`[Decidable P]` must stay instance-implicit, got {:?}",
        tele[1].0
    );
    assert_eq!(
        tele[2].0,
        BinderInfo::Default,
        "`variable (P Q a b)` must make the DECLARED `a` explicit, got {:?}",
        tele[2].0
    );
}

/// The `ite` guard sees a real `Prop`, not `?m`.
///
/// Pre-fix this raised `Type mismatch: expected conditional guard of type Bool
/// or Prop, got FVar(FVarId(9223372036854775808))` from
/// `ElabCtx::condition_is_bool` — nine `ite`/`dite` declarations in
/// `Mathlib/Logic/Basic.lean` died on exactly this.
#[test]
fn binder_annotation_update_keeps_the_ite_guard_a_prop() {
    let env =
        elaborate_file(&fixture()).unwrap_or_else(|e| panic!("fixture must fully check, got: {e}"));
    let ty = type_of(&env, "bavu_ite");
    assert_no_meta_fvar(&ty, "bavu_ite");
    let tele = telescope(&ty);
    assert_eq!(
        tele[0].0,
        BinderInfo::Default,
        "`bavu_ite`'s `P` must be explicit, got {:?}",
        tele[0].0
    );
}

/// `variable {P Q}` puts an explicit variable BACK to implicit, in place.
#[test]
fn binder_annotation_update_can_go_back_to_implicit() {
    let env =
        elaborate_file(&fixture()).unwrap_or_else(|e| panic!("fixture must fully check, got: {e}"));
    let ty = type_of(&env, "bavu_implicit");
    assert_no_meta_fvar(&ty, "bavu_implicit");
    let tele = telescope(&ty);
    assert_eq!(
        tele[0].0,
        BinderInfo::Implicit,
        "`variable {{P Q}}` must put `P` back to implicit, got {:?}",
        tele[0].0
    );
    assert_eq!(
        tele[2].0,
        BinderInfo::Default,
        "`a` was never re-annotated and must stay explicit, got {:?}",
        tele[2].0
    );
}

/// The re-binding is SECTION-SCOPED.
///
/// `variable (P)` inside `Inner` re-annotates the variable `Outer` declared;
/// `end Inner` must put it back. `FileContext::exit_section` truncates the
/// accumulated telescope, which cannot undo an edit to an entry BELOW the
/// section marker — the binder annotations are snapshotted on `enter_section`
/// and restored here. Lean 4.33.1 proves `bavu_inner : ∀ (P : Prop), P → P`
/// and `bavu_outer : ∀ {P : Prop}, P → P`.
#[test]
fn binder_annotation_update_is_section_scoped() {
    let env =
        elaborate_file(&fixture()).unwrap_or_else(|e| panic!("fixture must fully check, got: {e}"));

    let inner = type_of(&env, "bavu_inner");
    assert_no_meta_fvar(&inner, "bavu_inner");
    assert_eq!(
        telescope(&inner)[0].0,
        BinderInfo::Default,
        "inside `Inner`, `variable (P)` must make `P` explicit: {inner:?}"
    );

    let outer = type_of(&env, "bavu_outer");
    assert_no_meta_fvar(&outer, "bavu_outer");
    assert_eq!(
        telescope(&outer)[0].0,
        BinderInfo::Implicit,
        "after `end Inner`, `P` must be implicit again: {outer:?}"
    );
}

/// Source modules may group declarations in namespaces and sections. Their
/// leaf rejections are reported in the batch outcome.
fn elaborate_family_batch(source: &str) -> Result<Environment, String> {
    use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};

    let mut env = Environment::with_prelude();
    let declarations = parse_file(source).map_err(|error| format!("{error:?}"))?;
    let outcome = elaborate_module(
        &mut env,
        &mut FileContext::new(),
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    if outcome.is_clean() && outcome.committed {
        Ok(env)
    } else {
        Err(outcome.render_rejections())
    }
}

fn elaborate_family_module(source: &str) -> Result<Environment, String> {
    use clean_elab::module_driver::{
        elaborate_decls, module_elaboration_lock, DriverOptions, VerdictKind,
    };

    let _guard = module_elaboration_lock();
    let decls = parse_file(source).map_err(|error| format!("{error:?}"))?;
    let mut env = Environment::with_prelude();
    let report = elaborate_decls(
        &mut env,
        &decls,
        source,
        &mut FileContext::new(),
        DriverOptions {
            lean_front_door: true,
            ..Default::default()
        },
        &mut (),
    );
    if let Some(verdict) = report
        .verdicts
        .iter()
        .find(|v| v.kind != VerdictKind::Passed)
    {
        return Err(format!("{verdict:?}"));
    }
    Ok(env)
}

/// A family abstracts exactly the ambient locals used by its elaborated
/// parameters or fields, including their transitive type dependencies.
#[test]
fn family_section_parameters_follow_dependencies_and_shadowing() {
    let code = r#"
universe u
section
variable {α : Type u} (x : α) (unused : Nat)
structure Packet (p : x = x) : Prop where
  accepts : p = p
structure FieldOnly : Prop where
  accepts : x = x
structure Shadow (x : Nat) : Prop where
  accepts : x = x
class Label where
  value : α
class Decorated extends @Label α where
  another : α
inductive Chain where
  | leaf (y : α) : Chain
  | next (prev : Chain) : Chain
inductive Flag where
  | yes : Flag
end
"#;
    let env = elaborate_family_module(code).unwrap_or_else(|e| panic!("{e}"));
    for (name, expected) in [
        (
            "Packet",
            vec![
                BinderInfo::Implicit,
                BinderInfo::Default,
                BinderInfo::Default,
            ],
        ),
        ("FieldOnly", vec![BinderInfo::Implicit, BinderInfo::Default]),
        ("Shadow", vec![BinderInfo::Default]),
        ("Label", vec![BinderInfo::Implicit]),
        ("Decorated", vec![BinderInfo::Implicit]),
        ("Chain", vec![BinderInfo::Implicit]),
        ("Flag", vec![]),
    ] {
        let former = type_of(&env, name);
        let kinds: Vec<_> = telescope(&former).iter().map(|(kind, _)| *kind).collect();
        assert_eq!(kinds, expected, "{name}");
        assert_eq!(
            env.get_inductive(&Name::from_string(name))
                .unwrap()
                .num_params as usize,
            expected.len(),
            "{name}"
        );
        assert!(!former.has_fvar_quick(), "{name}");
    }
    for name in [
        "Packet.mk",
        "Packet.accepts",
        "FieldOnly.accepts",
        "Chain.next",
        "Decorated.another",
    ] {
        assert!(!type_of(&env, name).has_fvar_quick(), "{name}");
    }
}

#[test]
fn family_section_parameters_preserve_field_and_proof_refusals() {
    let originals = [
        include_str!("../../../reports/self-proof-w1-quotient-packet/fixtures/Ambient.lean"),
        include_str!(
            "../../../reports/self-proof-w1-quotient-packet/fixtures/SignatureAmbient.lean"
        ),
        include_str!("../../../reports/self-proof-w1-quotient-packet/fixtures/Explicit.lean"),
        include_str!(
            "../../../reports/self-proof-w1-quotient-packet/fixtures/SignatureExplicit.lean"
        ),
        include_str!("../../../reports/self-proof-w1-quotient-packet/fixtures/Independent.lean"),
    ];
    for check in [elaborate_family_module, elaborate_family_batch] {
        for input in originals {
            check(input).unwrap_or_else(|error| panic!("{error}: {input}"));
        }
        assert!(check(include_str!(
            "../../../reports/self-proof-w1-quotient-packet/fixtures/BadField.lean"
        ))
        .is_err());
        assert!(check(include_str!(
            "../../../reports/self-proof-w1-quotient-packet/fixtures/BadProof.lean"
        ))
        .is_err());
    }
}

#[test]
fn family_section_parameters_keep_only_used_instances_and_their_binder_kinds() {
    let code = r#"
universe u
section
variable {α : Type u} [inst : Inhabited α]
structure Keeps where
  ok : (default : α) = default
inductive Needs where
  | mk (ok : (default : α) = default) : Needs
inductive Drops where
  | mk (a : α) : Drops
end
"#;
    let env = elaborate_family_module(code).unwrap_or_else(|e| panic!("{e}"));
    for name in ["Keeps", "Keeps.mk", "Needs", "Needs.mk"] {
        let ty = type_of(&env, name);
        let binders = telescope(&ty);
        assert_eq!(binders[0].0, BinderInfo::Implicit, "{name}");
        assert_eq!(binders[1].0, BinderInfo::InstImplicit, "{name}");
    }
    assert_eq!(telescope(&type_of(&env, "Drops")).len(), 1);
}

#[test]
fn family_namespace_binders_restore_at_end_in_driver_and_batch() {
    let source = "variable (x : Nat)\nnamespace Inner\nvariable {x}\nstructure Uses : Prop where\n  ok : x = x\nend Inner\nstructure Outer : Prop where\n  ok : x = x\n";
    for check in [elaborate_family_module, elaborate_family_batch] {
        let env = check(source).unwrap_or_else(|e| panic!("{e}"));
        for (name, info) in [
            ("Inner.Uses", BinderInfo::Implicit),
            ("Outer", BinderInfo::Default),
        ] {
            let ty = type_of(&env, name);
            let binders = telescope(&ty);
            assert_eq!(binders.len(), 1, "{name}");
            assert_eq!(binders[0].0, info, "{name}");
        }
    }
}

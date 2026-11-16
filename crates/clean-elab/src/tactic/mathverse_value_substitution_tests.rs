// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VALUE substitution: the two properties that make it not a soundness hole.
//!
//! A resident declaration that agrees with a shard row in NAME, KIND and TYPE
//! but carries a different BODY is admitted by the dependency-loader gate on
//! purpose — see the `# SCOPE` note on `validate_resident_type_agreement` in
//! `mathverse_use.rs` for the measurement behind that decision. These tests pin
//! the two mechanisms the decision rests on, so a change that removes either is
//! caught here rather than in a corpus audit six months later:
//!
//! 1. `test_prelude_mode_keeps_definitional_proof_irrelevance` — a Prop-typed
//!    resident's VALUE cannot affect any def-eq outcome, because definitional
//!    proof irrelevance is live in the mode `Environment::with_prelude()`
//!    produces (`clean-kernel/src/tc/def_eq/proof_irrel.rs:16`, applied in
//!    `def_eq/mod.rs` before the lazy-delta loop). Measured: 151 of the 1,033
//!    gate-admitted residents are Prop-typed, 54 of them reachable from the
//!    308-name citation population, including its three busiest members.
//!
//! 2. `test_value_divergent_resident_the_proof_depends_on_fails_closed` and
//!    `..._the_proof_does_not_depend_on_still_closes` — everything the loader
//!    ADDS goes through checked `Environment::add_decl` in the SESSION
//!    environment, i.e. against the residents' actual bodies. So a value
//!    divergence the cited proof actually depends on is refused by the KERNEL,
//!    and one it does not depend on closes (which is why no value check is
//!    worth its citability cost).
//!
//! The pair uses one fixture family: shard `Victim := 1`, resident `Victim :=
//! 0`, and two cited theorems over it — one whose statement needs the shard's
//! body, one that is parametric in it.

#![cfg(feature = "mathverse-library")]

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{
    BinderInfo, Declaration, DeclarationVerification, Environment, Expr, ExprKind, Level, Name,
    TypeChecker,
};
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

use super::mathverse_use::{
    clear_mathverse_library, mathverse_apply_named, set_mathverse_library, TrustGate,
};
use super::{ProofState, TacticError};

/// Flatten a kernel `Level` into `writer`. Panics on anything the fixtures do
/// not use, rather than encoding an approximation the test did not mean.
fn add_level(writer: &mut ShardWriter, level: &Level) -> u32 {
    match level {
        Level::Zero => writer.add_level(FlatLevel::zero()),
        Level::Succ(inner) => {
            let inner_idx = add_level(writer, inner);
            writer.add_level(FlatLevel::succ(inner_idx))
        }
        other => panic!("fixture cannot encode level {other:?}"),
    }
}

/// Flatten a kernel `Expr` into `writer`, same policy as [`add_level`].
fn add_expr(writer: &mut ShardWriter, expr: &Expr) -> u32 {
    match expr.kind() {
        ExprKind::BVar(idx) => writer.add_expr(FlatExpr::bvar(*idx)),
        ExprKind::Sort(level) => {
            let level_idx = add_level(writer, level);
            writer.add_expr(FlatExpr::sort(level_idx))
        }
        ExprKind::Const(name, levels) => {
            let name_idx = writer.add_string(&name.to_string());
            let list_idx = if levels.is_empty() {
                u32::MAX
            } else {
                let indices: Vec<u32> = levels.iter().map(|l| add_level(writer, l)).collect();
                writer.add_level_list(&indices)
            };
            writer.add_expr(FlatExpr::const_ref(name_idx, list_idx))
        }
        ExprKind::App(func, arg) => {
            let fi = add_expr(writer, func);
            let ai = add_expr(writer, arg);
            writer.add_expr(FlatExpr::app(fi, ai))
        }
        ExprKind::Lam(bd, ty, body) => {
            let ti = add_expr(writer, ty);
            let bi = add_expr(writer, body);
            writer.add_expr(FlatExpr::lam(binder_info_u8(bd.info), ti, bi))
        }
        ExprKind::Pi(bd, ty, body) => {
            let ti = add_expr(writer, ty);
            let bi = add_expr(writer, body);
            writer.add_expr(FlatExpr::pi(binder_info_u8(bd.info), ti, bi))
        }
        other => panic!("fixture cannot encode {other:?}"),
    }
}

fn binder_info_u8(info: BinderInfo) -> u8 {
    match info {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

/// Every fixture row is `KernelVerified`, so the confidence gate never fires
/// and the residency rules are the only thing under test.
fn header(name_idx: u32, type_idx: u32, value_idx: u32, kind: DeclKind) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: kind as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn const_at_type(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())])
}

fn nat_one() -> Expr {
    Expr::app(const_("Nat.succ"), const_("Nat.zero"))
}

/// Install a two-row shard — `Cited.thm : thm_type := thm_value` depending on
/// `Victim : Nat := 1` — into the thread-local library, and return a session
/// environment holding CLEAN's `Victim : Nat := 0`: same name, same kind, same
/// type, different body, registered through the kernel's checked path so it is
/// a genuine `FullKernelCheck` resident.
fn install_value_divergent_fixture(thm_type: &Expr, thm_value: &Expr) -> Environment {
    let mut writer = ShardWriter::new();

    let thm_ty_idx = add_expr(&mut writer, thm_type);
    let thm_val_idx = add_expr(&mut writer, thm_value);
    let thm_name = writer.add_string("Cited.thm");
    writer.add_constant(header(thm_name, thm_ty_idx, thm_val_idx, DeclKind::Theorem));

    let victim_ty_idx = add_expr(&mut writer, &const_("Nat"));
    let victim_val_idx = add_expr(&mut writer, &nat_one());
    let victim_name = writer.add_string("Victim");
    writer.add_constant(header(
        victim_name,
        victim_ty_idx,
        victim_val_idx,
        DeclKind::Definition,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("fixture shard writes");
    let shard = ShardReader::from_bytes(&buf).expect("fixture shard reads");

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).expect("fixture shard loads");
    lib.add_dependency(0, 1);
    set_mathverse_library(lib);

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Victim"),
        level_params: vec![],
        type_: const_("Nat"),
        value: const_("Nat.zero"),
        is_reducible: false,
    })
    .expect("the resident registers through the kernel's checked path");
    assert_eq!(
        env.declaration_verification(&Name::from_string("Victim")),
        Some(DeclarationVerification::FullKernelCheck),
        "precondition: the resident is FULLY kernel-checked — that is what makes \
         the residency rule admit it instead of refusing it as shadowed-by-unchecked"
    );
    env
}

/// PROPERTY 1. For a resident whose TYPE is a Prop, no def-eq outcome anywhere
/// can depend on its VALUE, so `Theorem` rows (and Prop-typed `Definition`
/// rows — the exemption keys on the TYPE, not the kind) are exempt from value
/// substitution by construction.
///
/// The mechanism is definitional proof irrelevance
/// (`clean-kernel/src/tc/def_eq/proof_irrel.rs`), which
/// `is_def_eq_proof_irrel` declines ONLY in `CleanMode::Cubical` /
/// `CleanMode::Directed` (where it would derive UIP against univalence). This
/// test pins that `Environment::with_prelude()` — the environment every
/// citation runs in — is not one of those modes, and that the exemption is
/// restricted to Prop: the `Nat` control must NOT collapse.
///
/// Axioms cannot unfold, so proof irrelevance is the only rule that can equate
/// `hA` and `hB`.
#[test]
fn test_prelude_mode_keeps_definitional_proof_irrelevance() {
    let mut env = Environment::with_prelude();

    let axiom = |name: &str, type_: Expr| Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    };
    env.add_decl(axiom("PIrrel.P", Expr::sort(Level::zero())))
        .expect("P : Prop registers");
    env.add_decl(axiom("PIrrel.hA", const_("PIrrel.P")))
        .expect("hA : P registers");
    env.add_decl(axiom("PIrrel.hB", const_("PIrrel.P")))
        .expect("hB : P registers");
    env.add_decl(axiom("PIrrel.nA", const_("Nat")))
        .expect("nA : Nat registers");
    env.add_decl(axiom("PIrrel.nB", const_("Nat")))
        .expect("nB : Nat registers");

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&const_("PIrrel.hA"), &const_("PIrrel.hB")),
        "definitional proof irrelevance must be live in {:?} (the mode \
         `Environment::with_prelude()` produces); without it a Prop-typed \
         resident's body becomes observable and the VALUE-substitution \
         exemption recorded on `validate_resident_type_agreement` no longer holds",
        env.mode()
    );
    assert!(
        !tc.is_def_eq(&const_("PIrrel.nA"), &const_("PIrrel.nB")),
        "proof irrelevance must stay restricted to Prop — collapsing distinct \
         data-typed constants would be unsound"
    );
}

/// PROPERTY 2a. A value divergence the cited proof DEPENDS on fails closed —
/// and it fails at the KERNEL, not at the gate.
///
/// The shard says `Victim := 1` and proves `Victim = 1` by `rfl`; Clean's
/// resident says `Victim := 0` and is never replaced (the loader only adds
/// ABSENT names). The theorem is registered through checked
/// `Environment::add_decl` in the session environment, so its proof term is
/// re-checked against the RESIDENT reading and the type check fails. This is
/// why the gate does not need a value comparison: any divergence that matters
/// is caught by the kernel, on the real closure, after it is installed.
#[test]
fn test_value_divergent_resident_the_proof_depends_on_fails_closed() {
    // `Cited.thm : Victim = 1 := Eq.refl Nat 1` — true of the shard's `Victim`,
    // false of the resident's.
    let thm_type = Expr::app(
        Expr::app(
            Expr::app(const_at_type("Eq"), const_("Nat")),
            const_("Victim"),
        ),
        nat_one(),
    );
    let thm_value = Expr::app(
        Expr::app(const_at_type("Eq.refl"), const_("Nat")),
        nat_one(),
    );
    let env = install_value_divergent_fixture(&thm_type, &thm_value);

    let mut state = ProofState::new(env, thm_type);
    let result = mathverse_apply_named(&mut state, "Cited.thm", TrustGate::Strict);

    let detail = match result.expect_err("a value divergence the proof needs must fail closed") {
        TacticError::SearchExhausted { detail, .. } => detail,
        other => panic!("expected SearchExhausted, got {other:?}"),
    };
    assert!(
        detail.contains("checked registration for dependency"),
        "the refusal must come from checked `Environment::add_decl` — if this \
         ever reports something else, the loader has stopped re-checking what \
         it installs and the VALUE-substitution argument collapses: {detail}"
    );
    assert!(
        !state.is_complete(),
        "the goal must NOT be discharged against a body the shard did not carry"
    );
    assert!(
        state
            .env
            .get_const(&Name::from_string("Cited.thm"))
            .is_none(),
        "a refused citation must not leave the theorem registered"
    );
    clear_mathverse_library();
}

/// PROPERTY 2b, the other half, and the reason no value check is built: the
/// SAME divergent resident is admitted when the cited proof does not depend on
/// the divergence, and what closes is a theorem the kernel checked against
/// CLEAN's body.
///
/// Measured cost of the alternative: 177 of the 308-name Mathlib citation
/// population name a value-divergent resident (141 restricting to data-typed
/// ones), against a current 307/308 — and inspection showed every reachable
/// case to be the same function compiled differently, so the check would buy no
/// soundness. See the `# SCOPE` note on `validate_resident_type_agreement`.
///
/// The residual exposure this pins is a PROVENANCE defect, not a soundness one:
/// success is reported under the shard's name while the statement was checked
/// against the resident's reading. It is recorded, deliberately, as admitted.
#[test]
fn test_value_divergent_resident_the_proof_does_not_depend_on_still_closes() {
    // `Cited.thm : Victim = Victim := Eq.refl Nat Victim` — never unfolds
    // `Victim`, so it is true under either body.
    let thm_type = Expr::app(
        Expr::app(
            Expr::app(const_at_type("Eq"), const_("Nat")),
            const_("Victim"),
        ),
        const_("Victim"),
    );
    let thm_value = Expr::app(
        Expr::app(const_at_type("Eq.refl"), const_("Nat")),
        const_("Victim"),
    );
    let env = install_value_divergent_fixture(&thm_type, &thm_value);

    let mut state = ProofState::new(env, thm_type);
    mathverse_apply_named(&mut state, "Cited.thm", TrustGate::Strict)
        .expect("a value divergence the proof does not depend on must still close");
    assert!(state.is_complete(), "the goal is discharged");

    let resident_after = state
        .env
        .get_const(&Name::from_string("Victim"))
        .expect("Victim is still resident")
        .clone();
    assert_eq!(
        resident_after.value.as_ref(),
        Some(&const_("Nat.zero")),
        "the loader must not have replaced the resident — the citation stands on \
         CLEAN's body, which is exactly the provenance exposure being recorded"
    );
    assert!(
        state
            .env
            .get_const(&Name::from_string("Cited.thm"))
            .is_some(),
        "the cited theorem is registered, kernel-checked against that body"
    );
    clear_mathverse_library();
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for Lean-faithful elaborated TERM SHAPES — the
//! trust-ir Lean↔Clean bridge blocker B2 (the Bool-guarded `semIntBinOp`
//! division arms `UDiv`/`SDiv`/`URem`/`SRem`).
//!
//! ## Root cause (three coupled shape divergences)
//!
//! Real Lean 4 and clean agreed definitionally but not STRUCTURALLY on the
//! elaboration of the same source, so cross-encoding unification (a clean
//! `rfl`/`if_neg` against a `.olean`-imported real-Lean term) failed:
//!
//! 1. **Synthesized instance terms.** `init_instances_from_env` handed the
//!    resolver the instance constant's UNFOLDED VALUE, so `r == 0` elaborated
//!    with an inlined `BEq.mk (fun a b => Decidable.decide …)` structure
//!    literal where real Lean emits `instBEqOfDecidableEq Int
//!    Int.instDecidableEq`. Fixed: the resolver's fallback expression is the
//!    instance CONSTANT (Lean's `synthInstance` shape); whnf still unfolds it
//!    wherever a field is projected, so accepts are unchanged.
//! 2. **Candidate order.** Clean's unifier delta-unfolds non-reducible
//!    definitions, so a wrapper instance like lean-core's `Id.instOfNat :
//!    OfNat (Id α) n` — which real Lean's reducible-keyed discrimination tree
//!    never even considers for the goal `OfNat Int 0` — self-matched its own
//!    recursive subgoal up to the depth limit and buried `instOfNat` under 30+
//!    redundant wrappers. Fixed: within a priority tier, candidates whose
//!    conclusion has a rigid head-constant MISMATCH with the goal are demoted
//!    behind compatible ones (kept as a last resort, so completeness is
//!    preserved), and more exact head matches come first.
//! 3. **The Bool `if` lane.** `if (c : Bool) then t else e` lowered to
//!    `Bool.rec`, where real Lean coerces the condition through `c = true`
//!    and emits `@ite α (c = true) (instDecidableEqBool c true) t e`. Fixed:
//!    `mk_bool_if` produces the Lean shape whenever the environment can
//!    synthesize `Decidable (c = true)`, falling back to `Bool.rec` (never
//!    `sorry`) only when it cannot.
//!
//! Plus one name-resolution gap the pinned bridge statements exposed: bare
//! `false`/`true` (Lean's `export Bool (false true)`) fell through to
//! auto-implicit in imported environments, silently GENERALIZING
//! `(r == 0) = false` over an arbitrary Bool.

use crate::infer::ElabCtx;
use crate::{elaborate_decl_and_register, ElabResult};
use clean_kernel::{Environment, Expr, ExprKind, Level, Name};
use clean_parser::parse_file;

fn elaborate_all(env: &mut Environment, code: &str, label: &str) {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(env, decl);
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate, got: {result:?}"
        );
    }
}

fn def_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("{name} should have a value"))
}

fn count_const(expr: &Expr, needle: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == needle),
        ExprKind::App(f, a) => count_const(f, needle) + count_const(a, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const(ty, needle) + count_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const(ty, needle) + count_const(val, needle) + count_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => count_const(inner, needle),
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// 3. The Bool `if` lane
// ---------------------------------------------------------------------------

/// `if (b : Bool) then t else e` must lower to the real-Lean shape:
/// `@ite α (b = true) inst t e` — with the environment's decidable-equality
/// instance, NOT `Bool.rec`. (The native prelude carries
/// `instDecidableEqBool`, so the Lean lane fires.)
#[test]
fn test_bool_if_lowers_to_ite_over_eq_true() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "def boolIf (b : Bool) (x y : Nat) : Nat := if b then x else y\n",
        "bool-if",
    );
    let val = def_value(&env, "boolIf");
    assert_eq!(
        count_const(&val, "Bool.rec"),
        0,
        "Bool-guard if must not lower to Bool.rec when a Decidable instance exists, got {val:?}"
    );
    assert_eq!(count_const(&val, "ite"), 1, "expected one ite, got {val:?}");
    assert!(
        count_const(&val, "Eq") >= 1 && count_const(&val, "Bool.true") >= 1,
        "condition must be coerced to `b = true`, got {val:?}"
    );
    assert!(
        count_const(&val, "instDecidableEqBool") >= 1,
        "the Decidable instance must be the named constant (Lean shape), got {val:?}"
    );
}

/// Cross-lane definitional seal: the sugared Bool `if` and the explicit
/// Prop-lane `ite (b = true)` must produce the SAME term, so `rfl` closes the
/// equation with `b` open. Pre-fix the Bool lane produced `Bool.rec`, which is
/// NOT syntactically unifiable with `ite` on an open scrutinee.
#[test]
fn test_bool_if_cross_lane_rfl() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        r#"
def cleanIf (b : Bool) (x y : Nat) : Nat := if b then x else y

def leanIf (b : Bool) (x y : Nat) : Nat := ite (b = true) x y

theorem cross_lane_agree (b : Bool) (x y : Nat) : cleanIf b x y = leanIf b x y := rfl
"#,
        "cross-lane rfl",
    );
}

/// In an environment that cannot synthesize `Decidable (c = true)` at all,
/// the Bool `if` must still elaborate — via the definitional `Bool.rec`
/// fallback — and must NOT synthesize a `sorry`.
#[test]
fn test_bool_if_bool_rec_fallback_without_decidable_instance() {
    use clean_kernel::{Constructor, Declaration, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bool"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ty.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ty.clone(),
                },
            ],
        }],
    })
    .expect("Bool inductive should register");
    // `Eq` so the Lean lane's Decidable GOAL is at least well-formed; there is
    // still no Decidable type nor instance, so resolution must fail and the
    // fallback fire.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(
                    clean_kernel::BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::sort(Level::zero()),
                ),
            ),
        ),
    })
    .expect("Eq axiom should register");

    let mut env2 = env;
    let decls = parse_file("def pick (b : Bool) (x y : Bool) : Bool := if b then x else y\n")
        .expect("should parse");
    let result = elaborate_decl_and_register(&mut env2, &decls[0]);
    assert!(
        result.is_ok(),
        "Bool if must fall back to Bool.rec, got: {result:?}"
    );
    let val = def_value(&env2, "pick");
    assert!(
        count_const(&val, "Bool.rec") == 1 && count_const(&val, "ite") == 0,
        "expected the Bool.rec fallback shape, got {val:?}"
    );
    assert_eq!(
        count_const(&val, "sorryAx"),
        0,
        "the fallback must never synthesize sorry, got {val:?}"
    );
}

// ---------------------------------------------------------------------------
// 1. Synthesized instance terms are constants, not unfolded values
// ---------------------------------------------------------------------------

/// Resolution of a kernel-registered instance (registered without an explicit
/// type/value override, the `.olean`-import shape) must return the instance
/// CONSTANT — `instDecidableEqBool` — not its unfolded definition value
/// (`Bool.decEq`).
#[test]
fn test_resolve_instance_returns_const_ref() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let goal = Expr::app(
        Expr::const_(
            Name::from_string("DecidableEq"),
            vec![Level::succ(Level::zero())],
        ),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    let inst = ctx
        .resolve_instance(&goal)
        .expect("DecidableEq Bool should resolve in the prelude");
    let head = inst.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "instDecidableEqBool",
            "resolution must return the instance constant (Lean synthInstance shape), got {inst:?}"
        ),
        other => panic!("expected a constant head, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 2. Candidate order: rigid head mismatch is demoted
// ---------------------------------------------------------------------------

/// The isolated `Id.instOfNat` pathology: a wrapper instance over a
/// definitionally-transparent type former (`Wrap (MyId α)` with reducible-by-
/// unfolding `MyId α := α`), registered BEFORE the exact instance, must no
/// longer be chosen for a goal with a different rigid head. Pre-fix, `Wrap
/// Nat` resolved through `wrapMyId` recursively to the depth limit, producing
/// a 30+-deep wrapper stack around `wrapNat`; post-fix, `wrapNat` (exact head
/// match) is tried first and the result is the bare instance constant.
#[test]
fn test_candidate_order_demotes_rigid_head_mismatch() {
    use clean_kernel::env::{KernelClassInfo, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};
    use clean_kernel::{BinderInfo, Declaration};

    let mut env = Environment::with_prelude();
    let type0 = Expr::type_();
    let wrap = Name::from_string("Wrap");
    // Wrap : Type → Type (an opaque class carrier is enough for resolution).
    env.add_decl(Declaration::Axiom {
        name: wrap.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, type0.clone(), type0.clone()),
    })
    .expect("Wrap should register");
    // MyId (α : Type) : Type := α — definitionally transparent, like lean-core `Id`.
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyId"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, type0.clone(), type0.clone()),
        value: Expr::lam(BinderInfo::Default, type0.clone(), Expr::bvar(0)),
        is_reducible: true,
    })
    .expect("MyId should register");
    // wrapMyId : {α : Type} → [Wrap α] → Wrap (MyId α) — the wrapper.
    let wrap_const = Expr::const_(wrap.clone(), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("wrapMyId"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            type0.clone(),
            Expr::pi(
                BinderInfo::InstImplicit,
                Expr::app(wrap_const.clone(), Expr::bvar(0)),
                Expr::app(
                    wrap_const.clone(),
                    Expr::app(
                        Expr::const_(Name::from_string("MyId"), vec![]),
                        Expr::bvar(1),
                    ),
                ),
            ),
        ),
    })
    .expect("wrapMyId should register");
    // wrapNat : Wrap Nat — the exact instance.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("wrapNat"),
        level_params: vec![],
        type_: Expr::app(
            wrap_const.clone(),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .expect("wrapNat should register");

    env.register_class(KernelClassInfo {
        name: wrap.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    // The WRAPPER first — same priority, so pre-fix registration order made it
    // the first candidate tried.
    for inst in ["wrapMyId", "wrapNat"] {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(inst),
            class_name: wrap.clone(),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
    }

    let mut ctx = ElabCtx::new(&env);
    let goal = Expr::app(wrap_const, Expr::const_(Name::from_string("Nat"), vec![]));
    let inst = ctx
        .resolve_instance(&goal)
        .expect("Wrap Nat should resolve");
    assert_eq!(
        count_const(&inst, "wrapMyId"),
        0,
        "the MyId wrapper (rigid head mismatch with `Nat`) must be demoted \
         behind the exact-head instance, got {inst:?}"
    );
    match inst.get_app_fn().kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "wrapNat",
            "goal `Wrap Nat` must resolve to the exact-head instance, got {inst:?}"
        ),
        other => panic!("expected a constant head, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Bare `false` / `true` (Lean's `export Bool (false true)`)
// ---------------------------------------------------------------------------

/// In an environment WITHOUT root-level `true`/`false` definitions (the
/// `.olean`-import situation — Lean core only ships the `Bool.true` /
/// `Bool.false` constructors plus an elab-level `export`), a bare `false` in
/// a statement must resolve to the `Bool.false` constructor instead of being
/// auto-implicit-bound (which silently generalized the trust-ir bridge's
/// `(r == 0) = false` statements over an arbitrary Bool).
#[test]
fn test_bare_false_resolves_to_ctor_without_root_def() {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Bool"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ty.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ty.clone(),
                },
            ],
        }],
    })
    .expect("Bool inductive should register");
    assert!(
        env.get_const(&Name::from_string("false")).is_none(),
        "precondition: no root-level `false` in this environment"
    );

    let decls = parse_file("def f : Bool := false\n").expect("should parse");
    let result = elaborate_decl_and_register(&mut env, &decls[0]).expect("should elaborate");
    match &result {
        ElabResult::Definition { val, .. } => {
            assert_eq!(
                count_const(val, "Bool.false"),
                1,
                "bare `false` must resolve to the Bool.false constructor, got {val:?}"
            );
        }
        other => panic!("expected a definition, got {other:?}"),
    }
}

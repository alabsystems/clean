// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the instance-projection-as-premise lane
//! (`clean_auto::AutomationEngine::try_instance_projection_premises`, exercised
//! through `auto_prove_with_query` with a local typeclass instance in context).
//!
//! These tests live in `clean-cli/tests` (not `clean-auto/tests`) on purpose:
//! `clean-auto`'s dev-dependency graph pulls the sibling trust-cg / trust-ir
//! path-deps, whose hardcoded `clean-kernel` path collides during lockfile
//! resolution from a worktree. `clean-cli` depends only on `clean-auto`'s lib
//! (no trust-cg), so it drives the public API without that dep.
//!
//! SOUNDNESS (load-bearing): the projection lane is on the *search* side, not
//! the TCB. It projects a class's Prop-typed fields (its axioms) off a local
//! instance with the kernel `Proj(C, i, inst)` primitive, then closes the goal
//! with them. Every emitted term — each projection and the final proof — is
//! re-checked through the kernel here (`TypeChecker::infer_type` + `is_def_eq`
//! against the goal), so a test passes only when the proof *kernel-checks*,
//! never merely because `auto_prove_with_query` returned `Verified`. No `sorry`,
//! no axiom.

use std::time::Duration;

use clean_auto::{AutomationEngine, AutomationOutcome, AutomationQuery};
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType,
    KernelClassInfo, Level, LocalContext, Name, TypeChecker,
};

// ─── shared expression builders ────────────────────────────────────────────

fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn konst(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn level_one() -> Level {
    Level::succ(Level::zero())
}
/// `@Eq.{1} ty lhs rhs`.
fn eq1(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq"), vec![level_one()]),
        [ty.clone(), lhs.clone(), rhs.clone()],
    )
}

fn axiom(env: &mut Environment, n: &str, level_params: Vec<Name>, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: name(n),
        level_params,
        type_,
    })
    .unwrap_or_else(|e| panic!("axiom `{n}` should type-check: {e:?}"));
}

/// Base env: `Eq` (universe-poly), a carrier `M : Type`, an element `a : M`, and
/// an ABSTRACT unary op `op : M -> M` (so the class laws below are NOT trivially
/// true — the goal is unreachable without the instance's law).
fn base_env() -> Environment {
    let mut env = Environment::new();
    let u = || name("u");
    let su = || Expr::sort(Level::param(u()));
    let b = Expr::bvar;
    let d = BinderInfo::Default;

    // Eq : {α : Sort u} → α → α → Prop
    axiom(
        &mut env,
        "Eq",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), Expr::pi(d, b(1), Expr::prop()))),
    );
    axiom(&mut env, "M", vec![], Expr::type_()); // M : Type (Sort 1)
    axiom(&mut env, "a", vec![], konst("M")); // a : M
    axiom(&mut env, "op", vec![], Expr::pi(d, konst("M"), konst("M"))); // op : M → M
    env
}

/// Register the single-field class `Unit1` (no params):
///   class Unit1 where law : ∀ (x : M), @Eq M (op x) x
fn add_unit1(env: &mut Environment) {
    let d = BinderInfo::Default;
    // law : ∀ (x : M), @Eq M (op x) x   (M, op are globals → no bvar shift)
    let law_ty = Expr::pi(
        d,
        konst("M"),
        eq1(
            &konst("M"),
            &Expr::app(konst("op"), Expr::bvar(0)),
            &Expr::bvar(0),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("Unit1"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name("Unit1.mk"),
                type_: Expr::pi(d, law_ty, konst("Unit1")),
            }],
        }],
    })
    .expect("Unit1 inductive registers");
    env.register_structure_fields(name("Unit1"), vec![name("law")])
        .expect("Unit1 fields register");
    env.register_class(KernelClassInfo {
        name: name("Unit1"),
        num_params: 0,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Register the Monoid-shaped class `Mon` (1 param) with a DATA field `op` and a
/// Prop LAW field `unit`:
///   class Mon (α : Type) where op : α → α ; unit : ∀ (x:α), @Eq α (op x) x
fn add_mon(env: &mut Environment) {
    let d = BinderInfo::Default;
    let ty = Expr::type_();
    let mon = |a: Expr| Expr::app(konst("Mon"), a);
    // Mon : Type → Type
    let mon_ty = Expr::arrow(ty.clone(), ty.clone());
    // under α : op_ty = α → α   (α = bvar 0; codomain α under the arrow = bvar 1)
    let op_ty = Expr::pi(d, Expr::bvar(0), Expr::bvar(1));
    // under α, op : unit_ty = ∀ (x:α), @Eq α (op x) x
    //   x-binder domain α = bvar 1 (α); inside: α=bvar2, op=bvar1, x=bvar0
    let unit_ty = Expr::pi(
        d,
        Expr::bvar(1),
        eq1(
            &Expr::bvar(2),
            &Expr::app(Expr::bvar(1), Expr::bvar(0)),
            &Expr::bvar(0),
        ),
    );
    // Mon.mk : {α : Type} → (op : α→α) → (unit) → Mon α
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(d, op_ty, Expr::pi(d, unit_ty, mon(Expr::bvar(2)))),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name("Mon"),
            type_: mon_ty,
            constructors: vec![Constructor {
                name: name("Mon.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Mon inductive registers");
    env.register_structure_fields(name("Mon"), vec![name("op"), name("unit")])
        .expect("Mon fields register");
    env.register_class(KernelClassInfo {
        name: name("Mon"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Semigroup-shaped GRANDPARENT class `Sg` (1 param): a DATA field `op` and a
/// Prop LAW `sgLaw`. This is the parent whose law the transitive projection must
/// reach:  class Sg (α : Type) where op : α → α ; sgLaw : ∀ (x:α), @Eq α (op x) x
fn add_sg(env: &mut Environment) {
    let d = BinderInfo::Default;
    let ty = Expr::type_();
    let sg = |a: Expr| Expr::app(konst("Sg"), a);
    let sg_ty = Expr::arrow(ty.clone(), ty.clone());
    let op_ty = Expr::pi(d, Expr::bvar(0), Expr::bvar(1));
    // under α, op : sgLaw_ty = ∀ (x:α), @Eq α (op x) x
    //   x-binder domain α = bvar1; inside: α=bvar2, op=bvar1, x=bvar0
    let law_ty = Expr::pi(
        d,
        Expr::bvar(1),
        eq1(
            &Expr::bvar(2),
            &Expr::app(Expr::bvar(1), Expr::bvar(0)),
            &Expr::bvar(0),
        ),
    );
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(d, op_ty, Expr::pi(d, law_ty, sg(Expr::bvar(2)))),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name("Sg"),
            type_: sg_ty,
            constructors: vec![Constructor {
                name: name("Sg.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Sg inductive registers");
    env.register_structure_fields(name("Sg"), vec![name("op"), name("sgLaw")])
        .expect("Sg fields register");
    env.register_class(KernelClassInfo {
        name: name("Sg"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Monoid-shaped class `MonExt` (1 param) that EXTENDS `Sg`: its sole field is
/// the parent instance `toSg : Sg α` — a data-valued projection whose type head
/// is itself a class. It has NO law of its own; `sgLaw` lives on `Sg`, reachable
/// only *through* `MonExt.toSg`.  class MonExt (α : Type) extends Sg α
fn add_mon_ext(env: &mut Environment) {
    let d = BinderInfo::Default;
    let ty = Expr::type_();
    let mon = |a: Expr| Expr::app(konst("MonExt"), a);
    let mon_ty = Expr::arrow(ty.clone(), ty.clone());
    // under α: toSg : Sg α   (α = bvar0)
    let to_sg_ty = Expr::app(konst("Sg"), Expr::bvar(0));
    // MonExt.mk : {α : Type} → (toSg : Sg α) → MonExt α   (α = bvar1 in codomain)
    let mk_ty = Expr::pi(
        BinderInfo::Implicit,
        ty.clone(),
        Expr::pi(d, to_sg_ty, mon(Expr::bvar(1))),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: name("MonExt"),
            type_: mon_ty,
            constructors: vec![Constructor {
                name: name("MonExt.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("MonExt inductive registers");
    env.register_structure_fields(name("MonExt"), vec![name("toSg")])
        .expect("MonExt fields register");
    env.register_class(KernelClassInfo {
        name: name("MonExt"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Notation-wrapper structure `HMulU` (stands in for `HMul`): a single-field
/// structure whose projection `HMulU.hMul = Proj(HMulU, 0, ·)` is the analog of
/// `HMul.hMul`. A goal written `@HMulU.hMul instHMul a` (with `instHMul` wrapping
/// the class op) whnf-reduces to `inst.op a` — exactly the instance-notation
/// chain the whnf pre-pass must collapse. Not itself a class (never scanned as an
/// instance); only its projection is used, in the goal.
fn add_hmulu(env: &mut Environment) {
    let d = BinderInfo::Default;
    // HMulU.mk : (hMul : M → M) → HMulU
    let hmul_field_ty = Expr::pi(d, konst("M"), konst("M"));
    let mk_ty = Expr::pi(d, hmul_field_ty, konst("HMulU"));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("HMulU"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name("HMulU.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("HMulU inductive registers");
    env.register_structure_fields(name("HMulU"), vec![name("hMul")])
        .expect("HMulU fields register");
}

/// Kernel re-check gate: infer the proof term's type in `ctx` and require it
/// def-eq to `goal`.
fn assert_kernel_checks(env: &Environment, ctx: &LocalContext, term: &Expr, goal: &Expr) {
    let tc = TypeChecker::with_context(env, ctx.clone());
    let inferred = tc
        .infer_type(term)
        .unwrap_or_else(|e| panic!("projection proof failed to type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, goal),
        "projection proof kernel-checks to {inferred:?}, not the goal {goal:?}"
    );
}

fn goal_op_a_eq_a() -> Expr {
    eq1(
        &konst("M"),
        &Expr::app(konst("op"), konst("a")),
        &konst("a"),
    )
}

// ─── baseline: the "before" state the lane newly closes ────────────────────

/// Without an instance in context, `op a = a` is unprovable: `op` is abstract
/// and no law is in scope, so the routed engines have nothing to chain.
#[test]
fn test_projection_baseline_unprovable_without_instance() {
    let mut env = base_env();
    add_unit1(&mut env);
    add_mon(&mut env);
    let engine = AutomationEngine::new();
    let goal = goal_op_a_eq_a();
    let outcome =
        engine.auto_prove_with_query(&env, AutomationQuery::new(&goal, Duration::from_secs(20)));
    assert!(
        !matches!(outcome, AutomationOutcome::Verified(_)),
        "`op a = a` must be unprovable with no instance in context"
    );
}

// ─── Test A: single-field class, direct is_def_eq closer (single-lemma leaf) ─

/// With `[inst : Unit1]` in context, the lane projects the sole Prop field
/// `law : ∀ x, op x = x` as `Proj(Unit1, 0, inst)`, the DIRECT closer specialises
/// it to `a`, and the proof `Proj(Unit1,0,inst) a` KERNEL-CHECKS against
/// `op a = a`. The proof term itself must be that projection (proving the lane —
/// not some other engine — closed it).
#[test]
fn test_projection_single_field_leaf_direct_defeq_kernel_checked() {
    let mut env = base_env();
    add_unit1(&mut env);
    let engine = AutomationEngine::new();
    let goal = goal_op_a_eq_a();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(name("inst"), konst("Unit1"), BinderInfo::InstImplicit);

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!("projection lane should prove `op a = a`, got {other:?}"),
    };

    // The proof must actually go through the projection primitive on `inst`.
    let repr = format!("{:?}", result.proof_term());
    assert!(
        repr.contains("Proj") && repr.contains(&format!("FVarId({})", inst.as_u64())),
        "proof term must be a projection of the instance fvar, got {repr}"
    );

    // SOUNDNESS GATE.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

// ─── Test B: Monoid-shaped class, data field skipped, law field used ────────

/// With `[inst : Mon M]` in context, the lane must SKIP the data field `op`
/// (`M → M` : Type, not a Prop axiom) and project only the Prop law
/// `unit : ∀ x, (inst.op) x = x`, then close `inst.op a = a`. The proof
/// KERNEL-CHECKS.
#[test]
fn test_projection_monoid_shaped_skips_data_field_kernel_checked() {
    let mut env = base_env();
    add_mon(&mut env);
    let engine = AutomationEngine::new();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(
        name("inst"),
        Expr::app(konst("Mon"), konst("M")),
        BinderInfo::InstImplicit,
    );
    // goal: @Eq M (Proj(Mon,0,inst) a) a   (i.e. `inst.op a = a`)
    let proj_op = Expr::proj(name("Mon"), 0, Expr::fvar(inst));
    let goal = eq1(&konst("M"), &Expr::app(proj_op, konst("a")), &konst("a"));

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!("projection lane should prove `inst.op a = a`, got {other:?}"),
    };

    // SOUNDNESS GATE.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

// ─── Test C: transitive parent-projection (Monoid → Semigroup grandparent) ──

/// With `[inst : MonExt M]` in context (a class that EXTENDS `Sg`), the law the
/// goal needs — `sgLaw` — is NOT a field of `MonExt`; it lives on the grandparent
/// `Sg`, reachable only through the parent-instance projection `MonExt.toSg`. The
/// transitive scan must project `toSg` (a data field whose type head `Sg` is a
/// class), RECURSE into it, and surface `Proj(Sg, 1, Proj(MonExt, 0, inst))` — the
/// `sgLaw` law — which the direct closer specialises to `a`. The proof
/// `Proj(Sg,1,Proj(MonExt,0,inst)) a` KERNEL-CHECKS against `inst.toSg.op a = a`.
#[test]
fn test_projection_transitive_parent_reaches_grandparent_law_kernel_checked() {
    let mut env = base_env();
    add_sg(&mut env);
    add_mon_ext(&mut env);
    let engine = AutomationEngine::new();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(
        name("inst"),
        Expr::app(konst("MonExt"), konst("M")),
        BinderInfo::InstImplicit,
    );

    // goal: @Eq M ((inst.toSg).op a) a  =  @Eq M (Proj(Sg,0,Proj(MonExt,0,inst)) a) a
    let to_sg = Expr::proj(name("MonExt"), 0, Expr::fvar(inst));
    let sg_op = Expr::proj(name("Sg"), 0, to_sg);
    let goal = eq1(&konst("M"), &Expr::app(sg_op, konst("a")), &konst("a"));

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!("transitive projection should prove `inst.toSg.op a = a`, got {other:?}"),
    };

    // The proof must project the instance fvar through the parent chain (nested
    // `Proj`), not close by some unrelated route.
    let repr = format!("{:?}", result.proof_term());
    assert!(
        repr.contains("Proj") && repr.contains(&format!("FVarId({})", inst.as_u64())),
        "proof must project the instance fvar through the parent chain, got {repr}"
    );

    // SOUNDNESS GATE.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

// ─── Test D: whnf pre-pass normalizes a heterogeneous-operator goal ─────────

/// The goal is written with the notation wrapper `@HMulU.hMul instHMul a` (the
/// stand-in for `a * 1` = `@HMul.hMul … instMul a …`), whose operator head is
/// `Proj(HMulU, 0, …)` — syntactically DIFFERENT from the projected law's
/// `Proj(Mon, 0, inst)`, so the first-order matcher misses it head-on. Only after
/// the whnf pre-pass reduces `instHMul` (`= HMulU.mk (inst.op)`) does the goal
/// become `inst.op a = a`, which the projected `Mon.unit` law then closes. The
/// proof KERNEL-CHECKS against the ORIGINAL (un-normalized) goal — `is_def_eq`
/// bridges the notation, so normalization only widens matching, never trust.
#[test]
fn test_projection_whnf_normalizes_heterogeneous_operator_kernel_checked() {
    let mut env = base_env();
    add_mon(&mut env);
    add_hmulu(&mut env);
    let engine = AutomationEngine::new();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(
        name("inst"),
        Expr::app(konst("Mon"), konst("M")),
        BinderInfo::InstImplicit,
    );

    // instHMul := HMulU.mk (inst.op)   where inst.op = Proj(Mon,0,inst) : M → M
    let inst_op = Expr::proj(name("Mon"), 0, Expr::fvar(inst));
    let inst_hmul = Expr::app(konst("HMulU.mk"), inst_op);
    // goal: @Eq M (@HMulU.hMul instHMul a) a  =  @Eq M (Proj(HMulU,0,instHMul) a) a
    let hmul_op = Expr::proj(name("HMulU"), 0, inst_hmul);
    let goal = eq1(&konst("M"), &Expr::app(hmul_op, konst("a")), &konst("a"));

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!("whnf pre-pass should close the HMulU goal, got {other:?}"),
    };

    // SOUNDNESS GATE — re-checked against the ORIGINAL heterogeneous-operator goal.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

// ─── Test E: SUB-POSITION rewrite of a SURFACE-notation law (`(a*1)*b = a*b`) ─

/// Binary notation-wrapper structure `HBin` (stands in for `HMul`): a single
/// binary field `hMul : M → M → M`. Its projection `Proj(HBin, 0, ·)` is the
/// analog of `HMul.hMul`; `@HBin.hMul (HBin.mk f) x y` whnf-reduces to `f x y`.
/// Not itself a class — its projection appears in BOTH the goal and, crucially,
/// the *surface-notation law* of `MonB` below.
fn add_hbin(env: &mut Environment) {
    let d = BinderInfo::Default;
    // HBin.mk : (hMul : M → M → M) → HBin
    let hmul_field_ty = Expr::pi(d, konst("M"), Expr::pi(d, konst("M"), konst("M")));
    let mk_ty = Expr::pi(d, hmul_field_ty, konst("HBin"));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("HBin"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name("HBin.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("HBin inductive registers");
    env.register_structure_fields(name("HBin"), vec![name("hMul")])
        .expect("HBin fields register");
}

/// Monomorphic `Monoid`-shaped class `MonB` (no params) over the concrete carrier
/// `M`: DATA fields `mul`(0) `M→M→M`, `one`(1) `M`, and a Prop LAW `mul_one`(2)
/// STATED IN SURFACE `HBin` NOTATION —
///   `mul_one : ∀ (x:M), @HBin.hMul (HBin.mk mul) x one = x`.
/// Projected off an instance, its type therefore carries the SURFACE `HBin.hMul`
/// head (`Proj(HBin,0, HBin.mk (inst.mul))`), NOT the class-op `Proj(MonB,0,·)`
/// head — mirroring how real Mathlib's `Monoid.mul_one` is stated with
/// `@HMul.hMul`/`@OfNat.ofNat` rather than the raw class operator. This is what
/// forces the sub-position rewrite to align a SURFACE-notation law against a
/// SURFACE-notation goal, which the whnf-normalized goal (class-op heads) defeats.
fn add_monb(env: &mut Environment) {
    let d = BinderInfo::Default;
    let m = konst("M");
    // Under [mul, one]: `mul_one : ∀ (x:M), @HBin.hMul (HBin.mk mul) x one = x`.
    //   Inside [mul, one, x]: mul = bvar2, one = bvar1, x = bvar0.
    let star = Expr::proj(name("HBin"), 0, Expr::app(konst("HBin.mk"), Expr::bvar(2)));
    let mul_one_lhs = Expr::apps(star, [Expr::bvar(0), Expr::bvar(1)]);
    let mul_one_ty = Expr::pi(d, m.clone(), eq1(&m, &mul_one_lhs, &Expr::bvar(0)));
    // MonB.mk : (mul : M→M→M) → (one : M) → (mul_one) → MonB
    let mul_field_ty = Expr::pi(d, m.clone(), Expr::pi(d, m.clone(), m.clone()));
    let mk_ty = Expr::pi(
        d,
        mul_field_ty,
        Expr::pi(d, m.clone(), Expr::pi(d, mul_one_ty, konst("MonB"))),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("MonB"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name("MonB.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("MonB inductive registers");
    env.register_structure_fields(
        name("MonB"),
        vec![name("mul"), name("one"), name("mul_one")],
    )
    .expect("MonB fields register");
    env.register_class(KernelClassInfo {
        name: name("MonB"),
        num_params: 0,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// The G2 shape. With `[inst : MonB]` in context, `(a * 1) * b = a * b` — written
/// in SURFACE `HBin` notation (`@HBin.hMul (HBin.mk (inst.mul)) …`) — is closed by
/// the instance-projection REWRITE closer (`try_project_law_rewrite`). The direct
/// whole-goal closer cannot: `mul_one` must be matched at the SUB-position `a * 1`
/// (not the whole goal) and lifted through the outer `· * b` congruence.
///
/// The load-bearing detail: the projected `mul_one` law is in SURFACE `HBin.hMul`
/// notation, and the pre-fix rewrite lane searched ONLY the whnf-normalized goal
/// (whose `HBin.hMul` heads collapse to the class-op `Proj(MonB,0,inst)`), so the
/// surface-headed law never matched the class-op-headed sub-terms → `Unsolved`.
/// The fix ALSO searches the RAW goal (surface heads intact), where `mul_one`
/// aligns at `a * 1`, rewrites it to `a` via `congr`/`congrArg`, and closes the
/// residual `a * b = a * b` by reflexivity. Every term is kernel-checked; the
/// final `Eq.trans (congr …) (Eq.refl …)` re-checks against the ORIGINAL goal.
#[test]
fn test_projection_subposition_rewrite_surface_notation_kernel_checked() {
    // Unlike Tests A–D (which use the DIRECT closer — it only ever APPLIES a
    // projected law term, needing nothing but `Eq`), the multi-step rewrite closer
    // EMITS genuine `Eq.trans (congr/congrArg …) (Eq.refl …)` terms and re-checks
    // them. So this env carries the real `Eq` congruence prelude (via `init_eq`:
    // `Eq`/`Eq.refl`/`Eq.trans`/`congr`/`congrArg`) rather than `base_env`'s bare
    // `Eq` axiom — the same prelude the paragon bench's `tc_base_env` installs.
    let mut env = Environment::new();
    env.init_eq()
        .expect("init_eq installs the Eq congruence prelude");
    axiom(&mut env, "M", vec![], Expr::type_()); // M : Type (Sort 1)
    axiom(&mut env, "a", vec![], konst("M")); // a : M
    axiom(&mut env, "b", vec![], konst("M")); // b : M
    add_hbin(&mut env);
    add_monb(&mut env);
    let engine = AutomationEngine::new();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(name("inst"), konst("MonB"), BinderInfo::InstImplicit);

    // Surface `*` := `Proj(HBin, 0, HBin.mk (inst.mul))`; `1` := `inst.one`.
    let inst_mul = Expr::proj(name("MonB"), 0, Expr::fvar(inst));
    let inst_one = Expr::proj(name("MonB"), 1, Expr::fvar(inst));
    let star = Expr::proj(name("HBin"), 0, Expr::app(konst("HBin.mk"), inst_mul));
    let mul = |x: Expr, y: Expr| Expr::apps(star.clone(), [x, y]);
    // goal: @Eq M ((a * 1) * b) (a * b)   — needs `mul_one` under a congruence.
    let goal = eq1(
        &konst("M"),
        &mul(mul(konst("a"), inst_one), konst("b")),
        &mul(konst("a"), konst("b")),
    );

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!(
            "sub-position rewrite closer should prove `(a*1)*b = a*b` in surface \
             notation, got {other:?}"
        ),
    };

    // The proof must be a genuine rewrite (transitivity through a congruence),
    // not a bare projection — i.e. the REWRITE closer, not the direct one, closed it.
    let repr = format!("{:?}", result.proof_term());
    assert!(
        repr.contains("Eq.trans") || repr.contains("congr"),
        "proof must rewrite `mul_one` at the `a*1` sub-position under a congruence, \
         got {repr}"
    );

    // SOUNDNESS GATE — re-checked against the ORIGINAL surface-notation goal.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

// ─── Test E′: the `1` as real-Mathlib `@OfNat.ofNat _ (Lit 1) _` (fo_match Lit arm) ─

/// Opaque analogs of Lean's `OfNat` class and its `ofNat` projection, so a class
/// `1` can be written the way REAL Mathlib emits it — `@OfNat.ofNat M (Lit 1)
/// inst` — a `Const`-application carrying a structural `Lit(Nat 1)` node, NOT the
/// bare `Proj(MonB, 1, inst)` Test E uses. Both are added as axioms (a faithful
/// stand-in for the projection function); keeping `OfNat.ofNat` opaque guarantees
/// the `Lit 1` node survives whnf into the matcher.
///   `OfNat        : Type → Nat → Type`
///   `OfNat.ofNat  : (α : Type) → (n : Nat) → OfNat α n → α`
fn add_ofnat_axioms(env: &mut Environment) {
    let d = BinderInfo::Default;
    let ty = Expr::type_();
    let nat = konst("Nat");
    // OfNat : Type → Nat → Type
    axiom(
        env,
        "OfNat",
        vec![],
        Expr::pi(d, ty.clone(), Expr::pi(d, nat.clone(), ty.clone())),
    );
    // OfNat.ofNat : (α : Type) → (n : Nat) → OfNat α n → α
    //   under [α, n, inst]: the `OfNat α n` domain has α = bvar1, n = bvar0;
    //   the codomain α (3 binders deep) = bvar2.
    let ofnat_at = Expr::apps(konst("OfNat"), [Expr::bvar(1), Expr::bvar(0)]);
    let ofnat_ofnat_ty = Expr::pi(
        d,
        ty.clone(),
        Expr::pi(d, nat, Expr::pi(d, ofnat_at, Expr::bvar(2))),
    );
    axiom(env, "OfNat.ofNat", vec![], ofnat_ofnat_ty);
}

/// `MonB` restated so its `1` is `@OfNat.ofNat M (Lit 1) ofNatOne` — the shape
/// real Mathlib emits — instead of a bare `one` field. DATA fields `mul`(0)
/// `M→M→M` and `ofNatOne`(1) `OfNat M 1` (the numeric-one *instance*), and a Prop
/// LAW `mul_one`(2):
///   `mul_one : ∀ (x:M), @HBin.hMul (HBin.mk mul) x (@OfNat.ofNat M (Lit 1) ofNatOne) = x`.
/// Projected off an instance, the law's `1` is therefore
/// `@OfNat.ofNat M (Lit 1) (Proj(MonBof,1,inst))` — a `Lit(Nat 1)` node inside the
/// projected pattern, exactly as `Monoid.mul_one` carries on real Mathlib. The
/// sub-position rewrite's first-order matcher (`fo_match`) must therefore align
/// the goal's `a*1` against the law THROUGH that literal — the `Lit` arm the G2
/// fix added (engine_induction_match.rs). With a bare-`Proj` `1` (Test E) that arm
/// never fires.
fn add_monb_ofnat(env: &mut Environment) {
    let d = BinderInfo::Default;
    let m = konst("M");
    // Under [mul, ofNatOne, x]: mul = bvar2, ofNatOne = bvar1, x = bvar0.
    let star = Expr::proj(name("HBin"), 0, Expr::app(konst("HBin.mk"), Expr::bvar(2)));
    // `1` := @OfNat.ofNat M (Lit 1) ofNatOne
    let one = Expr::apps(
        konst("OfNat.ofNat"),
        [m.clone(), Expr::nat_lit(1), Expr::bvar(1)],
    );
    let mul_one_lhs = Expr::apps(star, [Expr::bvar(0), one]);
    let mul_one_ty = Expr::pi(d, m.clone(), eq1(&m, &mul_one_lhs, &Expr::bvar(0)));
    // MonBof.mk : (mul : M→M→M) → (ofNatOne : OfNat M 1) → (mul_one) → MonBof
    let mul_field_ty = Expr::pi(d, m.clone(), Expr::pi(d, m.clone(), m.clone()));
    let ofnat_one_field_ty = Expr::apps(konst("OfNat"), [m.clone(), Expr::nat_lit(1)]);
    let mk_ty = Expr::pi(
        d,
        mul_field_ty,
        Expr::pi(
            d,
            ofnat_one_field_ty,
            Expr::pi(d, mul_one_ty, konst("MonBof")),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name("MonBof"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name("MonBof.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("MonBof inductive registers");
    env.register_structure_fields(
        name("MonBof"),
        vec![name("mul"), name("ofNatOne"), name("mul_one")],
    )
    .expect("MonBof fields register");
    env.register_class(KernelClassInfo {
        name: name("MonBof"),
        num_params: 0,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Test E with the load-bearing change that makes the COMMITTED suite exercise
/// the fo_match `Lit` arm (fix half #2, the exact node that distinguishes real
/// Mathlib): the `1` in `(a*1)*b = a*b` is the real-Mathlib-shaped
/// `@OfNat.ofNat M (Lit 1) inst.ofNatOne` — a `Const`-application over a structural
/// `Lit(Nat 1)` — not a bare `Proj`. So when the sub-position rewrite closer aligns
/// the projected `mul_one` law against the `a*1` sub-position, `fo_match` recurses
/// into `(Lit 1) =?= (Lit 1)`, which without the `Lit` arm hits `_ => false` and
/// the rewrite (and hence the whole proof) is lost. Reverting the `Lit` arm makes
/// this test FAIL (verified by deleting that match arm and re-running: the goal
/// goes `Unsolved`), so the committed suite genuinely guards fix half #2. Every
/// emitted term is kernel-checked against the ORIGINAL goal, as ever.
#[test]
fn test_projection_subposition_rewrite_ofnat_literal_kernel_checked() {
    let mut env = Environment::new();
    env.init_eq()
        .expect("init_eq installs the Eq congruence prelude");
    env.init_nat()
        .expect("init_nat installs Nat (for the Lit 1 node)");
    axiom(&mut env, "M", vec![], Expr::type_()); // M : Type (Sort 1)
    axiom(&mut env, "a", vec![], konst("M")); // a : M
    axiom(&mut env, "b", vec![], konst("M")); // b : M
    add_hbin(&mut env);
    add_ofnat_axioms(&mut env);
    add_monb_ofnat(&mut env);
    let engine = AutomationEngine::new();

    let mut ctx = LocalContext::new();
    let inst = ctx.push(name("inst"), konst("MonBof"), BinderInfo::InstImplicit);

    // Surface `*` := `Proj(HBin, 0, HBin.mk (inst.mul))`;
    // `1` := `@OfNat.ofNat M (Lit 1) (inst.ofNatOne)`  — the real-Mathlib shape.
    let inst_mul = Expr::proj(name("MonBof"), 0, Expr::fvar(inst));
    let inst_ofnat_one = Expr::proj(name("MonBof"), 1, Expr::fvar(inst));
    let star = Expr::proj(name("HBin"), 0, Expr::app(konst("HBin.mk"), inst_mul));
    let mul = |x: Expr, y: Expr| Expr::apps(star.clone(), [x, y]);
    let one = Expr::apps(
        konst("OfNat.ofNat"),
        [konst("M"), Expr::nat_lit(1), inst_ofnat_one],
    );
    // goal: @Eq M ((a * 1) * b) (a * b) — the `1` carries a Lit(Nat 1) node.
    let goal = eq1(
        &konst("M"),
        &mul(mul(konst("a"), one), konst("b")),
        &mul(konst("a"), konst("b")),
    );

    let outcome = engine.auto_prove_with_query(
        &env,
        AutomationQuery::new(&goal, Duration::from_secs(20)).with_local_ctx(&ctx),
    );
    let result = match outcome {
        AutomationOutcome::Verified(r) => r,
        other => panic!(
            "sub-position rewrite closer should prove `(a*1)*b = a*b` with an \
             `@OfNat.ofNat _ (Lit 1) _` one, got {other:?}"
        ),
    };

    // The proof must be a genuine rewrite (transitivity through a congruence).
    let repr = format!("{:?}", result.proof_term());
    assert!(
        repr.contains("Eq.trans") || repr.contains("congr"),
        "proof must rewrite `mul_one` at the `a*1` sub-position under a congruence, \
         got {repr}"
    );

    // SOUNDNESS GATE — re-checked against the ORIGINAL surface-notation goal.
    assert_kernel_checks(&env, &ctx, result.proof_term(), &goal);
}

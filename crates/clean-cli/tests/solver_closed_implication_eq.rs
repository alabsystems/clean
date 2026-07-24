// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for the closed equality-implication solver weak areas.
//!
//! Both confirmed weak areas are *closed-implication* equality goals — the
//! antecedents are part of the goal rather than the local context:
//!
//!   * Weak area 1: transitivity chains
//!     `e0=e1 → e1=e2 → … → e_{k-1}=ek → e0=ek` (k = 2..10).
//!   * Weak area 2: congruence `a=b → f(a)=f(b)` and variants.
//!
//! Before the fix, `AutomationEngine::auto_prove` returned `None` for every one
//! of these shapes (clean-smt's reconstruction failed with "Implies(P, Q) — Q not
//! provable", clean-superposition saturated). The fix introduces the implication
//! antecedents as tracked hypotheses and reuses the open-form equality machinery.
//!
//! This test lives in `clean-cli/tests` (not `clean-auto/tests`) because
//! clean-auto's dev-dependency graph pulls the sibling trust-cg / trust-ir
//! path-deps, whose `clean-kernel` path-dep collides with a non-`~/clean`
//! worktree during lockfile resolution. clean-cli has no such dev-deps and
//! re-exports `clean_auto` through its normal dependency.
//!
//! SOUNDNESS: the solver is on the search side, not the TCB. Every proof it
//! returns is independently re-checked here via `TypeChecker::infer_type` +
//! `is_def_eq` against the original goal. A test passes only when the emitted
//! term *kernel-checks*, never merely because `auto_prove` returned `Some`.

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, Level, TypeChecker};

/// Universe level `1` (the universe of `A : Type`).
fn level_one() -> Level {
    Level::succ(Level::zero())
}

/// `@Eq.{lvl} ty lhs rhs`.
fn eq_at(lvl: Level, ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![lvl]), ty.clone()),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// `@Eq.{1} A lhs rhs` — equality of elements of the base type `A`.
fn eq_a(lhs: &Expr, rhs: &Expr) -> Expr {
    eq_at(level_one(), &ty_a(), lhs, rhs)
}

fn ty_a() -> Expr {
    Expr::const_(Name::from_string("A"), vec![])
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn axiom(env: &mut Environment, name: &str, level_params: Vec<Name>, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params,
        type_,
    })
    .unwrap_or_else(|e| panic!("faithful env axiom `{name}` should type-check: {e:?}"));
}

/// Build a faithful kernel environment with `Eq` and its lemmas (`Eq.refl`,
/// `Eq.symm`, `Eq.trans`, `congrArg`, `congr`) declared with their genuine Lean
/// types, plus a base type `A`, elements `e0..e10`/`a`/`b`/`c`, and functions
/// `f`/`g`/`h`. All binder de Bruijn indices are spelled out so the reconstructed
/// proof terms actually kernel-check.
fn build_env() -> Environment {
    let mut env = Environment::new();
    let u = || Name::from_string("u");
    let v = || Name::from_string("v");
    let su = || Expr::sort(Level::param(u()));
    let sv = || Expr::sort(Level::param(v()));
    let pu = || Level::param(u());
    let pv = || Level::param(v());
    let b = Expr::bvar;
    let d = BinderInfo::Default;

    // Eq : {α : Sort u} → α → α → Prop
    axiom(
        &mut env,
        "Eq",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), Expr::pi(d, b(1), Expr::prop()))),
    );

    // Eq.refl : {α : Sort u} → (a : α) → @Eq.{u} α a a
    axiom(
        &mut env,
        "Eq.refl",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), eq_at(pu(), &b(1), &b(0), &b(0)))),
    );

    // Eq.symm : {α : Sort u} → {a b : α} → @Eq.{u} α a b → @Eq.{u} α b a
    axiom(
        &mut env,
        "Eq.symm",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        eq_at(pu(), &b(2), &b(1), &b(0)),
                        eq_at(pu(), &b(3), &b(1), &b(2)),
                    ),
                ),
            ),
        ),
    );

    // Eq.trans : {α}{a b c} → @Eq α a b → @Eq α b c → @Eq α a c
    axiom(
        &mut env,
        "Eq.trans",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            eq_at(pu(), &b(3), &b(2), &b(1)),
                            Expr::pi(
                                d,
                                eq_at(pu(), &b(4), &b(2), &b(1)),
                                eq_at(pu(), &b(5), &b(4), &b(2)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    // congrArg : {α : Sort u}{β : Sort v}{a₁ a₂ : α} (f : α → β)
    //            → @Eq.{u} α a₁ a₂ → @Eq.{v} β (f a₁) (f a₂)
    axiom(
        &mut env,
        "congrArg",
        vec![u(), v()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                sv(),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            // f : α → β. `arrow` does not lift its codomain, so β
                            // (bvar2 here) is referenced as bvar3 under the arrow binder.
                            Expr::arrow(b(3), b(3)),
                            Expr::pi(
                                d,
                                eq_at(pu(), &b(4), &b(2), &b(1)),
                                eq_at(pv(), &b(4), &Expr::app(b(1), b(3)), &Expr::app(b(1), b(2))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    // congr : {α : Sort u}{β : Sort v}{f₁ f₂ : α → β}{a₁ a₂ : α}
    //         → @Eq.{imax u v} (α → β) f₁ f₂ → @Eq.{u} α a₁ a₂
    //         → @Eq.{v} β (f₁ a₁) (f₂ a₂)
    let imax = Level::imax(pu(), pv());
    axiom(
        &mut env,
        "congr",
        vec![u(), v()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                sv(),
                Expr::pi(
                    d,
                    // f₁ : α → β. β (bvar0) is bvar1 under the arrow binder.
                    Expr::arrow(b(1), b(1)),
                    Expr::pi(
                        d,
                        // f₂ : α → β. β (bvar1) is bvar2 under the arrow binder.
                        Expr::arrow(b(2), b(2)),
                        Expr::pi(
                            d,
                            b(3),
                            Expr::pi(
                                d,
                                b(4),
                                Expr::pi(
                                    d,
                                    // Eq over `α → β`: β (bvar4) is bvar5 under the arrow binder.
                                    eq_at(imax, &Expr::arrow(b(5), b(5)), &b(3), &b(2)),
                                    Expr::pi(
                                        d,
                                        eq_at(pu(), &b(6), &b(2), &b(1)),
                                        eq_at(
                                            pv(),
                                            &b(6),
                                            &Expr::app(b(5), b(3)),
                                            &Expr::app(b(4), b(2)),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    // Base type A : Type.
    axiom(&mut env, "A", vec![], Expr::type_());

    // Elements e0..e10, a, b, c : A.
    let elem_ty = ty_a();
    for i in 0..=10 {
        axiom(&mut env, &format!("e{i}"), vec![], elem_ty.clone());
    }
    for name in ["a", "b", "c"] {
        axiom(&mut env, name, vec![], elem_ty.clone());
    }

    // Unary functions f, g : A → A.
    for name in ["f", "g"] {
        axiom(&mut env, name, vec![], Expr::arrow(ty_a(), ty_a()));
    }
    // Binary function h : A → A → A.
    axiom(
        &mut env,
        "h",
        vec![],
        Expr::arrow(ty_a(), Expr::arrow(ty_a(), ty_a())),
    );

    env
}

/// Fold a list of closed antecedents into a non-dependent implication ending in
/// `consequent`: `H1 → H2 → … → Hn → consequent`.
fn implication(antecedents: &[Expr], consequent: &Expr) -> Expr {
    antecedents
        .iter()
        .rev()
        .fold(consequent.clone(), |acc, ante| {
            Expr::pi(BinderInfo::Default, ante.clone(), acc)
        })
}

/// Run `auto_prove` and kernel-check the emitted proof against `goal`.
///
/// Returns `Ok(())` only when a proof term is produced *and* its inferred type
/// is definitionally equal to `goal` under the kernel (empty context, since the
/// goal is closed). This is the soundness gate the test asserts on.
fn prove_and_kernel_check(env: &Environment, goal: &Expr, label: &str) {
    let engine = AutomationEngine::new();
    let result = engine.auto_prove(env, goal, Duration::from_secs(20), None);
    let proof =
        result.unwrap_or_else(|| panic!("auto_prove returned None for {label} (still unsolved)"));
    let proof_term = proof.proof_term();

    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(proof_term)
        .unwrap_or_else(|e| panic!("proof term for {label} failed to infer a type: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, goal),
        "proof term for {label} kernel-checks to {inferred:?}, not the goal {goal:?}"
    );
}

#[test]
fn faithful_env_is_kernel_sound() {
    // Guard: a hand-built `fun h1 h2 => Eq.trans A a b c h1 h2` must kernel-check
    // against `a=b → b=c → a=c`, and `fun h => congrArg A A a b f h` against
    // `a=b → f a = f b`. If these fail, the test env is wrong (not the fix).
    let env = build_env();
    let tc = TypeChecker::new(&env);
    let (a, b, c, f) = (konst("a"), konst("b"), konst("c"), konst("f"));
    let one = level_one();

    let trans_goal = implication(&[eq_a(&a, &b), eq_a(&b, &c)], &eq_a(&a, &c));
    // fun (h1 : a=b) (h2 : b=c) => @Eq.trans.{1} A a b c h1 h2  (h1=bvar1, h2=bvar0)
    let trans_term = {
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]);
        let applied = [&ty_a(), &a, &b, &c, &Expr::bvar(1), &Expr::bvar(0)]
            .into_iter()
            .fold(eq_trans, |acc, arg| Expr::app(acc, arg.clone()));
        Expr::lam(
            BinderInfo::Default,
            eq_a(&a, &b),
            Expr::lam(BinderInfo::Default, eq_a(&b, &c), applied),
        )
    };
    let inferred = tc
        .infer_type(&trans_term)
        .expect("hand-built Eq.trans proof should infer a type");
    assert!(
        tc.is_def_eq(&inferred, &trans_goal),
        "faithful env: hand-built Eq.trans proof must prove a=b → b=c → a=c"
    );

    let congr_goal = implication(
        &[eq_a(&a, &b)],
        &eq_a(
            &Expr::app(f.clone(), a.clone()),
            &Expr::app(f.clone(), b.clone()),
        ),
    );
    // fun (h : a=b) => @congrArg.{1,1} A A a b f h   (h = bvar0)
    let congr_term = {
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]);
        let applied = [&ty_a(), &ty_a(), &a, &b, &f, &Expr::bvar(0)]
            .into_iter()
            .fold(congr_arg, |acc, arg| Expr::app(acc, arg.clone()));
        Expr::lam(BinderInfo::Default, eq_a(&a, &b), applied)
    };
    let inferred = tc
        .infer_type(&congr_term)
        .expect("hand-built congrArg proof should infer a type");
    assert!(
        tc.is_def_eq(&inferred, &congr_goal),
        "faithful env: hand-built congrArg proof must prove a=b → f a = f b"
    );
}

#[test]
fn weak_area_1_eq_trans_chains_in_closed_implication_form() {
    let env = build_env();
    // For k = 2..=10: e0=e1 → e1=e2 → … → e_{k-1}=ek → e0=ek.
    for k in 2u32..=10 {
        let antecedents: Vec<Expr> = (0..k)
            .map(|i| eq_a(&konst(&format!("e{i}")), &konst(&format!("e{}", i + 1))))
            .collect();
        let consequent = eq_a(&konst("e0"), &konst(&format!("e{k}")));
        let goal = implication(&antecedents, &consequent);
        prove_and_kernel_check(&env, &goal, &format!("eq_trans chain k={k}"));
    }
}

#[test]
fn weak_area_2_congruence_in_closed_implication_form() {
    let env = build_env();
    let (a, b, c) = (konst("a"), konst("b"), konst("c"));
    let (f, g, h) = (konst("f"), konst("g"), konst("h"));
    let app = |func: &Expr, arg: &Expr| Expr::app(func.clone(), arg.clone());

    // a=b → f(a)=f(b)
    let goal = implication(&[eq_a(&a, &b)], &eq_a(&app(&f, &a), &app(&f, &b)));
    prove_and_kernel_check(&env, &goal, "congruence f(a)=f(b)");

    // a=b → g(a)=g(b)
    let goal = implication(&[eq_a(&a, &b)], &eq_a(&app(&g, &a), &app(&g, &b)));
    prove_and_kernel_check(&env, &goal, "congruence g(a)=g(b)");

    // a=b → f(f(a))=f(f(b))
    let goal = implication(
        &[eq_a(&a, &b)],
        &eq_a(&app(&f, &app(&f, &a)), &app(&f, &app(&f, &b))),
    );
    prove_and_kernel_check(&env, &goal, "congruence f(f(a))=f(f(b))");

    // a=b → h(a,c)=h(b,c)
    let h_a_c = app(&app(&h, &a), &c);
    let h_b_c = app(&app(&h, &b), &c);
    let goal = implication(&[eq_a(&a, &b)], &eq_a(&h_a_c, &h_b_c));
    prove_and_kernel_check(&env, &goal, "congruence h(a,c)=h(b,c)");
}

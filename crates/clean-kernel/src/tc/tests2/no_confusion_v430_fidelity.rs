// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! v4.30 heterogeneous noConfusion convention — fidelity + invariance gates.
//!
//! Design: `designs/2026-07-03-noconfusion-ctoridx-convention.md` §6:
//! - **A5 (fidelity):** for the parameterized prelude-seeded roots
//!   Option/Sum/Sigma/List/Prod/Fin, Clean's synthesized `noConfusion(Type)`
//!   TYPES must equal the genuine Lean v4.30 types (oracles hand-transcribed
//!   from `lean` 4.30.0-rc2 `#print` with `pp.explicit`+`pp.universes`,
//!   compared with the kernel's `is_def_eq` — the same fallback predicate the
//!   shard-acceptance path uses — plus an explicit binder-info walk).
//! - **A6 (0-param invariance):** `Nat`/`Bool`/`Int` twins must be
//!   BYTE-IDENTICAL to the pre-change classic output (the schemes coincide
//!   for `num_params = 0`); the expected exprs below are transcribed pins of
//!   that output.

use super::*;
use crate::env::Environment;
use crate::level::Level;

fn lp(n: &Name) -> Level {
    Level::param(n.clone())
}

fn sort(l: Level) -> Expr {
    Expr::from_kind(ExprKind::Sort(l))
}

fn c0(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

fn cl(n: &str, ls: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(n), ls)
}

fn apps(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn pi(bi: BinderInfo, d: Expr, b: Expr) -> Expr {
    Expr::pi(bi, d, b)
}

fn lam(bi: BinderInfo, d: Expr, b: Expr) -> Expr {
    Expr::lam(bi, d, b)
}

fn bv(i: u32) -> Expr {
    Expr::bvar(i)
}

/// Collect the outermost Pi binder infos of a type.
fn binder_infos(mut e: &Expr) -> Vec<BinderInfo> {
    let mut out = Vec::new();
    while let ExprKind::Pi(bi, _, body) = &e.kind {
        out.push(bi.info);
        e = body;
    }
    out
}

/// Assert `name`'s declared type is def-eq to `oracle` and has the expected
/// binder-info spine.
fn assert_type_matches(env: &Environment, name: &str, oracle: &Expr, infos: &[BinderInfo]) {
    let tc = TypeChecker::new(env);
    let ci = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert_eq!(
        binder_infos(&ci.type_),
        infos,
        "{name}: binder-info spine mismatch\n  got:  {:?}",
        ci.type_
    );
    assert!(
        tc.is_def_eq(&ci.type_, oracle),
        "{name}: type differs from the v4.30 oracle\n  got:    {:?}\n  oracle: {:?}",
        ci.type_,
        oracle
    );
}

use BinderInfo::{Default as D, Implicit as I};

// ════════════════════════════════════════════════════════════════════════
// A5 — parameterized fidelity oracles (Option/Sum/Sigma/List/Prod/Fin)
// ════════════════════════════════════════════════════════════════════════

/// Shared oracle for the single-`Type u`-param carriers List and Option:
///
/// ```text
/// T.noConfusionType.{r, a} :
///   Sort r → {α : Type a} → T α → {α' : Type a} → T α' → Sort r
/// T.noConfusion.{r, a} : {P : Sort r} →
///   {α : Type a} → {t : T α} → {α' : Type a} → {t' : T α'} →
///   @Eq.{a+2} (Type a) α α' → @HEq.{a+1} (T α) t (T α') t' →
///   @T.noConfusionType.{r, a} P α t α' t'
/// ```
///
/// (probe: `#print List.noConfusion` / `Option.noConfusion`, v4.30.0-rc2,
/// pp.universes — design §1.2.)
fn assert_one_type_param_carrier_fidelity(env: &Environment, ty_name: &str) {
    let nct_name = format!("{ty_name}.noConfusionType");
    let nc_name = format!("{ty_name}.noConfusion");
    let ci = env
        .get_const(&Name::from_string(&nc_name))
        .unwrap_or_else(|| panic!("{nc_name} should exist"));
    assert_eq!(ci.level_params.len(), 2, "{nc_name}: [result, elem] levels");
    let r = lp(&ci.level_params[0]);
    let a = lp(&ci.level_params[1]);
    let type_a = sort(Level::succ(a.clone()));
    let t_of = |x: Expr| Expr::app(cl(ty_name, vec![a.clone()]), x);

    // noConfusionType: Sort r → {α} → T α → {α'} → T α' → Sort r
    let nct_oracle = pi(
        D,
        sort(r.clone()),
        pi(
            I,
            type_a.clone(),
            pi(
                D,
                t_of(bv(0)),
                pi(I, type_a.clone(), pi(D, t_of(bv(0)), sort(r.clone()))),
            ),
        ),
    );
    assert_type_matches(env, &nct_name, &nct_oracle, &[D, I, D, I, D]);

    // noConfusion: {P} {α} {t} {α'} {t'} → α = α' → t ≍ t' → NCT P α t α' t'
    // At the premise depths: α = BVar(3), t = BVar(2), α' = BVar(1), t' = BVar(0).
    let eq_prem = apps(
        cl("Eq", vec![Level::succ(Level::succ(a.clone()))]),
        [type_a.clone(), bv(3), bv(1)],
    );
    // After the Eq premise binder: α=4, t=3, α'=2, t'=1.
    let heq_prem = apps(
        cl("HEq", vec![Level::succ(a.clone())]),
        [t_of(bv(4)), bv(3), t_of(bv(2)), bv(1)],
    );
    // After both premise binders: P=6, α=5, t=4, α'=3, t'=2.
    let result = apps(
        cl(&nct_name, vec![r.clone(), a.clone()]),
        [bv(6), bv(5), bv(4), bv(3), bv(2)],
    );
    let nc_oracle = pi(
        I,
        sort(r),
        pi(
            I,
            type_a.clone(),
            pi(
                I,
                t_of(bv(0)),
                pi(
                    I,
                    type_a,
                    pi(I, t_of(bv(0)), pi(D, eq_prem, pi(D, heq_prem, result))),
                ),
            ),
        ),
    );
    assert_type_matches(env, &nc_name, &nc_oracle, &[I, I, I, I, I, D, D]);
}

#[test]
fn test_v430_fidelity_list() {
    let env = Environment::with_prelude();
    assert_one_type_param_carrier_fidelity(&env, "List");
}

#[test]
fn test_v430_fidelity_option() {
    let env = Environment::with_prelude();
    assert_one_type_param_carrier_fidelity(&env, "Option");
}

/// Shared oracle for the two-independent-`Type`-param carriers Sum and Prod:
///
/// ```text
/// T.noConfusion.{r, a, b} : {P : Sort r} →
///   {α : Type a} → {β : Type b} → {t : T α β} →
///   {α' : Type a} → {β' : Type b} → {t' : T α' β'} →
///   @Eq.{a+2} (Type a) α α' → @Eq.{b+2} (Type b) β β' →
///   @HEq.{max (a+1) (b+1)} (T α β) t (T α' β') t' →
///   @T.noConfusionType.{r, a, b} P α β t α' β' t'
/// ```
///
/// (probe: `#print Sum.noConfusion` / `Prod.noConfusion` — design §1.2.)
fn assert_two_type_param_carrier_fidelity(env: &Environment, ty_name: &str) {
    let nct_name = format!("{ty_name}.noConfusionType");
    let nc_name = format!("{ty_name}.noConfusion");
    let ci = env
        .get_const(&Name::from_string(&nc_name))
        .unwrap_or_else(|| panic!("{nc_name} should exist"));
    assert_eq!(ci.level_params.len(), 3, "{nc_name}: [result, a, b] levels");
    let r = lp(&ci.level_params[0]);
    let a = lp(&ci.level_params[1]);
    let b = lp(&ci.level_params[2]);
    let type_a = sort(Level::succ(a.clone()));
    let type_b = sort(Level::succ(b.clone()));
    let t_of = |x: Expr, y: Expr| apps(cl(ty_name, vec![a.clone(), b.clone()]), [x, y]);

    // noConfusionType: Sort r → {α} {β} → T α β → {α'} {β'} → T α' β' → Sort r
    let nct_oracle = pi(
        D,
        sort(r.clone()),
        pi(
            I,
            type_a.clone(),
            pi(
                I,
                type_b.clone(),
                pi(
                    D,
                    t_of(bv(1), bv(0)),
                    pi(
                        I,
                        type_a.clone(),
                        pi(
                            I,
                            type_b.clone(),
                            pi(D, t_of(bv(1), bv(0)), sort(r.clone())),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_type_matches(env, &nct_name, &nct_oracle, &[D, I, I, D, I, I, D]);

    // noConfusion premises. At the first premise depth:
    // α=5, β=4, t=3, α'=2, β'=1, t'=0.
    let eq_a = apps(
        cl("Eq", vec![Level::succ(Level::succ(a.clone()))]),
        [type_a.clone(), bv(5), bv(2)],
    );
    // +1: α=6, β=5, α'=3, β'=2.
    let eq_b = apps(
        cl("Eq", vec![Level::succ(Level::succ(b.clone()))]),
        [type_b.clone(), bv(5), bv(2)],
    );
    // +2: α=7, β=6, t=5, α'=4, β'=3, t'=2.
    let heq_major = apps(
        cl(
            "HEq",
            vec![Level::max(Level::succ(a.clone()), Level::succ(b.clone()))],
        ),
        [t_of(bv(7), bv(6)), bv(5), t_of(bv(4), bv(3)), bv(2)],
    );
    // +3: P=9, α=8, β=7, t=6, α'=5, β'=4, t'=3.
    let result = apps(
        cl(&nct_name, vec![r.clone(), a.clone(), b.clone()]),
        [bv(9), bv(8), bv(7), bv(6), bv(5), bv(4), bv(3)],
    );
    let nc_oracle = pi(
        I,
        sort(r),
        pi(
            I,
            type_a.clone(),
            pi(
                I,
                type_b.clone(),
                pi(
                    I,
                    t_of(bv(1), bv(0)),
                    pi(
                        I,
                        type_a,
                        pi(
                            I,
                            type_b,
                            pi(
                                I,
                                t_of(bv(1), bv(0)),
                                pi(D, eq_a, pi(D, eq_b, pi(D, heq_major, result))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_type_matches(env, &nc_name, &nc_oracle, &[I, I, I, I, I, I, I, D, D, D]);
}

#[test]
fn test_v430_fidelity_sum() {
    let env = Environment::with_prelude();
    assert_two_type_param_carrier_fidelity(&env, "Sum");
}

#[test]
fn test_v430_fidelity_prod() {
    let env = Environment::with_prelude();
    assert_two_type_param_carrier_fidelity(&env, "Prod");
}

/// Sigma — the DEPENDENT-param oracle (`β : α → Type b` mentions `α`, so its
/// premise is `HEq`, not `Eq`):
///
/// ```text
/// Sigma.noConfusion.{r, a, b} : {P : Sort r} →
///   {α : Type a} → {β : α → Type b} → {t : @Sigma α β} →
///   {α' : Type a} → {β' : α' → Type b} → {t' : @Sigma α' β'} →
///   @Eq.{a+2} (Type a) α α' →
///   @HEq.{max (a+1) (b+2)} (α → Type b) β (α' → Type b) β' →
///   @HEq.{max (a+1) (b+1)} (@Sigma α β) t (@Sigma α' β') t' →
///   @Sigma.noConfusionType.{r, a, b} P α β t α' β' t'
/// ```
///
/// (probe: `#print Sigma.noConfusion`, pp.explicit + pp.universes — design
/// §1.2/§3.)
#[test]
fn test_v430_fidelity_sigma() {
    let env = Environment::with_prelude();
    let ci = env
        .get_const(&Name::from_string("Sigma.noConfusion"))
        .expect("Sigma.noConfusion should exist");
    assert_eq!(ci.level_params.len(), 3);
    let r = lp(&ci.level_params[0]);
    let a = lp(&ci.level_params[1]);
    let b = lp(&ci.level_params[2]);
    let type_a = sort(Level::succ(a.clone()));
    let type_b = sort(Level::succ(b.clone()));
    // β's domain at a given α position: `α → Type b`.
    let beta_dom = |alpha: Expr| pi(D, alpha, type_b.clone());
    let sigma_of = |x: Expr, y: Expr| apps(cl("Sigma", vec![a.clone(), b.clone()]), [x, y]);

    // noConfusionType.
    let nct_oracle = pi(
        D,
        sort(r.clone()),
        pi(
            I,
            type_a.clone(),
            pi(
                I,
                beta_dom(bv(0)),
                pi(
                    D,
                    sigma_of(bv(1), bv(0)),
                    pi(
                        I,
                        type_a.clone(),
                        pi(
                            I,
                            beta_dom(bv(0)),
                            pi(D, sigma_of(bv(1), bv(0)), sort(r.clone())),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_type_matches(
        &env,
        "Sigma.noConfusionType",
        &nct_oracle,
        &[D, I, I, D, I, I, D],
    );

    // noConfusion. First premise depth: α=5, β=4, t=3, α'=2, β'=1, t'=0.
    let eq_a = apps(
        cl("Eq", vec![Level::succ(Level::succ(a.clone()))]),
        [type_a.clone(), bv(5), bv(2)],
    );
    // +1: α=6, β=5, α'=3, β'=2. Dependent param β: HEq at heterogeneous
    // function types `α → Type b` vs `α' → Type b`.
    let heq_b = apps(
        cl(
            "HEq",
            vec![Level::max(
                Level::succ(a.clone()),
                Level::succ(Level::succ(b.clone())),
            )],
        ),
        [beta_dom(bv(6)), bv(5), beta_dom(bv(3)), bv(2)],
    );
    // +2: α=7, β=6, t=5, α'=4, β'=3, t'=2.
    let heq_major = apps(
        cl(
            "HEq",
            vec![Level::max(Level::succ(a.clone()), Level::succ(b.clone()))],
        ),
        [sigma_of(bv(7), bv(6)), bv(5), sigma_of(bv(4), bv(3)), bv(2)],
    );
    // +3: P=9, α=8, β=7, t=6, α'=5, β'=4, t'=3.
    let result = apps(
        cl(
            "Sigma.noConfusionType",
            vec![r.clone(), a.clone(), b.clone()],
        ),
        [bv(9), bv(8), bv(7), bv(6), bv(5), bv(4), bv(3)],
    );
    let nc_oracle = pi(
        I,
        sort(r),
        pi(
            I,
            type_a.clone(),
            pi(
                I,
                beta_dom(bv(0)),
                pi(
                    I,
                    sigma_of(bv(1), bv(0)),
                    pi(
                        I,
                        type_a,
                        pi(
                            I,
                            beta_dom(bv(0)),
                            pi(
                                I,
                                sigma_of(bv(1), bv(0)),
                                pi(D, eq_a, pi(D, heq_b, pi(D, heq_major, result))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_type_matches(
        &env,
        "Sigma.noConfusion",
        &nc_oracle,
        &[I, I, I, I, I, I, I, D, D, D],
    );
}

/// Fin — the concrete-param oracle (`n : Nat` — premise stays `Eq.{1}`):
///
/// ```text
/// Fin.noConfusion.{r} : {P : Sort r} →
///   {n : Nat} → {t : Fin n} → {n' : Nat} → {t' : Fin n'} →
///   @Eq.{1} Nat n n' → @HEq.{1} (Fin n) t (Fin n') t' →
///   @Fin.noConfusionType.{r} P n t n' t'
/// ```
///
/// (probe: `#print Fin.noConfusion` — design §1.2.)
#[test]
fn test_v430_fidelity_fin() {
    let env = Environment::with_prelude();
    let ci = env
        .get_const(&Name::from_string("Fin.noConfusion"))
        .expect("Fin.noConfusion should exist");
    assert_eq!(ci.level_params.len(), 1);
    let r = lp(&ci.level_params[0]);
    let one = Level::succ(Level::zero());
    let fin_of = |x: Expr| Expr::app(c0("Fin"), x);

    let nct_oracle = pi(
        D,
        sort(r.clone()),
        pi(
            I,
            c0("Nat"),
            pi(
                D,
                fin_of(bv(0)),
                pi(I, c0("Nat"), pi(D, fin_of(bv(0)), sort(r.clone()))),
            ),
        ),
    );
    assert_type_matches(&env, "Fin.noConfusionType", &nct_oracle, &[D, I, D, I, D]);

    // Premise depth: n=3, t=2, n'=1, t'=0.
    let eq_n = apps(cl("Eq", vec![one.clone()]), [c0("Nat"), bv(3), bv(1)]);
    // +1: n=4, t=3, n'=2, t'=1.
    let heq_major = apps(
        cl("HEq", vec![one]),
        [fin_of(bv(4)), bv(3), fin_of(bv(2)), bv(1)],
    );
    // +2: P=6, n=5, t=4, n'=3, t'=2.
    let result = apps(
        cl("Fin.noConfusionType", vec![r.clone()]),
        [bv(6), bv(5), bv(4), bv(3), bv(2)],
    );
    let nc_oracle = pi(
        I,
        sort(r),
        pi(
            I,
            c0("Nat"),
            pi(
                I,
                fin_of(bv(0)),
                pi(
                    I,
                    c0("Nat"),
                    pi(I, fin_of(bv(0)), pi(D, eq_n, pi(D, heq_major, result))),
                ),
            ),
        ),
    );
    assert_type_matches(&env, "Fin.noConfusion", &nc_oracle, &[I, I, I, I, I, D, D]);
}

// ════════════════════════════════════════════════════════════════════════
// A6 — 0-param byte-invariance pins (Nat / Bool / Int)
// ════════════════════════════════════════════════════════════════════════

/// Pin every field of a 0-param twin pair against transcribed expected exprs.
fn assert_twin_exact(env: &Environment, name: &str, ty: &Expr, val: &Expr) {
    let ci = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert_eq!(
        ci.level_params,
        vec![Name::from_string("u")],
        "{name}: level params"
    );
    assert_eq!(&ci.type_, ty, "{name}: TYPE must be byte-identical");
    assert_eq!(
        ci.value.as_ref().expect("twin has a value"),
        val,
        "{name}: VALUE must be byte-identical"
    );
}

/// `Nat` twins are byte-identical to the pre-change classic output — the
/// v4.30 switch (design §6/A6) must not touch 0-param types (the two schemes
/// coincide there, design §1.2).
#[test]
fn test_0param_invariance_nat_twins() {
    let env = Environment::with_prelude();
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let sort_u = sort(u.clone());
    let nat = c0("Nat");
    let motive = || lam(D, c0("Nat"), sort(u.clone()));
    let cases = || cl("Nat.casesOn", vec![Level::succ(u.clone())]);
    let eq1 = |x: Expr, y: Expr| apps(cl("Eq", vec![one.clone()]), [c0("Nat"), x, y]);

    // Nat.noConfusionType : Sort u → Nat → Nat → Sort u
    let nct_ty = pi(
        D,
        sort_u.clone(),
        pi(D, nat.clone(), pi(D, nat.clone(), sort_u.clone())),
    );
    // fun P a b => Nat.casesOn (motive) a
    //   (Nat.casesOn (motive) b ((P → P)) (fun n => P))         -- zero row
    //   (fun n => Nat.casesOn (motive) b P (fun m => (n = m → P) → P))
    let nct_val = lam(
        D,
        sort_u.clone(),
        lam(
            D,
            nat.clone(),
            lam(
                D,
                nat.clone(),
                apps(
                    cases(),
                    [
                        motive(),
                        bv(1),
                        apps(
                            cases(),
                            [
                                motive(),
                                bv(0),
                                pi(D, bv(2), bv(3)),
                                lam(D, c0("Nat"), bv(3)),
                            ],
                        ),
                        lam(
                            D,
                            c0("Nat"),
                            apps(
                                cases(),
                                [
                                    motive(),
                                    bv(1),
                                    bv(3),
                                    lam(
                                        D,
                                        c0("Nat"),
                                        pi(D, pi(D, eq1(bv(1), bv(0)), bv(5)), bv(5)),
                                    ),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Nat.noConfusionType", &nct_ty, &nct_val);

    // Nat.noConfusion : {P} {a b} → a = b → Nat.noConfusionType P a b
    let nc_ty = pi(
        I,
        sort_u.clone(),
        pi(
            I,
            nat.clone(),
            pi(
                I,
                nat.clone(),
                pi(
                    D,
                    eq1(bv(1), bv(0)),
                    apps(
                        cl("Nat.noConfusionType", vec![u.clone()]),
                        [bv(3), bv(2), bv(1)],
                    ),
                ),
            ),
        ),
    );
    let nc_val = lam(
        I,
        sort_u,
        lam(
            I,
            nat.clone(),
            lam(
                I,
                nat.clone(),
                lam(
                    D,
                    eq1(bv(1), bv(0)),
                    apps(
                        cl("Eq.ndrec", vec![u.clone(), one.clone()]),
                        [
                            c0("Nat"),
                            bv(2),
                            lam(
                                D,
                                c0("Nat"),
                                apps(
                                    cl("Nat.noConfusionType", vec![u.clone()]),
                                    [bv(4), bv(3), bv(0)],
                                ),
                            ),
                            apps(
                                cl("Nat.casesOn", vec![u.clone()]),
                                [
                                    lam(
                                        D,
                                        c0("Nat"),
                                        apps(
                                            cl("Nat.noConfusionType", vec![u.clone()]),
                                            [bv(4), bv(0), bv(0)],
                                        ),
                                    ),
                                    bv(2),
                                    lam(D, bv(3), bv(0)),
                                    lam(
                                        D,
                                        c0("Nat"),
                                        lam(
                                            D,
                                            pi(D, eq1(bv(0), bv(0)), bv(5)),
                                            Expr::app(
                                                bv(0),
                                                apps(
                                                    cl("Eq.refl", vec![one.clone()]),
                                                    [c0("Nat"), bv(1)],
                                                ),
                                            ),
                                        ),
                                    ),
                                ],
                            ),
                            bv(1),
                            bv(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Nat.noConfusion", &nc_ty, &nc_val);
}

/// `Bool` twins are byte-identical to the pre-change classic output (A6).
#[test]
fn test_0param_invariance_bool_twins() {
    let env = Environment::with_prelude();
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let sort_u = sort(u.clone());
    let bool_ = c0("Bool");
    let motive = || lam(D, c0("Bool"), sort(u.clone()));
    let cases = || cl("Bool.casesOn", vec![Level::succ(u.clone())]);
    let eq1 = |x: Expr, y: Expr| apps(cl("Eq", vec![one.clone()]), [c0("Bool"), x, y]);

    let nct_ty = pi(
        D,
        sort_u.clone(),
        pi(D, bool_.clone(), pi(D, bool_.clone(), sort_u.clone())),
    );
    // fun P a b => casesOn motive a
    //   (casesOn motive b (P → P) P)   (casesOn motive b P (P → P))
    let nct_val = lam(
        D,
        sort_u.clone(),
        lam(
            D,
            bool_.clone(),
            lam(
                D,
                bool_.clone(),
                apps(
                    cases(),
                    [
                        motive(),
                        bv(1),
                        apps(cases(), [motive(), bv(0), pi(D, bv(2), bv(3)), bv(2)]),
                        apps(cases(), [motive(), bv(0), bv(2), pi(D, bv(2), bv(3))]),
                    ],
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Bool.noConfusionType", &nct_ty, &nct_val);

    let nc_ty = pi(
        I,
        sort_u.clone(),
        pi(
            I,
            bool_.clone(),
            pi(
                I,
                bool_.clone(),
                pi(
                    D,
                    eq1(bv(1), bv(0)),
                    apps(
                        cl("Bool.noConfusionType", vec![u.clone()]),
                        [bv(3), bv(2), bv(1)],
                    ),
                ),
            ),
        ),
    );
    let nc_val = lam(
        I,
        sort_u,
        lam(
            I,
            bool_.clone(),
            lam(
                I,
                bool_.clone(),
                lam(
                    D,
                    eq1(bv(1), bv(0)),
                    apps(
                        cl("Eq.ndrec", vec![u.clone(), one.clone()]),
                        [
                            c0("Bool"),
                            bv(2),
                            lam(
                                D,
                                c0("Bool"),
                                apps(
                                    cl("Bool.noConfusionType", vec![u.clone()]),
                                    [bv(4), bv(3), bv(0)],
                                ),
                            ),
                            apps(
                                cl("Bool.casesOn", vec![u.clone()]),
                                [
                                    lam(
                                        D,
                                        c0("Bool"),
                                        apps(
                                            cl("Bool.noConfusionType", vec![u.clone()]),
                                            [bv(4), bv(0), bv(0)],
                                        ),
                                    ),
                                    bv(2),
                                    lam(D, bv(3), bv(0)),
                                    lam(D, bv(3), bv(0)),
                                ],
                            ),
                            bv(1),
                            bv(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Bool.noConfusion", &nc_ty, &nc_val);
}

/// `Int` twins are byte-identical to the pre-change classic output (A6).
/// Int has two single-`Nat`-field constructors (`ofNat`, `negSucc`), so both
/// diagonal cells carry a concrete `Eq.{1} Nat` chain — unchanged by the
/// v4.30 switch.
#[test]
fn test_0param_invariance_int_twins() {
    let env = Environment::with_prelude();
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let sort_u = sort(u.clone());
    let int = c0("Int");
    let motive = || lam(D, c0("Int"), sort(u.clone()));
    let cases = || cl("Int.casesOn", vec![Level::succ(u.clone())]);
    let eq_nat = |x: Expr, y: Expr| apps(cl("Eq", vec![one.clone()]), [c0("Nat"), x, y]);
    let eq_int = |x: Expr, y: Expr| apps(cl("Eq", vec![one.clone()]), [c0("Int"), x, y]);

    let nct_ty = pi(
        D,
        sort_u.clone(),
        pi(D, int.clone(), pi(D, int.clone(), sort_u.clone())),
    );
    // Diagonal cell under both one-field lambdas: ((n = m → P) → P).
    let diag_cell = || {
        lam(
            D,
            c0("Nat"),
            pi(D, pi(D, eq_nat(bv(1), bv(0)), bv(5)), bv(5)),
        )
    };
    let off_cell = || lam(D, c0("Nat"), bv(4));
    let nct_val = lam(
        D,
        sort_u.clone(),
        lam(
            D,
            int.clone(),
            lam(
                D,
                int.clone(),
                apps(
                    cases(),
                    [
                        motive(),
                        bv(1),
                        lam(
                            D,
                            c0("Nat"),
                            apps(cases(), [motive(), bv(1), diag_cell(), off_cell()]),
                        ),
                        lam(
                            D,
                            c0("Nat"),
                            apps(cases(), [motive(), bv(1), off_cell(), diag_cell()]),
                        ),
                    ],
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Int.noConfusionType", &nct_ty, &nct_val);

    let nc_ty = pi(
        I,
        sort_u.clone(),
        pi(
            I,
            int.clone(),
            pi(
                I,
                int.clone(),
                pi(
                    D,
                    eq_int(bv(1), bv(0)),
                    apps(
                        cl("Int.noConfusionType", vec![u.clone()]),
                        [bv(3), bv(2), bv(1)],
                    ),
                ),
            ),
        ),
    );
    // Both minors: fun (n : Nat) (k : (n = n → P)) => k (Eq.refl Nat n)
    let minor = || {
        lam(
            D,
            c0("Nat"),
            lam(
                D,
                pi(D, eq_nat(bv(0), bv(0)), bv(5)),
                Expr::app(
                    bv(0),
                    apps(cl("Eq.refl", vec![one.clone()]), [c0("Nat"), bv(1)]),
                ),
            ),
        )
    };
    let nc_val = lam(
        I,
        sort_u,
        lam(
            I,
            int.clone(),
            lam(
                I,
                int.clone(),
                lam(
                    D,
                    eq_int(bv(1), bv(0)),
                    apps(
                        cl("Eq.ndrec", vec![u.clone(), one.clone()]),
                        [
                            c0("Int"),
                            bv(2),
                            lam(
                                D,
                                c0("Int"),
                                apps(
                                    cl("Int.noConfusionType", vec![u.clone()]),
                                    [bv(4), bv(3), bv(0)],
                                ),
                            ),
                            apps(
                                cl("Int.casesOn", vec![u.clone()]),
                                [
                                    lam(
                                        D,
                                        c0("Int"),
                                        apps(
                                            cl("Int.noConfusionType", vec![u.clone()]),
                                            [bv(4), bv(0), bv(0)],
                                        ),
                                    ),
                                    bv(2),
                                    minor(),
                                    minor(),
                                ],
                            ),
                            bv(1),
                            bv(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    assert_twin_exact(&env, "Int.noConfusion", &nc_ty, &nc_val);
}

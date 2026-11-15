// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The subsingleton / large-elimination gate on a family whose result level
//! may be zero (`Sort u`), against pinned Lean.
//!
//! Lean's kernel grants large elimination unconditionally only when the result
//! level is PROVABLY nonzero (`inductive.cpp@v4.30.0-rc2`,
//! `elim_only_at_universe_zero`: `if (m_is_not_zero) return false;`). A level
//! that may be zero (`Sort u`) runs the restriction analysis: a mutual block,
//! or a single type with more than one constructor, eliminates only into
//! `Prop`. Pinned Lean 4.8.0 and v4.30.0-rc2, on
//! `set_option bootstrap.inductiveCheckResultingUniverse false in
//! inductive SU : Sort u | a | b` (measured 2026-10-17):
//! `@SU.rec : ∀ {motive : SU → Prop}, motive SU.a → motive SU.b → ∀ (t : SU), motive t`,
//! `@SU.rec.{1, 0}` is "too many explicit universe levels", and eliminating
//! `SU.{1}` into `Bool` is a type mismatch. The mutual
//! `EvU/OdU : Sort u` block gets `motive_1 : EvU → Prop`. `TU : Sort (u+1)`,
//! `MU : Sort (max 1 u)` and the field-less `PU : Sort u | mk` keep a motive
//! universe.
//!
//! ck0's gate asked `!is_zero` ("not provably zero") where Lean asks
//! `is_not_zero`, so `SU` got a large recursor. At `u := 0`, `SU.{0}` is a
//! proposition: proof irrelevance makes `SU.a ≡ SU.b`, and transporting along
//! that equation through `SU.rec` into `Bool` proves `False`.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_mutual, Budget, Constructor, Env, InductiveDecl, MinimalEnv,
    MutualBlock, Name, RawExpr, RawLevel, Term,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn r_sort(l: RawLevel) -> RawExpr {
    RawExpr::Sort(l)
}
fn l_nat(k: u32) -> RawLevel {
    (0..k).fold(RawLevel::Zero, |l, _| RawLevel::Succ(Box::new(l)))
}
fn l_u() -> RawLevel {
    RawLevel::Param(0)
}
fn r_const(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter()
        .fold(f, |f, a| RawExpr::App(Box::new(f), Box::new(a)))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}

fn boot(names: &[(&str, u32)]) -> MinimalEnv {
    names.iter().fold(MinimalEnv::new(), |env, (nm, nlp)| {
        env.with_const(n(nm), *nlp)
    })
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

/// `name.{nlp} : Sort sort` with field-less constructors `ctors`.
fn enum_decl(name: &str, nlp: u32, sort: RawLevel, ctors: &[&str]) -> InductiveDecl {
    let levels: Vec<RawLevel> = (0..nlp).map(RawLevel::Param).collect();
    let mut names = vec![(name.to_owned(), nlp)];
    names.extend(ctors.iter().map(|c| (format!("{name}.{c}"), nlp)));
    let pairs: Vec<(&str, u32)> = names.iter().map(|(s, k)| (s.as_str(), *k)).collect();
    let b = boot(&pairs);
    InductiveDecl {
        name: n(name),
        num_level_params: nlp,
        num_params: 0,
        type_: vlvl(&b, &r_sort(sort), nlp),
        constructors: ctors
            .iter()
            .map(|c| Constructor {
                name: n(&format!("{name}.{c}")),
                type_: vlvl(&b, &r_const(name, levels.clone()), nlp),
            })
            .collect(),
    }
}

/// `Eq.{u} {A : Sort u} (a : A) : A -> Prop`, `refl (a) : Eq a a`
/// (num_params = 2, as in the M2 fixture).
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    let ty = r_pi(
        r_sort(l_u()),
        r_pi(RawExpr::BVar(0), r_pi(RawExpr::BVar(1), r_sort(l_nat(0)))),
    );
    let refl_ty = r_pi(
        r_sort(l_u()),
        r_pi(
            RawExpr::BVar(0),
            r_apps(
                r_const("Eq", vec![l_u()]),
                vec![RawExpr::BVar(1), RawExpr::BVar(0), RawExpr::BVar(0)],
            ),
        ),
    );
    InductiveDecl {
        name: n("Eq"),
        num_level_params: 1,
        num_params: 2,
        type_: vlvl(&b, &ty, 1),
        constructors: vec![Constructor {
            name: n("Eq.refl"),
            type_: vlvl(&b, &refl_ty, 1),
        }],
    }
}

/// `False`, `True`, `Bool` and `Eq`, then `extra`.
fn env_with(extra: Vec<InductiveDecl>) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for decl in [
        enum_decl("False", 0, l_nat(0), &[]),
        enum_decl("True", 0, l_nat(0), &["intro"]),
        enum_decl("Bool", 0, l_nat(1), &["false", "true"]),
        eq_decl(),
    ]
    .into_iter()
    .chain(extra)
    {
        let name = decl.name.clone();
        add_inductive(&mut env, decl).unwrap_or_else(|e| panic!("{name:?} admits: {e:?}"));
    }
    env
}

fn large_elim(env: &MinimalEnv, name: &str) -> bool {
    env.inductive_large_elim(&n(name))
        .unwrap_or_else(|| panic!("{name} is admitted"))
}

/// `@I.rec.{motive_level, ind_level} (fun _ => Bool) true false major`.
fn to_bool(ind: &str, motive_level: RawLevel, ind_level: RawLevel, major: RawExpr) -> RawExpr {
    let i = r_const(ind, vec![ind_level.clone()]);
    r_apps(
        RawExpr::Elim(n(ind), motive_level, vec![ind_level]),
        vec![
            r_lam(i, r_const("Bool", vec![])),
            r_const("Bool.true", vec![]),
            r_const("Bool.false", vec![]),
            major,
        ],
    )
}

/// The proof of `False` a large `SU.rec` admits, at `u := 0`:
/// `@Eq.rec.{0,0} SU SU.a (fun x _ => P (toBool x)) True.intro SU.b (Eq.refl SU.a)`
/// with `P b := @Bool.rec.{1} (fun _ => Prop) False True b`, so the minor has
/// type `P true ≡ True` and the result `P false ≡ False`. `Eq.refl SU.a` has
/// type `SU.a = SU.b` only by proof irrelevance (`SU.{0} : Prop`).
fn false_derivation() -> RawExpr {
    let z = || l_nat(0);
    let su = || r_const("SU", vec![z()]);
    let a = || r_const("SU.a", vec![z()]);
    let b = || r_const("SU.b", vec![z()]);
    let p = |x: RawExpr| {
        r_apps(
            RawExpr::Elim(n("Bool"), l_nat(1), vec![]),
            vec![
                r_lam(r_const("Bool", vec![]), r_sort(z())),
                r_const("False", vec![]),
                r_const("True", vec![]),
                x,
            ],
        )
    };
    // motive : (x : SU) -> Eq SU a x -> Prop, under binders x (bvar 1), h (bvar 0).
    let motive = r_lam(
        su(),
        r_lam(
            r_apps(r_const("Eq", vec![z()]), vec![su(), a(), RawExpr::BVar(0)]),
            p(to_bool("SU", l_nat(1), z(), RawExpr::BVar(1))),
        ),
    );
    r_apps(
        RawExpr::Elim(n("Eq"), z(), vec![z()]),
        vec![
            su(),
            a(),
            motive,
            r_const("True.intro", vec![]),
            b(),
            r_apps(r_const("Eq.refl", vec![z()]), vec![su(), a()]),
        ],
    )
}

/// Whether `raw` validates and checks against `False` in `env`.
fn proves_false(env: &MinimalEnv, raw: &RawExpr) -> Result<(), String> {
    let ty = vlvl(env, &r_const("False", vec![]), 0);
    let proof = Term::validate(env, raw, 0, 0).map_err(|e| format!("validate: {e:?}"))?;
    let mut budget = Budget::default_budget();
    clean_ck0::check(env, &proof, &ty, &mut budget).map_err(|e| format!("check: {e:?}"))
}

#[test]
fn test_sort_u_two_constructor_family_eliminates_only_into_prop() {
    let env = env_with(vec![enum_decl("SU", 1, l_u(), &["a", "b"])]);
    assert!(
        !large_elim(&env, "SU"),
        "SU : Sort u with two constructors: Lean's SU.rec has motive SU → Prop"
    );
}

#[test]
fn test_sort_u_false_derivation_is_refused() {
    let env = env_with(vec![enum_decl("SU", 1, l_u(), &["a", "b"])]);
    let verdict = proves_false(&env, &false_derivation());
    assert!(
        verdict.is_err(),
        "a proof of False through SU.rec into Bool must be refused"
    );
}

/// Even at `u := 1` (where `SU.{1}` is a type) Lean's `SU.rec` eliminates only
/// into `Prop`: the decision is made once, for every instance.
#[test]
fn test_sort_u_elimination_into_bool_is_refused_at_every_level() {
    let env = env_with(vec![enum_decl("SU", 1, l_u(), &["a", "b"])]);
    let raw = to_bool("SU", l_nat(1), l_nat(1), r_const("SU.a", vec![l_nat(1)]));
    let ty = vlvl(&env, &r_const("Bool", vec![]), 0);
    let mut budget = Budget::default_budget();
    let checked = Term::validate(&env, &raw, 0, 0)
        .map_err(|e| format!("{e:?}"))
        .and_then(|t| clean_ck0::check(&env, &t, &ty, &mut budget).map_err(|e| format!("{e:?}")));
    assert!(checked.is_err(), "SU.rec into Bool must be refused");
}

/// `EvU/OdU : Sort u`, mutual: Lean's recursors have `motive_1 : EvU → Prop`.
fn even_odd_block(sort: RawLevel) -> MutualBlock {
    let b = boot(&[
        ("EvU", 1),
        ("OdU", 1),
        ("EvU.z", 1),
        ("EvU.s", 1),
        ("OdU.s", 1),
    ]);
    let ev = || r_const("EvU", vec![l_u()]);
    let od = || r_const("OdU", vec![l_u()]);
    let decl = |name: &str, ctors: Vec<(&str, RawExpr)>| InductiveDecl {
        name: n(name),
        num_level_params: 1,
        num_params: 0,
        type_: vlvl(&b, &r_sort(sort.clone()), 1),
        constructors: ctors
            .into_iter()
            .map(|(c, ty)| Constructor {
                name: n(c),
                type_: vlvl(&b, &ty, 1),
            })
            .collect(),
    };
    MutualBlock {
        decls: vec![
            decl("EvU", vec![("EvU.z", ev()), ("EvU.s", r_pi(od(), ev()))]),
            decl("OdU", vec![("OdU.s", r_pi(ev(), od()))]),
        ],
    }
}

#[test]
fn test_sort_u_mutual_block_eliminates_only_into_prop() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, even_odd_block(l_u())).expect("EvU/OdU admits");
    assert!(!large_elim(&env, "EvU"), "Lean: motive_1 : EvU → Prop");
    assert!(!large_elim(&env, "OdU"), "Lean: motive_2 : OdU → Prop");
}

/// Honest twins (pinned Lean gives each a motive universe): `Sort (u+1)` and
/// `Sort (max 1 u)` are provably nonzero, and a single field-less constructor
/// large-eliminates at any level. The mutual twin at `Sort (u+1)` too.
#[test]
fn test_provably_nonzero_and_field_less_families_large_eliminate() {
    let max1u = RawLevel::Max(Box::new(l_nat(1)), Box::new(l_u()));
    let env = env_with(vec![
        enum_decl("TU", 1, RawLevel::Succ(Box::new(l_u())), &["a", "b"]),
        enum_decl("MU", 1, max1u, &["a", "b"]),
        enum_decl("PU", 1, l_u(), &["mk"]),
    ]);
    for name in ["TU", "MU", "PU"] {
        assert!(large_elim(&env, name), "{name} large-eliminates in Lean");
    }
    // TU.{0} : Type eliminates into Bool, and the recursor computes.
    let raw = to_bool("TU", l_nat(1), l_nat(0), r_const("TU.b", vec![l_nat(0)]));
    let term = vlvl(&env, &raw, 0);
    let ty = vlvl(&env, &r_const("Bool", vec![]), 0);
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &term, &ty, &mut budget).expect("TU.rec into Bool checks");
    let value = clean_ck0::whnf::whnf(&env, &term, &mut budget).expect("whnf");
    assert_eq!(value, vlvl(&env, &r_const("Bool.false", vec![]), 0));

    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, even_odd_block(RawLevel::Succ(Box::new(l_u()))))
        .expect("EvU/OdU at Sort (u+1) admits");
    assert!(large_elim(&env, "EvU") && large_elim(&env, "OdU"));
}

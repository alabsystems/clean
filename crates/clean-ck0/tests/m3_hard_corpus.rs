// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ck0 M3 HARD corpus — the largest-risk surface stress test (design §5.2, §7).
//!
//! M3 (mutual + nested recursor derivation, no-confusion / injectivity, harder
//! ι-reduction) is the surface the design flags as the scariest unsoundness with
//! NO differential oracle: the prior `m3_stdlib_smoke` and `m3_mutual_nested`
//! tests drove SIMPLE inductives + a couple of literal ι-steps, but did not push
//! real *closed proof terms* through the mutual/nested recursors, did not build
//! no-confusion/injectivity, and did not exercise genuine multi-step ι reduction.
//!
//! This file drives REAL, Lean-faithful declarations through ck0's ACTUAL
//! machinery (`Term::validate` chokepoint -> `add_inductive`/`add_inductive_mutual`
//! /`add_inductive_nested` with kernel-checked derived recursors ->
//! `infer`/`check` with genuine ι-reduction). Everything is REAL — no `_unchecked`,
//! no stubs. Each soundness claim is LOAD-BEARING: every acceptance is paired with
//! the matching rejection.
//!
//! A. REAL MUTUAL inductive (Even/Odd over Nat indices) — block admits, both
//!    recursors kernel-check, a closed proof consuming `Even.rec` type-checks, and
//!    a cross-type ι-step reduces.
//! B. REAL NESTED inductive (rose tree through `List`) — admits via the auxiliary
//!    construction, derived recursors kernel-check, a literal tree builds and its
//!    recursor ι-reduces.
//! C. NO-CONFUSION / INJECTIVITY — `Nat.succ_ne_zero` and `Nat.succ.inj` as CLOSED
//!    proof terms built from `Nat.rec` / `Eq.rec` and a discriminating motive.
//! D. HARDER ι-REDUCTION — `Nat.add` defined via `Nat.rec` (typed `with_def`),
//!    `2 + 2` def-eq `4` (genuine multi-step), and NOT def-eq `3`.
//! E. NEGATIVE CONTROLS — every acceptance is meaningful: non-positive nesting,
//!    an ill-typed no-confusion leak, a wrong mutual-recursor motive, and `2+2 ≠ 5`
//!    are each REJECTED for the right reason.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_mutual, add_inductive_nested, Budget, Constructor, Env,
    InductiveDecl, MinimalEnv, MutualBlock, Name, RawExpr, RawLevel, Term, Transparency,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

// ---- RawExpr builders (same idiom as m3_stdlib_smoke) ----

fn r_sort(level: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..level {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}
fn r_prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}
fn r_sort_param(i: u32) -> RawExpr {
    RawExpr::Sort(RawLevel::Param(i))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_const_p(name: &str, levels: Vec<RawLevel>) -> RawExpr {
    RawExpr::Const(n(name), levels)
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_apps(f: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    args.into_iter().fold(f, r_app)
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn r_bvar(i: u32) -> RawExpr {
    RawExpr::BVar(i)
}
fn lzero() -> RawLevel {
    RawLevel::Zero
}
fn lone() -> RawLevel {
    RawLevel::Succ(Box::new(RawLevel::Zero))
}
fn lparam(i: u32) -> RawLevel {
    RawLevel::Param(i)
}

fn boot(decls: &[(&str, u32)]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for (nm, nlp) in decls {
        env = env.with_const(n(nm), *nlp);
    }
    env
}
fn vlvl(env: &dyn Env, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("term validates")
}

// Common Nat sugar.
fn nat_zero() -> RawExpr {
    r_const("Nat.zero")
}
fn nat_succ(x: RawExpr) -> RawExpr {
    r_app(r_const("Nat.succ"), x)
}
fn nat_lit(k: u32) -> RawExpr {
    let mut e = nat_zero();
    for _ in 0..k {
        e = nat_succ(e);
    }
    e
}

// ===========================================================================
// Shared base inductives: Nat, Eq, False, True (real Lean signatures), admitted
// into a fresh env. Re-used by C, D and several negative controls.
// ===========================================================================

fn nat_decl() -> InductiveDecl {
    let b = boot(&[("Nat", 0), ("Nat.zero", 0), ("Nat.succ", 0)]);
    InductiveDecl {
        name: n("Nat"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_sort(1), 0),
        constructors: vec![
            Constructor {
                name: n("Nat.zero"),
                type_: vlvl(&b, &r_const("Nat"), 0),
            },
            Constructor {
                name: n("Nat.succ"),
                type_: vlvl(&b, &r_pi(r_const("Nat"), r_const("Nat")), 0),
            },
        ],
    }
}

/// `Eq.{u} {A : Sort u} (a : A) : A -> Prop`, `refl (a) : Eq a a` (num_params=2).
fn eq_decl() -> InductiveDecl {
    let b = boot(&[("Eq", 1), ("Eq.refl", 1)]);
    let ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(r_bvar(1), r_prop())));
    let refl_ty = r_pi(
        r_sort_param(0),
        r_pi(
            r_bvar(0),
            r_apps(
                r_const_p("Eq", vec![lparam(0)]),
                vec![r_bvar(1), r_bvar(0), r_bvar(0)],
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

fn false_decl() -> InductiveDecl {
    let b = boot(&[("False", 0)]);
    InductiveDecl {
        name: n("False"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_prop(), 0),
        constructors: vec![],
    }
}

fn true_decl() -> InductiveDecl {
    let b = boot(&[("True", 0), ("True.intro", 0)]);
    InductiveDecl {
        name: n("True"),
        num_level_params: 0,
        num_params: 0,
        type_: vlvl(&b, &r_prop(), 0),
        constructors: vec![Constructor {
            name: n("True.intro"),
            type_: vlvl(&b, &r_const("True"), 0),
        }],
    }
}

/// Env with Nat, Eq, False, True admitted (their recursors kernel-checked).
fn base_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive(&mut env, eq_decl()).expect("Eq admits");
    add_inductive(&mut env, false_decl()).expect("False admits");
    add_inductive(&mut env, true_decl()).expect("True admits");
    env
}

fn admit_theorem(env: &MinimalEnv, ty_raw: &RawExpr, proof_raw: &RawExpr, level_arity: u32) {
    let ty = Term::validate(env, ty_raw, 0, level_arity).expect("theorem type validates");
    let mut budget = Budget::default_budget();
    clean_ck0::infer_sort_in_context(env, &[], &ty, &mut budget)
        .expect("theorem type infers to a Sort");
    let proof = Term::validate(env, proof_raw, 0, level_arity).expect("proof term validates");
    clean_ck0::check(env, &proof, &ty, &mut budget).expect("proof checks against the theorem type");
}

// ===========================================================================
// A. REAL MUTUAL inductive: Even / Odd over Nat indices (Prop, indexed).
// ===========================================================================
//
//   Even : Nat -> Prop   with  even_zero : Even 0
//                              even_succ : (n:Nat) -> Odd n  -> Even (succ n)
//   Odd  : Nat -> Prop   with  odd_succ  : (n:Nat) -> Even n -> Odd (succ n)
//
// This is the genuine Lean-shaped mutual *predicate*: one INDEX (the Nat), the
// recursive field of even_succ targets the Odd motive (cross-type), and vice
// versa. (The m3_mutual_nested Even/Odd was unindexed & Type-valued; this adds
// the real index telescope and Prop sorting.)

fn even_odd_block() -> MutualBlock {
    let b = boot(&[
        ("Nat", 0),
        ("Nat.zero", 0),
        ("Nat.succ", 0),
        ("Even", 0),
        ("Odd", 0),
        ("even_zero", 0),
        ("even_succ", 0),
        ("odd_succ", 0),
    ]);
    // Even : Nat -> Prop ; Odd : Nat -> Prop
    let pred_ty = vlvl(&b, &r_pi(r_const("Nat"), r_prop()), 0);
    // even_zero : Even Nat.zero
    let even_zero = Constructor {
        name: n("even_zero"),
        type_: vlvl(&b, &r_app(r_const("Even"), nat_zero()), 0),
    };
    // even_succ : (n:Nat) -> Odd n -> Even (Nat.succ n)
    let even_succ = Constructor {
        name: n("even_succ"),
        type_: vlvl(
            &b,
            &r_pi(
                r_const("Nat"), // n : Nat   (bvar1 in body)
                r_pi(
                    r_app(r_const("Odd"), r_bvar(0)),            // Odd n
                    r_app(r_const("Even"), nat_succ(r_bvar(1))), // Even (succ n)
                ),
            ),
            0,
        ),
    };
    // odd_succ : (n:Nat) -> Even n -> Odd (Nat.succ n)
    let odd_succ = Constructor {
        name: n("odd_succ"),
        type_: vlvl(
            &b,
            &r_pi(
                r_const("Nat"),
                r_pi(
                    r_app(r_const("Even"), r_bvar(0)),
                    r_app(r_const("Odd"), nat_succ(r_bvar(1))),
                ),
            ),
            0,
        ),
    };
    MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("Even"),
                num_level_params: 0,
                num_params: 0,
                type_: pred_ty.clone(),
                constructors: vec![even_zero, even_succ],
            },
            InductiveDecl {
                name: n("Odd"),
                num_level_params: 0,
                num_params: 0,
                type_: pred_ty,
                constructors: vec![odd_succ],
            },
        ],
    }
}

/// Admit Nat (single) then the Even/Odd mutual block into a fresh env.
fn even_odd_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive_mutual(&mut env, even_odd_block()).expect("Even/Odd block admits");
    env
}

#[test]
fn test_a_even_odd_block_admits_and_recursors_kernel_check() {
    let env = even_odd_env();
    // (i)+(ii): both derived recursors exist and kernel-check (infer to a Sort).
    for ind in ["Even", "Odd"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec type stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
    // Even.rec telescope: 2 motives + 3 minors (even_zero, even_succ, odd_succ)
    // + 1 index (Nat) + major = 7 leading Pis. (Both predicates are Prop, no
    // subsingleton ⇒ Prop-only elimination, so NO extra motive level param.)
    let rec_ty = env.recursor_type(&n("Even")).expect("Even.rec");
    let mut count = 0u32;
    let mut cur = rec_ty;
    while let clean_ck0::term::TermKind::Pi(_, _, codom) = cur.kind() {
        count += 1;
        cur = codom.clone();
    }
    assert_eq!(
        count, 7,
        "Even.rec = 2 motives + 3 minors + index + major (got {count})"
    );
    // Prop block (no large elim) ⇒ recursor has 0 universe params.
    assert_eq!(env.num_level_params(&n("Even.rec")), Some(0));
    assert_eq!(env.num_level_params(&n("Odd.rec")), Some(0));
}

#[test]
fn test_a_even_odd_closed_proof_consumes_recursor() {
    let env = even_odd_env();
    // Real proof term: `Even.elim_to_False`-shaped — actually we prove a genuine
    // theorem CONSUMING Even.rec. The cleanest closed proof: build the witness
    // `even_two : Even 2` from constructors, then `Odd.rec`/`Even.rec` to derive
    // a property. We prove:  (n:Nat) -> Even n -> Even n   by Even.rec with motive
    // `fun k _ => Even k` and minors that rebuild the constructors. This forces
    // the kernel to type-check a full mutual-recursor application against a
    // Prop-valued (indexed) motive — the load-bearing M3 surface.
    //
    // Even.rec  (Prop-only, no level param) arg order:
    //   {motive_E : (k:Nat) -> Even k -> Prop}
    //   {motive_O : (k:Nat) -> Odd  k -> Prop}
    //   (m_ez : motive_E 0 even_zero)
    //   (m_es : (n:Nat)(h:Odd n)(ih:motive_O n h) -> motive_E (succ n) (even_succ n h))
    //   (m_os : (n:Nat)(h:Even n)(ih:motive_E n h) -> motive_O (succ n) (odd_succ n h))
    //   {k : Nat} (major : Even k) -> motive_E k major
    //
    // motive_E := fun (k:Nat) (_:Even k) => Even k
    // motive_O := fun (k:Nat) (_:Odd  k) => Odd  k
    // m_ez := even_zero
    // m_es := fun (n:Nat)(h:Odd n)(ih:Odd n) => even_succ n ih
    // m_os := fun (n:Nat)(h:Even n)(ih:Even n) => odd_succ  n ih
    let even = |k: RawExpr| r_app(r_const("Even"), k);
    let odd = |k: RawExpr| r_app(r_const("Odd"), k);

    let motive_e = r_lam(r_const("Nat"), r_lam(even(r_bvar(0)), even(r_bvar(1))));
    let motive_o = r_lam(r_const("Nat"), r_lam(odd(r_bvar(0)), odd(r_bvar(1))));
    let m_ez = r_const("even_zero");
    // fun (n:Nat)(h:Odd n)(ih:Odd n) => even_succ n ih   [n=bvar2, h=bvar1, ih=bvar0]
    let m_es = r_lam(
        r_const("Nat"),
        r_lam(
            odd(r_bvar(0)),
            r_lam(
                odd(r_bvar(1)),
                r_apps(r_const("even_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    // fun (n:Nat)(h:Even n)(ih:Even n) => odd_succ n ih
    let m_os = r_lam(
        r_const("Nat"),
        r_lam(
            even(r_bvar(0)),
            r_lam(
                even(r_bvar(1)),
                r_apps(r_const("odd_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    // Even.rec is Prop-only ⇒ motive level 0, no ind level params: Elim(Even,0,[]).
    let elim = RawExpr::Elim(n("Even"), lzero(), vec![]);
    // Theorem: (k:Nat) -> Even k -> Even k.   proof = fun k (m:Even k) =>
    //   Even.rec motive_e motive_o m_ez m_es m_os k m
    // In the proof body [k, m]: k=bvar1, m=bvar0.
    let body = r_apps(
        elim,
        vec![
            motive_e,
            motive_o,
            m_ez,
            m_es,
            m_os,
            r_bvar(1), // index k
            r_bvar(0), // major m
        ],
    );
    let ty = r_pi(r_const("Nat"), r_pi(even(r_bvar(0)), even(r_bvar(1))));
    let proof = r_lam(r_const("Nat"), r_lam(even(r_bvar(0)), body));
    admit_theorem(&env, &ty, &proof, 0);
}

// A Type-valued indexed mutual block `EvenT / OddT : Nat -> Type` with the same
// cross-type recursive shape. A *Type*-valued block large-eliminates
// unconditionally (the subsingleton gate only restricts Prop blocks), so the
// recursor can compute into `Nat` — letting us OBSERVE a genuine multi-step,
// cross-type ι reduction to a concrete value. (The Prop Even/Odd above is
// Prop-only-eliminating per `block_large_eliminates`, so its recursor results are
// proof-irrelevant and not observable; that is why the computation uses a Type
// family — an honest distinction, not a workaround.)
fn even_odd_type_block() -> MutualBlock {
    let b = boot(&[
        ("Nat", 0),
        ("Nat.zero", 0),
        ("Nat.succ", 0),
        ("EvenT", 0),
        ("OddT", 0),
        ("evenT_zero", 0),
        ("evenT_succ", 0),
        ("oddT_succ", 0),
    ]);
    // EvenT : Nat -> Type 0 (= Sort 1) ; OddT : Nat -> Type 0
    let fam_ty = vlvl(&b, &r_pi(r_const("Nat"), r_sort(1)), 0);
    let evt_zero = Constructor {
        name: n("evenT_zero"),
        type_: vlvl(&b, &r_app(r_const("EvenT"), nat_zero()), 0),
    };
    let evt_succ = Constructor {
        name: n("evenT_succ"),
        type_: vlvl(
            &b,
            &r_pi(
                r_const("Nat"),
                r_pi(
                    r_app(r_const("OddT"), r_bvar(0)),
                    r_app(r_const("EvenT"), nat_succ(r_bvar(1))),
                ),
            ),
            0,
        ),
    };
    let odt_succ = Constructor {
        name: n("oddT_succ"),
        type_: vlvl(
            &b,
            &r_pi(
                r_const("Nat"),
                r_pi(
                    r_app(r_const("EvenT"), r_bvar(0)),
                    r_app(r_const("OddT"), nat_succ(r_bvar(1))),
                ),
            ),
            0,
        ),
    };
    MutualBlock {
        decls: vec![
            InductiveDecl {
                name: n("EvenT"),
                num_level_params: 0,
                num_params: 0,
                type_: fam_ty.clone(),
                constructors: vec![evt_zero, evt_succ],
            },
            InductiveDecl {
                name: n("OddT"),
                num_level_params: 0,
                num_params: 0,
                type_: fam_ty,
                constructors: vec![odt_succ],
            },
        ],
    }
}

#[test]
fn test_a_even_odd_iota_step_reduces() {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive_mutual(&mut env, even_odd_type_block()).expect("EvenT/OddT block admits");
    // A genuine cross-type ι-step. Eliminate `EvenT` into a Nat-valued "depth".
    // motive_E k _ := Nat, motive_O k _ := Nat; m_ez := zero;
    // m_es n h ih := succ ih; m_os n h ih := succ ih.
    // major = evenT_succ 0 (oddT_succ 0 evenT_zero) : EvenT 2.
    //   EvenT.rec ... (evenT_succ 0 (oddT_succ 0 evenT_zero))
    //     ι~> m_es 0 (oddT_succ 0 evenT_zero) (OddT.rec ... (oddT_succ 0 evenT_zero))
    //     ~> succ (OddT.rec ... (oddT_succ 0 evenT_zero))
    //     ι~> succ (m_os 0 evenT_zero (EvenT.rec ... evenT_zero))
    //     ~> succ (succ (EvenT.rec ... evenT_zero))
    //     ι~> succ (succ m_ez) = succ (succ zero) = 2.
    let m_e = r_lam(
        r_const("Nat"),
        r_lam(r_app(r_const("EvenT"), r_bvar(0)), r_const("Nat")),
    );
    let m_o = r_lam(
        r_const("Nat"),
        r_lam(r_app(r_const("OddT"), r_bvar(0)), r_const("Nat")),
    );
    let m_ez = nat_zero();
    // m_es : (n:Nat)(h:OddT n)(ih:Nat) -> Nat := λ n h ih => succ ih
    let m_es = r_lam(
        r_const("Nat"),
        r_lam(
            r_app(r_const("OddT"), r_bvar(0)),
            r_lam(r_const("Nat"), nat_succ(r_bvar(0))),
        ),
    );
    // m_os : (n:Nat)(h:EvenT n)(ih:Nat) -> Nat := λ n h ih => succ ih
    let m_os = r_lam(
        r_const("Nat"),
        r_lam(
            r_app(r_const("EvenT"), r_bvar(0)),
            r_lam(r_const("Nat"), nat_succ(r_bvar(0))),
        ),
    );
    // Type-valued block ⇒ large elim; motive lands in Type 0 = Sort 1: Elim(EvenT,1,[]).
    let elim = RawExpr::Elim(n("EvenT"), lone(), vec![]);
    // Witness of `EvenT 2`:
    //   evenT_zero               : EvenT 0
    //   oddT_succ 0 evenT_zero   : OddT 1
    //   evenT_succ 1 (..)        : EvenT 2     (succ's index arg is the PREDECESSOR)
    let major = r_apps(
        r_const("evenT_succ"),
        vec![
            nat_lit(1), // n = 1, so the result is EvenT (succ 1) = EvenT 2
            r_apps(
                r_const("oddT_succ"),
                vec![nat_zero(), r_const("evenT_zero")],
            ),
        ],
    );
    let app = r_apps(elim, vec![m_e, m_o, m_ez, m_es, m_os, nat_lit(2), major]);
    let t = Term::validate_closed(&env, &app).expect("validates");
    let mut budget = Budget::default_budget();
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("infers");
    let nat = Term::validate_closed(&env, &r_const("Nat")).expect("Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &nat, &mut budget).expect("def_eq"),
        "EvenT.rec depth has type Nat"
    );
    let two = Term::validate_closed(&env, &nat_lit(2)).expect("two");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &two, &mut budget).expect("def_eq"),
        "EvenT.rec depth of `evenT_succ 0 (oddT_succ 0 evenT_zero)` ι-reduces (cross-type IH) to 2"
    );
}

// ===========================================================================
// B. REAL NESTED inductive: rose tree through List.
//   Tree (A:Type) where node : A -> List (Tree A) -> Tree A.
// ===========================================================================
//
// Discovered API (src/nested.rs): the nesting container `List` must be a known
// inductive (admitted via the single path so its ctors + num_params are
// recorded); `add_inductive_nested` collects the `List (Tree A)` occurrence,
// builds the auxiliary `Tree._List`, rewrites `node`, and admits the mutual
// block [Tree, Tree._List].
//
// The m3_mutual_nested RoseTree was `List RoseTree -> RoseTree` with NO param and
// NO leading data field. This adds: a real type parameter A AND a non-recursive
// leading field (`A`), which is the canonical Lean rose tree.

fn env_with_list() -> MinimalEnv {
    let b = boot(&[("List", 1), ("List.nil", 1), ("List.cons", 1)]);
    let ty = vlvl(&b, &r_pi(r_sort_param(0), r_sort_param(0)), 1);
    let nil_ty = r_pi(
        r_sort_param(0),
        r_app(r_const_p("List", vec![lparam(0)]), r_bvar(0)),
    );
    let list_a = |db: u32| r_app(r_const_p("List", vec![lparam(0)]), r_bvar(db));
    let cons_ty = r_pi(r_sort_param(0), r_pi(r_bvar(0), r_pi(list_a(1), list_a(2))));
    let list_decl = InductiveDecl {
        name: n("List"),
        num_level_params: 1,
        num_params: 1,
        type_: ty,
        constructors: vec![
            Constructor {
                name: n("List.nil"),
                type_: vlvl(&b, &nil_ty, 1),
            },
            Constructor {
                name: n("List.cons"),
                type_: vlvl(&b, &cons_ty, 1),
            },
        ],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, list_decl).expect("List admits");
    env
}

/// `RoseTree : Type 0` with `RoseTree.node : Nat -> List RoseTree -> RoseTree`.
///
/// This exercises the PARAMETERLESS nested path: a rose tree carrying a leading
/// non-recursive `Nat` field plus the `List`-nested recursive children. The
/// PARAMETERIZED case — the textbook `Tree (A) where node : A -> List (Tree A) ->
/// Tree A`, where the auxiliary `Tree._List (A)` is itself parametric in `A` — is
/// now admitted soundly and covered in `tests/m3_param_nested.rs`. `Nat` must be
/// admitted in the env first.
fn rose_tree_decl() -> InductiveDecl {
    // Bootstrap env knows RoseTree (0 params), List, Nat, and RoseTree.node.
    let b = MinimalEnv::new()
        .with_const(n("RoseTree"), 0)
        .with_const(n("RoseTree.node"), 0)
        .with_const(n("List"), 1)
        .with_const(n("Nat"), 0);
    let ty = vlvl(&b, &r_sort(1), 0);
    // node : Nat -> List.{1} RoseTree -> RoseTree.
    //   RoseTree : Type 0 = Sort 1, so List's level arg is 1.
    let list_rt = r_app(r_const_p("List", vec![lone()]), r_const("RoseTree"));
    let node_ty = vlvl(
        &b,
        &r_pi(r_const("Nat"), r_pi(list_rt, r_const("RoseTree"))),
        0,
    );
    InductiveDecl {
        name: n("RoseTree"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("RoseTree.node"),
            type_: node_ty,
        }],
    }
}

/// Env with List + Nat + the nested RoseTree admitted.
fn rose_tree_env() -> MinimalEnv {
    let mut env = env_with_list();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    add_inductive_nested(&mut env, rose_tree_decl())
        .expect("RoseTree (nested through List) admits via auxiliary");
    env
}

#[test]
fn test_b_rose_tree_nested_admits_and_recursors_kernel_check() {
    let env = rose_tree_env();
    // (i) auxiliary RoseTree._List was created; (ii) both recursors kernel-check.
    let aux = n("RoseTree._List");
    assert!(
        env.recursor_type(&aux).is_some(),
        "auxiliary RoseTree._List recursor exists"
    );
    for ind in ["RoseTree", "RoseTree._List"] {
        let rec_ty = env
            .recursor_type(&n(ind))
            .unwrap_or_else(|| panic!("{ind}.rec stored"));
        let mut budget = Budget::default_budget();
        clean_ck0::infer_sort_in_context(&env, &[], &rec_ty, &mut budget)
            .unwrap_or_else(|e| panic!("{ind}.rec kernel-checks: {e:?}"));
    }
}

#[test]
fn test_b_rose_tree_value_builds_and_recursor_iota_reduces() {
    let env = rose_tree_env();

    // Build a leaf: `RoseTree.node Nat.zero (RoseTree._List.nil)` — a node with a
    // `0` label and NO children (empty aux list). The aux nil ctor mirrors
    // `List.nil` after substituting A := RoseTree, so it takes NO arguments here
    // (the substituted element type is fixed): RoseTree._List.nil : RoseTree._List.
    let aux_nil = r_const("RoseTree._List.nil");
    let leaf = r_apps(r_const("RoseTree.node"), vec![nat_zero(), aux_nil.clone()]);

    // The leaf type-checks to `RoseTree`.
    let leaf_t = Term::validate_closed(&env, &leaf).expect("leaf validates");
    let mut budget = Budget::default_budget();
    let leaf_ty = clean_ck0::infer(&env, &leaf_t, &mut budget).expect("leaf infers");
    let rt = Term::validate_closed(&env, &r_const("RoseTree")).expect("RoseTree");
    assert!(
        clean_ck0::is_def_eq(&env, &leaf_ty, &rt, &mut budget).expect("def_eq"),
        "RoseTree.node 0 nil : RoseTree"
    );

    // ι-reduce `RoseTree.rec` on the leaf — the recursor must fire on the literal
    // `RoseTree.node`. Eliminate everything into a constant Nat: the node minor
    // returns `succ zero`, so the whole rec ι-reduces to `succ zero`.
    //
    // Block is [RoseTree, RoseTree._List]; RoseTree.rec arg order:
    //   {motive_RT : RoseTree -> Sort 1}
    //   {motive_L  : RoseTree._List -> Sort 1}
    //   (node_minor : (lbl:Nat)(cs:RoseTree._List)(ih_cs:Nat) -> Nat)
    //   (nil_minor  : Nat)
    //   (cons_minor : (h:RoseTree)(t:RoseTree._List)(ih_h:Nat)(ih_t:Nat) -> Nat)
    //   (major : RoseTree) -> Nat
    let m_rt = r_lam(r_const("RoseTree"), r_const("Nat"));
    let m_l = r_lam(r_const("RoseTree._List"), r_const("Nat"));
    // node_minor lbl cs ih_cs := succ zero
    let node_minor = r_lam(
        r_const("Nat"),
        r_lam(r_const("RoseTree._List"), r_lam(r_const("Nat"), nat_lit(1))),
    );
    let nil_minor = nat_zero();
    let cons_minor = r_lam(
        r_const("RoseTree"),
        r_lam(
            r_const("RoseTree._List"),
            r_lam(r_const("Nat"), r_lam(r_const("Nat"), nat_zero())),
        ),
    );
    // RoseTree.rec is large-elim (Type-valued motive): Elim(RoseTree, 1, []).
    let elim = RawExpr::Elim(n("RoseTree"), lone(), vec![]);
    let app = r_apps(
        elim,
        vec![m_rt, m_l, node_minor, nil_minor, cons_minor, leaf],
    );
    let t = Term::validate_closed(&env, &app).expect("rec app validates");
    let mut budget2 = Budget::default_budget();
    let w = clean_ck0::whnf(&env, &t, &mut budget2).expect("whnf");
    let one = Term::validate_closed(&env, &nat_lit(1)).expect("one");
    assert!(
        clean_ck0::is_def_eq(&env, &w, &one, &mut budget2).expect("def_eq"),
        "RoseTree.rec on a literal leaf ι-reduces to the node minor's result (succ zero)"
    );
}

/// `rose_tree_env` plus a transparent `Nat.add : Nat -> Nat -> Nat` (the same
/// `Nat.rec`-on-2nd-arg definition used by section D). The non-empty-tree size
/// fold (below) needs `add` to combine the children's induction-hypothesis
/// results across `RoseTree._List.cons`.
fn rose_tree_add_env() -> MinimalEnv {
    let env = rose_tree_env();
    let add_ty = Term::validate_closed(
        &env,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat"))),
    )
    .expect("add type validates");
    let add_body = Term::validate_closed(&env, &add_def_body()).expect("add body validates");
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &add_body, &add_ty, &mut budget)
        .expect("Nat.add body checks against Nat -> Nat -> Nat");
    env.with_def(n("Nat.add"), 0, add_ty, add_body, Transparency::Transparent)
}

#[test]
fn test_b_rose_tree_nonempty_recursor_folds_through_children() {
    // The LOAD-BEARING nested-recursion test: build a REAL non-empty rose tree and
    // confirm `RoseTree.rec` ι-reduces THROUGH the `RoseTree._List` of children
    // (the genuine nested induction hypothesis). The prior leaf-only test never
    // fires the nested IH (its child list is `nil`), so its ι claim is vacuous for
    // the actual nesting; this one is not.
    //
    // Tree:  t = node 0 (cons (node 1 nil) (cons (node 2 nil) nil))
    //   — a root (label 0) with TWO leaf children (labels 1 and 2).
    //
    // Motive: a Nat "size" = number of `RoseTree.node`s in the tree. The fold is
    //   node_minor lbl cs ih_cs := succ ih_cs   (this node + its children's count)
    //   nil_minor                := 0           (empty child list)
    //   cons_minor h t ih_h ih_t := add ih_h ih_t  (head's size + rest's size)
    // so each node contributes 1 + (sum of its children's sizes). This REQUIRES
    // folding over the children's IH results: `ih_cs` (the `motive_L cs` IH on the
    // node's child LIST) only carries the children's sizes because `cons_minor`
    // recursed into each child via `ih_h` (a `motive_RT h` IH = the child tree's
    // own size). An empty-leaf-only kernel would compute size(root)=succ 0=1.
    //
    // Expected: size(node 1 nil)=1, size(node 2 nil)=1, inner cons=add 1 0=1,
    //   outer cons=add 1 1=2, t=succ 2 = 3.
    let env = rose_tree_add_env();
    let mut budget = Budget::default_budget();

    // --- build the non-empty tree, using the EXACT aux ctors the file uses ---
    let aux_nil = r_const("RoseTree._List.nil");
    let aux_cons = |h: RawExpr, t: RawExpr| r_apps(r_const("RoseTree._List.cons"), vec![h, t]);
    let node = |lbl: RawExpr, kids: RawExpr| r_apps(r_const("RoseTree.node"), vec![lbl, kids]);
    let leaf1 = node(nat_lit(1), aux_nil.clone()); // node 1 []
    let leaf2 = node(nat_lit(2), aux_nil.clone()); // node 2 []
    let children = aux_cons(leaf1, aux_cons(leaf2, aux_nil.clone())); // [leaf1, leaf2]
    let tree = node(nat_zero(), children); // node 0 [leaf1, leaf2]

    // The tree type-checks to `RoseTree` (it really is a well-formed value, and the
    // children list is a real, non-empty `RoseTree._List`).
    let tree_t = Term::validate_closed(&env, &tree).expect("non-empty tree validates");
    let tree_ty = clean_ck0::infer(&env, &tree_t, &mut budget).expect("tree infers");
    let rt = Term::validate_closed(&env, &r_const("RoseTree")).expect("RoseTree");
    assert!(
        clean_ck0::is_def_eq(&env, &tree_ty, &rt, &mut budget).expect("def_eq"),
        "node 0 [node 1 [], node 2 []] : RoseTree"
    );

    // --- RoseTree.rec size fold (arg order discovered from the derived rec type):
    //   {motive_RT : RoseTree -> Sort _}  {motive_L : RoseTree._List -> Sort _}
    //   (node_minor : (lbl:Nat)(cs:RoseTree._List)(ih_cs:motive_L cs) -> Nat)
    //   (nil_minor  : motive_L RoseTree._List.nil)
    //   (cons_minor : (h:RoseTree)(t:RoseTree._List)(ih_h:motive_RT h)(ih_t:motive_L t) -> Nat)
    //   (major : RoseTree) -> motive_RT major
    // With both motives constant `Nat`, the IH binders are `Nat`-typed.
    let m_rt = r_lam(r_const("RoseTree"), r_const("Nat"));
    let m_l = r_lam(r_const("RoseTree._List"), r_const("Nat"));
    // node_minor lbl cs ih_cs := succ ih_cs   [lbl=#2, cs=#1, ih_cs=#0]
    let node_minor = r_lam(
        r_const("Nat"),
        r_lam(
            r_const("RoseTree._List"),
            r_lam(r_const("Nat"), nat_succ(r_bvar(0))),
        ),
    );
    let nil_minor = nat_zero();
    // cons_minor h t ih_h ih_t := add ih_h ih_t   [h=#3, t=#2, ih_h=#1, ih_t=#0]
    let cons_minor = r_lam(
        r_const("RoseTree"),
        r_lam(
            r_const("RoseTree._List"),
            r_lam(
                r_const("Nat"),
                r_lam(r_const("Nat"), add(r_bvar(1), r_bvar(0))),
            ),
        ),
    );
    // RoseTree.rec is large-elim (Type-valued motive): Elim(RoseTree, 1, []).
    let elim = RawExpr::Elim(n("RoseTree"), lone(), vec![]);
    let app = r_apps(
        elim,
        vec![m_rt, m_l, node_minor, nil_minor, cons_minor, tree],
    );
    let t = Term::validate_closed(&env, &app).expect("rec app validates");

    // (1) It infers to `Nat`.
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("rec app infers");
    let nat = Term::validate_closed(&env, &r_const("Nat")).expect("Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &nat, &mut budget).expect("def_eq"),
        "RoseTree.rec size of the non-empty tree : Nat"
    );

    // (2) It ι-reduces (multi-step, THROUGH the children list) to EXACTLY 3.
    let three = Term::validate_closed(&env, &nat_lit(3)).expect("three");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &three, &mut budget).expect("def_eq"),
        "RoseTree.rec folds through RoseTree._List children: size(node 0 [node 1 [], node 2 []]) = 3"
    );

    // (3) DISCRIMINATING negative: it is NOT 1 (the empty-leaf-only answer). If the
    // recursor failed to recurse into the children list, the root's `ih_cs` would
    // be `nil_minor = 0` and the size would be `succ 0 = 1`. 3 ≠ 1 proves the
    // nested IH genuinely fired through the non-empty `RoseTree._List`.
    let one = Term::validate_closed(&env, &nat_lit(1)).expect("one");
    assert!(
        !clean_ck0::is_def_eq(&env, &t, &one, &mut budget).expect("def_eq"),
        "non-empty tree size must NOT be 1 (the empty-leaf-only answer) — nested IH is load-bearing"
    );
    // And not 2 either (a partial fold that missed one child).
    let two = Term::validate_closed(&env, &nat_lit(2)).expect("two");
    assert!(
        !clean_ck0::is_def_eq(&env, &t, &two, &mut budget).expect("def_eq"),
        "non-empty tree size must NOT be 2 (both children must be folded in)"
    );
}

// ===========================================================================
// C. NO-CONFUSION / INJECTIVITY: Nat.succ_ne_zero and Nat.succ.inj as CLOSED
//    proof terms built from Nat.rec / Eq.rec + a discriminating motive.
// ===========================================================================

/// The discriminating predicate `D : Nat -> Prop` with `D zero = False`,
/// `D (succ _) = True`, built by `Nat.rec`. Returns the RawExpr for `D` as a
/// closed lambda `fun (x:Nat) => Nat.rec (motive := fun _ => Prop) False .. x`.
fn discriminator_d() -> RawExpr {
    // `D : Nat -> Prop`, so the recursor motive `C := fun _:Nat => Prop` (each
    // `C n = Prop = Sort 0`). The result values `C n = Prop` live in `Sort 1`, so
    // the elimination level `u = 1`: Elim(Nat, 1, []). The minors return `Prop`:
    // zero-case := False : Prop, succ-case := fun (n:Nat)(ih:Prop) => True : Prop.
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]);
    let motive = r_lam(r_const("Nat"), r_prop()); // fun _:Nat => Prop (= Sort 0)
    let zero_case = r_const("False");
    // succ-case : (n:Nat) -> (ih:Prop) -> Prop := fun n ih => True. The `ih` binder
    // type is `C n = Prop`.
    let succ_case = r_lam(r_const("Nat"), r_lam(r_prop(), r_const("True")));
    r_lam(
        r_const("Nat"),
        r_apps(elim, vec![motive, zero_case, succ_case, r_bvar(0)]),
    )
}

#[test]
fn test_c_discriminator_reduces_on_both_constructors() {
    // Load-bearing ι-computation: D zero ι~> False, D (succ zero) ι~> True.
    let env = base_env();
    let d = discriminator_d();
    let mut budget = Budget::default_budget();

    let d_zero = Term::validate_closed(&env, &r_app(d.clone(), nat_zero())).expect("v");
    let false_t = Term::validate_closed(&env, &r_const("False")).expect("False");
    assert!(
        clean_ck0::is_def_eq(&env, &d_zero, &false_t, &mut budget).expect("def_eq"),
        "D zero ι-reduces to False"
    );

    let d_succ = Term::validate_closed(&env, &r_app(d.clone(), nat_lit(1))).expect("v");
    let true_t = Term::validate_closed(&env, &r_const("True")).expect("True");
    assert!(
        clean_ck0::is_def_eq(&env, &d_succ, &true_t, &mut budget).expect("def_eq"),
        "D (succ zero) ι-reduces to True"
    );
    // And the discrimination is REAL: D zero is NOT def-eq to True.
    assert!(
        !clean_ck0::is_def_eq(&env, &d_zero, &true_t, &mut budget).expect("def_eq"),
        "D zero must NOT be def-eq to True (discrimination is meaningful)"
    );
}

#[test]
fn test_c_succ_ne_zero_closed_proof_checks() {
    // Nat.succ_ne_zero : (n:Nat) -> Eq Nat (Nat.succ n) Nat.zero -> False
    // proof = fun (n:Nat) (h : succ n = zero) =>
    //   Eq.rec (motive := fun (x:Nat) (_:Eq Nat (succ n) x) => D x)
    //          (True.intro : D (succ n))   -- minor: motive (succ n) refl ≡ D (succ n) = True
    //          (x := zero) (h)             -- transports to D zero = False
    // Here `True.intro : True` and `D (succ n)` ι-reduces to `True`, so the minor
    // type-checks; the result `D zero` ι-reduces to `False`.
    let env = base_env();
    let d = discriminator_d();
    let d_of = |x: RawExpr| r_app(d.clone(), x);

    // TYPE: (n:Nat) -> Eq.{1} Nat (succ n) zero -> False
    let eq_nat =
        |x: RawExpr, y: RawExpr| r_apps(r_const_p("Eq", vec![lone()]), vec![r_const("Nat"), x, y]);
    let ty = r_pi(
        r_const("Nat"), // n   (bvar0 in body)
        r_pi(
            eq_nat(nat_succ(r_bvar(0)), nat_zero()), // succ n = zero   (h : bvar0)
            r_const("False"),
        ),
    );

    // Eq.rec is large-elim. motive : (x:Nat) -> Eq Nat (succ n) x -> Prop, so
    // motive_level = 0 (Prop), ind_level = 1 (A = Nat : Sort 1). Elim(Eq, 0, [1]).
    let elim = RawExpr::Elim(n("Eq"), lzero(), vec![lone()]);
    // motive = fun (x:Nat) (_:Eq Nat (succ n) x) => D x.
    // The HEQ-DOMAIN sits in context [n, h, x] (depth 3): x=bvar0, h=bvar1, n=bvar2.
    // The D-BODY sits in context [n, h, x, heq] (depth 4): x=bvar1, heq=bvar0, n=bvar3.
    let motive = r_lam(
        r_const("Nat"), // x : Nat   (domain in [n,h], depth 2)
        r_lam(
            eq_nat(nat_succ(r_bvar(2)), r_bvar(0)), // Eq Nat (succ n) x   (n=bvar2, x=bvar0)
            d_of(r_bvar(1)),                        // D x                 (x=bvar1)
        ),
    );
    // minor : motive (succ n) (Eq.refl ..) ≡ D (succ n) ≡ True. Provide True.intro.
    let minor = r_const("True.intro");
    // @Eq.rec Nat (succ n) motive minor zero h.   (params A=Nat, a=succ n; index x=zero; major h)
    let body = r_apps(
        elim,
        vec![
            r_const("Nat"),      // A
            nat_succ(r_bvar(1)), // a := succ n
            motive,
            minor,
            nat_zero(), // index x := zero
            r_bvar(0),  // major h
        ],
    );
    let proof = r_lam(
        r_const("Nat"),
        r_lam(eq_nat(nat_succ(r_bvar(0)), nat_zero()), body),
    );
    admit_theorem(&env, &ty, &proof, 0);
}

#[test]
fn test_c_succ_inj_closed_proof_checks() {
    // Nat.succ.inj : (m n:Nat) -> Eq Nat (succ m) (succ n) -> Eq Nat m n.
    // proof = fun (m n:Nat) (h : succ m = succ n) =>
    //   Eq.rec (motive := fun (x:Nat) (_:Eq Nat (succ m) x) => Eq Nat m (pred x))
    //          (Eq.refl Nat m : Eq Nat m (pred (succ m)))    -- pred (succ m) ι~> m
    //          (x := succ n) (h)
    //   : Eq Nat m (pred (succ n)) ≡ Eq Nat m n.
    // where pred := fun x => Nat.rec (motive := fun _ => Nat) zero (fun k _ => k) x
    //   pred zero ι~> zero, pred (succ k) ι~> k.
    let env = base_env();

    // pred : Nat -> Nat
    let pred = {
        let elim = RawExpr::Elim(n("Nat"), lone(), vec![]); // Type-valued (Nat), large elim
        let motive = r_lam(r_const("Nat"), r_const("Nat"));
        let zero_case = nat_zero();
        // succ-case : (k:Nat)(ih:Nat) -> Nat := fun k ih => k
        let succ_case = r_lam(r_const("Nat"), r_lam(r_const("Nat"), r_bvar(1)));
        r_lam(
            r_const("Nat"),
            r_apps(elim, vec![motive, zero_case, succ_case, r_bvar(0)]),
        )
    };
    let pred_of = |x: RawExpr| r_app(pred.clone(), x);

    let eq_nat =
        |x: RawExpr, y: RawExpr| r_apps(r_const_p("Eq", vec![lone()]), vec![r_const("Nat"), x, y]);
    // TYPE: (m n:Nat) -> Eq Nat (succ m) (succ n) -> Eq Nat m n.
    let ty = r_pi(
        r_const("Nat"), // m  (bvar1 in body)
        r_pi(
            r_const("Nat"), // n  (bvar0 in body before h)
            r_pi(
                eq_nat(nat_succ(r_bvar(1)), nat_succ(r_bvar(0))), // succ m = succ n
                eq_nat(r_bvar(2), r_bvar(1)),                     // m = n
            ),
        ),
    );
    // Eq.rec large-elim into Prop: Elim(Eq, 0, [1]).
    let elim = RawExpr::Elim(n("Eq"), lzero(), vec![lone()]);
    // proof body context [m, n, h]: m=bvar2, n=bvar1, h=bvar0 at the Eq.rec site.
    // motive = fun (x:Nat)(_:Eq Nat (succ m) x) => Eq Nat m (pred x).
    //   HEQ-DOMAIN in [m,n,h,x] (depth 4): x=bvar0, m=bvar3.
    //   BODY in [m,n,h,x,heq] (depth 5): x=bvar1, m=bvar4.
    let motive = r_lam(
        r_const("Nat"), // x
        r_lam(
            eq_nat(nat_succ(r_bvar(3)), r_bvar(0)), // Eq Nat (succ m) x   (m=bvar3, x=bvar0)
            eq_nat(r_bvar(4), pred_of(r_bvar(1))),  // Eq Nat m (pred x)   (m=bvar4, x=bvar1)
        ),
    );
    // minor : motive (succ m) refl ≡ Eq Nat m (pred (succ m)) ≡ Eq Nat m m. Provide
    // Eq.refl Nat m.
    let minor = r_apps(
        r_const_p("Eq.refl", vec![lone()]),
        vec![r_const("Nat"), r_bvar(2)], // refl Nat m   (m=bvar2 in proof body)
    );
    // @Eq.rec Nat (succ m) motive minor (succ n) h.
    let body = r_apps(
        elim,
        vec![
            r_const("Nat"),      // A
            nat_succ(r_bvar(2)), // a := succ m
            motive,
            minor,
            nat_succ(r_bvar(1)), // index x := succ n
            r_bvar(0),           // major h
        ],
    );
    let proof = r_lam(
        r_const("Nat"),
        r_lam(
            r_const("Nat"),
            r_lam(eq_nat(nat_succ(r_bvar(1)), nat_succ(r_bvar(0))), body),
        ),
    );
    admit_theorem(&env, &ty, &proof, 0);
}

// ===========================================================================
// D. HARDER ι-REDUCTION: Nat.add via Nat.rec; 2+2 ≡ 4, 2+2 ≢ 3.
// ===========================================================================

/// `Nat.add` as a typed transparent definition whose body is `Nat.rec` recursing
/// on the SECOND argument (Lean's `Nat.add` recurses on the second arg):
///   add m n := Nat.rec (motive := fun _ => Nat) m (fun _ ih => succ ih) n
/// so  add m 0 = m,  add m (succ k) = succ (add m k).
fn add_def_body() -> RawExpr {
    let elim = RawExpr::Elim(n("Nat"), lone(), vec![]); // Type-valued ⇒ large elim
                                                        // body: fun (m n:Nat) => Nat.rec (fun _:Nat => Nat) m (fun (k:Nat)(ih:Nat) => succ ih) n
                                                        // depth [m, n]: m=bvar1, n=bvar0.
    let motive = r_lam(r_const("Nat"), r_const("Nat"));
    let base = r_bvar(1); // m
    let step = r_lam(r_const("Nat"), r_lam(r_const("Nat"), nat_succ(r_bvar(0)))); // λ k ih => succ ih
    r_lam(
        r_const("Nat"),
        r_lam(
            r_const("Nat"),
            r_apps(elim, vec![motive, base, step, r_bvar(0)]),
        ),
    )
}

/// Env with Nat + a transparent `Nat.add : Nat -> Nat -> Nat`.
fn add_env() -> MinimalEnv {
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, nat_decl()).expect("Nat admits");
    // add : Nat -> Nat -> Nat
    let add_ty = Term::validate_closed(
        &env,
        &r_pi(r_const("Nat"), r_pi(r_const("Nat"), r_const("Nat"))),
    )
    .expect("add type validates");
    let add_body = Term::validate_closed(&env, &add_def_body()).expect("add body validates");
    // The body must check against the declared type before we register it (real,
    // not _unchecked): infer the body and confirm it is def-eq to add_ty.
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &add_body, &add_ty, &mut budget)
        .expect("Nat.add body checks against Nat -> Nat -> Nat");
    env.with_def(n("Nat.add"), 0, add_ty, add_body, Transparency::Transparent)
}

fn add(x: RawExpr, y: RawExpr) -> RawExpr {
    r_apps(r_const("Nat.add"), vec![x, y])
}

#[test]
fn test_d_add_body_checks_and_two_plus_two_is_four() {
    let env = add_env();
    let mut budget = Budget::default_budget();
    // add 2 2 : Nat
    let t = Term::validate_closed(&env, &add(nat_lit(2), nat_lit(2))).expect("validates");
    let inferred = clean_ck0::infer(&env, &t, &mut budget).expect("infers");
    let nat = Term::validate_closed(&env, &r_const("Nat")).expect("Nat");
    assert!(
        clean_ck0::is_def_eq(&env, &inferred, &nat, &mut budget).expect("def_eq"),
        "add 2 2 : Nat"
    );
    // Genuine MULTI-step ι: add 2 2 ≡ 4.
    let four = Term::validate_closed(&env, &nat_lit(4)).expect("four");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &four, &mut budget).expect("def_eq"),
        "add 2 2 multi-step ι-reduces to 4"
    );
    // It is NOT one-step: confirm the intermediate `add 2 1` is succ-ish, i.e.
    // add 2 2 ≢ 3 (so we really computed, not matched a trivial shape).
    let three = Term::validate_closed(&env, &nat_lit(3)).expect("three");
    assert!(
        !clean_ck0::is_def_eq(&env, &t, &three, &mut budget).expect("def_eq"),
        "add 2 2 must NOT be def-eq to 3"
    );
}

#[test]
fn test_d_add_zero_and_comm_statements_type_check() {
    // The PROOFS need def-by-recursion (induction) on Nat, which is out of M0–M3
    // scope (no def-by-rec frontend / no `rfl`-by-computation for the open case);
    // but the STATEMENTS are real Props that must type-check.
    let env = add_env();
    let eq_nat =
        |x: RawExpr, y: RawExpr| r_apps(r_const_p("Eq", vec![lone()]), vec![r_const("Nat"), x, y]);
    let env = {
        // We need Eq to state the theorems.
        let mut e = env;
        add_inductive(&mut e, eq_decl()).expect("Eq admits");
        e
    };
    let mut budget = Budget::default_budget();

    // add_zero : (n:Nat) -> Eq Nat (add n zero) n
    let add_zero = r_pi(
        r_const("Nat"),
        eq_nat(add(r_bvar(0), nat_zero()), r_bvar(0)),
    );
    let t = Term::validate_closed(&env, &add_zero).expect("validates");
    let s = clean_ck0::infer_sort_in_context(&env, &[], &t, &mut budget)
        .expect("add_zero statement is a well-formed type");
    assert!(s.is_zero(), "add_zero is a Prop");

    // add_comm : (m n:Nat) -> Eq Nat (add m n) (add n m)
    let add_comm = r_pi(
        r_const("Nat"),
        r_pi(
            r_const("Nat"),
            eq_nat(add(r_bvar(1), r_bvar(0)), add(r_bvar(0), r_bvar(1))),
        ),
    );
    let t = Term::validate_closed(&env, &add_comm).expect("validates");
    let s = clean_ck0::infer_sort_in_context(&env, &[], &t, &mut budget)
        .expect("add_comm statement is a well-formed type");
    assert!(s.is_zero(), "add_comm is a Prop");
}

// ===========================================================================
// E. NEGATIVE CONTROLS — every acceptance above is meaningful.
// ===========================================================================

#[test]
fn test_e1_non_positive_nested_inductive_rejected() {
    // A non-strictly-positive NESTED inductive: `Bad : Type` with
    // `Bad.mk : List (Bad -> Bad) -> Bad`. The nesting arg `(Bad -> Bad)` puts
    // Bad to the LEFT of an arrow, so the nesting is non-positive: REJECT.
    let mut env = env_with_list();
    let b = MinimalEnv::new()
        .with_const(n("Bad"), 0)
        .with_const(n("Bad.mk"), 0)
        .with_const(n("List"), 1);
    let ty = vlvl(&b, &r_sort(1), 0);
    // field : List.{1} (Bad -> Bad)
    let inner = r_pi(r_const("Bad"), r_const("Bad"));
    let field = r_app(r_const_p("List", vec![lone()]), inner);
    let mk_ty = vlvl(&b, &r_pi(field, r_const("Bad")), 0);
    let decl = InductiveDecl {
        name: n("Bad"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("Bad.mk"),
            type_: mk_ty,
        }],
    };
    let r = add_inductive_nested(&mut env, decl);
    assert!(
        matches!(
            r,
            Err(clean_ck0::NestedError::NonStrictlyPositiveNesting { .. })
        ),
        "non-positive nesting must be NonStrictlyPositiveNesting, got {r:?}"
    );
}

#[test]
fn test_e1b_non_positive_direct_inductive_rejected() {
    // The direct (non-nested) analogue: `Tree` with `bad : (Tree -> Tree) -> Tree`
    // must be rejected NonPositive at single-inductive admission.
    let b = boot(&[("BadTree", 0), ("BadTree.bad", 0)]);
    let ty = vlvl(&b, &r_sort(1), 0);
    let mk_ty = vlvl(
        &b,
        &r_pi(
            r_pi(r_const("BadTree"), r_const("BadTree")),
            r_const("BadTree"),
        ),
        0,
    );
    let decl = InductiveDecl {
        name: n("BadTree"),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors: vec![Constructor {
            name: n("BadTree.bad"),
            type_: mk_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    let r = add_inductive(&mut env, decl);
    assert!(
        matches!(r, Err(clean_ck0::AdmitError::NonPositive { .. })),
        "direct non-positive inductive must be NonPositive, got {r:?}"
    );
}

#[test]
fn test_e2_illtyped_no_confusion_leak_rejected() {
    // An ill-typed no-confusion attempt: try to use the discriminator BACKWARD to
    // forge `False` from `zero = succ zero` WITHOUT a hypothesis — i.e. claim that
    // `True.intro : D zero`. Since D zero ι~> False, `True.intro : False` is the
    // forbidden leak. The kernel must REJECT `True.intro : D zero` (True.intro :
    // True, and True ≢ D zero = False).
    let env = base_env();
    let d = discriminator_d();
    let d_zero = r_app(d.clone(), nat_zero()); // ι~> False
    let claimed_ty = Term::validate_closed(&env, &d_zero).expect("D zero validates");
    let leak = Term::validate_closed(&env, &r_const("True.intro")).expect("True.intro validates");
    let mut budget = Budget::default_budget();
    // NON-VACUOUS: True.intro DOES check against True (the term itself is fine — the
    // rejection below is purely about the FALSE claim `True.intro : D zero`).
    let true_t = Term::validate_closed(&env, &r_const("True")).expect("True");
    clean_ck0::check(&env, &leak, &true_t, &mut budget).expect("True.intro : True (sanity)");
    // The forged leak must be rejected for TypeMismatch (True ≢ D zero = False).
    let r = clean_ck0::check(&env, &leak, &claimed_ty, &mut budget);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "True.intro must be rejected TypeMismatch against `D zero` (= False): {r:?}"
    );

    // And the symmetric forgery: a closed term claiming `succ_ne_zero` WITHOUT the
    // hypothesis — `fun (n:Nat) => True.intro : ... -> False` directly — must fail.
    let bad_proof = r_lam(r_const("Nat"), r_const("True.intro"));
    let bad_ty = r_pi(r_const("Nat"), r_const("False")); // (n:Nat) -> False  (absurd)
    let p = Term::validate_closed(&env, &bad_proof).expect("validates");
    let ft = Term::validate_closed(&env, &bad_ty).expect("validates");
    let r2 = clean_ck0::check(&env, &p, &ft, &mut budget);
    assert!(
        matches!(r2, Err(clean_ck0::InferError::TypeMismatch)),
        "fun n => True.intro must be rejected TypeMismatch against (n:Nat) -> False: {r2:?}"
    );
}

#[test]
fn test_e3_wrong_mutual_recursor_motive_rejected() {
    // A wrong mutual recursor motive (mismatched index) must be rejected by infer
    // with TypeMismatch. We feed Even.rec a motive_E whose major-domain index is
    // wrong: motive_E : (k:Nat) -> Odd k -> Prop  (Odd instead of Even) — the
    // major `Even k` cannot match the motive's expected `Odd k` major domain.
    let env = even_odd_env();
    let even = |k: RawExpr| r_app(r_const("Even"), k);
    let odd = |k: RawExpr| r_app(r_const("Odd"), k);
    // BAD motive_E: fun (k:Nat) (_:Odd k) => Even k   -- expects an Odd major.
    let bad_motive_e = r_lam(r_const("Nat"), r_lam(odd(r_bvar(0)), even(r_bvar(1))));
    let motive_o = r_lam(r_const("Nat"), r_lam(odd(r_bvar(0)), odd(r_bvar(1))));
    let m_ez = r_const("even_zero");
    let m_es = r_lam(
        r_const("Nat"),
        r_lam(
            odd(r_bvar(0)),
            r_lam(
                odd(r_bvar(1)),
                r_apps(r_const("even_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    let m_os = r_lam(
        r_const("Nat"),
        r_lam(
            even(r_bvar(0)),
            r_lam(
                even(r_bvar(1)),
                r_apps(r_const("odd_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    let elim = RawExpr::Elim(n("Even"), lzero(), vec![]);
    let app = r_apps(
        elim,
        vec![
            bad_motive_e,
            motive_o,
            m_ez,
            m_es,
            m_os,
            nat_zero(),           // index k := 0
            r_const("even_zero"), // major : Even 0
        ],
    );
    let t = Term::validate_closed(&env, &app).expect("structurally validates");
    let mut budget = Budget::default_budget();
    let r = clean_ck0::infer(&env, &t, &mut budget);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "Even.rec with a wrong motive_E (Odd-major) must fail TypeMismatch: {r:?}"
    );

    // NON-VACUOUS: the SAME application with the CORRECT motive_E (Even-major) DOES
    // infer — so the rejection above is specifically the bad motive, not a broken
    // recursor application shape.
    let good_motive_e = r_lam(r_const("Nat"), r_lam(even(r_bvar(0)), even(r_bvar(1))));
    let motive_o2 = r_lam(r_const("Nat"), r_lam(odd(r_bvar(0)), odd(r_bvar(1))));
    let m_ez2 = r_const("even_zero");
    let m_es2 = r_lam(
        r_const("Nat"),
        r_lam(
            odd(r_bvar(0)),
            r_lam(
                odd(r_bvar(1)),
                r_apps(r_const("even_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    let m_os2 = r_lam(
        r_const("Nat"),
        r_lam(
            even(r_bvar(0)),
            r_lam(
                even(r_bvar(1)),
                r_apps(r_const("odd_succ"), vec![r_bvar(2), r_bvar(0)]),
            ),
        ),
    );
    let elim2 = RawExpr::Elim(n("Even"), lzero(), vec![]);
    let good_app = r_apps(
        elim2,
        vec![
            good_motive_e,
            motive_o2,
            m_ez2,
            m_es2,
            m_os2,
            nat_zero(),
            r_const("even_zero"),
        ],
    );
    let gt = Term::validate_closed(&env, &good_app).expect("validates");
    clean_ck0::infer(&env, &gt, &mut budget).expect("Even.rec with correct motive_E infers");
}

#[test]
fn test_e4_two_plus_two_not_def_eq_five() {
    let env = add_env();
    let mut budget = Budget::default_budget();
    let t = Term::validate_closed(&env, &add(nat_lit(2), nat_lit(2))).expect("validates");
    let five = Term::validate_closed(&env, &nat_lit(5)).expect("five");
    assert!(
        !clean_ck0::is_def_eq(&env, &t, &five, &mut budget).expect("def_eq"),
        "add 2 2 must NOT be def-eq to 5"
    );
    // Sanity: it IS def-eq to 4 (so the negative result is not vacuous).
    let four = Term::validate_closed(&env, &nat_lit(4)).expect("four");
    assert!(
        clean_ck0::is_def_eq(&env, &t, &four, &mut budget).expect("def_eq"),
        "add 2 2 IS def-eq to 4 (negative control is non-vacuous)"
    );
}

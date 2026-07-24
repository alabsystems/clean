// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: elimination of *imported* `Prop`-valued inductives whose
//! recursors carry the special **large-elimination** rules (prop_recursor
//! scenario).
//!
//! ## What a Prop inductive's eliminator encodes
//!
//! A `Prop`-valued inductive's recursor has a universe shape that depends on
//! whether the type is *subsingleton-eligible* (large-elimination eligible):
//!
//! - A **single-constructor** Prop inductive all of whose fields are themselves
//!   `Prop` (e.g. `And`, `Eq`, `Acc`) permits **large elimination** — its
//!   `.rec`/`.casesOn` is universe-polymorphic in the motive: `{motive : … →
//!   Sort u}`, so the recursor carries an *extra* motive universe parameter.
//! - A **two-constructor** Prop inductive (e.g. `Or`) does **not** permit large
//!   elimination — its `.rec`/`.casesOn` only eliminates into `Prop`:
//!   `{motive : … → Prop}`, with **no** motive universe parameter.
//!
//! The kernel computes this via `elim_only_at_universe_zero`; for the latter the
//! recursor's `level_params` is exactly the inductive's (no extra `u`).
//!
//! ## Why imports are special (mirrors B43/B45/B47/B48)
//!
//! A native clean-built inductive registers `T.casesOn` as a *recursor*
//! (`RecursorVal`) that records `level_params` directly. A real Lean `.olean`
//! ships ONLY the recursor `T.rec` plus a **definitional** `T.casesOn` constant
//! in the `MajorAfterMotive` layout — `get_recursor("T.casesOn") == None`.
//!
//! The match elaborator picks the eliminator's universe instantiation in
//! `eliminator_levels` (`infer/elab_match/helpers.rs`). On the native path it
//! reads the recursor's `level_params` and *only* prepends a motive universe
//! when the recursor actually has one (`has_motive_univ`). On the **import**
//! path the recursor is absent, so it took the fallback heuristic — which
//! **unconditionally** prepended a motive universe level. For an imported
//! Prop-only `Or.casesOn` (whose declared `level_params` is empty) that emits
//! `Or.casesOn.{u}` — a constant applied to ONE universe level when it declares
//! ZERO — which the kernel rejects with a universe-arity mismatch. So a match on
//! an imported `Or` (eliminating into `Prop`) failed to elaborate even though it
//! is perfectly legal.
//!
//! ## The probes
//!
//! (a) `MyAnd` (single ctor, both fields Prop → large elim): project a
//!     component out of an imported `And` via a `match`, eliminating into a
//!     proof — exercises the large-elim motive-universe path on import.
//! (b) `MyEq`-style transport: eliminate an imported subsingleton (single ctor)
//!     into a large (`Type`) motive — the large-elimination capability itself.
//! (c) `MyOr` (two ctors → Prop-only): `match` on an imported `Or` into `Prop`.
//!     This is the direct repro of the universe-arity bug above.
//!
//! Native controls (where `T.casesOn` IS a recursor) run alongside so the fix is
//! shown general, not import-specific, and native behavior stays unchanged.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Declaration;
use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to WHNF and return the head `Const` name.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn def_eq(env: &Environment, a: &Expr, b: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(a, b)
}

/// Elaborate + register declarations from `source`. `elaborate_decl_and_register`
/// runs the full kernel type-check per definition; reaching the end means every
/// body kernel-checked.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

// ---------------------------------------------------------------------------
// Prop inductives.
//
// `MyOr (a b : Prop) : Prop` with `inl : a → MyOr a b` and `inr : b → MyOr a b`
// is a TWO-constructor Prop inductive → Prop-only elimination (no motive univ).
//
// `MyAnd (a b : Prop) : Prop` with `intro : a → b → MyAnd a b` is a
// single-constructor Prop inductive all of whose fields are Prop → large elim
// (the recursor carries a motive universe parameter).
// ---------------------------------------------------------------------------

/// `inductive MyOr (a b : Prop) : Prop | inl (h : a) | inr (h : b)`.
fn myor_decl() -> InductiveDecl {
    // MyOr : Prop -> Prop -> Prop
    let myor_ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );
    // MyOr a b under [a, b]: `MyOr #1 #0`
    let myor_ab = Expr::app(Expr::app(const_("MyOr"), Expr::bvar(1)), Expr::bvar(0));
    // inl : (a b : Prop) -> a -> MyOr a b
    //   under [a, b, h:a]: a = #2, MyOr a b = MyOr #2 #1
    let inl_ret = Expr::app(Expr::app(const_("MyOr"), Expr::bvar(2)), Expr::bvar(1));
    let inl_ty = Expr::pi(BinderInfo::Default, Expr::bvar(1), inl_ret); // h : a (a = #1 under [a,b])
    let inl_ty = Expr::pi(BinderInfo::Default, Expr::prop(), inl_ty); // b
    let inl_ty = Expr::pi(BinderInfo::Default, Expr::prop(), inl_ty); // a
                                                                      // inr : (a b : Prop) -> b -> MyOr a b
    let inr_ret = Expr::app(Expr::app(const_("MyOr"), Expr::bvar(2)), Expr::bvar(1));
    let inr_ty = Expr::pi(BinderInfo::Default, Expr::bvar(0), inr_ret); // h : b (b = #0 under [a,b])
    let inr_ty = Expr::pi(BinderInfo::Default, Expr::prop(), inr_ty); // b
    let inr_ty = Expr::pi(BinderInfo::Default, Expr::prop(), inr_ty); // a
    let _ = myor_ab;

    InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("MyOr"),
            type_: myor_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOr.inl"),
                    type_: inl_ty,
                },
                Constructor {
                    name: Name::from_string("MyOr.inr"),
                    type_: inr_ty,
                },
            ],
        }],
    }
}

/// `inductive MyAnd (a b : Prop) : Prop | intro (l : a) (r : b)`.
fn myand_decl() -> InductiveDecl {
    let myand_ty = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    );
    // intro : (a b : Prop) -> a -> b -> MyAnd a b
    //   under [a, b, l:a, r:b]: a = #3, b = #2, MyAnd a b = MyAnd #3 #2
    let intro_ret = Expr::app(Expr::app(const_("MyAnd"), Expr::bvar(3)), Expr::bvar(2));
    let intro_ty = Expr::pi(BinderInfo::Default, Expr::bvar(1), intro_ret); // r : b (b = #1 under [a,b,l])
    let intro_ty = Expr::pi(BinderInfo::Default, Expr::bvar(1), intro_ty); // l : a (a = #1 under [a,b])
    let intro_ty = Expr::pi(BinderInfo::Default, Expr::prop(), intro_ty); // b
    let intro_ty = Expr::pi(BinderInfo::Default, Expr::prop(), intro_ty); // a

    InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("MyAnd"),
            type_: myand_ty,
            constructors: vec![Constructor {
                name: Name::from_string("MyAnd.intro"),
                type_: intro_ty,
            }],
        }],
    }
}

// ---------------------------------------------------------------------------
// `MyOr` imported casesOn (Prop-only: NO motive universe parameter).
//
// MajorAfterMotive layout:
//   MyOr.casesOn :
//     {a b : Prop} -> {motive : MyOr a b -> Prop} -> (t : MyOr a b)
//       -> ((h : a) -> motive (MyOr.inl a b h))
//       -> ((h : b) -> motive (MyOr.inr a b h))
//       -> motive t
//   := fun a b motive t m_inl m_inr => MyOr.rec a b motive m_inl m_inr t
// ---------------------------------------------------------------------------

/// `MyOr.inl a b h` / `MyOr.inr a b h` under a binder telescope where the
/// supplied exprs already reference the right BVars.
fn myor_ctor(ctor: &str, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(const_(ctor), a), b), h)
}

/// `MyOr a b`.
fn myor_at(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(const_("MyOr"), a), b)
}

fn myor_imported_cases_type() -> Expr {
    // Telescope (outer -> inner): a, b, motive, t, m_inl, m_inr.
    // Indices inside the innermost scope [a,b,motive,t,m_inl,m_inr]:
    //   a=5, b=4, motive=3, t=2, m_inl=1, m_inr=0
    // result `motive t`: motive=#3, t=#2
    let result = Expr::app(Expr::bvar(3), Expr::bvar(2));

    // m_inr domain under [a,b,motive,t,m_inl]: (h : b) -> motive (MyOr.inr a b h)
    //   inside h scope [a,b,motive,t,m_inl,h]: a=5, b=4, motive=3, h=0
    let m_inr_body = Expr::app(
        Expr::bvar(3),
        myor_ctor("MyOr.inr", Expr::bvar(5), Expr::bvar(4), Expr::bvar(0)),
    );
    let m_inr_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_inr_body); // h : b (b=#3 under [a,b,motive,t,m_inl])

    // m_inl domain under [a,b,motive,t]: (h : a) -> motive (MyOr.inl a b h)
    //   inside h scope [a,b,motive,t,h]: a=4, b=3, motive=2, h=0
    let m_inl_body = Expr::app(
        Expr::bvar(2),
        myor_ctor("MyOr.inl", Expr::bvar(4), Expr::bvar(3), Expr::bvar(0)),
    );
    let m_inl_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_inl_body); // h : a (a=#3 under [a,b,motive,t])

    // t domain under [a,b,motive]: MyOr a b (a=#2, b=#1)
    let t_dom = myor_at(Expr::bvar(2), Expr::bvar(1));
    // motive domain under [a,b]: MyOr a b -> Prop (a=#1, b=#0)
    let motive_dom = Expr::pi(
        BinderInfo::Default,
        myor_at(Expr::bvar(1), Expr::bvar(0)),
        Expr::prop(),
    );

    let body = Expr::pi(BinderInfo::Default, m_inr_dom, result);
    let body = Expr::pi(BinderInfo::Default, m_inl_dom, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, motive_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, Expr::prop(), body); // b
    Expr::pi(BinderInfo::Implicit, Expr::prop(), body) // a
}

fn myor_imported_cases_value() -> Expr {
    // value body under [a,b,motive,t,m_inl,m_inr]:
    //   MyOr.rec a b motive m_inl m_inr t  (native MajorAfterMinors)
    //   a=5, b=4, motive=3, t=2, m_inl=1, m_inr=0
    let rec = Expr::const_(Name::from_string("MyOr.rec"), vec![]);
    let body = Expr::app(rec, Expr::bvar(5)); // a
    let body = Expr::app(body, Expr::bvar(4)); // b
    let body = Expr::app(body, Expr::bvar(3)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // m_inl
    let body = Expr::app(body, Expr::bvar(0)); // m_inr
    let body = Expr::app(body, Expr::bvar(2)); // t (major last)

    // Rebuild the same binder domains as the type, as lambdas.
    let m_inr_body = Expr::app(
        Expr::bvar(3),
        myor_ctor("MyOr.inr", Expr::bvar(5), Expr::bvar(4), Expr::bvar(0)),
    );
    let m_inr_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_inr_body);
    let m_inl_body = Expr::app(
        Expr::bvar(2),
        myor_ctor("MyOr.inl", Expr::bvar(4), Expr::bvar(3), Expr::bvar(0)),
    );
    let m_inl_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_inl_body);
    let t_dom = myor_at(Expr::bvar(2), Expr::bvar(1));
    let motive_dom = Expr::pi(
        BinderInfo::Default,
        myor_at(Expr::bvar(1), Expr::bvar(0)),
        Expr::prop(),
    );

    let body = Expr::lam(BinderInfo::Default, m_inr_dom, body);
    let body = Expr::lam(BinderInfo::Default, m_inl_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, motive_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, Expr::prop(), body); // b
    Expr::lam(BinderInfo::Implicit, Expr::prop(), body) // a
}

/// Copy the kernel-built `MyOr` core (inductive + ctors + `MyOr.rec`) into
/// `env`, then synthesize the definitional `MyOr.casesOn` — mirroring `.olean`
/// import: `MyOr.rec` stays a recursor; `MyOr.casesOn` is a plain constant.
fn imported_myor_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.add_inductive(myor_decl()).expect("MyOr declares");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let iv = native
        .get_inductive(&Name::from_string("MyOr"))
        .cloned()
        .expect("MyOr inductive");
    env.register_inductive(iv);
    for ctor in ["MyOr.inl", "MyOr.inr"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let rv = native
        .get_recursor(&Name::from_string("MyOr.rec"))
        .cloned()
        .expect("MyOr.rec recursor");
    let rc = native
        .get_const(&Name::from_string("MyOr.rec"))
        .cloned()
        .expect("MyOr.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked against the casesOn type by `add_decl_structural`. This
    // reproduces exactly what an `.olean` import of a Prop-only inductive ships:
    // `MyOr.rec` present as a recursor, `MyOr.casesOn` a definitional constant
    // (NOT a registered recursor) with EMPTY level params (Prop-only ⇒ no motive
    // universe). No production path is involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("MyOr.casesOn"),
        level_params: vec![],
        type_: myor_imported_cases_type(),
        value: myor_imported_cases_value(),
        is_reducible: false,
    })
    .expect("imported MyOr.casesOn should kernel-check");

    env
}

// ===========================================================================
// Precondition: the synthesized `MyOr` matches the IMPORT configuration:
// recursor present, `.casesOn` a definitional constant (NOT a recursor) with
// EMPTY level params (Prop-only ⇒ no motive universe). This proves the probes
// exercise the import path AND the Prop-only universe shape.
// ===========================================================================

#[test]
fn test_imported_myor_cases_on_is_prop_only_definition_not_recursor() {
    let env = imported_myor_env();

    let ind = env
        .get_inductive(&Name::from_string("MyOr"))
        .expect("MyOr inductive imported");
    assert!(
        !ind.is_large_elim,
        "MyOr is a two-constructor Prop inductive: it must NOT permit large elimination"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyOr.rec")).is_some(),
        "MyOr.rec stays a registered recursor on import"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyOr.casesOn"))
            .is_none(),
        "imported MyOr.casesOn must NOT be a registered recursor — routes match \
         lowering through the imported MajorAfterMotive path"
    );
    let cases = env
        .get_const(&Name::from_string("MyOr.casesOn"))
        .expect("MyOr.casesOn const exists");
    assert!(
        cases.value.is_some(),
        "imported MyOr.casesOn must be a definitional constant with a value"
    );
    assert!(
        cases.level_params.is_empty(),
        "imported Prop-only MyOr.casesOn must have ZERO universe params (no motive \
         universe). The recursor's true universe arity is what the elaborator must \
         emit; got {:?}",
        cases.level_params
    );
}

// ===========================================================================
// MAIN PROBE (c): `match` on an imported two-constructor Prop inductive `MyOr`,
// eliminating into `Prop`. The result type is constant in the scrutinee, so the
// motive is `fun _ => MyOr b a : Prop`. The imported Prop-only `MyOr.casesOn`
// declares ZERO universe params; the elaborator must instantiate it with ZERO
// universe levels. Emitting a spurious motive universe (the bug) yields
// `MyOr.casesOn.{0}` — one level where none is declared — which the kernel
// rejects. We assert the def elaborates, compiles through the imported
// `MyOr.casesOn`, and reduces each branch to the correct (distinct) commuted
// constructor.
// ===========================================================================

#[test]
fn test_match_on_imported_prop_only_or_eliminates_into_prop() {
    let mut env = imported_myor_env();

    // orComm : commute an imported `MyOr` into `Prop`. Branches return DISTINCT
    // constructors (inl -> inr, inr -> inl) so a mis-routed branch is observable.
    elaborate_decls_into(
        &mut env,
        "def orComm (a b : Prop) (h : MyOr a b) : MyOr b a := match h with\n  \
         | MyOr.inl ha => MyOr.inr b a ha\n  \
         | MyOr.inr hb => MyOr.inl b a hb",
    );

    let info = env
        .get_const(&Name::from_string("orComm"))
        .expect("orComm should be registered");
    let body = info.value.as_ref().expect("orComm is a definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyOr.casesOn")),
        "orComm must compile through the imported MyOr.casesOn, got: {:?}",
        body.collect_constants()
    );

    // Two distinct atomic Props P, Q with proofs, and witnesses orPQ/orQP, so the
    // branches reduce to observable distinct constructor heads.
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def orPQ : MyOr P Q := MyOr.inl P Q hp\n\
         def orQP : MyOr P Q := MyOr.inr P Q hq",
    );

    // orComm P Q (MyOr.inl P Q hp) ~> MyOr.inr Q P hp  (head MyOr.inr).
    let call_inl = Expr::app(
        Expr::app(Expr::app(const_("orComm"), const_("P")), const_("Q")),
        const_("orPQ"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inl).as_deref(),
        Some("MyOr.inr"),
        "orComm on an inl-built MyOr must reduce to the inr branch (MyOr.inr)"
    );

    // orComm P Q (MyOr.inr P Q hq) ~> MyOr.inl Q P hq  (head MyOr.inl).
    let call_inr = Expr::app(
        Expr::app(Expr::app(const_("orComm"), const_("P")), const_("Q")),
        const_("orQP"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inr).as_deref(),
        Some("MyOr.inl"),
        "orComm on an inr-built MyOr must reduce to the inl branch (MyOr.inl)"
    );

    // Distinct heads: a collapsed/mis-routed branch would surface here.
    assert_ne!(
        whnf_head_const(&env, &call_inl),
        whnf_head_const(&env, &call_inr),
        "the two branches must reduce to distinct constructor heads (inr vs inl)"
    );
}

// ---------------------------------------------------------------------------
// `MyAnd` imported casesOn (single ctor, all-Prop fields ⇒ LARGE elim:
// the eliminator DOES carry a motive universe parameter `u`).
//
// MajorAfterMotive layout:
//   MyAnd.casesOn.{u} :
//     {a b : Prop} -> {motive : MyAnd a b -> Sort u} -> (t : MyAnd a b)
//       -> ((l : a) -> (r : b) -> motive (MyAnd.intro a b l r))
//       -> motive t
//   := fun a b motive t m_intro => MyAnd.rec.{u} a b motive m_intro t
// ---------------------------------------------------------------------------

/// `MyAnd a b`.
fn myand_at(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(const_("MyAnd"), a), b)
}

/// `MyAnd.intro a b l r`.
fn myand_intro(a: Expr, b: Expr, l: Expr, r: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::app(Expr::app(const_("MyAnd.intro"), a), b), l),
        r,
    )
}

fn myand_imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // Telescope (outer -> inner): a, b, motive, t, m_intro.
    // Innermost scope [a,b,motive,t,m_intro]: a=4, b=3, motive=2, t=1, m_intro=0
    // result `motive t`: motive=#2, t=#1
    let result = Expr::app(Expr::bvar(2), Expr::bvar(1));

    // m_intro domain under [a,b,motive,t]:
    //   (l : a) -> (r : b) -> motive (MyAnd.intro a b l r)
    //   inside [a,b,motive,t,l,r]: a=5, b=4, motive=3, t=2, l=1, r=0
    let m_intro_body = Expr::app(
        Expr::bvar(3),
        myand_intro(Expr::bvar(5), Expr::bvar(4), Expr::bvar(1), Expr::bvar(0)),
    );
    // r : b — inside [a,b,motive,t,l]: a=4, b=3, motive=2, t=1, l=0 ⇒ b=#3
    let m_intro_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_intro_body);
    // l : a — inside [a,b,motive,t]: a=3 ⇒ a=#3
    let m_intro_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_intro_dom);

    // t domain under [a,b,motive]: MyAnd a b (a=#2, b=#1)
    let t_dom = myand_at(Expr::bvar(2), Expr::bvar(1));
    // motive domain under [a,b]: MyAnd a b -> Sort u (a=#1, b=#0)
    let motive_dom = Expr::pi(
        BinderInfo::Default,
        myand_at(Expr::bvar(1), Expr::bvar(0)),
        sort_u,
    );

    let body = Expr::pi(BinderInfo::Default, m_intro_dom, result);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, motive_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, Expr::prop(), body); // b
    Expr::pi(BinderInfo::Implicit, Expr::prop(), body) // a
}

fn myand_imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("MyAnd.rec"),
        vec![Level::param(u.clone())],
    );
    let sort_u = Expr::sort(Level::param(u.clone()));
    // body under [a,b,motive,t,m_intro]:
    //   MyAnd.rec.{u} a b motive m_intro t  (native MajorAfterMinors)
    //   a=4, b=3, motive=2, t=1, m_intro=0
    let body = Expr::app(rec, Expr::bvar(4)); // a
    let body = Expr::app(body, Expr::bvar(3)); // b
    let body = Expr::app(body, Expr::bvar(2)); // motive
    let body = Expr::app(body, Expr::bvar(0)); // m_intro
    let body = Expr::app(body, Expr::bvar(1)); // t (major last)

    let m_intro_body = Expr::app(
        Expr::bvar(3),
        myand_intro(Expr::bvar(5), Expr::bvar(4), Expr::bvar(1), Expr::bvar(0)),
    );
    let m_intro_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_intro_body); // r : b (b=#3)
    let m_intro_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3), m_intro_dom); // l : a (a=#3)
    let t_dom = myand_at(Expr::bvar(2), Expr::bvar(1));
    let motive_dom = Expr::pi(
        BinderInfo::Default,
        myand_at(Expr::bvar(1), Expr::bvar(0)),
        sort_u,
    );

    let body = Expr::lam(BinderInfo::Default, m_intro_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, motive_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, Expr::prop(), body); // b
    Expr::lam(BinderInfo::Implicit, Expr::prop(), body) // a
}

/// Copy the kernel-built `MyAnd` core into `env`, then synthesize the
/// definitional `MyAnd.casesOn`. Mirrors `.olean` import of a large-elim Prop
/// inductive: `MyAnd.rec` stays a recursor; `MyAnd.casesOn` a plain constant
/// WITH a motive universe parameter `u`.
fn imported_myand_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.add_inductive(myand_decl()).expect("MyAnd declares");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let iv = native
        .get_inductive(&Name::from_string("MyAnd"))
        .cloned()
        .expect("MyAnd inductive");
    env.register_inductive(iv);
    let c = native
        .get_constructor(&Name::from_string("MyAnd.intro"))
        .cloned()
        .expect("MyAnd.intro ctor");
    env.register_constructor(c);
    let rv = native
        .get_recursor(&Name::from_string("MyAnd.rec"))
        .cloned()
        .expect("MyAnd.rec recursor");
    let rc = native
        .get_const(&Name::from_string("MyAnd.rec"))
        .cloned()
        .expect("MyAnd.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);

    let u = native
        .get_recursor(&Name::from_string("MyAnd.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("MyAnd.rec has a motive universe parameter (large elim)");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked against the casesOn type by `add_decl_structural`. This
    // reproduces what an `.olean` import of a single-constructor all-Prop-field
    // inductive ships: `MyAnd.rec` present as a recursor, `MyAnd.casesOn` a
    // definitional constant (NOT a registered recursor) WITH one motive universe
    // param (large elim). No production path is involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("MyAnd.casesOn"),
        level_params: vec![u.clone()],
        type_: myand_imported_cases_type(&u),
        value: myand_imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported MyAnd.casesOn should kernel-check");

    env
}

// ===========================================================================
// Precondition: the synthesized `MyAnd` is large-elim and `.casesOn` is a
// definitional constant (NOT a recursor) carrying exactly ONE motive universe.
// ===========================================================================

#[test]
fn test_imported_myand_cases_on_is_large_elim_definition_not_recursor() {
    let env = imported_myand_env();

    let ind = env
        .get_inductive(&Name::from_string("MyAnd"))
        .expect("MyAnd inductive imported");
    assert!(
        ind.is_large_elim,
        "MyAnd is a single-ctor all-Prop-field inductive: it MUST permit large elimination"
    );
    assert!(
        env.get_recursor(&Name::from_string("MyAnd.casesOn"))
            .is_none(),
        "imported MyAnd.casesOn must NOT be a registered recursor"
    );
    let cases = env
        .get_const(&Name::from_string("MyAnd.casesOn"))
        .expect("MyAnd.casesOn const exists");
    assert!(
        cases.value.is_some(),
        "imported MyAnd.casesOn must be a definitional constant with a value"
    );
    assert_eq!(
        cases.level_params.len(),
        1,
        "imported large-elim MyAnd.casesOn must carry exactly one motive universe param; got {:?}",
        cases.level_params
    );
}

// ===========================================================================
// MAIN PROBE (a): project a component out of an imported `MyAnd` via a `match`,
// eliminating into a PROOF (Prop motive). The left/right projections take an
// imported large-elim `MyAnd` apart. Distinct atomic props P, Q make a swapped
// projection observable.
// ===========================================================================

#[test]
fn test_match_projection_on_imported_and_into_prop() {
    let mut env = imported_myand_env();

    // andLeft / andRight : the two projections of an imported MyAnd, into Prop.
    elaborate_decls_into(
        &mut env,
        "def andLeft (a b : Prop) (h : MyAnd a b) : a := match h with\n  \
         | MyAnd.intro l r => l\n\
         def andRight (a b : Prop) (h : MyAnd a b) : b := match h with\n  \
         | MyAnd.intro l r => r\n\
         def andSwap (a b : Prop) (h : MyAnd a b) : MyAnd b a := match h with\n  \
         | MyAnd.intro l r => MyAnd.intro b a r l",
    );

    for name in ["andLeft", "andRight", "andSwap"] {
        let body = env
            .get_const(&Name::from_string(name))
            .and_then(|i| i.value.clone())
            .unwrap_or_else(|| panic!("{name} should be a registered definition"));
        assert!(
            body.collect_constants()
                .contains(&Name::from_string("MyAnd.casesOn")),
            "{name} must compile through the imported MyAnd.casesOn, got: {:?}",
            body.collect_constants()
        );
    }

    // Concrete props + a witness so the projections reduce to observable heads.
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def pq : MyAnd P Q := MyAnd.intro P Q hp hq",
    );

    // andLeft P Q pq ⇝ hp ⇝ P.mk; andRight P Q pq ⇝ hq ⇝ Q.mk (distinct heads).
    let left = Expr::app(
        Expr::app(Expr::app(const_("andLeft"), const_("P")), const_("Q")),
        const_("pq"),
    );
    assert_eq!(
        whnf_head_const(&env, &left).as_deref(),
        Some("P.mk"),
        "andLeft must project the FIRST field (hp ⇝ P.mk)"
    );
    let right = Expr::app(
        Expr::app(Expr::app(const_("andRight"), const_("P")), const_("Q")),
        const_("pq"),
    );
    assert_eq!(
        whnf_head_const(&env, &right).as_deref(),
        Some("Q.mk"),
        "andRight must project the SECOND field (hq ⇝ Q.mk)"
    );
    assert_ne!(
        whnf_head_const(&env, &left),
        whnf_head_const(&env, &right),
        "the two projections must select DISTINCT fields (P.mk vs Q.mk) — a swapped \
         field binding would surface here"
    );

    // andSwap reduces to the intro with the fields swapped; reduction head is the
    // constructor MyAnd.intro (proof-irrelevant body, but the head is observable).
    let swap = Expr::app(
        Expr::app(Expr::app(const_("andSwap"), const_("P")), const_("Q")),
        const_("pq"),
    );
    assert_eq!(
        whnf_head_const(&env, &swap).as_deref(),
        Some("MyAnd.intro"),
        "andSwap must reduce to a MyAnd.intro"
    );
}

// ===========================================================================
// MAIN PROBE (b): LARGE ELIMINATION of an imported subsingleton Prop inductive
// into `Type`. `MyAnd` is large-elim eligible, so a match eliminating it into a
// `Type`-valued motive (returning a Nat) is LEGAL and must elaborate. The
// imported large-elim `MyAnd.casesOn.{u}` carries a motive universe; the
// elaborator must instantiate it with the *type* universe of the result (here
// `Sort 1`, the universe of `Nat`), not collapse it to `Prop`.
// ===========================================================================

#[test]
fn test_large_elimination_of_imported_and_into_type() {
    let mut env = imported_myand_env();

    // andToNat : MyAnd a b -> Nat, eliminating an imported Prop subsingleton into
    // the Type-valued result `Nat`. This is the large-elimination capability:
    // returning a non-Prop value from a Prop scrutinee. A two-ctor Prop inductive
    // could NOT do this; `MyAnd` (single ctor, all-Prop fields) can.
    elaborate_decls_into(
        &mut env,
        "def andToNat (a b : Prop) (h : MyAnd a b) : Nat := match h with\n  \
         | MyAnd.intro l r => Nat.succ Nat.zero",
    );

    let body = env
        .get_const(&Name::from_string("andToNat"))
        .and_then(|i| i.value.clone())
        .expect("andToNat should be a registered definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("MyAnd.casesOn")),
        "andToNat must compile through the imported MyAnd.casesOn, got: {:?}",
        body.collect_constants()
    );

    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def pq : MyAnd P Q := MyAnd.intro P Q hp hq",
    );

    // andToNat P Q pq ⇝ Nat.succ Nat.zero = 1 (a genuine Type-level value pulled
    // out of a Prop scrutinee — the large-elimination result).
    let call = Expr::app(
        Expr::app(Expr::app(const_("andToNat"), const_("P")), const_("Q")),
        const_("pq"),
    );
    let one = Expr::app(const_("Nat.succ"), const_("Nat.zero"));
    assert!(
        def_eq(&env, &call, &one),
        "andToNat P Q pq must large-eliminate to 1 (Nat.succ Nat.zero); got head {:?}",
        whnf_head_const(&env, &call)
    );
    assert!(
        !def_eq(&env, &call, &const_("Nat.zero")),
        "the large-elim result must be 1, not 0 — a collapsed motive would surface here"
    );
}

// ===========================================================================
// Control: the imported Prop-only `MyOr.casesOn` reduces correctly when applied
// BY HAND with a Prop motive, isolating any match-test failure to the
// elaborator's lowering rather than the kernel's reduction of the imported
// definitional casesOn.
// ===========================================================================

#[test]
fn test_imported_or_cases_on_kernel_reduction_is_correct() {
    let mut env = imported_myor_env();
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk",
    );

    // motive := fun (_ : MyOr P Q) => MyOr Q P  (constant Prop motive)
    let motive = Expr::lam(
        BinderInfo::Default,
        myor_at(const_("P"), const_("Q")),
        myor_at(const_("Q"), const_("P")),
    );
    // m_inl := fun (h : P) => MyOr.inr Q P h
    let m_inl = Expr::lam(
        BinderInfo::Default,
        const_("P"),
        myor_ctor("MyOr.inr", const_("Q"), const_("P"), Expr::bvar(0)),
    );
    // m_inr := fun (h : Q) => MyOr.inl Q P h
    let m_inr = Expr::lam(
        BinderInfo::Default,
        const_("Q"),
        myor_ctor("MyOr.inl", const_("Q"), const_("P"), Expr::bvar(0)),
    );

    // cases := @MyOr.casesOn P Q motive major m_inl m_inr  (MajorAfterMotive, 0 levels)
    let mk_cases = |major: Expr| {
        let c = Expr::const_(Name::from_string("MyOr.casesOn"), vec![]);
        let c = Expr::app(c, const_("P")); // a
        let c = Expr::app(c, const_("Q")); // b
        let c = Expr::app(c, motive.clone()); // motive
        let c = Expr::app(c, major); // major (MajorAfterMotive)
        let c = Expr::app(c, m_inl.clone()); // m_inl
        Expr::app(c, m_inr.clone()) // m_inr
    };

    let inl_major = myor_ctor("MyOr.inl", const_("P"), const_("Q"), const_("hp"));
    assert_eq!(
        whnf_head_const(&env, &mk_cases(inl_major)).as_deref(),
        Some("MyOr.inr"),
        "imported MyOr.casesOn on an inl value must select the inl minor (MyOr.inr)"
    );
    let inr_major = myor_ctor("MyOr.inr", const_("P"), const_("Q"), const_("hq"));
    assert_eq!(
        whnf_head_const(&env, &mk_cases(inr_major)).as_deref(),
        Some("MyOr.inl"),
        "imported MyOr.casesOn on an inr value must select the inr minor (MyOr.inl)"
    );
}

// ===========================================================================
// Control (generality): the SAME Prop-into-Prop `MyOr` match works on the NATIVE
// path (where MyOr.casesOn IS a registered recursor with EMPTY level params).
// The eliminator-levels fix is general — not import-specific — so this passing
// alongside the imported test confirms native behavior is correct, not merely
// preserved.
// ===========================================================================

#[test]
fn test_match_on_native_prop_only_or_unchanged() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(myor_decl()).expect("MyOr declares");

    let rec = env
        .get_recursor(&Name::from_string("MyOr.casesOn"))
        .expect("native MyOr.casesOn should be a registered recursor");
    assert!(
        rec.level_params.is_empty(),
        "native Prop-only MyOr.casesOn recursor must have EMPTY level params"
    );

    elaborate_decls_into(
        &mut env,
        "def orCommN (a b : Prop) (h : MyOr a b) : MyOr b a := match h with\n  \
         | MyOr.inl ha => MyOr.inr b a ha\n  \
         | MyOr.inr hb => MyOr.inl b a hb",
    );
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def orPQ : MyOr P Q := MyOr.inl P Q hp\n\
         def orQP : MyOr P Q := MyOr.inr P Q hq",
    );

    let call_inl = Expr::app(
        Expr::app(Expr::app(const_("orCommN"), const_("P")), const_("Q")),
        const_("orPQ"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inl).as_deref(),
        Some("MyOr.inr"),
        "native orCommN on inl must reduce to the inr branch"
    );
    let call_inr = Expr::app(
        Expr::app(Expr::app(const_("orCommN"), const_("P")), const_("Q")),
        const_("orQP"),
    );
    assert_eq!(
        whnf_head_const(&env, &call_inr).as_deref(),
        Some("MyOr.inl"),
        "native orCommN on inr must reduce to the inl branch"
    );
}

// ===========================================================================
// Control (generality): the SAME large-elim `MyAnd` match works on the NATIVE
// path (where MyAnd.casesOn IS a registered recursor carrying a motive
// universe). Confirms the eliminator-levels fix preserves native large-elim.
// ===========================================================================

#[test]
fn test_large_elimination_of_native_and_into_type_unchanged() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.add_inductive(myand_decl()).expect("MyAnd declares");

    let rec = env
        .get_recursor(&Name::from_string("MyAnd.casesOn"))
        .expect("native MyAnd.casesOn should be a registered recursor");
    assert_eq!(
        rec.level_params.len(),
        1,
        "native large-elim MyAnd.casesOn recursor must carry one motive universe param"
    );

    elaborate_decls_into(
        &mut env,
        "def andToNatN (a b : Prop) (h : MyAnd a b) : Nat := match h with\n  \
         | MyAnd.intro l r => Nat.succ Nat.zero",
    );
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def pq : MyAnd P Q := MyAnd.intro P Q hp hq",
    );

    let call = Expr::app(
        Expr::app(Expr::app(const_("andToNatN"), const_("P")), const_("Q")),
        const_("pq"),
    );
    let one = Expr::app(const_("Nat.succ"), const_("Nat.zero"));
    assert!(
        def_eq(&env, &call, &one),
        "native andToNatN P Q pq must large-eliminate to 1; got head {:?}",
        whnf_head_const(&env, &call)
    );
}

// ===========================================================================
// Control: the imported large-elim `MyAnd.casesOn` reduces correctly when
// applied BY HAND with a Type motive (`fun _ => Nat`), independently pinning
// the synthesized fixture's faithfulness (its minor binds the two distinct
// fields `l : a`, `r : b` in the right slots). Isolates any match-test failure
// to the elaborator's lowering rather than the synthesized definitional casesOn.
// ===========================================================================

#[test]
fn test_imported_and_cases_on_kernel_reduction_is_correct() {
    let mut env = imported_myand_env();
    elaborate_decls_into(
        &mut env,
        "inductive P : Prop | mk\n\
         inductive Q : Prop | mk\n\
         def hp : P := P.mk\n\
         def hq : Q := Q.mk\n\
         def pq : MyAnd P Q := MyAnd.intro P Q hp hq",
    );

    // motive := fun (_ : MyAnd P Q) => Nat  (large-elim: Type-valued motive)
    let motive = Expr::lam(
        BinderInfo::Default,
        myand_at(const_("P"), const_("Q")),
        const_("Nat"),
    );
    // m_intro := fun (l : P) (r : Q) => Nat.succ Nat.zero  (constant 1)
    let one = Expr::app(const_("Nat.succ"), const_("Nat.zero"));
    let m_intro = Expr::lam(
        BinderInfo::Default,
        const_("P"),
        Expr::lam(BinderInfo::Default, const_("Q"), one.clone()),
    );

    // @MyAnd.casesOn.{1} P Q motive pq m_intro  (MajorAfterMotive, motive univ = 1)
    let c = Expr::const_(
        Name::from_string("MyAnd.casesOn"),
        vec![Level::succ(Level::zero())],
    );
    let c = Expr::app(c, const_("P")); // a
    let c = Expr::app(c, const_("Q")); // b
    let c = Expr::app(c, motive); // motive
    let c = Expr::app(c, const_("pq")); // major (MajorAfterMotive)
    let app = Expr::app(c, m_intro); // m_intro

    assert!(
        def_eq(&env, &app, &one),
        "imported MyAnd.casesOn must reduce the intro minor to 1 (Nat.succ Nat.zero); got head {:?}",
        whnf_head_const(&env, &app)
    );
}

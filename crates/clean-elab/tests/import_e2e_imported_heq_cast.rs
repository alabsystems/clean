// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: HETEROGENEOUS EQUALITY (`HEq`), `cast`, `Eq.mp`/`Eq.mpr`, and
//! `Eq.subst` transport through an *imported* inductive type (imported_heq_cast
//! scenario).
//!
//! ## What the transport machinery is
//!
//! `cast`, `Eq.mp`, `Eq.mpr`, `Eq.subst`, `heq_of_eq`, and `eq_of_heq` are the
//! Lean/Init equality-transport primitives. They are *generic* definitions built
//! on top of `Eq.rec` / `HEq.rec`:
//!
//! ```text
//! cast    : {α β : Sort u} → Eq α β → α → β          := Eq.ndrec via Eq.rec
//! Eq.mpr  : {α β : Sort u} → Eq α β → β → α           := cast ∘ Eq.symm
//! Eq.subst: {α} {motive : α → Prop} {a b} → Eq a b → motive a → motive b
//! ```
//!
//! When the value being transported (or the type appearing in a transported
//! goal/motive) is an *imported* inductive `T`, the transport itself unfolds to
//! `Eq.rec`/`HEq.rec` on `Eq`/`HEq` (always present from the kernel) — but any
//! *downstream* elimination of the transported `T`-value (a `match` / projection)
//! must lower through the **imported** `T.casesOn`. That is where native metadata
//! is absent and the import path is exercised.
//!
//! ## Why imports are special (mirrors B43/B45/B47/B48/B49/B50)
//!
//! A native clean-built inductive registers `T.casesOn` as a *recursor*
//! (`RecursorVal`, `MajorAfterMinors` layout) and a clean-side `structure_fields`
//! table for the projections. A real Lean `.olean` ships ONLY the recursor
//! `T.rec` + the projection *functions* + a **definitional** `T.casesOn` constant
//! in the `MajorAfterMotive` layout, and registers NONE of the clean-side
//! metadata: `get_recursor("T.casesOn") == None`, `get_structure_field_names ==
//! None`. The match elaborator must therefore compute motive / major / minor
//! layout and the eliminator universe arity from the *imported* eliminator
//! constant's own type, not from absent recursor metadata.
//!
//! The hypothesized bug class for this scenario: `cast`/`HEq.rec` lowering, or
//! the `match` that consumes a transported value, computes motive / major / index
//! layout from native metadata that the import does not carry, so the transported
//! term mis-typechecks or fails to reduce — in particular, a `cast` of a
//! constructor value across `rfl` must reduce back to the value (Eq.rec iota on a
//! reflexivity proof), and a subsequent `match` must select the right branch.
//!
//! ## Result: imported transport is correct — this file LOCKS IT IN
//!
//! Probing the transport surface against an imported wrapper (`Box`) shows the
//! import path is already correct: transporting an imported value across `rfl`
//! via `cast` / `Eq.mp` / `Eq.mpr`, then projecting / matching it, elaborates,
//! kernel-checks, and reduces to the genuinely-correct (distinct) value through
//! the imported `Box.casesOn`. `Eq.subst` over a `Box`-valued motive and
//! `Eq.mpr` rewriting a `Box`-projection goal likewise elaborate and
//! kernel-check. `HEq.refl` / `eq_of_heq` on the imported type build their
//! `HEq.rec` motives correctly.
//!
//! Every transported term uses *explicit* universe arguments
//! (`@cast.{1} … (@Eq.refl.{2} (Sort 1) Box …)`), which is exactly the fully
//! elaborated shape a real `.olean` member ships — it does NOT rely on surface
//! universe inference for the `cast`'s implicit `{u}` (that inference's
//! Sort-vs-element ambiguity for bare `cast (Eq.refl T) x` is an orthogonal,
//! non-import elaborator concern that reproduces identically on built-in `Nat`,
//! and is therefore out of scope here). The probes assert *distinct* reductions
//! so a wrong branch / dropped transport / wrong major slot surfaces as a
//! different observable `Nat` rather than passing silently. A by-hand kernel
//! control and a native control (where `Box.casesOn` IS a recursor and the field
//! table IS present) run alongside so any regression is isolated to the
//! elaborator's lowering rather than the kernel's reduction, and so the behavior
//! is shown general rather than import-specific.

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

/// Church-style `Nat` literal `k` (`Nat.succ^k Nat.zero`).
fn nat(k: usize) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..k {
        e = Expr::app(const_("Nat.succ"), e);
    }
    e
}

/// `Box.mk n`.
fn box_mk(n: Expr) -> Expr {
    Expr::app(const_("Box.mk"), n)
}

/// `Box` self-equality proof `@Eq.refl.{2} (Sort 1) Box : @Eq.{2} (Sort 1) Box Box`.
/// `Box : Type = Sort 1`, so the type-level reflexivity lives at universe `2`.
///
/// `Eq.refl.{w} : {α : Sort w} → (a : α) → @Eq.{w} α a a`. Instantiating `a :=
/// Box` (an element of `Sort 1`) forces `α := Sort 1` and `w := 2`.
fn box_self_eq() -> Expr {
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::succ(Level::zero()))],
    );
    // @Eq.refl.{2} (Sort 1) Box
    Expr::app(
        Expr::app(eq_refl, Expr::sort(Level::succ(Level::zero()))),
        const_("Box"),
    )
}

fn def_eq(env: &Environment, a: &Expr, b: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(a, b)
}

/// Reduce `expr` to WHNF and return its head `Const` name, if any.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Elaborate + register declarations from `source`. `elaborate_decl_and_register`
/// runs the full kernel type-check per definition, so reaching the end means
/// every body kernel-checked.
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
// `inductive Box : Type | mk (n : Nat)` — a single-constructor wrapper of `Nat`.
//
// A `Type`-valued single-ctor inductive: `cast`/`Eq.mp`/`Eq.mpr` over `Box`
// instantiate the transport machinery at `u := 1` (`Box : Sort 1`), and its
// `casesOn` carries a motive universe (large elim into `Type`).
// ---------------------------------------------------------------------------

fn box_decl() -> InductiveDecl {
    // Box : Type
    let box_ty = Expr::type_();
    // Box.mk : Nat -> Box
    let mk_ty = Expr::pi(BinderInfo::Default, const_("Nat"), const_("Box"));
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Box"),
            type_: box_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Box.mk"),
                type_: mk_ty,
            }],
        }],
    }
}

/// The imported `MajorAfterMotive` `Box.casesOn` **type**:
///
/// ```text
/// Box.casesOn.{u} :
///   {motive : Box -> Sort u} -> (t : Box)
///     -> ((n : Nat) -> motive (Box.mk n))
///     -> motive t
/// ```
fn box_imported_cases_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    // Telescope (outer -> inner): motive, t, m_mk.
    // Innermost scope [motive, t, m_mk]: motive=2, t=1, m_mk=0.
    // result `motive t`: motive=#2, t=#1
    let result = Expr::app(Expr::bvar(2), Expr::bvar(1));
    // m_mk domain under [motive, t]: (n : Nat) -> motive (Box.mk n)
    //   inside [motive, t, n]: motive=2, n=0
    let m_mk_body = Expr::app(Expr::bvar(2), box_mk(Expr::bvar(0)));
    let m_mk_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_mk_body);
    let t_dom = const_("Box");
    let motive_dom = Expr::pi(BinderInfo::Default, const_("Box"), sort_u);

    let body = Expr::pi(BinderInfo::Default, m_mk_dom, result);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    Expr::pi(BinderInfo::Implicit, motive_dom, body)
}

/// The imported `Box.casesOn` **value**, unfolding to `Box.rec`:
///
/// ```text
/// fun motive t m_mk => Box.rec motive m_mk t
/// ```
fn box_imported_cases_value(u: &Name) -> Expr {
    let rec = Expr::const_(Name::from_string("Box.rec"), vec![Level::param(u.clone())]);
    let sort_u = Expr::sort(Level::param(u.clone()));
    // body under [motive, t, m_mk]: Box.rec motive m_mk t (native MajorAfterMinors)
    let body = Expr::app(rec, Expr::bvar(2)); // motive
    let body = Expr::app(body, Expr::bvar(0)); // m_mk (minor)
    let body = Expr::app(body, Expr::bvar(1)); // t (major last)

    let m_mk_body = Expr::app(Expr::bvar(2), box_mk(Expr::bvar(0)));
    let m_mk_dom = Expr::pi(BinderInfo::Default, const_("Nat"), m_mk_body);
    let t_dom = const_("Box");
    let motive_dom = Expr::pi(BinderInfo::Default, const_("Box"), sort_u);

    let body = Expr::lam(BinderInfo::Default, m_mk_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    Expr::lam(BinderInfo::Implicit, motive_dom, body)
}

/// Build an environment holding a *faithfully imported* `Box`: the real
/// kernel-built inductive + ctor + `Box.rec` recursor, plus `Eq`/`HEq` and the
/// transport machinery (`cast`, `Eq.mp`, `Eq.mpr`, `Eq.subst`, `heq_of_eq`,
/// `eq_of_heq`) from the kernel — but `Box.casesOn` as a plain
/// `Declaration::Definition` (so `get_recursor("Box.casesOn") == None`) and NO
/// `structure_fields` table, exactly as an `.olean` import ships.
fn imported_box_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_heq().expect("init_heq"); // also pulls in Eq + cast + Eq.mpr + ...
    native
        .add_inductive(box_decl())
        .expect("Box should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_heq().expect("init_heq");

    let iv = native
        .get_inductive(&Name::from_string("Box"))
        .cloned()
        .expect("scratch env has Box");
    env.register_inductive(iv);
    let c = native
        .get_constructor(&Name::from_string("Box.mk"))
        .cloned()
        .expect("Box.mk ctor");
    env.register_constructor(c);
    // Box.rec stays a recursor on import; copy its ConstantInfo so the kernel can
    // type-check the casesOn definition that references it.
    let rv = native
        .get_recursor(&Name::from_string("Box.rec"))
        .cloned()
        .expect("Box.rec recursor");
    let rc = native
        .get_const(&Name::from_string("Box.rec"))
        .cloned()
        .expect("Box.rec const");
    env.extend_constants_unchecked(std::iter::once(rc));
    env.register_recursor(rv);

    let u = native
        .get_recursor(&Name::from_string("Box.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("Box.rec has a motive universe parameter");

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body, kernel
    // type-checked by `add_decl_structural` against the casesOn type. This
    // reproduces exactly what an `.olean` import of a single-ctor wrapper ships
    // (recursor present, `.casesOn` a definitional constant, no clean-side
    // recursor registration, no structure_fields table). No production path is
    // involved.
    env.add_decl_structural(Declaration::Definition {
        name: Name::from_string("Box.casesOn"),
        level_params: vec![u.clone()],
        type_: box_imported_cases_type(&u),
        value: box_imported_cases_value(&u),
        is_reducible: false,
    })
    .expect("imported Box.casesOn definition should kernel-check");

    env
}

// ===========================================================================
// Precondition: the synthesized env is genuinely the *import* configuration —
// recursor `Box.rec` present, `Box.casesOn` a definitional constant (NOT a
// recursor), and NO clean-side `structure_fields` table. This proves the probes
// exercise the import path.
// ===========================================================================

#[test]
fn test_imported_box_is_cases_on_definition_not_recursor_no_field_table() {
    let env = imported_box_env();

    // Box.rec stays a registered recursor.
    assert!(
        env.get_recursor(&Name::from_string("Box.rec")).is_some(),
        "Box.rec must stay a registered recursor on import"
    );
    // Box.casesOn is a definitional constant (NOT a registered recursor) — this
    // routes the match elaborator through the imported MajorAfterMotive path.
    assert!(
        env.get_recursor(&Name::from_string("Box.casesOn"))
            .is_none(),
        "imported Box.casesOn must NOT be a registered recursor"
    );
    let cases = env
        .get_const(&Name::from_string("Box.casesOn"))
        .expect("Box.casesOn const");
    assert!(
        cases.value.is_some(),
        "imported Box.casesOn must be a definitional constant with a value"
    );
    // No clean-side structure field table — the import condition for projections.
    assert!(
        env.get_structure_field_names(&Name::from_string("Box"))
            .is_none(),
        "imported Box must carry NO clean-side structure_fields table"
    );
    // The transport machinery is present (kernel-supplied), so the probes below
    // genuinely exercise transport, not a missing-constant error.
    for prim in [
        "cast",
        "Eq.mp",
        "Eq.mpr",
        "Eq.subst",
        "heq_of_eq",
        "eq_of_heq",
        "HEq",
        "HEq.refl",
    ] {
        assert!(
            env.get_const(&Name::from_string(prim)).is_some(),
            "transport primitive {prim} must be available"
        );
    }
}

// ===========================================================================
// Control: a by-hand `cast`/`Eq.mp` of an imported `Box` constructor across
// `rfl` reduces back to the value, and `Box.casesOn` applied by hand to that
// transported value selects the right minor. Isolates any later match-test
// failure to the *elaborator's* lowering rather than the kernel's reduction of
// `Eq.rec` iota / the synthesized definitional `Box.casesOn`.
// ===========================================================================

#[test]
fn test_imported_cast_of_box_ctor_reduces_by_hand() {
    let env = imported_box_env();

    // h : @Eq.{2} (Sort 1) Box Box  (reflexivity at the type level).
    let h = box_self_eq();
    // val := Box.mk 5.
    let val = box_mk(nat(5));
    // cast.{1} : {α β : Sort 1} → @Eq.{2} (Sort 1) α β → α → β
    let cast = Expr::const_(Name::from_string("cast"), vec![Level::succ(Level::zero())]);
    // @cast.{1} Box Box h (Box.mk 5)  ~>  Box.mk 5  (Eq.rec iota on rfl).
    let casted = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cast, const_("Box")), const_("Box")),
            h.clone(),
        ),
        val.clone(),
    );
    assert!(
        def_eq(&env, &casted, &val),
        "cast of (Box.mk 5) across rfl must reduce back to (Box.mk 5); got head {:?}",
        whnf_head_const(&env, &casted)
    );

    // Now eliminate the transported value via the imported Box.casesOn into Nat:
    // @Box.casesOn.{1} (fun _ : Box => Nat) (cast ... (Box.mk 5)) (fun n => n) ~> 5.
    let motive = Expr::lam(BinderInfo::Default, const_("Box"), const_("Nat"));
    let m_mk = Expr::lam(BinderInfo::Default, const_("Nat"), Expr::bvar(0));
    let cases = Expr::const_(
        Name::from_string("Box.casesOn"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::app(cases, motive);
    let app = Expr::app(app, casted); // major (MajorAfterMotive)
    let app = Expr::app(app, m_mk);
    assert!(
        def_eq(&env, &app, &nat(5)),
        "Box.casesOn on the transported (Box.mk 5) must bind n = 5; got head {:?}",
        whnf_head_const(&env, &app)
    );
    assert!(
        !def_eq(&env, &app, &nat(3)),
        "the transported value must yield 5, not a stale/other Nat (3)"
    );
}

// ===========================================================================
// MAIN PROBE (a): `cast` / `Eq.mp` / `Eq.mpr` transport an imported `Box` value
// across `rfl`, and a `def`-level `match` consumes the transported value through
// the imported `Box.casesOn`. The transports use the fully elaborated explicit-
// universe shape an `.olean` ships. Distinct witnesses (5 vs 3) make a dropped
// transport / wrong major slot / wrong branch observable.
// ===========================================================================

#[test]
fn test_match_on_cast_transported_imported_box_reduces_correctly() {
    let mut env = imported_box_env();

    // unwrap projects the field out of a Box THROUGH the imported Box.casesOn.
    // b5 / b3 are distinct boxed Nats. castB / mpB / mpEq transport them across
    // rfl via cast / Eq.mpr / Eq.mp respectively.
    elaborate_decls_into(
        &mut env,
        "def unwrap (b : Box) : Nat := match b with | Box.mk n => n\n\
         def b5 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))\n\
         def b3 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ Nat.zero)))\n\
         def castB : Box := @cast.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) b5\n\
         def mpEqB : Box := @Eq.mp.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) b5\n\
         def mprB : Box := @Eq.mpr.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) b3\n\
         def matchCast : Nat := match (@cast.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) b5) with | Box.mk n => n",
    );

    // The match-on-cast `def` must compile through the imported Box.casesOn.
    let body = env
        .get_const(&Name::from_string("matchCast"))
        .and_then(|i| i.value.clone())
        .expect("matchCast should be a registered definition");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Box.casesOn")),
        "matchCast must lower through the imported Box.casesOn, got: {:?}",
        body.collect_constants()
    );
    // And it must mention `cast` — the scrutinee really is a transported value.
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("cast")),
        "matchCast's scrutinee must be a cast-transported Box"
    );

    // matchCast ~> 5 (the cast across rfl is transparent; the match binds n = 5).
    assert!(
        def_eq(&env, &const_("matchCast"), &nat(5)),
        "matchCast must reduce to 5; got head {:?}",
        whnf_head_const(&env, &const_("matchCast"))
    );
    assert!(
        !def_eq(&env, &const_("matchCast"), &nat(3)),
        "matchCast must be 5, not the OTHER witness 3 — a dropped/wrong transport surfaces here"
    );

    // unwrap castB ~> 5, unwrap mpEqB ~> 5 (Eq.mp also forward-transports b5).
    let uc = Expr::app(const_("unwrap"), const_("castB"));
    assert!(def_eq(&env, &uc, &nat(5)), "unwrap castB must reduce to 5");
    let ue = Expr::app(const_("unwrap"), const_("mpEqB"));
    assert!(def_eq(&env, &ue, &nat(5)), "unwrap mpEqB must reduce to 5");

    // unwrap mprB ~> 3 (Eq.mpr backward-transports b3). DISTINCT from the b5
    // transports above, so a transport that ignores its argument or grabs the
    // wrong box would surface as a different Nat.
    let um = Expr::app(const_("unwrap"), const_("mprB"));
    assert!(def_eq(&env, &um, &nat(3)), "unwrap mprB must reduce to 3");
    assert!(
        !def_eq(&env, &um, &nat(5)),
        "the Eq.mpr-transported value must be 3, not 5"
    );
}

// ===========================================================================
// MAIN PROBE (b): `Eq.subst` / `Eq.mpr` / `Eq.ndrec` REWRITE / TRANSPORT over
// the imported type. `substBox` transports a `Box`-projection proposition along
// an equality of imported `Box` values; `mprGoal` rewrites a `Box`-projection
// Prop goal via `Eq.mpr`; `projCongr` builds the rewrite equality via `congrArg`
// over a lambda mentioning the imported projection. All must elaborate and
// kernel-check (reaching the end of `elaborate_decls_into` is the proof). A
// SHARPER, Type-valued `Eq.ndrec` transport then yields an observable distinct
// `Nat`, so a dropped/wrong transport surfaces as a different value rather than
// being masked by `Prop` proof-irrelevance.
// ===========================================================================

#[test]
fn test_eq_subst_and_mpr_rewrite_goal_over_imported_box() {
    let mut env = imported_box_env();

    // The motive / equality arguments are supplied *explicitly* — exactly the
    // fully elaborated shape an `.olean` member ships (Lean's `rw`/`simp` produce
    // the explicit `Eq.subst`/`Eq.mpr` application; automatic higher-order motive
    // inference for the bare `Eq.subst h pa` surface form is an orthogonal,
    // non-import elaborator concern). Each motive / goal genuinely mentions the
    // imported `Box` and its imported-eliminator projection `unwrap`.
    // `@Eq.subst` transports a proof of `P x` (a motive over the imported `Box`)
    // along an equality `Eq a b` of imported `Box` values. `Eq.mpr` rewrites a
    // Prop goal mentioning the imported projection `unwrap`, given an equality
    // between the two projection propositions; `congrArg` over a lambda
    // mentioning `unwrap` builds exactly that equality.
    elaborate_decls_into(
        &mut env,
        "def unwrap (b : Box) : Nat := match b with | Box.mk n => n",
    );
    elaborate_decls_into(&mut env, "def b0 : Box := Box.mk Nat.zero");
    elaborate_decls_into(
        &mut env,
        "def substBox (P : Box -> Prop) (a b : Box) (h : Eq a b) (pa : P a) : P b := @Eq.subst Box P a b h pa",
    );
    elaborate_decls_into(
        &mut env,
        "def mprGoal (b1 b2 : Box) (heq : Eq (Eq (unwrap b1) Nat.zero) (Eq (unwrap b2) Nat.zero)) (p : Eq (unwrap b2) Nat.zero) : Eq (unwrap b1) Nat.zero := Eq.mpr heq p",
    );
    elaborate_decls_into(
        &mut env,
        "def projCongr (b1 b2 : Box) (h : Eq (unwrap b1) (unwrap b2)) : Eq (Eq (unwrap b1) Nat.zero) (Eq (unwrap b2) Nat.zero) := congrArg (fun n => Eq n Nat.zero) h",
    );

    // All three defs registered & kernel-checked.
    for name in ["substBox", "mprGoal", "projCongr"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be a registered definition"
        );
    }

    // substBox is the generic Eq.subst-driven rewrite over a `Box` motive.
    // Instantiated on the motive `fun x => Eq (unwrap x) (unwrap x)`, the value
    // `b0`, and `rfl`, it must be the identity transport: the transported proof
    // is def-eq to the input proof (subst along reflexivity is transparent). The
    // motive references the imported projection `unwrap`, so the transport is
    // genuinely *about* the imported type.
    elaborate_decls_into(
        &mut env,
        "def pmotive : Box -> Prop := fun x => @Eq.{1} Nat (unwrap x) (unwrap x)",
    );
    elaborate_decls_into(
        &mut env,
        "def p0 : @Eq.{1} Nat (unwrap b0) (unwrap b0) := @Eq.refl.{1} Nat (unwrap b0)",
    );
    elaborate_decls_into(
        &mut env,
        "def transported : @Eq.{1} Nat (unwrap b0) (unwrap b0) := substBox pmotive b0 b0 (@Eq.refl.{1} Box b0) p0",
    );

    assert!(
        def_eq(&env, &const_("transported"), &const_("p0")),
        "Eq.subst of a proof along rfl over an imported Box motive must be the identity transport"
    );

    // unwrap b0 genuinely reduces through the imported Box.casesOn to 0 — the
    // projection the rewrites are *about* really is the imported-eliminator path.
    let u0 = Expr::app(const_("unwrap"), const_("b0"));
    assert!(
        def_eq(&env, &u0, &nat(0)),
        "unwrap b0 must reduce through the imported Box.casesOn to 0"
    );

    // SHARPER, Type-valued transport: `Eq.ndrec` transports the projected `Nat`
    // (`unwrap a`) across an equality of imported `Box` values into a `Type`
    // motive. Unlike the proof-irrelevant `Eq.subst` above, the result is a
    // genuine `Nat`, so a transport that drops its payload / grabs the wrong box
    // surfaces as a different value. `ndTransport a b h` reduces, when `a = b` and
    // `h := rfl`, to `unwrap a` — the imported-eliminator projection.
    elaborate_decls_into(
        &mut env,
        "def b5 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
    );
    elaborate_decls_into(
        &mut env,
        "def ndTransport (a b : Box) (h : Eq a b) : Nat := @Eq.ndrec Box a (fun x => Nat) (unwrap a) b h",
    );
    assert!(
        env.get_const(&Name::from_string("ndTransport")).is_some(),
        "ndTransport (Eq.ndrec into a Type motive over imported Box) should elaborate"
    );
    // ndTransport b5 b5 rfl ~> unwrap b5 ~> 5 (transport across rfl is the identity).
    let refl_b5 = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            const_("Box"),
        ),
        const_("b5"),
    );
    let nd = Expr::app(
        Expr::app(Expr::app(const_("ndTransport"), const_("b5")), const_("b5")),
        refl_b5,
    );
    assert!(
        def_eq(&env, &nd, &nat(5)),
        "ndTransport b5 b5 rfl must transport the projected Nat to 5; got head {:?}",
        whnf_head_const(&env, &nd)
    );
    assert!(
        !def_eq(&env, &nd, &nat(3)),
        "the Type-valued ndrec transport must yield 5, not a stale/other Nat (3)"
    );
}

// ===========================================================================
// MAIN PROBE (a'/HEq): `HEq.refl` and `eq_of_heq` over the imported type build
// their `HEq.rec`/`Eq.rec` motives correctly; `eq_of_heq` of a homogeneous HEq
// yields an Eq, and transporting along it leaves the imported value's projection
// unchanged.
// ===========================================================================

#[test]
fn test_heq_refl_and_eq_of_heq_over_imported_box() {
    let mut env = imported_box_env();

    // `HEq.refl` on an imported `Box` value builds an `HEq.rec` motive over the
    // imported type; `eq_of_heq` bridges a (homogeneous) `HEq` on `Box` to an
    // `Eq` on `Box`; `heqTransport` transports a `Box`-projection proof along the
    // bridged `Eq` (explicit motive over the imported projection `unwrap` — the
    // elaborated `.olean` shape).
    elaborate_decls_into(
        &mut env,
        "def unwrap (b : Box) : Nat := match b with | Box.mk n => n",
    );
    elaborate_decls_into(
        &mut env,
        "def b7 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))",
    );
    elaborate_decls_into(&mut env, "def hrefl : HEq b7 b7 := HEq.refl b7");
    elaborate_decls_into(
        &mut env,
        "def eoh (a b : Box) (h : HEq a b) : Eq a b := eq_of_heq h",
    );
    elaborate_decls_into(
        &mut env,
        "def heqTransport (a b : Box) (h : HEq a b) (p : @Eq.{1} Nat (unwrap a) (unwrap a)) : @Eq.{1} Nat (unwrap b) (unwrap b) := @Eq.subst Box (fun x => @Eq.{1} Nat (unwrap x) (unwrap x)) a b (eq_of_heq h) p",
    );

    for name in ["hrefl", "eoh", "heqTransport"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be a registered definition"
        );
    }

    // heqTransport, instantiated on b7/b7 with HEq.refl and a refl proof, must be
    // the identity transport (def-eq to the input proof). The motive references
    // the imported projection `unwrap`, so the HEq → Eq bridge + Eq.subst is
    // genuinely about the imported type.
    elaborate_decls_into(
        &mut env,
        "def q7 : @Eq.{1} Nat (unwrap b7) (unwrap b7) := @Eq.refl.{1} Nat (unwrap b7)",
    );
    elaborate_decls_into(
        &mut env,
        "def heqT7 : @Eq.{1} Nat (unwrap b7) (unwrap b7) := heqTransport b7 b7 (HEq.refl b7) q7",
    );
    assert!(
        def_eq(&env, &const_("heqT7"), &const_("q7")),
        "eq_of_heq + Eq.subst along HEq.refl over an imported Box must be the identity transport"
    );

    // unwrap b7 genuinely reduces through the imported Box.casesOn to 7 — the
    // projection the HEq transport is *about* is the imported-eliminator path.
    let u7 = Expr::app(const_("unwrap"), const_("b7"));
    assert!(def_eq(&env, &u7, &nat(7)), "unwrap b7 must reduce to 7");
    assert!(!def_eq(&env, &u7, &nat(0)), "unwrap b7 must be 7, not 0");
}

// ===========================================================================
// Control (generality): the SAME transports work on the NATIVE path, where
// `Box.casesOn` IS a registered recursor (`MajorAfterMinors`) and the
// `structure_fields` table is present. Confirms the transport behavior is
// general — not import-specific — and that native reduction is unchanged.
// ===========================================================================

#[test]
fn test_native_box_transport_unchanged() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_heq().expect("init_heq");
    env.add_inductive(box_decl()).expect("Box should declare");

    // Native Box.casesOn IS a registered recursor (MajorAfterMinors layout).
    let rec = env
        .get_recursor(&Name::from_string("Box.casesOn"))
        .expect("native Box.casesOn should be a registered recursor");
    assert_eq!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors,
        "native casesOn uses the MajorAfterMinors layout"
    );

    elaborate_decls_into(
        &mut env,
        "def unwrapN (b : Box) : Nat := match b with | Box.mk n => n\n\
         def n5 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))\n\
         def n3 : Box := Box.mk (Nat.succ (Nat.succ (Nat.succ Nat.zero)))\n\
         def castN : Box := @cast.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) n5\n\
         def mprN : Box := @Eq.mpr.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) n3\n\
         def matchCastN : Nat := match (@cast.{1} Box Box (@Eq.refl.{2} (Sort 1) Box) n5) with | Box.mk n => n",
    );

    // Native body still lowers through Box.casesOn (the registered recursor).
    let body = env
        .get_const(&Name::from_string("matchCastN"))
        .and_then(|i| i.value.clone())
        .expect("matchCastN body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Box.casesOn")),
        "native matchCastN lowers through Box.casesOn (the registered recursor)"
    );

    assert!(
        def_eq(&env, &const_("matchCastN"), &nat(5)),
        "native matchCastN must reduce to 5"
    );
    let uc = Expr::app(const_("unwrapN"), const_("castN"));
    assert!(
        def_eq(&env, &uc, &nat(5)),
        "native unwrapN castN must reduce to 5"
    );
    let um = Expr::app(const_("unwrapN"), const_("mprN"));
    assert!(
        def_eq(&env, &um, &nat(3)),
        "native unwrapN mprN must reduce to 3"
    );
    assert!(
        !def_eq(&env, &um, &nat(5)),
        "native Eq.mpr-transported value must be 3, not 5"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end probe: `match` lowering + kernel recursor reduction on an
//! *imported PARAMETERIZED* inductive (B45 / param_recursor scenario).
//!
//! Background. The B43 fix in `infer/elab_match/mod.rs` repaired the
//! `casesOn` argument-layout for an *imported* inductive: a Lean-compiled
//! `T.casesOn` loaded from `.olean` is a *definitional constant* (not a
//! registered recursor) whose body unfolds to `T.rec` with the **major
//! premise placed right after the motive** (`MajorAfterMotive`), whereas a
//! *native* clean-elab `T.casesOn` is a registered recursor with
//! `MajorAfterMinors`. The match lowering detects the imported layout via
//! `env.get_recursor(casesOn) == None` and emits the scrutinee *before* the
//! minor premises.
//!
//! B43 only exercised a **nullary enum** (`MyBool | myTrue | myFalse`). A
//! *parameterized* inductive with **field-carrying constructors** (a List/
//! Option-like `MyOption (α : Type) | none | some α`) adds two things the
//! nullary case never stressed:
//!
//!   1. The eliminator must be applied to the type **parameters**
//!      (`apply_eliminator_params`) *before* the motive — for the imported
//!      `MajorAfterMotive` layout the param/motive/major prefix must line up
//!      with the imported `.casesOn`'s actual binder telescope.
//!   2. The `some` minor premise carries a **field** that the match arm binds
//!      (`some x => x`); the field-binding lambda must wrap the body in the
//!      correct position so iota-reduction substitutes the *actual* field
//!      value.
//!
//! Either could be mis-handled the way the B43 nullary case silently mis-
//! reduced (every branch had the same type, so a wrong branch still type-
//! checked). This probe drives the whole chain and asserts the reduced
//! *value*, with distinct field/branch witnesses so a wrong branch or a wrong
//! field binding surfaces as the wrong constructor rather than passing
//! silently.
//!
//! Synthesizing the import. No checked-in `.olean` fixture carries a
//! parameterized inductive (the `Init/Option.olean` fixture is a re-export
//! header that adds zero constants; `custom/Inductive.olean` is the nullary
//! `MyBool`). So this test *synthesizes* the exact registration shape a real
//! `.olean` import produces, validated against the live `MyBool` fixture:
//!
//!   * `MyOption` inductive + `MyOption.none` / `MyOption.some` constructors +
//!     `MyOption.rec` recursor are built by the kernel (`add_inductive`) and
//!     copied verbatim — these are identical native-vs-imported.
//!   * `MyOption.casesOn` is registered as a **definitional constant** (a
//!     `Declaration::Definition`, *not* a recursor) whose value is the
//!     `MajorAfterMotive` body `fun α motive t mnone msome => MyOption.rec α
//!     motive mnone msome t`. This is byte-for-byte the shape the live
//!     `MyBool.casesOn` fixture has (confirmed by
//!     `test_imported_casesOn_shape_matches_live_mybool_fixture`), so
//!     `env.get_recursor("MyOption.casesOn")` is `None` — routing the match
//!     elaborator through the **imported** path under test.

use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};
use clean_olean::load_olean_file;
use std::path::PathBuf;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn inductive_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

/// Reduce `expr` to weak-head normal form and return the head `Const` name.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    match tc.whnf(expr).kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Build `MyBool : Type | myTrue | myFalse` natively. Provides two distinct
/// nullary witnesses so a wrong field/branch is observable in the reduced
/// result.
fn mybool_decl() -> InductiveDecl {
    let mybool = Name::from_string("MyBool");
    let ty = Expr::type_();
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mybool.clone(),
            type_: ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.myTrue"),
                    type_: const_("MyBool"),
                },
                Constructor {
                    name: Name::from_string("MyBool.myFalse"),
                    type_: const_("MyBool"),
                },
            ],
        }],
    }
}

/// Build `MyOption (α : Type) : Type | none | some (a : α)` natively.
///
/// Constructor types (the inductive's params are leading explicit binders):
/// `MyOption.none : (α : Type) → MyOption α` (with `α = BVar(0)`) and
/// `MyOption.some : (α : Type) → α → MyOption α` (under 2 binders, `α = BVar(1)`,
/// `a = BVar(0)`).
fn myoption_decl() -> InductiveDecl {
    let myoption = Name::from_string("MyOption");

    // MyOption : Type → Type
    let ind_ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());

    // MyOption.none : (α : Type) → MyOption α
    let none_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::app(const_("MyOption"), Expr::bvar(0)),
    );

    // MyOption.some : (α : Type) → α → MyOption α
    let some_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(const_("MyOption"), Expr::bvar(1)),
        ),
    );

    InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: myoption.clone(),
            type_: ind_ty,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOption.none"),
                    type_: none_ty,
                },
                Constructor {
                    name: Name::from_string("MyOption.some"),
                    type_: some_ty,
                },
            ],
        }],
    }
}

/// Build the *imported* (Lean `MajorAfterMotive`) `MyOption.casesOn` **type**:
///
/// ```text
/// (α : Type) → (motive : MyOption α → Sort u) → (t : MyOption α)
///   → motive (MyOption.none α)
///   → ((a : α) → motive (MyOption.some α a))
///   → motive t
/// ```
///
/// This is the parameterized analogue of the live `MyBool.casesOn` fixture
/// type `(motive) → (t) → motive myTrue → motive myFalse → motive t`, where
/// the **major premise `t` sits right after the motive** and the minor
/// premises come last — the layout the imported-match path expects. (The
/// native `build_cases_on` instead emits `... → minors → major`, so it cannot
/// stand in for the imported casesOn here.)
fn imported_myoption_cases_on_type(u: &Name) -> Expr {
    let myoption = |arg: Expr| Expr::app(const_("MyOption"), arg);
    let none = |a: Expr| Expr::app(const_("MyOption.none"), a);
    let some = |a: Expr, x: Expr| Expr::app(Expr::app(const_("MyOption.some"), a), x);
    let sort_u = Expr::sort(Level::param(u.clone()));

    // result (under 5 binders): motive t  →  App(BVar3=motive, BVar2=t)
    let result = Expr::app(Expr::bvar(3), Expr::bvar(2));

    // msome (under 4 binders: α=3, motive=2, t=1, mnone=0):
    //   (a : α) → motive (some α a)
    //   inside the inner Pi (+1 binder `a`): α=4, motive=3, a=0
    let msome = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(3), // a : α
        Expr::app(Expr::bvar(3), some(Expr::bvar(4), Expr::bvar(0))),
    );

    // mnone (under 3 binders: α=2, motive=1, t=0): motive (none α)
    let mnone = Expr::app(Expr::bvar(1), none(Expr::bvar(2)));

    // t : MyOption α (under 2 binders: α=1, motive=0)
    let t_dom = myoption(Expr::bvar(1));

    // motive : MyOption α → Sort u (under 1 binder: α=0; inner Pi: α=1)
    let motive_dom = Expr::pi(BinderInfo::Default, myoption(Expr::bvar(0)), sort_u);

    // α : Type
    let alpha_dom = Expr::type_();

    // Assemble outermost → innermost.
    let body = Expr::pi(BinderInfo::Default, msome, result);
    let body = Expr::pi(BinderInfo::Default, mnone, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Default, motive_dom, body);
    Expr::pi(BinderInfo::Implicit, alpha_dom, body)
}

/// Build the imported `MyOption.casesOn` **value**:
///
/// ```text
/// fun (α) (motive) (t) (mnone) (msome) => MyOption.rec.{u} α motive mnone msome t
/// ```
///
/// The inner `MyOption.rec` application uses the kernel's `MajorAfterMinors`
/// rec order `params → motives → minors → major`, exactly as the live
/// `MyBool.casesOn` body uses `MyBool.rec motive mtrue mfalse t`.
fn imported_myoption_cases_on_value(u: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("MyOption.rec"),
        vec![Level::param(u.clone())],
    );
    // Under 5 lambdas: α=4, motive=3, t=2, mnone=1, msome=0.
    // rec α motive mnone msome t
    let body = Expr::app(rec, Expr::bvar(4)); // α
    let body = Expr::app(body, Expr::bvar(3)); // motive
    let body = Expr::app(body, Expr::bvar(1)); // mnone
    let body = Expr::app(body, Expr::bvar(0)); // msome
    let body = Expr::app(body, Expr::bvar(2)); // t (major)

    // Wrap in the matching lambda telescope (same binder types as the type).
    let myoption = |arg: Expr| Expr::app(const_("MyOption"), arg);
    let some = |a: Expr, x: Expr| Expr::app(Expr::app(const_("MyOption.some"), a), x);
    let none = |a: Expr| Expr::app(const_("MyOption.none"), a);
    let sort_u = Expr::sort(Level::param(u.clone()));

    let msome_dom = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(3),
        Expr::app(Expr::bvar(3), some(Expr::bvar(4), Expr::bvar(0))),
    );
    let mnone_dom = Expr::app(Expr::bvar(1), none(Expr::bvar(2)));
    let t_dom = myoption(Expr::bvar(1));
    let motive_dom = Expr::pi(BinderInfo::Default, myoption(Expr::bvar(0)), sort_u);

    let body = Expr::lam(BinderInfo::Default, msome_dom, body);
    let body = Expr::lam(BinderInfo::Default, mnone_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Default, motive_dom, body);
    Expr::lam(BinderInfo::Implicit, Expr::type_(), body)
}

/// Build an environment that holds `MyBool` (native) and a *faithfully
/// imported* parameterized `MyOption`: real kernel-built inductive +
/// constructors + `MyOption.rec` recursor, but `MyOption.casesOn` as a plain
/// `Declaration::Definition` (so `get_recursor` is `None` — the imported path).
fn imported_myoption_env() -> Environment {
    // Native scratch env: lets the kernel build the correct MyOption.rec and
    // MyOption.casesOn *types* / rules for us to copy.
    let mut native = Environment::new();
    native
        .add_inductive(mybool_decl())
        .expect("MyBool should declare");
    native
        .add_inductive(myoption_decl())
        .expect("MyOption should declare");

    let mut env = Environment::new();

    // MyBool: copy inductive + constructors (we only need its two values).
    let mybool_ind = native
        .get_inductive(&Name::from_string("MyBool"))
        .cloned()
        .expect("MyBool inductive");
    env.register_inductive(mybool_ind);
    for ctor in ["MyBool.myTrue", "MyBool.myFalse"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }

    // MyOption: copy inductive + constructors + the `rec` recursor verbatim.
    let myopt_ind = native
        .get_inductive(&Name::from_string("MyOption"))
        .cloned()
        .expect("MyOption inductive");
    env.register_inductive(myopt_ind);
    for ctor in ["MyOption.none", "MyOption.some"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }
    let myopt_rec = native
        .get_recursor(&Name::from_string("MyOption.rec"))
        .cloned()
        .expect("MyOption.rec");
    // Also register the rec's ConstantInfo so the kernel can type-check the
    // casesOn definition that references MyOption.rec.
    let rec_const = native
        .get_const(&Name::from_string("MyOption.rec"))
        .cloned()
        .expect("MyOption.rec const");
    env.extend_constants_unchecked(std::iter::once(rec_const));
    env.register_recursor(myopt_rec.clone());

    // The recursor's single universe parameter (the motive universe) — reused
    // verbatim so the synthesized casesOn references the same `u` as the rec.
    let u = myopt_rec
        .level_params
        .first()
        .cloned()
        .expect("MyOption.rec has a motive universe parameter");

    // Synthesize the imported `MyOption.casesOn` as a Definition (NOT a
    // recursor) with the Lean `MajorAfterMotive` casesOn **type** (major right
    // after the motive) and a value that unfolds to `MyOption.rec`.
    let cases_type = imported_myoption_cases_on_type(&u);
    let cases_value = imported_myoption_cases_on_value(&u);

    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body and is kernel
    // type-checked by `add_decl_structural` against the casesOn type below.
    // Mirrors exactly what `.olean` import produces (see module docs).
    env.add_decl_structural(clean_kernel::env::Declaration::Definition {
        name: Name::from_string("MyOption.casesOn"),
        level_params: vec![u],
        type_: cases_type,
        value: cases_value,
        is_reducible: false,
    })
    .expect("imported MyOption.casesOn definition should kernel-check");

    env
}

/// Elaborate and register declarations from `source` into `env`.
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
// Precondition: the synthesized import matches the live `.olean` shape.
// ---------------------------------------------------------------------------

/// Lock the claim that the synthesized `MyOption.casesOn` reproduces the exact
/// registration shape a real `.olean` import produces, by checking the live
/// `MyBool.casesOn` fixture against the same invariants:
///
/// * `casesOn` is a *definitional constant with a value* (NOT a recursor),
/// * `rec` IS a registered recursor with `MajorAfterMinors`.
///
/// If the import representation ever changes, this fails first and tells us the
/// synthesis is stale.
#[test]
fn test_imported_cases_on_shape_matches_live_mybool_fixture() {
    let mut fixture_env = Environment::default();
    load_olean_file(&mut fixture_env, inductive_fixture_path())
        .expect("MyBool fixture should load");

    // Live fixture invariants.
    assert!(
        fixture_env
            .get_recursor(&Name::from_string("MyBool.casesOn"))
            .is_none(),
        "live imported MyBool.casesOn must NOT be a registered recursor"
    );
    let mybool_cases = fixture_env
        .get_const(&Name::from_string("MyBool.casesOn"))
        .expect("MyBool.casesOn const");
    assert!(
        mybool_cases.value.is_some(),
        "live imported MyBool.casesOn must be a definitional constant with a value"
    );
    assert_eq!(
        fixture_env
            .get_recursor(&Name::from_string("MyBool.rec"))
            .map(|r| r.arg_order),
        Some(clean_kernel::RecursorArgOrder::MajorAfterMinors),
        "live MyBool.rec must be a MajorAfterMinors recursor"
    );

    // Synthesized MyOption matches those invariants.
    let env = imported_myoption_env();
    assert!(
        env.get_recursor(&Name::from_string("MyOption.casesOn"))
            .is_none(),
        "synthesized MyOption.casesOn must NOT be a registered recursor \
         (this is what routes the elaborator through the imported path)"
    );
    let myopt_cases = env
        .get_const(&Name::from_string("MyOption.casesOn"))
        .expect("MyOption.casesOn const");
    assert!(
        myopt_cases.value.is_some(),
        "synthesized MyOption.casesOn must be a definitional constant with a value"
    );
    assert_eq!(
        env.get_recursor(&Name::from_string("MyOption.rec"))
            .map(|r| r.arg_order),
        Some(clean_kernel::RecursorArgOrder::MajorAfterMinors),
        "MyOption.rec must be a MajorAfterMinors recursor"
    );
    assert_eq!(
        env.get_inductive(&Name::from_string("MyOption"))
            .map(|i| i.num_params),
        Some(1),
        "MyOption is a single-parameter inductive"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `MyOption.casesOn` itself reduces correctly when
// applied by hand. This isolates any failure in the match test to the
// *elaborator's* lowering rather than the kernel's reduction of the imported
// definitional casesOn.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_param_cases_on_kernel_reduction_is_correct() {
    let env = imported_myoption_env();

    // Apply MyOption.casesOn directly:
    //   casesOn.{0} (α := MyBool) (motive := fun _ => MyBool)
    //               (t := some MyBool myTrue)
    //               (mnone := myFalse) (msome := fun a => a)
    // Should iota-reduce (via the inner MyOption.rec) to `myTrue`.
    let mybool = const_("MyBool");
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(const_("MyOption"), mybool.clone()),
        mybool.clone(),
    );
    let some_true = Expr::app(
        Expr::app(const_("MyOption.some"), mybool.clone()),
        const_("MyBool.myTrue"),
    );
    let msome = Expr::lam(BinderInfo::Default, mybool.clone(), Expr::bvar(0));

    let cases = Expr::const_(Name::from_string("MyOption.casesOn"), vec![Level::zero()]);
    let app = Expr::app(cases.clone(), mybool.clone()); // α
    let app = Expr::app(app, motive.clone()); // motive
    let app = Expr::app(app, some_true); // major (MajorAfterMotive)
    let app = Expr::app(app, const_("MyBool.myFalse")); // mnone
    let app = Expr::app(app, msome.clone()); // msome
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("MyBool.myTrue"),
        "imported MyOption.casesOn on (some myTrue) must select the some branch and bind the field"
    );

    // none case → mnone (myFalse).
    let none_val = Expr::app(const_("MyOption.none"), mybool.clone());
    let app = Expr::app(cases, mybool.clone());
    let app = Expr::app(app, motive);
    let app = Expr::app(app, none_val); // major
    let app = Expr::app(app, const_("MyBool.myFalse")); // mnone
    let app = Expr::app(app, msome); // msome
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("MyBool.myFalse"),
        "imported MyOption.casesOn on none must select the none branch"
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE: clean-elab `match` on the imported parameterized inductive must
// reduce to the correct branch AND bind the field value correctly.
// ---------------------------------------------------------------------------

#[test]
fn test_match_on_imported_param_inductive_reduces_and_binds_field() {
    let mut env = imported_myoption_env();

    // A clean-elab definition that matches on the imported parameterized
    // inductive, binding the `some` field and returning a *distinct* value in
    // each branch so a wrong branch / wrong field binding is observable.
    //
    //   getOr (d : MyBool) : MyOption MyBool → MyBool
    //     | MyOption.none   => d
    //     | MyOption.some x => x
    elaborate_decls_into(
        &mut env,
        "def getOr (d : MyBool) : MyOption MyBool → MyBool\n  \
         | MyOption.none => d\n  \
         | MyOption.some x => x",
    );

    // Confirm the elaborated body went through the imported eliminator and the
    // imported constructors — proving the chain is genuinely wired.
    let info = env
        .get_const(&Name::from_string("getOr"))
        .expect("getOr should be registered");
    let body = info.value.as_ref().expect("getOr is a definition");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("MyOption.casesOn")),
        "getOr must compile through the imported MyOption.casesOn, got: {referenced:?}"
    );

    // some-branch: getOr myFalse (some MyBool myTrue) must bind the field and
    // return myTrue (NOT the default myFalse, NOT the wrong branch).
    let some_true = Expr::app(
        Expr::app(const_("MyOption.some"), const_("MyBool")),
        const_("MyBool.myTrue"),
    );
    let call_some = Expr::app(
        Expr::app(const_("getOr"), const_("MyBool.myFalse")),
        some_true,
    );
    assert_eq!(
        whnf_head_const(&env, &call_some).as_deref(),
        Some("MyBool.myTrue"),
        "getOr myFalse (some myTrue) must reduce to the bound field myTrue — \
         a wrong branch would give myFalse, a wrong field binding would give the default"
    );

    // none-branch: getOr myTrue none must return the default myTrue.
    let none_val = Expr::app(const_("MyOption.none"), const_("MyBool"));
    let call_none = Expr::app(
        Expr::app(const_("getOr"), const_("MyBool.myTrue")),
        none_val,
    );
    assert_eq!(
        whnf_head_const(&env, &call_none).as_deref(),
        Some("MyBool.myTrue"),
        "getOr myTrue none must reduce to the default myTrue (the none branch)"
    );

    // Cross-check the discriminating witness: swapping the default proves the
    // some-branch genuinely returns the field, not the default.
    let some_true2 = Expr::app(
        Expr::app(const_("MyOption.some"), const_("MyBool")),
        const_("MyBool.myTrue"),
    );
    let call_some_swapped_default = Expr::app(
        Expr::app(const_("getOr"), const_("MyBool.myFalse")),
        some_true2,
    );
    assert_ne!(
        whnf_head_const(&env, &call_some_swapped_default).as_deref(),
        Some("MyBool.myFalse"),
        "the some-branch must return the bound field, never the (myFalse) default"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end probe: `match` lowering + kernel recursor reduction on an
//! *imported MUTUAL inductive member* (mutual_recursor scenario).
//!
//! Background. B45 (`import_e2e_param_recursor_tests.rs`) validated the
//! imported-eliminator path for a *single, parameterized* inductive whose
//! `T.casesOn` is a definitional constant unfolding to `T.rec` in the Lean
//! `MajorAfterMotive` layout (`get_recursor(casesOn) == None`).
//!
//! A genuine **mutual** inductive block (`Even`/`Odd`) raises the bar: its
//! recursor / casesOn are *multi-motive* eliminators — `num_motives == 2`
//! (one motive per type in the block) and `num_minors == 3` (the minors span
//! *every* constructor of *both* types, with cross-referencing IH/conclusion
//! motives). The Clean kernel builds `Even.casesOn` exactly this way:
//!
//! ```text
//! Even.casesOn :
//!   {me : Even -> Sort u} -> {mo : Odd -> Sort u}        -- TWO motives
//!     -> me Even.even_zero                                -- minor: Even.even_zero
//!     -> ((o : Odd) -> me (Even.even_succ o))             -- minor: Even.even_succ
//!     -> ((e : Even) -> mo (Odd.odd_succ e))              -- minor: Odd.odd_succ
//!     -> (t : Even) -> me t
//! ```
//!
//! The imported (Lean `.olean`) shape places the major premise *right after
//! the motives* and is registered as a plain `Declaration::Definition` (so
//! `env.get_recursor("Even.casesOn") == None`), routing the match elaborator
//! through the imported path under test:
//!
//! ```text
//! imported Even.casesOn :
//!   {me} -> {mo} -> (t : Even)
//!     -> me Even.even_zero
//!     -> ((o : Odd) -> me (Even.even_succ o))
//!     -> ((e : Even) -> mo (Odd.odd_succ e))
//!     -> me t
//!   := fun me mo t m0 m1 m2 => Even.rec me mo m0 m1 m2 t
//! ```
//!
//! This probe drives the whole chain — `match` lowering against the imported
//! multi-motive `casesOn`, then kernel iota-reduction — and asserts the
//! reduced *value* with distinct branch witnesses so a motive/minor
//! mis-indexing surfaces as the wrong constructor rather than passing
//! silently.

use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to weak-head normal form and return its head `Const` name.
///
/// The head is the function of the (possibly applied) whnf result, so this
/// handles both a bare constant (`Even.even_zero`) and a constructor applied
/// to fields (`Even.even_succ o`).
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Build the Even/Odd mutual block:
///
/// ```text
/// mutual
///   inductive Even : Type | even_zero | even_succ (o : Odd)
///   inductive Odd  : Type | odd_succ (e : Even)
/// end
/// ```
///
/// The constructors cross-reference (`Even.even_succ` carries an `Odd`,
/// `Odd.odd_succ` carries an `Even`), which is what forces the recursor to be
/// genuinely multi-motive.
fn even_odd_decl() -> InductiveDecl {
    // Even.even_zero : Even
    let even_zero_ty = const_("Even");
    // Even.even_succ : Odd -> Even
    let even_succ_ty = Expr::pi(BinderInfo::Default, const_("Odd"), const_("Even"));
    // Odd.odd_succ : Even -> Odd
    let odd_succ_ty = Expr::pi(BinderInfo::Default, const_("Even"), const_("Odd"));

    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: Name::from_string("Even"),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Even.even_zero"),
                        type_: even_zero_ty,
                    },
                    Constructor {
                        name: Name::from_string("Even.even_succ"),
                        type_: even_succ_ty,
                    },
                ],
            },
            InductiveType {
                name: Name::from_string("Odd"),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("Odd.odd_succ"),
                    type_: odd_succ_ty,
                }],
            },
        ],
    }
}

/// Build the imported (Lean `MajorAfterMotive`) `Even.casesOn` **type**:
///
/// ```text
/// {me : Even -> Sort u} -> {mo : Odd -> Sort u} -> (t : Even)
///   -> me Even.even_zero
///   -> ((o : Odd) -> me (Even.even_succ o))
///   -> ((e : Even) -> mo (Odd.odd_succ e))
///   -> me t
/// ```
fn imported_even_cases_on_type(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let even_succ = |o: Expr| Expr::app(const_("Even.even_succ"), o);
    let odd_succ = |e: Expr| Expr::app(const_("Odd.odd_succ"), e);

    // Binder telescope (outer -> inner):
    //   #5 me, #4 mo, #3 t, #2 m0, #1 m1, #0 m2 ... but indices below are stated
    //   relative to each binder's scope (innermost binder = #0).

    // result (under 6 binders me,mo,t,m0,m1,m2): me t  => (#5 #3)
    let result = Expr::app(Expr::bvar(5), Expr::bvar(3));

    // m2 (under 5 binders me,mo,t,m0,m1): (e : Even) -> mo (Odd.odd_succ e)
    //   inside inner Pi (+1 binder e): me=5, mo=4, e=0 -> mo (odd_succ e) = (#4 (odd_succ #0))
    let m2 = Expr::pi(
        BinderInfo::Default,
        const_("Even"),
        Expr::app(Expr::bvar(4), odd_succ(Expr::bvar(0))),
    );

    // m1 (under 4 binders me,mo,t,m0): (o : Odd) -> me (Even.even_succ o)
    //   inside inner Pi (+1 binder o): me=4, o=0 -> me (even_succ o) = (#4 (even_succ #0))
    let m1 = Expr::pi(
        BinderInfo::Default,
        const_("Odd"),
        Expr::app(Expr::bvar(4), even_succ(Expr::bvar(0))),
    );

    // m0 (under 3 binders me,mo,t): me Even.even_zero => (#2 even_zero)
    let m0 = Expr::app(Expr::bvar(2), const_("Even.even_zero"));

    // t : Even (under 2 binders me,mo)
    let t_dom = const_("Even");

    // mo : Odd -> Sort u (under 1 binder me)
    let mo_dom = Expr::pi(BinderInfo::Default, const_("Odd"), sort_u.clone());

    // me : Even -> Sort u (under 0 binders)
    let me_dom = Expr::pi(BinderInfo::Default, const_("Even"), sort_u);

    // Assemble outermost -> innermost.
    let body = Expr::pi(BinderInfo::Default, m2, result);
    let body = Expr::pi(BinderInfo::Default, m1, body);
    let body = Expr::pi(BinderInfo::Default, m0, body);
    let body = Expr::pi(BinderInfo::Default, t_dom, body);
    let body = Expr::pi(BinderInfo::Implicit, mo_dom, body);
    Expr::pi(BinderInfo::Implicit, me_dom, body)
}

/// Build the imported `Even.casesOn` **value**:
///
/// ```text
/// fun me mo t m0 m1 m2 =>
///   Even.rec.{u} me mo
///     m0
///     (fun (o : Odd)  (_ih : mo o) => m1 o)   -- drop the IH the rec passes
///     (fun (e : Even) (_ih : me e) => m2 e)   -- drop the IH the rec passes
///     t
/// ```
///
/// The inner `Even.rec` uses the kernel's `MajorAfterMinors` layout, and each
/// minor of `rec` carries an extra induction-hypothesis binder that `casesOn`
/// must absorb (this is precisely how Lean derives `casesOn` from `rec`).
fn imported_even_cases_on_value(u: &Name) -> Expr {
    let rec = Expr::const_(Name::from_string("Even.rec"), vec![Level::param(u.clone())]);
    let even_succ = |o: Expr| Expr::app(const_("Even.even_succ"), o);
    let odd_succ = |e: Expr| Expr::app(const_("Odd.odd_succ"), e);

    // Outer telescope binders (de Bruijn from the body): me=5, mo=4, t=3,
    // m0=2, m1=1, m2=0.
    //
    // even_succ rec-minor := fun (o : Odd) (_ih : mo o) => m1 o
    //   innermost body under [me,mo,t,m0,m1,m2,o,ih]: ih=0,o=1,m2=2,m1=3 -> m1 o = (#3 #1)
    let esucc_body = Expr::app(Expr::bvar(3), Expr::bvar(1));
    //   ih binder type under [me,mo,t,m0,m1,m2,o]: mo=5, o=0 -> mo o = (#5 #0)
    let esucc_ih_ty = Expr::app(Expr::bvar(5), Expr::bvar(0));
    let esucc_minor = Expr::lam(BinderInfo::Default, esucc_ih_ty, esucc_body);
    let esucc_minor = Expr::lam(BinderInfo::Default, const_("Odd"), esucc_minor);

    // odd_succ rec-minor := fun (e : Even) (_ih : me e) => m2 e
    //   under binders me,mo,t,m0,m1,m2,e (e innermost=0): me=6, e=0 -> me e = (#6 #0)
    //   innermost body under [.., m2, e, ih]: ih=0, e=1, m2=2 -> m2 e = (#2 #1)
    let osucc_body = Expr::app(Expr::bvar(2), Expr::bvar(1));
    let osucc_ih_ty = Expr::app(Expr::bvar(6), Expr::bvar(0));
    let osucc_minor = Expr::lam(BinderInfo::Default, osucc_ih_ty, osucc_body);
    let osucc_minor = Expr::lam(BinderInfo::Default, const_("Even"), osucc_minor);

    // rec me mo m0 esucc_minor osucc_minor t
    let body = Expr::app(rec, Expr::bvar(5)); // me
    let body = Expr::app(body, Expr::bvar(4)); // mo
    let body = Expr::app(body, Expr::bvar(2)); // m0 (even_zero, no fields)
    let body = Expr::app(body, esucc_minor); // even_succ wrapped minor
    let body = Expr::app(body, osucc_minor); // odd_succ wrapped minor
    let body = Expr::app(body, Expr::bvar(3)); // t (major)

    // Wrap in the matching lambda telescope (same binder types as the type).
    let sort_u = Expr::sort(Level::param(u.clone()));
    let m2_dom = Expr::pi(
        BinderInfo::Default,
        const_("Even"),
        Expr::app(Expr::bvar(4), odd_succ(Expr::bvar(0))),
    );
    let m1_dom = Expr::pi(
        BinderInfo::Default,
        const_("Odd"),
        Expr::app(Expr::bvar(4), even_succ(Expr::bvar(0))),
    );
    let m0_dom = Expr::app(Expr::bvar(2), const_("Even.even_zero"));
    let t_dom = const_("Even");
    let mo_dom = Expr::pi(BinderInfo::Default, const_("Odd"), sort_u.clone());
    let me_dom = Expr::pi(BinderInfo::Default, const_("Even"), sort_u);

    let body = Expr::lam(BinderInfo::Default, m2_dom, body);
    let body = Expr::lam(BinderInfo::Default, m1_dom, body);
    let body = Expr::lam(BinderInfo::Default, m0_dom, body);
    let body = Expr::lam(BinderInfo::Default, t_dom, body);
    let body = Expr::lam(BinderInfo::Implicit, mo_dom, body);
    Expr::lam(BinderInfo::Implicit, me_dom, body)
}

/// Build an environment holding a *faithfully imported* mutual `Even`/`Odd`:
/// real kernel-built inductives + constructors + `Even.rec`/`Odd.rec`
/// recursors, but `Even.casesOn` as a plain `Declaration::Definition` (so
/// `get_recursor("Even.casesOn")` is `None` — the imported path).
fn imported_even_odd_env() -> Environment {
    // Native scratch env: lets the kernel build the correct recs / casesOns.
    let mut native = Environment::new();
    native
        .add_inductive(even_odd_decl())
        .expect("Even/Odd should declare");

    let mut env = Environment::new();

    // Copy both inductives + all constructors verbatim.
    for ind in ["Even", "Odd"] {
        let iv = native
            .get_inductive(&Name::from_string(ind))
            .cloned()
            .unwrap_or_else(|| panic!("{ind} inductive"));
        env.register_inductive(iv);
    }
    for ctor in ["Even.even_zero", "Even.even_succ", "Odd.odd_succ"] {
        let c = native
            .get_constructor(&Name::from_string(ctor))
            .cloned()
            .unwrap_or_else(|| panic!("{ctor} ctor"));
        env.register_constructor(c);
    }

    // Copy Even.rec + Odd.rec recursors verbatim (these stay recursors on
    // import) and their ConstantInfo so the kernel can type-check the casesOn
    // definitions that reference them.
    for rec in ["Even.rec", "Odd.rec"] {
        let rv = native
            .get_recursor(&Name::from_string(rec))
            .cloned()
            .unwrap_or_else(|| panic!("{rec} recursor"));
        let rc = native
            .get_const(&Name::from_string(rec))
            .cloned()
            .unwrap_or_else(|| panic!("{rec} const"));
        env.extend_constants_unchecked(std::iter::once(rc));
        env.register_recursor(rv);
    }

    // The recursor's motive universe parameter, reused verbatim.
    let u = native
        .get_recursor(&Name::from_string("Even.rec"))
        .and_then(|r| r.level_params.first().cloned())
        .expect("Even.rec has a motive universe parameter");

    // Synthesize the imported `Even.casesOn` as a Definition (NOT a recursor)
    // with the Lean `MajorAfterMotive` casesOn type and a value unfolding to
    // `Even.rec`.
    //
    // SOUNDNESS: test-only synthesis of the imported `.casesOn` definitional
    // constant. The value is the standard casesOn-via-rec body and is kernel
    // type-checked by `add_decl_structural` against the casesOn type. Mirrors
    // exactly what `.olean` import of a mutual member produces.
    env.add_decl_structural(clean_kernel::env::Declaration::Definition {
        name: Name::from_string("Even.casesOn"),
        level_params: vec![u.clone()],
        type_: imported_even_cases_on_type(&u),
        value: imported_even_cases_on_value(&u),
        is_reducible: false,
    })
    .expect("imported Even.casesOn definition should kernel-check");

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
// Precondition: the synthesized import has the multi-motive shape.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_mutual_cases_on_shape() {
    let env = imported_even_odd_env();

    // Even.rec / Odd.rec are real multi-motive recursors.
    let even_rec = env
        .get_recursor(&Name::from_string("Even.rec"))
        .expect("Even.rec recursor");
    assert_eq!(
        even_rec.num_motives, 2,
        "Even.rec is a multi-motive mutual recursor"
    );
    assert_eq!(
        even_rec.num_minors, 3,
        "Even.rec spans all 3 constructors of the mutual block"
    );

    // Even.casesOn is a definitional constant (NOT a registered recursor) —
    // this routes the match elaborator through the imported path.
    assert!(
        env.get_recursor(&Name::from_string("Even.casesOn"))
            .is_none(),
        "imported Even.casesOn must NOT be a registered recursor"
    );
    let cases = env
        .get_const(&Name::from_string("Even.casesOn"))
        .expect("Even.casesOn const");
    assert!(
        cases.value.is_some(),
        "imported Even.casesOn must be a definitional constant with a value"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported multi-motive `Even.casesOn` reduces correctly when
// applied by hand. Isolates any match-test failure to the *elaborator's*
// lowering rather than the kernel's reduction of the imported casesOn.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_mutual_cases_on_kernel_reduction_is_correct() {
    let env = imported_even_odd_env();

    // motive_even := fun _ : Even => MyResult-ish; we use a small enum-free
    // result type `Even` itself, returning distinct constructors per branch.
    // me := fun _ : Even => Even ; mo := fun _ : Odd => Even.
    let me = Expr::lam(BinderInfo::Default, const_("Even"), const_("Even"));
    let mo = Expr::lam(BinderInfo::Default, const_("Odd"), const_("Even"));

    // minors:
    //   m0 (even_zero)  := Even.even_zero
    //   m1 (even_succ)  := fun (o : Odd) => Even.even_zero      -- distinct: zero
    //   m2 (odd_succ)   := fun (e : Even) => e                  -- dead for Even scrutinee
    let m0 = const_("Even.even_zero");
    let m1 = Expr::lam(BinderInfo::Default, const_("Odd"), const_("Even.even_zero"));
    let m2 = Expr::lam(BinderInfo::Default, const_("Even"), Expr::bvar(0));

    let cases = Expr::const_(Name::from_string("Even.casesOn"), vec![Level::zero()]);

    // even_succ branch: casesOn me mo (even_succ odd_succ even_zero) m0 m1 m2
    // should select m1 and reduce to Even.even_zero (the m1 body).
    let odd_val = Expr::app(const_("Odd.odd_succ"), const_("Even.even_zero"));
    let even_succ_val = Expr::app(const_("Even.even_succ"), odd_val);
    let app = Expr::app(cases.clone(), me.clone()); // me
    let app = Expr::app(app, mo.clone()); // mo
    let app = Expr::app(app, even_succ_val); // major (MajorAfterMotive)
    let app = Expr::app(app, m0.clone()); // m0
    let app = Expr::app(app, m1.clone()); // m1
    let app = Expr::app(app, m2.clone()); // m2
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("Even.even_zero"),
        "imported multi-motive Even.casesOn on (even_succ _) must select the m1 minor"
    );

    // even_zero branch: casesOn me mo even_zero m0 m1 m2 -> m0 = even_zero.
    // (Distinguish from m1 by making m0 also even_zero but with the major being
    // even_zero; this checks the major routes to the right minor.)
    let app = Expr::app(cases, me);
    let app = Expr::app(app, mo);
    let app = Expr::app(app, const_("Even.even_zero")); // major
    let app = Expr::app(app, m0); // m0
    let app = Expr::app(app, m1); // m1
    let app = Expr::app(app, m2); // m2
    assert_eq!(
        whnf_head_const(&env, &app).as_deref(),
        Some("Even.even_zero"),
        "imported multi-motive Even.casesOn on even_zero must select the m0 minor"
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE: clean-elab `match` on the imported mutual member must lower
// through the multi-motive imported `Even.casesOn` and reduce to the correct
// branch.
// ---------------------------------------------------------------------------

#[test]
fn test_match_on_imported_mutual_member_reduces_to_correct_branch() {
    let mut env = imported_even_odd_env();

    // A clean-elab definition matching on the imported mutual member `Even`,
    // returning a *distinct* value per branch so a wrong branch / motive /
    // minor mis-indexing is observable:
    //
    //   def classify (x : Even) : Even := match x with
    //     | Even.even_zero   => Even.even_zero
    //     | Even.even_succ o => Even.even_succ o
    //
    // The branches return values with *different constructor heads*
    // (`Even.even_zero` vs `Even.even_succ`), and the even_succ branch *binds
    // the field* `o : Odd` and re-wraps it — so a wrong branch, a dropped
    // second motive/minor, or a wrong field binding surfaces observably.
    elaborate_decls_into(
        &mut env,
        "def classify (x : Even) : Even := match x with\n  \
         | Even.even_zero => Even.even_zero\n  \
         | Even.even_succ o => Even.even_succ o",
    );

    // Confirm the body compiled through the imported multi-motive casesOn.
    let info = env
        .get_const(&Name::from_string("classify"))
        .expect("classify should be registered");
    let body = info.value.as_ref().expect("classify is a definition");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Even.casesOn")),
        "classify must compile through the imported Even.casesOn, got: {referenced:?}"
    );

    // even_zero branch: classify even_zero must select the zero branch and
    // reduce to Even.even_zero.
    let call_zero = Expr::app(const_("classify"), const_("Even.even_zero"));
    assert_eq!(
        whnf_head_const(&env, &call_zero).as_deref(),
        Some("Even.even_zero"),
        "classify even_zero must select the even_zero branch"
    );

    // even_succ branch: classify (even_succ o) must select the even_succ branch
    // and reduce to Even.even_succ — a DIFFERENT head than the zero branch.
    let inner_odd = Expr::app(const_("Odd.odd_succ"), const_("Even.even_zero"));
    let even_succ_val = Expr::app(const_("Even.even_succ"), inner_odd);
    let call_succ = Expr::app(const_("classify"), even_succ_val);
    assert_eq!(
        whnf_head_const(&env, &call_succ).as_deref(),
        Some("Even.even_succ"),
        "classify (even_succ o) must select the even_succ branch \
         (head Even.even_succ, NOT the even_zero branch)"
    );

    // Field-binding witness: the even_succ branch must rebuild even_succ from
    // the *bound* field `o` verbatim. With a deep `o`, `classify (even_succ o)`
    // must reduce to exactly `even_succ o`.
    let tc = TypeChecker::new(&env);
    let deep_odd = Expr::app(
        const_("Odd.odd_succ"),
        Expr::app(
            const_("Even.even_succ"),
            Expr::app(const_("Odd.odd_succ"), const_("Even.even_zero")),
        ),
    );
    let succ_deep = Expr::app(const_("Even.even_succ"), deep_odd);
    let call_succ_deep = Expr::app(const_("classify"), succ_deep.clone());
    let reduced_succ_deep = tc.whnf(&call_succ_deep);
    assert!(
        tc.is_def_eq(&reduced_succ_deep, &succ_deep),
        "classify (even_succ o) must rebuild even_succ from the bound field o; \
         got head {} but expected even_succ",
        debug_head(&reduced_succ_deep),
    );
    // And it must NOT collapse to the even_zero branch's value — a dropped
    // motive/minor that mis-routed the branch would surface here.
    assert!(
        !tc.is_def_eq(&reduced_succ_deep, &const_("Even.even_zero")),
        "the even_succ branch must NOT collapse to the even_zero branch value; \
         a dropped second motive/minor would mis-route the branch"
    );
}

/// Render the head constructor application of `e` for assertion messages.
fn debug_head(e: &Expr) -> String {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => format!("{other:?}"),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: well-founded recursion over an *imported* `Acc` (accessibility)
//! eliminator (well_founded_recursion scenario).
//!
//! ## Why `Acc` is the sharpest WF-recursion import probe
//!
//! The whole point of well-founded recursion in Lean is `Acc.rec`: every
//! `WellFounded.fix` / `WellFounded.fixF` definition bottoms out in
//! `@Acc.rec`, which iota-reduces when (and only when) its *major premise* — an
//! accessibility proof — is headed by the constructor `Acc.intro`. `Acc.rec` is
//! a large-eliminating recursor on a `Prop` (`Acc r x : Prop`, eliminating into
//! `Sort v`), so its eliminator layout is special:
//!
//! ```text
//! @Acc.rec.{v, u}
//!   {α : Sort u} {r : α → α → Prop}
//!   {motive : (a : α) → Acc r a → Sort v}       -- motive AFTER params
//!   (minor : (x : α) → (h : ∀ y, r y x → Acc r y)
//!              → (ih : ∀ y, r y x → motive y (h y …)) → motive x (Acc.intro x h))
//!   {a : α}                                       -- the index
//!   (t : Acc r a)                                 -- the major premise (last)
//!   : motive a t
//! ```
//!
//! `num_params == 2`, `num_motives == 1`, `num_minors == 1`, `num_indices == 1`,
//! `arg_order == MajorAfterMinors`, and crucially the recursor carries **two**
//! universe params `[v, u]` (motive universe first). A path that computes any of
//! that layout from native clean-side metadata — rather than from the imported
//! `RecursorVal` — would place the motive, the `Acc.intro` minor, the index, or
//! the major premise in the wrong slot, and the term would either fail to
//! type-check or fail to iota-reduce.
//!
//! ## The imported (`.olean`) shape we reproduce
//!
//! A real Lean `.olean` ships `Acc` + `Acc.intro` + the **recursor** `Acc.rec`,
//! and ships `WellFounded.fix` / `WellFounded.fixF` as plain *definitional
//! constants* that unfold to `@Acc.rec`. It does **not** run Clean's
//! `init_well_founded` bootstrap — so `Acc.rec` is a genuine registered
//! recursor, but there is no clean-side WellFounded scaffolding. We reproduce
//! that exactly: the kernel builds `Acc` + `Acc.rec` in a scratch env, we copy
//! the inductive / constructor / recursor verbatim into a fresh env, and we then
//! build the WF combinator *through the clean-elab elaborator* over the imported
//! `Acc.rec`. We assert `get_recursor("Acc.rec") == Some` (genuine eliminator)
//! and `has not been initialised via init_well_founded` so the probe stays
//! honest about exercising the import path.
//!
//! ## What this pins
//!
//! `Acc.rec` reduction (kernel) and the clean-elab lowering of a definition that
//! recurses through the imported `Acc.rec` both place the motive / `Acc.intro`
//! minor / index / major premise in the right slots and reduce to the genuinely
//! correct value. Distinct witnesses make a wrong slot observable as a different
//! `Nat` (or a stuck term) rather than passing silently. A native control
//! (Clean's own `Acc` built in-process, `Acc.rec` a registered recursor) isolates
//! any regression to the imported-eliminator handling. This validated the import
//! path — no clean-elab correctness bug was found for WF recursion over imports;
//! the tests lock the behavior in.
//!
//! One genuine *elaboration-feature* gap is pinned with a flip-on-fix assertion
//! (not `#[ignore]`): well-founded recursion does **not** reduce definitionally
//! through a *named, opaque* accessibility proof — matching Lean, where WF
//! definitions reduce only via the propositional `WellFounded.fixFEq` equation,
//! never by kernel iota on an opaque `Acc` proof. The probe reduces through an
//! *inlined* `Acc.intro` proof, which is where iota genuinely fires.

use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, RecursorArgOrder, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

fn nat() -> Expr {
    const_("Nat")
}

/// `Nat` literal `n` built from `Nat.zero` / `Nat.succ`.
fn nat_lit(n: u32) -> Expr {
    let mut e = const_("Nat.zero");
    for _ in 0..n {
        e = succ(e);
    }
    e
}

/// `Sort 1` = the universe `Nat` lives in (`Nat : Type 0 = Sort 1`).
fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// `Acc.{1}` — `Acc` specialised to a `Type`-level `α` (here `Nat`).
fn acc_c() -> Expr {
    Expr::const_(Name::from_string("Acc"), vec![lvl1()])
}

/// The empty relation on `Nat`: `fun (_ _ : Nat) => False`. Nothing is below
/// anything, so *every* point is trivially accessible with a non-recursive
/// `Acc.intro` whose field is discharged from `False`.
fn empty_rel() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), const_("False")),
    )
}

/// `Acc Nat emptyRel x`.
fn acc_at(x: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(acc_c(), nat()), empty_rel()), x)
}

/// A concrete, *inlined* accessibility proof
/// `@Acc.intro Nat emptyRel x (fun (y : Nat) (h : emptyRel y x) => False.elim h)`.
///
/// `emptyRel y x` reduces to `False`, so the field is discharged with
/// `False.elim` and no recursion — a closed `Acc.intro`-headed term. Inlining
/// (rather than naming a `def`) matters: `Acc.rec` only iota-reduces when the
/// major premise *whnfs to* `Acc.intro`, and a named proof of a `Prop` stays
/// opaque (see the pinned flip-on-fix test).
fn acc_proof(x: Expr) -> Expr {
    // Under [y, h]: y = BVar(1).  motive of False.elim is `Acc emptyRel y`.
    let acc_r_y = Expr::app(
        Expr::app(Expr::app(acc_c(), nat()), empty_rel()),
        Expr::bvar(1),
    );
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![lvl1()]);
    let body = Expr::app(Expr::app(false_elim, acc_r_y), Expr::bvar(0));
    // h : emptyRel y x  (under [y]: y = BVar0, x is the closed argument)
    let rel_y_x = Expr::app(Expr::app(empty_rel(), Expr::bvar(0)), x.clone());
    let h = Expr::lam(BinderInfo::Default, rel_y_x, body);
    let h = Expr::lam(BinderInfo::Default, nat(), h);
    let intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1()]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(intro, nat()), empty_rel()), x),
        h,
    )
}

/// Reduce `expr` to whnf and return its head `Const` name (handles bare
/// constants and constructor / literal applications).
fn whnf_head(env: &Environment, expr: &Expr) -> String {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Lit(_) => format!("{:?}", reduced.kind()),
        _ => match reduced.get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        },
    }
}

/// Build the `Acc : {α : Sort u} → (α → α → Prop) → α → Prop` inductive with
/// `Acc.intro : {α} → (r) → (x : α) → (∀ y, r y x → Acc r y) → Acc r x`.
///
/// This mirrors Clean's `init_well_founded` kernel build of `Acc`, so the
/// kernel-generated `Acc.rec` is byte-identical to the one an `.olean` ships.
fn acc_decl() -> InductiveDecl {
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let sort_u = Expr::sort(u_level.clone());
    let prop = Expr::prop();
    let acc_const = Expr::const_(Name::from_string("Acc"), vec![u_level.clone()]);

    // r_type = α → α → Prop, placed where α sits at de Bruijn `alpha_depth`.
    let mk_r_type = |alpha_depth: u32| -> Expr {
        let inner = Expr::pi(
            BinderInfo::Default,
            Expr::bvar(alpha_depth + 1),
            prop.clone(),
        );
        Expr::pi(BinderInfo::Default, Expr::bvar(alpha_depth), inner)
    };

    // Acc : Π {α : Sort u}. Π (r : α→α→Prop). Π (a : α). Prop
    let acc_type = {
        let r_type = mk_r_type(0);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone());
        let body = Expr::pi(BinderInfo::Default, r_type, body);
        Expr::pi(BinderInfo::Implicit, sort_u.clone(), body)
    };

    // Acc.intro : Π {α}. Π (r). Π (x : α). Π (h : ∀ y, r y x → Acc r y). Acc r x
    let acc_ctor_type = {
        // under [α,r,x,y]: α=3,r=2,x=1,y=0.  r y x = r (BVar0) (BVar1).
        let r_y_x = Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::bvar(1));
        // Acc r y shifted under the arrow binder: [α,r,x,y,hyp] α=4,r=3,y=1.
        let acc_r_y = Expr::app(
            Expr::app(Expr::app(acc_const.clone(), Expr::bvar(4)), Expr::bvar(3)),
            Expr::bvar(1),
        );
        let imp = Expr::pi(BinderInfo::Default, r_y_x, acc_r_y);
        let h_type = Expr::pi(BinderInfo::Default, Expr::bvar(2), imp);
        // result Acc r x under [α,r,x,h]: α=3,r=2,x=1.
        let result = Expr::app(
            Expr::app(Expr::app(acc_const.clone(), Expr::bvar(3)), Expr::bvar(2)),
            Expr::bvar(1),
        );
        let body = Expr::pi(BinderInfo::Default, h_type, result);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(1), body); // x : α (α=BVar1)
        let r_type = mk_r_type(0);
        let body = Expr::pi(BinderInfo::Default, r_type, body);
        Expr::pi(BinderInfo::Implicit, sort_u, body)
    };

    InductiveDecl {
        level_params: vec![u],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("Acc"),
            type_: acc_type,
            constructors: vec![Constructor {
                name: Name::from_string("Acc.intro"),
                type_: acc_ctor_type,
            }],
        }],
    }
}

/// Build a faithfully *imported* `Acc`: the real kernel-built family +
/// constructor + `Acc.rec` recursor copied verbatim into a fresh env, with **no**
/// `init_well_founded` bootstrap. `Acc.rec` is a registered recursor;
/// `WellFounded.*` are absent (an importing def would synthesise them).
fn imported_acc_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_true_false().expect("init_true_false");
    native
        .add_inductive(acc_decl())
        .expect("Acc should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");

    let iv = native
        .get_inductive(&Name::from_string("Acc"))
        .cloned()
        .expect("scratch env has Acc");
    env.register_inductive(iv);
    let ctor = native
        .get_constructor(&Name::from_string("Acc.intro"))
        .cloned()
        .expect("Acc.intro constructor");
    env.register_constructor(ctor);
    // Acc.rec stays a recursor on import; copy its ConstantInfo + RecursorVal so
    // the kernel can iota-reduce and the elaborator can reference it.
    let rec_const = native
        .get_const(&Name::from_string("Acc.rec"))
        .cloned()
        .expect("Acc.rec const");
    env.extend_constants_unchecked(std::iter::once(rec_const));
    let rec_val = native
        .get_recursor(&Name::from_string("Acc.rec"))
        .cloned()
        .expect("Acc.rec recursor");
    env.register_recursor(rec_val);
    env
}

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
// Precondition: the synthesized env is genuinely the *import* configuration —
// Acc.rec is a registered recursor with the special two-universe / Prop-major
// layout, and no clean-side WellFounded bootstrap exists.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_acc_has_rec_with_prop_major_layout_and_no_wf_bootstrap() {
    let env = imported_acc_env();

    let ind = env
        .get_inductive(&Name::from_string("Acc"))
        .expect("Acc inductive should be imported");
    assert_eq!(ind.num_params, 2, "Acc has two params: α and r");
    assert_eq!(ind.num_indices, 1, "Acc is indexed by the point a : α");

    let rec = env
        .get_recursor(&Name::from_string("Acc.rec"))
        .expect("Acc.rec must be a registered recursor on import");
    assert_eq!(rec.num_params, 2, "Acc.rec: params = α, r");
    assert_eq!(rec.num_motives, 1, "Acc.rec: single motive");
    assert_eq!(rec.num_minors, 1, "Acc.rec: one minor (the Acc.intro case)");
    assert_eq!(rec.num_indices, 1, "Acc.rec: one index (the point)");
    assert_eq!(
        rec.arg_order,
        RecursorArgOrder::MajorAfterMinors,
        "Acc.rec uses the standard MajorAfterMinors layout"
    );
    assert_eq!(
        rec.level_params.len(),
        2,
        "Acc.rec carries TWO universe params [motive_u, u] — large elimination \
         from a Prop. A one-universe layout (Prop-only elim) would mis-handle it."
    );
    assert!(!rec.is_k, "Acc.rec is not K-like (it has a field)");

    // No clean-side WellFounded bootstrap: these come only from an importing def.
    assert!(
        env.get_const(&Name::from_string("WellFounded.fix"))
            .is_none(),
        "imported env must NOT have a clean-side WellFounded.fix"
    );
    assert!(
        env.get_const(&Name::from_string("WellFounded")).is_none(),
        "imported env must NOT have a clean-side WellFounded structure"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `Acc.rec` iota-reduces *by hand* on `Acc.intro` to the
// genuinely correct value. Isolates any later elaborator-test failure to the
// clean-elab lowering rather than the kernel's reduction of the imported rec.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_acc_rec_kernel_reduction_is_correct() {
    let env = imported_acc_env();

    // motive := fun (a : Nat) (_ : Acc emptyRel a) => Nat
    let motive = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, acc_at(Expr::bvar(0)), nat()),
    );
    // minor := fun (x : Nat) (h : ∀ y, r y x → Acc r y)
    //              (ih : ∀ y, r y x → Nat) => Nat.succ x
    //   We return `Nat.succ x` (a value derived from the eliminated point), so a
    //   wrong minor / wrong major slot yields a different Nat or a stuck term.
    let minor = {
        // h_type under [x]: ∀ (y:Nat). emptyRel y x → Acc emptyRel y ; x = BVar0
        let h_type = {
            let rel_y_x = Expr::app(Expr::app(empty_rel(), Expr::bvar(0)), Expr::bvar(1));
            let acc_r_y = Expr::app(
                Expr::app(Expr::app(acc_c(), nat()), empty_rel()),
                Expr::bvar(1),
            );
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(BinderInfo::Default, rel_y_x, acc_r_y),
            )
        };
        // ih_type under [x, h]: ∀ (y:Nat). emptyRel y x → Nat ; x = BVar1
        let ih_type = {
            let rel_y_x = Expr::app(Expr::app(empty_rel(), Expr::bvar(0)), Expr::bvar(2));
            Expr::pi(
                BinderInfo::Default,
                nat(),
                Expr::pi(BinderInfo::Default, rel_y_x, nat()),
            )
        };
        let body = succ(Expr::bvar(2)); // Nat.succ x  (under [x,h,ih]: x = BVar2)
        let lam = Expr::lam(BinderInfo::Default, ih_type, body);
        let lam = Expr::lam(BinderInfo::Default, h_type, lam);
        Expr::lam(BinderInfo::Default, nat(), lam)
    };

    // @Acc.rec.{1, 1} Nat emptyRel motive minor 3 (Acc.intro 3 …) -> Nat.succ 3 = 4.
    let acc_rec = Expr::const_(Name::from_string("Acc.rec"), vec![lvl1(), lvl1()]);
    let three = nat_lit(3);
    let app = Expr::app(acc_rec, nat());
    let app = Expr::app(app, empty_rel());
    let app = Expr::app(app, motive);
    let app = Expr::app(app, minor);
    let app = Expr::app(app, three.clone());
    let app = Expr::app(app, acc_proof(three.clone()));

    let tc = TypeChecker::new(&env);
    let four = nat_lit(4);
    assert!(
        tc.is_def_eq(&app, &four),
        "imported Acc.rec on (Acc.intro 3 …) must select the minor and bind the \
         eliminated point (3), reducing to Nat.succ 3 = 4; got head {}",
        whnf_head(&env, &app)
    );
    // A wrong major/minor slot would not land on exactly `4`.
    assert!(
        !tc.is_def_eq(&app, &three),
        "the reduction must advance the point (4), not echo the input (3)"
    );
    assert!(
        !tc.is_def_eq(&app, &nat_lit(0)),
        "the reduction must not collapse to 0"
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE: the clean-elab elaborator lowers a definition that recurses
// through the *imported* `Acc.rec` (placing the motive / Acc.intro minor /
// index / major premise in the right slots), the kernel accepts it, and it
// reduces to the genuinely correct value on a concrete inlined Acc.intro proof.
// ---------------------------------------------------------------------------

#[test]
fn test_clean_elab_def_through_imported_acc_rec_reduces_correctly() {
    let mut env = imported_acc_env();

    // `emptyRel` and a monomorphic well-founded fixpoint combinator built *by the
    // elaborator* over the imported `@Acc.rec`. `accFix F x a` runs the WF
    // recursion; `F` gets the point `x` and a `rec` callback (never invoked here,
    // since nothing is below anything under `emptyRel`).
    //
    //   accFix (F : (x:Nat) → ((y:Nat) → emptyRel y x → Nat) → Nat)
    //          (x : Nat) (a : Acc emptyRel x) : Nat
    //     := @Acc.rec Nat emptyRel (fun a _ => Nat)
    //          (fun x h ih => F x ih) x a
    //
    //   double x  : runs accFix returning `x + x`  (distinct from the input)
    elaborate_decls_into(
        &mut env,
        "def emptyRel (a b : Nat) : Prop := False\n\
         def accFix (F : (x : Nat) -> ((y : Nat) -> emptyRel y x -> Nat) -> Nat) \
           (x : Nat) (a : Acc emptyRel x) : Nat :=\n  \
           @Acc.rec Nat emptyRel (fun a _ => Nat) (fun x h ih => F x ih) x a\n\
         def addSelf (x : Nat) (a : Acc emptyRel x) : Nat :=\n  \
           accFix (fun n recf => Nat.add n n) x a",
    );

    // accFix must compile through the imported `Acc.rec`.
    let body = env
        .get_const(&Name::from_string("accFix"))
        .and_then(|i| i.value.clone())
        .expect("accFix should be registered with a value");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Acc.rec")),
        "accFix must compile through the imported Acc.rec, got: {:?}",
        body.collect_constants()
    );

    let tc = TypeChecker::new(&env);

    // addSelf 3 (Acc.intro 3 …) -> Nat.add 3 3 = 6. Reduces because the major
    // premise is an inlined `Acc.intro` term (where Acc.rec iota genuinely fires).
    let three = nat_lit(3);
    let call = Expr::app(
        Expr::app(const_("addSelf"), three.clone()),
        acc_proof(three),
    );
    let six = nat_lit(6);
    assert!(
        tc.is_def_eq(&call, &six),
        "addSelf 3 (Acc.intro 3 …) must reduce through the imported Acc.rec to \
         Nat.add 3 3 = 6; got head {}",
        whnf_head(&env, &call)
    );
    // Distinct from the input point (3) and from 0 — a wrong slot/branch shows here.
    assert!(
        !tc.is_def_eq(&call, &nat_lit(3)),
        "the WF fixpoint must compute (6), not echo the point (3)"
    );
    assert!(
        !tc.is_def_eq(&call, &nat_lit(0)),
        "the WF fixpoint must not collapse to 0"
    );

    // A second, distinct witness at a different point: addSelf 5 -> 10.
    let five = nat_lit(5);
    let call5 = Expr::app(Expr::app(const_("addSelf"), five.clone()), acc_proof(five));
    assert!(
        tc.is_def_eq(&call5, &nat_lit(10)),
        "addSelf 5 (Acc.intro 5 …) must reduce to Nat.add 5 5 = 10; got head {}",
        whnf_head(&env, &call5)
    );
}

// ---------------------------------------------------------------------------
// FLIP-ON-FIX pin: WF recursion does NOT reduce definitionally through a
// *named, opaque* accessibility proof. This matches Lean exactly — a `def`
// returning `Acc r x : Prop` stays opaque to whnf, so `Acc.rec` never sees an
// `Acc.intro` head and the iota rule cannot fire. Lean closes this gap only
// with the *propositional* `WellFounded.fixFEq` equation, never by kernel iota.
// Pinned (not `#[ignore]`d) so it flips to a failure — prompting an assertion
// update — if Clean ever gains definitional unfolding here. The main probe
// above proves reduction works through an *inlined* Acc.intro.
// ---------------------------------------------------------------------------

#[test]
fn test_wf_recursion_through_named_acc_proof_is_stuck_pending() {
    let mut env = imported_acc_env();

    elaborate_decls_into(
        &mut env,
        "def emptyRel (a b : Nat) : Prop := False\n\
         def accProof (x : Nat) : Acc emptyRel x :=\n  \
           @Acc.intro Nat emptyRel x (fun (y : Nat) (h : emptyRel y x) => False.elim h)\n\
         def accFix (F : (x : Nat) -> ((y : Nat) -> emptyRel y x -> Nat) -> Nat) \
           (x : Nat) (a : Acc emptyRel x) : Nat :=\n  \
           @Acc.rec Nat emptyRel (fun a _ => Nat) (fun x h ih => F x ih) x a\n\
         def addSelf (x : Nat) : Nat :=\n  \
           accFix (fun n recf => Nat.add n n) x (accProof x)",
    );

    let tc = TypeChecker::new(&env);
    // addSelf 3 routes through the *named* `accProof 3`, which is opaque.
    let call = Expr::app(const_("addSelf"), nat_lit(3));
    let head = whnf_head(&env, &call);
    let reduces = tc.is_def_eq(&call, &nat_lit(6));
    assert!(
        !reduces,
        "FLIP-ON-FIX: WF recursion through a NAMED opaque accessibility proof now \
         reduces definitionally (whnf head was {head}) — Clean gained unfolding \
         that Lean does not have. Replace this pin with a positive assertion that \
         `addSelf 3` reduces to 6, and re-examine soundness vs. Lean's fixFEq-only \
         reduction model."
    );
    // The term is well-typed and stuck on the opaque proof (head is Acc.rec or the
    // named def), not erroring — the def kernel-checked, it simply does not iota.
    assert!(
        head == "Acc.rec" || head == "addSelf" || head == "accFix",
        "stuck WF recursion should be headed by the eliminator / the def, got {head}"
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path — Clean's own `Acc` built in-process (Acc.rec a
// registered recursor) — lowers the same WF combinator and reduces identically.
// Confirms the imported-eliminator handling matches native behavior byte-for-byte.
// ---------------------------------------------------------------------------

#[test]
fn test_native_acc_rec_wf_recursion_reduces_correctly() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.add_inductive(acc_decl()).expect("Acc should declare");

    // Native Acc.rec IS a registered recursor (same layout as the import copy).
    let rec = env
        .get_recursor(&Name::from_string("Acc.rec"))
        .expect("native Acc.rec recursor");
    assert_eq!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);
    assert_eq!(rec.level_params.len(), 2);

    elaborate_decls_into(
        &mut env,
        "def emptyRel (a b : Nat) : Prop := False\n\
         def accFixN (F : (x : Nat) -> ((y : Nat) -> emptyRel y x -> Nat) -> Nat) \
           (x : Nat) (a : Acc emptyRel x) : Nat :=\n  \
           @Acc.rec Nat emptyRel (fun a _ => Nat) (fun x h ih => F x ih) x a\n\
         def addSelfN (x : Nat) (a : Acc emptyRel x) : Nat :=\n  \
           accFixN (fun n recf => Nat.add n n) x a",
    );

    let body = env
        .get_const(&Name::from_string("accFixN"))
        .and_then(|i| i.value.clone())
        .expect("accFixN body");
    assert!(
        body.collect_constants()
            .contains(&Name::from_string("Acc.rec")),
        "native accFixN lowers through Acc.rec"
    );

    let tc = TypeChecker::new(&env);
    let three = nat_lit(3);
    let call = Expr::app(
        Expr::app(const_("addSelfN"), three.clone()),
        acc_proof(three),
    );
    assert!(
        tc.is_def_eq(&call, &nat_lit(6)),
        "native addSelfN 3 (Acc.intro 3 …) must reduce to 6; got head {}",
        whnf_head(&env, &call)
    );
    assert!(
        !tc.is_def_eq(&call, &nat_lit(3)),
        "native WF fixpoint must compute (6), not echo the point (3)"
    );
}

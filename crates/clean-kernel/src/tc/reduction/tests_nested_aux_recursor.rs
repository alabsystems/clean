// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction for nested-inductive *auxiliary* recursors (FAMILY A).
//!
//! Lean 4 transforms a nested inductive such as `Lean.Syntax` (whose `node`
//! constructor carries an `Array Syntax`) into a mutual block with auxiliary
//! types, and emits auxiliary recursors `Lean.Syntax.rec_1` / `rec_2` that
//! recurse over the container spine (`Array.mk` / `List.cons`). The kernel
//! `RecursorVal` for `rec_1` has its sole reduction rule keyed on the *container*
//! constructor `Array.mk`, but its declared "inductive" is `Lean.Syntax.rec_1`
//! itself — i.e. it does NOT equal `Array`.
//!
//! Lean's kernel selects the reduction rule purely by constructor *name*
//! (`get_rec_rule_for`); it never compares the constructor's parent inductive to
//! the recursor's inductive. clean previously gated iota on
//! `ctor.inductive_name == rec.inductive_name`, so these aux recursors stayed
//! stuck, which broke `Lean.Syntax.brecOn.go`, `…_sizeOf_2_eq`, etc. on import.
//!
//! These tests reproduce the stuck reduction minimally and pin the soundness
//! boundary: a recursor only reduces on a constructor it actually has a rule
//! for; an ill-typed application to an unrelated constructor stays stuck.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{
    Constructor, InductiveDecl, InductiveType, RecursorArgOrder, RecursorRule, RecursorVal,
};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Register `Box (A : Type) : Type` with `Box.mk : A → Box A`.
///
/// This is a faithful stand-in for the `Array`/`List` containers that the real
/// nested `Lean.Syntax` block recurses over: a single-parameter inductive whose
/// single constructor holds one field.
fn add_box(env: &mut Environment) {
    let box_name = Name::from_string("Box");
    // Box : Type → Type  (monomorphic, no level params — like the test helpers
    // in env/tests_nested_elim.rs use `Expr::type_()`).
    let box_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // Box.mk : (A : Type) → A → Box A    (A is the parameter)
    let box_a = Expr::app(
        Expr::const_(box_name.clone(), vec![]),
        Expr::bvar(1), // A, under the field binder
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),                                       // A : Type
        Expr::pi(BinderInfo::Default, Expr::bvar(0), box_a), // (_ : A) → Box A
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: box_name,
            type_: box_type,
            constructors: vec![Constructor {
                name: Name::from_string("Box.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("Box inductive should register");
}

/// Build the nested-aux recursor `T.rec_1` that mirrors `Lean.Syntax.rec_1`:
/// `inductive_name` is `T.rec_1` (NOT `Box`), one motive, one minor, and a single
/// rule keyed on `Box.mk` (the container constructor).
///
/// RHS lambda layout matches clean's iota application order
/// (`λ motives. λ minors. λ fields. body`); with one motive, one minor and one
/// field the body `BVar1 BVar0` is `minor field`.
fn aux_rec_val() -> RecursorVal {
    let u = Name::from_string("u");
    // body: minor (BVar1) applied to field (BVar0)
    let body = Expr::app(Expr::bvar(1), Expr::bvar(0));
    let unit = Expr::from_kind(ExprKind::Sort(Level::zero()));
    // λ (motive). λ (minor). λ (field). minor field
    let rhs = Expr::lam(
        BinderInfo::Default,
        unit.clone(),
        Expr::lam(
            BinderInfo::Default,
            unit.clone(),
            Expr::lam(BinderInfo::Default, unit.clone(), body),
        ),
    );
    RecursorVal {
        name: Name::from_string("T.rec_1"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![u],
        type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
        // NOTE: deliberately NOT `Box` — this is the nested-aux discrepancy.
        inductive_name: Name::from_string("T.rec_1"),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            constructor_name: Name::from_string("Box.mk"),
            num_fields: 1,
            recursive_fields: vec![false],
            rhs,
        }],
        is_k: false,
    }
}

/// The core fix: a nested-aux recursor whose rule is keyed on a *container*
/// constructor (`Box.mk`) whose parent inductive differs from the recursor's
/// `inductive_name` must still iota-reduce on a genuine `Box.mk` major premise.
#[test]
fn test_nested_aux_recursor_reduces_on_container_ctor() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    add_box(&mut env);
    env.register_recursor(aux_rec_val());
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    // major = Box.mk Nat Nat.zero  (params=[Nat], field=[Nat.zero])
    let major = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Box.mk"), vec![]),
            nat.clone(),
        ),
        n.clone(),
    );

    // We supply a `minor` that wraps its field in `Nat.succ`, so a successful
    // iota gives `Nat.succ Nat.zero`.
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let minor = succ.clone(); // minor field == Nat.succ field

    // T.rec_1 {0} motive minor major
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("T.rec_1"), vec![Level::zero()]),
                motive,
            ),
            minor,
        ),
        major,
    );

    let result = tc.whnf(&app);
    // Expect `Nat.succ Nat.zero`, which the kernel may further normalize to the
    // Nat literal `1`. EITHER form proves the recursor fired (it was stuck before
    // the fix, leaving head `T.rec_1`). A stuck result keeps head `T.rec_1`.
    let head = result.get_app_fn();
    let fired = match head.kind() {
        ExprKind::Const(name, _) => *name == Name::from_string("Nat.succ"),
        ExprKind::Lit(crate::expr::Literal::Nat(n)) => !n.is_zero(),
        _ => false,
    };
    assert!(
        fired,
        "nested-aux recursor should reduce `T.rec_1 .. (Box.mk Nat zero)` to \
         `Nat.succ Nat.zero` (or literal 1); got {result:?}"
    );
    // And it must NOT be stuck on the recursor head.
    if let ExprKind::Const(name, _) = head.kind() {
        assert_ne!(
            *name,
            Name::from_string("T.rec_1"),
            "nested-aux recursor stayed stuck — the fix did not fire"
        );
    }
}

/// ADVERSARIAL: the same nested-aux recursor must STAY STUCK when its major
/// premise is a constructor it has no rule for (`Nat.zero`). The fix selects the
/// rule by constructor name; `Nat.zero` matches no rule ⇒ no reduction. If this
/// ever reduced, the recursor would be applied to a value outside its domain.
#[test]
fn test_nested_aux_recursor_stuck_on_foreign_ctor() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    add_box(&mut env);
    env.register_recursor(aux_rec_val());
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let minor = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // Major premise is `Nat.zero` — NOT a `Box.mk`, so no rule matches.
    let major = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("T.rec_1"), vec![Level::zero()]),
                motive,
            ),
            minor,
        ),
        major,
    );

    let result = tc.whnf(&app);
    // Must stay an application headed by `T.rec_1` (stuck), NOT reduce.
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            *name,
            Name::from_string("T.rec_1"),
            "ill-typed nested-aux recursor application must stay stuck on a \
             foreign constructor, but it reduced (head={name})"
        ),
        other => panic!("expected stuck `T.rec_1 ..`, got {other:?}"),
    }
}

/// ADVERSARIAL: a *real* `Box.rec` (inductive_name == `Box`) applied to a
/// `Nat.zero` major premise must also stay stuck — confirming the by-name rule
/// selection in the aligned (fast-path) branch is equally safe. This guards
/// against the fix accidentally widening the aligned path.
#[test]
fn test_real_recursor_still_stuck_on_foreign_ctor() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    add_box(&mut env);
    let tc = TypeChecker::new(&env);

    // Box.rec exists (generated by add_inductive). Apply it to Nat.zero.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let box_rec = env
        .get_recursor(&Name::from_string("Box.rec"))
        .expect("Box.rec generated");
    let n_args = box_rec.num_params as usize
        + box_rec.num_motives as usize
        + box_rec.num_minors as usize
        + box_rec.num_indices as usize;
    // Use the recursor's actual declared level-param count so the only reason it
    // can stay stuck is the foreign constructor (not a level-count mismatch).
    let rec_levels: Vec<Level> = box_rec.level_params.iter().map(|_| Level::zero()).collect();

    // Build Box.rec with placeholder motive/params/minors then Nat.zero as major.
    let mut app = Expr::const_(Name::from_string("Box.rec"), rec_levels);
    // params (Box has 1: the element type A) — use Nat
    app = Expr::app(app, nat.clone());
    // motive — a dummy lambda; only structurally present, never evaluated since stuck
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(Expr::const_(Name::from_string("Box"), vec![]), nat.clone()),
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    app = Expr::app(app, motive);
    // remaining minors as placeholders (Nat.zero), then major Nat.zero
    let placeholders = n_args.saturating_sub(2); // already supplied param + motive
    for _ in 0..placeholders {
        app = Expr::app(app, zero.clone());
    }
    app = Expr::app(app, zero.clone()); // major = Nat.zero (foreign to Box)

    let result = tc.whnf(&app);
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            *name,
            Name::from_string("Box.rec"),
            "Box.rec must stay stuck on a foreign (non-Box) constructor, head={name}"
        ),
        other => panic!("expected stuck `Box.rec ..`, got {other:?}"),
    }
}

/// Sanity: the *aligned* path (recursor inductive == ctor inductive) still
/// reduces correctly — i.e. the fix did not break ordinary recursors.
#[test]
fn test_aligned_recursor_still_reduces() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );
    // major = Nat.succ Nat.zero
    let major = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        major,
    );
    let result = tc.whnf(&app);
    // succ_case returns its first argument (the predecessor) = zero. The kernel
    // represents `Nat.zero` either as the constructor or as the Nat literal 0.
    let head = result.get_app_fn();
    let is_zero = match head.kind() {
        ExprKind::Const(name, _) => *name == Name::from_string("Nat.zero"),
        ExprKind::Lit(crate::expr::Literal::Nat(n)) => n.is_zero(),
        _ => false,
    };
    assert!(
        is_zero,
        "Nat.rec on `succ zero` with `succ_case = λ n ih. n` should give zero, got {result:?}"
    );
}

// =========================================================================
// Struct-eta on a free major premise (getMajorInduct parity)
// =========================================================================

/// Struct-eta on a FREE (non-constructor) major premise via a nested-aux
/// recursor whose `inductive_name` differs from the major's inductive.
///
/// Mirrors `Trie._sizeOf_3_eq`: `Trie.rec_3` eliminates `Prod Key (Trie α)` —
/// its rule is keyed on the STRUCTURE's constructor while `inductive_name` is
/// the family head `Trie`. Lean keys `to_cnstr_when_structure` on the
/// recursor's MAJOR-premise inductive (`RecursorVal.getMajorInduct`,
/// inductive.h:60-73), so a free `h : Pair` eta-expands to `Pair.mk h.0 h.1`
/// and iota fires. clean previously keyed on `inductive_name`, leaving the
/// application stuck and failing the `_sizeOf_N_eq` lemmas of every
/// structure-nested inductive on import.
#[test]
fn test_nested_aux_recursor_struct_eta_on_free_major() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);

    // Pair : Type, Pair.mk : Nat → Nat → Pair — structure-like (one ctor,
    // no indices, not recursive), so eta expansion is admissible.
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::pi(BinderInfo::Default, nat.clone(), pair_ref.clone()),
                ),
            }],
        }],
    })
    .expect("Pair inductive should register");

    // h : Pair — the free (non-constructor) major premise.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: pair_ref.clone(),
    })
    .expect("axiom h : Pair should register");

    // Aux recursor T.rec_1: rule keyed on Pair.mk, `inductive_name` a foreign
    // family head "T". Unlike `aux_rec_val` above, `type_` carries the faithful
    // telescope (motive, minor, major : Pair) so `major_induct()` can read
    // `Pair` off the major-premise domain — that is precisely what the fix
    // consumes.
    let unit = Expr::from_kind(ExprKind::Sort(Level::zero()));
    // rhs: λ motive. λ minor. λ f1. λ f2. minor f1 f2
    let rhs = Expr::lam(
        BinderInfo::Default,
        unit.clone(),
        Expr::lam(
            BinderInfo::Default,
            unit.clone(),
            Expr::lam(
                BinderInfo::Default,
                unit.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    unit.clone(),
                    Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0)),
                ),
            ),
        ),
    );
    let rec_type = Expr::pi(
        BinderInfo::Default,
        unit.clone(), // motive slot (only the major domain matters here)
        Expr::pi(
            BinderInfo::Default,
            unit.clone(), // minor slot
            Expr::pi(BinderInfo::Default, pair_ref.clone(), unit.clone()),
        ),
    );
    env.register_recursor(RecursorVal {
        name: Name::from_string("T.rec_1"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![],
        type_: rec_type,
        inductive_name: Name::from_string("T"),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            constructor_name: Name::from_string("Pair.mk"),
            num_fields: 2,
            recursive_fields: vec![false, false],
            rhs,
        }],
        is_k: false,
    });
    let tc = TypeChecker::new(&env);

    // T.rec_1 motive minor h with minor = λ a b. a: after struct-eta
    // (h ↦ Pair.mk h.0 h.1) and iota, the whnf is the projection h.0.
    let motive = Expr::lam(BinderInfo::Default, pair_ref.clone(), nat.clone());
    let minor = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("T.rec_1"), vec![]), motive),
            minor,
        ),
        h,
    );

    let result = tc.whnf(&app);
    assert!(
        matches!(result.kind(), ExprKind::Proj(name, 0, _) if *name == pair_name),
        "aux recursor with a structure-typed major should struct-eta the free \
         major and iota-reduce `T.rec_1 motive (λ a b. a) h` to `h.0`; got {result:?}"
    );
}

/// `major_induct()` reads the major premise's inductive off the recursor type
/// for both argument orders, and degrades to `None` (caller falls back to
/// `inductive_name`) when the type is not a faithful telescope.
#[test]
fn test_recursor_major_induct_metadata() {
    let unit = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let pair_ref = Expr::const_(Name::from_string("Pair"), vec![]);
    let telescope = Expr::pi(
        BinderInfo::Default,
        unit.clone(),
        Expr::pi(
            BinderInfo::Default,
            unit.clone(),
            Expr::pi(BinderInfo::Default, pair_ref.clone(), unit.clone()),
        ),
    );
    let mut rec = aux_rec_val();
    rec.type_ = telescope;
    assert_eq!(
        rec.major_induct(),
        Some(&Name::from_string("Pair")),
        "MajorAfterMinors: major domain head should be Pair"
    );

    // recOn order: params → motives → indices → major → minors. With one
    // motive and one minor, the major is the SECOND binder.
    let telescope_recon = Expr::pi(
        BinderInfo::Default,
        unit.clone(),
        Expr::pi(
            BinderInfo::Default,
            pair_ref.clone(),
            Expr::pi(BinderInfo::Default, unit.clone(), unit.clone()),
        ),
    );
    let mut rec_on = aux_rec_val();
    rec_on.arg_order = RecursorArgOrder::MajorAfterMotive;
    rec_on.type_ = telescope_recon;
    assert_eq!(
        rec_on.major_induct(),
        Some(&Name::from_string("Pair")),
        "MajorAfterMotive: major domain head should be Pair"
    );

    // Degenerate type (the `aux_rec_val` default is a bare Sort): no telescope
    // to read, so None — the reduction path then falls back to
    // `inductive_name`, i.e. exactly the pre-fix behavior.
    assert_eq!(
        aux_rec_val().major_induct(),
        None,
        "non-Pi recursor type should yield None"
    );
}

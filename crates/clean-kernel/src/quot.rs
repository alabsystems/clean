// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quotient Types
//!
//! Lean's quotient types allow construction of types modulo an equivalence relation.
//! This module implements the four quotient primitives:
//!
//! - `Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u` - The quotient type
//! - `Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : @Quot.{u} α r` - Constructor
//! - `Quot.lift.{u v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
//!     (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β` - Eliminator
//! - `Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop} :
//!     (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q` - Induction
//!
//! The key computation rule (iota/quot reduction):
//! `Quot.lift f h (Quot.mk r a) ≡ f a`
//!
//! This means when `lift` is applied to a `mk`, we can reduce directly to the function
//! application, discarding the proof obligation.
//!
//! References:
//! - Lean 4 kernel: src/kernel/quot.cpp
//! - lean4lean: Lean4Lean/Quot.lean

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use serde::{Deserialize, Serialize};

/// Well-known quotient type names.
pub mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    /// The `Quot` type constructor name.
    pub static QUOT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Quot"));
    /// The `Quot.mk` constructor name.
    pub static QUOT_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Quot.mk"));
    /// The `Quot.lift` eliminator name.
    pub static QUOT_LIFT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Quot.lift"));
    /// The `Quot.ind` induction principle name.
    pub static QUOT_IND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Quot.ind"));
    pub static QUOT_SOUND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Quot.sound"));
}

/// Information about a quotient primitive
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuotVal {
    /// Name of the quotient primitive
    pub name: Name,
    /// Universe parameters
    pub level_params: Vec<Name>,
    /// Type of the primitive
    pub type_: Expr,
    /// Which quotient primitive this is
    pub kind: QuotKind,
}

/// The kind of quotient primitive
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum QuotKind {
    /// Quot - the quotient type former
    Type,
    /// Quot.mk - the constructor
    Mk,
    /// Quot.lift - the eliminator/recursor
    Lift,
    /// Quot.ind - induction principle
    Ind,
    /// Quot.sound - quotient soundness axiom
    Sound,
}

impl QuotKind {
    /// Get the name for this quotient kind
    pub fn name(&self) -> Name {
        match self {
            QuotKind::Type => names::QUOT.clone(),
            QuotKind::Mk => names::QUOT_MK.clone(),
            QuotKind::Lift => names::QUOT_LIFT.clone(),
            QuotKind::Ind => names::QUOT_IND.clone(),
            QuotKind::Sound => names::QUOT_SOUND.clone(),
        }
    }
}

/// Build the type of `Quot`:
/// `Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u`
///
/// # Contract
///
/// REQUIRES: `u` is a valid universe parameter name
/// ENSURES: Returns the type of the Quot type former (an axiom)
/// ENSURES: Result is `{α : Sort u} → (α → α → Prop) → Sort u`
pub(crate) fn quot_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    // {α : Sort u}
    let alpha = Expr::bvar(0);
    // r : α → α → Prop
    let r_type = Expr::pi(
        BinderInfo::Default,
        alpha.clone(),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
    );
    // The result type: Sort u
    let result = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // Build: {α : Sort u} → (r : α → α → Prop) → Sort u
    Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::pi(BinderInfo::Default, r_type, result),
    )
}

/// Build the type of `Quot.mk`:
/// `Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot.{u} α r`
///
/// # Contract
///
/// REQUIRES: `u` is a valid universe parameter name
/// ENSURES: Returns the type of the Quot.mk constructor (an axiom)
/// ENSURES: Result is `{α : Sort u} → (r : α → α → Prop) → α → @Quot α r`
pub fn quot_mk_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // α is BVar 2 after binding α, r, a
    // r is BVar 1 after binding α, r, a
    // a is BVar 0 after binding α, r, a

    // r : α → α → Prop (α is BVar 0 at this point)
    let r_type = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // α
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
    );

    // Build @Quot.{u} α r where α is BVar 2, r is BVar 1
    let quot_app = Expr::app(
        Expr::app(
            Expr::const_(names::QUOT.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(2), // α
        ),
        Expr::bvar(1), // r
    );

    // Build: {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot.{u} α r
    Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::pi(
            BinderInfo::Default,
            r_type,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : α (α is now BVar 1)
                quot_app,
            ),
        ),
    )
}

/// Build the type of `Quot.lift`:
/// `Quot.lift.{u v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
///   (f : α → β) → (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β`
///
/// # Contract
///
/// REQUIRES: `u` and `v` are valid universe parameter names
/// ENSURES: Returns the type of the Quot.lift eliminator (an axiom)
/// ENSURES: Lift allows computing from Quot to any Sort v, given proof f respects r
pub fn quot_lift_type(u: &Name, v: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));

    // r : α → α → Prop (α is BVar 0 at this point)
    let r_type = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // α
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
    );

    // After binding α, r, β: α is BVar 2, r is BVar 1, β is BVar 0
    // f : α → β
    let f_type = Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(1));

    // Build the proof obligation type:
    // ∀ a b : α, r a b → f a = f b
    // After binding α, r, β, f: α is BVar 3, r is BVar 2, β is BVar 1, f is BVar 0
    // In the proof type, we bind a, b internally
    let proof_type = build_lift_proof_type(Level::param(v.clone()));

    // @Quot.{u} α r
    // After all bindings: α is BVar 4, r is BVar 3
    let quot_type_app = Expr::app(
        Expr::app(
            Expr::const_(names::QUOT.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4), // α
        ),
        Expr::bvar(3), // r
    );

    // Result type: β. The result is the *body* of the final `(q : Quot α r)`
    // Pi, so the context is α, r, β, f, proof, q (six binders); β is the third
    // from the outside, i.e. BVar 3 from the inside (NOT BVar 2 — that is f).
    // SOUNDNESS: corrects a latent off-by-one that gave `Quot.lift` the result
    // type `f` (the lifting function) instead of the codomain `β`. As with the
    // respect-obligation fix above, this only makes the eliminator's type
    // *correct*; the previous index produced an ill-typed result for any lift
    // and so could not have been relied upon by a sound proof. Surfaced by the
    // faithful `Multiset.cons` quotient lift.
    let result = Expr::bvar(3);

    // Build the full type with all binders
    Expr::pi(
        BinderInfo::Implicit,
        sort_u, // α : Sort u
        Expr::pi(
            BinderInfo::Implicit,
            r_type, // r : α → α → Prop
            Expr::pi(
                BinderInfo::Implicit,
                sort_v, // β : Sort v
                Expr::pi(
                    BinderInfo::Default,
                    f_type, // f : α → β
                    Expr::pi(
                        BinderInfo::Default,
                        proof_type, // proof : ∀ a b, r a b → f a = f b
                        Expr::pi(
                            BinderInfo::Default,
                            quot_type_app, // q : @Quot α r
                            result,        // β
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Build the proof obligation type for Quot.lift:
/// `∀ a b : α, r a b → @Eq.{v} β (f a) (f b)`
/// At the point this is used: α is BVar 3, r is BVar 2, β is BVar 1, f is BVar 0
fn build_lift_proof_type(level_v: Level) -> Expr {
    // α at BVar 3
    let alpha = Expr::bvar(3);
    // r at BVar 2 (used in the body after binding)
    let _r = Expr::bvar(2);
    // f at BVar 0 (used in the body after binding)
    let _f = Expr::bvar(0);

    // After binding a, b: a is BVar 1, b is BVar 0
    // α becomes BVar 5, r becomes BVar 4, f becomes BVar 2
    // r a b (application)
    let r_a_b = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(1)), Expr::bvar(0));

    // f a, f b (applications)
    // f becomes BVar 3 after binding a, b, h
    let f_a = Expr::app(Expr::bvar(3), Expr::bvar(2)); // in the body after binding h
    let f_b = Expr::app(Expr::bvar(3), Expr::bvar(1)); // after binding h

    // f a = f b (using Eq)
    // In Lean: @Eq.{v} β (f a) (f b).
    // At proof-type entry the context (innermost-first) is f=#0, β=#1, r=#2,
    // α=#3 (see the doc comment above). After binding a, b, h the β reference
    // shifts up by 3, so β is BVar 4 here (NOT BVar 5 — that is r).
    // SOUNDNESS: this corrects a latent off-by-one that pointed the lifted
    // equality's type at `r` instead of the codomain `β`. The previous index
    // made `Quot.lift`'s respect-obligation demand `@Eq r (f a) (f b)`, which
    // is ill-typed unless `β` is definitionally `r`, so no proof could ever
    // satisfy it except in that degenerate case; correcting it to `β` only
    // *enables* legitimate lifts and never accepts a previously-rejected
    // unsound term. Surfaced by the faithful `Multiset.cons` quotient lift.
    let eq_type = make_eq_type(level_v, Expr::bvar(4), f_a, f_b);

    // Build: ∀ a b : α, r a b → f a = f b
    // Note: α is BVar 3 -> becomes BVar 4 after binding a -> becomes BVar 5 after binding b
    Expr::pi(
        BinderInfo::Default,
        alpha.clone(), // a : α
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(4), // b : α (α shifted by 1)
            Expr::pi(
                BinderInfo::Default,
                r_a_b,   // h : r a b
                eq_type, // f a = f b
            ),
        ),
    )
}

/// Build @Eq.{v} β a b
/// This creates the type for equality of two terms in type β : Sort v
fn make_eq_type(level_v: Level, beta: Expr, a: Expr, b: Expr) -> Expr {
    // Construct @Eq.{v} β a b
    // Eq.{u} : {alpha : Sort u} -> alpha -> alpha -> Prop
    // The universe parameter must match the sort of beta
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![level_v]), beta),
            a,
        ),
        b,
    )
}

/// Build the type of `Quot.ind`:
/// `Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} →
///   {β : @Quot.{u} α r → Prop} →
///   (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q`
///
/// # Contract
///
/// REQUIRES: `u` is a valid universe parameter name
/// ENSURES: Returns the type of the Quot.ind induction principle (an axiom)
/// ENSURES: Allows proving propositions about Quot by proving them for Quot.mk
pub fn quot_ind_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // r : α → α → Prop
    let r_type = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
    );

    // @Quot.{u} α r (after binding α, r)
    // α is BVar 1, r is BVar 0
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(names::QUOT.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    // β : @Quot.{u} α r → Prop (after binding α, r)
    // When used later, shifts accordingly
    let beta_type = Expr::pi(BinderInfo::Default, quot_alpha_r.clone(), Expr::prop());

    // Build the induction hypothesis type:
    // ∀ a : α, β (@Quot.mk.{u} α r a)
    // After binding α, r, β: α is BVar 2, r is BVar 1, β is BVar 0
    let ih_type = build_ind_hyp_type(u);

    // @Quot.{u} α r for the final argument
    // After binding α, r, β, h: α is BVar 3, r is BVar 2
    let quot_final = Expr::app(
        Expr::app(
            Expr::const_(names::QUOT.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(3),
        ),
        Expr::bvar(2),
    );

    // β q. This is the body of the final `(q : Quot α r)` Pi, so the context
    // is α, r, β, h, q (five binders); β is the third from the outside, i.e.
    // BVar 2 from the inside (NOT BVar 1 — that is the hypothesis `h`), and q
    // is BVar 0.
    // SOUNDNESS: corrects a latent off-by-one that gave `Quot.ind` the result
    // type `h q` (the induction hypothesis applied) instead of the motive
    // `β q`. As with the `Quot.lift` fixes, the previous index made the
    // eliminator's result type ill-formed for any genuine use, so no sound
    // proof could have depended on it. Surfaced by `Multiset.mem_cons_self`.
    let beta_q = Expr::app(Expr::bvar(2), Expr::bvar(0));

    // Build the full type
    Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::pi(
            BinderInfo::Implicit,
            r_type,
            Expr::pi(
                BinderInfo::Implicit,
                beta_type,
                Expr::pi(
                    BinderInfo::Default,
                    ih_type,
                    Expr::pi(BinderInfo::Default, quot_final, beta_q),
                ),
            ),
        ),
    )
}

/// Build the induction hypothesis type:
/// `∀ a : α, β (@Quot.mk.{u} α r a)`
/// At the point this is used: α is BVar 2, r is BVar 1, β is BVar 0
fn build_ind_hyp_type(u: &Name) -> Expr {
    // α is BVar 2
    let alpha = Expr::bvar(2);

    // After binding a: α is BVar 3, r is BVar 2, β is BVar 1, a is BVar 0
    // @Quot.mk.{u} α r a
    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(names::QUOT_MK.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(3), // α
            ),
            Expr::bvar(2), // r
        ),
        Expr::bvar(0), // a
    );

    // β (@Quot.mk α r a) where β is BVar 1 after binding a
    let beta_mk_a = Expr::app(Expr::bvar(1), mk_a);

    // ∀ a : α, β (@Quot.mk α r a)
    Expr::pi(BinderInfo::Default, alpha, beta_mk_a)
}

/// Build the type of `Quot.sound`:
/// `Quot.sound.{u} : {α : Sort u} → {r : α → α → Prop} → {a b : α} → r a b → Quot.mk.{u} α r a = Quot.mk.{u} α r b`
pub fn quot_sound_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // r : α → α → Prop
    let r_type = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
    );

    // a : α
    let a_type = Expr::bvar(1);

    // b : α
    let b_type = Expr::bvar(2);

    // h : r a b
    let h_type = Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0));

    // Return type: Eq.{u} (Quot.{u} α r) (Quot.mk.{u} α r a) (Quot.mk.{u} α r b)
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(names::QUOT.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4), // α
        ),
        Expr::bvar(3), // r
    );

    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(names::QUOT_MK.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4), // α
            ),
            Expr::bvar(3), // r
        ),
        Expr::bvar(2), // a
    );

    let mk_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(names::QUOT_MK.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4), // α
            ),
            Expr::bvar(3), // r
        ),
        Expr::bvar(1), // b
    );

    let eq_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]),
                quot_alpha_r,
            ),
            mk_a,
        ),
        mk_b,
    );

    Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::pi(
            BinderInfo::Implicit,
            r_type,
            Expr::pi(
                BinderInfo::Implicit,
                a_type,
                Expr::pi(
                    BinderInfo::Implicit,
                    b_type,
                    Expr::pi(BinderInfo::Default, h_type, eq_app),
                ),
            ),
        ),
    )
}

/// Initialize the quotient types in an environment
/// Returns the five QuotVal primitives to be added
///
/// # Contract
///
/// ENSURES: Returns exactly 5 QuotVal entries: Quot, Quot.mk, Quot.lift, Quot.ind, Quot.sound
/// ENSURES: Each entry has correct universe parameters and types
/// ENSURES: Types match the Lean 4 kernel's quotient axioms
pub fn init_quot_vals() -> Vec<QuotVal> {
    let u = Name::from_string("u");
    let v = Name::from_string("v");

    vec![
        QuotVal {
            name: names::QUOT.clone(),
            level_params: vec![u.clone()],
            type_: quot_type(&u),
            kind: QuotKind::Type,
        },
        QuotVal {
            name: names::QUOT_MK.clone(),
            level_params: vec![u.clone()],
            type_: quot_mk_type(&u),
            kind: QuotKind::Mk,
        },
        QuotVal {
            name: names::QUOT_LIFT.clone(),
            level_params: vec![u.clone(), v.clone()],
            type_: quot_lift_type(&u, &v),
            kind: QuotKind::Lift,
        },
        QuotVal {
            name: names::QUOT_IND.clone(),
            level_params: vec![u.clone()],
            type_: quot_ind_type(&u),
            kind: QuotKind::Ind,
        },
        QuotVal {
            name: names::QUOT_SOUND.clone(),
            level_params: vec![u.clone()],
            type_: quot_sound_type(&u),
            kind: QuotKind::Sound,
        },
    ]
}

/// Check if a name is a quotient primitive
///
/// # Contract
///
/// REQUIRES: `name` is a valid Name
/// ENSURES: Returns true iff `name` is Quot, Quot.mk, Quot.lift, or Quot.ind
pub fn is_quot_name(name: &Name) -> bool {
    *name == *names::QUOT
        || *name == *names::QUOT_MK
        || *name == *names::QUOT_LIFT
        || *name == *names::QUOT_IND
        || *name == *names::QUOT_SOUND
}

/// Get the QuotKind for a name, if it's a quotient primitive
///
/// # Contract
///
/// REQUIRES: `name` is a valid Name
/// ENSURES: Returns Some(kind) if `name` is a quotient primitive
/// ENSURES: Returns None if `name` is not a quotient primitive
pub fn get_quot_kind(name: &Name) -> Option<QuotKind> {
    if *name == *names::QUOT {
        Some(QuotKind::Type)
    } else if *name == *names::QUOT_MK {
        Some(QuotKind::Mk)
    } else if *name == *names::QUOT_LIFT {
        Some(QuotKind::Lift)
    } else if *name == *names::QUOT_IND {
        Some(QuotKind::Ind)
    } else if *name == *names::QUOT_SOUND {
        Some(QuotKind::Sound)
    } else {
        None
    }
}

/// Try to reduce a Quot.lift application
///
/// The reduction rule is:
/// `Quot.lift.{u v} α r β f h (Quot.mk.{u} α r a) ≡ f a`
///
/// Returns Some(reduced) if the expression can be reduced, None otherwise.
///
/// # Contract
///
/// REQUIRES: `fn_head` is the head of an application
/// REQUIRES: `args` are the arguments to the application
/// REQUIRES: `whnf` computes weak head normal form
/// ENSURES: Returns Some(f a) if fn_head is Quot.lift and 6th arg is Quot.mk a
/// ENSURES: Returns None if conditions for reduction are not met
/// ENSURES: Implements the iota/quot computation rule (soundness-critical)
pub fn try_quot_lift_reduction(
    fn_head: &Expr,
    args: &[&Expr],
    whnf: impl Fn(&Expr) -> Expr,
) -> Option<Expr> {
    // Check if the head is Quot.lift
    if let ExprKind::Const(name, _levels) = &fn_head.kind {
        if *name != *names::QUOT_LIFT {
            return None;
        }
    } else {
        return None;
    }

    // Quot.lift has 6 arguments: α, r, β, f, h, q
    // The 6th argument (q) should be Quot.mk applied to something
    if args.len() < 6 {
        return None;
    }

    // Get the major premise (the quotient value)
    let major = args[5];
    let major_whnf = whnf(major);

    // Check if major is Quot.mk applied to arguments
    // Check head before collecting args for efficiency on non-Quot.mk cases
    let major_head = major_whnf.get_app_fn();

    let ExprKind::Const(name, _) = &major_head.kind else {
        return None;
    };
    if *name != *names::QUOT_MK {
        return None;
    }

    // Now collect args (only after confirming head is Quot.mk)
    let major_args = major_whnf.get_app_args();

    // Quot.mk has 3 arguments: α, r, a
    if major_args.len() < 3 {
        return None;
    }

    // The value being quoted
    let a = major_args[2];

    // f is args[3]
    let f = args[3];

    // Result: f a (extra_args...)
    // Lean 4 quot.h:66-68: apply extra arguments after the major premise.
    // For Quot.lift, elim_arity = 6 (α, r, β, f, h, q). Args beyond index 5
    // are trailing args that must be applied to the result.
    let mut result = Expr::app(f.clone(), a.clone());
    let elim_arity = 6;
    for extra in args.iter().skip(elim_arity) {
        result = Expr::app(result, (*extra).clone());
    }
    Some(result)
}

/// Try to reduce a Quot.ind application
///
/// The reduction rule is:
/// `Quot.ind.{u} α r β f (Quot.mk.{u} α r a) ≡ f a`
///
/// Quot.ind has 5 arguments: α, r, β, f, q
/// When q reduces (via whnf) to `Quot.mk α r a`, the result is `f a`.
///
/// Returns Some(reduced) if the expression can be reduced, None otherwise.
///
/// # Contract
///
/// REQUIRES: `fn_head` is the head of an application
/// REQUIRES: `args` are the arguments to the application
/// REQUIRES: `whnf` computes weak head normal form
/// ENSURES: Returns Some(f a) if fn_head is Quot.ind and 5th arg is Quot.mk a
/// ENSURES: Returns None if conditions for reduction are not met
/// ENSURES: Implements the iota/quot computation rule (soundness-critical)
///
/// Reference: Lean 4 kernel quot.h:52-68 `quot_reduce_rec`
pub fn try_quot_ind_reduction(
    fn_head: &Expr,
    args: &[&Expr],
    whnf: impl Fn(&Expr) -> Expr,
) -> Option<Expr> {
    // Check if the head is Quot.ind
    if let ExprKind::Const(name, _levels) = &fn_head.kind {
        if *name != *names::QUOT_IND {
            return None;
        }
    } else {
        return None;
    }

    // Quot.ind has 5 arguments: α, r, β, f, q
    // The 5th argument (q) should be Quot.mk applied to something
    if args.len() < 5 {
        return None;
    }

    // Get the major premise (the quotient value)
    let major = args[4];
    let major_whnf = whnf(major);

    // Check if major is Quot.mk applied to arguments
    // Check head before collecting args for efficiency on non-Quot.mk cases
    let major_head = major_whnf.get_app_fn();

    let ExprKind::Const(name, _) = &major_head.kind else {
        return None;
    };
    if *name != *names::QUOT_MK {
        return None;
    }

    // Now collect args (only after confirming head is Quot.mk)
    let major_args = major_whnf.get_app_args();

    // Quot.mk has 3 arguments: α, r, a
    if major_args.len() < 3 {
        return None;
    }

    // The value being quoted
    let a = major_args[2];

    // f is args[3]
    let f = args[3];

    // Result: f a (extra_args...)
    // Lean 4 quot.h:66-68: apply extra arguments after the major premise.
    // For Quot.ind, elim_arity = 5 (α, r, β, f, q). Args beyond index 4
    // are trailing args that must be applied to the result.
    let mut result = Expr::app(f.clone(), a.clone());
    let elim_arity = 5;
    for extra in args.iter().skip(elim_arity) {
        result = Expr::app(result, (*extra).clone());
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quot_names() {
        assert_eq!(names::QUOT.to_string(), "Quot");
        assert_eq!(names::QUOT_MK.to_string(), "Quot.mk");
        assert_eq!(names::QUOT_LIFT.to_string(), "Quot.lift");
        assert_eq!(names::QUOT_IND.to_string(), "Quot.ind");
    }

    #[test]
    fn test_is_quot_name() {
        assert!(is_quot_name(&Name::from_string("Quot")));
        assert!(is_quot_name(&Name::from_string("Quot.mk")));
        assert!(is_quot_name(&Name::from_string("Quot.lift")));
        assert!(is_quot_name(&Name::from_string("Quot.ind")));
        assert!(is_quot_name(&Name::from_string("Quot.sound")));
        assert!(!is_quot_name(&Name::from_string("Nat")));
        assert!(!is_quot_name(&Name::from_string("List")));
    }

    #[test]
    fn test_get_quot_kind() {
        assert_eq!(
            get_quot_kind(&Name::from_string("Quot")),
            Some(QuotKind::Type)
        );
        assert_eq!(
            get_quot_kind(&Name::from_string("Quot.mk")),
            Some(QuotKind::Mk)
        );
        assert_eq!(
            get_quot_kind(&Name::from_string("Quot.lift")),
            Some(QuotKind::Lift)
        );
        assert_eq!(
            get_quot_kind(&Name::from_string("Quot.ind")),
            Some(QuotKind::Ind)
        );
        assert_eq!(
            get_quot_kind(&Name::from_string("Quot.sound")),
            Some(QuotKind::Sound)
        );
        assert_eq!(get_quot_kind(&Name::from_string("Nat")), None);
    }

    #[test]
    fn test_quot_type_structure() {
        let u = Name::from_string("u");
        let typ = quot_type(&u);

        // Should be a Pi type
        match &typ.kind {
            ExprKind::Pi(bi, _, _) => {
                // First binder should be implicit (α)
                assert_eq!(bi.info, BinderInfo::Implicit);
            }
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_quot_mk_type_structure() {
        let u = Name::from_string("u");
        let typ = quot_mk_type(&u);

        // Should be a Pi type
        match &typ.kind {
            ExprKind::Pi(bi, _, _) => {
                // First binder should be implicit (α)
                assert_eq!(bi.info, BinderInfo::Implicit);
            }
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_init_quot_vals() {
        let vals = init_quot_vals();
        assert_eq!(vals.len(), 5);

        // Check all five primitives are present
        let names: Vec<&Name> = vals.iter().map(|v| &v.name).collect();
        assert!(names.iter().any(|n| n.to_string() == "Quot"));
        assert!(names.iter().any(|n| n.to_string() == "Quot.mk"));
        assert!(names.iter().any(|n| n.to_string() == "Quot.lift"));
        assert!(names.iter().any(|n| n.to_string() == "Quot.ind"));
        assert!(names.iter().any(|n| n.to_string() == "Quot.sound"));

        // Check kinds
        for val in &vals {
            match &val.kind {
                QuotKind::Type => assert_eq!(val.name.to_string(), "Quot"),
                QuotKind::Mk => assert_eq!(val.name.to_string(), "Quot.mk"),
                QuotKind::Lift => assert_eq!(val.name.to_string(), "Quot.lift"),
                QuotKind::Ind => assert_eq!(val.name.to_string(), "Quot.ind"),
                QuotKind::Sound => assert_eq!(val.name.to_string(), "Quot.sound"),
            }
        }
    }

    #[test]
    fn test_quot_lift_reduction_not_lift() {
        // Test that non-Quot.lift heads return None
        let head = Expr::const_(Name::from_string("Nat"), vec![]);
        let args: Vec<&Expr> = vec![];
        let result = try_quot_lift_reduction(&head, &args, Expr::clone);
        assert!(
            result.is_none(),
            "non-Quot.lift head should return None, got {result:?}"
        );
    }

    #[test]
    fn test_quot_lift_reduction_insufficient_args() {
        // Test that Quot.lift with insufficient args returns None
        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![Level::zero()]);
        let arg1 = Expr::prop();
        let args: Vec<&Expr> = vec![&arg1]; // Only 1 arg, need 6
        let result = try_quot_lift_reduction(&head, &args, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.lift with insufficient args should return None, got {result:?}"
        );
    }

    #[test]
    fn test_quot_lift_reduction_success() {
        // Build a reducible expression: Quot.lift α r β f h (Quot.mk α r a)
        // This should reduce to: f a

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));

        // Dummy values for α, r, β
        let alpha = Expr::type_();
        let r = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        );
        let beta = Expr::type_();

        // f : α → β (identity function for simplicity)
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

        // h : proof (dummy)
        let h = Expr::prop();

        // a : α (some value)
        let a = Expr::const_(Name::from_string("x"), vec![]);

        // Build Quot.mk α r a
        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        // Build the head and args for Quot.lift
        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u, v]);
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &mk_app];

        // The reduction should give us f a
        let reduced = try_quot_lift_reduction(&head, &args, Expr::clone)
            .expect("Quot.lift reduction should succeed with all args");
        // Check it's f applied to a
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                // func should be f (the lambda)
                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                // arg should be a
                assert_eq!(arg.as_ref(), &a);
            }
            _ => panic!("Expected App, got {reduced:?}"),
        }
    }

    // =========================================================================
    // Mutation Testing Kill Tests - quot.rs survivors
    // =========================================================================

    #[test]
    fn test_quot_lift_reduction_args_boundary() {
        // Kill mutant: replace < with > in try_quot_lift_reduction (line 462)
        // The check is: if args.len() < 6 { return None; }
        // With exactly 5 args, should return None. With 6+, should potentially work.

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));
        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u, v]);

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::prop();
        let h = Expr::prop();

        // Exactly 5 args - should NOT reduce (less than 6)
        let args_5: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h];
        let result_5 = try_quot_lift_reduction(&head, &args_5, Expr::clone);
        assert!(result_5.is_none(), "5 args < 6, should return None");

        // Exactly 6 args but last is NOT Quot.mk - should not reduce
        let not_mk = Expr::type_();
        let args_6: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &not_mk];
        let result_6 = try_quot_lift_reduction(&head, &args_6, Expr::clone);
        assert!(
            result_6.is_none(),
            "6 args but no Quot.mk, should return None"
        );

        // For completeness, 4 args should also return None
        let args_4: Vec<&Expr> = vec![&alpha, &r, &beta, &f];
        let result_4 = try_quot_lift_reduction(&head, &args_4, Expr::clone);
        assert!(result_4.is_none(), "4 args < 6, should return None");
    }

    #[test]
    fn test_quot_lift_reduction_major_args_boundary() {
        // Kill mutant at line 462: replace < with > in `major_args.len() < 3`
        // This checks if Quot.mk has enough arguments (needs 3: α, r, a)

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));
        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u.clone(), v]);

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f_func = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let h = Expr::prop();

        // Build Quot.mk with ONLY 2 arguments (not enough - needs 3)
        // Quot.mk α r (missing the value 'a')
        let mk_partial = Expr::app(
            Expr::app(
                Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                alpha.clone(),
            ),
            r.clone(),
        );

        // Call with 6 outer args where major (6th) is Quot.mk with only 2 inner args
        let args_with_partial_mk: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &h, &mk_partial];
        let result = try_quot_lift_reduction(&head, &args_with_partial_mk, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.mk with only 2 args (< 3), should return None"
        );

        // Now with exactly 3 args for Quot.mk (should work)
        let a_value = Expr::const_(Name::from_string("x"), vec![]);
        let mk_complete = Expr::app(mk_partial.clone(), a_value.clone());

        let args_with_complete_mk: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &h, &mk_complete];
        let result = try_quot_lift_reduction(&head, &args_with_complete_mk, Expr::clone);
        assert!(
            result.is_some(),
            "Quot.mk with exactly 3 args (>= 3), should reduce"
        );

        // Verify the result is f a
        let reduced = result.unwrap();
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                assert!(
                    matches!(&func.as_ref().kind, ExprKind::Lam(..)),
                    "Result function should be the lambda f"
                );
                assert_eq!(arg.as_ref(), &a_value, "Result arg should be a");
            }
            _ => panic!("Expected App"),
        }

        // Edge case: Quot.mk with exactly 1 arg
        let mk_1arg = Expr::app(
            Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
            alpha.clone(),
        );
        let args_1arg: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &h, &mk_1arg];
        let result = try_quot_lift_reduction(&head, &args_1arg, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.mk with 1 arg (< 3), should return None"
        );

        // Edge case: Quot.mk with 0 args (just the constant)
        let mk_0arg = Expr::const_(names::QUOT_MK.clone(), vec![u]);
        let args_0arg: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &h, &mk_0arg];
        let result = try_quot_lift_reduction(&head, &args_0arg, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.mk with 0 args (< 3), should return None"
        );
    }

    // =========================================================================
    // Tests for quot_lift_type and quot_ind_type type structures
    // =========================================================================

    #[test]
    fn test_quot_lift_type_structure() {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let typ = quot_lift_type(&u, &v);

        // quot_lift_type has 6 binders:
        // {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
        //   (f : α → β) → (h : ∀ a b, r a b → f a = f b) → (@Quot α r → β)

        // Count the nested Pi types (should be 6 total binders)
        fn count_pis(e: &Expr) -> usize {
            match &e.kind {
                ExprKind::Pi(_, _, body) => 1 + count_pis(body),
                _ => 0,
            }
        }

        assert_eq!(
            count_pis(&typ),
            6,
            "quot_lift_type should have 6 Pi binders"
        );

        // Verify first 3 binders are implicit
        match &typ.kind {
            ExprKind::Pi(bi1, _, body1) => {
                assert_eq!(
                    bi1.info,
                    BinderInfo::Implicit,
                    "First binder (α) should be implicit"
                );
                match &body1.as_ref().kind {
                    ExprKind::Pi(bi2, _, body2) => {
                        assert_eq!(
                            bi2.info,
                            BinderInfo::Implicit,
                            "Second binder (r) should be implicit"
                        );
                        match &body2.as_ref().kind {
                            ExprKind::Pi(bi3, _, body3) => {
                                assert_eq!(
                                    bi3.info,
                                    BinderInfo::Implicit,
                                    "Third binder (β) should be implicit"
                                );
                                // Next 3 should be explicit
                                match &body3.as_ref().kind {
                                    ExprKind::Pi(bi4, _, body4) => {
                                        assert_eq!(
                                            bi4.info,
                                            BinderInfo::Default,
                                            "Fourth binder (f) should be explicit"
                                        );
                                        match &body4.as_ref().kind {
                                            ExprKind::Pi(bi5, _, body5) => {
                                                assert_eq!(
                                                    bi5.info,
                                                    BinderInfo::Default,
                                                    "Fifth binder (h) should be explicit"
                                                );
                                                match &body5.as_ref().kind {
                                                    ExprKind::Pi(bi6, _, _) => {
                                                        assert_eq!(
                                                            bi6.info,
                                                            BinderInfo::Default,
                                                            "Sixth binder (q) should be explicit"
                                                        );
                                                    }
                                                    _ => panic!("Expected 6th Pi"),
                                                }
                                            }
                                            _ => panic!("Expected 5th Pi"),
                                        }
                                    }
                                    _ => panic!("Expected 4th Pi"),
                                }
                            }
                            _ => panic!("Expected 3rd Pi"),
                        }
                    }
                    _ => panic!("Expected 2nd Pi"),
                }
            }
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_quot_ind_type_structure() {
        let u = Name::from_string("u");
        let typ = quot_ind_type(&u);

        // quot_ind_type has 4 binders:
        // {α : Sort u} → {r : α → α → Prop} →
        //   {β : @Quot α r → Prop} →
        //   (ih : ∀ a : α, β (Quot.mk α r a)) → ∀ q : @Quot α r, β q

        fn count_pis(e: &Expr) -> usize {
            match &e.kind {
                ExprKind::Pi(_, _, body) => 1 + count_pis(body),
                _ => 0,
            }
        }

        assert_eq!(count_pis(&typ), 5, "quot_ind_type should have 5 Pi binders");

        // Verify first 3 binders are implicit
        match &typ.kind {
            ExprKind::Pi(bi1, _, body1) => {
                assert_eq!(
                    bi1.info,
                    BinderInfo::Implicit,
                    "First binder (α) should be implicit"
                );
                match &body1.as_ref().kind {
                    ExprKind::Pi(bi2, _, body2) => {
                        assert_eq!(
                            bi2.info,
                            BinderInfo::Implicit,
                            "Second binder (r) should be implicit"
                        );
                        match &body2.as_ref().kind {
                            ExprKind::Pi(bi3, _, body3) => {
                                assert_eq!(
                                    bi3.info,
                                    BinderInfo::Implicit,
                                    "Third binder (β) should be implicit"
                                );
                                // Next 2 should be explicit
                                match &body3.as_ref().kind {
                                    ExprKind::Pi(bi4, _, body4) => {
                                        assert_eq!(
                                            bi4.info,
                                            BinderInfo::Default,
                                            "Fourth binder (ih) should be explicit"
                                        );
                                        match &body4.as_ref().kind {
                                            ExprKind::Pi(bi5, _, _) => {
                                                assert_eq!(
                                                    bi5.info,
                                                    BinderInfo::Default,
                                                    "Fifth binder (q) should be explicit"
                                                );
                                            }
                                            _ => panic!("Expected 5th Pi"),
                                        }
                                    }
                                    _ => panic!("Expected 4th Pi"),
                                }
                            }
                            _ => panic!("Expected 3rd Pi"),
                        }
                    }
                    _ => panic!("Expected 2nd Pi"),
                }
            }
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_quot_type_has_correct_universe_params() {
        let u = Name::from_string("u");
        let typ = quot_type(&u);

        // The first binder's type should be Sort(u)
        match &typ.kind {
            ExprKind::Pi(_, domain, _) => {
                assert!(
                    matches!(&domain.as_ref().kind, ExprKind::Sort(l) if matches!(l, Level::Param(_))),
                    "First binder domain should be Sort(u)"
                );
            }
            _ => panic!("Expected Pi type"),
        }
    }

    #[test]
    fn test_quot_mk_type_returns_quot_type() {
        let u = Name::from_string("u");
        let typ = quot_mk_type(&u);

        // Navigate to the innermost return type
        fn get_return_type(e: &Expr) -> &Expr {
            match &e.kind {
                ExprKind::Pi(_, _, body) => get_return_type(body),
                _ => e,
            }
        }

        let ret = get_return_type(&typ);

        // Return type should be @Quot α r which is App(App(Const(...), ...), ...)
        assert!(
            matches!(&ret.kind, ExprKind::App(_, _)),
            "Return type of Quot.mk should be an application (Quot α r)"
        );
    }

    #[test]
    fn test_quot_lift_returns_correct_type() {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let typ = quot_lift_type(&u, &v);

        fn get_return_type(e: &Expr) -> &Expr {
            match &e.kind {
                ExprKind::Pi(_, _, body) => get_return_type(body),
                _ => e,
            }
        }

        let ret = get_return_type(&typ);

        // Return type should be β (a BVar referring to the third binder)
        assert!(
            matches!(&ret.kind, ExprKind::BVar(_)),
            "Return type of Quot.lift should be a bound variable (β)"
        );
    }

    #[test]
    fn test_quot_ind_returns_correct_type() {
        let u = Name::from_string("u");
        let typ = quot_ind_type(&u);

        fn get_return_type(e: &Expr) -> &Expr {
            match &e.kind {
                ExprKind::Pi(_, _, body) => get_return_type(body),
                _ => e,
            }
        }

        let ret = get_return_type(&typ);

        // Return type should be (β q) which is App(β, q)
        assert!(
            matches!(&ret.kind, ExprKind::App(_, _)),
            "Return type of Quot.ind should be an application (β q)"
        );
    }

    #[test]
    fn test_quot_kind_name_mapping() {
        // Verify that QuotKind::name() returns the correct name for each variant
        assert_eq!(QuotKind::Type.name().to_string(), "Quot");
        assert_eq!(QuotKind::Mk.name().to_string(), "Quot.mk");
        assert_eq!(QuotKind::Lift.name().to_string(), "Quot.lift");
        assert_eq!(QuotKind::Ind.name().to_string(), "Quot.ind");
        assert_eq!(QuotKind::Sound.name().to_string(), "Quot.sound");
    }

    #[test]
    fn test_init_quot_vals_level_params() {
        let vals = init_quot_vals();

        for val in &vals {
            match &val.kind {
                QuotKind::Type | QuotKind::Mk | QuotKind::Ind | QuotKind::Sound => {
                    // These have 1 universe parameter (u)
                    assert_eq!(
                        val.level_params.len(),
                        1,
                        "{:?} should have 1 level param",
                        val.kind
                    );
                }
                QuotKind::Lift => {
                    // Lift has 2 universe parameters (u, v)
                    assert_eq!(val.level_params.len(), 2, "Lift should have 2 level params");
                }
            }
        }
    }

    // =========================================================================
    // Issue #1028: Edge case tests for quotient lift reduction
    // =========================================================================

    #[test]
    fn test_quot_lift_reduction_whnf_reveals_quot_mk() {
        // Test that WHNF is actually called to expose Quot.mk under a let-binding
        // This tests the key semantic case: the major premise isn't immediately
        // Quot.mk, but becomes so after WHNF.

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let h = Expr::prop();
        let a = Expr::const_(Name::from_string("a_val"), vec![]);

        // Build the actual Quot.mk application
        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        // Wrap it in a let binding: let x = Quot.mk α r a in x
        // This simulates a non-reduced form that requires WHNF
        let let_wrapped = Expr::from_kind(ExprKind::Let(
            Name::anon(),
            Expr::type_().into(),  // type annotation
            mk_app.clone().into(), // value = Quot.mk ...
            Expr::bvar(0).into(),  // body = x (refers to the let-bound value)
            false,
        ));

        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u.clone(), v.clone()]);
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &let_wrapped];

        // With identity WHNF (no reduction), should fail because major isn't Quot.mk
        let result_no_whnf = try_quot_lift_reduction(&head, &args, Expr::clone);
        assert!(
            result_no_whnf.is_none(),
            "Without real WHNF, let-wrapped Quot.mk should not reduce"
        );

        // With a WHNF that unwraps let bindings, should succeed
        let whnf_unwrap_let = |e: &Expr| -> Expr {
            match &e.kind {
                ExprKind::Let(_, _ty, val, body, _) => {
                    // Simple let unwrapping: substitute val for BVar(0) in body
                    if matches!(&body.as_ref().kind, ExprKind::BVar(0)) {
                        val.as_ref().clone()
                    } else {
                        e.clone()
                    }
                }
                _ => e.clone(),
            }
        };

        let result_with_whnf = try_quot_lift_reduction(&head, &args, whnf_unwrap_let);
        assert!(
            result_with_whnf.is_some(),
            "With WHNF that unwraps let, should reduce"
        );

        // Verify result is f a
        let reduced = result_with_whnf.unwrap();
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                assert_eq!(arg.as_ref(), &a);
            }
            _ => panic!("Expected App(f, a)"),
        }
    }

    #[test]
    fn test_quot_lift_reduction_universe_levels_preserved() {
        // Verify that universe level parameters on Quot.lift don't affect reduction
        // and that the result is correctly formed regardless of universe choice

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let h = Expr::prop();
        let a = Expr::const_(Name::from_string("test_val"), vec![]);

        // Test with different universe level combinations
        let universe_pairs = vec![
            (Level::zero(), Level::zero()),              // u=0, v=0
            (Level::succ(Level::zero()), Level::zero()), // u=1, v=0
            (Level::zero(), Level::succ(Level::zero())), // u=0, v=1
            (
                Level::param(Name::from_string("u")),
                Level::param(Name::from_string("v")),
            ), // parametric
        ];

        for (u, v) in universe_pairs {
            let mk_app = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                        alpha.clone(),
                    ),
                    r.clone(),
                ),
                a.clone(),
            );

            let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u.clone(), v.clone()]);
            let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &mk_app];

            let result = try_quot_lift_reduction(&head, &args, Expr::clone);
            assert!(
                result.is_some(),
                "Reduction should succeed for u={u:?}, v={v:?}"
            );

            // Result should always be f a, regardless of universe levels
            let reduced = result.unwrap();
            match &reduced.kind {
                ExprKind::App(func, arg) => {
                    assert!(
                        matches!(&func.as_ref().kind, ExprKind::Lam(..)),
                        "Function should be lambda for u={u:?}, v={v:?}"
                    );
                    assert_eq!(
                        arg.as_ref(),
                        &a,
                        "Argument should be 'a' for u={u:?}, v={v:?}"
                    );
                }
                _ => panic!("Expected App for u={u:?}, v={v:?}"),
            }
        }
    }

    #[test]
    fn test_quot_lift_reduction_proof_irrelevance() {
        // The proof argument h should be irrelevant - different proofs should
        // produce the same result (this is the computational content of proof
        // irrelevance for quotients)

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let a = Expr::const_(Name::from_string("test_val"), vec![]);

        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        // Try different "proofs" for h - they should all produce the same result
        let proof_variants = vec![
            Expr::prop(),                                                // Prop as dummy proof
            Expr::const_(Name::from_string("refl"), vec![]),             // Named proof constant
            Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)), // Lambda proof
            Expr::app(
                // Applied proof
                Expr::const_(Name::from_string("eq_proof"), vec![]),
                Expr::prop(),
            ),
        ];

        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u, v]);
        let mut results = Vec::new();

        for h in &proof_variants {
            let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, h, &mk_app];
            let result = try_quot_lift_reduction(&head, &args, Expr::clone);
            assert!(
                result.is_some(),
                "Reduction should succeed for all proof variants"
            );
            results.push(result.unwrap());
        }

        // All results should be structurally identical (f a)
        // The proof h is not part of the computational content
        let first = &results[0];
        for (i, result) in results.iter().enumerate().skip(1) {
            assert_eq!(
                first, result,
                "Result with proof variant {i} should match first result"
            );
        }

        // Additionally verify the result structure
        match &first.kind {
            ExprKind::App(func, arg) => {
                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                assert_eq!(arg.as_ref(), &a);
            }
            _ => panic!("Expected App(f, a)"),
        }
    }

    #[test]
    fn test_quot_lift_reduction_non_const_head_rejected() {
        // Verify that non-Const expressions as head are rejected early
        // This tests the initial match arm in try_quot_lift_reduction

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::prop();
        let h = Expr::prop();
        let q = Expr::prop();
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &q];

        // Lambda as head (not Const)
        let lam_head = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        assert!(
            try_quot_lift_reduction(&lam_head, &args, Expr::clone).is_none(),
            "Lambda head should be rejected"
        );

        // App as head
        let app_head = Expr::app(Expr::type_(), Expr::prop());
        assert!(
            try_quot_lift_reduction(&app_head, &args, Expr::clone).is_none(),
            "App head should be rejected"
        );

        // FVar as head
        let fvar_head = Expr::fvar(crate::FVarId(42));
        assert!(
            try_quot_lift_reduction(&fvar_head, &args, Expr::clone).is_none(),
            "FVar head should be rejected"
        );

        // BVar as head
        let bvar_head = Expr::bvar(0);
        assert!(
            try_quot_lift_reduction(&bvar_head, &args, Expr::clone).is_none(),
            "BVar head should be rejected"
        );
    }

    #[test]
    fn test_quot_lift_major_premise_non_const_whnf() {
        // Test case where WHNF of major premise is not a Const
        // (e.g., it's a variable, lambda, or application that doesn't reduce to Quot.mk)

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let h = Expr::prop();

        let head = Expr::const_(names::QUOT_LIFT.clone(), vec![u, v]);

        // Major premise that reduces to a lambda (not Quot.mk)
        let major_lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let args_lam: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &major_lam];
        assert!(
            try_quot_lift_reduction(&head, &args_lam, Expr::clone).is_none(),
            "Lambda major premise should not reduce"
        );

        // Major premise that reduces to an FVar
        let major_fvar = Expr::fvar(crate::FVarId(100));
        let args_fvar: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &major_fvar];
        assert!(
            try_quot_lift_reduction(&head, &args_fvar, Expr::clone).is_none(),
            "FVar major premise should not reduce"
        );

        // Major premise that's a Const but not Quot.mk
        let major_other = Expr::const_(Name::from_string("List.nil"), vec![]);
        let args_other: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &h, &major_other];
        assert!(
            try_quot_lift_reduction(&head, &args_other, Expr::clone).is_none(),
            "Non-Quot.mk Const should not reduce"
        );
    }

    /// Regression test for #2171: Quot.lift proof obligation must use @Eq.{v}, not @Eq.{}
    #[test]
    fn test_quot_lift_eq_has_universe_level() {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let typ = quot_lift_type(&u, &v);

        // Navigate to the 5th binder (the proof obligation type):
        // {α} → {r} → {β} → (f) → (h : ∀ a b, r a b → @Eq.{v} β (f a) (f b)) → ...
        fn find_eq_levels(e: &Expr) -> Option<usize> {
            match &e.kind {
                ExprKind::Const(name, levels) if name.to_string() == "Eq" => Some(levels.len()),
                ExprKind::App(f, a) => find_eq_levels(f).or_else(|| find_eq_levels(a)),
                ExprKind::Pi(_, dom, body) => find_eq_levels(dom).or_else(|| find_eq_levels(body)),
                _ => None,
            }
        }

        let eq_level_count = find_eq_levels(&typ).expect("Quot.lift type should contain Eq");
        assert_eq!(
            eq_level_count, 1,
            "Eq should have exactly 1 universe level, got {eq_level_count}"
        );
    }

    // =========================================================================
    // Tests for try_quot_ind_reduction (#3227)
    // =========================================================================

    #[test]
    fn test_quot_ind_reduction_not_ind() {
        // Test that non-Quot.ind heads return None
        let head = Expr::const_(Name::from_string("Nat"), vec![]);
        let args: Vec<&Expr> = vec![];
        let result = try_quot_ind_reduction(&head, &args, Expr::clone);
        assert!(
            result.is_none(),
            "non-Quot.ind head should return None, got {result:?}"
        );
    }

    #[test]
    fn test_quot_ind_reduction_insufficient_args() {
        // Test that Quot.ind with insufficient args returns None
        let head = Expr::const_(names::QUOT_IND.clone(), vec![Level::zero()]);
        let arg1 = Expr::prop();
        let args: Vec<&Expr> = vec![&arg1]; // Only 1 arg, need 5
        let result = try_quot_ind_reduction(&head, &args, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.ind with insufficient args should return None, got {result:?}"
        );
    }

    #[test]
    fn test_quot_ind_reduction_success() {
        // Build a reducible expression: Quot.ind α r β f (Quot.mk α r a)
        // This should reduce to: f a

        let u = Level::param(Name::from_string("u"));

        // Dummy values for α, r, β
        let alpha = Expr::type_();
        let r = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        );
        let beta = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::prop());

        // f : ∀ a : α, β (Quot.mk α r a) — simplified to identity-like for testing
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

        // a : α (some value)
        let a = Expr::const_(Name::from_string("x"), vec![]);

        // Build Quot.mk α r a
        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        // Build the head and args for Quot.ind
        let head = Expr::const_(names::QUOT_IND.clone(), vec![u]);
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &mk_app];

        // The reduction should give us f a
        let reduced = try_quot_ind_reduction(&head, &args, Expr::clone)
            .expect("Quot.ind reduction should succeed with all args");
        // Check it's f applied to a
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                // func should be f (the lambda)
                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                // arg should be a
                assert_eq!(arg.as_ref(), &a);
            }
            _ => panic!("Expected App, got {reduced:?}"),
        }
    }

    #[test]
    fn test_quot_ind_reduction_args_boundary() {
        // Kill mutant: replace < with > in try_quot_ind_reduction
        // The check is: if args.len() < 5 { return None; }

        let u = Level::param(Name::from_string("u"));
        let head = Expr::const_(names::QUOT_IND.clone(), vec![u]);

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::prop();
        let f = Expr::prop();

        // Exactly 4 args - should NOT reduce (less than 5)
        let args_4: Vec<&Expr> = vec![&alpha, &r, &beta, &f];
        let result_4 = try_quot_ind_reduction(&head, &args_4, Expr::clone);
        assert!(result_4.is_none(), "4 args < 5, should return None");

        // Exactly 5 args but last is NOT Quot.mk - should not reduce
        let not_mk = Expr::type_();
        let args_5: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &not_mk];
        let result_5 = try_quot_ind_reduction(&head, &args_5, Expr::clone);
        assert!(
            result_5.is_none(),
            "5 args but no Quot.mk, should return None"
        );

        // For completeness, 3 args should also return None
        let args_3: Vec<&Expr> = vec![&alpha, &r, &beta];
        let result_3 = try_quot_ind_reduction(&head, &args_3, Expr::clone);
        assert!(result_3.is_none(), "3 args < 5, should return None");
    }

    #[test]
    fn test_quot_ind_reduction_major_args_boundary() {
        // Check that Quot.mk with insufficient inner args returns None

        let u = Level::param(Name::from_string("u"));
        let head = Expr::const_(names::QUOT_IND.clone(), vec![u.clone()]);

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::prop();
        let f_func = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

        // Build Quot.mk with ONLY 2 arguments (not enough - needs 3)
        let mk_partial = Expr::app(
            Expr::app(
                Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                alpha.clone(),
            ),
            r.clone(),
        );

        let args_partial: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &mk_partial];
        let result = try_quot_ind_reduction(&head, &args_partial, Expr::clone);
        assert!(
            result.is_none(),
            "Quot.mk with only 2 args (< 3), should return None"
        );

        // With exactly 3 args for Quot.mk (should work)
        let a_value = Expr::const_(Name::from_string("x"), vec![]);
        let mk_complete = Expr::app(mk_partial, a_value.clone());

        let args_complete: Vec<&Expr> = vec![&alpha, &r, &beta, &f_func, &mk_complete];
        let result = try_quot_ind_reduction(&head, &args_complete, Expr::clone);
        assert!(
            result.is_some(),
            "Quot.mk with exactly 3 args (>= 3), should reduce"
        );

        // Verify the result is f a
        let reduced = result.unwrap();
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                assert!(
                    matches!(&func.as_ref().kind, ExprKind::Lam(..)),
                    "Result function should be the lambda f"
                );
                assert_eq!(arg.as_ref(), &a_value, "Result arg should be a");
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_quot_ind_reduction_non_const_head_rejected() {
        // Verify that non-Const expressions as head are rejected early

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::prop();
        let q = Expr::prop();
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &q];

        // Lambda as head (not Const)
        let lam_head = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        assert!(
            try_quot_ind_reduction(&lam_head, &args, Expr::clone).is_none(),
            "Lambda head should be rejected"
        );

        // App as head
        let app_head = Expr::app(Expr::type_(), Expr::prop());
        assert!(
            try_quot_ind_reduction(&app_head, &args, Expr::clone).is_none(),
            "App head should be rejected"
        );

        // FVar as head
        let fvar_head = Expr::fvar(crate::FVarId(42));
        assert!(
            try_quot_ind_reduction(&fvar_head, &args, Expr::clone).is_none(),
            "FVar head should be rejected"
        );
    }

    #[test]
    fn test_quot_ind_reduction_whnf_reveals_quot_mk() {
        // Test that WHNF is called to expose Quot.mk under a let-binding

        let u = Level::param(Name::from_string("u"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::prop();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let a = Expr::const_(Name::from_string("a_val"), vec![]);

        // Build the actual Quot.mk application
        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        // Wrap it in a let binding: let x = Quot.mk α r a in x
        let let_wrapped = Expr::from_kind(ExprKind::Let(
            Name::anon(),
            Expr::type_().into(),
            mk_app.clone().into(),
            Expr::bvar(0).into(),
            false,
        ));

        let head = Expr::const_(names::QUOT_IND.clone(), vec![u]);
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &let_wrapped];

        // With identity WHNF (no reduction), should fail
        let result_no_whnf = try_quot_ind_reduction(&head, &args, Expr::clone);
        assert!(
            result_no_whnf.is_none(),
            "Without real WHNF, let-wrapped Quot.mk should not reduce"
        );

        // With a WHNF that unwraps let bindings, should succeed
        let whnf_unwrap_let = |e: &Expr| -> Expr {
            match &e.kind {
                ExprKind::Let(_, _ty, val, body, _) => {
                    if matches!(&body.as_ref().kind, ExprKind::BVar(0)) {
                        val.as_ref().clone()
                    } else {
                        e.clone()
                    }
                }
                _ => e.clone(),
            }
        };

        let result_with_whnf = try_quot_ind_reduction(&head, &args, whnf_unwrap_let);
        assert!(
            result_with_whnf.is_some(),
            "With WHNF that unwraps let, should reduce"
        );

        let reduced = result_with_whnf.unwrap();
        match &reduced.kind {
            ExprKind::App(func, arg) => {
                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                assert_eq!(arg.as_ref(), &a);
            }
            _ => panic!("Expected App(f, a)"),
        }
    }

    #[test]
    fn test_quot_ind_reduction_trailing_args() {
        // Verify that trailing arguments beyond elim_arity=5 are applied to the result

        let u = Level::param(Name::from_string("u"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::prop();
        let f = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let a = Expr::const_(Name::from_string("x"), vec![]);

        let mk_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(names::QUOT_MK.clone(), vec![u.clone()]),
                    alpha.clone(),
                ),
                r.clone(),
            ),
            a.clone(),
        );

        let extra1 = Expr::const_(Name::from_string("extra1"), vec![]);
        let extra2 = Expr::const_(Name::from_string("extra2"), vec![]);

        let head = Expr::const_(names::QUOT_IND.clone(), vec![u]);
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &mk_app, &extra1, &extra2];

        let reduced = try_quot_ind_reduction(&head, &args, Expr::clone)
            .expect("Quot.ind reduction with trailing args should succeed");

        // Result should be ((f a) extra1) extra2
        // Outermost App: ((f a) extra1) applied to extra2
        match &reduced.kind {
            ExprKind::App(inner, arg) => {
                assert_eq!(arg.as_ref(), &extra2, "Outermost arg should be extra2");
                // inner should be (f a) extra1
                match &inner.as_ref().kind {
                    ExprKind::App(inner2, arg2) => {
                        assert_eq!(arg2.as_ref(), &extra1, "Second arg should be extra1");
                        // inner2 should be f a
                        match &inner2.as_ref().kind {
                            ExprKind::App(func, val) => {
                                assert!(matches!(&func.as_ref().kind, ExprKind::Lam(..)));
                                assert_eq!(val.as_ref(), &a);
                            }
                            _ => panic!("Expected App(f, a) at innermost level"),
                        }
                    }
                    _ => panic!("Expected App((f a), extra1)"),
                }
            }
            _ => panic!("Expected App with trailing args"),
        }
    }

    #[test]
    fn test_quot_ind_reduction_quot_lift_head_rejected() {
        // Verify that Quot.lift head is rejected by try_quot_ind_reduction

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));

        let alpha = Expr::type_();
        let r = Expr::prop();
        let beta = Expr::type_();
        let f = Expr::prop();
        let q = Expr::prop();
        let args: Vec<&Expr> = vec![&alpha, &r, &beta, &f, &q];

        let lift_head = Expr::const_(names::QUOT_LIFT.clone(), vec![u, v]);
        assert!(
            try_quot_ind_reduction(&lift_head, &args, Expr::clone).is_none(),
            "Quot.lift head should be rejected by try_quot_ind_reduction"
        );
    }
}

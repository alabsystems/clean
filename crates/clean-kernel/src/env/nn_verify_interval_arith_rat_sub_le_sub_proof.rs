// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof term for `Rat.sub_le_sub` (#3539).
//!
//! Promotes `Rat.sub_le_sub` from `Declaration::Axiom` to a genuine
//! `Declaration::Theorem` with a lambda proof term. Unlocks the
//! downstream `NNVerify.IntervalArith.interval_sub_contains` (T02) native
//! save path once the parent register site is flipped to use this proof.
//!
//! # Statement
//!
//! ```text
//! Rat.sub_le_sub : ∀ (a b c d : Rat), a ≤ b → d ≤ c → a - c ≤ b - d
//! ```
//!
//! # Proof strategy
//!
//! Given `h1 : a ≤ b` and `h2 : d ≤ c`:
//!
//! 1. Build `h_neg : Rat.neg c ≤ Rat.neg d` via
//!    `Rat.neg_le_neg d c h2`.
//!    (`Rat.neg_le_neg : ∀ x y, x ≤ y → Rat.neg y ≤ Rat.neg x`, so
//!    instantiating at `x = d, y = c` with `h2 : d ≤ c` gives
//!    `Rat.neg c ≤ Rat.neg d`.)
//! 2. Apply
//!    `Rat.add_le_add a b (Rat.neg c) (Rat.neg d) h1 h_neg`
//!    to obtain `Rat.add a (Rat.neg c) ≤ Rat.add b (Rat.neg d)`.
//! 3. By delta on the reducible `Rat.sub` definition
//!    (`Rat.sub x y := Rat.add x (Rat.neg y)`), this is exactly the
//!    target conclusion `Rat.sub a c ≤ Rat.sub b d`.
//!
//! # Axiom closure
//!
//! This proof term introduces **no new domain axioms**. Its transitive
//! dependency set is exactly the union of the already kernel-validated
//! closures of `Rat.add_le_add` and `Rat.neg_le_neg` — both of which
//! were promoted to `Declaration::Theorem` in #3537 and #3538,
//! respectively.
//!
//! Foundational (`FOUNDATIONAL_AXIOMS`):
//! * `Rat.add_le_add_left` (transitively via both siblings)
//! * `Rat.le_trans` (transitively via `Rat.add_le_add`)
//! * `Eq.subst`, `Eq.refl`, `Eq.symm`, `Eq.trans`, `congrArg`
//!
//! Rat field/order axioms (non-foundational but honest — the same
//! closure as the sibling theorems):
//! * `Rat.add_comm`        (via `Rat.add_le_add`)
//! * `Rat.add_left_neg`, `Rat.add_neg_self` (via `Rat.neg_le_neg`)
//! * `Rat.add_zero`, `Rat.zero_add`         (via `Rat.neg_le_neg`)
//! * `Rat.add_assoc`, `Rat.add_right_cancel` (via `Rat.neg_le_neg`)
//!
//! Because the two siblings already transitively depend on the full
//! Rat ordered-field axiom set, this proof term is **strictly
//! conservative** with respect to the domain-axiom footprint: no
//! new axiom names are introduced.
//!
//! Per design doc Proof Soundness Rules, the ordered-field axioms are
//! **not** foundational. Hence the commit that flips the register
//! site uses the verb "Formalize" (not "Prove"), and the downstream
//! `interval_sub_contains` (T02) remains `AxiomDependent` in the
//! clean-native save pipeline until `FOUNDATIONAL_AXIOMS` is
//! expanded to include the Rat ordered-field axioms.
//!
//! Part of #3539 (T02 unlock); companions #3537 (`Rat.add_le_add`)
//! and #3538 (`Rat.neg_le_neg`).

use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Build `LE.le.{0} @Rat @instLERat lhs rhs`.
fn rat_le(rat: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
    let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
    Expr::apps(le_le, [rat.clone(), inst, lhs, rhs])
}

/// Build `Rat.neg a`.
fn rat_neg(a: Expr) -> Expr {
    let neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    Expr::app(neg, a)
}

/// Build the constructive proof term for `Rat.sub_le_sub`:
/// `∀ (a b c d : Rat), a ≤ b → d ≤ c → a - c ≤ b - d`.
///
/// Shape:
/// ```text
/// fun (a b c d : Rat) (h1 : a ≤ b) (h2 : d ≤ c) =>
///   Rat.add_le_add a b (Rat.neg c) (Rat.neg d) h1 (Rat.neg_le_neg d c h2)
/// ```
pub(super) fn build_rat_sub_le_sub_proof() -> Expr {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(rat.clone());
    let (bv_id, bv) = b.fresh_local(rat.clone());
    let (cv_id, cv) = b.fresh_local(rat.clone());
    let (dv_id, dv) = b.fresh_local(rat.clone());

    // h1 : a ≤ b
    let h1_ty = rat_le(&rat, a.clone(), bv.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    // h2 : d ≤ c
    let h2_ty = rat_le(&rat, dv.clone(), cv.clone());
    let (h2_id, h2) = b.fresh_local(h2_ty.clone());

    // h_neg : Rat.neg c ≤ Rat.neg d  via  Rat.neg_le_neg d c h2
    let neg_le_neg = Expr::const_(Name::from_string("Rat.neg_le_neg"), vec![]);
    let h_neg = Expr::apps(neg_le_neg, [dv.clone(), cv.clone(), h2]);

    // Body : Rat.add a (Rat.neg c) ≤ Rat.add b (Rat.neg d)
    //        (≡ Rat.sub a c ≤ Rat.sub b d by delta on the reducible Rat.sub)
    //        via  Rat.add_le_add a b (Rat.neg c) (Rat.neg d) h1 h_neg
    let add_le_add = Expr::const_(Name::from_string("Rat.add_le_add"), vec![]);
    let neg_c = rat_neg(cv.clone());
    let neg_d = rat_neg(dv.clone());
    let body = Expr::apps(add_le_add, [a.clone(), bv.clone(), neg_c, neg_d, h1, h_neg]);

    // Wrap lambdas in reverse binder order: fun (a b c d : Rat) (h1 : a ≤ b) (h2 : d ≤ c) => body
    let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(dv_id, BinderInfo::Default, rat.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, rat, e);
    b.finish(e)
}

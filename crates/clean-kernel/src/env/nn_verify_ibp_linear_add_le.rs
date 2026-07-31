// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T (#3490, Batch 0): Constructive proof term for `NNVerify.add_le_add`.
//!
//! Promotes `add_le_add` from sorry-inhabited `Declaration::Opaque` to a
//! constructive `Declaration::Theorem`. The proof uses only the foundational
//! order axiom `Rat.add_le_add_left` plus the field axiom `Rat.add_comm` and
//! the transitive axiom `Rat.le_trans`:
//!
//! * `Rat.add_le_add_left` (foundational) — `a ≤ b → ∀ c, c+a ≤ c+b`
//! * `Rat.add_comm`                        — `a+b = b+a`
//! * `Rat.le_trans`        (foundational) — `a ≤ b → b ≤ c → a ≤ c`
//! * `Eq.subst`            (foundational) — for rewriting via add_comm
//!
//! ## Proof chain
//!
//! Given `a1 b1 a2 b2 : Rat`, `h1 : a1 ≤ b1`, `h2 : a2 ≤ b2`:
//!
//! 1. `step_a : a2 + a1 ≤ a2 + b1` — `Rat.add_le_add_left a1 b1 h1 a2`
//! 2. `comm1  : a2 + a1 = a1 + a2` — `Rat.add_comm a2 a1`
//! 3. `step_b : a1 + a2 ≤ a2 + b1` — `Eq.subst` motive `λ x, x ≤ a2+b1`
//! 4. `comm2  : a2 + b1 = b1 + a2` — `Rat.add_comm a2 b1`
//! 5. `step_c : a1 + a2 ≤ b1 + a2` — `Eq.subst` motive `λ x, a1+a2 ≤ x`
//! 6. `step_d : b1 + a2 ≤ b1 + b2` — `Rat.add_le_add_left a2 b2 h2 b1`
//! 7. result  : a1 + a2 ≤ b1 + b2  — `Rat.le_trans (a1+a2) (b1+a2) (b1+b2) step_c step_d`
//!
//! Split into its own module to keep `nn_verify_ibp_linear.rs` under the
//! 500-line limit and match the existing `nn_verify_ibp_linear_transport.rs`
//! / `nn_verify_ibp_linear_mul_le.rs` pattern for T2/T3 (#3490).
//!
//! ## Closure impact
//!
//! The transitive axiom closure of `NNVerify.add_le_add` after this
//! promotion is
//!   `{Rat.add_le_add_left, Rat.add_comm, Rat.le_trans}` ∪ foundational
//! — all honest axioms from the existing whitelist — and LOSES `sorry`.
//!
//! Part of #3490 Batch 0 / #3476.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_farkas_order::RatOrderConsts;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a` for α = Rat.
///
/// Produces `motive b` from `h_eq : Eq a b` and `h_motive_a : motive a`.
fn eq_subst_rat(
    c: &RatOrderConsts,
    motive: Expr,
    a: Expr,
    b: Expr,
    h_eq: Expr,
    h_motive_a: Expr,
) -> Expr {
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_subst, [c.rat.clone(), motive, a, b, h_eq, h_motive_a])
}

/// Build the constructive proof term for `NNVerify.add_le_add`:
/// `∀ a1 b1 a2 b2 : Rat, a1 ≤ b1 → a2 ≤ b2 → a1+a2 ≤ b1+b2`.
///
/// Shape:
/// ```text
/// fun (a1 b1 a2 b2 : Rat) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) =>
///   let step_a : a2+a1 ≤ a2+b1 := Rat.add_le_add_left a1 b1 h1 a2
///   let comm1  : a2+a1 = a1+a2 := Rat.add_comm a2 a1
///   let step_b : a1+a2 ≤ a2+b1 :=
///     Eq.subst.{1} Rat (fun x => x ≤ a2+b1) (a2+a1) (a1+a2) comm1 step_a
///   let comm2  : a2+b1 = b1+a2 := Rat.add_comm a2 b1
///   let step_c : a1+a2 ≤ b1+a2 :=
///     Eq.subst.{1} Rat (fun x => a1+a2 ≤ x) (a2+b1) (b1+a2) comm2 step_b
///   let step_d : b1+a2 ≤ b1+b2 := Rat.add_le_add_left a2 b2 h2 b1
///   Rat.le_trans (a1+a2) (b1+a2) (b1+b2) step_c step_d
/// ```
pub(super) fn build_add_le_add_proof(c: &RatOrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a1_id, a1) = b.fresh_local(c.rat.clone());
    let (b1_id, b1v) = b.fresh_local(c.rat.clone());
    let (a2_id, a2) = b.fresh_local(c.rat.clone());
    let (b2_id, b2v) = b.fresh_local(c.rat.clone());

    let h1_ty = c.rat_le(a1.clone(), b1v.clone());
    let h2_ty = c.rat_le(a2.clone(), b2v.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let (h2_id, h2) = b.fresh_local(h2_ty.clone());

    // Reusable sums.
    let a2_plus_a1 = c.add(a2.clone(), a1.clone());
    let a1_plus_a2 = c.add(a1.clone(), a2.clone());
    let a2_plus_b1 = c.add(a2.clone(), b1v.clone());
    let b1_plus_a2 = c.add(b1v.clone(), a2.clone());
    let b1_plus_b2 = c.add(b1v.clone(), b2v.clone());

    // 1. step_a : Rat.le (a2 + a1) (a2 + b1)  via Rat.add_le_add_left a1 b1 h1 a2.
    let add_le_add_left = Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]);
    let step_a = Expr::apps(
        add_le_add_left.clone(),
        [a1.clone(), b1v.clone(), h1, a2.clone()],
    );

    // 2. comm1 : Eq Rat (a2 + a1) (a1 + a2)  via Rat.add_comm a2 a1.
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let comm1 = Expr::apps(add_comm.clone(), [a2.clone(), a1.clone()]);

    // 3. motive1 : Rat → Prop = fun x => Rat.le x (a2+b1)
    let motive1 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, a2_plus_b1.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // Eq.subst motive1 (a2+a1) (a1+a2) comm1 step_a
    //   : motive1 (a1+a2) = Rat.le (a1+a2) (a2+b1)
    let step_b = eq_subst_rat(c, motive1, a2_plus_a1, a1_plus_a2.clone(), comm1, step_a);

    // 4. comm2 : Eq Rat (a2 + b1) (b1 + a2)  via Rat.add_comm a2 b1.
    let comm2 = Expr::apps(add_comm, [a2.clone(), b1v.clone()]);

    // 5. motive2 : Rat → Prop = fun x => Rat.le (a1+a2) x
    let motive2 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(a1_plus_a2.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // Eq.subst motive2 (a2+b1) (b1+a2) comm2 step_b
    //   : motive2 (b1+a2) = Rat.le (a1+a2) (b1+a2)
    let step_c = eq_subst_rat(c, motive2, a2_plus_b1, b1_plus_a2.clone(), comm2, step_b);

    // 6. step_d : Rat.le (b1 + a2) (b1 + b2)  via Rat.add_le_add_left a2 b2 h2 b1.
    let step_d = Expr::apps(add_le_add_left, [a2.clone(), b2v.clone(), h2, b1v.clone()]);

    // 7. Rat.le_trans (a1+a2) (b1+a2) (b1+b2) step_c step_d : Rat.le (a1+a2) (b1+b2).
    let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
    let body = Expr::apps(
        le_trans,
        [a1_plus_a2, b1_plus_a2, b1_plus_b2, step_c, step_d],
    );

    let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a1_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K4 strict-add spine (run 2): the three strict-order
//! primitives the `Fin.sum_lt_sum` pigeonhole layer consumes.
//!
//! Building on the landed `Rat.add_lt_add_left` (strictadd run 1) and the B1c
//! mixed-transitivity spine (`Rat.lt_of_le_of_lt`, `Rat.lt_of_lt_of_le`):
//!
//! ```text
//! Rat.add_lt_add_right : ∀ a b c : Rat, a < b → (a + c) < (b + c)
//! Rat.lt_trans         : ∀ a b c : Rat, a < b → b < c → a < c
//! Rat.add_lt_add       : ∀ a b c d : Rat, a < b → c < d → (a + c) < (b + d)
//! Rat.add_le_add_right : ∀ a b c : Rat, a ≤ b → (a + c) ≤ (b + c)
//! ```
//!
//! (`add_le_add_right` is the non-strict `≤` twin needed by `Fin.sum_lt_sum`'s
//! prefix step — the live `Rat.add_le_add_left` has no right-side mirror.)
//!
//! `Rat.lt` is a `Quot.lift` and is NEVER reduced for variable arguments — all
//! strict-order reasoning goes through `Rat.lt_iff_le_not_le` propositionally
//! (or through the already-propositional spine lemmas), exactly as in the
//! B1c/B1d layers and the strictadd run-1 layer.
//!
//! ## Proofs (constructive, empty domain-axiom closure)
//!
//! - **`add_lt_add_right`** (`a<b → a+c < b+c`): mirror of `add_lt_add_left`
//!   via `Rat.add_comm` transport. `add_lt_add_left a b h c : (c+a) < (c+b)`;
//!   rewrite both endpoints `(c+a)=(a+c)`, `(c+b)=(b+c)` via `Rat.add_comm`
//!   lifted through `Eq.subst` over `Rat.lt`.
//! - **`lt_trans`** (`a<b → b<c → a<c`): `Rat.lt_of_lt_of_le a b c hab
//!   (And.left (mp hbc))` — the `b<c` hypothesis carries its own `b≤c`
//!   le-component (via `lt_iff_le_not_le`), so `lt_of_lt_of_le` closes it.
//! - **`add_lt_add`** (`a<b → c<d → a+c < b+d`): chain the two strict one-sided
//!   adds through `lt_trans`. `add_lt_add_right a b c hab : a+c < b+c` and
//!   `add_lt_add_left c d hcd b : b+c < b+d`, then `lt_trans (a+c)(b+c)(b+d)`.
//!
//! Every dependency (`Rat.add_lt_add_left`, `Rat.add_comm`,
//! `Rat.lt_of_lt_of_le`, `Rat.lt_iff_le_not_le`) is `Constructive` with empty
//! closure, so all three lemmas here are too.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ── Small Prop / Iff / And plumbing (mirrors the B1c layer) ────────────────

fn rat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
}
fn not_(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}
fn and_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}
fn iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}
fn lt_rhs(c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    and_(c.rat_le(a.clone(), b.clone()), not_(c.rat_le(b, a)))
}

/// `Rat.add_comm a b : Eq Rat (a+b) (b+a)`.
fn add_comm(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        [a, b],
    )
}

/// `Rat.add_lt_add_left : ∀ (a b c : Rat), a < b → Rat.lt (c+a) (c+b)`.
/// Application order is `a b c h`.
fn add_lt_add_left(a: Expr, b: Expr, c: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_lt_add_left"), vec![]),
        [a, b, c, h],
    )
}

/// `Rat.add_lt_add_right : ∀ (a b c : Rat), a < b → Rat.lt (a+c) (b+c)`.
/// Application order is `a b c h`.
fn add_lt_add_right(a: Expr, b: Expr, c: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_lt_add_right"), vec![]),
        [a, b, c, h],
    )
}

/// `Rat.add_le_add_left : ∀ (a b : Rat), a ≤ b → ∀ (c : Rat), (c+a) ≤ (c+b)`.
/// Application order is `a b h c`.
fn add_le_add_left(a: Expr, b: Expr, h: Expr, c: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]),
        [a, b, h, c],
    )
}

/// `Rat.lt_of_lt_of_le a b c hab hbc : Rat.lt a c`.
fn lt_of_lt_of_le(a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_of_lt_of_le"), vec![]),
        [a, b, cc, hab, hbc],
    )
}

/// `Rat.lt_trans a b c hab hbc : Rat.lt a c`.
fn lt_trans(a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_trans"), vec![]),
        [a, b, cc, hab, hbc],
    )
}

impl Environment {
    /// Register the K4 strict-add spine: `Rat.add_lt_add_right`,
    /// `Rat.lt_trans`, `Rat.add_lt_add`. Idempotent.
    ///
    /// Depends on `register_rat_add_lt_add_left` (run 1) and the B1c
    /// mixed-transitivity spine.
    pub fn init_boolean_analysis_kkl_strictadd2(&mut self) -> Result<(), EnvError> {
        self.register_rat_add_lt_add_left()?;
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_lt_of_le, lt_iff

        self.register_rat_add_lt_add_right()?;
        self.register_rat_lt_trans()?;
        self.register_rat_add_lt_add()?;
        self.register_rat_add_le_add_right()?;
        Ok(())
    }

    /// `Rat.add_le_add_right : ∀ a b c : Rat, a ≤ b → (a + c) ≤ (b + c)`.
    ///
    /// Non-strict right-add monotonicity, mirror of the live `Rat.add_le_add_left`
    /// via `Rat.add_comm` transport (the `≤` twin of `Rat.add_lt_add_right`).
    /// Kernel-checked, constructive, empty closure.
    pub fn register_rat_add_le_add_right(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_le_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // `Rat.add_le_add_left` + `Rat.add_comm` come from the interval-arith /
        // Rat field surface the order toolkit already initializes.
        self.init_boolean_analysis_order_toolkit()?;

        let c = OrderConsts::new();
        let ty = add_le_add_right_type(&c);
        let value = build_add_le_add_right_proof(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_lt_add_right : ∀ a b c : Rat, a < b → (a + c) < (b + c)`.
    ///
    /// Strict right-add monotonicity, mirror of `add_lt_add_left` via
    /// `Rat.add_comm` transport. Kernel-checked, constructive, empty closure.
    pub fn register_rat_add_lt_add_right(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_lt_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_add_lt_add_left()?;

        let c = OrderConsts::new();
        let ty = add_lt_add_right_type(&c);
        let value = build_add_lt_add_right_proof(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_trans : ∀ a b c : Rat, a < b → b < c → a < c`.
    ///
    /// Strict transitivity, derived from `Rat.lt_of_lt_of_le` plus the
    /// `b ≤ c` le-component of `b < c`. Kernel-checked, constructive, empty
    /// closure.
    pub fn register_rat_lt_trans(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit_b1c()?;

        let c = OrderConsts::new();
        let ty = lt_trans_type(&c);
        let value = build_lt_trans_proof(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_lt_add : ∀ a b c d : Rat, a < b → c < d → (a + c) < (b + d)`.
    ///
    /// Two-sided strict-add monotonicity. `add_lt_add_right` ∘ `add_lt_add_left`
    /// ∘ `lt_trans`. Kernel-checked, constructive, empty closure.
    pub fn register_rat_add_lt_add(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_lt_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_add_lt_add_right()?;
        self.register_rat_lt_trans()?;

        let c = OrderConsts::new();
        let ty = add_lt_add_type(&c);
        let value = build_add_lt_add_proof(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ── 1. Rat.add_lt_add_right ────────────────────────────────────────────────

/// Type `∀ a b c, Rat.lt a b → Rat.lt (a+c) (b+c)`.
fn add_lt_add_right_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(a.clone(), bv.clone());
    let concl = rat_lt(c.add(a.clone(), cv.clone()), c.add(bv.clone(), cv.clone()));
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_lt_add_right`.
///
/// `add_lt_add_left a b h c : (c+a) < (c+b)`. Rewrite the LHS endpoint
/// `(c+a)=(a+c)` and the RHS endpoint `(c+b)=(b+c)` via `Rat.add_comm` lifted
/// through `Eq.subst` over `Rat.lt`.
fn build_add_lt_add_right_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let ca = c.add(cv.clone(), a.clone()); // c+a
    let cb = c.add(cv.clone(), bv.clone()); // c+b
    let ac = c.add(a.clone(), cv.clone()); // a+c
    let bc = c.add(bv.clone(), cv.clone()); // b+c

    // base : (c+a) < (c+b)   [add_lt_add_left a b c h]
    let base = add_lt_add_left(a.clone(), bv.clone(), cv.clone(), h);

    // rewrite LHS endpoint (c+a) -> (a+c) via add_comm c a : (c+a)=(a+c).
    // motive_l := fun (t : Rat) => Rat.lt t (c+b)
    let h_comm_l = add_comm(cv.clone(), a.clone()); // (c+a)=(a+c)
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = rat_lt(t, cb.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_l = c.subst(motive_l, ca.clone(), ac.clone(), h_comm_l, base);

    // rewrite RHS endpoint (c+b) -> (b+c) via add_comm c b : (c+b)=(b+c).
    // motive_r := fun (t : Rat) => Rat.lt (a+c) t
    let h_comm_r = add_comm(cv.clone(), bv.clone()); // (c+b)=(b+c)
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = rat_lt(ac.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let body = c.subst(motive_r, cb.clone(), bc.clone(), h_comm_r, step_l);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ── 1b. Rat.add_le_add_right (≤ twin of add_lt_add_right) ──────────────────

/// Type `∀ a b c, Rat.le a b → Rat.le (a+c) (b+c)`.
fn add_le_add_right_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = c.rat_le(a.clone(), bv.clone());
    let concl = c.rat_le(c.add(a.clone(), cv.clone()), c.add(bv.clone(), cv.clone()));
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_le_add_right`.
///
/// `add_le_add_left a b h c : (c+a) ≤ (c+b)`. Rewrite the LHS endpoint
/// `(c+a)=(a+c)` and the RHS endpoint `(c+b)=(b+c)` via `Rat.add_comm` lifted
/// through `Eq.subst` over `Rat.le`.
fn build_add_le_add_right_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = c.rat_le(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let ca = c.add(cv.clone(), a.clone()); // c+a
    let cb = c.add(cv.clone(), bv.clone()); // c+b
    let ac = c.add(a.clone(), cv.clone()); // a+c
    let bc = c.add(bv.clone(), cv.clone()); // b+c

    // base : (c+a) ≤ (c+b)   [add_le_add_left a b h c]
    let base = add_le_add_left(a.clone(), bv.clone(), h, cv.clone());

    // rewrite LHS endpoint (c+a) -> (a+c) via add_comm c a.
    let h_comm_l = add_comm(cv.clone(), a.clone()); // (c+a)=(a+c)
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rat_le(t, cb.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_l = c.subst(motive_l, ca.clone(), ac.clone(), h_comm_l, base);

    // rewrite RHS endpoint (c+b) -> (b+c) via add_comm c b.
    let h_comm_r = add_comm(cv.clone(), bv.clone()); // (c+b)=(b+c)
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rat_le(ac.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let body = c.subst(motive_r, cb.clone(), bc.clone(), h_comm_r, step_l);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ── 2. Rat.lt_trans ────────────────────────────────────────────────────────

/// Type `∀ a b c, Rat.lt a b → Rat.lt b c → Rat.lt a c`.
fn lt_trans_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = rat_lt(a.clone(), bv.clone());
    let h_bc_ty = rat_lt(bv.clone(), cv.clone());
    let concl = rat_lt(a.clone(), cv.clone());
    let (h1_id, _) = b.fresh_local(h_ab_ty.clone());
    let (h2_id, _) = b.fresh_local(h_bc_ty.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, h_bc_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.lt_trans`.
///
/// `lt_of_lt_of_le a b c hab (And.left (mp hbc))` — extract `b ≤ c` from the
/// `b < c` hypothesis via `lt_iff_le_not_le` and feed it to `lt_of_lt_of_le`.
fn build_lt_trans_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = rat_lt(a.clone(), bv.clone());
    let h_bc_ty = rat_lt(bv.clone(), cv.clone());
    let (hab_id, h_ab) = b.fresh_local(h_ab_ty.clone());
    let (hbc_id, h_bc) = b.fresh_local(h_bc_ty.clone());

    // mp hbc : (b ≤ c) ∧ ¬(c ≤ b)
    let rhs_bc = lt_rhs(c, bv.clone(), cv.clone());
    let mp = iff_mp(
        rat_lt(bv.clone(), cv.clone()),
        rhs_bc,
        lt_iff(bv.clone(), cv.clone()),
        h_bc,
    );
    let le_bc = c.rat_le(bv.clone(), cv.clone());
    let not_le_cb = not_(c.rat_le(cv.clone(), bv.clone()));
    let h_le_bc = and_left(le_bc, not_le_cb, mp); // b ≤ c

    let body = lt_of_lt_of_le(a.clone(), bv.clone(), cv.clone(), h_ab, h_le_bc);

    let e = b.mk_lam(hbc_id, BinderInfo::Default, h_bc_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

// ── 3. Rat.add_lt_add ──────────────────────────────────────────────────────

/// Type `∀ a b c d, Rat.lt a b → Rat.lt c d → Rat.lt (a+c) (b+d)`.
fn add_lt_add_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let (dv_id, dv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = rat_lt(a.clone(), bv.clone());
    let h_cd_ty = rat_lt(cv.clone(), dv.clone());
    let concl = rat_lt(c.add(a.clone(), cv.clone()), c.add(bv.clone(), dv.clone()));
    let (h1_id, _) = b.fresh_local(h_ab_ty.clone());
    let (h2_id, _) = b.fresh_local(h_cd_ty.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, h_cd_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_pi(dv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_lt_add`.
///
/// `add_lt_add_right a b c hab : (a+c) < (b+c)` and
/// `add_lt_add_left c d hcd b : (b+c) < (b+d)`, chained through
/// `lt_trans (a+c) (b+c) (b+d)`.
fn build_add_lt_add_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let (dv_id, dv) = b.fresh_local(c.rat.clone());
    let h_ab_ty = rat_lt(a.clone(), bv.clone());
    let h_cd_ty = rat_lt(cv.clone(), dv.clone());
    let (hab_id, h_ab) = b.fresh_local(h_ab_ty.clone());
    let (hcd_id, h_cd) = b.fresh_local(h_cd_ty.clone());

    let ac = c.add(a.clone(), cv.clone()); // a+c
    let bc = c.add(bv.clone(), cv.clone()); // b+c
    let bd = c.add(bv.clone(), dv.clone()); // b+d

    // left step: (a+c) < (b+c)   [add_lt_add_right a b c hab]
    let step1 = add_lt_add_right(a.clone(), bv.clone(), cv.clone(), h_ab);
    // right step: (b+c) < (b+d)  [add_lt_add_left c d b hcd]
    let step2 = add_lt_add_left(cv.clone(), dv.clone(), bv.clone(), h_cd);
    // chain via lt_trans
    let body = lt_trans(ac, bc, bd, step1, step2);

    let e = b.mk_lam(hcd_id, BinderInfo::Default, h_cd_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, h_ab_ty, e);
    let e = b.mk_lam(dv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "Rat.add_lt_add_right",
        "Rat.lt_trans",
        "Rat.add_lt_add",
        "Rat.add_le_add_right",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_kkl_strictadd2()
            .expect("init_boolean_analysis_kkl_strictadd2");
        env
    }

    #[test]
    fn test_strictadd2_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty"
            );
        }
    }

    #[test]
    fn test_strictadd2_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis_kkl_strictadd2().expect("first");
        env.init_boolean_analysis_kkl_strictadd2()
            .expect("second (idempotent)");
    }
}

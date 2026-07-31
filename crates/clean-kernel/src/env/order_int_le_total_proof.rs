// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof of
//! `Int.le_total : ∀ a b : Int, Or (Int.le a b) (Int.le b a)`.
//!
//! Replaces the prior `Declaration::Axiom` registration in
//! `order_int.rs::init_int_linear_order` (whose comment previously read
//! "`Int.le_total` … REMAIN axioms: they need totality / decidable Int
//! comparison, which has no constructive proof in-tree") with a
//! `Declaration::Theorem` whose body is a genuine kernel-checked proof term.
//!
//! # Definitions in play
//!
//! ```text
//! Int.le a b := Int.NonNeg (Int.sub b a)            -- reducible Definition
//! Int.sub a b := Int.add a (Int.neg b)              -- reducible Definition
//! Int.neg (Int.ofNat n)   ≡ Int.negOfNat n          -- by iota on Int.rec
//! Int.neg (Int.negSucc n) ≡ Int.ofNat (Nat.succ n)
//! inductive Int.NonNeg : Int → Prop where
//!   | mk (n : Nat) : Int.NonNeg (Int.ofNat n)
//! ```
//!
//! So `Int.le a b` delta/iota-reduces to `Int.NonNeg (Int.sub b a)` and the
//! goal `Or (Int.le a b) (Int.le b a)` is `Or (NonNeg (sub b a)) (NonNeg (sub a b))`.
//!
//! # Proof sketch
//!
//! The arithmetic core is the `Int.subNatNat`-totality helper
//!
//! ```text
//! Int.subNatNat_total : ∀ m n : Nat,
//!   Or (Int.NonNeg (Int.subNatNat m n)) (Int.NonNeg (Int.subNatNat n m))
//! ```
//!
//! proved by double `Nat` induction (the exact shape of `Nat.le_total`):
//! `Nat.rec` on `m`, `Nat.casesOn` on `n`, `Or.rec` on the IH in the
//! successor/successor case. The clamped subtraction `Int.subNatNat k 0`
//! reduces to `Int.ofNat k`, so the base and zero cases discharge directly
//! with `@Int.NonNeg.mk`; the succ/succ case lifts the IH through
//! `Int.subNatNat_succ_succ` (transporting each `NonNeg` witness with
//! `@Eq.subst`).
//!
//! `Int.le_total` itself case-splits on `a` and `b` via `@Int.rec`:
//!
//! - **`ofNat m`, `ofNat n`**: `Int.neg (ofNat _) ≡ negOfNat _`, so
//!   `sub (ofNat n) (ofNat m) ≡ add (ofNat n) (negOfNat m)` and (by
//!   `Int.subNatNat_eq_add`) `= subNatNat n m`. Transport both disjuncts of
//!   `subNatNat_total n m` along `subNatNat_eq_add` to recover
//!   `Or (NonNeg (sub (ofNat n)(ofNat m))) (NonNeg (sub (ofNat m)(ofNat n)))`.
//! - **`ofNat m`, `negSucc n`** (`a = ofNat m`, `b = negSucc n`):
//!   `sub a b ≡ ofNat (Nat.add m (Nat.succ n))`, always `NonNeg`, so
//!   `Or.inr (@Int.NonNeg.mk (Nat.add m (Nat.succ n)))`.
//! - **`negSucc m`, `ofNat n`**: symmetric, `sub b a ≡ ofNat (Nat.add n (Nat.succ m))`,
//!   so `Or.inl (@Int.NonNeg.mk (Nat.add n (Nat.succ m)))`.
//! - **`negSucc m`, `negSucc n`**: `Int.neg (negSucc _) ≡ ofNat (succ _)`, so
//!   `sub (negSucc n)(negSucc m) ≡ subNatNat (succ m)(succ n)` and (by
//!   `Int.subNatNat_succ_succ`) `= subNatNat m n`. Transport both disjuncts of
//!   `subNatNat_total m n` along `subNatNat_succ_succ` to recover the goal.
//!
//! Each transport step is a single `@Eq.subst.{1}` with motive
//! `fun x : Int => Int.NonNeg x`; the kernel closes every case up to its own
//! definitional reduction of `Int.le` / `Int.sub` / `Int.neg` / `Int.add`.
//!
//! # Axiom closure
//!
//! The proof term mentions only the auto-generated recursors `Int.rec`,
//! `Nat.rec`, `Nat.casesOn`, `Int.NonNeg.rec` (via `Or.rec`); the constructors
//! `Int.ofNat`, `Int.negSucc`, `Int.NonNeg.mk`, `Nat.succ`, `Or.inl`,
//! `Or.inr`; the foundational `Eq.subst`; and the constructive
//! `Declaration::Theorem`s `Int.subNatNat_eq_add` and
//! `Int.subNatNat_succ_succ`. None is a `Declaration::Axiom`, so
//! `env.axiom_deps("Int.le_total")` is empty and
//! `env.proof_quality("Int.le_total") == ProofQuality::Constructive`.
//!
//! Unblocked by the constructive `Nat.le_total` (#3599,
//! `order_nat_le_total_proof.rs`) — though this proof reduces to the
//! `subNatNat` layer directly rather than routing through `Nat.le_total`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across type and value construction.
struct IntLeTotalConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_rec: Expr,
    nat_cases_on: Expr,
    int_le: Expr,
    int_sub: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_sub_nat_nat: Expr,
    int_rec_prop: Expr,
    nonneg: Expr,
    nonneg_mk: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    eq_subst: Expr,
    sub_nat_nat_eq_add: Expr,
    sub_nat_nat_succ_succ: Expr,
}

impl IntLeTotalConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            // Nat.rec.{0} / Nat.casesOn.{0} — Prop-valued motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nat_cases_on: Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_sub_nat_nat: Expr::const_(Name::from_string("Int.subNatNat"), vec![]),
            // Int.rec.{0} — eliminating into `Prop = Sort 0`, since each case's
            // motive value `fun _ : Int => Or … : Prop` lives in `Sort 0`.
            int_rec_prop: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            nonneg_mk: Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            // @Eq.subst.{1} for `x : Int`.
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            sub_nat_nat_eq_add: Expr::const_(Name::from_string("Int.subNatNat_eq_add"), vec![]),
            sub_nat_nat_succ_succ: Expr::const_(
                Name::from_string("Int.subNatNat_succ_succ"),
                vec![],
            ),
        }
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn nat_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }

    fn snn(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.int_sub_nat_nat.clone(), [m, n])
    }

    fn nonneg_of(&self, x: Expr) -> Expr {
        Expr::app(self.nonneg.clone(), x)
    }

    /// `Int.le x y` (raw reducible Definition form).
    fn le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }

    /// `Int.sub x y`.
    fn sub(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [x, y])
    }

    /// `@Int.NonNeg.mk k : Int.NonNeg (Int.ofNat k)`.
    fn nonneg_mk(&self, k: Expr) -> Expr {
        Expr::app(self.nonneg_mk.clone(), k)
    }

    /// `Or (Int.NonNeg (subNatNat m n)) (Int.NonNeg (subNatNat n m))`.
    fn snn_or(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::apps(
            self.or_const.clone(),
            [
                self.nonneg_of(self.snn(m.clone(), n.clone())),
                self.nonneg_of(self.snn(n.clone(), m.clone())),
            ],
        )
    }

    /// `motive := fun x : Int => Int.NonNeg x` for `@Eq.subst`.
    fn nonneg_motive(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(self.int_type.clone());
        let body = self.nonneg_of(x);
        let lam = mb.mk_lam(x_id, BinderInfo::Default, self.int_type.clone(), body);
        mb.finish_child(lam)
    }

    /// `@Eq.subst.{1} Int (fun x => NonNeg x) lhs rhs h_eq witness :
    ///   Int.NonNeg rhs` from `h_eq : Eq Int lhs rhs` and
    /// `witness : Int.NonNeg lhs`.
    fn nonneg_subst(
        &self,
        parent: &EnvDeclBuilder,
        lhs: Expr,
        rhs: Expr,
        h_eq: Expr,
        witness: Expr,
    ) -> Expr {
        let motive = self.nonneg_motive(parent);
        Expr::apps(
            self.eq_subst.clone(),
            [self.int_type.clone(), motive, lhs, rhs, h_eq, witness],
        )
    }
}

// ============================================================================
// Helper: Int.subNatNat_total
// ============================================================================

/// `∀ m n : Nat, Or (NonNeg (subNatNat m n)) (NonNeg (subNatNat n m))`.
#[cfg(test)]
fn snn_total_type(c: &IntLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());
    let body = c.snn_or(&m, &n);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

/// Outer `Nat.rec` motive: `fun s : Nat => ∀ y : Nat,
///   Or (NonNeg (subNatNat s y)) (NonNeg (subNatNat y s))`.
fn snn_motive(c: &IntLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (s_id, s) = mb.fresh_local(c.nat_type.clone());
    let inner = {
        let mut yb = EnvDeclBuilder::child_of(&mb);
        let (y_id, y) = yb.fresh_local(c.nat_type.clone());
        let body = c.snn_or(&s, &y);
        let pi = yb.mk_pi(y_id, BinderInfo::Default, c.nat_type.clone(), body);
        yb.finish_child(pi)
    };
    let lam = mb.mk_lam(s_id, BinderInfo::Default, c.nat_type.clone(), inner);
    mb.finish_child(lam)
}

/// Base case (`m = 0`): `fun y : Nat =>
///   Or.inr _ _ (@Int.NonNeg.mk y)`.
///
/// Goal `Or (NonNeg (subNatNat 0 y)) (NonNeg (subNatNat y 0))`; the right
/// disjunct `subNatNat y 0 ≡ ofNat y`, so `@Int.NonNeg.mk y` inhabits it.
fn snn_base(c: &IntLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut zb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = zb.fresh_local(c.nat_type.clone());
    let left = c.nonneg_of(c.snn(c.nat_zero.clone(), y.clone()));
    let right = c.nonneg_of(c.snn(y.clone(), c.nat_zero.clone()));
    let body = Expr::apps(c.or_inr.clone(), [left, right, c.nonneg_mk(y.clone())]);
    let lam = zb.mk_lam(y_id, BinderInfo::Default, c.nat_type.clone(), body);
    zb.finish_child(lam)
}

/// `Nat.casesOn` motive for the inner split on `y`:
///   `fun w : Nat => Or (NonNeg (subNatNat (succ s) w)) (NonNeg (subNatNat w (succ s)))`.
fn snn_cases_motive(c: &IntLeTotalConsts, parent: &EnvDeclBuilder, succ_s: &Expr) -> Expr {
    let mut cm = EnvDeclBuilder::child_of(parent);
    let (w_id, w) = cm.fresh_local(c.nat_type.clone());
    let body = c.snn_or(succ_s, &w);
    let lam = cm.mk_lam(w_id, BinderInfo::Default, c.nat_type.clone(), body);
    cm.finish_child(lam)
}

/// Inner zero case (`y = 0`): `Or.inl` witnessed by `@Int.NonNeg.mk (succ s)`,
/// proving `Or (NonNeg (subNatNat (succ s) 0)) (NonNeg (subNatNat 0 (succ s)))`
/// — the left disjunct `subNatNat (succ s) 0 ≡ ofNat (succ s)`.
fn snn_inner_zero(c: &IntLeTotalConsts, succ_s: &Expr) -> Expr {
    let left = c.nonneg_of(c.snn(succ_s.clone(), c.nat_zero.clone()));
    let right = c.nonneg_of(c.snn(c.nat_zero.clone(), succ_s.clone()));
    Expr::apps(c.or_inl.clone(), [left, right, c.nonneg_mk(succ_s.clone())])
}

/// Inner successor case (`y = succ j`): `fun j : Nat => Or.rec … (ih j)`,
/// lifting `ih j : Or (NonNeg (subNatNat s j)) (NonNeg (subNatNat j s))`
/// through `Int.subNatNat_succ_succ` into
/// `Or (NonNeg (subNatNat (succ s)(succ j))) (NonNeg (subNatNat (succ j)(succ s)))`.
fn snn_inner_succ(
    c: &IntLeTotalConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    succ_s: &Expr,
    ih: &Expr,
) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = cb.fresh_local(c.nat_type.clone());
    let succ_j = c.succ(j.clone());

    // IH disjuncts (over subNatNat s j / subNatNat j s).
    let a_prop = c.nonneg_of(c.snn(s.clone(), j.clone())); // NonNeg (subNatNat s j)
    let b_prop = c.nonneg_of(c.snn(j.clone(), s.clone())); // NonNeg (subNatNat j s)

    // Goal disjuncts (over subNatNat (succ s)(succ j) / subNatNat (succ j)(succ s)).
    let goal_left = c.nonneg_of(c.snn(succ_s.clone(), succ_j.clone()));
    let goal_right = c.nonneg_of(c.snn(succ_j.clone(), succ_s.clone()));
    let goal = Expr::apps(c.or_const.clone(), [goal_left.clone(), goal_right.clone()]);

    // const motive for Or.rec: `fun _ : Or a_prop b_prop => goal`.
    let or_motive = {
        let mut om = EnvDeclBuilder::child_of(&cb);
        let or_ab = Expr::apps(c.or_const.clone(), [a_prop.clone(), b_prop.clone()]);
        let (hh_id, _hh) = om.fresh_local(or_ab.clone());
        let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
        om.finish_child(lam)
    };

    // inl case: `fun h : NonNeg (subNatNat s j) =>
    //   Or.inl _ _ (subst (succ_succ s j) h)` where
    //   `subNatNat_succ_succ s j : subNatNat (succ s)(succ j) = subNatNat s j`.
    //   We transport `h : NonNeg (subNatNat s j)` to
    //   `NonNeg (subNatNat (succ s)(succ j))` along `Eq.symm`-free direction by
    //   using the equation `subNatNat (succ s)(succ j) = subNatNat s j` read
    //   right-to-left: `Eq.subst` needs `lhs = rhs` with witness over `lhs`.
    //   Since the witness is over `subNatNat s j` (the RHS) and the target is
    //   `subNatNat (succ s)(succ j)` (the LHS), we feed `succ_succ` reversed.
    let succ_succ_sj = Expr::apps(c.sub_nat_nat_succ_succ.clone(), [s.clone(), j.clone()]);
    let snn_ss_sj = c.snn(succ_s.clone(), succ_j.clone()); // subNatNat (succ s)(succ j)
    let snn_s_j = c.snn(s.clone(), j.clone()); // subNatNat s j
    let case_inl = {
        let mut ic = EnvDeclBuilder::child_of(&cb);
        let (h_id, h) = ic.fresh_local(a_prop.clone());
        // We need `NonNeg (subNatNat (succ s)(succ j))` from
        // `h : NonNeg (subNatNat s j)`. `succ_succ_sj :
        // subNatNat (succ s)(succ j) = subNatNat s j`; reverse it via Eq.symm
        // to `subNatNat s j = subNatNat (succ s)(succ j)`, then subst `h`.
        let h_eq = c.eq_symm_int(
            &ic,
            snn_ss_sj.clone(),
            snn_s_j.clone(),
            succ_succ_sj.clone(),
        );
        let lifted = c.nonneg_subst(&ic, snn_s_j.clone(), snn_ss_sj.clone(), h_eq, h);
        let body = Expr::apps(
            c.or_inl.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), body);
        ic.finish_child(lam)
    };

    // inr case: symmetric over subNatNat j s / subNatNat (succ j)(succ s).
    let succ_succ_js = Expr::apps(c.sub_nat_nat_succ_succ.clone(), [j.clone(), s.clone()]);
    let snn_ss_js = c.snn(succ_j.clone(), succ_s.clone());
    let snn_j_s = c.snn(j.clone(), s.clone());
    let case_inr = {
        let mut rc = EnvDeclBuilder::child_of(&cb);
        let (h_id, h) = rc.fresh_local(b_prop.clone());
        let h_eq = c.eq_symm_int(
            &rc,
            snn_ss_js.clone(),
            snn_j_s.clone(),
            succ_succ_js.clone(),
        );
        let lifted = c.nonneg_subst(&rc, snn_j_s.clone(), snn_ss_js.clone(), h_eq, h);
        let body = Expr::apps(
            c.or_inr.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
        rc.finish_child(lam)
    };

    let ih_j = Expr::app(ih.clone(), j.clone());
    let or_rec_app = Expr::apps(
        c.or_rec.clone(),
        [a_prop, b_prop, or_motive, case_inl, case_inr, ih_j],
    );
    let lam_j = cb.mk_lam(j_id, BinderInfo::Default, c.nat_type.clone(), or_rec_app);
    cb.finish_child(lam_j)
}

/// Step case (`m = succ s`): `fun s ih y => Nat.casesOn motive y zero succ`.
fn snn_step(c: &IntLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (s_id, s) = sb.fresh_local(c.nat_type.clone());

    // ih : ∀ y, Or (NonNeg (subNatNat s y)) (NonNeg (subNatNat y s))
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&sb);
        let (y_id, y) = ib.fresh_local(c.nat_type.clone());
        let body = c.snn_or(&s, &y);
        let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat_type.clone(), body);
        ib.finish_child(pi)
    };
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let (y_id, y) = sb.fresh_local(c.nat_type.clone());
    let succ_s = c.succ(s.clone());

    let cases_motive = snn_cases_motive(c, &sb, &succ_s);
    let zero_case = snn_inner_zero(c, &succ_s);
    let succ_case = snn_inner_succ(c, &sb, &s, &succ_s, &ih);

    // Lean-faithful casesOn order: motive, major, then minors.
    let cases = Expr::apps(
        c.nat_cases_on.clone(),
        [cases_motive, y.clone(), zero_case, succ_case],
    );
    let lam_y = sb.mk_lam(y_id, BinderInfo::Default, c.nat_type.clone(), cases);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_y);
    let lam_s = sb.mk_lam(s_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
    sb.finish_child(lam_s)
}

/// `fun m n : Nat => @Nat.rec motive base step m n`.
fn snn_total_value(c: &IntLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat_type.clone());
    let (n_id, n) = b.fresh_local(c.nat_type.clone());

    let motive = snn_motive(c, &b);
    let base = snn_base(c, &b);
    let step = snn_step(c, &b);

    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, m.clone()]);
    let applied = Expr::app(rec_app, n.clone());

    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), applied);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), e);
    b.finish(e)
}

impl IntLeTotalConsts {
    /// `@Eq.symm.{1} Int a b h : Eq Int b a` from `h : Eq Int a b`, built
    /// without caching an `Eq.symm` constant (Eq.symm only needed here).
    fn eq_symm_int(&self, _parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_symm, [self.int_type.clone(), a, b, h])
    }
}

// ============================================================================
// Main theorem: Int.le_total
// ============================================================================

/// `∀ a b : Int, Or (Int.le a b) (Int.le b a)` (raw `Int.le` form; this is
/// definitionally the typeclass `LE.le @Int instLEInt` form used by the
/// downstream `instLinearOrderInt`, since `instLEInt` is the reducible
/// `LE.mk Int.le`).
fn le_total_type(c: &IntLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());
    let body = Expr::apps(
        c.or_const.clone(),
        [c.le(a.clone(), bv.clone()), c.le(bv.clone(), a.clone())],
    );
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), e);
    b.finish(e)
}

/// Outer `Int.rec` motive on `a`:
///   `fun a : Int => ∀ b : Int, Or (Int.le a b) (Int.le b a)`.
fn le_total_outer_motive(c: &IntLeTotalConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (a_id, a) = mb.fresh_local(c.int_type.clone());
    let inner = {
        let mut bb = EnvDeclBuilder::child_of(&mb);
        let (bv_id, bv) = bb.fresh_local(c.int_type.clone());
        let body = Expr::apps(
            c.or_const.clone(),
            [c.le(a.clone(), bv.clone()), c.le(bv.clone(), a.clone())],
        );
        let pi = bb.mk_pi(bv_id, BinderInfo::Default, c.int_type.clone(), body);
        bb.finish_child(pi)
    };
    let lam = mb.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), inner);
    mb.finish_child(lam)
}

/// Inner `Int.rec` motive on `b` for a fixed `a`:
///   `fun b : Int => Or (Int.le a b) (Int.le b a)`.
fn le_total_inner_motive(c: &IntLeTotalConsts, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (bv_id, bv) = mb.fresh_local(c.int_type.clone());
    let body = Expr::apps(
        c.or_const.clone(),
        [c.le(a.clone(), bv.clone()), c.le(bv.clone(), a.clone())],
    );
    let lam = mb.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

/// negSucc m, negSucc n branch (a = negSucc m, b = negSucc n):
///   `sub b a ≡ subNatNat (succ m)(succ n)` and `sub a b ≡ subNatNat (succ n)(succ m)`;
///   transport `subNatNat_total m n` onto the goal via `subNatNat_succ_succ`.
fn le_total_negsucc_negsucc(
    c: &IntLeTotalConsts,
    parent: &EnvDeclBuilder,
    snn_total: &Expr,
    m: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = mb.fresh_local(c.nat_type.clone());
    let succ_m = c.succ(m.clone());
    let succ_n = c.succ(n.clone());
    let neg_m = c.neg_succ(m.clone());
    let neg_n = c.neg_succ(n.clone());

    // Goal disjuncts (a = negSucc m, b = negSucc n):
    //   left  = NonNeg (sub b a) = NonNeg (sub (negSucc n)(negSucc m))
    //           ≡ NonNeg (subNatNat (succ m)(succ n))
    //   right = NonNeg (sub a b) = NonNeg (sub (negSucc m)(negSucc n))
    //           ≡ NonNeg (subNatNat (succ n)(succ m))
    let goal_left = c.nonneg_of(c.sub(neg_n.clone(), neg_m.clone()));
    let goal_right = c.nonneg_of(c.sub(neg_m.clone(), neg_n.clone()));
    let goal = Expr::apps(c.or_const.clone(), [goal_left.clone(), goal_right.clone()]);

    // h := subNatNat_total m n
    //    : Or (NonNeg (subNatNat m n)) (NonNeg (subNatNat n m)).
    // We route: left goal needs subNatNat (succ m)(succ n) ← subNatNat m n
    //           right goal needs subNatNat (succ n)(succ m) ← subNatNat n m.
    let a_prop = c.nonneg_of(c.snn(m.clone(), n.clone())); // NonNeg (subNatNat m n)
    let b_prop = c.nonneg_of(c.snn(n.clone(), m.clone())); // NonNeg (subNatNat n m)
    let h = Expr::apps(snn_total.clone(), [m.clone(), n.clone()]);

    let or_motive = {
        let mut om = EnvDeclBuilder::child_of(&mb);
        let or_ab = Expr::apps(c.or_const.clone(), [a_prop.clone(), b_prop.clone()]);
        let (hh_id, _hh) = om.fresh_local(or_ab.clone());
        let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
        om.finish_child(lam)
    };

    // inl: h : NonNeg (subNatNat m n) -> NonNeg (subNatNat (succ m)(succ n)) (= goal_left).
    //   succ_succ m n : subNatNat (succ m)(succ n) = subNatNat m n; subst reversed.
    let snn_mn = c.snn(m.clone(), n.clone());
    let snn_ss_mn = c.snn(succ_m.clone(), succ_n.clone());
    let case_inl = {
        let mut ic = EnvDeclBuilder::child_of(&mb);
        let (h_id, hh) = ic.fresh_local(a_prop.clone());
        let succ_succ = Expr::apps(c.sub_nat_nat_succ_succ.clone(), [m.clone(), n.clone()]);
        let eq = c.eq_symm_int(&ic, snn_ss_mn.clone(), snn_mn.clone(), succ_succ);
        // eq : subNatNat m n = subNatNat (succ m)(succ n); subst hh.
        let lifted = c.nonneg_subst(&ic, snn_mn.clone(), snn_ss_mn.clone(), eq, hh);
        let body = Expr::apps(
            c.or_inl.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), body);
        ic.finish_child(lam)
    };

    let snn_nm = c.snn(n.clone(), m.clone());
    let snn_ss_nm = c.snn(succ_n.clone(), succ_m.clone());
    let case_inr = {
        let mut rc = EnvDeclBuilder::child_of(&mb);
        let (h_id, hh) = rc.fresh_local(b_prop.clone());
        let succ_succ = Expr::apps(c.sub_nat_nat_succ_succ.clone(), [n.clone(), m.clone()]);
        let eq = c.eq_symm_int(&rc, snn_ss_nm.clone(), snn_nm.clone(), succ_succ);
        let lifted = c.nonneg_subst(&rc, snn_nm.clone(), snn_ss_nm.clone(), eq, hh);
        let body = Expr::apps(
            c.or_inr.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
        rc.finish_child(lam)
    };

    let or_rec_app = Expr::apps(
        c.or_rec.clone(),
        [a_prop, b_prop, or_motive, case_inl, case_inr, h],
    );
    let lam_n = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), or_rec_app);
    mb.finish_child(lam_n)
}

/// Build the full `Int.le_total` proof value.
fn le_total_value(c: &IntLeTotalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (bv_id, bv) = b.fresh_local(c.int_type.clone());

    // Closed helper `subNatNat_total` as a let-free inline term reused in the
    // ofNat/ofNat and negSucc/negSucc branches.
    let snn_total = snn_total_value(c);

    let outer_motive = le_total_outer_motive(c, &b);

    // ofNat minor of the OUTER Int.rec on a: `fun m : Nat => <inner rec on b>`.
    let outer_ofnat = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let a_val = c.of_nat(m.clone());
        let inner_motive = le_total_inner_motive(c, &ob, &a_val);
        // inner ofNat (n): ofNat m, ofNat n -> ofNat_ofNat, but that helper
        // binds its own m,n. Inline the ofNat/ofNat branch specialized to this m.
        let inner_ofnat = le_total_ofnat_ofnat_with_m(c, &ob, &snn_total, &m);
        let inner_negsucc = le_total_ofnat_negsucc_with_m(c, &ob, &m);
        let (bvar_id, bvar) = ob.fresh_local(c.int_type.clone());
        let inner_rec = Expr::apps(
            c.int_rec_prop.clone(),
            [inner_motive, inner_ofnat, inner_negsucc, bvar.clone()],
        );
        let lam_b = ob.mk_lam(bvar_id, BinderInfo::Default, c.int_type.clone(), inner_rec);
        let lam_m = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
        ob.finish_child(lam_m)
    };

    // negSucc minor of the OUTER Int.rec on a: `fun m : Nat => <inner rec on b>`.
    let outer_negsucc = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ob.fresh_local(c.nat_type.clone());
        let a_val = c.neg_succ(m.clone());
        let inner_motive = le_total_inner_motive(c, &ob, &a_val);
        // inner ofNat (n): a = negSucc m, b = ofNat n -> Or.inl.
        let inner_ofnat = le_total_negsucc_ofnat_with_m(c, &ob, &m);
        let inner_negsucc = le_total_negsucc_negsucc(c, &ob, &snn_total, &m);
        let (bvar_id, bvar) = ob.fresh_local(c.int_type.clone());
        let inner_rec = Expr::apps(
            c.int_rec_prop.clone(),
            [inner_motive, inner_ofnat, inner_negsucc, bvar.clone()],
        );
        let lam_b = ob.mk_lam(bvar_id, BinderInfo::Default, c.int_type.clone(), inner_rec);
        let lam_m = ob.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), lam_b);
        ob.finish_child(lam_m)
    };

    // @Int.rec.{1} outer_motive outer_ofnat outer_negsucc a : (∀ b, …); apply b.
    let outer_rec = Expr::apps(
        c.int_rec_prop.clone(),
        [outer_motive, outer_ofnat, outer_negsucc, a.clone()],
    );
    let applied = Expr::app(outer_rec, bv.clone());

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.int_type.clone(), applied);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), e);
    b.finish(e)
}

/// ofNat m fixed, inner ofNat n: build the `fun n : Nat => …` minor for the
/// inner `Int.rec` on b, with the outer `m` already bound.
fn le_total_ofnat_ofnat_with_m(
    c: &IntLeTotalConsts,
    parent: &EnvDeclBuilder,
    snn_total: &Expr,
    m: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = mb.fresh_local(c.nat_type.clone());
    let int_m = c.of_nat(m.clone());
    let int_n = c.of_nat(n.clone());

    let goal_left = c.nonneg_of(c.sub(int_n.clone(), int_m.clone()));
    let goal_right = c.nonneg_of(c.sub(int_m.clone(), int_n.clone()));
    let goal = Expr::apps(c.or_const.clone(), [goal_left.clone(), goal_right.clone()]);

    let a_prop = c.nonneg_of(c.snn(n.clone(), m.clone()));
    let b_prop = c.nonneg_of(c.snn(m.clone(), n.clone()));
    let h = Expr::apps(snn_total.clone(), [n.clone(), m.clone()]);

    let or_motive = {
        let mut om = EnvDeclBuilder::child_of(&mb);
        let or_ab = Expr::apps(c.or_const.clone(), [a_prop.clone(), b_prop.clone()]);
        let (hh_id, _hh) = om.fresh_local(or_ab.clone());
        let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
        om.finish_child(lam)
    };

    let snn_nm = c.snn(n.clone(), m.clone());
    let sub_nm = c.sub(int_n.clone(), int_m.clone());
    let case_inl = {
        let mut ic = EnvDeclBuilder::child_of(&mb);
        let (h_id, hh) = ic.fresh_local(a_prop.clone());
        let eq = Expr::apps(c.sub_nat_nat_eq_add.clone(), [n.clone(), m.clone()]);
        let lifted = c.nonneg_subst(&ic, snn_nm.clone(), sub_nm.clone(), eq, hh);
        let body = Expr::apps(
            c.or_inl.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), body);
        ic.finish_child(lam)
    };

    let snn_mn = c.snn(m.clone(), n.clone());
    let sub_mn = c.sub(int_m.clone(), int_n.clone());
    let case_inr = {
        let mut rc = EnvDeclBuilder::child_of(&mb);
        let (h_id, hh) = rc.fresh_local(b_prop.clone());
        let eq = Expr::apps(c.sub_nat_nat_eq_add.clone(), [m.clone(), n.clone()]);
        let lifted = c.nonneg_subst(&rc, snn_mn.clone(), sub_mn.clone(), eq, hh);
        let body = Expr::apps(
            c.or_inr.clone(),
            [goal_left.clone(), goal_right.clone(), lifted],
        );
        let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
        rc.finish_child(lam)
    };

    let or_rec_app = Expr::apps(
        c.or_rec.clone(),
        [a_prop, b_prop, or_motive, case_inl, case_inr, h],
    );
    let lam_n = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), or_rec_app);
    mb.finish_child(lam_n)
}

/// ofNat m fixed, inner negSucc n (a = ofNat m, b = negSucc n):
///   `sub a b ≡ ofNat (Nat.add m (Nat.succ n))` → `Or.inr (NonNeg.mk …)`.
fn le_total_ofnat_negsucc_with_m(c: &IntLeTotalConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = mb.fresh_local(c.nat_type.clone());
    let int_m = c.of_nat(m.clone());
    let neg_n = c.neg_succ(n.clone());
    // a = ofNat m, b = negSucc n.
    let goal_left = c.nonneg_of(c.sub(neg_n.clone(), int_m.clone())); // sub b a
    let goal_right = c.nonneg_of(c.sub(int_m.clone(), neg_n.clone())); // sub a b
                                                                       // sub a b ≡ ofNat (Nat.add m (Nat.succ n)); witness:
    let k = c.nat_add(m.clone(), c.succ(n.clone()));
    let witness = c.nonneg_mk(k);
    let body = Expr::apps(c.or_inr.clone(), [goal_left, goal_right, witness]);
    let lam_n = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam_n)
}

/// negSucc m fixed, inner ofNat n (a = negSucc m, b = ofNat n):
///   `sub b a ≡ ofNat (Nat.add n (Nat.succ m))` → `Or.inl (NonNeg.mk …)`.
fn le_total_negsucc_ofnat_with_m(c: &IntLeTotalConsts, parent: &EnvDeclBuilder, m: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = mb.fresh_local(c.nat_type.clone());
    let neg_m = c.neg_succ(m.clone());
    let int_n = c.of_nat(n.clone());
    // a = negSucc m, b = ofNat n.
    let goal_left = c.nonneg_of(c.sub(int_n.clone(), neg_m.clone())); // sub b a
    let goal_right = c.nonneg_of(c.sub(neg_m.clone(), int_n.clone())); // sub a b
                                                                       // sub b a ≡ ofNat (Nat.add n (Nat.succ m)); witness:
    let k = c.nat_add(n.clone(), c.succ(m.clone()));
    let witness = c.nonneg_mk(k);
    let body = Expr::apps(c.or_inl.clone(), [goal_left, goal_right, witness]);
    let lam_n = mb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam_n)
}

impl Environment {
    /// Register `Int.le_total` as a kernel-checked `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_int_ord()` has registered `Int.le`, `Int.NonNeg`,
    ///           `Int.NonNeg.mk`, `Int.sub`, `Int.add`, `Int.neg`, `Int.ofNat`,
    ///           `Int.negSucc`, `Int.subNatNat`, `Int.rec`.
    /// REQUIRES: `self.init_or()` has registered `Or`, `Or.inl`, `Or.inr`,
    ///           `Or.rec`; `self.init_eq()` has registered `Eq.subst` /
    ///           `Eq.symm`.
    /// REQUIRES: the constructive `Int.subNatNat_eq_add` /
    ///           `Int.subNatNat_succ_succ` theorems (registered below).
    /// ENSURES: On success, `Int.le_total` is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — if `Int.le_total` is already registered with any
    ///          declaration kind, this call returns `Ok(())` without
    ///          modification.
    pub(crate) fn register_int_le_total_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.le_total");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_ord()?;
        self.init_or()?;
        self.init_eq()?;
        // Constructive subNatNat bridge lemmas.
        self.register_int_sub_nat_nat_eq_add_proof()?;
        self.register_int_sub_nat_nat_succ_succ_proof()?;

        let c = IntLeTotalConsts::new();
        let type_ = le_total_type(&c);
        let value = le_total_value(&c);

        // SOUNDNESS: Real kernel-checked proof term (replacing the prior
        // `Declaration::Axiom` in `order_int.rs::init_int_linear_order`). The
        // goal `Or (Int.le a b) (Int.le b a)` delta-reduces to
        // `Or (NonNeg (sub b a)) (NonNeg (sub a b))`. An inline
        // `subNatNat_total : ∀ m n, Or (NonNeg (subNatNat m n)) (NonNeg (subNatNat n m))`
        // helper (double `Nat.rec`/`Nat.casesOn`/`Or.rec` induction, mirroring
        // `Nat.le_total`, lifting the IH through `Int.subNatNat_succ_succ`)
        // discharges the two same-sign branches of a `@Int.rec`×`@Int.rec`
        // split, transported onto the `Int.sub` goal via `Int.subNatNat_eq_add`
        // / `Int.subNatNat_succ_succ` and `@Eq.subst.{1}`; the two mixed-sign
        // branches reduce definitionally to `NonNeg (ofNat …)` and close with
        // `@Int.NonNeg.mk`. No `sorry`, no self-reference, no domain-axiom
        // dependency (`Int.subNatNat_eq_add` / `Int.subNatNat_succ_succ` are
        // constructive `Declaration::Theorem`s; the recursors, `Or`/`Eq`
        // primitives are foundational).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// Kernel accepts the proof term; registered as a Theorem (not Axiom),
    /// idempotently, and type-checks.
    #[test]
    fn test_int_le_total_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_le_total_proof()
            .expect("first registration");
        env.register_int_le_total_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Int.le_total"))
            .expect("Int.le_total should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Int.le_total"), vec![]))
            .expect("Int.le_total should type-check");
    }

    /// `init_int_linear_order` registers `Int.le_total` as the constructive
    /// Theorem (not the legacy Axiom), and the whole hierarchy still builds.
    #[test]
    fn test_init_int_linear_order_registers_le_total_theorem() {
        let mut env = Environment::new();
        env.init_int_linear_order().expect("linear order init");
        let info = env
            .get_const(&Name::from_string("Int.le_total"))
            .expect("Int.le_total should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Int.le_total must be a Theorem after init_int_linear_order"
        );
    }

    /// After peeling the two outer λ binders (a, b), the proof root is
    /// `@Int.rec` — guards against an axiom-reference masquerade.
    #[test]
    fn test_int_le_total_proof_uses_int_rec() {
        let mut env = Environment::new();
        env.register_int_le_total_proof().unwrap();
        let info = env
            .get_const(&Name::from_string("Int.le_total"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..2 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Int.rec",
                "Int.le_total proof root must be Int.rec"
            ),
            k => panic!("expected Const(Int.rec, ..), got {:?}", k),
        }
    }

    /// Axiom closure is empty (constructive).
    #[test]
    fn test_int_le_total_axiom_deps_empty() {
        let mut env = Environment::new();
        env.register_int_le_total_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("Int.le_total"))
            .expect("registered, axiom_deps should return Some");
        let domain_deps: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            domain_deps.is_empty(),
            "Int.le_total must have empty axiom closure (constructive proof), got {:?}",
            domain_deps
        );
    }

    /// Proof quality is `Constructive`.
    #[test]
    fn test_int_le_total_proof_quality_constructive() {
        let mut env = Environment::new();
        env.register_int_le_total_proof().unwrap();
        let quality = env
            .proof_quality(&Name::from_string("Int.le_total"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.le_total must be Constructive, got {:?}",
            quality
        );
    }
}

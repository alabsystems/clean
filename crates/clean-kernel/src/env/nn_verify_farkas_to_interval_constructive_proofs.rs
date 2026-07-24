// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type/proof-term builders for the constructive Farkas-to-bound theorem.
//!
//! Split out of `nn_verify_farkas_to_interval_constructive.rs` to keep that
//! module under the 500-line limit, matching the existing
//! `nn_verify_farkas_list` / `nn_verify_farkas_list_proofs` split.
//!
//! These build, over the same `List Row = (mu, a, b)` representation used by
//! `NNVerify.farkas_combine_list`:
//!
//! - the value of the real `NNVerify.farkasCertificateValid` *definition*
//!   (NOT an opaque axiom predicate):
//!     `farkasCertificateValid rows bound
//!        := And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`,
//!   which carries BOTH the per-row premises (`farkasRowsValid`, i.e. each
//!   `0 ≤ muᵢ ∧ aᵢ ≤ bᵢ`) AND the dominating-constant condition
//!   (`farkasUpper rows ≤ bound`, i.e. `Σ muᵢ*bᵢ ≤ bound`); and
//!
//! - the proof term of `NNVerify.farkas_to_interval_constructive`:
//!     `∀ (rows : List Row) (bound : Rat),
//!        farkasCertificateValid rows bound → farkasLower rows ≤ bound`,
//!   discharged constructively by
//!     `Rat.le_trans (farkasLower rows) (farkasUpper rows) bound
//!        (@farkas_combine_list rows (And.left hcert))   -- lower ≤ upper
//!        (And.right hcert)`                              -- upper ≤ bound
//!   i.e. the n-row combination `farkas_combine_list` chained with the
//!   dominating bound, exactly the Farkas → bound fact. No opaque predicate,
//!   no `sorry`: the transitive axiom closure is only honest `Rat`
//!   ordered-field axioms (those under `farkas_combine_list` plus
//!   `Rat.le_trans`).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the constructive Farkas-to-bound theorem, built over
/// the `List Row` encoding shared with `farkas_combine_list`.
pub(super) struct FarkasToIntervalConsts {
    rat: Expr,
    prop: Expr,
    prod: Expr, // Prod @{0,0}
    list: Expr, // List @{0}
    le_le: Expr,
    inst_le_rat: Expr,
    le_trans: Expr,     // Rat.le_trans
    and: Expr,          // And
    and_left: Expr,     // And.left
    and_right: Expr,    // And.right
    lower: Expr,        // NNVerify.farkasLower
    upper: Expr,        // NNVerify.farkasUpper
    rows_valid: Expr,   // NNVerify.farkasRowsValid
    combine_list: Expr, // NNVerify.farkas_combine_list
}

impl FarkasToIntervalConsts {
    pub(super) fn new() -> Self {
        let lvl0 = Level::zero();
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::sort(Level::zero()),
            prod: Expr::const_(Name::from_string("Prod"), vec![lvl0.clone(), lvl0.clone()]),
            list: Expr::const_(Name::from_string("List"), vec![lvl0.clone()]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![lvl0]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            lower: Expr::const_(Name::from_string("NNVerify.farkasLower"), vec![]),
            upper: Expr::const_(Name::from_string("NNVerify.farkasUpper"), vec![]),
            rows_valid: Expr::const_(Name::from_string("NNVerify.farkasRowsValid"), vec![]),
            combine_list: Expr::const_(Name::from_string("NNVerify.farkas_combine_list"), vec![]),
        }
    }

    /// `Prod Rat Rat` — the inner `(a, b)` pair type.
    fn pair_ty(&self) -> Expr {
        Expr::app(
            Expr::app(self.prod.clone(), self.rat.clone()),
            self.rat.clone(),
        )
    }

    /// `Row := Prod Rat (Prod Rat Rat)` — the `(mu, a, b)` row type.
    fn row_ty(&self) -> Expr {
        Expr::app(
            Expr::app(self.prod.clone(), self.rat.clone()),
            self.pair_ty(),
        )
    }

    /// `List Row`.
    pub(super) fn rows_ty(&self) -> Expr {
        Expr::app(self.list.clone(), self.row_ty())
    }

    pub(super) fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }

    pub(super) fn prop_ty(&self) -> Expr {
        self.prop.clone()
    }

    /// `LE.le Rat instLERat a b` — i.e. `a ≤ b` at `Rat`.
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    /// `farkasLower rows : Rat`.
    fn lower_app(&self, rows: &Expr) -> Expr {
        Expr::app(self.lower.clone(), rows.clone())
    }

    /// `farkasUpper rows : Rat`.
    fn upper_app(&self, rows: &Expr) -> Expr {
        Expr::app(self.upper.clone(), rows.clone())
    }

    /// `farkasRowsValid rows : Prop`.
    fn rows_valid_app(&self, rows: &Expr) -> Expr {
        Expr::app(self.rows_valid.clone(), rows.clone())
    }

    /// `And a b`.
    fn and_(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), a), b)
    }

    /// `And.left @a @b h`.
    fn and_left_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [a, b, h])
    }

    /// `And.right @a @b h`.
    fn and_right_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [a, b, h])
    }

    /// The body of `farkasCertificateValid rows bound`:
    /// `And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`.
    fn cert_body(&self, rows: &Expr, bound: &Expr) -> Expr {
        self.and_(
            self.rows_valid_app(rows),
            self.rat_le(self.upper_app(rows), bound.clone()),
        )
    }

    /// `farkasCertificateValid rows bound` as a const application — the
    /// hypothesis of the constructive theorem.
    fn cert_app(&self, rows: &Expr, bound: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNVerify.farkasCertificateValid"), vec![]),
            [rows.clone(), bound.clone()],
        )
    }

    /// `@NNVerify.farkas_combine_list rows hv : farkasLower rows ≤ farkasUpper rows`.
    fn apply_combine_list(&self, rows: &Expr, hv: Expr) -> Expr {
        Expr::apps(self.combine_list.clone(), [rows.clone(), hv])
    }

    /// `Rat.le_trans a b c hab hbc : a ≤ c`.
    fn trans(&self, a: Expr, b: Expr, cv: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cv, hab, hbc])
    }
}

// ── farkasCertificateValid : List Row → Rat → Prop ─────────────────────

/// Type of `farkasCertificateValid`: `List Row → Rat → Prop`.
pub(super) fn build_cert_valid_type(c: &FarkasToIntervalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, _rows) = b.fresh_local(c.rows_ty());
    let (bound_id, _bound) = b.fresh_local(c.rat_ty());
    let e = b.mk_pi(bound_id, BinderInfo::Default, c.rat_ty(), c.prop_ty());
    let e = b.mk_pi(rows_id, BinderInfo::Default, c.rows_ty(), e);
    b.finish(e)
}

/// Value of `farkasCertificateValid`:
/// `fun (rows : List Row) (bound : Rat) =>
///    And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`.
pub(super) fn build_cert_valid_value(c: &FarkasToIntervalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());
    let (bound_id, bound) = b.fresh_local(c.rat_ty());
    let body = c.cert_body(&rows, &bound);
    let e = b.mk_lam(bound_id, BinderInfo::Default, c.rat_ty(), body);
    let e = b.mk_lam(rows_id, BinderInfo::Default, c.rows_ty(), e);
    b.finish(e)
}

// ── farkas_to_interval_constructive theorem ────────────────────────────

/// Type: `∀ (rows : List Row) (bound : Rat),
///   farkasCertificateValid rows bound → farkasLower rows ≤ bound`.
pub(super) fn build_to_interval_type(c: &FarkasToIntervalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());
    let (bound_id, bound) = b.fresh_local(c.rat_ty());
    let hyp = c.cert_app(&rows, &bound);
    let concl = c.rat_le(c.lower_app(&rows), bound.clone());
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bound_id, BinderInfo::Default, c.rat_ty(), e);
    let e = b.mk_pi(rows_id, BinderInfo::Default, c.rows_ty(), e);
    b.finish(e)
}

/// Proof term:
/// `fun (rows : List Row) (bound : Rat)
///      (hcert : farkasCertificateValid rows bound) =>
///    Rat.le_trans (farkasLower rows) (farkasUpper rows) bound
///      (@farkas_combine_list rows (And.left … hcert))
///      (And.right … hcert)`.
///
/// `hcert : farkasCertificateValid rows bound` δ/ι-reduces to
/// `And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`, so `And.left`
/// yields the `farkasRowsValid rows` premise that `farkas_combine_list`
/// consumes, and `And.right` yields `farkasUpper rows ≤ bound`. The two
/// chain via `Rat.le_trans` to `farkasLower rows ≤ bound`.
pub(super) fn build_to_interval_proof(c: &FarkasToIntervalConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());
    let (bound_id, bound) = b.fresh_local(c.rat_ty());
    let hyp = c.cert_app(&rows, &bound);
    let (h_id, h) = b.fresh_local(hyp.clone());

    // The reduced shape of the certificate hypothesis: the two And-conjuncts.
    let valid_prop = c.rows_valid_app(&rows);
    let dom_prop = c.rat_le(c.upper_app(&rows), bound.clone());

    // h_valid : farkasRowsValid rows         (And.left)
    // h_dom   : farkasUpper rows ≤ bound      (And.right)
    let h_valid = c.and_left_app(valid_prop.clone(), dom_prop.clone(), h.clone());
    let h_dom = c.and_right_app(valid_prop, dom_prop, h);

    // lower ≤ upper, via the n-row combination theorem.
    let lower = c.lower_app(&rows);
    let upper = c.upper_app(&rows);
    let combined = c.apply_combine_list(&rows, h_valid);

    // Rat.le_trans lower upper bound combined h_dom : lower ≤ bound.
    let body = c.trans(lower, upper, bound.clone(), combined, h_dom);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(bound_id, BinderInfo::Default, c.rat_ty(), e);
    let e = b.mk_lam(rows_id, BinderInfo::Default, c.rows_ty(), e);
    b.finish(e)
}

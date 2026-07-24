// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C007 expression constants and type builders — ZERO DOMAIN AXIOMS.
//!
//! Defines `C007Consts` (shared expression atoms) used by the theorem type
//! and proof builders. All declarations are now `Declaration::Opaque` or
//! `Declaration::Theorem` — zero `Declaration::Axiom` entries remain (#3381).
//!
//! See the AXIOM-DEPENDENT header in `nn_verify_streaming_certs.rs` for full
//! C007 status. See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ## Key types (all axiom-declared)
//!
//! - `NNVerify.C007.BaBCert d` — verification certificate for a BaB subproblem
//!   over input region `IntervalBounds d`
//! - `NNVerify.C007.cert_sound` — a certificate is sound if its claimed bounds
//!   contain all reachable outputs
//! - `NNVerify.C007.merge_cert` — merges two certificates for disjoint
//!   sub-regions into one for the union
//! - `NNVerify.C007.restrict_cert` — restricts a certificate to a sub-region
//! - `NNVerify.C007.cert_cost` — cost metric for a certificate (Nat-valued)
//! - `NNVerify.C007.delta_cost` — cost of an incremental update delta (Nat)
//!
//! Part of #3312, #3150.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C007 streaming certificate theorem construction.
pub(super) struct C007Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) ib_subset: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) le_nat: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) rat_add: Expr,
    pub(super) nat_add: Expr,
    pub(super) and: Expr,
    pub(super) eq: Expr,
    pub(super) eq_refl: Expr,
    // C007-specific symbols
    pub(super) bab_cert: Expr,
    pub(super) cert_sound: Expr,
    pub(super) merge_cert: Expr,
    pub(super) restrict_cert: Expr,
    pub(super) cert_cost: Expr,
    pub(super) delta_cost: Expr,
    pub(super) disjoint_cover: Expr,
    // Helper axioms
    pub(super) merge_sound_helper: Expr,
    pub(super) restrict_refines_helper: Expr,
    pub(super) incremental_cost_helper: Expr,
}

impl C007Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            le_nat: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            eq_refl: Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            bab_cert: Expr::const_(Name::from_string("NNVerify.C007.BaBCert"), vec![]),
            cert_sound: Expr::const_(Name::from_string("NNVerify.C007.cert_sound"), vec![]),
            merge_cert: Expr::const_(Name::from_string("NNVerify.C007.merge_cert"), vec![]),
            restrict_cert: Expr::const_(Name::from_string("NNVerify.C007.restrict_cert"), vec![]),
            cert_cost: Expr::const_(Name::from_string("NNVerify.C007.cert_cost"), vec![]),
            delta_cost: Expr::const_(Name::from_string("NNVerify.C007.delta_cost"), vec![]),
            disjoint_cover: Expr::const_(Name::from_string("NNVerify.C007.disjoint_cover"), vec![]),
            merge_sound_helper: Expr::const_(
                Name::from_string("NNVerify.C007.merge_sound_helper"),
                vec![],
            ),
            restrict_refines_helper: Expr::const_(
                Name::from_string("NNVerify.C007.restrict_refines_helper"),
                vec![],
            ),
            incremental_cost_helper: Expr::const_(
                Name::from_string("NNVerify.C007.incremental_cost_helper"),
                vec![],
            ),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    pub(super) fn cert_of(&self, d: &Expr) -> Expr {
        Expr::app(self.bab_cert.clone(), d.clone())
    }

    /// `IntervalBounds.contains @d B x`
    pub(super) fn contains(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }

    /// `IntervalBounds.subset @d B1 B2`
    pub(super) fn subset(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }

    /// `cert_sound @d B c`
    pub(super) fn sound(&self, d: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.cert_sound.clone(), d.clone()), b.clone()),
            c.clone(),
        )
    }

    /// `merge_cert @d c1 c2`
    pub(super) fn merge(&self, d: &Expr, c1: &Expr, c2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.merge_cert.clone(), d.clone()), c1.clone()),
            c2.clone(),
        )
    }

    /// `restrict_cert @d c B_sub`
    pub(super) fn restrict(&self, d: &Expr, c: &Expr, b_sub: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.restrict_cert.clone(), d.clone()), c.clone()),
            b_sub.clone(),
        )
    }

    /// `cert_cost @d c`
    pub(super) fn cost(&self, d: &Expr, c: &Expr) -> Expr {
        Expr::app(Expr::app(self.cert_cost.clone(), d.clone()), c.clone())
    }

    /// `delta_cost @d c1 c2`
    pub(super) fn dcost(&self, d: &Expr, c1: &Expr, c2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.delta_cost.clone(), d.clone()), c1.clone()),
            c2.clone(),
        )
    }

    /// `disjoint_cover @d B1 B2 B0`
    pub(super) fn disj_cover(&self, d: &Expr, b1: &Expr, b2: &Expr, b0: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.disjoint_cover.clone(), d.clone()),
                    b1.clone(),
                ),
                b2.clone(),
            ),
            b0.clone(),
        )
    }

    pub(super) fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_nat.clone(), self.nat.clone()),
                    self.inst_le_nat.clone(),
                ),
                a,
            ),
            b,
        )
    }

    pub(super) fn add_nat(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), a), b)
    }

    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }
}

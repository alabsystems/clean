// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Orbit-CROWN symmetry quotienting types and operations (C030).
//!
//! **Status:** C030 has ZERO `Declaration::Axiom` entries.
//! 3 `Declaration::Opaque` entries (sorry-inhabited claims C030a/b/d, formerly axioms),
//! 2 `Declaration::Definition` (Nat.div, Equivariant), and
//! 8 `Declaration::Opaque` entries (SymmetryGroup, GroupAction, QuotientSpace,
//! OrbitBound, GroupOrder, quotient_project, crown_on_quotient, crown_on_full).
//!
//! Originally all 13 declarations were axioms ("pure axiom dump"). Bulk
//! classification reduced axioms from 13 to 3 by converting type constructors
//! and computable functions to Opaque, and standard definitions to Definition.
//!
//! File layout:
//! - This file: `OrbitCrownConsts` struct + `init_nn_verify_orbit_crown`
//! - `nn_verify_orbit_crown_defs`: infrastructure registrations (Definitions + Opaques)
//! - `nn_verify_orbit_crown_theorems`: C030a/b/d trust envelopes plus the
//!   hypothesis-wrapped C030c theorem

use crate::env::{EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for Orbit-CROWN declaration construction.
///
/// Visible to `nn_verify_orbit_crown_defs` and `nn_verify_orbit_crown_theorems`.
pub(super) struct OrbitCrownConsts {
    pub(super) nat: Expr,
    pub(super) type0: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) eq: Expr,
    pub(super) exists_: Expr,
    #[cfg(test)]
    pub(super) nat_div: Expr,
    pub(super) symmetry_group: Expr,
    pub(super) equivariant: Expr,
    pub(super) orbit_bound: Expr,
    pub(super) group_order: Expr,
    pub(super) quotient_project: Expr,
    pub(super) crown_on_quotient: Expr,
    pub(super) crown_on_full: Expr,
    pub(super) ib_subset: Expr,
    pub(super) fin: Expr,
    pub(super) rat_zero: Expr,
    pub(super) ib_mk: Expr,
}

impl OrbitCrownConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::sort(Level::zero()),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            exists_: Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            #[cfg(test)]
            nat_div: Expr::const_(Name::from_string("Nat.div"), vec![]),
            symmetry_group: Expr::const_(
                Name::from_string("NNVerify.OrbitCROWN.SymmetryGroup"),
                vec![],
            ),
            equivariant: Expr::const_(Name::from_string("NNVerify.OrbitCROWN.Equivariant"), vec![]),
            orbit_bound: Expr::const_(Name::from_string("NNVerify.OrbitCROWN.OrbitBound"), vec![]),
            group_order: Expr::const_(Name::from_string("NNVerify.OrbitCROWN.GroupOrder"), vec![]),
            quotient_project: Expr::const_(
                Name::from_string("NNVerify.OrbitCROWN.quotient_project"),
                vec![],
            ),
            crown_on_quotient: Expr::const_(
                Name::from_string("NNVerify.OrbitCROWN.crown_on_quotient"),
                vec![],
            ),
            crown_on_full: Expr::const_(
                Name::from_string("NNVerify.OrbitCROWN.crown_on_full"),
                vec![],
            ),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    pub(super) fn sym_group_of(&self, n: &Expr) -> Expr {
        Expr::app(self.symmetry_group.clone(), n.clone())
    }

    /// Non-dependent function type `NNVec d_in -> NNVec d_out`.
    ///
    /// Uses raw `Expr::pi` instead of `EnvDeclBuilder` because the binder
    /// variable is not referenced in the codomain, and the arguments may
    /// contain FVars from an outer builder that would trip `finish()`.
    pub(super) fn vec_fn_ty(&self, d_in: &Expr, d_out: &Expr) -> Expr {
        let dom = self.vec_of(d_in);
        let cod = self.vec_of(d_out);
        Expr::pi(BinderInfo::Default, dom, cod)
    }

    pub(super) fn nat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.nat.clone()),
                    self.inst_le_nat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    pub(super) fn eq_of(&self, alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), alpha), lhs), rhs)
    }

    pub(super) fn exists_of(&self, witness_ty: Expr, pred: Expr) -> Expr {
        Expr::app(Expr::app(self.exists_.clone(), witness_ty), pred)
    }

    pub(super) fn equivariant_app(&self, d_in: &Expr, d_out: &Expr, f: Expr, g: Expr) -> Expr {
        Expr::apps(
            self.equivariant.clone(),
            [d_in.clone(), d_out.clone(), f, g],
        )
    }

    pub(super) fn orbit_bound_app(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::app(Expr::app(self.orbit_bound.clone(), n.clone()), g.clone())
    }

    pub(super) fn group_order_app(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::app(Expr::app(self.group_order.clone(), n.clone()), g.clone())
    }

    pub(super) fn quotient_project_app(&self, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.quotient_project.clone(),
            [n.clone(), g.clone(), x.clone()],
        )
    }

    pub(super) fn crown_on_quotient_app(
        &self,
        d_in: &Expr,
        d_out: &Expr,
        f: Expr,
        g: Expr,
        b_q: Expr,
    ) -> Expr {
        Expr::apps(
            self.crown_on_quotient.clone(),
            [d_in.clone(), d_out.clone(), f, g, b_q],
        )
    }

    pub(super) fn crown_on_full_app(
        &self,
        d_in: &Expr,
        d_out: &Expr,
        f: Expr,
        g: Expr,
        b_q: Expr,
    ) -> Expr {
        Expr::apps(
            self.crown_on_full.clone(),
            [d_in.clone(), d_out.clone(), f, g, b_q],
        )
    }

    pub(super) fn ib_subset_app(&self, d: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.ib_subset.clone(), [d.clone(), lhs, rhs])
    }

    #[cfg(test)]
    pub(super) fn div_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.nat_div.clone(), lhs), rhs)
    }

    /// Construct `Nat.mul lhs rhs`.
    ///
    /// #3564: Used by the C030d sharp orbit-stabilizer bound
    /// `|Orbit| * |G| <= d_in` (multiplicative form of the division
    /// inequality `|Orbit| <= d_in / |G|`).
    pub(super) fn mul_nat(&self, lhs: Expr, rhs: Expr) -> Expr {
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        Expr::app(Expr::app(nat_mul, lhs), rhs)
    }

    /// Construct `Fin n` where `n : Nat`.
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
}

impl Environment {
    /// Initialize Orbit-CROWN symmetry quotienting declarations (C030).
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for `NNVec` and `IntervalBounds`
    /// - `init_nn_verify_crown_layernorm()` for shared CROWN overlay deps
    /// - `init_rat_arith()` for shared arithmetic overlay deps
    /// - `init_eq()` for `Eq`
    /// - `init_exists()` for the existential factoring theorem
    /// - `init_le()` for `LE.le @Nat instLENat` in C030c
    /// - `init_nat_preorder()` for shared Nat ordering declarations used by
    ///   other math-overlay registrations
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_orbit_crown(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_orbit_crown_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_nn_verify_crown_layernorm()?;
        self.init_rat_arith()?;
        self.init_eq()?;
        self.init_exists()?;
        self.init_le()?;
        // init_nat_preorder is idempotent and pulls init_le() transitively.
        self.init_nat_preorder()?;

        let c = OrbitCrownConsts::new();
        self.register_orbit_crown_nat_div()?;
        self.register_symmetry_group_type(&c)?;
        self.register_group_action(&c)?;
        self.register_equivariant(&c)?;
        self.register_quotient_space(&c)?;
        self.register_orbit_bound(&c)?;
        self.register_group_order(&c)?;
        self.register_quotient_project(&c)?;
        self.register_crown_on_quotient(&c)?;
        self.register_crown_on_full(&c)?;
        self.register_c030a_equivariant_factors(&c)?;
        self.register_c030b_quotient_crown_sound(&c)?;
        self.register_c030c_verification_speedup(&c)?;
        // #3564: Sharp orbit-stabilizer bound `|Orbit| * |G| <= d_in`.
        // Registered as Opaque with sorry_inhabit_pi, mirroring the
        // C030a/C030b honest-stub pattern. See
        // `register_c030d_orbit_stabilizer_sharp` for the full rationale.
        self.register_c030d_orbit_stabilizer_sharp(&c)?;

        self.nn_verify_orbit_crown_init = true;
        Ok(())
    }
}

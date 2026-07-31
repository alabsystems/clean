// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat min/max ordering lemmas
//!
//! Split from order_lemmas.rs (#307). Contains:
//! - Min lemmas (min_le_left, min_le_right, le_min, min_comm)
//! - Max lemmas (le_max_left, le_max_right, max_le, max_comm)

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Nat min/max ordering lemmas
    ///
    /// Registers 8 lemmas: min_le_left, min_le_right, le_min, min_comm,
    ///                      le_max_left, le_max_right, max_le, max_comm.
    ///
    /// #3604: all eight are now demoted to constructive `Declaration::Theorem`s
    /// by `register_nat_minmax_proofs` (see `order_lemmas_minmax_proofs.rs`),
    /// registered *before* the legacy axiom block below. Each `add_nat_*` site
    /// is guarded by a `get_const` check and becomes an idempotent no-op once
    /// the Theorem form is present, so the constructive form always wins.
    pub(crate) fn init_nat_minmax_lemmas(&mut self) -> Result<(), EnvError> {
        if self.nat_minmax_lemmas_init {
            return Ok(());
        }
        self.init_nat_minmax()?;
        self.init_le()?;
        self.init_eq()?;

        // #3604: constructive demotion. Registered first so the Theorem form
        // wins; the legacy axiom sites below short-circuit via `get_const`.
        self.register_nat_minmax_proofs()?;

        self.add_nat_min_le_left()?;
        self.add_nat_min_le_right()?;
        self.add_nat_le_min()?;
        self.add_nat_min_comm()?;
        self.add_nat_le_max_left()?;
        self.add_nat_le_max_right()?;
        self.add_nat_max_le()?;
        self.add_nat_max_comm()?;

        self.nat_minmax_lemmas_init = true;
        Ok(())
    }

    fn add_nat_min_le_left(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let min = Expr::const_(Name::from_string("Nat.min"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let min_ab = Expr::app(Expr::app(min, a.clone()), bv);
        let body = Expr::app(Expr::app(le, min_ab), a);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.min_le_left"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.min_le_left"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_min_le_right(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let min = Expr::const_(Name::from_string("Nat.min"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let min_ab = Expr::app(Expr::app(min, a), bv.clone());
        let body = Expr::app(Expr::app(le, min_ab), bv);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.min_le_right"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.min_le_right"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_le_min(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let min = Expr::const_(Name::from_string("Nat.min"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let (c_id, c) = b.fresh_local(nat.clone());
        let le_c_a = Expr::app(Expr::app(le.clone(), c.clone()), a.clone());
        let le_c_b = Expr::app(Expr::app(le.clone(), c.clone()), bv.clone());
        let min_ab = Expr::app(Expr::app(min, a), bv);
        let body = Expr::app(Expr::app(le, c), min_ab);
        let (h1_id, _) = b.fresh_local(le_c_a.clone());
        let (h2_id, _) = b.fresh_local(le_c_b.clone());
        let e = b.mk_pi(h2_id, BinderInfo::Default, le_c_b, body);
        let e = b.mk_pi(h1_id, BinderInfo::Default, le_c_a, e);
        let e = b.mk_pi(c_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self.get_const(&Name::from_string("Nat.le_min")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.le_min"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_min_comm(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let min = Expr::const_(Name::from_string("Nat.min"), vec![]);
        let eq_nat = Expr::app(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            nat.clone(),
        );
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let min_ab = Expr::app(Expr::app(min.clone(), a.clone()), bv.clone());
        let min_ba = Expr::app(Expr::app(min, bv), a);
        let body = Expr::app(Expr::app(eq_nat, min_ab), min_ba);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self.get_const(&Name::from_string("Nat.min_comm")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.min_comm"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_le_max_left(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let max = Expr::const_(Name::from_string("Nat.max"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let max_ab = Expr::app(Expr::app(max, a.clone()), bv);
        let body = Expr::app(Expr::app(le, a), max_ab);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.le_max_left"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.le_max_left"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_le_max_right(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let max = Expr::const_(Name::from_string("Nat.max"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let max_ab = Expr::app(Expr::app(max, a), bv.clone());
        let body = Expr::app(Expr::app(le, bv), max_ab);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self
            .get_const(&Name::from_string("Nat.le_max_right"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.le_max_right"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_max_le(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let max = Expr::const_(Name::from_string("Nat.max"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let (c_id, c) = b.fresh_local(nat.clone());
        let le_a_c = Expr::app(Expr::app(le.clone(), a.clone()), c.clone());
        let le_b_c = Expr::app(Expr::app(le.clone(), bv.clone()), c.clone());
        let max_ab = Expr::app(Expr::app(max, a), bv);
        let body = Expr::app(Expr::app(le, max_ab), c);
        let (h1_id, _) = b.fresh_local(le_a_c.clone());
        let (h2_id, _) = b.fresh_local(le_b_c.clone());
        let e = b.mk_pi(h2_id, BinderInfo::Default, le_b_c, body);
        let e = b.mk_pi(h1_id, BinderInfo::Default, le_a_c, e);
        let e = b.mk_pi(c_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self.get_const(&Name::from_string("Nat.max_le")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.max_le"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    fn add_nat_max_comm(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let max = Expr::const_(Name::from_string("Nat.max"), vec![]);
        let eq_nat = Expr::app(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            nat.clone(),
        );
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat.clone());
        let (b_id, bv) = b.fresh_local(nat.clone());
        let max_ab = Expr::app(Expr::app(max.clone(), a.clone()), bv.clone());
        let max_ba = Expr::app(Expr::app(max, bv), a);
        let body = Expr::app(Expr::app(eq_nat, max_ab), max_ba);
        let e = b.mk_pi(b_id, BinderInfo::Default, nat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, nat, e);
        // #3604: skipped when the constructive Theorem form is present.
        if self.get_const(&Name::from_string("Nat.max_comm")).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.max_comm"),
            level_params: vec![],
            type_: b.finish(e),
        })
    }

    #[cfg(test)]
    pub(crate) fn has_nat_minmax_lemmas(&self) -> bool {
        self.nat_minmax_lemmas_init
    }
}

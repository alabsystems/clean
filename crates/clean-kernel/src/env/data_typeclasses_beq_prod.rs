// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The parametric `BEq (α × β)` instance.
//!
//! Lean ground truth, `Init/Core.lean` (v4.8.0, line 1171):
//!
//! ```lean
//! instance [BEq α] [BEq β] : BEq (α × β) where
//!   beq := fun (a₁, b₁) (a₂, b₂) => a₁ == a₂ && b₁ == b₂
//! ```
//!
//! `#print instBEqProd` under `pp.all` (v4.8.0 and v4.30.0-rc2, measured
//! 2026-09-30) gives the type
//! `{α : Type u_1} → {β : Type u_2} → [BEq.{u_1} α] → [BEq.{u_2} β] →
//! BEq.{max u_2 u_1} (Prod.{u_1, u_2} α β)` — the `max u_2 u_1` order is
//! spelled here exactly, so the prelude declaration is type-EQUAL to Lean's
//! and adds no row to `data/prelude_collision_census.json`.
//!
//! Lean's body splits both pairs with a matcher (`instDecidableEqProd.match_2`,
//! i.e. `Prod.casesOn`). This one projects (`Prod.fst` / `Prod.snd`): the two
//! are definitionally equal on every pair, closed or open, because Lean's
//! kernel η-expands a structure-typed major premise before ι-reduction, so the
//! matcher on a variable `p` reduces to the same `p.1` / `p.2` comparison. The
//! conjunction is `and`, the constant `&&` elaborates to.
//!
//! Without this instance `x == y` at `Nat × Int` — and therefore at
//! `Option (Nat × Int)` through `instBEqOption` — failed to synthesize, which
//! is what refused trust-ir's `Pred.lean` (`membersContainKey`, `insertByKey`,
//! `constBeq`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `instBEqProd` (module docs).
    ///
    /// Runs at the tail of `init_beq`. IMPORT MODE
    /// (`suppress_lossy_structure_stubs`): skipped, like `instBEqOption` and
    /// `instBEqList` beside it — the genuine Lean instance of the same name
    /// imports through the checked path, and a prelude stub would shadow it
    /// (`.olean` import is first-registered-wins). A cut-down environment
    /// without `Prod` or `and` skips it, keeping the "failed to synthesize"
    /// refusal rather than failing prelude construction.
    pub(crate) fn init_beq_prod(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let registered =
            |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();
        if !registered(self, "Prod.fst")
            || !registered(self, "Prod.snd")
            || !registered(self, "and")
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        // Lean's serialized order: `BEq.{max u_2 u_1}`.
        let beq_level = Level::max(v_level.clone(), u_level.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_level.clone())));
        let beq_at = |level: &Level, carrier: Expr| {
            Expr::app(
                Expr::const_(Name::from_string("BEq"), vec![level.clone()]),
                carrier,
            )
        };
        let prod_levels = vec![u_level.clone(), v_level.clone()];
        let prod_of = |a: &Expr, b: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Prod"), prod_levels.clone()),
                [a.clone(), b.clone()],
            )
        };
        let project = |field: &str, a: &Expr, b: &Expr, p: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string(field), prod_levels.clone()),
                [a.clone(), b.clone(), p],
            )
        };

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let beq_alpha = beq_at(&u_level, alpha.clone());
            let beq_beta = beq_at(&v_level, beta.clone());
            let (ia_id, _ia) = b.fresh_local(beq_alpha.clone());
            let (ib_id, _ib) = b.fresh_local(beq_beta.clone());
            let r = beq_at(&beq_level, prod_of(&alpha, &beta));
            let r = b.mk_pi(ib_id, BinderInfo::InstImplicit, beq_beta, r);
            let r = b.mk_pi(ia_id, BinderInfo::InstImplicit, beq_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let beq_alpha = beq_at(&u_level, alpha.clone());
            let beq_beta = beq_at(&v_level, beta.clone());
            let (ia_id, ia) = b.fresh_local(beq_alpha.clone());
            let (ib_id, ib) = b.fresh_local(beq_beta.clone());
            let prod_ab = prod_of(&alpha, &beta);

            // fun (x y : α × β) => and (x.1 == y.1) (x.2 == y.2)
            let beq_fn = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(prod_ab.clone());
                let (y_id, y) = c.fresh_local(prod_ab.clone());
                let cmp = |level: &Level, carrier: &Expr, inst: &Expr, field: &str| {
                    Expr::apps(
                        Expr::const_(Name::from_string("BEq.beq"), vec![level.clone()]),
                        [
                            carrier.clone(),
                            inst.clone(),
                            project(field, &alpha, &beta, x.clone()),
                            project(field, &alpha, &beta, y.clone()),
                        ],
                    )
                };
                let body = Expr::apps(
                    Expr::const_(Name::from_string("and"), vec![]),
                    [
                        cmp(&u_level, &alpha, &ia, "Prod.fst"),
                        cmp(&v_level, &beta, &ib, "Prod.snd"),
                    ],
                );
                let r = c.mk_lam(y_id, BinderInfo::Default, prod_ab.clone(), body);
                let r = c.mk_lam(x_id, BinderInfo::Default, prod_ab.clone(), r);
                c.finish_child(r)
            };
            let body = Expr::apps(
                Expr::const_(Name::from_string("BEq.mk"), vec![beq_level.clone()]),
                [prod_ab, beq_fn],
            );
            let r = b.mk_lam(ib_id, BinderInfo::InstImplicit, beq_beta, body);
            let r = b.mk_lam(ia_id, BinderInfo::InstImplicit, beq_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instBEqProd"),
            level_params: vec![u, v],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instBEqProd"),
            class_name: Name::from_string("BEq"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
#[path = "data_typeclasses_beq_prod_tests.rs"]
mod tests;

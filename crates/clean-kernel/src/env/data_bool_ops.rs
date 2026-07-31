// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic `Bool` operations (`Bool.toNat`).
//!
//! Registers the Lean core `Bool.toNat` as a real, fully-checked
//! `Declaration::Definition` (no axioms):
//!
//! ```text
//! @[inline] def Bool.toNat (b : Bool) : Nat := match b with
//!   | false => 0
//!   | true  => 1
//! ```
//!
//! Lean source: `Init/Data/Bool.lean` (toolchain `v4.30.0-rc2`).
//!
//! Registered as a reducible `Bool.rec` fold. The motive folds into `Nat`
//! (`Sort 1`), so the recursor eliminates at the concrete universe `1`
//! (`Bool.rec.{succ zero}`), and — matching `Bool.rec`'s minor-premise order —
//! the `false` case yields `0` and the `true` case yields `1`. Without this
//! constant, `(b : Bool).toNat` failed with `UnknownIdent`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Bool.toNat : Bool → Nat := fun b => Bool.rec 0 1 b`.
    ///
    /// Lean fidelity: `Init/Data/Bool.lean` — `false ↦ 0`, `true ↦ 1`.
    /// Reducible (Clean's defeq-unfolding analog of Lean's `@[inline]`),
    /// value is a `Bool.rec` fold into `Nat`, no axioms.
    ///
    /// Skipped when a `Bool.toNat` constant is already present (e.g. restored
    /// from a real `.olean` import), so an imported definition always wins.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.bool_ops_init == true`
    /// ENSURES: Idempotent — calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_bool_ops(&mut self) -> Result<(), EnvError> {
        if self.bool_ops_init {
            return Ok(());
        }

        // An imported `Bool.toNat` (real olean) takes precedence: never clobber.
        if self.get_const(&Name::from_string("Bool.toNat")).is_none() {
            let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
            let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

            // Bool.toNat : Bool → Nat
            let to_nat_type = {
                let mut b = EnvDeclBuilder::new();
                let (bid, _bvar) = b.fresh_local(bool_const.clone());
                let r = b.mk_pi(
                    bid,
                    BinderInfo::Default,
                    bool_const.clone(),
                    nat_const.clone(),
                );
                b.finish(r)
            };

            // value: fun (b : Bool) => @Bool.rec.{1} (fun _ : Bool => Nat) 0 1 b
            let to_nat_value = {
                let mut b = EnvDeclBuilder::new();
                let (bid, bvar) = b.fresh_local(bool_const.clone());
                // Bool.rec eliminating into Nat (Sort 1): motive universe 1.
                let bool_rec = Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                );
                // motive: fun (_ : Bool) => Nat
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(bool_const.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        bool_const.clone(),
                        nat_const.clone(),
                    );
                    c.finish_child(r)
                };
                // @Bool.rec motive <false=0> <true=1> b
                let body = Expr::apps(bool_rec, [motive, Expr::nat_lit(0), Expr::nat_lit(1), bvar]);
                let r = b.mk_lam(bid, BinderInfo::Default, bool_const.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Bool.toNat"),
                level_params: vec![],
                type_: to_nat_type,
                value: to_nat_value,
                is_reducible: true,
            })?;
        }

        self.bool_ops_init = true;
        Ok(())
    }
}

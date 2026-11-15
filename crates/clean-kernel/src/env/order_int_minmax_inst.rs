// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Min Int` / `Max Int` instances.
//!
//! Lean ground truth, v4.8.0 (`Init/Data/Int/Basic.lean`, lines 332/334, in
//! `namespace Int`):
//!
//! ```lean
//! instance : Min Int := minOfLe
//! instance : Max Int := maxOfLe
//! ```
//!
//! with (`Init/Prelude.lean`, lines 1129/1142)
//!
//! ```lean
//! def maxOfLe [LE α] [DecidableRel (@LE.le α _)] : Max α where
//!   max x y := ite (LE.le x y) y x
//! def minOfLe [LE α] [DecidableRel (@LE.le α _)] : Min α where
//!   min x y := ite (LE.le x y) x y
//! ```
//!
//! `#print Int.instMin` under `pp.all` (pinned v4.8.0 and v4.30.0-rc2,
//! measured 2026-10-04) gives `def Int.instMin : Min.{0} Int :=
//! @minOfLe.{0} Int Int.instLEInt Int.decLe`, and `Int.instMax` the same over
//! `maxOfLe`; both toolchains name them `Int.instMin` / `Int.instMax`
//! (`#synth Min Int`).
//!
//! The prelude has no `DecidableRel` (whose own statement changed between
//! v4.8.0 and v4.30.0-rc2, so neither spelling of `minOfLe`'s type could be
//! registered without a differing-type collision against one of them). Each
//! body here is therefore `minOfLe` / `maxOfLe` already δβ-reduced at
//! `Int`: `Min.mk (fun x y => @ite Int (x ≤ y) (Int.decLe x y) x y)`. That is
//! definitionally equal to Lean's value on every argument, open or closed, so
//! `min n m = if n ≤ m then n else m := rfl` checks here as it does in Lean
//! (`Int.min_def` is proved by `rfl` in v4.8.0 `Init/Data/Int/Order.lean`).
//!
//! Without these instances `min (a : Int) b` failed to synthesize, which
//! refused trust-ir's `TrustIr/Pred.lean` `intBoundsAux`, `intersectBounds` and
//! `hullBounds`, and cascaded through every declaration that names them.
//!
//! IMPORT MODE (`suppress_lossy_structure_stubs`): skipped. The genuine
//! instances import through the checked path under the same names, and a
//! prelude declaration would shadow them (`.olean` import is
//! first-registered-wins) — the same discipline as `instMinNat` /
//! `instMaxNat` (`order_ord.rs`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which of the two instances to build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Extremum {
    /// `minOfLe`: `ite (x ≤ y) x y`.
    Min,
    /// `maxOfLe`: `ite (x ≤ y) y x`.
    Max,
}

impl Extremum {
    fn class(self) -> &'static str {
        match self {
            Self::Min => "Min",
            Self::Max => "Max",
        }
    }

    fn ctor(self) -> &'static str {
        match self {
            Self::Min => "Min.mk",
            Self::Max => "Max.mk",
        }
    }

    fn instance(self) -> &'static str {
        match self {
            Self::Min => "Int.instMin",
            Self::Max => "Int.instMax",
        }
    }
}

impl Environment {
    /// Register `Int.instMin` / `Int.instMax` (module docs). Idempotent; a
    /// no-op in import mode.
    pub(crate) fn init_int_minmax_inst(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("Int.instMin")).is_some() {
            return Ok(());
        }
        self.init_minmax_class()?;
        self.init_ite()?;
        // `instLEInt`, `Int.decLe`.
        self.init_int_decidable_ord()?;

        for extremum in [Extremum::Min, Extremum::Max] {
            self.register_int_extremum_instance(extremum)?;
        }
        Ok(())
    }

    fn register_int_extremum_instance(&mut self, extremum: Extremum) -> Result<(), EnvError> {
        let int = Expr::const_(Name::from_string("Int"), vec![]);
        let class_at_int = Expr::app(
            Expr::const_(Name::from_string(extremum.class()), vec![Level::zero()]),
            int.clone(),
        );

        // fun (x y : Int) => @ite.{1} Int (@LE.le.{0} Int instLEInt x y)
        //                                 (Int.decLe x y) <then> <else>
        let operation = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(int.clone());
            let (y_id, y) = b.fresh_local(int.clone());
            let le = Expr::apps(
                Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                [
                    int.clone(),
                    Expr::const_(Name::from_string("instLEInt"), vec![]),
                    x.clone(),
                    y.clone(),
                ],
            );
            let decision = Expr::apps(
                Expr::const_(Name::from_string("Int.decLe"), vec![]),
                [x.clone(), y.clone()],
            );
            let (then_branch, else_branch) = match extremum {
                Extremum::Min => (x, y),
                Extremum::Max => (y, x),
            };
            let body = Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
                [int.clone(), le, decision, then_branch, else_branch],
            );
            let r = b.mk_lam(y_id, BinderInfo::Default, int.clone(), body);
            let r = b.mk_lam(x_id, BinderInfo::Default, int.clone(), r);
            b.finish(r)
        };
        let value = Expr::apps(
            Expr::const_(Name::from_string(extremum.ctor()), vec![Level::zero()]),
            [int, operation],
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string(extremum.instance()),
            level_params: vec![],
            type_: class_at_int,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(extremum.instance()),
            class_name: Name::from_string(extremum.class()),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
#[path = "order_int_minmax_inst_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! When a later branch may see the FOLDED type of an earlier one (G31's gate).
//!
//! G31 (ledger (101)) hands an `if`'s else-branch, and a `match`'s later
//! alternatives, the first branch's type as written rather than its whnf, as
//! Lean's `elabIf`/`elabMatch` do. Lean then resolves the later branch's
//! instance goals (`Pure M`, `MonadExcept _ M`) at `.instances` transparency,
//! where a semireducible `def M := StateT …` stays folded and NO instance
//! matches: "failed to synthesize instance". Clean's instance search still
//! sees through a semireducible def (G47, ledger (117), another lane), so
//! handing it the folded `M Unit` turned the old wrong-reason refusal into a
//! FALSE ACCEPTANCE (r4 review, `r9`/`r10`).
//!
//! The gate: the folded type is handed on only when Lean's instance search
//! could match it without delta-unfolding a semireducible definition — its
//! reducible whnf is not headed by a semireducible/irreducible definition, or
//! that definition is itself the rigid head of a registered instance's class
//! argument (`StateT`, which `instance : Monad (StateT σ m)` keys on). Otherwise
//! the unfolded type is used exactly as before G31, so the gate never accepts
//! more than integ/r2 did there. `abbrev Sem := StateT …` (trust-ir's shape)
//! passes: its reducible whnf is `StateT …`.
//!
//! Lift the gate when G47 lands (instance search at `.instances`
//! transparency): Lean hands the folded type on unconditionally.

use super::*;

impl<'a> ElabCtx<'a> {
    /// The type a later branch elaborates against: `folded` when
    /// [`Self::folded_type_reaches_instances`], else `unfolded` (the pre-G31
    /// behavior).
    pub(super) fn later_branch_type(&self, folded: Expr, unfolded: Expr) -> Expr {
        if self.folded_type_reaches_instances(&folded) {
            folded
        } else {
            unfolded
        }
    }

    /// Whether instance search can meet `ty` folded without unfolding a
    /// semireducible definition (see the module note).
    pub(super) fn folded_type_reaches_instances(&self, ty: &Expr) -> bool {
        let reduced = self.whnf_reducible(ty);
        let ExprKind::Const(head, _) = reduced.get_app_fn().kind() else {
            return true;
        };
        let Some(info) = self.env.get_const(head) else {
            return true;
        };
        let semireducible_def = info.value.is_some()
            && matches!(
                info.reducibility,
                Reducibility::Regular(_) | Reducibility::Irreducible
            );
        !semireducible_def || self.instance_keys_on(head)
    }

    /// Whether some registered instance names `head` as the rigid head of one
    /// of its class arguments (Lean's discrimination-tree key for it).
    fn instance_keys_on(&self, head: &Name) -> bool {
        self.instances.classes().any(|class| {
            self.instances
                .get_instances(&class.name)
                .iter()
                .any(|inst| {
                    let mut concl = &inst.type_;
                    while let ExprKind::Pi(_, _, body) = concl.kind() {
                        concl = body;
                    }
                    crate::instances::extract_class_app(concl).is_some_and(|(_, args)| {
                        args.iter().any(
                            |a| matches!(a.get_app_fn().kind(), ExprKind::Const(n, _) if n == head),
                        )
                    })
                })
        })
    }
}

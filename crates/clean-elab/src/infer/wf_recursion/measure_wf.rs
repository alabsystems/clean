// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct `WellFounded` witness for a `Nat`-valued termination measure.
//!
//! For a measure `m : α → Nat` this module builds, using only the builtin
//! prelude's constructive foundation (`Acc`, `Acc.rec`, `Nat.accNatLt`), the
//! relation
//!
//! ```text
//! rel := fun (a b : α) => Nat.lt (m a) (m b)
//! ```
//!
//! and a proof `hwf : WellFounded rel` — without going through `invImage` /
//! `WellFoundedRelation`, which the builtin prelude does not register (they
//! are import-lane constants).
//!
//! The accessibility argument avoids `Eq`-rewriting entirely. For every
//! `a : α`, `Acc rel a` follows by `Acc.rec` over `Acc Nat.lt (succ (m a))`
//! with motive
//!
//! ```text
//! fun (n : Nat) (_ : Acc Nat.lt n) => ∀ (x : α), Nat.lt (m x) n → Acc rel x
//! ```
//!
//! — the standard strong-induction transport of `Nat.lt`'s well-foundedness
//! along `m`. The final step instantiates the transported statement at
//! `n := succ (m a)`, `x := a` with `Nat.le.refl (succ (m a))` (definitional:
//! `Nat.lt k (succ k) ≡ Nat.le (succ k) (succ k)`).
//!
//! SOUNDNESS: every term built here flows into a `Declaration::Definition`
//! that the kernel re-checks in full at registration; nothing is trusted at
//! construction time and no sorry/axiom is ever emitted.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

use super::ElabCtx;

/// Constants this construction references. The caller gates on their presence
/// so an environment without the well-founded foundation fails closed with
/// the canonical `termination_by` diagnostic instead of leaking a raw
/// unknown-constant kernel error.
pub(super) const REQUIRED_CONSTANTS: &[&str] = &[
    "Nat",
    "Nat.lt",
    "Nat.succ",
    "Nat.le.refl",
    "Nat.accNatLt",
    "Acc",
    "Acc.intro",
    "Acc.rec",
    "WellFounded",
    "WellFounded.intro",
    "WellFounded.fix",
];

/// The measure evaluated at `e`: `measure_expr[param_fvar := e]`.
pub(super) fn measure_at(measure_expr: &Expr, param_fvar: FVarId, e: &Expr) -> Expr {
    measure_expr.subst_fvar(param_fvar, e)
}

impl ElabCtx<'_> {
    /// Build `fun (a b : α) => Nat.lt (m a) (m b)`.
    pub(super) fn build_measure_rel(
        &mut self,
        alpha: &Expr,
        measure_expr: &Expr,
        param_fvar: FVarId,
    ) -> Expr {
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();
        let body = Expr::apps(
            nat_lt,
            [
                measure_at(measure_expr, param_fvar, &Expr::fvar(a)),
                measure_at(measure_expr, param_fvar, &Expr::fvar(b)),
            ],
        );
        let inner = Expr::lam(BinderInfo::Default, alpha.clone(), body.abstract_fvar(b));
        Expr::lam(BinderInfo::Default, alpha.clone(), inner.abstract_fvar(a))
    }

    /// Build `WellFounded.intro α rel (fun (a : α) => …)` — the
    /// well-foundedness witness for [`build_measure_rel`]'s relation.
    ///
    /// `u_level` is the sort level of `alpha` (`alpha : Sort u_level`).
    pub(super) fn build_measure_wf_proof(
        &mut self,
        alpha: &Expr,
        u_level: &Level,
        rel: &Expr,
        measure_expr: &Expr,
        param_fvar: FVarId,
    ) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let lvl1 = Level::succ(Level::zero());
        let acc_nat = Expr::const_(Name::from_string("Acc"), vec![lvl1.clone()]);
        let acc_alpha = Expr::const_(Name::from_string("Acc"), vec![u_level.clone()]);

        let m_at = |e: &Expr| measure_at(measure_expr, param_fvar, e);
        let lt = |x: Expr, y: Expr| Expr::apps(nat_lt.clone(), [x, y]);
        let acc_nat_at = |e: Expr| Expr::apps(acc_nat.clone(), [nat.clone(), nat_lt.clone(), e]);
        let acc_rel_at = |e: Expr| Expr::apps(acc_alpha.clone(), [alpha.clone(), rel.clone(), e]);

        // motive := fun (n : Nat) (_ : Acc Nat.lt n) =>
        //             ∀ (x : α), Nat.lt (m x) n → Acc rel x
        let motive = {
            let n = self.fresh_fvar();
            let acc = self.fresh_fvar();
            let x = self.fresh_fvar();
            let target = Expr::arrow(
                lt(m_at(&Expr::fvar(x)), Expr::fvar(n)),
                acc_rel_at(Expr::fvar(x)),
            );
            let forall_x = Expr::pi(BinderInfo::Default, alpha.clone(), target.abstract_fvar(x));
            let lam_acc = Expr::lam(
                BinderInfo::Default,
                acc_nat_at(Expr::fvar(n)),
                forall_x.abstract_fvar(acc),
            );
            Expr::lam(BinderInfo::Default, nat.clone(), lam_acc.abstract_fvar(n))
        };

        // minor := fun (n : Nat)
        //              (h  : ∀ (k : Nat), Nat.lt k n → Acc Nat.lt k)
        //              (ih : ∀ (k : Nat), Nat.lt k n →
        //                      ∀ (x : α), Nat.lt (m x) k → Acc rel x)
        //              (x : α) (hx : Nat.lt (m x) n) =>
        //            Acc.intro α rel x
        //              (fun (y : α) (hy : rel y x) => ih (m x) hx y hy)
        let minor = {
            let n = self.fresh_fvar();
            let h_ty = {
                let k = self.fresh_fvar();
                let t = Expr::arrow(lt(Expr::fvar(k), Expr::fvar(n)), acc_nat_at(Expr::fvar(k)));
                Expr::pi(BinderInfo::Default, nat.clone(), t.abstract_fvar(k))
            };
            let ih_ty = {
                let k = self.fresh_fvar();
                let x = self.fresh_fvar();
                let inner = Expr::arrow(
                    lt(m_at(&Expr::fvar(x)), Expr::fvar(k)),
                    acc_rel_at(Expr::fvar(x)),
                );
                let forall_x = Expr::pi(BinderInfo::Default, alpha.clone(), inner.abstract_fvar(x));
                let t = Expr::arrow(lt(Expr::fvar(k), Expr::fvar(n)), forall_x);
                Expr::pi(BinderInfo::Default, nat.clone(), t.abstract_fvar(k))
            };

            let h = self.fresh_fvar();
            let ih = self.fresh_fvar();
            let x = self.fresh_fvar();
            let hx = self.fresh_fvar();

            // fun (y : α) (hy : rel y x) => ih (m x) hx y hy
            let intro_arg = {
                let y = self.fresh_fvar();
                let hy = self.fresh_fvar();
                let call = Expr::apps(
                    Expr::fvar(ih),
                    [
                        m_at(&Expr::fvar(x)),
                        Expr::fvar(hx),
                        Expr::fvar(y),
                        Expr::fvar(hy),
                    ],
                );
                let hy_ty = Expr::apps(rel.clone(), [Expr::fvar(y), Expr::fvar(x)]);
                let lam_hy = Expr::lam(BinderInfo::Default, hy_ty, call.abstract_fvar(hy));
                Expr::lam(BinderInfo::Default, alpha.clone(), lam_hy.abstract_fvar(y))
            };

            let intro = Expr::apps(
                Expr::const_(Name::from_string("Acc.intro"), vec![u_level.clone()]),
                [alpha.clone(), rel.clone(), Expr::fvar(x), intro_arg],
            );

            let t = Expr::lam(
                BinderInfo::Default,
                lt(m_at(&Expr::fvar(x)), Expr::fvar(n)),
                intro.abstract_fvar(hx),
            );
            let t = Expr::lam(BinderInfo::Default, alpha.clone(), t.abstract_fvar(x));
            let t = Expr::lam(BinderInfo::Default, ih_ty, t.abstract_fvar(ih));
            let t = Expr::lam(BinderInfo::Default, h_ty, t.abstract_fvar(h));
            Expr::lam(BinderInfo::Default, nat.clone(), t.abstract_fvar(n))
        };

        // apply := fun (a : α) =>
        //   Acc.rec.{0,1} Nat Nat.lt motive minor (succ (m a))
        //     (Nat.accNatLt (succ (m a))) a (Nat.le.refl (succ (m a)))
        let apply_lam = {
            let a = self.fresh_fvar();
            let succ_ma = Expr::app(succ, m_at(&Expr::fvar(a)));
            let rec_head = Expr::const_(Name::from_string("Acc.rec"), vec![Level::zero(), lvl1]);
            let acc_proof = Expr::app(
                Expr::const_(Name::from_string("Nat.accNatLt"), vec![]),
                succ_ma.clone(),
            );
            let rec_app = Expr::apps(
                rec_head,
                [nat, nat_lt, motive, minor, succ_ma.clone(), acc_proof],
            );
            let hlt = Expr::app(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                succ_ma,
            );
            let body = Expr::apps(rec_app, [Expr::fvar(a), hlt]);
            Expr::lam(BinderInfo::Default, alpha.clone(), body.abstract_fvar(a))
        };

        Expr::apps(
            Expr::const_(
                Name::from_string("WellFounded.intro"),
                vec![u_level.clone()],
            ),
            [alpha.clone(), rel.clone(), apply_lam],
        )
    }
}

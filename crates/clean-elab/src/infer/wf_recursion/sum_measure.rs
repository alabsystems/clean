// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A measure over SEVERAL parameters** — the course-of-values lowering
//! (WF phase 3, 2026-08-25).
//!
//! Phase 2 widened the SIGNATURE while keeping the MEASURE at one parameter:
//! `gcd a b` with `termination_by b` puts `b` at the front of the fix
//! telescope and threads `a` through the motive. That covers `a % b`-style
//! Euclid and nothing else. A two-branch **subtractive** Euclid
//!
//! ```lean
//! gcdSub a b = … gcdSub (a - b) b … gcdSub a (b - a) …
//! ```
//!
//! decreases in NEITHER parameter — only in `a + b` — so it needs a measure
//! that mentions both, which phase 2 refused as "lexicographic / packed".
//!
//! # The encoding, and why it needs no packing
//!
//! A measure `m : (p⃗) → Nat` still induces a **one-parameter** well-founded
//! relation: `Nat.lt` on the measure's VALUE. The parameters do not have to be
//! packed into a `PSigma` to travel with it — they can ride in the motive,
//! tied to the recursion variable by a hypothesis:
//!
//! ```text
//! α    := Nat                                         -- the measure's value
//! rel  := Nat.lt
//! hwf  := @WellFounded.intro.{1} Nat Nat.lt Nat.accNatLt
//! C    := fun (n : Nat) => Π (p⃗), Nat.lt m n → ret
//! F    := fun (n : Nat) (rec : (k : Nat) → Nat.lt k n → C k)
//!             (p⃗) (hm : Nat.lt m n) =>
//!           body[ f a⃗ ↦ rec m hm a⃗ prf ]
//! f    := fun (p⃗) => @WellFounded.fix.{1, v} Nat C Nat.lt hwf F
//!             (Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))
//! ```
//!
//! Two identities carry it:
//!
//! * `rec`'s major premise is `m` — the measure at the CURRENT parameters —
//!   and `hm` is exactly the `Nat.lt m n` it demands. So
//!   `rec m hm : Π p⃗', Nat.lt m[p⃗'] m → ret`, and the only obligation left at
//!   a call site is **`Nat.lt m[p⃗ := a⃗] m`**: the same shape the
//!   one-parameter cascade in [`super::decreasing`] already discharges, with a
//!   multi-parameter `m`. Nothing about the obligation is weakened; it is the
//!   real decrease and it is proved or the definition is refused.
//! * The seed `Nat.lt m (Nat.succ m)` is `Nat.le (Nat.succ m) (Nat.succ m)` by
//!   δ, i.e. `Nat.le.refl (Nat.succ m)` — the identity
//!   [`super::measure_wf`] already relies on.
//!
//! No `PSigma`, no `Prod`, no `invImage`/`WellFoundedRelation`, and no
//! `Eq`-rewriting. **Kernel-probed before this module was written**:
//! `clean-kernel/tests/wf_sum_measure_kernel_probe.rs` hand-builds this exact
//! shape, kernel-checks it, computes with it, requires a wrong-typed decrease
//! to be REJECTED, and audits the axiom closure empty.
//!
//! # What this path does NOT change
//!
//! * A measure naming ONE parameter never reaches here — [`super::mod`]'s
//!   phase 2b routes it to `build_wf_definition`, which still emits the
//!   byte-identical phase-1/phase-2 term. The superproject's recursion probes
//!   pin that shape and it must not move.
//! * The telescope is NOT reordered (the parameters stay in source order and
//!   the motive re-binds them in source order), so unlike the phase-2 path
//!   this one has no "recursion parameter's type depends on another
//!   parameter" restriction to impose.
//! * FAIL CLOSED is untouched: every refusal returns
//!   [`super::wf_unsupported`], and the kernel re-checks the whole definition
//!   at `add_decl`.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceName;

use super::{call_sites, encoding, wf_unsupported, ElabCtx};
use crate::ElabError;

impl ElabCtx<'_> {
    /// Build the `WellFounded.fix` definition value for a measure that
    /// mentions several parameters. See the module docs for the shape.
    ///
    /// Returns `(type, value)`. The kernel re-checks the value in full at
    /// registration; every decreasing proof was already strictly re-checked at
    /// synthesis time by [`super::decreasing`].
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_wf_sum_definition(
        &mut self,
        name: &SurfaceName,
        func_ty: &Expr,
        ret_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        binders: &[clean_parser::SurfaceBinder],
        measure_expr: &Expr,
    ) -> Result<(Expr, Expr), ElabError> {
        // `n`, `rec` and `hm` are pushed as locals so the universe inference
        // below and the decreasing cascade both see a well-formed context.
        // Unwound on BOTH the success and the failure path.
        //
        // The unwind restores a recorded DEPTH rather than popping a fixed
        // count: the core returns early from several points, and at the
        // earliest of them only `n` has been pushed. A fixed three-pop would
        // then eat two of the CALLER's binder locals — silently corrupting the
        // context every later refusal is reported against.
        let depth = self.locals.len();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let n_fvar = self.push_local(SurfaceName::unspellable("_wf_bound", 0), nat);
        let result = self.build_wf_sum_definition_core(
            name,
            func_ty,
            ret_ty,
            func_body,
            func_fvar,
            binder_fvars,
            binders,
            measure_expr,
            n_fvar,
        );
        while self.locals.len() > depth {
            self.pop_local();
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn build_wf_sum_definition_core(
        &mut self,
        name: &SurfaceName,
        func_ty: &Expr,
        ret_ty: &Expr,
        func_body: &Expr,
        func_fvar: FVarId,
        binder_fvars: &[(FVarId, Expr)],
        binders: &[clean_parser::SurfaceBinder],
        measure_expr: &Expr,
        n_fvar: FVarId,
    ) -> Result<(Expr, Expr), ElabError> {
        use crate::infer::convert_binder_info;

        let arity = binder_fvars.len();
        let binder_info_at = |index: usize| {
            binders
                .get(index)
                .map_or(BinderInfo::Default, |b| convert_binder_info(b.info))
        };

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let lt = |x: Expr, y: Expr| Expr::apps(nat_lt.clone(), [x, y]);
        // `Nat : Type 0 = Sort 1`, and α IS `Nat` here — not a parameter's
        // type — so the major universe is a constant, never inferred.
        let u_level = Level::succ(Level::zero());

        // C's body: Π (p⃗) → Nat.lt m n → ret, with the parameters re-bound in
        // their ORIGINAL order (so a dependency between parameter types is
        // preserved rather than refused).
        let mut motive_body =
            Expr::arrow(lt(measure_expr.clone(), Expr::fvar(n_fvar)), ret_ty.clone());
        for index in (0..arity).rev() {
            let (fvar, binder_ty) = &binder_fvars[index];
            motive_body = Expr::pi(
                binder_info_at(index),
                binder_ty.clone(),
                motive_body.abstract_fvar(*fvar),
            );
        }
        let v_level = self.infer_sort(&motive_body).map_err(|_| {
            wf_unsupported(
                name,
                "could not determine the universe of the motive built from the \
                 return type",
            )
        })?;
        let motive = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            motive_body.abstract_fvar(n_fvar),
        );

        // rec : (k : Nat) → Nat.lt k n → C k
        let rec_ty = {
            let k = self.fresh_fvar();
            let inner = Expr::arrow(
                lt(Expr::fvar(k), Expr::fvar(n_fvar)),
                Expr::app(motive.clone(), Expr::fvar(k)),
            );
            Expr::pi(BinderInfo::Default, nat.clone(), inner.abstract_fvar(k))
        };
        let rec_fvar = self.push_local(SurfaceName::unspellable("_wf_rec", 0), rec_ty.clone());
        let hm_ty = lt(measure_expr.clone(), Expr::fvar(n_fvar));
        let hm_fvar = self.push_local(SurfaceName::unspellable("_wf_measure_lt", 0), hm_ty.clone());

        // Open the body: func_body = fun p₀ … pₙ₋₁ => body.
        let mut body_open = func_body.clone();
        for (fvar, _) in binder_fvars {
            let ExprKind::Lam(_, _, inner) = body_open.kind() else {
                return Err(wf_unsupported(
                    name,
                    "the elaborated function value is not a lambda",
                ));
            };
            body_open = inner.instantiate(&Expr::fvar(*fvar));
        }

        // Rewrite `f a⃗` to `rec m hm a⃗ prf`, synthesizing the real decrease
        // `Nat.lt m[p⃗ := a⃗] m` per call site. FAIL CLOSED on any failure.
        let cfg = call_sites::RecCallRewrite {
            func_fvar,
            rec_fvar,
            arity,
            measure_expr,
            shape: call_sites::RecShape::MeasureValue {
                hm_fvar,
                params: binder_fvars,
            },
        };
        let transformed = self
            .transform_rec_calls_proved(&body_open, &cfg)
            .map_err(|reject| wf_unsupported(name, &reject.0))?;

        // Backstop, independent of the rewriter: no self-reference survives.
        if encoding::contains_fvar(&transformed, func_fvar) {
            return Err(wf_unsupported(
                name,
                "a self-reference survived the call-site rewrite",
            ));
        }

        // F := fun (n) (rec) (p⃗) (hm) => transformed
        let fix_body = {
            let mut inner = Expr::lam(
                BinderInfo::Default,
                hm_ty,
                transformed.abstract_fvar(hm_fvar),
            );
            for index in (0..arity).rev() {
                let (fvar, binder_ty) = &binder_fvars[index];
                inner = Expr::lam(
                    binder_info_at(index),
                    binder_ty.clone(),
                    inner.abstract_fvar(*fvar),
                );
            }
            let with_rec = Expr::lam(BinderInfo::Default, rec_ty, inner.abstract_fvar(rec_fvar));
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                with_rec.abstract_fvar(n_fvar),
            )
        };

        // hwf := @WellFounded.intro.{1} Nat Nat.lt Nat.accNatLt.
        //
        // Built inline rather than cited as `Nat.lt_wf` so the witness is
        // guaranteed to REDUCE: `WellFounded.fix` only computes if
        // `WellFounded.apply hwf` exposes the `Acc` proof, and an inline
        // `intro` exposes it without depending on a named constant's
        // unfolding policy.
        let hwf = Expr::apps(
            Expr::const_(
                Name::from_string("WellFounded.intro"),
                vec![u_level.clone()],
            ),
            [
                nat.clone(),
                nat_lt.clone(),
                Expr::const_(Name::from_string("Nat.accNatLt"), vec![]),
            ],
        );

        // value := fun (p⃗) => fix … (Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))
        let succ_m = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            measure_expr.clone(),
        );
        let wf_fix = Expr::const_(Name::from_string("WellFounded.fix"), vec![u_level, v_level]);
        let mut applied = Expr::apps(wf_fix, [nat, motive, nat_lt, hwf, fix_body, succ_m.clone()]);
        for (fvar, _) in binder_fvars {
            applied = Expr::app(applied, Expr::fvar(*fvar));
        }
        applied = Expr::app(
            applied,
            Expr::app(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                succ_m,
            ),
        );

        let mut value = applied;
        for index in (0..arity).rev() {
            let (fvar, binder_ty) = &binder_fvars[index];
            value = Expr::lam(
                binder_info_at(index),
                binder_ty.clone(),
                value.abstract_fvar(*fvar),
            );
        }

        Ok((func_ty.clone(), value))
    }
}

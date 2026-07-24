// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `Ord` for a PARAMETRIC inductive whose every field's type
//! is one of the type parameters (`Box a | mk : a -> Box a`;
//! `MyOpt a | none2 | some2 : a -> MyOpt a`; `MySum a b | inl | inr`).
//!
//! The parametric path in `derive_ord_inductive` previously fell to a weak total
//! `Ordering.eq` (a reachable silent-wrong once `Ord` was wired into the
//! prelude — `compare (Box.mk 1) (Box.mk 2)` gave `eq`). This builds the REAL
//! comparison, mirroring `build_beq_parametric_multi`: two nested `casesOn`s
//! binding the fields, the same-ctor diagonal chaining per-field
//! `@Ord.compare pᵢ instᵢ` with `Ordering.then` (inlined via `Ordering.casesOn`,
//! `Ordering.eq` when nullary), every off-diagonal (distinct ctors) comparing
//! the constructor ordinals via `Nat.compare`. Built with fvars (depth-invariant
//! parameters) and abstracted once at the end.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build `λ {p₀ … : Type} [Ord p₀] … => @Ord.mk (Ind p…) (fun a b => …)` for
    /// an inductive whose every field's type is a type parameter.
    /// `per_ctor_fields[c]` maps ctor `c`'s fields to their parameter indices
    /// (`[]` for a nullary ctor). All parameters are `Type 0`, so every class
    /// level is `0` and every `casesOn`/motive universe is `1`.
    pub(super) fn build_ord_parametric(
        &mut self,
        ind_name: &Name,
        num_params: usize,
        per_ctor_fields: &[Vec<usize>],
        ctor_names: &[Name],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // motive universe (→ Ordering : Sort 1)
        let l0 = Level::zero(); // pᵢ : Type 0 ⇒ Ord/Ord.compare level 0
        let type0 = Expr::sort(l1.clone());
        let n_ctor = per_ctor_fields.len();
        if n_ctor == 0 || n_ctor != ctor_names.len() || num_params == 0 {
            return None;
        }
        if per_ctor_fields.iter().flatten().any(|&p| p >= num_params) {
            return None;
        }

        let params: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let insts: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();
        let xf: Vec<Vec<FVarId>> = per_ctor_fields
            .iter()
            .map(|f| (0..f.len()).map(|_| self.fresh_fvar()).collect())
            .collect();
        let yf: Vec<Vec<FVarId>> = per_ctor_fields
            .iter()
            .map(|f| (0..f.len()).map(|_| self.fresh_fvar()).collect())
            .collect();

        let fv = Expr::fvar;
        let param_args: Vec<Expr> = params.iter().map(|p| fv(*p)).collect();
        let ind_applied = Expr::apps(Expr::const_(ind_name.clone(), vec![]), param_args.clone());
        let ordering_ty = Expr::const_(Name::from_string("Ordering"), vec![]);
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let motive = Expr::lam(
            BinderInfo::Default,
            ind_applied.clone(),
            ordering_ty.clone(),
        );

        // `Ordering.then x y` inlined via `Ordering.casesOn`: lt ⇒ lt, eq ⇒ y,
        // gt ⇒ gt (ctor order lt, eq, gt).
        let then = |x: Expr, y: Expr| -> Expr {
            let m = Expr::lam(
                BinderInfo::Default,
                ordering_ty.clone(),
                ordering_ty.clone(),
            );
            Expr::apps(
                Expr::const_(Name::from_string("Ordering.casesOn"), vec![l1.clone()]),
                [
                    m,
                    x,
                    Expr::const_(Name::from_string("Ordering.lt"), vec![]),
                    y,
                    Expr::const_(Name::from_string("Ordering.gt"), vec![]),
                ],
            )
        };

        // Bind ctor `c`'s fields (innermost-first) around `body`.
        let bind_fields = |body: Expr, c: usize, fvars: &[Vec<FVarId>]| -> Expr {
            let flds = &per_ctor_fields[c];
            let mut acc = body;
            for k in (0..flds.len()).rev() {
                acc = Expr::lam(
                    BinderInfo::Default,
                    fv(params[flds[k]]),
                    acc.abstract_fvar(fvars[c][k]),
                );
            }
            acc
        };

        // Outer casesOn on `a`: minor i binds ctor i's x-fields; body is an inner
        // casesOn on `b` — diagonal (i == j) chains per-field Ord.compare,
        // off-diagonal (i != j) compares ordinals via Nat.compare.
        let mut outer_args = param_args.clone();
        outer_args.push(motive.clone());
        outer_args.push(fv(a));
        for i in 0..n_ctor {
            let mut inner_args = param_args.clone();
            inner_args.push(motive.clone());
            inner_args.push(fv(b));
            for j in 0..n_ctor {
                let body_j = if i == j {
                    let flds = &per_ctor_fields[i];
                    if flds.is_empty() {
                        Expr::const_(Name::from_string("Ordering.eq"), vec![])
                    } else {
                        let cmp_k = |k: usize| {
                            Expr::apps(
                                Expr::const_(Name::from_string("Ord.compare"), vec![l0.clone()]),
                                [
                                    fv(params[flds[k]]),
                                    fv(insts[flds[k]]),
                                    fv(xf[i][k]),
                                    fv(yf[i][k]),
                                ],
                            )
                        };
                        let mut acc = cmp_k(flds.len() - 1);
                        for k in (0..flds.len() - 1).rev() {
                            acc = then(cmp_k(k), acc);
                        }
                        acc
                    }
                } else {
                    Expr::apps(
                        Expr::const_(Name::from_string("Nat.compare"), vec![]),
                        [Expr::nat_lit(i as u64), Expr::nat_lit(j as u64)],
                    )
                };
                inner_args.push(bind_fields(body_j, j, &yf));
            }
            let inner_cases =
                Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);
            outer_args.push(bind_fields(inner_cases, i, &xf));
        }
        let outer_cases = Expr::apps(Expr::const_(cases_on, vec![l1.clone()]), outer_args);

        // λ (a b : Ind p…) => outer_cases
        let b_lam = Expr::lam(
            BinderInfo::Default,
            ind_applied.clone(),
            outer_cases.abstract_fvar(b),
        );
        let ab_lam = Expr::lam(
            BinderInfo::Default,
            ind_applied.clone(),
            b_lam.abstract_fvar(a),
        );

        // `Ord` is a CLASS — value is `@Ord.mk.{0} (Ind p…) (fun a b => …)`, then
        // [Ord pᵢ] then {pᵢ} binders.
        let mut result = Expr::apps(
            Expr::const_(Name::from_string("Ord.mk"), vec![l0.clone()]),
            [ind_applied, ab_lam],
        );
        for i in (0..num_params).rev() {
            let ord_pi = Expr::app(
                Expr::const_(Name::from_string("Ord"), vec![l0.clone()]),
                fv(params[i]),
            );
            result = Expr::lam(
                BinderInfo::InstImplicit,
                ord_pi,
                result.abstract_fvar(insts[i]),
            );
        }
        for i in (0..num_params).rev() {
            result = Expr::lam(
                BinderInfo::Implicit,
                type0.clone(),
                result.abstract_fvar(params[i]),
            );
        }
        Some(result)
    }
}

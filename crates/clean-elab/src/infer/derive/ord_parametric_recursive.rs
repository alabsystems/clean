// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `Ord` for a SINGLE-PARAMETER, DIRECTLY self-recursive
//! inductive (`Tree a | leaf | node : Tree a -> a -> Tree a -> Tree a`).
//!
//! The `Ord` twin of `beq_parametric_recursive.rs`: drives the parametric
//! recursor `@Ind.rec.{1} p motive minors… a b` with a per-field induction
//! hypothesis (`motive l = Ind p → Ordering`). The same-ctor diagonal chains
//! per-field comparisons with `Ordering.then` — a recursive `Ind p` field via
//! its IH, the parameter field via the bound `[Ord p]`; distinct constructors
//! compare their ordinals via `Nat.compare`. Scoped to `num_params == 1`,
//! num_motives = 1 (via [`classify_single_param_recursive`]).

use super::beq_parametric_recursive::RecField;
use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build `λ {p : Type} [Ord p] => @Ord.mk (Ind p) (fun a b => @Ind.rec.{1} p
    /// (fun _ => Ind p → Ordering) minors… a b)`.
    pub(super) fn build_ord_parametric_recursive(
        &mut self,
        ind_name: &Name,
        per_ctor_fields: &[Vec<RecField>],
        ctor_names: &[Name],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // motive universe (→ (Ind p → Ordering) : Sort 1)
        let l0 = Level::zero();
        let type0 = Expr::sort(l1.clone());
        let n_ctor = per_ctor_fields.len();
        if n_ctor == 0 || n_ctor != ctor_names.len() {
            return None;
        }

        let p = self.fresh_fvar();
        let inst = self.fresh_fvar();
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();
        let fv = Expr::fvar;
        let ind_p = Expr::app(Expr::const_(ind_name.clone(), vec![]), fv(p));
        let ordering_ty = Expr::const_(Name::from_string("Ordering"), vec![]);
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // rec motive: `fun (_ : Ind p) => Ind p → Ordering`
        let rec_motive = Expr::lam(
            BinderInfo::Default,
            ind_p.clone(),
            Expr::arrow(ind_p.clone(), ordering_ty.clone()),
        );
        // casesOn motive: `fun (_ : Ind p) => Ordering`
        let cases_motive = Expr::lam(BinderInfo::Default, ind_p.clone(), ordering_ty.clone());

        // `Ordering.then x y` inlined via `Ordering.casesOn`.
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

        let af: Vec<Vec<FVarId>> = per_ctor_fields
            .iter()
            .map(|f| f.iter().map(|_| self.fresh_fvar()).collect())
            .collect();
        let ih: Vec<Vec<FVarId>> = per_ctor_fields
            .iter()
            .map(|f| {
                f.iter()
                    .filter(|k| **k == RecField::SelfRec)
                    .map(|_| self.fresh_fvar())
                    .collect()
            })
            .collect();
        let bf: Vec<Vec<Vec<FVarId>>> = (0..n_ctor)
            .map(|_| {
                per_ctor_fields
                    .iter()
                    .map(|f| f.iter().map(|_| self.fresh_fvar()).collect())
                    .collect()
            })
            .collect();

        let field_ty = |k: RecField| match k {
            RecField::Param => fv(p),
            RecField::SelfRec => ind_p.clone(),
        };
        let bind_ctor_fields = |body: Expr, c: usize, fvars: &[Vec<FVarId>]| -> Expr {
            let flds = &per_ctor_fields[c];
            let mut acc = body;
            for k in (0..flds.len()).rev() {
                acc = Expr::lam(
                    BinderInfo::Default,
                    field_ty(flds[k]),
                    acc.abstract_fvar(fvars[c][k]),
                );
            }
            acc
        };

        let mut rec_args: Vec<Expr> = vec![fv(p), rec_motive];
        for i in 0..n_ctor {
            let mut inner_args = vec![fv(p), cases_motive.clone(), fv(b)];
            for j in 0..n_ctor {
                let body_j = if i == j {
                    let flds = &per_ctor_fields[i];
                    if flds.is_empty() {
                        Expr::const_(Name::from_string("Ordering.eq"), vec![])
                    } else {
                        // Per-field comparison, folded right with Ordering.then.
                        let mut ih_idx = 0usize;
                        let mut cmps: Vec<Expr> = Vec::with_capacity(flds.len());
                        for (k, fk) in flds.iter().enumerate() {
                            let cmp = match fk {
                                RecField::SelfRec => {
                                    let e = Expr::app(fv(ih[i][ih_idx]), fv(bf[i][i][k]));
                                    ih_idx += 1;
                                    e
                                }
                                RecField::Param => Expr::apps(
                                    Expr::const_(
                                        Name::from_string("Ord.compare"),
                                        vec![l0.clone()],
                                    ),
                                    [fv(p), fv(inst), fv(af[i][k]), fv(bf[i][i][k])],
                                ),
                            };
                            cmps.push(cmp);
                        }
                        let mut acc = cmps.pop().expect("non-empty");
                        while let Some(c) = cmps.pop() {
                            acc = then(c, acc);
                        }
                        acc
                    }
                } else {
                    Expr::apps(
                        Expr::const_(Name::from_string("Nat.compare"), vec![]),
                        [Expr::nat_lit(i as u64), Expr::nat_lit(j as u64)],
                    )
                };
                inner_args.push(bind_ctor_fields(body_j, j, &bf[i]));
            }
            let inner_cases =
                Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);
            let b_lam = Expr::lam(
                BinderInfo::Default,
                ind_p.clone(),
                inner_cases.abstract_fvar(b),
            );

            let mut minor = b_lam;
            for k in (0..ih[i].len()).rev() {
                minor = Expr::lam(
                    BinderInfo::Default,
                    Expr::arrow(ind_p.clone(), ordering_ty.clone()),
                    minor.abstract_fvar(ih[i][k]),
                );
            }
            minor = bind_ctor_fields(minor, i, &af);
            rec_args.push(minor);
        }
        rec_args.push(fv(a));
        rec_args.push(fv(b));
        let rec_app = Expr::apps(Expr::const_(rec_name, vec![l1.clone()]), rec_args);

        let inner_b = Expr::lam(BinderInfo::Default, ind_p.clone(), rec_app.abstract_fvar(b));
        let ab_lam = Expr::lam(BinderInfo::Default, ind_p.clone(), inner_b.abstract_fvar(a));

        // @Ord.mk.{0} (Ind p) (fun a b => …), then [Ord p], then {p}.
        let mut result = Expr::apps(
            Expr::const_(Name::from_string("Ord.mk"), vec![l0.clone()]),
            [ind_p.clone(), ab_lam],
        );
        let ord_p = Expr::app(
            Expr::const_(Name::from_string("Ord"), vec![l0.clone()]),
            fv(p),
        );
        result = Expr::lam(BinderInfo::InstImplicit, ord_p, result.abstract_fvar(inst));
        result = Expr::lam(BinderInfo::Implicit, type0, result.abstract_fvar(p));
        Some(result)
    }
}

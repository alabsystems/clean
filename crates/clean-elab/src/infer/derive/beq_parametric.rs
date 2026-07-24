// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `BEq` for a PARAMETRIC inductive with a single constructor
//! whose every field's type is one of the type parameters
//! (`inductive Box (a : Type) | mk : a -> Box a`;
//! `inductive Pair (a b : Type) | mk : a -> b -> Pair a b`).
//!
//! The parametric path in `derive_beq_inductive` previously fell back to a weak
//! total `Bool.true` for single-ctor types. This builds the REAL comparison —
//! `mk x… == mk y…  ≡  (x₀ == y₀) && …` — using the bound `[BEq pᵢ]` instances.
//!
//! `BEq` returns `Bool`, so unlike `DecidableEq` there is no equality proof,
//! injectivity, or `noConfusion`: the value is two nested `casesOn`s binding the
//! fields, then a `Bool.and` fold over per-field `BEq.beq`. Constructed with
//! fvars (depth-invariant parameters) and abstracted once at the end. See
//! `designs/2026-07-14-parametric-decidable-eq-deriving.md`.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build `λ {p₀ … : Type} [BEq p₀] … (a b : Ind p…) => a == b` for a single
    /// constructor whose every field's type is one of the `num_params` type
    /// parameters. `field_params[j]` is the parameter index of field `j` (`[0]`
    /// for `Box a`, `[0, 1]` for `Pair a b`). All parameters are `Type 0`, so
    /// every class level is `0` and `casesOn`'s motive universe is `1`.
    pub(super) fn build_beq_parametric(
        &mut self,
        ind_name: &Name,
        num_params: usize,
        field_params: &[usize],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // Type 0 = Sort 1 (motive universe)
        let l0 = Level::zero(); // pᵢ : Type 0 ⇒ BEq/BEq.beq level 0
        let type0 = Expr::sort(l1.clone());
        let n = field_params.len();
        if n == 0 || num_params == 0 || field_params.iter().any(|&p| p >= num_params) {
            return None;
        }

        let params: Vec<_> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let insts: Vec<_> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();
        let xf: Vec<_> = (0..n).map(|_| self.fresh_fvar()).collect();
        let yf: Vec<_> = (0..n).map(|_| self.fresh_fvar()).collect();

        let fv = Expr::fvar;
        let param_args: Vec<Expr> = params.iter().map(|p| fv(*p)).collect();
        // Ind p₀ … p_{k-1}
        let ind_applied = Expr::apps(Expr::const_(ind_name.clone(), vec![]), param_args.clone());
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));

        // Per-field `@BEq.beq.{0} p_{fp} inst_{fp} xⱼ yⱼ`, folded right with Bool.and.
        let beqs: Vec<Expr> = (0..n)
            .map(|j| {
                let p = field_params[j];
                Expr::apps(
                    Expr::const_(Name::from_string("BEq.beq"), vec![l0.clone()]),
                    [fv(params[p]), fv(insts[p]), fv(xf[j]), fv(yf[j])],
                )
            })
            .collect();
        let mut and_chain = beqs[n - 1].clone();
        for j in (0..n - 1).rev() {
            and_chain = Expr::apps(
                Expr::const_(Name::from_string("Bool.and"), vec![]),
                [beqs[j].clone(), and_chain],
            );
        }

        let motive = Expr::lam(BinderInfo::Default, ind_applied.clone(), bool_ty);

        // Bind the ctor's fields (innermost-first) as `λ (f₀ : p_{fp₀}) … => body`.
        let bind_fields = |body: Expr, fvars: &[FVarId]| -> Expr {
            let mut acc = body;
            for j in (0..n).rev() {
                acc = Expr::lam(
                    BinderInfo::Default,
                    fv(params[field_params[j]]),
                    acc.abstract_fvar(fvars[j]),
                );
            }
            acc
        };

        let y_minor = bind_fields(and_chain, &yf);
        let mut inner_args = param_args.clone();
        inner_args.push(motive.clone());
        inner_args.push(fv(b));
        inner_args.push(y_minor);
        let inner_cases = Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);

        let x_minor = bind_fields(inner_cases, &xf);
        let mut outer_args = param_args;
        outer_args.push(motive);
        outer_args.push(fv(a));
        outer_args.push(x_minor);
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

        // `BEq` is a CLASS (structure with a `beq` field), not a def — the value
        // is `@BEq.mk.{0} (Ind p…) (fun a b => …)`, not the bare function.
        let mut result = Expr::apps(
            Expr::const_(Name::from_string("BEq.mk"), vec![l0.clone()]),
            [ind_applied, ab_lam],
        );
        // Instance constraints innermost, then type params (matching the instance
        // type from `build_parametric_instance_type`).
        for i in (0..num_params).rev() {
            let beq_pi = Expr::app(
                Expr::const_(Name::from_string("BEq"), vec![l0.clone()]),
                fv(params[i]),
            );
            result = Expr::lam(
                BinderInfo::InstImplicit,
                beq_pi,
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

    /// Build `BEq` for a MULTI-constructor parametric inductive whose every
    /// field's type is one of the `num_params` type parameters
    /// (`MyOpt a | none2 | some2 : a → MyOpt a`; `Sum a b | inl : a → … | inr : b → …`).
    /// `per_ctor_fields[c]` maps constructor `c`'s fields to their parameter
    /// indices (`[]` for a nullary ctor). The value nests `casesOn` on both
    /// scrutinees: the diagonal minor (same ctor) folds per-field `BEq.beq` with
    /// `Bool.and` (`Bool.true` when the ctor is nullary); every off-diagonal
    /// minor (distinct ctors) is `Bool.false`. This retires the weak `Bool.true`
    /// total fallback (silent-wrong S2) for multi-ctor parametric types.
    pub(super) fn build_beq_parametric_multi(
        &mut self,
        ind_name: &Name,
        num_params: usize,
        per_ctor_fields: &[Vec<usize>],
        ctor_names: &[Name],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // motive universe (→ Bool : Sort 1)
        let l0 = Level::zero(); // pᵢ : Type 0 ⇒ BEq/BEq.beq level 0
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
        // Per-ctor, per-side field fvars (x = left scrutinee, y = right).
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
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let motive = Expr::lam(BinderInfo::Default, ind_applied.clone(), bool_ty);

        // Bind ctor `c`'s fields (innermost-first) around `body`, typing each
        // field with its parameter and abstracting the fvar from `fvars[c]`.
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

        // Outer casesOn on `a`: minor i binds ctor i's x-fields; its body is an
        // inner casesOn on `b` whose minor j is the diagonal fold (i == j) or
        // Bool.false (i != j).
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
                        Expr::const_(Name::from_string("Bool.true"), vec![])
                    } else {
                        let beq_k = |k: usize| {
                            Expr::apps(
                                Expr::const_(Name::from_string("BEq.beq"), vec![l0.clone()]),
                                [
                                    fv(params[flds[k]]),
                                    fv(insts[flds[k]]),
                                    fv(xf[i][k]),
                                    fv(yf[i][k]),
                                ],
                            )
                        };
                        let mut acc = beq_k(flds.len() - 1);
                        for k in (0..flds.len() - 1).rev() {
                            acc = Expr::apps(
                                Expr::const_(Name::from_string("Bool.and"), vec![]),
                                [beq_k(k), acc],
                            );
                        }
                        acc
                    }
                } else {
                    bool_false.clone()
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

        // @BEq.mk.{0} (Ind p…) (fun a b => …), then [BEq pᵢ] then {pᵢ} binders.
        let mut result = Expr::apps(
            Expr::const_(Name::from_string("BEq.mk"), vec![l0.clone()]),
            [ind_applied, ab_lam],
        );
        for i in (0..num_params).rev() {
            let beq_pi = Expr::app(
                Expr::const_(Name::from_string("BEq"), vec![l0.clone()]),
                fv(params[i]),
            );
            result = Expr::lam(
                BinderInfo::InstImplicit,
                beq_pi,
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

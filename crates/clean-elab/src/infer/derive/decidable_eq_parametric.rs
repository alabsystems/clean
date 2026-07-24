// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for a PARAMETRIC inductive with a single
//! constructor whose every field's type is one of the type parameters
//! (`inductive Box (a : Type) | mk : a -> Box a`;
//! `inductive Pair (a b : Type) | mk : a -> b -> Pair a b`).
//!
//! The monomorphic builders are bvar-based with a monomorphic `casesOn.{1}` (no
//! parameter argument) and decide the same-ctor `isFalse` direction via the
//! type's `noConfusion` — the intricate heterogeneous form for a parametric
//! type. This builder instead:
//!
//! - constructs the whole value with **fvars** (a parameter fvar is
//!   depth-invariant, referenced at every nesting depth and abstracted at the
//!   end), and
//! - derives constructor injectivity WITHOUT `noConfusion`, via per-field
//!   `casesOn` projections `unmkᵢ := fun p => Ind.casesOn p (fun f… => fᵢ)`
//!   plus `congrArg`.
//!
//! Fields are decided left-to-right through a nested `Decidable.casesOn`: any
//! field that differs yields `isFalse` (projection injectivity); when ALL fields
//! are equal, `isTrue` is witnessed by an `Eq.trans` chain of `congrArg` steps.
//! See `designs/2026-07-14-parametric-decidable-eq-deriving.md`. The derived
//! decision is kernel-re-checked AND asserted to *reduce* by tests.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build the fully-abstracted instance value
    /// `λ {p₀ … : Type} [DecidableEq p₀] … (a b : Ind p…) => …` for a single
    /// constructor whose every field's type is one of the `num_params`
    /// parameters. `field_params[j]` is the parameter index of field `j`.
    pub(super) fn build_decidable_eq_parametric(
        &mut self,
        ind_name: &Name,
        ctor_name: &Name,
        num_params: usize,
        field_params: &[usize],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // Type 0 = Sort 1
        let type0 = Expr::sort(l1.clone());
        let n = field_params.len();
        if n == 0 || num_params == 0 || field_params.iter().any(|&p| p >= num_params) {
            return None;
        }

        let params: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let insts: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();
        let xf: Vec<FVarId> = (0..n).map(|_| self.fresh_fvar()).collect();
        let yf: Vec<FVarId> = (0..n).map(|_| self.fresh_fvar()).collect();
        let heqf: Vec<FVarId> = (0..n).map(|_| self.fresh_fvar()).collect();

        let fv = Expr::fvar;
        let param_args: Vec<Expr> = params.iter().map(|p| fv(*p)).collect();
        let ind_applied = Expr::apps(Expr::const_(ind_name.clone(), vec![]), param_args.clone());
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));

        let eq = |ty: &Expr, u: &Expr, v: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [ty.clone(), u.clone(), v.clone()],
            )
        };
        let decidable = |p: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                p.clone(),
            )
        };
        // `@Ctor p… f…`
        let mk = |fields: &[Expr]| {
            let mut args = param_args.clone();
            args.extend_from_slice(fields);
            Expr::apps(Expr::const_(ctor_name.clone(), vec![]), args)
        };

        let mk_x = mk(&xf.iter().map(|f| fv(*f)).collect::<Vec<_>>());
        let mk_y = mk(&yf.iter().map(|f| fv(*f)).collect::<Vec<_>>());
        let whole_eq = eq(&ind_applied, &mk_x, &mk_y);

        // unmkᵢ : Ind p… → p_{fpᵢ}  (projection of field i)
        let unmk = |this: &mut Self, i: usize| -> Expr {
            let bb = this.fresh_fvar();
            let ff: Vec<FVarId> = (0..n).map(|_| this.fresh_fvar()).collect();
            let motive = Expr::lam(
                BinderInfo::Default,
                ind_applied.clone(),
                fv(params[field_params[i]]),
            );
            // mk-minor projecting field i: λ f₀ … f_{n-1} => fᵢ
            let mut minor = fv(ff[i]);
            for j in (0..n).rev() {
                minor = Expr::lam(
                    BinderInfo::Default,
                    fv(params[field_params[j]]),
                    minor.abstract_fvar(ff[j]),
                );
            }
            let mut args = param_args.clone();
            args.push(motive);
            args.push(fv(bb));
            args.push(minor);
            let body = Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), args);
            Expr::lam(
                BinderInfo::Default,
                ind_applied.clone(),
                body.abstract_fvar(bb),
            )
        };

        // isTrue congruence: `mk x… = mk y…` via Eq.trans over per-field congrArg
        // steps. Step i replaces field i (fields <i already y, fields >i still x):
        //   congrArg (λ t => mk y₀…y_{i-1} t x_{i+1}…) heqᵢ.
        let point = |k: usize| -> Expr {
            // mk with first k fields = y, rest = x
            let fields: Vec<Expr> = (0..n)
                .map(|j| if j < k { fv(yf[j]) } else { fv(xf[j]) })
                .collect();
            mk(&fields)
        };
        // Build the Eq.trans chain: proof that point(0) = point(n).
        let congruence = {
            let mut proof: Option<Expr> = None;
            for i in 0..n {
                // step_i : point(i) = point(i+1)
                let t = self.fresh_fvar();
                let hole_fields: Vec<Expr> = (0..n)
                    .map(|j| {
                        if j < i {
                            fv(yf[j])
                        } else if j == i {
                            fv(t)
                        } else {
                            fv(xf[j])
                        }
                    })
                    .collect();
                let hole_fn = Expr::lam(
                    BinderInfo::Default,
                    fv(params[field_params[i]]),
                    mk(&hole_fields).abstract_fvar(t),
                );
                let step = Expr::apps(
                    Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                    [
                        fv(params[field_params[i]]),
                        ind_applied.clone(),
                        fv(xf[i]),
                        fv(yf[i]),
                        hole_fn,
                        fv(heqf[i]),
                    ],
                );
                proof = Some(match proof {
                    None => step,
                    Some(prev) => Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
                        [
                            ind_applied.clone(),
                            point(0),
                            point(i),
                            point(i + 1),
                            prev,
                            step,
                        ],
                    ),
                });
            }
            proof.expect("n >= 1")
        };
        let is_true = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                whole_eq.clone(),
            ),
            congruence,
        );

        // Nested field decision, built inner-first. `body` starts as the all-equal
        // `isTrue`; wrap each field k (n-1 … 0) in a `Decidable.casesOn`.
        let mut body = is_true;
        for k in (0..n).rev() {
            let p = field_params[k];
            let eq_k = eq(&fv(params[p]), &fv(xf[k]), &fv(yf[k]));
            let dec_motive = Expr::lam(BinderInfo::Default, decidable(&eq_k), decidable(&whole_eq));
            let inst_app = Expr::apps(fv(insts[p]), [fv(xf[k]), fv(yf[k])]);

            // isFalse minor: λ (hne : ¬eq_k) => isFalse whole_eq
            //   (λ (h : mk x… = mk y…) => hne (congrArg unmkₖ h))
            let unmk_k = unmk(self, k);
            let hne = self.fresh_fvar();
            let h = self.fresh_fvar();
            let congr = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                [
                    ind_applied.clone(),
                    fv(params[p]),
                    mk_x.clone(),
                    mk_y.clone(),
                    unmk_k,
                    fv(h),
                ],
            );
            let apply_hne = Expr::app(fv(hne), congr);
            let inner = Expr::lam(
                BinderInfo::Default,
                whole_eq.clone(),
                apply_hne.abstract_fvar(h),
            );
            let is_false = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                    whole_eq.clone(),
                ),
                inner,
            );
            let not_ty = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_k.clone());
            let isfalse_minor = Expr::lam(BinderInfo::Default, not_ty, is_false.abstract_fvar(hne));

            // isTrue minor: λ (heqₖ : eq_k) => body   (body references heqf[k])
            let istrue_minor = Expr::lam(
                BinderInfo::Default,
                eq_k.clone(),
                body.abstract_fvar(heqf[k]),
            );

            body = Expr::apps(
                Expr::const_(Name::from_string("Decidable.casesOn"), vec![l1.clone()]),
                [eq_k, dec_motive, inst_app, isfalse_minor, istrue_minor],
            );
        }

        // inner casesOn on b: bind y-fields.
        let inner_motive = {
            let qp = self.fresh_fvar();
            let m = decidable(&eq(&ind_applied, &mk_x, &fv(qp)));
            Expr::lam(
                BinderInfo::Default,
                ind_applied.clone(),
                m.abstract_fvar(qp),
            )
        };
        let mut y_minor = body;
        for j in (0..n).rev() {
            y_minor = Expr::lam(
                BinderInfo::Default,
                fv(params[field_params[j]]),
                y_minor.abstract_fvar(yf[j]),
            );
        }
        let mut inner_args = param_args.clone();
        inner_args.push(inner_motive);
        inner_args.push(fv(b));
        inner_args.push(y_minor);
        let inner_cases = Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);

        // outer casesOn on a: bind x-fields.
        let outer_motive = {
            let ap = self.fresh_fvar();
            let m = decidable(&eq(&ind_applied, &fv(ap), &fv(b)));
            Expr::lam(
                BinderInfo::Default,
                ind_applied.clone(),
                m.abstract_fvar(ap),
            )
        };
        let mut x_minor = inner_cases;
        for j in (0..n).rev() {
            x_minor = Expr::lam(
                BinderInfo::Default,
                fv(params[field_params[j]]),
                x_minor.abstract_fvar(xf[j]),
            );
        }
        let mut outer_args = param_args;
        outer_args.push(outer_motive);
        outer_args.push(fv(a));
        outer_args.push(x_minor);
        let outer_cases = Expr::apps(Expr::const_(cases_on, vec![l1.clone()]), outer_args);

        // λ (a b : Ind p…) => outer_cases  (DecidableEq is a def; value IS the fn)
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

        // λ {p…} [inst : @DecidableEq.{1} pᵢ] … : constraints innermost, then params.
        let mut result = ab_lam;
        for i in (0..num_params).rev() {
            let deceq_pi = Expr::app(
                Expr::const_(Name::from_string("DecidableEq"), vec![l1.clone()]),
                fv(params[i]),
            );
            result = Expr::lam(
                BinderInfo::InstImplicit,
                deceq_pi,
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

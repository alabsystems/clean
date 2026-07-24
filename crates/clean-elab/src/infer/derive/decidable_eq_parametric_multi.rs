// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for a MULTI-constructor PARAMETRIC inductive
//! whose every field's type is one of the type parameters
//! (`MyOpt a | none2 | some2 : a -> MyOpt a`;
//! `MySum a b | inl : a -> … | inr : b -> …`).
//!
//! Generalizes the single-constructor builder (`decidable_eq_parametric`) to N
//! constructors via a nested `casesOn` on both scrutinees. For the outer ctor
//! `i` and inner ctor `j`:
//!
//! - **diagonal** (`i == j`): decide ctor `i`'s fields left-to-right through a
//!   nested `Decidable.casesOn`; a differing field yields `isFalse` witnessed by
//!   projection injectivity (`unmkₖ` via `casesOn`, the other ctors' minors
//!   returning an in-scope default of the right type), all-equal yields `isTrue`
//!   via an `Eq.trans` chain of `congrArg` steps — identical to the single-ctor
//!   builder.
//! - **off-diagonal** (`i != j`): `isFalse` from a `casesOn` discriminator
//!   `discᵢ : Ind p… → Prop` (ctor `i` ↦ `True`, every other ↦ `False`) — then
//!   `@Eq.mp.{0} (discᵢ A) (discᵢ B) (congrArg discᵢ h) True.intro : False`.
//!   This is `noConfusion`-FREE: Clean generates a HETEROGENEOUS `noConfusion`
//!   for parameterized families (`PendingHeterogeneousEquality`), so the
//!   monomorphic `@Ind.noConfusion False …` route does not apply here.
//!
//! All parameters are `Type 0`, so every class level is `0` and every
//! `casesOn`/`Eq`/`congrArg` motive universe is `1`. Built with fvars
//! (depth-invariant) and abstracted once at the end. Retires the `sorry`
//! fallback for Option/Sum shapes. See
//! `designs/2026-07-14-parametric-decidable-eq-deriving.md`.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build `λ {p₀ … : Type} [DecidableEq p₀] … (a b : Ind p…) => …` for a
    /// multi-constructor inductive whose every field's type is a type parameter.
    /// `per_ctor_fields[c]` maps ctor `c`'s fields to their parameter indices
    /// (`[]` for a nullary ctor).
    pub(super) fn build_decidable_eq_parametric_multi(
        &mut self,
        ind_name: &Name,
        ctor_names: &[Name],
        num_params: usize,
        per_ctor_fields: &[Vec<usize>],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // Type 0 = Sort 1
        let l0 = Level::zero();
        let type0 = Expr::sort(l1.clone());
        let n_ctor = per_ctor_fields.len();
        if n_ctor < 2 || n_ctor != ctor_names.len() || num_params == 0 {
            return None;
        }
        if per_ctor_fields.iter().flatten().any(|&p| p >= num_params) {
            return None;
        }

        let params: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let insts: Vec<FVarId> = (0..num_params).map(|_| self.fresh_fvar()).collect();
        let a = self.fresh_fvar();
        let b = self.fresh_fvar();

        let fv = Expr::fvar;
        let param_args: Vec<Expr> = params.iter().map(|p| fv(*p)).collect();
        let ind_applied = Expr::apps(Expr::const_(ind_name.clone(), vec![]), param_args.clone());
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));

        // --- pure (self-free) helpers ---
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
        // `@ctor_c p… fields`
        let mk_ctor = |c: usize, fields: &[Expr]| {
            let mut args = param_args.clone();
            args.extend_from_slice(fields);
            Expr::apps(Expr::const_(ctor_names[c].clone(), vec![]), args)
        };

        // outer motive: `fun (x : Ind) => Decidable (x = b)`
        let outer_motive = {
            let ap = self.fresh_fvar();
            let m = decidable(&eq(&ind_applied, &fv(ap), &fv(b)));
            Expr::lam(
                BinderInfo::Default,
                ind_applied.clone(),
                m.abstract_fvar(ap),
            )
        };

        let mut outer_minors: Vec<Expr> = Vec::with_capacity(n_ctor);
        for i in 0..n_ctor {
            let flds_i = &per_ctor_fields[i];
            let m_i = flds_i.len();
            let xf_i: Vec<FVarId> = (0..m_i).map(|_| self.fresh_fvar()).collect();
            let x_fields: Vec<Expr> = xf_i.iter().map(|f| fv(*f)).collect();
            let mk_x = mk_ctor(i, &x_fields);

            // inner motive: `fun (y : Ind) => Decidable (mk_x = y)`
            let inner_motive = {
                let qp = self.fresh_fvar();
                let m = decidable(&eq(&ind_applied, &mk_x, &fv(qp)));
                Expr::lam(
                    BinderInfo::Default,
                    ind_applied.clone(),
                    m.abstract_fvar(qp),
                )
            };

            let mut inner_minors: Vec<Expr> = Vec::with_capacity(n_ctor);
            for j in 0..n_ctor {
                let flds_j = &per_ctor_fields[j];
                let m_j = flds_j.len();
                let yf_j: Vec<FVarId> = (0..m_j).map(|_| self.fresh_fvar()).collect();
                let y_fields: Vec<Expr> = yf_j.iter().map(|f| fv(*f)).collect();
                let mk_y = mk_ctor(j, &y_fields);
                let whole_eq = eq(&ind_applied, &mk_x, &mk_y);

                let decision = if i == j {
                    // DIAGONAL: decide ctor i's fields (mk_x = ctor_i xf, mk_y = ctor_i yf).
                    let heqf: Vec<FVarId> = (0..m_i).map(|_| self.fresh_fvar()).collect();

                    // isTrue congruence: mk x… = mk y… via Eq.trans over congrArg steps.
                    // point(k) = ctor_i with first k fields = y, rest = x.
                    let point = |k: usize| -> Expr {
                        let fields: Vec<Expr> = (0..m_i)
                            .map(|t| if t < k { fv(yf_j[t]) } else { fv(xf_i[t]) })
                            .collect();
                        mk_ctor(i, &fields)
                    };
                    let congruence: Option<Expr> = {
                        let mut proof: Option<Expr> = None;
                        for k in 0..m_i {
                            let fp = flds_i[k];
                            let t = self.fresh_fvar();
                            let hole_fields: Vec<Expr> = (0..m_i)
                                .map(|s| {
                                    if s < k {
                                        fv(yf_j[s])
                                    } else if s == k {
                                        fv(t)
                                    } else {
                                        fv(xf_i[s])
                                    }
                                })
                                .collect();
                            let hole_fn = Expr::lam(
                                BinderInfo::Default,
                                fv(params[fp]),
                                mk_ctor(i, &hole_fields).abstract_fvar(t),
                            );
                            let step = Expr::apps(
                                Expr::const_(
                                    Name::from_string("congrArg"),
                                    vec![l1.clone(), l1.clone()],
                                ),
                                [
                                    fv(params[fp]),
                                    ind_applied.clone(),
                                    fv(xf_i[k]),
                                    fv(yf_j[k]),
                                    hole_fn,
                                    fv(heqf[k]),
                                ],
                            );
                            proof = Some(match proof {
                                None => step,
                                Some(prev) => Expr::apps(
                                    Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
                                    [
                                        ind_applied.clone(),
                                        point(0),
                                        point(k),
                                        point(k + 1),
                                        prev,
                                        step,
                                    ],
                                ),
                            });
                        }
                        proof
                    };

                    // Nullary diagonal ctor: reflexive `isTrue (Eq.refl (mk_x))`.
                    if m_i == 0 {
                        let eq_refl = Expr::apps(
                            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                            [ind_applied.clone(), mk_x.clone()],
                        );
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                                whole_eq.clone(),
                            ),
                            eq_refl,
                        )
                    } else {
                        let is_true = Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                                whole_eq.clone(),
                            ),
                            congruence.expect("congruence present when m_i > 0"),
                        );

                        // Nested field decision, inner-first.
                        let mut body = is_true;
                        for k in (0..m_i).rev() {
                            let fp = flds_i[k];
                            let eq_k = eq(&fv(params[fp]), &fv(xf_i[k]), &fv(yf_j[k]));
                            let dec_motive = Expr::lam(
                                BinderInfo::Default,
                                decidable(&eq_k),
                                decidable(&whole_eq),
                            );
                            let inst_app = Expr::apps(fv(insts[fp]), [fv(xf_i[k]), fv(yf_j[k])]);

                            // unmkₖ : Ind → p_{fp}  (project field k of ctor i;
                            // other ctors' minors default to the in-scope xf_i[k]).
                            let unmk_k = {
                                let z = self.fresh_fvar();
                                let proj_motive = Expr::lam(
                                    BinderInfo::Default,
                                    ind_applied.clone(),
                                    fv(params[fp]),
                                );
                                let mut proj_minors: Vec<Expr> = Vec::with_capacity(n_ctor);
                                for (c, flds_c) in per_ctor_fields.iter().enumerate() {
                                    let gg: Vec<FVarId> =
                                        (0..flds_c.len()).map(|_| self.fresh_fvar()).collect();
                                    let mut minor = if c == i { fv(gg[k]) } else { fv(xf_i[k]) };
                                    for t in (0..flds_c.len()).rev() {
                                        minor = Expr::lam(
                                            BinderInfo::Default,
                                            fv(params[flds_c[t]]),
                                            minor.abstract_fvar(gg[t]),
                                        );
                                    }
                                    proj_minors.push(minor);
                                }
                                let mut proj_args = param_args.clone();
                                proj_args.push(proj_motive);
                                proj_args.push(fv(z));
                                proj_args.extend(proj_minors);
                                let body = Expr::apps(
                                    Expr::const_(cases_on.clone(), vec![l1.clone()]),
                                    proj_args,
                                );
                                Expr::lam(
                                    BinderInfo::Default,
                                    ind_applied.clone(),
                                    body.abstract_fvar(z),
                                )
                            };

                            // isFalse minor: λ (hne : ¬eq_k) => isFalse whole_eq
                            //   (λ (h : mk_x = mk_y) => hne (congrArg unmkₖ h))
                            let hne = self.fresh_fvar();
                            let h = self.fresh_fvar();
                            let congr = Expr::apps(
                                Expr::const_(
                                    Name::from_string("congrArg"),
                                    vec![l1.clone(), l1.clone()],
                                ),
                                [
                                    ind_applied.clone(),
                                    fv(params[fp]),
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
                            let not_ty = Expr::app(
                                Expr::const_(Name::from_string("Not"), vec![]),
                                eq_k.clone(),
                            );
                            let isfalse_minor =
                                Expr::lam(BinderInfo::Default, not_ty, is_false.abstract_fvar(hne));
                            let istrue_minor = Expr::lam(
                                BinderInfo::Default,
                                eq_k.clone(),
                                body.abstract_fvar(heqf[k]),
                            );
                            body = Expr::apps(
                                Expr::const_(
                                    Name::from_string("Decidable.casesOn"),
                                    vec![l1.clone()],
                                ),
                                [eq_k, dec_motive, inst_app, isfalse_minor, istrue_minor],
                            );
                        }
                        body
                    }
                } else {
                    // OFF-DIAGONAL: isFalse via the discriminator discᵢ.
                    // discᵢ : Ind p… → Prop  (ctor i ↦ True, others ↦ False)
                    let disc_i = {
                        let z = self.fresh_fvar();
                        let prop = Expr::sort(l0.clone());
                        let disc_motive = Expr::lam(BinderInfo::Default, ind_applied.clone(), prop);
                        let mut disc_minors: Vec<Expr> = Vec::with_capacity(n_ctor);
                        for (c, flds_c) in per_ctor_fields.iter().enumerate() {
                            let gg: Vec<FVarId> =
                                (0..flds_c.len()).map(|_| self.fresh_fvar()).collect();
                            let mut minor = if c == i {
                                Expr::const_(Name::from_string("True"), vec![])
                            } else {
                                Expr::const_(Name::from_string("False"), vec![])
                            };
                            for t in (0..flds_c.len()).rev() {
                                minor = Expr::lam(
                                    BinderInfo::Default,
                                    fv(params[flds_c[t]]),
                                    minor.abstract_fvar(gg[t]),
                                );
                            }
                            disc_minors.push(minor);
                        }
                        let mut disc_args = param_args.clone();
                        disc_args.push(disc_motive);
                        disc_args.push(fv(z));
                        disc_args.extend(disc_minors);
                        let body =
                            Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), disc_args);
                        Expr::lam(
                            BinderInfo::Default,
                            ind_applied.clone(),
                            body.abstract_fvar(z),
                        )
                    };
                    // neg : ¬(mk_x = mk_y) = λ (h : mk_x = mk_y) =>
                    //   @Eq.mp.{0} (discᵢ mk_x) (discᵢ mk_y)
                    //     (@congrArg.{1,1} Ind Prop mk_x mk_y discᵢ h) True.intro
                    let h = self.fresh_fvar();
                    let prop = Expr::sort(l0.clone());
                    let disc_x = Expr::app(disc_i.clone(), mk_x.clone());
                    let disc_y = Expr::app(disc_i.clone(), mk_y.clone());
                    let congr = Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [
                            ind_applied.clone(),
                            prop,
                            mk_x.clone(),
                            mk_y.clone(),
                            disc_i,
                            fv(h),
                        ],
                    );
                    let eq_mp = Expr::apps(
                        Expr::const_(Name::from_string("Eq.mp"), vec![l0.clone()]),
                        [
                            disc_x,
                            disc_y,
                            congr,
                            Expr::const_(Name::from_string("True.intro"), vec![]),
                        ],
                    );
                    let neg = Expr::lam(
                        BinderInfo::Default,
                        whole_eq.clone(),
                        eq_mp.abstract_fvar(h),
                    );
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                            whole_eq.clone(),
                        ),
                        neg,
                    )
                };

                // Bind ctor j's y-fields around the decision.
                let mut minor = decision;
                for k in (0..m_j).rev() {
                    minor = Expr::lam(
                        BinderInfo::Default,
                        fv(params[flds_j[k]]),
                        minor.abstract_fvar(yf_j[k]),
                    );
                }
                inner_minors.push(minor);
            }

            // inner casesOn on b
            let mut inner_args = param_args.clone();
            inner_args.push(inner_motive);
            inner_args.push(fv(b));
            inner_args.extend(inner_minors);
            let inner_cases =
                Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);

            // Bind ctor i's x-fields around the inner casesOn.
            let mut minor = inner_cases;
            for k in (0..m_i).rev() {
                minor = Expr::lam(
                    BinderInfo::Default,
                    fv(params[flds_i[k]]),
                    minor.abstract_fvar(xf_i[k]),
                );
            }
            outer_minors.push(minor);
        }

        // outer casesOn on a
        let mut outer_args = param_args.clone();
        outer_args.push(outer_motive);
        outer_args.push(fv(a));
        outer_args.extend(outer_minors);
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

        // λ {p…} [DecidableEq pᵢ] … : constraints innermost, then params.
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

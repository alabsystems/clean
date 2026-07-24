// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for a SINGLE-PARAMETER, DIRECTLY
//! self-recursive inductive (`Tree a | leaf | node : Tree a -> a -> Tree a -> Tree a`).
//!
//! Combines the parametric recursor of `beq_parametric_recursive.rs` with the
//! decision-proof machinery of `decidable_eq_parametric_multi.rs`. Drives
//! `@Ind.rec.{1} p motive minors… a b` with the DEPENDENT motive
//! `fun t => (t' : Ind p) → Decidable (t = t')`, so each recursive `Ind p`
//! sub-field gets an induction hypothesis `ih : (t' : Ind p) → Decidable (l = t')`.
//! Per constructor pair (via an inner `casesOn` on the second scrutinee):
//!
//! - same ctor: decide each field left-to-right through a nested
//!   `Decidable.casesOn` — a recursive field via `ih_k b_k`, the parameter field
//!   via the bound `[DecidableEq p]`; a differing field yields `isFalse`
//!   (projection injectivity), all-equal yields `isTrue` (an `Eq.trans` chain of
//!   `congrArg` steps).
//! - distinct ctors: `isFalse` via a `casesOn` discriminator (`disc_i : Ind p →
//!   Prop`, then `Eq.mp ∘ congrArg`), NoConfusion-free.
//!
//! Scoped to `num_params == 1`, num_motives = 1 (via
//! [`super::beq_parametric_recursive::classify_single_param_recursive`]).

use super::beq_parametric_recursive::RecField;
use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

impl<'a> ElabCtx<'a> {
    /// Build `λ {p : Type} [DecidableEq p] (a b : Ind p) => @Ind.rec.{1} p motive
    /// minors… a b`. `DecidableEq` is a def, so the value IS the function.
    pub(super) fn build_decidable_eq_parametric_recursive(
        &mut self,
        ind_name: &Name,
        per_ctor_fields: &[Vec<RecField>],
        ctor_names: &[Name],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero());
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
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Helpers.
        let eq = |ty: &Expr, u: &Expr, v: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
                [ty.clone(), u.clone(), v.clone()],
            )
        };
        let decidable = |prop: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                prop.clone(),
            )
        };
        // `@ctor_c p field…`
        let mk_ctor = |c: usize, fields: &[Expr]| {
            let mut args = vec![fv(p)];
            args.extend_from_slice(fields);
            Expr::apps(Expr::const_(ctor_names[c].clone(), vec![]), args)
        };
        let field_ty = |k: RecField| match k {
            RecField::Param => fv(p),
            RecField::SelfRec => ind_p.clone(),
        };

        // rec motive: `fun (mt : Ind p) => (t' : Ind p) → Decidable (mt = t')`.
        let rec_motive = {
            let mt = self.fresh_fvar();
            let tprime = self.fresh_fvar();
            let inner = decidable(&eq(&ind_p, &fv(mt), &fv(tprime)));
            let pi = Expr::pi(
                BinderInfo::Default,
                ind_p.clone(),
                inner.abstract_fvar(tprime),
            );
            Expr::lam(BinderInfo::Default, ind_p.clone(), pi.abstract_fvar(mt))
        };
        // IH type: `(t' : Ind p) → Decidable (fld = t')` for a bound recursive
        // field fvar `fld`.
        // (built per-use below since it depends on the field fvar)

        // Per-ctor a-field fvars, IH fvars (per SelfRec field), congruence eq-hyp
        // fvars (per field), and per-(i,j) b-field fvars.
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
        let heqf: Vec<Vec<FVarId>> = per_ctor_fields
            .iter()
            .map(|f| f.iter().map(|_| self.fresh_fvar()).collect())
            .collect();
        let bf: Vec<Vec<Vec<FVarId>>> = (0..n_ctor)
            .map(|_| {
                per_ctor_fields
                    .iter()
                    .map(|f| f.iter().map(|_| self.fresh_fvar()).collect())
                    .collect()
            })
            .collect();

        // Bind ctor `c`'s fields (innermost-first) around `body`.
        let bind_fields = |body: Expr, c: usize, fvars: &[Vec<FVarId>]| -> Expr {
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

        // Build the rec minors.
        let mut rec_args: Vec<Expr> = vec![fv(p), rec_motive];
        for i in 0..n_ctor {
            let flds_i = &per_ctor_fields[i];
            let m_i = flds_i.len();
            let a_fields: Vec<Expr> = af[i].iter().map(|f| fv(*f)).collect();
            let mk_a = mk_ctor(i, &a_fields);

            // inner casesOn motive: `fun (bb : Ind p) => Decidable (mk_a = bb)`.
            let inner_motive = {
                let bb = self.fresh_fvar();
                let m = decidable(&eq(&ind_p, &mk_a, &fv(bb)));
                Expr::lam(BinderInfo::Default, ind_p.clone(), m.abstract_fvar(bb))
            };

            let mut inner_args = vec![fv(p), inner_motive, fv(b)];
            for j in 0..n_ctor {
                let flds_j = &per_ctor_fields[j];
                let m_j = flds_j.len();
                let b_fields: Vec<Expr> = bf[i][j].iter().map(|f| fv(*f)).collect();
                let mk_b = mk_ctor(j, &b_fields);
                let whole_eq = eq(&ind_p, &mk_a, &mk_b);

                let decision = if i == j {
                    // DIAGONAL. Nullary ctor ⇒ reflexive isTrue.
                    if m_i == 0 {
                        let eq_refl = Expr::apps(
                            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
                            [ind_p.clone(), mk_a.clone()],
                        );
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                                whole_eq.clone(),
                            ),
                            eq_refl,
                        )
                    } else {
                        // isTrue congruence: mk_a = mk_b via Eq.trans over congrArg
                        // steps. point(k) = ctor i with first k fields = b, rest = a.
                        let point = |k: usize| -> Expr {
                            let fields: Vec<Expr> = (0..m_i)
                                .map(|t| if t < k { fv(bf[i][i][t]) } else { fv(af[i][t]) })
                                .collect();
                            mk_ctor(i, &fields)
                        };
                        let congruence = {
                            let mut proof: Option<Expr> = None;
                            for k in 0..m_i {
                                let fkty = field_ty(flds_i[k]);
                                let t = self.fresh_fvar();
                                let hole_fields: Vec<Expr> = (0..m_i)
                                    .map(|s| {
                                        if s < k {
                                            fv(bf[i][i][s])
                                        } else if s == k {
                                            fv(t)
                                        } else {
                                            fv(af[i][s])
                                        }
                                    })
                                    .collect();
                                let hole_fn = Expr::lam(
                                    BinderInfo::Default,
                                    fkty.clone(),
                                    mk_ctor(i, &hole_fields).abstract_fvar(t),
                                );
                                let step = Expr::apps(
                                    Expr::const_(
                                        Name::from_string("congrArg"),
                                        vec![l1.clone(), l1.clone()],
                                    ),
                                    [
                                        fkty.clone(),
                                        ind_p.clone(),
                                        fv(af[i][k]),
                                        fv(bf[i][i][k]),
                                        hole_fn,
                                        fv(heqf[i][k]),
                                    ],
                                );
                                proof = Some(match proof {
                                    None => step,
                                    Some(prev) => Expr::apps(
                                        Expr::const_(
                                            Name::from_string("Eq.trans"),
                                            vec![l1.clone()],
                                        ),
                                        [
                                            ind_p.clone(),
                                            point(0),
                                            point(k),
                                            point(k + 1),
                                            prev,
                                            step,
                                        ],
                                    ),
                                });
                            }
                            proof.expect("m_i > 0")
                        };
                        let is_true = Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                                whole_eq.clone(),
                            ),
                            congruence,
                        );

                        // Nested field decision, inner-first.
                        let mut ih_idx_by_field = vec![usize::MAX; m_i];
                        {
                            let mut c = 0;
                            for (k, fk) in flds_i.iter().enumerate() {
                                if *fk == RecField::SelfRec {
                                    ih_idx_by_field[k] = c;
                                    c += 1;
                                }
                            }
                        }
                        let mut body = is_true;
                        for k in (0..m_i).rev() {
                            let fkty = field_ty(flds_i[k]);
                            let eq_k = eq(&fkty, &fv(af[i][k]), &fv(bf[i][i][k]));
                            let dec_motive = Expr::lam(
                                BinderInfo::Default,
                                decidable(&eq_k),
                                decidable(&whole_eq),
                            );
                            // Field decision instance: SelfRec ⇒ `ih_k b_k`, Param
                            // ⇒ `@inst a_k b_k`.
                            let inst_app = match flds_i[k] {
                                RecField::SelfRec => {
                                    Expr::app(fv(ih[i][ih_idx_by_field[k]]), fv(bf[i][i][k]))
                                }
                                RecField::Param => {
                                    Expr::apps(fv(inst), [fv(af[i][k]), fv(bf[i][i][k])])
                                }
                            };

                            // unmkₖ : Ind p → fieldₖ ty (project field k; other
                            // ctors' minors default to the in-scope a-field).
                            let unmk_k = {
                                let z = self.fresh_fvar();
                                let proj_motive =
                                    Expr::lam(BinderInfo::Default, ind_p.clone(), fkty.clone());
                                let mut proj_minors: Vec<Expr> = vec![fv(p), proj_motive, fv(z)];
                                for (c, flds_c) in per_ctor_fields.iter().enumerate() {
                                    let gg: Vec<FVarId> =
                                        (0..flds_c.len()).map(|_| self.fresh_fvar()).collect();
                                    let mut minor = if c == i { fv(gg[k]) } else { fv(af[i][k]) };
                                    for t in (0..flds_c.len()).rev() {
                                        minor = Expr::lam(
                                            BinderInfo::Default,
                                            field_ty(flds_c[t]),
                                            minor.abstract_fvar(gg[t]),
                                        );
                                    }
                                    proj_minors.push(minor);
                                }
                                let body = Expr::apps(
                                    Expr::const_(cases_on.clone(), vec![l1.clone()]),
                                    proj_minors,
                                );
                                Expr::lam(BinderInfo::Default, ind_p.clone(), body.abstract_fvar(z))
                            };

                            let hne = self.fresh_fvar();
                            let h = self.fresh_fvar();
                            let congr = Expr::apps(
                                Expr::const_(
                                    Name::from_string("congrArg"),
                                    vec![l1.clone(), l1.clone()],
                                ),
                                [
                                    ind_p.clone(),
                                    fkty.clone(),
                                    mk_a.clone(),
                                    mk_b.clone(),
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
                                body.abstract_fvar(heqf[i][k]),
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
                    let disc_i = {
                        let z = self.fresh_fvar();
                        let prop = Expr::sort(Level::zero());
                        let disc_motive = Expr::lam(BinderInfo::Default, ind_p.clone(), prop);
                        let mut disc_minors: Vec<Expr> = vec![fv(p), disc_motive, fv(z)];
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
                                    field_ty(flds_c[t]),
                                    minor.abstract_fvar(gg[t]),
                                );
                            }
                            disc_minors.push(minor);
                        }
                        let body = Expr::apps(
                            Expr::const_(cases_on.clone(), vec![l1.clone()]),
                            disc_minors,
                        );
                        Expr::lam(BinderInfo::Default, ind_p.clone(), body.abstract_fvar(z))
                    };
                    let h = self.fresh_fvar();
                    let disc_a = Expr::app(disc_i.clone(), mk_a.clone());
                    let disc_b = Expr::app(disc_i.clone(), mk_b.clone());
                    let prop = Expr::sort(Level::zero());
                    let congr = Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
                        [
                            ind_p.clone(),
                            prop,
                            mk_a.clone(),
                            mk_b.clone(),
                            disc_i,
                            fv(h),
                        ],
                    );
                    let eq_mp = Expr::apps(
                        Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
                        [
                            disc_a,
                            disc_b,
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

                // Bind ctor j's b-fields around the decision.
                let mut minor = decision;
                for k in (0..m_j).rev() {
                    minor = Expr::lam(
                        BinderInfo::Default,
                        field_ty(flds_j[k]),
                        minor.abstract_fvar(bf[i][j][k]),
                    );
                }
                inner_args.push(minor);
            }

            let inner_cases =
                Expr::apps(Expr::const_(cases_on.clone(), vec![l1.clone()]), inner_args);
            let b_lam = Expr::lam(
                BinderInfo::Default,
                ind_p.clone(),
                inner_cases.abstract_fvar(b),
            );

            // Wrap IHs (innermost-first) then a-fields. IH type:
            // `(t' : Ind p) → Decidable (af_k = t')`.
            let mut minor = b_lam;
            // Map ih order back to the SelfRec fields (in field order).
            let selfrec_fields: Vec<usize> = flds_i
                .iter()
                .enumerate()
                .filter(|(_, f)| **f == RecField::SelfRec)
                .map(|(k, _)| k)
                .collect();
            for (ih_pos, &fk) in selfrec_fields.iter().enumerate().rev() {
                let tprime = self.fresh_fvar();
                let ih_ty = {
                    let inner = decidable(&eq(&ind_p, &fv(af[i][fk]), &fv(tprime)));
                    Expr::pi(
                        BinderInfo::Default,
                        ind_p.clone(),
                        inner.abstract_fvar(tprime),
                    )
                };
                minor = Expr::lam(
                    BinderInfo::Default,
                    ih_ty,
                    minor.abstract_fvar(ih[i][ih_pos]),
                );
            }
            minor = bind_fields(minor, i, &af);
            rec_args.push(minor);
        }
        rec_args.push(fv(a));
        rec_args.push(fv(b));
        let rec_app = Expr::apps(Expr::const_(rec_name, vec![l1.clone()]), rec_args);

        // λ (a b : Ind p) => rec_app, then [DecidableEq p], then {p}.
        let inner_b = Expr::lam(BinderInfo::Default, ind_p.clone(), rec_app.abstract_fvar(b));
        let ab_lam = Expr::lam(BinderInfo::Default, ind_p.clone(), inner_b.abstract_fvar(a));
        let mut result = ab_lam;
        let deceq_p = Expr::app(
            Expr::const_(Name::from_string("DecidableEq"), vec![l1.clone()]),
            fv(p),
        );
        result = Expr::lam(
            BinderInfo::InstImplicit,
            deceq_p,
            result.abstract_fvar(inst),
        );
        result = Expr::lam(BinderInfo::Implicit, type0, result.abstract_fvar(p));
        Some(result)
    }
}

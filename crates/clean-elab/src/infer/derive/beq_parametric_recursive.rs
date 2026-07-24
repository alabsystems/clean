// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `BEq` for a SINGLE-PARAMETER, DIRECTLY self-recursive
//! inductive (`Tree a | leaf | node : Tree a -> a -> Tree a -> Tree a`).
//!
//! Generalizes the monomorphic recursive builder (`beq_recursive.rs`) to a
//! parametric type by driving the parametric recursor `@Ind.rec.{1} p motive
//! minors… a b`: recursive `Ind p` sub-fields compare via the per-field
//! induction hypothesis (the recursor's `motive l = Ind p → Bool`), the
//! parameter field via the bound `[BEq p]`, distinct constructors via
//! `Bool.false`. Scoped to `num_params == 1` and the num_motives = 1 shape
//! (direct self-recursion, no nested container — those need the mutual-block
//! recursor). Built with fvars and abstracted once at the end.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};
use clean_parser::{SurfaceBinder, SurfaceCtor, SurfaceExpr};

/// A recursive-ctor field is either the sole type parameter or a direct
/// self-reference `Ind p`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum RecField {
    Param,
    SelfRec,
}

/// Classify a single-parameter inductive's constructors for the recursive BEq
/// builder. Each field must be either the parameter or `Ind p` (a direct
/// self-reference); at least one `SelfRec` field must exist (otherwise the
/// non-recursive multi-ctor builder is the right choice). `None` on any other
/// shape (multi-param, nested containers, non-parameter scalars).
pub(super) fn classify_single_param_recursive(
    ind_name: &Name,
    binders: &[SurfaceBinder],
    ctors: &[SurfaceCtor],
) -> Option<Vec<Vec<RecField>>> {
    fn peel(e: &SurfaceExpr) -> &SurfaceExpr {
        match e {
            SurfaceExpr::Paren(_, inner) => peel(inner),
            other => other,
        }
    }
    if binders.len() != 1 {
        return None;
    }
    let pname = binders[0].name.as_str();
    let short = ind_name.to_string();
    let short = short.rsplit('.').next().unwrap_or(&short);

    let mut per_ctor = Vec::with_capacity(ctors.len());
    let mut saw_rec = false;
    for ctor in ctors {
        let mut fields = Vec::new();
        let mut cur = peel(&ctor.ty);
        while let SurfaceExpr::Arrow(_, dom, cod) = cur {
            match peel(dom) {
                SurfaceExpr::Ident(_, n) if n == pname => fields.push(RecField::Param),
                // `Ind p` — head is the inductive, sole arg is the parameter.
                SurfaceExpr::App(_, head, args) => {
                    let head_ok = matches!(peel(head), SurfaceExpr::Ident(_, n) if n == short);
                    let arg_ok = args.len() == 1
                        && matches!(peel(&args[0].expr), SurfaceExpr::Ident(_, n) if n == pname);
                    if head_ok && arg_ok {
                        fields.push(RecField::SelfRec);
                        saw_rec = true;
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
            cur = peel(cod);
        }
        per_ctor.push(fields);
    }
    if saw_rec {
        Some(per_ctor)
    } else {
        None
    }
}

impl<'a> ElabCtx<'a> {
    /// Build `λ {p : Type} [BEq p] => @BEq.mk (Ind p) (fun a b => @Ind.rec.{1} p
    /// (fun _ => Ind p → Bool) minors… a b)` for a single-parameter, directly
    /// self-recursive inductive.
    pub(super) fn build_beq_parametric_recursive(
        &mut self,
        ind_name: &Name,
        per_ctor_fields: &[Vec<RecField>],
        ctor_names: &[Name],
    ) -> Option<Expr> {
        let l1 = Level::succ(Level::zero()); // motive universe (→ (Ind p → Bool) : Sort 1)
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
        // Ind p
        let ind_p = Expr::app(Expr::const_(ind_name.clone(), vec![]), fv(p));
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // rec motive: `fun (_ : Ind p) => Ind p → Bool`
        let rec_motive = Expr::lam(
            BinderInfo::Default,
            ind_p.clone(),
            Expr::arrow(ind_p.clone(), bool_ty.clone()),
        );
        // casesOn motive: `fun (_ : Ind p) => Bool`
        let cases_motive = Expr::lam(BinderInfo::Default, ind_p.clone(), bool_ty.clone());

        // Per-ctor field fvars (a-side, bound by the rec minor) + IH fvars
        // (one per SelfRec field, bound after the fields).
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
        // Per (outer i, inner j) b-side field fvars for the inner casesOn.
        let bf: Vec<Vec<Vec<FVarId>>> = (0..n_ctor)
            .map(|_| {
                per_ctor_fields
                    .iter()
                    .map(|f| f.iter().map(|_| self.fresh_fvar()).collect())
                    .collect()
            })
            .collect();

        // Field type for a RecField.
        let field_ty = |k: RecField| match k {
            RecField::Param => fv(p),
            RecField::SelfRec => ind_p.clone(),
        };

        // Bind ctor `c`'s fields (innermost-first) around `body`.
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

        // Build the rec minors.
        let mut rec_args: Vec<Expr> = vec![fv(p), rec_motive];
        for i in 0..n_ctor {
            // Inner casesOn over b: `@Ind.casesOn.{1} p cases_motive b inner_0 …`.
            let mut inner_args = vec![fv(p), cases_motive.clone(), fv(b)];
            for j in 0..n_ctor {
                let body_j = if i == j {
                    // &&-chain over ctor i's fields: SelfRec ⇒ `ih_k (bf_k)`,
                    // Param ⇒ `@BEq.beq p inst (af_k) (bf_k)`.
                    let flds = &per_ctor_fields[i];
                    if flds.is_empty() {
                        bool_true.clone()
                    } else {
                        // map field index → ih index (only SelfRec fields have an IH)
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
                                    Expr::const_(Name::from_string("BEq.beq"), vec![l0.clone()]),
                                    [fv(p), fv(inst), fv(af[i][k]), fv(bf[i][i][k])],
                                ),
                            };
                            cmps.push(cmp);
                        }
                        let mut acc = cmps.pop().expect("non-empty");
                        while let Some(c) = cmps.pop() {
                            acc = Expr::apps(
                                Expr::const_(Name::from_string("Bool.and"), vec![]),
                                [c, acc],
                            );
                        }
                        acc
                    }
                } else {
                    bool_false.clone()
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

            // Wrap the IHs (innermost-first) then the fields.
            let mut minor = b_lam;
            for k in (0..ih[i].len()).rev() {
                minor = Expr::lam(
                    BinderInfo::Default,
                    Expr::arrow(ind_p.clone(), bool_ty.clone()),
                    minor.abstract_fvar(ih[i][k]),
                );
            }
            minor = bind_ctor_fields(minor, i, &af);
            rec_args.push(minor);
        }
        rec_args.push(fv(a));
        rec_args.push(fv(b));
        let rec_app = Expr::apps(Expr::const_(rec_name, vec![l1.clone()]), rec_args);

        // λ (a b : Ind p) => rec_app
        let inner_b = Expr::lam(BinderInfo::Default, ind_p.clone(), rec_app.abstract_fvar(b));
        let ab_lam = Expr::lam(BinderInfo::Default, ind_p.clone(), inner_b.abstract_fvar(a));

        // @BEq.mk.{0} (Ind p) (fun a b => …), then [BEq p], then {p}.
        let mut result = Expr::apps(
            Expr::const_(Name::from_string("BEq.mk"), vec![l0.clone()]),
            [ind_p.clone(), ab_lam],
        );
        let beq_p = Expr::app(
            Expr::const_(Name::from_string("BEq"), vec![l0.clone()]),
            fv(p),
        );
        result = Expr::lam(BinderInfo::InstImplicit, beq_p, result.abstract_fvar(inst));
        result = Expr::lam(BinderInfo::Implicit, type0, result.abstract_fvar(p));
        Some(result)
    }
}

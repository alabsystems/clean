// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for monomorphic, multi-constructor
//! inductives with DIRECT self-recursive fields (`vector : Nat -> Ty -> Ty`),
//! driven by the type's own recursor `Ind.rec` so the equality of recursive
//! sub-terms is decided by the structural induction hypothesis.
//!
//! Wave-1/Track-L built real `DecidableEq` only for all-nullary enums and
//! (Track P) multi-field NON-recursive ctors; a recursive field forced a
//! `mk_sorry_with_level` fallback in `inductive.rs`. This module discharges
//! that obligation for the single-motive (`num_motives = 1`) direct-recursion
//! shape:
//!
//! ```text
//! fun (a b : Ind) =>
//!   @Ind.rec.{1}
//!     (motive := fun a' : Ind => (b : Ind) -> Decidable (a' = b))
//!     minor_c0 .. minor_cN
//!     a b
//! ```
//!
//! Each minor binds its ctor's fields plus an IH `(b : Ind) -> Decidable (fᵢ = b)`
//! per recursive field, and returns `fun (b : Ind) => Ind.casesOn b ...`. The
//! inner `casesOn` decides, field by field, via a nested `Decidable.casesOn`:
//! a scalar field uses its resolved `DecidableEq` instance, a recursive field
//! uses its IH applied to `b`'s matching sub-term. When all fields decide equal
//! the accumulated proofs are folded through `congrArg`/`Eq.trans` to witness
//! the whole-ctor equality (`isTrue`); a field mismatch short-circuits to
//! `isFalse` via `Ind.noConfusion`. A cross-constructor `b` is `isFalse` by
//! `noConfusion` directly.
//!
//! The produced term INFER-TYPES against the kernel-generated `Ind.rec` /
//! `Ind.casesOn` / `Ind.noConfusion`, and `decide (x = y)` reduces through the
//! recursor's iota rules — no `sorry`, empty `axiom_deps`.
//!
//! Only the direct (`num_motives = 1`) shape is handled here. A nested
//! `List Self` field (mutual block, `num_motives = 2`) is NOT covered; the
//! caller falls back for those (honestly reported).

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{SurfaceCtor, SurfaceExpr};

/// Classification of one constructor field for recursive DecidableEq.
#[derive(Clone)]
enum FieldKind {
    /// A direct self-reference (`Ind`): decided by the recursor IH.
    SelfRec,
    /// A non-recursive field with a resolved closed `DecidableEq` instance.
    Scalar { ty: Expr, inst: Expr },
}

/// One constructor analyzed for recursive DecidableEq.
#[derive(Clone)]
struct CtorAnalysis {
    /// Fully-qualified ctor name (`Ind.vector`).
    name: Name,
    fields: Vec<FieldKind>,
}

impl<'a> ElabCtx<'a> {
    /// Build a real recursive `DecidableEq` decision via `Ind.rec` for the
    /// direct self-recursion shape, or `None` (caller falls back) for shapes
    /// not supported (nested `List Self`, unresolved field instance, etc.).
    ///
    /// `ind_type` is `Ind`. `a`/`b` are `bvar 1` / `bvar 0` inside the outer
    /// `λ (a b : Ind)` the caller wraps around the returned body.
    pub(super) fn build_decidable_eq_recursive(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ctors: &[SurfaceCtor],
    ) -> Option<Expr> {
        let short = ind_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string();

        // Analyze every ctor; bail if any field is an unsupported recursive shape
        // (e.g. `List Self`) or lacks a closed `DecidableEq` instance.
        let mut analyzed = Vec::with_capacity(ctors.len());
        let mut saw_self_rec = false;
        for ctor in ctors {
            let ca = self.analyze_ctor_deceq_rec(ind_name, &short, ind_type, ctor)?;
            if ca.fields.iter().any(|f| matches!(f, FieldKind::SelfRec)) {
                saw_self_rec = true;
            }
            analyzed.push(ca);
        }
        // This builder is only worth taking when there is at least one direct
        // self-recursive field (otherwise the non-recursive fielded builder
        // already handles it).
        if !saw_self_rec {
            return None;
        }

        let level_one = Level::succ(Level::zero());
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Recursor motive: `fun a' : Ind => (b : Ind) -> Decidable (@Eq Ind a' b)`.
        // Inside the motive lambda, a' = bvar 1 under the `(b : Ind)` binder,
        // and b = bvar 0.
        let motive = {
            let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
            let eq_prop = mk_eq(&level_one, ind_type, &Expr::bvar(1), &Expr::bvar(0));
            let inner = Expr::arrow(ind_type.clone(), Expr::app(decidable, eq_prop));
            // `inner` = `(b : Ind) -> Decidable (a' = b)` with a' = bvar 0 here.
            Expr::lam(BinderInfo::Default, ind_type.clone(), inner)
        };

        // Build one minor per ctor.
        let mut minors = Vec::with_capacity(analyzed.len());
        for ca in &analyzed {
            minors.push(self.build_rec_minor_deceq_rec(ind_name, ind_type, &analyzed, ca)?);
        }

        // `@Ind.rec.{1} motive minor.. a b`.
        let mut rec_app = Expr::const_(rec_name, vec![level_one]);
        rec_app = Expr::app(rec_app, motive);
        for m in minors {
            rec_app = Expr::app(rec_app, m);
        }
        rec_app = Expr::app(rec_app, Expr::bvar(1)); // a -> (b:Ind)->Decidable(a=b)
        rec_app = Expr::app(rec_app, Expr::bvar(0)); // b -> Decidable(a=b)
        Some(rec_app)
    }

    /// Classify a ctor's fields; `None` if any field is unsupported.
    fn analyze_ctor_deceq_rec(
        &mut self,
        ind_name: &Name,
        short: &str,
        ind_type: &Expr,
        ctor: &SurfaceCtor,
    ) -> Option<CtorAnalysis> {
        let mut fields = Vec::new();
        self.collect_fields_deceq_rec(short, ind_type, &ctor.ty, &mut fields)?;
        // Use the FULLY-QUALIFIED inductive name to name the constructor; the
        // kernel registers ctors as `{ind_name}.{ctor}` (e.g. `N.Tree.leaf`).
        // `short` is retained only for surface-type self-recursion detection.
        Some(CtorAnalysis {
            name: Name::from_string(&format!("{ind_name}.{}", ctor.name)),
            fields,
        })
    }

    /// Peel a ctor's surface telescope, classifying each field.
    fn collect_fields_deceq_rec(
        &mut self,
        short: &str,
        ind_type: &Expr,
        surf: &SurfaceExpr,
        out: &mut Vec<FieldKind>,
    ) -> Option<()> {
        match surf {
            SurfaceExpr::Arrow(_, d, c) => {
                out.push(self.classify_field_deceq_rec(short, ind_type, d)?);
                self.collect_fields_deceq_rec(short, ind_type, c, out)
            }
            SurfaceExpr::Pi(span, binders, body) => {
                let b = binders.first()?;
                let t = b.ty.as_ref()?;
                out.push(self.classify_field_deceq_rec(short, ind_type, t)?);
                if binders.len() > 1 {
                    let tail = SurfaceExpr::Pi(*span, binders[1..].to_vec(), body.clone());
                    self.collect_fields_deceq_rec(short, ind_type, &tail, out)
                } else {
                    self.collect_fields_deceq_rec(short, ind_type, body, out)
                }
            }
            SurfaceExpr::Paren(_, inner) => {
                self.collect_fields_deceq_rec(short, ind_type, inner, out)
            }
            _ => Some(()),
        }
    }

    /// Classify a single field surface type into a [`FieldKind`].
    fn classify_field_deceq_rec(
        &mut self,
        short: &str,
        ind_type: &Expr,
        ty: &SurfaceExpr,
    ) -> Option<FieldKind> {
        let ty = peel_paren(ty);
        // Direct self reference.
        if let SurfaceExpr::Ident(_, n) = ty {
            if n == short {
                return Some(FieldKind::SelfRec);
            }
        }
        // Any OTHER mention of the inductive (e.g. `List Self`) is unsupported
        // here — bail so the caller falls back honestly.
        if surface_mentions(ty, short) {
            return None;
        }
        let elaborated = self.elaborate(ty).ok()?;
        if expr_mentions_const(&elaborated, ind_type) {
            return None;
        }
        let class = Name::from_string("DecidableEq");
        let goal = Expr::app(self.mk_const(&class), elaborated.clone());
        let inst = self.resolve_instance(&goal)?;
        if inst.has_fvar_quick() || self.has_metavars(&inst) {
            return None;
        }
        Some(FieldKind::Scalar {
            ty: elaborated,
            inst,
        })
    }

    /// Build a recursor minor: `fun (fields..) (ihs..) (b : Ind) => casesOn b ..`.
    fn build_rec_minor_deceq_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        all_ctors: &[CtorAnalysis],
        ca: &CtorAnalysis,
    ) -> Option<Expr> {
        // Fresh fvars for a's fields and the per-recursive-field IHs.
        let a_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ih_fvars: Vec<(usize, FVarId)> = ca
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| matches!(f, FieldKind::SelfRec))
            .map(|(i, _)| (i, self.fresh_fvar()))
            .collect();

        // a_applied = Ind.ctor a_fields..
        let ctor_c = Expr::const_(ca.name.clone(), vec![]);
        let a_applied = apply_fvars(&ctor_c, &a_fvars);

        let b_fvar = self.fresh_fvar();
        let inner = self.build_inner_decide_deceq_rec(
            ind_name, ind_type, all_ctors, ca, &a_fvars, &ih_fvars, &a_applied, b_fvar,
        )?;

        // fun (b : Ind) => inner
        let mut body = inner.abstract_fvar(b_fvar);
        body = Expr::lam(BinderInfo::Default, ind_type.clone(), body);

        // Abstract IHs (field order ⇒ reverse for innermost-first).
        for (idx, ih) in ih_fvars.iter().rev() {
            debug_assert!(matches!(ca.fields[*idx], FieldKind::SelfRec));
            body = body.abstract_fvar(*ih);
            // IH type: (b : Ind) -> Decidable (fᵢ = b).
            let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
            let level_one = Level::succ(Level::zero());
            let eq_prop = mk_eq(&level_one, ind_type, &Expr::bvar(0), &Expr::bvar(0));
            // Build `(b:Ind) -> Decidable (fᵢ = b)` where fᵢ is the field fvar.
            // Under the `(b:Ind)` binder, fᵢ is the captured fvar (closed) and b
            // is bvar 0.
            let _ = eq_prop;
            let ih_eq = mk_eq(
                &level_one,
                ind_type,
                &Expr::fvar(a_fvars[*idx]),
                &Expr::bvar(0),
            );
            let ih_body = Expr::app(decidable, ih_eq);
            let ih_ty = Expr::pi(BinderInfo::Default, ind_type.clone(), ih_body);
            // Abstracting the field fvar happens with the surrounding field
            // binders below; but the IH type references a_fvars[idx], which is
            // abstracted AFTER the IHs (fields are outermost). Since `body` here
            // still has a_fvars[idx] as a free fvar, and we add the IH binder
            // now, the field fvar in `ih_ty` will be abstracted by the field
            // loop below (it abstracts across the whole `body`, including binder
            // annotations). So leave `ih_ty` with the fvar in place.
            body = Expr::lam(BinderInfo::Default, ih_ty, body);
        }
        // Abstract fields (innermost-first).
        for k in (0..a_fvars.len()).rev() {
            body = body.abstract_fvar(a_fvars[k]);
            let fty = field_type(&ca.fields[k], ind_type);
            body = Expr::lam(BinderInfo::Default, fty, body);
        }
        Some(body)
    }

    /// Inner `casesOn` over `b`, deciding `a_applied = b` for each ctor of `b`.
    #[allow(clippy::too_many_arguments)]
    fn build_inner_decide_deceq_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        all_ctors: &[CtorAnalysis],
        ca: &CtorAnalysis,
        a_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
        b_fvar: FVarId,
    ) -> Option<Expr> {
        let level_one = Level::succ(Level::zero());
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);

        // Inner motive: `fun b' : Ind => Decidable (@Eq Ind a_applied b')`.
        let inner_motive = {
            let eq_prop = mk_eq(&level_one, ind_type, a_applied, &Expr::bvar(0));
            Expr::lam(
                BinderInfo::Default,
                ind_type.clone(),
                Expr::app(decidable.clone(), eq_prop),
            )
        };

        // Minors over b's ctor.
        let mut minors = Vec::with_capacity(all_ctors.len());
        for cb in all_ctors {
            let minor = if cb.name == ca.name {
                self.build_same_ctor_decision_deceq_rec(
                    ind_name, ind_type, ca, a_fvars, ih_fvars, a_applied,
                )?
            } else {
                self.build_diff_ctor_decision_deceq_rec(ind_name, ind_type, cb, a_applied)
            };
            minors.push(minor);
        }

        // `Ind.casesOn.{1} inner_motive b minor..`.
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut inner = Expr::const_(cases_on, vec![level_one]);
        inner = Expr::app(inner, inner_motive);
        inner = Expr::app(inner, Expr::fvar(b_fvar));
        for m in minors {
            inner = Expr::app(inner, m);
        }
        Some(inner)
    }

    /// Inner minor for a cross-constructor `b`: `isFalse` by `noConfusion`.
    fn build_diff_ctor_decision_deceq_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        cb: &CtorAnalysis,
        a_applied: &Expr,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);

        let b_fvars: Vec<FVarId> = cb.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_b = Expr::const_(cb.name.clone(), vec![]);
        let b_applied = apply_fvars(&ctor_b, &b_fvars);

        let eq_prop = mk_eq(&level_one, ind_type, a_applied, &b_applied);

        // neg : eq_prop -> False == fun e => noConfusion False (Cᵢ a) (Cⱼ b) e
        let e_fvar = self.fresh_fvar();
        let nc = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::const_(no_conf, vec![Level::zero()]), false_const),
                    a_applied.clone(),
                ),
                b_applied.clone(),
            ),
            Expr::fvar(e_fvar),
        );
        let neg = Expr::lam(
            BinderInfo::Default,
            eq_prop.clone(),
            nc.abstract_fvar(e_fvar),
        );
        let mut body = Expr::app(Expr::app(is_false, eq_prop), neg);

        // Abstract b's fields.
        for k in (0..b_fvars.len()).rev() {
            body = body.abstract_fvar(b_fvars[k]);
            body = Expr::lam(
                BinderInfo::Default,
                field_type(&cb.fields[k], ind_type),
                body,
            );
        }
        body
    }

    /// Inner minor when `b`'s ctor matches `a`'s: bind `b`'s fields and decide
    /// field by field (scalars via `DecidableEq`, recursive fields via IH),
    /// combining via `congrArg`/`Eq.trans` (`isTrue`) and `noConfusion`
    /// (`isFalse`).
    fn build_same_ctor_decision_deceq_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ca: &CtorAnalysis,
        a_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
    ) -> Option<Expr> {
        let b_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_c = Expr::const_(ca.name.clone(), vec![]);
        let b_applied = apply_fvars(&ctor_c, &b_fvars);

        // Nullary same ctor: reflexive isTrue.
        if ca.fields.is_empty() {
            let level_one = Level::succ(Level::zero());
            let whole_eq = mk_eq(&level_one, ind_type, a_applied, &b_applied);
            let refl = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.refl"), vec![level_one]),
                    ind_type.clone(),
                ),
                a_applied.clone(),
            );
            return Some(Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                    whole_eq,
                ),
                refl,
            ));
        }

        let heq_fvars: Vec<FVarId> = Vec::new();
        let mut decision = self.decide_from_field_rec(
            ind_name, ind_type, ca, &ctor_c, a_fvars, &b_fvars, ih_fvars, a_applied, &b_applied, 0,
            &heq_fvars,
        );

        // Abstract b's fields.
        for k in (0..b_fvars.len()).rev() {
            decision = decision.abstract_fvar(b_fvars[k]);
            decision = Expr::lam(
                BinderInfo::Default,
                field_type(&ca.fields[k], ind_type),
                decision,
            );
        }
        Some(decision)
    }

    /// Recursive driver mirroring the non-recursive fielded fold, but a
    /// recursive (`SelfRec`) field's decision comes from its IH `(b)->Decidable`
    /// rather than a `DecidableEq` instance.
    #[allow(clippy::too_many_arguments)]
    fn decide_from_field_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ca: &CtorAnalysis,
        ctor_c: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
        b_applied: &Expr,
        k: usize,
        heq_fvars: &[FVarId],
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let whole_eq = mk_eq(&level_one, ind_type, a_applied, b_applied);

        if k == ca.fields.len() {
            let proof = self.build_congr_chain_rec(
                &level_one, ind_type, ca, ctor_c, a_fvars, b_fvars, heq_fvars,
            );
            let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
            return Expr::app(Expr::app(is_true, whole_eq), proof);
        }

        let fa = Expr::fvar(a_fvars[k]);
        let fb = Expr::fvar(b_fvars[k]);

        // field type + per-field decision and field-eq prop.
        let (fty, field_eq, dec) = match &ca.fields[k] {
            FieldKind::Scalar { ty, inst } => {
                let feq = mk_eq(&level_one, ty, &fa, &fb);
                let d = Expr::app(Expr::app(inst.clone(), fa.clone()), fb.clone());
                (ty.clone(), feq, d)
            }
            FieldKind::SelfRec => {
                let ih = ih_fvars
                    .iter()
                    .find(|(i, _)| *i == k)
                    .map(|(_, id)| *id)
                    .expect("recursive field has IH");
                let feq = mk_eq(&level_one, ind_type, &fa, &fb);
                // IH applied to b's sub-term decides `fa = fb`.
                let d = Expr::app(Expr::fvar(ih), fb.clone());
                (ind_type.clone(), feq, d)
            }
        };

        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_cases_on = Name::from_string("Decidable.casesOn");
        let dec_field = Expr::app(decidable.clone(), field_eq.clone());

        // motive: fun (_ : Decidable field_eq) => Decidable whole_eq.
        let motive = Expr::lam(
            BinderInfo::Default,
            dec_field,
            Expr::app(decidable.clone(), whole_eq.clone()),
        );

        // isFalse minor.
        let isfalse_minor = self.build_isfalse_minor_rec(
            ind_name, ind_type, ca, a_fvars, b_fvars, a_applied, b_applied, &whole_eq, &field_eq, k,
        );

        // isTrue minor: fun (h_k : fa = fb) => decide_from_field(k+1, heq ++ [h_k]).
        let istrue_minor = {
            let h_fvar = self.fresh_fvar();
            let mut next = heq_fvars.to_vec();
            next.push(h_fvar);
            let body = self.decide_from_field_rec(
                ind_name,
                ind_type,
                ca,
                ctor_c,
                a_fvars,
                b_fvars,
                ih_fvars,
                a_applied,
                b_applied,
                k + 1,
                &next,
            );
            Expr::lam(
                BinderInfo::Default,
                field_eq.clone(),
                body.abstract_fvar(h_fvar),
            )
        };

        let _ = fty;
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut cases = Expr::const_(dec_cases_on, vec![level_one]);
        cases = Expr::app(cases, field_eq);
        cases = Expr::app(cases, motive);
        cases = Expr::app(cases, dec);
        cases = Expr::app(cases, isfalse_minor);
        cases = Expr::app(cases, istrue_minor);
        cases
    }

    /// `isFalse` minor for a field-`k` mismatch (recursive variant — identical
    /// `noConfusion` plumbing to the non-recursive builder).
    #[allow(clippy::too_many_arguments)]
    fn build_isfalse_minor_rec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ca: &CtorAnalysis,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        a_applied: &Expr,
        b_applied: &Expr,
        whole_eq: &Expr,
        field_eq_k: &Expr,
        k: usize,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let hne_fvar = self.fresh_fvar();
        let e_fvar = self.fresh_fvar();

        // Continuation: fun (e₀:a₀=b₀) … (e_{n-1}) => hne e_k.
        let ek_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        let mut cont = Expr::app(Expr::fvar(hne_fvar), Expr::fvar(ek_fvars[k]));
        for (i, f) in ca.fields.iter().enumerate().rev() {
            cont = cont.abstract_fvar(ek_fvars[i]);
            let ei_ty = mk_eq(
                &level_one,
                &field_type(f, ind_type),
                &Expr::fvar(a_fvars[i]),
                &Expr::fvar(b_fvars[i]),
            );
            cont = Expr::lam(BinderInfo::Default, ei_ty, cont);
        }

        let nc = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(no_conf, vec![Level::zero()]),
                        false_const.clone(),
                    ),
                    a_applied.clone(),
                ),
                b_applied.clone(),
            ),
            Expr::fvar(e_fvar),
        );
        let nc_applied = Expr::app(nc, cont);
        let neg = Expr::lam(
            BinderInfo::Default,
            whole_eq.clone(),
            nc_applied.abstract_fvar(e_fvar),
        );
        let body = Expr::app(Expr::app(is_false, whole_eq.clone()), neg);
        let hne_ty = Expr::arrow(field_eq_k.clone(), false_const);
        Expr::lam(BinderInfo::Default, hne_ty, body.abstract_fvar(hne_fvar))
    }

    /// Build `C a.. = C b..` from field-equality proofs via chained `congrArg` /
    /// `Eq.trans` (same fold as the non-recursive builder; recursive fields are
    /// `Ind`-typed so `congrArg`'s domain is `ind_type`).
    #[allow(clippy::too_many_arguments)]
    fn build_congr_chain_rec(
        &mut self,
        level_one: &Level,
        ind_type: &Expr,
        ca: &CtorAnalysis,
        ctor_c: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        heq_fvars: &[FVarId],
    ) -> Expr {
        let n = ca.fields.len();
        let congr_arg = Name::from_string("congrArg");

        let mid = |j: usize| -> Expr {
            let mut applied = ctor_c.clone();
            for i in 0..n {
                let arg = if i < j {
                    Expr::fvar(b_fvars[i])
                } else {
                    Expr::fvar(a_fvars[i])
                };
                applied = Expr::app(applied, arg);
            }
            applied
        };

        let mut acc: Option<Expr> = None;
        for k in 0..n {
            let fty = field_type(&ca.fields[k], ind_type);
            let fa = Expr::fvar(a_fvars[k]);
            let fb = Expr::fvar(b_fvars[k]);
            let h_k = Expr::fvar(heq_fvars[k]);

            let x_fvar = self.fresh_fvar();
            let mut applied = ctor_c.clone();
            for j in 0..n {
                let arg = if j < k {
                    Expr::fvar(b_fvars[j])
                } else if j == k {
                    Expr::fvar(x_fvar)
                } else {
                    Expr::fvar(a_fvars[j])
                };
                applied = Expr::app(applied, arg);
            }
            let f_k = Expr::lam(
                BinderInfo::Default,
                fty.clone(),
                applied.abstract_fvar(x_fvar),
            );

            let step = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        congr_arg.clone(),
                                        vec![level_one.clone(), level_one.clone()],
                                    ),
                                    fty,
                                ),
                                ind_type.clone(),
                            ),
                            fa,
                        ),
                        fb,
                    ),
                    f_k,
                ),
                h_k,
            );

            acc = Some(match acc {
                None => step,
                Some(prev) => eq_trans(
                    level_one,
                    ind_type,
                    &mid(0),
                    &mid(k),
                    &mid(k + 1),
                    prev,
                    step,
                ),
            });
        }
        acc.expect("non-empty fields")
    }
}

/// `head f₀ f₁ …` applied over field fvars.
fn apply_fvars(head: &Expr, fvars: &[FVarId]) -> Expr {
    let mut e = head.clone();
    for f in fvars {
        e = Expr::app(e, Expr::fvar(*f));
    }
    e
}

/// The kernel field type for a [`FieldKind`].
fn field_type(f: &FieldKind, ind_type: &Expr) -> Expr {
    match f {
        FieldKind::SelfRec => ind_type.clone(),
        FieldKind::Scalar { ty, .. } => ty.clone(),
    }
}

fn peel_paren(e: &SurfaceExpr) -> &SurfaceExpr {
    match e {
        SurfaceExpr::Paren(_, inner) => peel_paren(inner),
        other => other,
    }
}

/// `@Eq.{u} α a b`.
fn mk_eq(level: &Level, ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
                ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// `@Eq.trans.{u} α x y z p q : x = z`.
fn eq_trans(level: &Level, ty: &Expr, x: &Expr, y: &Expr, z: &Expr, p: Expr, q: Expr) -> Expr {
    let trans = Expr::const_(Name::from_string("Eq.trans"), vec![level.clone()]);
    let mut e = Expr::app(trans, ty.clone());
    e = Expr::app(e, x.clone());
    e = Expr::app(e, y.clone());
    e = Expr::app(e, z.clone());
    e = Expr::app(e, p);
    e = Expr::app(e, q);
    e
}

/// Whether a surface type mentions identifier `name`.
fn surface_mentions(expr: &SurfaceExpr, name: &str) -> bool {
    match expr {
        SurfaceExpr::Ident(_, n) => n == name,
        SurfaceExpr::App(_, h, args) => {
            surface_mentions(h, name) || args.iter().any(|a| surface_mentions(&a.expr, name))
        }
        SurfaceExpr::Arrow(_, l, r) => surface_mentions(l, name) || surface_mentions(r, name),
        SurfaceExpr::Paren(_, i) | SurfaceExpr::Ascription(_, i, _) => surface_mentions(i, name),
        _ => false,
    }
}

/// Whether an elaborated expr references the inductive's own type constant.
fn expr_mentions_const(expr: &Expr, ind_type: &Expr) -> bool {
    let target = match ind_type.kind() {
        ExprKind::Const(n, _) => n.clone(),
        _ => return false,
    };
    fn go(e: &Expr, target: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == target,
            ExprKind::App(f, a) => go(f, target) || go(a, target),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => go(t, target) || go(b, target),
            _ => false,
        }
    }
    go(expr, &target)
}

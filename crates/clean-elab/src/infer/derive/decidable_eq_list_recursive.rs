// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for a monomorphic inductive whose
//! constructors carry a NESTED `List Self` field (`tuple : List Ty -> Ty`),
//! driven by the kernel's mutual recursor `Ind.rec` (`num_motives = 2`).
//!
//! `decidable_eq_recursive.rs` (Track P) handles only the DIRECT self-recursion
//! shape (`num_motives = 1`, `vector : Nat -> Ty`); a `List Self` field forced a
//! `mk_sorry_with_level` fallback in `inductive.rs`. This module discharges that
//! obligation for the nested-`List` shape, exactly mirroring the recursive
//! `BEq` builder (`beq_recursive.rs`) but producing `Decidable (a = b)` proofs
//! instead of `Bool`.
//!
//! ## The restored nested recursor shape
//!
//! When a ctor field is `List Ind`, nested-inductive elimination temporarily
//! rewrites the declaration through a mutual helper. Restoration removes that
//! helper and exposes `Ind.tuple : List Ind -> Ind`, while `Ind.rec` and
//! `Ind.casesOn` retain two motives and `N + 2` minors (the primary constructors,
//! then `List.nil` and `List.cons`). List-valued inner elimination uses ordinary
//! `List.casesOn` and the standard parameterized `List.noConfusion`.
//!
//! ```text
//! fun (a b : Ind) =>
//!   @Ind.rec.{1}
//!     (motive_Ind  := fun a'  : Ind        => (b  : Ind)        -> Decidable (a'  = b))
//!     (motive_List := fun la' : List Ind => (lb : List Ind) -> Decidable (la' = lb))
//!     minor_c0 .. minor_cN  minor_nil  minor_cons
//!     a b
//! ```
//!
//! Each minor binds its ctor's fields plus an IH per recursive field — an
//! `Ind` field's IH is `(b : Ind) -> Decidable (f = b)`, while a `List Ind`
//! field's IH is `(lb : List Ind) -> Decidable (f = lb)` — and returns
//! `fun (b : major_ty) => casesOn b ...`. The inner `casesOn` decides field by
//! field through a nested `Decidable.casesOn`: a scalar field via its resolved
//! `DecidableEq` instance, a recursive (`Ind` / `List Ind`) field via its IH
//! applied to `b`'s matching sub-term. When all fields decide equal the proofs
//! are folded through `congrArg`/`Eq.trans`; a mismatch short-circuits to
//! `isFalse` via the relevant type's `noConfusion`. A cross-constructor `b` is
//! `isFalse` by `noConfusion` directly.
//!
//! Because the restored `Ind.casesOn` still requires the companion motive and
//! nil/cons minors, its off-type motive is the trivially inhabited
//! `fun _ => PUnit.{1}` and its off-type minors return `PUnit.unit.{1}`. These
//! branches are unreachable for an `Ind` major and exist only to satisfy the
//! registered eliminator telescope.
//!
//! The produced term infer-types against the restored `Ind.rec` /
//! `Ind.casesOn`, ordinary `List.casesOn`, and the relevant `*.noConfusion`;
//! moreover,
//! `decide (x = y)` reduces through the recursor's iota rules — no `sorry`,
//! empty `axiom_deps`.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{SurfaceCtor, SurfaceExpr};

/// Classification of one constructor field for the nested-`List` recursive
/// DecidableEq.
#[derive(Clone)]
enum FieldKind {
    /// A direct self-reference (`Ind`): decided by an `Ind` IH.
    SelfRec,
    /// A restored `List Ind` field, decided by its companion IH.
    ListSelf,
    /// A non-recursive field with a resolved closed `DecidableEq` instance.
    Scalar { ty: Expr, inst: Expr },
}

/// One constructor analyzed for recursive DecidableEq: fully-qualified ctor name
/// plus its field kinds in declaration order.
#[derive(Clone)]
struct CtorAnalysis {
    name: Name,
    fields: Vec<FieldKind>,
}

impl<'a> ElabCtx<'a> {
    /// Build a real `DecidableEq` decision via the mutual `Ind.rec` for the
    /// nested-`List Self` shape, or `None` (caller falls back) if the shape is
    /// not the nested-`List` shape this builder targets (no `List Self` field,
    /// an unresolved scalar instance, etc.).
    ///
    /// `ind_type` is `Ind`. `a`/`b` are `bvar 1` / `bvar 0` inside the outer
    /// `λ (a b : Ind)` the caller wraps around the returned body.
    pub(super) fn build_decidable_eq_list_recursive(
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
        // Nested restore removes the temporary `Ind._List` declaration and
        // exposes the declared container type again.  The primary recursor
        // keeps its companion motive/minors, but those rules are re-keyed to
        // the ordinary `List` constructors.
        let aux_name = Name::from_string("List");
        let aux_type = Expr::app(
            Expr::const_(aux_name.clone(), vec![Level::zero()]),
            ind_type.clone(),
        );

        // Analyze primary ctors; bail on any unsupported field shape.
        let mut primary = Vec::with_capacity(ctors.len());
        let mut saw_list = false;
        for ctor in ctors {
            let ca = self.analyze_ctor_listrec(ind_name, &short, ind_type, &aux_type, ctor)?;
            if ca.fields.iter().any(|f| matches!(f, FieldKind::ListSelf)) {
                saw_list = true;
            }
            primary.push(ca);
        }
        // This builder is ONLY for the nested-`List Self` (mutual) shape. A
        // shape with only direct self-recursion (or none) is handled by the
        // direct recursive / fielded builders — bail so the caller routes there.
        if !saw_list {
            return None;
        }

        // Restored companion rules use the real List constructors.
        let aux_nil = CtorAnalysis {
            name: Name::from_string("List.nil"),
            fields: vec![],
        };
        let aux_cons = CtorAnalysis {
            name: Name::from_string("List.cons"),
            fields: vec![FieldKind::SelfRec, FieldKind::ListSelf],
        };

        // Complete restored rule set for Ind.rec/Ind.casesOn. List.casesOn uses
        // the filtered List.nil/List.cons subset below.
        let mut all_targets: Vec<CtorAnalysis> = primary.clone();
        all_targets.push(aux_nil.clone());
        all_targets.push(aux_cons.clone());

        let level_one = Level::succ(Level::zero());
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Real recursor motives.
        // motive_Ind  : fun a'  : Ind       => (b  : Ind)       -> Decidable (a'  = b)
        let motive_ind = self.mk_dec_motive_listrec(ind_type, ind_type);
        // motive_List : fun la' : List Ind => (lb : List Ind) -> Decidable (la' = lb)
        let motive_list = self.mk_dec_motive_listrec(&aux_type, &aux_type);

        // Build minors: primary ctors (decl order), then aux nil, aux cons.
        let mut minors: Vec<Expr> = Vec::with_capacity(primary.len() + 2);
        for ca in &primary {
            minors.push(self.build_minor_listrec(
                ind_name,
                ind_type,
                &aux_name,
                &aux_type,
                &all_targets,
                ca,
                /* major_is_aux */ false,
            )?);
        }
        for ca in [&aux_nil, &aux_cons] {
            minors.push(self.build_minor_listrec(
                ind_name,
                ind_type,
                &aux_name,
                &aux_type,
                &all_targets,
                ca,
                /* major_is_aux */ true,
            )?);
        }

        // `@Ind.rec.{1} motive_Ind motive_List minor.. a b`.
        let mut rec_app = Expr::const_(rec_name, vec![level_one]);
        rec_app = Expr::app(rec_app, motive_ind);
        rec_app = Expr::app(rec_app, motive_list);
        for m in minors {
            rec_app = Expr::app(rec_app, m);
        }
        rec_app = Expr::app(rec_app, Expr::bvar(1)); // a -> (b:Ind) -> Decidable (a=b)
        rec_app = Expr::app(rec_app, Expr::bvar(0)); // b -> Decidable (a=b)
        Some(rec_app)
    }

    /// `fun a' : self_ty => (b : self_ty) -> Decidable (@Eq self_ty a' b)`.
    fn mk_dec_motive_listrec(&mut self, self_ty: &Expr, b_ty: &Expr) -> Expr {
        let level_one = Level::succ(Level::zero());
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        // Under the (b) binder: a' = bvar 1, b = bvar 0.
        let eq_prop = mk_eq(&level_one, self_ty, &Expr::bvar(1), &Expr::bvar(0));
        let inner = Expr::pi(
            BinderInfo::Default,
            b_ty.clone(),
            Expr::app(decidable, eq_prop),
        );
        Expr::lam(BinderInfo::Default, self_ty.clone(), inner)
    }

    /// Classify a ctor's fields; `None` on any unsupported field.
    fn analyze_ctor_listrec(
        &mut self,
        ind_name: &Name,
        short: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        ctor: &SurfaceCtor,
    ) -> Option<CtorAnalysis> {
        let mut fields = Vec::new();
        self.collect_fields_listrec(short, ind_type, aux_type, &ctor.ty, &mut fields)?;
        // The kernel registers ctors under the fully-qualified inductive name
        // (`{ind_name}.{ctor}`); `short` is only for surface-recursion detection.
        Some(CtorAnalysis {
            name: Name::from_string(&format!("{ind_name}.{}", ctor.name)),
            fields,
        })
    }

    /// Peel a ctor's surface telescope, classifying each field.
    fn collect_fields_listrec(
        &mut self,
        short: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        surf: &SurfaceExpr,
        out: &mut Vec<FieldKind>,
    ) -> Option<()> {
        match surf {
            SurfaceExpr::Arrow(_, d, c) => {
                out.push(self.classify_field_listrec(short, ind_type, aux_type, d)?);
                self.collect_fields_listrec(short, ind_type, aux_type, c, out)
            }
            SurfaceExpr::Pi(span, binders, body) => {
                let b = binders.first()?;
                let t = b.ty.as_ref()?;
                out.push(self.classify_field_listrec(short, ind_type, aux_type, t)?);
                if binders.len() > 1 {
                    let tail = SurfaceExpr::Pi(*span, binders[1..].to_vec(), body.clone());
                    self.collect_fields_listrec(short, ind_type, aux_type, &tail, out)
                } else {
                    self.collect_fields_listrec(short, ind_type, aux_type, body, out)
                }
            }
            SurfaceExpr::Paren(_, inner) => {
                self.collect_fields_listrec(short, ind_type, aux_type, inner, out)
            }
            _ => Some(()),
        }
    }

    /// Classify a single field surface type.
    fn classify_field_listrec(
        &mut self,
        short: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        ty: &SurfaceExpr,
    ) -> Option<FieldKind> {
        let ty = peel_paren(ty);
        // Direct self reference: `Ind`.
        if let SurfaceExpr::Ident(_, n) = ty {
            if n == short {
                return Some(FieldKind::SelfRec);
            }
        }
        // Restored nested-recursive container: `List Ind`.
        if let SurfaceExpr::App(_, head, args) = ty {
            if let SurfaceExpr::Ident(_, container) = peel_paren(head) {
                if container == "List" && args.len() == 1 {
                    if let SurfaceExpr::Ident(_, n) = peel_paren(&args[0].expr) {
                        if n == short {
                            return Some(FieldKind::ListSelf);
                        }
                    }
                }
            }
        }
        // Any OTHER mention of the inductive is unsupported here.
        if surface_mentions(ty, short) {
            return None;
        }
        let elaborated = self.elaborate(ty).ok()?;
        if expr_mentions_ind(&elaborated, ind_type, aux_type) {
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

    /// Build one recursor minor: bind ctor fields + per-recursive-field IHs, then
    /// `fun (b : major_ty) => inner_casesOn`.
    fn build_minor_listrec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        aux_name: &Name,
        aux_type: &Expr,
        all_targets: &[CtorAnalysis],
        ca: &CtorAnalysis,
        major_is_aux: bool,
    ) -> Option<Expr> {
        let a_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        // IH per recursive field (SelfRec or ListSelf), in field order.
        let ih_fvars: Vec<(usize, FVarId)> = ca
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| matches!(f, FieldKind::SelfRec | FieldKind::ListSelf))
            .map(|(i, _)| (i, self.fresh_fvar()))
            .collect();

        let ctor_c = ctor_head_listrec(ca, aux_name, ind_type);
        let a_applied = apply_fvars(&ctor_c, &a_fvars);
        let major_ty = if major_is_aux { aux_type } else { ind_type };

        let b_fvar = self.fresh_fvar();
        let inner = self.build_inner_decide_listrec(
            ind_name,
            ind_type,
            aux_name,
            aux_type,
            all_targets,
            ca,
            &a_fvars,
            &ih_fvars,
            &a_applied,
            major_is_aux,
            b_fvar,
        )?;

        // fun (b : major_ty) => inner
        let mut body = inner.abstract_fvar(b_fvar);
        body = Expr::lam(BinderInfo::Default, major_ty.clone(), body);

        // Abstract IHs (field order ⇒ reverse for innermost-first).
        for (idx, ih) in ih_fvars.iter().rev() {
            body = body.abstract_fvar(*ih);
            let ih_ty = self.mk_ih_ty_listrec(&ca.fields[*idx], ind_type, aux_type, a_fvars[*idx]);
            body = Expr::lam(BinderInfo::Default, ih_ty, body);
        }
        // Abstract fields (innermost-first).
        for k in (0..a_fvars.len()).rev() {
            body = body.abstract_fvar(a_fvars[k]);
            let fty = field_type(&ca.fields[k], ind_type, aux_type);
            body = Expr::lam(BinderInfo::Default, fty, body);
        }
        Some(body)
    }

    /// IH type for a recursive field `fᵢ` (the captured field fvar): a
    /// `SelfRec` field decides against `Ind`, a `ListSelf` field against
    /// `List Ind`. Type: `(x : sub_ty) -> Decidable (fᵢ = x)`.
    fn mk_ih_ty_listrec(
        &mut self,
        fk: &FieldKind,
        ind_type: &Expr,
        aux_type: &Expr,
        field_fvar: FVarId,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let sub_ty = match fk {
            FieldKind::SelfRec => ind_type.clone(),
            FieldKind::ListSelf => aux_type.clone(),
            FieldKind::Scalar { .. } => unreachable!("scalar fields have no IH"),
        };
        // Under (x), fᵢ is the captured fvar (closed) and x is bvar 0.
        let eq_prop = mk_eq(&level_one, &sub_ty, &Expr::fvar(field_fvar), &Expr::bvar(0));
        Expr::pi(BinderInfo::Default, sub_ty, Expr::app(decidable, eq_prop))
    }

    /// Inner `casesOn` over `b`, deciding `a_applied = b` per constructor.
    /// Restored `Ind.casesOn` gets both motives and the full minor set; ordinary
    /// `List.casesOn` gets only its real motive and nil/cons minors.
    #[allow(clippy::too_many_arguments)]
    fn build_inner_decide_listrec(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        aux_name: &Name,
        aux_type: &Expr,
        all_targets: &[CtorAnalysis],
        ca: &CtorAnalysis,
        a_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
        major_is_aux: bool,
        b_fvar: FVarId,
    ) -> Option<Expr> {
        let level_one = Level::succ(Level::zero());
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let cases_on = if major_is_aux {
            Name::from_string("List.casesOn")
        } else {
            Name::from_string(&format!("{ind_name}.casesOn"))
        };
        let major_ty = if major_is_aux { aux_type } else { ind_type };

        // Real motive for the major's type.  `Ind.casesOn` remains a
        // two-motive restored recursor, whereas ordinary `List.casesOn` has
        // only its own motive.
        let real_motive = {
            let eq_prop = mk_eq(&level_one, major_ty, a_applied, &Expr::bvar(0));
            Expr::lam(
                BinderInfo::Default,
                major_ty.clone(),
                Expr::app(decidable.clone(), eq_prop),
            )
        };
        let dummy_motive_aux = mk_punit_motive(aux_type);

        // Minors over each target ctor.
        let mut minors = Vec::with_capacity(all_targets.len());
        for tb in all_targets {
            // Whether this target belongs to the major's type (Ind ctors when
            // major is Ind; aux ctors when major is aux).
            let target_is_aux = is_aux_ctor(&tb.name, aux_name);
            if major_is_aux && !target_is_aux {
                continue;
            }
            let minor = if target_is_aux != major_is_aux {
                // Off-type target: never reached; inhabit the dummy PUnit motive.
                const_punit_minor(tb, ind_type, aux_type)
            } else if tb.name == ca.name {
                self.build_same_ctor_decision_listrec(
                    ind_name, aux_name, ind_type, aux_type, ca, a_fvars, ih_fvars, a_applied,
                )?
            } else {
                self.build_diff_ctor_decision_listrec(
                    ind_name,
                    aux_name,
                    ind_type,
                    aux_type,
                    tb,
                    a_applied,
                    major_is_aux,
                )
            };
            minors.push(minor);
        }

        // Lean-faithful casesOn order: parameters, motive, major, minors.
        let mut inner = if major_is_aux {
            let list_cases = Expr::const_(cases_on, vec![level_one, Level::zero()]);
            let list_cases = Expr::app(list_cases, ind_type.clone());
            Expr::app(list_cases, real_motive)
        } else {
            let ind_cases = Expr::const_(cases_on, vec![level_one]);
            let ind_cases = Expr::app(ind_cases, real_motive);
            Expr::app(ind_cases, dummy_motive_aux)
        };
        inner = Expr::app(inner, Expr::fvar(b_fvar));
        for m in minors {
            inner = Expr::app(inner, m);
        }
        Some(inner)
    }

    /// Inner minor for a cross-constructor `b` (same type as `a`): `isFalse` via
    /// the type's `noConfusion`.
    #[allow(clippy::too_many_arguments)]
    fn build_diff_ctor_decision_listrec(
        &mut self,
        ind_name: &Name,
        aux_name: &Name,
        ind_type: &Expr,
        aux_type: &Expr,
        tb: &CtorAnalysis,
        a_applied: &Expr,
        major_is_aux: bool,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let major_ty = if major_is_aux { aux_type } else { ind_type };
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);

        let b_fvars: Vec<FVarId> = tb.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_b = ctor_head_listrec(tb, aux_name, ind_type);
        let b_applied = apply_fvars(&ctor_b, &b_fvars);

        let eq_prop = mk_eq(&level_one, major_ty, a_applied, &b_applied);

        let e_fvar = self.fresh_fvar();
        let nc = if major_is_aux {
            list_noconfusion_app(
                ind_type,
                aux_type,
                a_applied,
                &b_applied,
                Expr::fvar(e_fvar),
            )
        } else {
            let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(no_conf, vec![Level::zero()]), false_const),
                        a_applied.clone(),
                    ),
                    b_applied.clone(),
                ),
                Expr::fvar(e_fvar),
            )
        };
        let neg = Expr::lam(
            BinderInfo::Default,
            eq_prop.clone(),
            nc.abstract_fvar(e_fvar),
        );
        let mut body = Expr::app(Expr::app(is_false, eq_prop), neg);

        for k in (0..b_fvars.len()).rev() {
            body = body.abstract_fvar(b_fvars[k]);
            body = Expr::lam(
                BinderInfo::Default,
                field_type(&tb.fields[k], ind_type, aux_type),
                body,
            );
        }
        body
    }

    /// Inner minor when `b`'s ctor matches `a`'s: bind `b`'s fields, decide field
    /// by field (scalars via instance, recursive via IH), combine via
    /// `congrArg`/`Eq.trans` and `noConfusion`.
    #[allow(clippy::too_many_arguments)]
    fn build_same_ctor_decision_listrec(
        &mut self,
        ind_name: &Name,
        aux_name: &Name,
        ind_type: &Expr,
        aux_type: &Expr,
        ca: &CtorAnalysis,
        a_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
    ) -> Option<Expr> {
        let major_is_aux = is_aux_ctor(&ca.name, aux_name);
        let major_ty = if major_is_aux { aux_type } else { ind_type };
        let b_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_c = ctor_head_listrec(ca, aux_name, ind_type);
        let b_applied = apply_fvars(&ctor_c, &b_fvars);

        // Nullary same ctor (e.g. nil): reflexive isTrue.
        if ca.fields.is_empty() {
            let level_one = Level::succ(Level::zero());
            let whole_eq = mk_eq(&level_one, major_ty, a_applied, &b_applied);
            let refl = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.refl"), vec![level_one]),
                    major_ty.clone(),
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
        let mut decision = self.decide_from_field_listrec(
            ind_name, aux_name, ind_type, aux_type, ca, &ctor_c, major_ty, a_fvars, &b_fvars,
            ih_fvars, a_applied, &b_applied, 0, &heq_fvars,
        );

        for k in (0..b_fvars.len()).rev() {
            decision = decision.abstract_fvar(b_fvars[k]);
            decision = Expr::lam(
                BinderInfo::Default,
                field_type(&ca.fields[k], ind_type, aux_type),
                decision,
            );
        }
        Some(decision)
    }

    /// Recursive field-fold driver (mirrors the direct recursive builder, but a
    /// `ListSelf` field's decision comes from its `List Ind` IH).
    #[allow(clippy::too_many_arguments)]
    fn decide_from_field_listrec(
        &mut self,
        ind_name: &Name,
        aux_name: &Name,
        ind_type: &Expr,
        aux_type: &Expr,
        ca: &CtorAnalysis,
        ctor_c: &Expr,
        major_ty: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        a_applied: &Expr,
        b_applied: &Expr,
        k: usize,
        heq_fvars: &[FVarId],
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let whole_eq = mk_eq(&level_one, major_ty, a_applied, b_applied);

        if k == ca.fields.len() {
            let proof = self.build_congr_chain_listrec(
                &level_one, ind_type, aux_type, ca, ctor_c, major_ty, a_fvars, b_fvars, heq_fvars,
            );
            let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
            return Expr::app(Expr::app(is_true, whole_eq), proof);
        }

        let fa = Expr::fvar(a_fvars[k]);
        let fb = Expr::fvar(b_fvars[k]);

        let (field_eq, dec) = match &ca.fields[k] {
            FieldKind::Scalar { ty, inst } => {
                let feq = mk_eq(&level_one, ty, &fa, &fb);
                let d = Expr::app(Expr::app(inst.clone(), fa.clone()), fb.clone());
                (feq, d)
            }
            FieldKind::SelfRec => {
                let ih = find_ih(ih_fvars, k);
                let feq = mk_eq(&level_one, ind_type, &fa, &fb);
                let d = Expr::app(Expr::fvar(ih), fb.clone());
                (feq, d)
            }
            FieldKind::ListSelf => {
                let ih = find_ih(ih_fvars, k);
                let feq = mk_eq(&level_one, aux_type, &fa, &fb);
                let d = Expr::app(Expr::fvar(ih), fb.clone());
                (feq, d)
            }
        };

        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_cases_on = Name::from_string("Decidable.casesOn");
        let dec_field = Expr::app(decidable.clone(), field_eq.clone());

        let motive = Expr::lam(
            BinderInfo::Default,
            dec_field,
            Expr::app(decidable.clone(), whole_eq.clone()),
        );

        let isfalse_minor = self.build_isfalse_minor_listrec(
            ind_name, aux_name, ind_type, aux_type, ca, a_fvars, b_fvars, a_applied, b_applied,
            &whole_eq, &field_eq, k,
        );

        let istrue_minor = {
            let h_fvar = self.fresh_fvar();
            let mut next = heq_fvars.to_vec();
            next.push(h_fvar);
            let body = self.decide_from_field_listrec(
                ind_name,
                aux_name,
                ind_type,
                aux_type,
                ca,
                ctor_c,
                major_ty,
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

        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut cases = Expr::const_(dec_cases_on, vec![level_one]);
        cases = Expr::app(cases, field_eq);
        cases = Expr::app(cases, motive);
        cases = Expr::app(cases, dec);
        cases = Expr::app(cases, isfalse_minor);
        cases = Expr::app(cases, istrue_minor);
        cases
    }

    /// `isFalse` minor for a field-`k` mismatch (the type's `noConfusion`).
    #[allow(clippy::too_many_arguments)]
    fn build_isfalse_minor_listrec(
        &mut self,
        ind_name: &Name,
        aux_name: &Name,
        ind_type: &Expr,
        aux_type: &Expr,
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
        let major_is_aux = is_aux_ctor(&ca.name, aux_name);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let hne_fvar = self.fresh_fvar();
        let e_fvar = self.fresh_fvar();

        // Continuation: fun (e₀:a₀=b₀) … (e_{n-1}) => hne e_k.
        let ek_fvars: Vec<FVarId> = ca.fields.iter().map(|_| self.fresh_fvar()).collect();
        let mismatch_proof = if major_is_aux {
            mk_eq_of_heq_listrec(
                &field_type(&ca.fields[k], ind_type, aux_type),
                &Expr::fvar(a_fvars[k]),
                &Expr::fvar(b_fvars[k]),
                Expr::fvar(ek_fvars[k]),
            )
        } else {
            Expr::fvar(ek_fvars[k])
        };
        let mut cont = Expr::app(Expr::fvar(hne_fvar), mismatch_proof);
        for (i, f) in ca.fields.iter().enumerate().rev() {
            cont = cont.abstract_fvar(ek_fvars[i]);
            let field_ty = field_type(f, ind_type, aux_type);
            let ei_ty = if major_is_aux {
                mk_heq_listrec(&field_ty, &Expr::fvar(a_fvars[i]), &Expr::fvar(b_fvars[i]))
            } else {
                mk_eq(
                    &level_one,
                    &field_ty,
                    &Expr::fvar(a_fvars[i]),
                    &Expr::fvar(b_fvars[i]),
                )
            };
            cont = Expr::lam(BinderInfo::Default, ei_ty, cont);
        }

        let nc = if major_is_aux {
            list_noconfusion_app(ind_type, aux_type, a_applied, b_applied, Expr::fvar(e_fvar))
        } else {
            let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
            Expr::app(
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
            )
        };
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

    /// `C a.. = C b..` via chained `congrArg`/`Eq.trans`; each field's `congrArg`
    /// domain is its field type (`Ind`, `List Ind`, or a scalar type).
    #[allow(clippy::too_many_arguments)]
    fn build_congr_chain_listrec(
        &mut self,
        level_one: &Level,
        ind_type: &Expr,
        aux_type: &Expr,
        ca: &CtorAnalysis,
        ctor_c: &Expr,
        major_ty: &Expr,
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
            let fty = field_type(&ca.fields[k], ind_type, aux_type);
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

            // @congrArg.{1,1} T_k major_ty a_k b_k f_k h_k : mid(k) = mid(k+1).
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
                                major_ty.clone(),
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
                    major_ty,
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

/// Find the IH fvar for field index `k` (must be recursive).
fn find_ih(ih_fvars: &[(usize, FVarId)], k: usize) -> FVarId {
    ih_fvars
        .iter()
        .find(|(i, _)| *i == k)
        .map(|(_, id)| *id)
        .expect("recursive field must have an IH")
}

/// Is `ctor` one of the restored companion `List` constructors?
fn is_aux_ctor(ctor: &Name, aux_name: &Name) -> bool {
    ctor == &Name::append(aux_name, "nil") || ctor == &Name::append(aux_name, "cons")
}

/// Constructor head with restored List parameters made explicit.  The
/// companion recursor minors mention `List.nil`/`List.cons`, but their ordinary
/// polymorphic constants still require the element type parameter.
fn ctor_head_listrec(ca: &CtorAnalysis, aux_name: &Name, ind_type: &Expr) -> Expr {
    if is_aux_ctor(&ca.name, aux_name) {
        Expr::app(
            Expr::const_(ca.name.clone(), vec![Level::zero()]),
            ind_type.clone(),
        )
    } else {
        Expr::const_(ca.name.clone(), vec![])
    }
}

/// `@HEq.{1} ty a ty b`, used by the v4.30 parameterized List noConfusion
/// convention.  Both instantiated element parameters are identical here.
fn mk_heq_listrec(ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    let level_one = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("HEq"), vec![level_one]),
                    ty.clone(),
                ),
                a.clone(),
            ),
            ty.clone(),
        ),
        b.clone(),
    )
}

/// Convert a diagonal HEq field premise back to Eq for the field decision's
/// negative hypothesis.
fn mk_eq_of_heq_listrec(ty: &Expr, a: &Expr, b: &Expr, h: Expr) -> Expr {
    let level_one = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("eq_of_heq"), vec![level_one]),
                    ty.clone(),
                ),
                a.clone(),
            ),
            b.clone(),
        ),
        h,
    )
}

/// Apply `List.noConfusion` using Lean 4.30's heterogeneous convention for a
/// parameterized inductive.  In addition to the two instantiated element
/// parameters it requires their reflexive equality and a heterogeneous form
/// of the list equality major premise.
fn list_noconfusion_app(
    ind_type: &Expr,
    list_type: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    eq_proof: Expr,
) -> Expr {
    let level_zero = Level::zero();
    let level_one = Level::succ(level_zero.clone());
    let level_two = Level::succ(level_one.clone());
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let mut nc = Expr::const_(
        Name::from_string("List.noConfusion"),
        vec![level_zero, Level::zero()],
    );
    nc = Expr::app(nc, false_const);
    nc = Expr::app(nc, ind_type.clone());
    nc = Expr::app(nc, lhs.clone());
    nc = Expr::app(nc, ind_type.clone());
    nc = Expr::app(nc, rhs.clone());

    // The parameter domain is `Type`, whose type is `Sort 2` in the kernel's
    // universe accounting.
    let param_refl = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), vec![level_two]),
            Expr::sort(level_one.clone()),
        ),
        ind_type.clone(),
    );
    nc = Expr::app(nc, param_refl);

    let major_heq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("heq_of_eq"), vec![level_one]),
                    list_type.clone(),
                ),
                lhs.clone(),
            ),
            rhs.clone(),
        ),
        eq_proof,
    );
    Expr::app(nc, major_heq)
}

/// `fun _ : self_ty => PUnit.{1}` — a trivially-inhabited dummy motive.
fn mk_punit_motive(self_ty: &Expr) -> Expr {
    let punit = Expr::const_(Name::from_string("PUnit"), vec![Level::succ(Level::zero())]);
    Expr::lam(BinderInfo::Default, self_ty.clone(), punit)
}

/// A minor inhabiting the dummy `PUnit` motive: binds `b`'s fields, returns
/// `PUnit.unit.{1}`.
fn const_punit_minor(target: &CtorAnalysis, ind_type: &Expr, aux_type: &Expr) -> Expr {
    let unit = Expr::const_(
        Name::from_string("PUnit.unit"),
        vec![Level::succ(Level::zero())],
    );
    let mut body = unit;
    for k in (0..target.fields.len()).rev() {
        let fty = field_type(&target.fields[k], ind_type, aux_type);
        body = Expr::lam(BinderInfo::Default, fty, body);
    }
    body
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
fn field_type(f: &FieldKind, ind_type: &Expr, aux_type: &Expr) -> Expr {
    match f {
        FieldKind::SelfRec => ind_type.clone(),
        FieldKind::ListSelf => aux_type.clone(),
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

/// Whether an elaborated expr references the inductive's own type or aux type.
fn expr_mentions_ind(expr: &Expr, ind_type: &Expr, _aux_type: &Expr) -> bool {
    fn go(e: &Expr, ind: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == ind,
            ExprKind::App(f, a) => go(f, ind) || go(a, ind),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => go(t, ind) || go(b, ind),
            _ => false,
        }
    }
    let ind = match ind_type.kind() {
        ExprKind::Const(n, _) => n.clone(),
        _ => return false,
    };
    go(expr, &ind)
}

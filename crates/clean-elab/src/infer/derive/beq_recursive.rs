// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Genuinely-recursive `BEq` body for monomorphic, multi-constructor inductives
//! whose constructors carry *recursive* fields — a direct self reference
//! (`vector : Nat -> Ty -> Ty`) or a nested `List` of the type being defined
//! (`tuple : List Ty -> Ty`).
//!
//! Wave-2's `beq_inductive.rs` bound only NON-recursive fields and fell back to
//! a weak `x == x ⇒ true` body for recursive/nested fields — a correctness bug
//! (`vector 1 int == vector 2 int` returned `true`). This module fixes that for
//! the trust-ir `Ty` shape by driving the kernel's **own recursor** `Ind.rec`,
//! whose minors supply induction hypotheses for recursive fields, so a
//! self-recursive ctor compares its sub-terms with the type's OWN `BEq` and a
//! `List Ind` field compares element-wise via the element `BEq`.
//!
//! ## Two recursor shapes, one builder
//!
//! There are two distinct kernel recursor shapes a recursive enum can produce,
//! and the SAME enum may need both (real trust-ir `Ty` has `vector : Nat -> Ty`
//! AND `tuple : List Ty -> Ty`):
//!
//! * **Direct self-recursion** (`num_motives = 1`). When NO ctor field is a
//!   nested container of self, the kernel keeps a single-type inductive. `Ind.rec`
//!   has one motive `motive_Ind`, one minor per ctor, and the minor for a
//!   self-recursive field carries an IH `Ind -> Bool` for that field. The inner
//!   `Ind.casesOn` is the ordinary single-motive eliminator.
//!
//! * **Nested-`List` restored block** (`num_motives = 2`). For a `List Ind`
//!   field, nested-inductive elimination temporarily introduces a mutual helper
//!   and then restores the public declaration to the source-level `List Ind`
//!   shape. The helper constants are erased, while `Ind.rec` and `Ind.casesOn`
//!   retain the companion `List Ind` motive and the `List.nil`/`List.cons`
//!   minors. Inner elimination of a list uses the ordinary `List.casesOn`.
//!
//! In both shapes:
//!
//! ```text
//! beq a b :=
//!   @Ind.rec.{1}
//!     (motive_Ind  := fun _ : Ind        => Ind -> Bool)
//!     [ (motive_List := fun _ : List Ind => List Ind -> Bool) ]  -- only if List
//!     minor_c0 .. minor_cN [minor_nil minor_cons]
//!     a b
//! ```
//!
//! Each minor receives the constructor fields plus an IH for every recursive
//! field (IH for an `Ind` field is `Ind -> Bool`, for a `List Ind` field it is
//! `List Ind -> Bool`) and returns the inner comparator that `casesOn`s the
//! *second* value. For mismatched constructors the comparator is `false`; for a
//! match it `&&`-chains field comparisons: recursive fields via their IH, scalar
//! fields via the resolved `@BEq.beq fieldTy inst`.
//!
//! This discharges the ty#4145-class soundness obligation for real: distinct
//! values compare `false`, and the produced term is kernel-checked against the
//! genuine `Ind.rec` after the inductive (and its recursor) are registered.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{SurfaceCtor, SurfaceExpr};

/// Classification of one constructor field for recursive BEq.
#[derive(Clone)]
enum FieldKind {
    /// A direct self-reference: the field has type `Ind` itself.
    SelfRec,
    /// A restored `List Ind` field, compared element-wise via its companion IH.
    ListSelf,
    /// A non-recursive field of the given (elaborated) type, compared via the
    /// resolved `@BEq.beq fieldTy inst`.
    Scalar { ty: Expr, inst: Expr },
}

/// One constructor analyzed for recursive BEq: fully-qualified ctor name plus
/// its field kinds in declaration order. Used both as a recursor minor source
/// and as an inner-`casesOn` target.
#[derive(Clone)]
struct CtorAnalysis {
    name: Name,
    fields: Vec<FieldKind>,
}

impl<'a> ElabCtx<'a> {
    /// Build a real recursive `BEq` body via `Ind.rec`, covering BOTH the direct
    /// self-recursion (`num_motives = 1`) and nested-`List`-of-self
    /// (`num_motives = 2`) shapes, or return `None` if the shape is not one this
    /// builder supports (so the caller falls back).
    ///
    /// `a_ref` / `b_ref` are the two `Ind` arguments (typically `bvar 1` /
    /// `bvar 0` inside the outer `λ a b`).
    pub(super) fn build_beq_recursive(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ctors: &[SurfaceCtor],
        a_ref: &Expr,
        b_ref: &Expr,
    ) -> Option<Expr> {
        let short = ind_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string();
        // Nested restore erases the temporary `Ind._List` mirror and restores
        // every exposed domain to the declared container application.
        let aux_name = Name::from_string("List");
        let aux_type = Expr::app(
            Expr::const_(aux_name.clone(), vec![Level::zero()]),
            ind_type.clone(),
        );

        // Analyze the primary constructors. Bail on any unsupported field type.
        let mut primary = Vec::with_capacity(ctors.len());
        let mut saw_recursive = false;
        let mut saw_list = false;
        for ctor in ctors {
            let analysis = self.analyze_ctor_fields(ind_name, &short, ind_type, &aux_type, ctor)?;
            for f in &analysis.fields {
                match f {
                    FieldKind::SelfRec => saw_recursive = true,
                    FieldKind::ListSelf => {
                        saw_recursive = true;
                        saw_list = true;
                    }
                    FieldKind::Scalar { .. } => {}
                }
            }
            primary.push(analysis);
        }
        // Only handle shapes that actually have a recursive field — otherwise the
        // non-recursive field-binding builder is the right (and simpler) choice.
        if !saw_recursive {
            return None;
        }

        // `num_motives = 2` iff a `List Self` field forced a nested mutual block;
        // otherwise the inductive is a single self-recursive type (1 motive).
        let has_list = saw_list;
        let num_motives = if has_list { 2 } else { 1 };

        // Restored auxiliary rules are keyed to the real List constructors.
        // Only relevant when a `List Self` field forced the mutual block.
        let aux_nil = CtorAnalysis {
            name: Name::from_string("List.nil"),
            fields: vec![],
        };
        let aux_cons = CtorAnalysis {
            name: Name::from_string("List.cons"),
            fields: vec![FieldKind::SelfRec, FieldKind::ListSelf],
        };

        // `Ind.casesOn` retains the complete restored minor set (primary ctors,
        // then List.nil/List.cons). Inner list elimination uses ordinary
        // `List.casesOn`, so its target list is filtered to those two rules.
        let mut all_targets: Vec<CtorAnalysis> = primary.clone();
        if has_list {
            all_targets.push(aux_nil.clone());
            all_targets.push(aux_cons.clone());
        }

        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);

        // Recursor motives: `fun _ => T -> Bool`, one per type in the block.
        let motive_ind = Expr::lam(
            BinderInfo::Default,
            ind_type.clone(),
            Expr::arrow(ind_type.clone(), bool_ty()),
        );
        let motive_list = Expr::lam(
            BinderInfo::Default,
            aux_type.clone(),
            Expr::arrow(aux_type.clone(), bool_ty()),
        );

        // Build minors: primary ctors (decl order), then (mutual only) aux nil,
        // aux cons.
        let mut minors: Vec<Expr> = Vec::with_capacity(primary.len() + 2);
        for analysis in &primary {
            minors.push(self.build_rec_minor(
                ind_type,
                &aux_type,
                ind_name,
                &aux_name,
                analysis,
                /* major_is_aux */ false,
                num_motives,
                &all_targets,
                &bool_true,
                &bool_false,
            ));
        }
        if has_list {
            for analysis in [&aux_nil, &aux_cons] {
                minors.push(self.build_rec_minor(
                    ind_type,
                    &aux_type,
                    ind_name,
                    &aux_name,
                    analysis,
                    /* major_is_aux */ true,
                    num_motives,
                    &all_targets,
                    &bool_true,
                    &bool_false,
                ));
            }
        }

        // `@Ind.rec.{1} motive_Ind [motive_List] minor... a b`
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));
        let level_one = Level::succ(Level::zero());
        let mut rec_app = Expr::const_(rec_name, vec![level_one]);
        rec_app = Expr::app(rec_app, motive_ind);
        if has_list {
            rec_app = Expr::app(rec_app, motive_list);
        }
        for m in minors {
            rec_app = Expr::app(rec_app, m);
        }
        rec_app = Expr::app(rec_app, a_ref.clone()); // -> motive_Ind a = (Ind -> Bool)
        rec_app = Expr::app(rec_app, b_ref.clone()); // -> Bool
        Some(rec_app)
    }

    /// Classify each field of a constructor. Returns `None` if any field type is
    /// unsupported (so the whole derive falls back safely).
    fn analyze_ctor_fields(
        &mut self,
        ind_name: &Name,
        short_ind: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        ctor: &SurfaceCtor,
    ) -> Option<CtorAnalysis> {
        let mut fields = Vec::new();
        self.collect_surface_fields(short_ind, ind_type, aux_type, &ctor.ty, &mut fields)?;
        // The kernel registers ctors under the fully-qualified inductive name
        // (`{ind_name}.{ctor}`); `short_ind` is only for surface-recursion
        // detection in `collect_surface_fields`.
        Some(CtorAnalysis {
            name: Name::from_string(&format!("{ind_name}.{}", ctor.name)),
            fields,
        })
    }

    /// Peel a constructor's surface arrow/Pi telescope, classifying each field.
    fn collect_surface_fields(
        &mut self,
        short_ind: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        surf: &SurfaceExpr,
        out: &mut Vec<FieldKind>,
    ) -> Option<()> {
        match surf {
            SurfaceExpr::Arrow(_, d, c) => {
                out.push(self.classify_field(short_ind, ind_type, aux_type, d)?);
                self.collect_surface_fields(short_ind, ind_type, aux_type, c, out)
            }
            SurfaceExpr::Pi(span, binders, body) => {
                let Some(b) = binders.first() else {
                    return Some(());
                };
                let t = b.ty.as_ref()?;
                out.push(self.classify_field(short_ind, ind_type, aux_type, t)?);
                if binders.len() > 1 {
                    let tail = SurfaceExpr::Pi(*span, binders[1..].to_vec(), body.clone());
                    self.collect_surface_fields(short_ind, ind_type, aux_type, &tail, out)
                } else {
                    self.collect_surface_fields(short_ind, ind_type, aux_type, body, out)
                }
            }
            SurfaceExpr::Paren(_, inner) => {
                self.collect_surface_fields(short_ind, ind_type, aux_type, inner, out)
            }
            // Return type reached (the inductive itself): no more fields.
            _ => Some(()),
        }
    }

    /// Classify a single field surface type into a [`FieldKind`].
    fn classify_field(
        &mut self,
        short_ind: &str,
        ind_type: &Expr,
        aux_type: &Expr,
        ty: &SurfaceExpr,
    ) -> Option<FieldKind> {
        let ty = peel_paren(ty);
        // Direct self reference: `Ind`.
        if let SurfaceExpr::Ident(_, n) = ty {
            if n == short_ind {
                return Some(FieldKind::SelfRec);
            }
        }
        // Restored nested-recursive container: `List Ind`.
        if let SurfaceExpr::App(_, head, args) = ty {
            if let SurfaceExpr::Ident(_, container) = peel_paren(head) {
                if container == "List" && args.len() == 1 {
                    if let SurfaceExpr::Ident(_, n) = peel_paren(&args[0].expr) {
                        if n == short_ind {
                            return Some(FieldKind::ListSelf);
                        }
                    }
                }
            }
        }
        // Otherwise: a non-recursive scalar field. Elaborate its type, reject any
        // residual mention of the inductive, and resolve a CLOSED `BEq` instance.
        let elaborated = self.elaborate(ty).ok()?;
        if expr_mentions_ind(&elaborated, ind_type, aux_type) {
            return None;
        }
        let beq_class = Name::from_string("BEq");
        let goal = Expr::app(self.mk_const(&beq_class), elaborated.clone());
        let inst = self.resolve_instance(&goal)?;
        if inst.has_fvar_quick() || self.has_metavars(&inst) {
            return None;
        }
        Some(FieldKind::Scalar {
            ty: elaborated,
            inst,
        })
    }

    /// Build one recursor minor: a function taking the ctor's fields, then (for
    /// each recursive field, in field order) its IH, returning the inner
    /// comparator `λ (b : major_ty) => casesOn b ...`.
    #[allow(clippy::too_many_arguments)]
    fn build_rec_minor(
        &mut self,
        ind_type: &Expr,
        aux_type: &Expr,
        ind_name: &Name,
        aux_name: &Name,
        analysis: &CtorAnalysis,
        major_is_aux: bool,
        num_motives: usize,
        all_targets: &[CtorAnalysis],
        bool_true: &Expr,
        bool_false: &Expr,
    ) -> Expr {
        // Fresh fvars for fields, then for the IHs of recursive fields.
        let field_fvars: Vec<FVarId> = analysis.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ih_fvars: Vec<(usize, FVarId)> = analysis
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| matches!(f, FieldKind::SelfRec | FieldKind::ListSelf))
            .map(|(i, _)| (i, self.fresh_fvar()))
            .collect();

        let major_ty = if major_is_aux { aux_type } else { ind_type };
        let b_fvar = self.fresh_fvar();
        let inner = self.build_inner_compare(
            ind_type,
            aux_type,
            ind_name,
            aux_name,
            major_is_aux,
            num_motives,
            analysis,
            &field_fvars,
            &ih_fvars,
            all_targets,
            b_fvar,
            bool_true,
            bool_false,
        );
        let mut body = inner.abstract_fvar(b_fvar);
        body = Expr::lam(BinderInfo::Default, major_ty.clone(), body);

        // Abstract the IHs (in field order ⇒ reverse for innermost-first).
        for (idx, ih) in ih_fvars.iter().rev() {
            body = body.abstract_fvar(*ih);
            let ih_ty = match analysis.fields[*idx] {
                FieldKind::SelfRec => Expr::arrow(ind_type.clone(), bool_ty()),
                FieldKind::ListSelf => Expr::arrow(aux_type.clone(), bool_ty()),
                FieldKind::Scalar { .. } => unreachable!("scalar fields have no IH"),
            };
            body = Expr::lam(BinderInfo::Default, ih_ty, body);
        }
        // Abstract the fields (innermost-first).
        for k in (0..field_fvars.len()).rev() {
            body = body.abstract_fvar(field_fvars[k]);
            let fty = field_kind_type(&analysis.fields[k], ind_type, aux_type);
            body = Expr::lam(BinderInfo::Default, fty, body);
        }
        body
    }

    /// Build the inner `casesOn` over the *second* value `b_fvar`, comparing the
    /// captured constructor's fields/IHs against `b`'s matching fields.
    #[allow(clippy::too_many_arguments)]
    fn build_inner_compare(
        &mut self,
        ind_type: &Expr,
        aux_type: &Expr,
        ind_name: &Name,
        _aux_name: &Name,
        major_is_aux: bool,
        num_motives: usize,
        analysis: &CtorAnalysis,
        a_field_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        targets: &[CtorAnalysis],
        b_fvar: FVarId,
        bool_true: &Expr,
        bool_false: &Expr,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let cases_on_name = if major_is_aux {
            Name::from_string("List.casesOn")
        } else {
            Name::from_string(&format!("{ind_name}.casesOn"))
        };

        // The restored `Ind.casesOn` takes all registered motives and minors.
        // Ordinary `List.casesOn` takes only the element parameter, list motive,
        // major, and its nil/cons minors.
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let m_ind = Expr::lam(BinderInfo::Default, ind_type.clone(), bool_ty());
        let m_list = Expr::lam(BinderInfo::Default, aux_type.clone(), bool_ty());

        let mut cases = if major_is_aux {
            // List.casesOn.{motive, element} (A := Ind)
            Expr::app(
                Expr::const_(cases_on_name, vec![level_one, Level::zero()]),
                ind_type.clone(),
            )
        } else {
            Expr::const_(cases_on_name, vec![level_one])
        };
        if major_is_aux {
            cases = Expr::app(cases, m_list);
        } else {
            cases = Expr::app(cases, m_ind);
            if num_motives == 2 {
                cases = Expr::app(cases, m_list);
            }
        }
        cases = Expr::app(cases, Expr::fvar(b_fvar)); // major = b

        for target in targets
            .iter()
            .filter(|target| !major_is_aux || is_list_companion_ctor(&target.name))
        {
            let minor = if target.name == analysis.name {
                self.build_same_ctor_minor(
                    ind_type,
                    aux_type,
                    analysis,
                    target,
                    a_field_fvars,
                    ih_fvars,
                    bool_true,
                )
            } else {
                const_minor(target, ind_type, aux_type, bool_false.clone())
            };
            cases = Expr::app(cases, minor);
        }
        cases
    }

    /// A minor for the case where `b`'s ctor matches the captured ctor: bind
    /// `b`'s fields and `&&`-chain field comparisons.
    #[allow(clippy::too_many_arguments)]
    fn build_same_ctor_minor(
        &mut self,
        ind_type: &Expr,
        aux_type: &Expr,
        analysis: &CtorAnalysis,
        target: &CtorAnalysis,
        a_field_fvars: &[FVarId],
        ih_fvars: &[(usize, FVarId)],
        bool_true: &Expr,
    ) -> Expr {
        let b_field_fvars: Vec<FVarId> = target.fields.iter().map(|_| self.fresh_fvar()).collect();
        let bool_and = Name::from_string("Bool.and");

        let mut acc: Option<Expr> = None;
        for (k, fk) in analysis.fields.iter().enumerate() {
            let a = Expr::fvar(a_field_fvars[k]);
            let b = Expr::fvar(b_field_fvars[k]);
            let cmp = match fk {
                FieldKind::SelfRec | FieldKind::ListSelf => {
                    // IH for this field index. The recursor IH for a recursive
                    // field has type `subterm_ty -> Bool`; apply to b's subterm.
                    let ih = ih_fvars
                        .iter()
                        .find(|(i, _)| *i == k)
                        .map(|(_, id)| *id)
                        .expect("recursive field must have IH");
                    let _ = a; // captured subterm is implicit in the IH closure
                    Expr::app(Expr::fvar(ih), b)
                }
                FieldKind::Scalar { ty, inst } => {
                    let beq_beq = self.mk_const_str("BEq.beq");
                    Expr::app(
                        Expr::app(Expr::app(Expr::app(beq_beq, ty.clone()), inst.clone()), a),
                        b,
                    )
                }
            };
            acc = Some(match acc {
                None => cmp,
                Some(prev) => {
                    Expr::app(Expr::app(Expr::const_(bool_and.clone(), vec![]), prev), cmp)
                }
            });
        }
        let mut body = acc.unwrap_or_else(|| bool_true.clone());

        // Abstract b's fields (innermost-first).
        for k in (0..b_field_fvars.len()).rev() {
            body = body.abstract_fvar(b_field_fvars[k]);
            let fty = field_kind_type(&target.fields[k], ind_type, aux_type);
            body = Expr::lam(BinderInfo::Default, fty, body);
        }
        body
    }
}

/// Whether `name` is one of the two real `List` constructors retained as
/// companion rules after nested-inductive restoration.
///
/// This must be an exact structural-name check. A namespace-prefix check would
/// also classify ordinary user constructors such as `List.Tree.leaf` as
/// companion rules and over-apply `List.casesOn` with primary-inductive minors.
fn is_list_companion_ctor(name: &Name) -> bool {
    name == &Name::from_string("List.nil") || name == &Name::from_string("List.cons")
}

/// A minor that ignores `b`'s fields and returns a constant Bool.
fn const_minor(target: &CtorAnalysis, ind_type: &Expr, aux_type: &Expr, value: Expr) -> Expr {
    let mut body = value;
    for k in (0..target.fields.len()).rev() {
        let fty = field_kind_type(&target.fields[k], ind_type, aux_type);
        body = Expr::lam(BinderInfo::Default, fty, body);
    }
    body
}

/// The kernel type of a field by its [`FieldKind`].
fn field_kind_type(f: &FieldKind, ind_type: &Expr, aux_type: &Expr) -> Expr {
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

fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

/// Whether `expr` mentions the inductive's own type constant or its aux type.
fn expr_mentions_ind(expr: &Expr, ind_type: &Expr, aux_type: &Expr) -> bool {
    fn go(e: &Expr, ind: &Name, aux: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == ind || n == aux,
            ExprKind::App(f, a) => go(f, ind, aux) || go(a, ind, aux),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => go(t, ind, aux) || go(b, ind, aux),
            _ => false,
        }
    }
    let ind = match ind_type.kind() {
        ExprKind::Const(n, _) => n.clone(),
        _ => return false,
    };
    let aux = match aux_type.kind() {
        ExprKind::Const(n, _) => n.clone(),
        _ => ind.clone(),
    };
    go(expr, &ind, &aux)
}

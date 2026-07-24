// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive type declaration elaboration.

use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Expr, ExprFolder, ExprVisitor, FVarId, InductiveDecl, InductiveType,
    Level, LevelVec,
};
use clean_parser::{DeclModifiers, SurfaceBinder, SurfaceCtor, SurfaceExpr};

use super::{convert_binder_info, ElabCtx, ElabResult};

type AutoImplicitBinder = (String, FVarId, Expr);
type RawCtor = (Name, Expr, Vec<AutoImplicitBinder>);

struct LevelParamCollector<'a> {
    params: &'a mut Vec<Name>,
}

impl ExprVisitor for LevelParamCollector<'_> {
    type Result = ();

    fn combine(&self, _: Self::Result, _: Self::Result) -> Self::Result {}

    fn visit_sort(&mut self, level: &Level) -> Self::Result {
        level.collect_params(self.params);
    }

    fn visit_const(&mut self, _name: &Name, levels: &LevelVec) -> Self::Result {
        for level in levels {
            level.collect_params(self.params);
        }
    }
}

fn collect_expr_level_params(expr: &Expr, params: &mut Vec<Name>) {
    if !expr.has_level_param_quick() {
        return;
    }
    let mut collector = LevelParamCollector { params };
    collector.visit_expr(expr);
}

struct MetaFVarCollector<'a> {
    metas: &'a mut Vec<crate::unify::MetaId>,
}

impl ExprVisitor for MetaFVarCollector<'_> {
    type Result = ();

    fn combine(&self, _: Self::Result, _: Self::Result) -> Self::Result {}

    fn visit_fvar(&mut self, id: FVarId) -> Self::Result {
        if let Some(meta_id) = crate::unify::MetaState::from_fvar(id) {
            if !self.metas.contains(&meta_id) {
                self.metas.push(meta_id);
            }
        }
    }
}

fn collect_expr_meta_fvars(expr: &Expr, metas: &mut Vec<crate::unify::MetaId>) {
    if !expr.has_fvar_quick() {
        return;
    }
    let mut collector = MetaFVarCollector { metas };
    collector.visit_expr(expr);
}

fn replace_fvar(expr: Expr, from: FVarId, to: FVarId) -> Expr {
    struct ReplaceFVarFolder {
        from: FVarId,
        to: FVarId,
    }

    impl ExprFolder for ReplaceFVarFolder {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.from {
                Expr::fvar(self.to)
            } else {
                Expr::fvar(id)
            }
        }
    }

    let mut folder = ReplaceFVarFolder { from, to };
    folder.fold_expr(&expr)
}

/// Insert additional applied arguments into self-references of an inductive type.
///
/// After meta-promotion, the inductive type gains new parameters (the promoted metas)
/// that weren't present when `replace_fvar_with_const` created the self-references.
/// This function finds `Const(ind_name, levels)` heads in application spines and
/// inserts the `extra_args` between the Const and the existing arguments.
///
/// Example: `Const("T", [u]) x y z` → `Const("T", [u]) α x y z` when extra_args = [α].
fn insert_self_ref_args(expr: Expr, ind_name: &Name, extra_args: &[Expr]) -> Expr {
    struct SelfRefArgInserter<'a> {
        ind_name: &'a Name,
        extra_args: &'a [Expr],
    }

    impl ExprFolder for SelfRefArgInserter<'_> {
        fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
            // Check if the function head (innermost Const in app spine) is the
            // inductive self-reference. If so, insert extra args after the Const
            // and before the existing arguments.
            let head = f.get_app_fn();
            if let clean_kernel::ExprKind::Const(name, _) = head.kind() {
                if name == self.ind_name {
                    // Collect existing args from the application spine
                    let mut args: Vec<Expr> = f
                        .get_app_args()
                        .into_iter()
                        .map(|e| self.fold_expr(e))
                        .collect();
                    args.push(self.fold_expr(a));

                    // Build: head extra_arg0 extra_arg1 ... arg0 arg1 ...
                    let mut result = head.clone();
                    for extra in self.extra_args {
                        result = Expr::app(result, extra.clone());
                    }
                    for arg in args {
                        result = Expr::app(result, arg);
                    }
                    return result;
                }
            }

            // Default: recurse into f and a
            Expr::app(self.fold_expr(f), self.fold_expr(a))
        }
    }

    let mut folder = SelfRefArgInserter {
        ind_name,
        extra_args,
    };
    folder.fold_expr(&expr)
}

/// Walk an expression and assign unsolved header-position metas in
/// self-references to their corresponding header FVars (#2680).
///
/// When ind_fvar is wrapped with header auto-implicits, elab_app creates
/// fresh metas at each self-reference. Some get solved by unification
/// (e.g., `Cover x y z` constrains α via `x : List α`), but others may
/// remain unsolved (e.g., `Cover [] [] []` — nil doesn't constrain α).
/// This assigns the unsolved ones to the header FVars so all constructors
/// use a consistent set of header values.
fn assign_header_metas(
    expr: &Expr,
    metas: &mut crate::unify::MetaState,
    ind_fvar: FVarId,
    header_fvars: &[FVarId],
) {
    crate::stack_safe(|| match expr.kind() {
        clean_kernel::ExprKind::App(_, _) => {
            let head = expr.get_app_fn();
            if matches!(head.kind(), clean_kernel::ExprKind::FVar(id) if *id == ind_fvar) {
                let args = expr.get_app_args();
                for (i, arg) in args.iter().enumerate() {
                    if i >= header_fvars.len() {
                        break;
                    }
                    if let clean_kernel::ExprKind::FVar(fvar_id) = arg.kind() {
                        if let Some(meta_id) = crate::unify::MetaState::from_fvar(*fvar_id) {
                            if !metas.is_assigned(meta_id) {
                                metas.assign(meta_id, Expr::fvar(header_fvars[i]));
                            }
                        }
                    }
                }
            }
            // Recurse into sub-expressions (covers nested self-refs in Pi domains).
            let args = expr.get_app_args();
            for arg in &args {
                assign_header_metas(arg, metas, ind_fvar, header_fvars);
            }
            assign_header_metas(head, metas, ind_fvar, header_fvars);
        }
        clean_kernel::ExprKind::Pi(_, domain, body)
        | clean_kernel::ExprKind::Lam(_, domain, body) => {
            assign_header_metas(domain, metas, ind_fvar, header_fvars);
            assign_header_metas(body, metas, ind_fvar, header_fvars);
        }
        _ => {}
    })
}

impl<'a> ElabCtx<'a> {
    /// Elaborate an inductive type declaration
    ///
    /// An inductive type has:
    /// - A name (e.g., `List`)
    /// - Universe parameters (e.g., `u`)
    /// - Parameters (e.g., `α : Type u`)
    /// - A result type (e.g., `Type u`)
    /// - Constructors (e.g., `nil`, `cons`)
    ///
    /// Example:
    /// ```text
    /// inductive List (α : Type u) : Type u
    /// | nil : List α
    /// | cons : α → List α → List α
    /// ```
    pub(super) fn elab_inductive(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        ctors: &[SurfaceCtor],
        deriving: &[String],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        let ind_name = Name::from_string(name);

        // Collect fvars and elaborated types for parameters
        // We store the elaborated types to avoid re-elaborating them multiple times
        // (once for push_local, once for ind_ty, and once per constructor)
        let mut param_fvars = Vec::new();
        let mut param_tys = Vec::new();

        // Elaborate parameters and store both fvars and types
        for binder in binders {
            let binder_ty = if let Some(t) = &binder.ty {
                self.elaborate(t)?
            } else {
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());
            param_fvars.push(fvar);
            param_tys.push(binder_ty);
        }

        // Record the auto-implicit start before result type elaboration (#2680).
        // Auto-implicits created during result type elaboration (e.g., α in
        // `Cover : (x y z : List α) → Type u`) form the header packet.
        let header_auto_start = self.auto_implicit_count();

        // Elaborate the result type (e.g., Type, Type u, Prop)
        let result_ty = self.elaborate(ty)?;

        let mut result_sort = result_ty.clone();
        while let clean_kernel::ExprKind::Pi(_, _, body) = result_sort.kind() {
            result_sort = body.as_ref().clone();
        }
        if let clean_kernel::ExprKind::Sort(result_level) = result_sort.kind() {
            if !result_level.is_zero() {
                for (_name, _fvar, auto_ty) in &self.auto_implicits {
                    let auto_ty = self.metas.instantiate(auto_ty);
                    let auto_ty = self.metas.instantiate_levels(&auto_ty);
                    if matches!(auto_ty.kind(), clean_kernel::ExprKind::Sort(_)) {
                        let ctx = self.build_local_ctx();
                        let mut unifier =
                            crate::unify::Unifier::with_env(&mut self.metas, self.env, ctx);
                        let _ = unifier.unify(&auto_ty, &Expr::sort(result_level.clone()));
                    }
                }
            }
        }

        // Freeze the header auto-implicit packet (#2680). This identifies which
        // auto-implicits are header-level (from result type elaboration) vs
        // constructor-local, enabling the uniform-prefix num_params analysis.
        let header_auto_fvars: Vec<FVarId> = self.auto_implicits[header_auto_start..]
            .iter()
            .map(|(_, fvar, _)| *fvar)
            .collect();

        // Build the inductive type: (param1 : T1) → ... → (paramN : TN) → result_ty
        // Reuse the stored param_tys instead of re-elaborating
        let mut ind_ty = result_ty.clone();
        for i in (0..binders.len()).rev() {
            let binder = &binders[i];
            ind_ty = ind_ty.abstract_fvar(param_fvars[i]);
            let bi = convert_binder_info(binder.info);
            ind_ty = Expr::pi(bi, param_tys[i].clone(), ind_ty);
        }

        // Snapshot header auto-implicit packet (#2680). This is non-destructive:
        // the FVars remain in scope for constructor elaboration.
        let header_packet = self.snapshot_auto_implicits_since(header_auto_start);

        // Build wrapped ind_fvar type (#2680 design step 3): the temporary
        // inductive local carries the header auto-implicits as implicit Pi
        // binders so that elab_app inserts per-occurrence metavariables for
        // them during constructor elaboration. This eliminates the need for
        // post-hoc resolve_ind_self_ref_args.
        let ind_fvar_ty = Self::wrap_type_with_auto_implicits(ind_ty.clone(), &header_packet);
        // Push the local with the SHORT name (the part after the last dot),
        // so that constructor types can reference the inductive by its unqualified
        // name. Inside `namespace Foo`, the surface syntax `inductive Color where
        // | red : Color` uses the unqualified name `Color`, not `Foo.Color`.
        let local_name = name.rsplit('.').next().unwrap_or(name).to_string();
        let ind_fvar = self.push_local(local_name, ind_fvar_ty);

        // Phase 1: Elaborate all constructor types.
        // This may auto-bind universe params (e.g., from `Type u` in constructor args),
        // so we must collect all raw types BEFORE doing replace_fvar_with_const.
        // Fix for #2001: replace_fvar_with_const reads self.universe_params at call time;
        // calling it per-constructor inside the elaboration loop means early constructors
        // get fewer universe levels than later ones (or than the final declared count).
        let mut raw_ctors: Vec<RawCtor> = Vec::new();
        for ctor in ctors {
            let ctor_name = Name::from_string(&format!("{}.{}", name, ctor.name));
            let ctor_auto_implicit_start = self.auto_implicit_count();
            let ctor_ty_raw = self.elaborate(&ctor.ty)?;
            // Assign unsolved header-position metas to header FVars (#2680).
            // e.g., in `done : Cover [] [] []`, the α meta stays unsolved
            // because nil doesn't constrain it. This ensures all constructors
            // use the same header FVars for consistent num_params.
            assign_header_metas(&ctor_ty_raw, &mut self.metas, ind_fvar, &header_auto_fvars);
            let ctor_auto_implicits = self.take_auto_implicits_since(ctor_auto_implicit_start);
            raw_ctors.push((ctor_name, ctor_ty_raw, ctor_auto_implicits));
        }

        let mut decl_level_params = Vec::new();
        let ind_ty_levels = self.metas.instantiate_levels(&ind_ty);
        collect_expr_level_params(&ind_ty_levels, &mut decl_level_params);
        for (_ctor_name, ctor_ty_raw, ctor_auto_implicits) in &raw_ctors {
            let ctor_ty_levels = self.metas.instantiate_levels(ctor_ty_raw);
            collect_expr_level_params(&ctor_ty_levels, &mut decl_level_params);
            for (_name, _fvar, implicit_ty) in ctor_auto_implicits {
                let implicit_ty_levels = self.metas.instantiate_levels(implicit_ty);
                collect_expr_level_params(&implicit_ty_levels, &mut decl_level_params);
            }
        }

        // Phase 2: Now self.universe_params is complete (all auto-bound params collected).
        // Replace inductive FVar with Const. The wrapped ind_fvar means elab_app
        // already inserted per-occurrence header args as metas (#2680 step 6):
        // just swap the FVar head to Const, do NOT prepend header args again.

        // Collect shared metas from ind_ty — only these get promoted to inductive params.
        let ind_ty_inst = self.metas.instantiate(&ind_ty);
        let mut shared_meta_ids: Vec<crate::unify::MetaId> = Vec::new();
        collect_expr_meta_fvars(&ind_ty_inst, &mut shared_meta_ids);

        let mut constructors = Vec::new();
        let mut ctor_return_arg_sets: Vec<Vec<Expr>> = Vec::new();
        for (ctor_name, ctor_ty_raw, ctor_auto_implicits) in raw_ctors {
            // Instantiate solved metas so elab_app-inserted metas that were
            // resolved during unification become concrete values.
            let mut ctor_ty_raw = self.metas.instantiate(&ctor_ty_raw);

            // Instantiate auto-implicit types too.
            let mut ctor_auto_implicits: Vec<AutoImplicitBinder> = ctor_auto_implicits
                .into_iter()
                .map(|(n, fv, ty)| (n, fv, self.metas.instantiate(&ty)))
                .collect();

            // Collect unsolved metas remaining in this constructor.
            let mut ctor_meta_ids: Vec<crate::unify::MetaId> = Vec::new();
            collect_expr_meta_fvars(&ctor_ty_raw, &mut ctor_meta_ids);
            for (_, _, impl_ty) in &ctor_auto_implicits {
                collect_expr_meta_fvars(impl_ty, &mut ctor_meta_ids);
            }

            // Separate ctor-local metas (not shared with ind_ty).
            // These represent per-constructor implicit args from elab_app
            // (e.g. the x,y,z,t metas in Linear's `left` constructor).
            let ctor_local_meta_ids: Vec<crate::unify::MetaId> = ctor_meta_ids
                .into_iter()
                .filter(|id| !shared_meta_ids.contains(id))
                .collect();

            // Convert ctor-local metas to fresh FVars and collect as extra
            // implicit binders, matching Lean 4's extraCtorParams.
            let mut extra_ctor_binders: Vec<AutoImplicitBinder> = Vec::new();
            for meta_id in &ctor_local_meta_ids {
                let meta_fvar = crate::unify::MetaState::to_fvar(*meta_id);
                let Some(meta) = self.metas.get(*meta_id) else {
                    continue;
                };
                let mut meta_ty = self.metas.instantiate(&meta.ty);
                let fresh = self.fresh_fvar();
                ctor_ty_raw = replace_fvar(ctor_ty_raw, meta_fvar, fresh);
                for (_, _, ty) in &mut ctor_auto_implicits {
                    *ty = replace_fvar(ty.clone(), meta_fvar, fresh);
                }
                for (_, _, ty) in &mut extra_ctor_binders {
                    *ty = replace_fvar(ty.clone(), meta_fvar, fresh);
                }
                meta_ty = replace_fvar(meta_ty, meta_fvar, fresh);
                extra_ctor_binders.push((format!("_ctor_{}", meta_id.0), fresh, meta_ty));
            }

            // Replace ind_fvar with Const — no extra applied args (#2680 step 6).
            let ctor_ty_raw = self.replace_fvar_with_const(
                ctor_ty_raw,
                ind_fvar,
                &ind_name,
                &decl_level_params,
                &[],
            );

            // Collect return type args for num_params analysis (before wrapping).
            {
                let mut ret = &ctor_ty_raw;
                while let clean_kernel::ExprKind::Pi(_, _, body) = ret.kind() {
                    ret = body;
                }
                let return_args: Vec<Expr> =
                    ret.get_app_args().iter().map(|e| (*e).clone()).collect();
                ctor_return_arg_sets.push(return_args);
            }

            // Combine extra ctor binders (promoted ctor-local metas) with
            // the auto-implicit binders. Extra binders come first since their
            // types may be referenced by auto-implicits (e.g. c : Cover α x y z
            // depends on the x,y,z ctor-local metas).
            let mut all_ctor_implicits = extra_ctor_binders;
            all_ctor_implicits.extend(ctor_auto_implicits);

            let mut ctor_ty = Self::wrap_type_with_auto_implicits(ctor_ty_raw, &all_ctor_implicits);

            // Abstract constructor type over parameters from the inside out so
            // nested constructor-local binders keep the right de Bruijn indices.
            // Lean 4 also treats inductive parameters as implicit in constructors.
            for (param_fvar, param_ty) in param_fvars.iter().zip(param_tys.iter()).rev() {
                ctor_ty = ctor_ty.abstract_fvar(*param_fvar);
                ctor_ty = Expr::pi(BinderInfo::Implicit, param_ty.clone(), ctor_ty);
            }

            constructors.push((ctor_name, ctor_ty));
        }

        // Pop inductive fvar
        self.pop_local();

        // Pop param fvars
        for _ in 0..binders.len() {
            self.pop_local();
        }

        let mut ind_auto_implicits = self.take_auto_implicits();
        let mut promoted_meta_implicits = Vec::new();
        // Only promote metas found in ind_ty and auto-implicit types (#2680).
        // Ctor-local metas were already converted to fresh FVars per-constructor
        // in Phase 2 above, so they won't appear here.
        //
        // Instantiate ind_ty first so assigned metas are resolved through their
        // assignment chains. Without this, an assigned meta (e.g., MetaId(0)
        // assigned to MetaId(7)) and its target both get promoted as separate
        // parameters, causing a kernel type mismatch.
        ind_ty = self.metas.instantiate(&ind_ty);
        // Also instantiate constructors so assigned metas are resolved
        // consistently with ind_ty.
        constructors = constructors
            .into_iter()
            .map(|(name, ty)| (name, self.metas.instantiate(&ty)))
            .collect();
        let mut promoted_meta_ids = Vec::new();
        collect_expr_meta_fvars(&ind_ty, &mut promoted_meta_ids);
        for (_name, _fvar, implicit_ty) in &ind_auto_implicits {
            collect_expr_meta_fvars(implicit_ty, &mut promoted_meta_ids);
        }
        for meta_id in promoted_meta_ids {
            // Skip assigned metas — their values already reference the final
            // unassigned meta, which will be promoted separately.
            if self.metas.is_assigned(meta_id) {
                continue;
            }
            let Some(meta_ty) = self.metas.get(meta_id).map(|meta| meta.ty.clone()) else {
                continue;
            };
            let promoted_fvar = self.fresh_fvar();
            let promoted_ty = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&meta_ty));
            let promoted_meta_fvar = crate::unify::MetaState::to_fvar(meta_id);
            ind_ty = replace_fvar(ind_ty, promoted_meta_fvar, promoted_fvar);
            constructors = constructors
                .into_iter()
                .map(|(name, ty)| (name, replace_fvar(ty, promoted_meta_fvar, promoted_fvar)))
                .collect();
            ind_auto_implicits = ind_auto_implicits
                .into_iter()
                .map(|(name, fvar, ty)| {
                    (
                        name,
                        fvar,
                        replace_fvar(ty, promoted_meta_fvar, promoted_fvar),
                    )
                })
                .collect();
            promoted_meta_implicits.push((
                format!("__auto_meta_{}", meta_id.0),
                promoted_fvar,
                promoted_ty,
            ));
        }
        let promoted_count = promoted_meta_implicits.len();
        if !promoted_meta_implicits.is_empty() {
            // The promoted metas become additional parameters of the inductive type,
            // prepended before the existing auto-implicits. Self-references in
            // constructor types (Const(ind_name, levels) applied_args...) were created
            // by replace_fvar_with_const BEFORE promotion, so they lack the promoted
            // FVars. Insert them now: for each Const(ind_name), wrap it with App
            // nodes for the promoted FVars so self-refs carry all parameters.
            let promoted_fvars: Vec<Expr> = promoted_meta_implicits
                .iter()
                .map(|(_name, fvar, _ty)| Expr::fvar(*fvar))
                .collect();
            if !promoted_fvars.is_empty() {
                constructors = constructors
                    .into_iter()
                    .map(|(name, ty)| {
                        let ty = insert_self_ref_args(ty, &ind_name, &promoted_fvars);
                        (name, ty)
                    })
                    .collect();
            }
            promoted_meta_implicits.extend(ind_auto_implicits);
            ind_auto_implicits = promoted_meta_implicits;
        }
        let ind_ty = Self::wrap_type_with_auto_implicits(ind_ty, &ind_auto_implicits);

        // Note: Recursors (rec, casesOn) are generated by the kernel during add_inductive.
        // They can be queried after registration via env.get_recursor("Type.rec").

        // Determine which auto-implicits are true parameters vs indices (#796).
        // An auto-implicit at position i is a parameter if, in ALL constructors'
        // return types, the arg at that position is the auto-implicit FVar itself.
        // Only a contiguous prefix qualifies (kernel requires contiguous params).
        // Promoted metas are always uniform parameters.
        let mut uniform_original_prefix = 0;
        'prefix: for (i, fvar) in header_auto_fvars.iter().enumerate() {
            for return_args in &ctor_return_arg_sets {
                if i >= return_args.len() {
                    break 'prefix;
                }
                if !matches!(
                    return_args[i].kind(),
                    clean_kernel::ExprKind::FVar(id) if *id == *fvar
                ) {
                    break 'prefix;
                }
            }
            uniform_original_prefix += 1;
        }
        let num_params = u32::try_from(binders.len() + promoted_count + uniform_original_prefix)
            .unwrap_or(u32::MAX);

        // Substitute level constraints collected during unification
        let ind_ty = self.metas.instantiate_levels(&ind_ty);
        let constructors: Vec<_> = constructors
            .into_iter()
            .map(|(name, ty)| {
                let ty = Self::wrap_type_with_auto_implicits(ty, &ind_auto_implicits);
                (name, self.metas.instantiate_levels(&ty))
            })
            .collect();

        // Derive against an isolated environment containing the exact completed
        // parent declaration.  Built-in recursive/nested generators can then use
        // the kernel's authoritative recursor and constructor metadata without
        // publishing the parent early or returning a placeholder value.  The
        // real environment remains untouched until the outer registration
        // transaction commits the complete result.
        let derived_instances = if deriving.is_empty() {
            Vec::new()
        } else {
            let mut registered_candidate = self.env.clone();
            let candidate_decl = InductiveDecl {
                level_params: decl_level_params.clone(),
                num_params,
                types: vec![InductiveType {
                    name: ind_name.clone(),
                    type_: ind_ty.clone(),
                    constructors: constructors
                        .iter()
                        .map(|(name, type_)| Constructor {
                            name: name.clone(),
                            type_: type_.clone(),
                        })
                        .collect(),
                }],
            };
            registered_candidate
                .add_inductive(candidate_decl)
                .map_err(|error| ElabError::KernelRegistrationFailed {
                    operation: format!(
                        "prepare candidate environment for deriving on `{ind_name}`"
                    ),
                    detail: error.to_string(),
                })?;

            // Derive handlers may allocate internal universe parameters.  The
            // parent declaration's parameter set is already complete, so restore
            // this mutable elaborator state on both success and failure.
            let ind_universe_params_len = self.universe_params.len();
            let result = self.generate_derived_instances_inductive(
                &registered_candidate,
                &ind_name,
                universe_params,
                binders,
                ctors,
                &ind_ty,
                deriving,
            );
            self.universe_params.truncate(ind_universe_params_len);
            result?
        };

        // Use self.universe_params which includes any auto-bound params added
        // during elaboration (e.g., `inductive Eq (A : Type u)` auto-binds `u`)
        // Fix for #821: previously used the explicit `universe_params` parameter
        // which is empty when universe params are auto-bound from type annotations
        Ok(ElabResult::Inductive {
            name: ind_name,
            universe_params: decl_level_params,
            num_params,
            ty: ind_ty,
            constructors,
            derived_instances,
            modifiers: *modifiers,
        })
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure and class declaration elaboration.
//!
//! Extracted from elaborate_decl.rs to reduce file size (Part of #307).

use crate::instances::{extract_class_app, DEFAULT_PRIORITY};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprFolder, ExprVisitor, Level, LevelVec};
use clean_parser::{DeclModifiers, Span, SurfaceBinder, SurfaceExpr, SurfaceField};

use super::{
    convert_binder_info, is_out_param_type, is_semi_out_param_type, ClassRegistration,
    DerivedInstance, ElabCtx, ElabResult,
};

/// Collect all Level::Param names that appear in an expression's Sort and Const nodes.
/// Used to determine which universe parameters are actually referenced after level
/// instantiation resolves concrete assignments (#3390).
struct StructLevelParamCollector<'a> {
    params: &'a mut Vec<Name>,
}

impl ExprVisitor for StructLevelParamCollector<'_> {
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

fn collect_struct_level_params(expr: &Expr, params: &mut Vec<Name>) {
    if !expr.has_level_param_quick() {
        return;
    }
    let mut collector = StructLevelParamCollector { params };
    collector.visit_expr(expr);
}

/// Extract the universe levels on the head constant of an applied type, e.g.
/// `App(App(Const(Inh, [u]), α), …)` ⇒ `[u]`. Used to reference a parameterized
/// parent's projections at the same levels the child applied to the parent
/// (`@Parent.f.{levels}`). Returns empty if the head is not a `Const`.
fn head_const_levels(ty: &Expr) -> Vec<Level> {
    let mut current = ty;
    while let clean_kernel::ExprKind::App(func, _) = current.kind() {
        current = func.as_ref();
    }
    if let clean_kernel::ExprKind::Const(_, levels) = current.kind() {
        levels.iter().cloned().collect()
    } else {
        Vec::new()
    }
}

/// Whether a structure-like declaration is a plain `structure` or a `class`.
///
/// Controls the binder infos of the generated projection functions, mirroring
/// Lean 4's `mkProjections` (invoked with `isClass` from
/// `src/Lean/Elab/Structure.lean`; implementation in
/// `src/library/constructions/projection.cpp`): for a CLASS, every structure
/// parameter becomes an implicit binder and the major premise `self` is
/// instance-implicit, so `C.f x` inserts `{α}` as a metavariable and `[self]`
/// via instance synthesis. Verified against Lean 4 v4.30.0-rc2:
/// `@MyMag.op : {α : Type} → [self : MyMag α] → α → α → α`, and an
/// instance-implicit class param `[BEq α]` also becomes implicit
/// (`@WithInst.w : {α : Type} → {inst : BEq α} → [self : WithInst α] → α → Nat`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::infer) enum StructureKind {
    /// A plain `structure`: projections keep the declared parameter binder
    /// infos and an explicit `self` (current Clean behavior; Lean additionally
    /// makes structure params implicit in projections — tracked as a separate
    /// fidelity gap. The CONSTRUCTOR's params are implicit, matching Lean —
    /// see the ctor abstraction pass).
    Structure,
    /// A `class`: projections take implicit params and inst-implicit `self`.
    Class,
}

/// A structure field to elaborate: either inherited from an `extends` parent
/// (type already elaborated to a closed kernel `Expr`) or declared locally
/// (type still a surface expression to elaborate). Both variants are processed
/// uniformly when building the constructor and projections so that inherited
/// fields are flattened into the derived structure.
enum FieldSpec<'a> {
    /// Field flattened from a parent structure. `ty` is the parent field's
    /// elaborated kernel type; `default` is any registered parent default.
    Inherited {
        name: String,
        ty: Expr,
        default: Option<Expr>,
    },
    /// Field declared directly on the structure.
    Own(&'a SurfaceField),
}

impl FieldSpec<'_> {
    fn name(&self) -> &str {
        match self {
            FieldSpec::Inherited { name, .. } => name,
            FieldSpec::Own(field) => &field.name,
        }
    }
}

/// A parent structure embedded as a subobject via `extends`, mirroring Lean's
/// subobject layout (`src/Lean/Elab/Structure.lean` `withParents`): the parent
/// becomes a single constructor field `toParent : Parent` (NOT flattened), and
/// every field accessible on `Parent` is re-exposed on the child as a derived
/// projection composed through the `toParent` subobject.
struct ParentSubobject {
    /// The subobject field name, e.g. `toA` (Lean `mkToParentName`).
    to_field: Name,
    /// The parent structure's name, e.g. `A`.
    parent_name: Name,
    /// The elaborated parent type used as the subobject field's type. For a
    /// parameter-less parent this is `Const(A)`; for a parameterized parent
    /// (`extends Inh α`) it is the full applied type `Inh α` (referencing the
    /// child's own parameter fvars), stored verbatim as the subobject field's
    /// type — exactly Lean's subobject layout.
    parent_ty: Expr,
    /// The actual arguments the parent is applied to in `extends Parent args…`
    /// (`[α]` for `extends Inh α`), referencing the child's parameter fvars.
    /// Empty for a parameter-less parent. Used to instantiate the parent's
    /// projection telescopes so inherited field types/values specialize to the
    /// child's parameters (`@Parent.f parent_args (Child.toParent self)`).
    parent_args: Vec<Expr>,
    /// The universe levels on the parent head constant in `parent_ty`
    /// (`@Parent.{levels}`). The parent's projections share these level
    /// parameters, so an inherited-field reference is `@Parent.f.{levels} …`.
    /// Empty for a monomorphic parent.
    parent_levels: Vec<Level>,
    /// Every field projectable on the parent, as `(field_name, result_type)`.
    /// For a parameter-less parent this includes its own fields, its own
    /// subobjects, and (transitively) its inherited fields; for a parameterized
    /// parent it is the parent's DIRECT fields with their result types already
    /// specialized to the child's parameters (via `parent_args`). Used to
    /// synthesize the child's derived projections
    /// `Child.field := @Parent.field parent_args (Child.toParent self)` and to
    /// make inherited fields resolve as bare identifiers in later field types.
    flattened: Vec<(Name, Expr)>,
}

/// Rewrite every self-occurrence `Const(struct_name, …)` (and the struct's own
/// projection members `Struct.field`, `Struct.toParent`) to carry EXACTLY the
/// struct's surviving universe parameters (`keep_params`), in declaration order.
///
/// A structure's self-occurrence always applies the struct to its own universe
/// parameters, so the correct level list is precisely `keep_params` — the same
/// list the declaration is registered with. Replacing (rather than positionally
/// filtering the pre-`instantiate_levels` list) is what makes this robust to
/// universe pollution: when field elaboration mints a fresh universe param that
/// later collapses onto a declared one (e.g. a universe-polymorphic field/parent
/// constant `Inh.{u_0} α` whose `u_0` unifies with the struct's `u`), the
/// self-occurrence otherwise ends up with a DUPLICATED level slot (`Struct.{u,u}`)
/// while the declaration keeps a single param — a kernel-rejected mismatch. This
/// also subsumes the concrete-collapse case (#3390) where a minted param resolves
/// to a concrete level and must simply not appear in a self-occurrence.
struct FilterStructSelfLevels<'a> {
    struct_name: &'a Name,
    keep_params: &'a [Name],
}

impl FilterStructSelfLevels<'_> {
    /// Whether `name` is the structure itself or one of its projection members
    /// (`Struct.field`), which share the structure's universe parameters.
    fn is_self_or_member(&self, name: &Name) -> bool {
        if name == self.struct_name {
            return true;
        }
        // A projection member `Struct.field` renders as `<struct>.<field>`; the
        // dotted prefix is exactly the struct's rendered name.
        let member_prefix = format!("{}.", self.struct_name);
        name.to_string().starts_with(&member_prefix)
    }
}

impl ExprFolder for FilterStructSelfLevels<'_> {
    fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
        if self.is_self_or_member(name) {
            // A self-occurrence carries exactly the struct's surviving params,
            // in declaration order (replace, don't positionally filter — see the
            // type doc for why filtering leaves duplicate/stale slots).
            let replaced: Vec<Level> = self
                .keep_params
                .iter()
                .map(|p| Level::param(p.clone()))
                .collect();
            Expr::const_(name.clone(), replaced)
        } else {
            Expr::const_(name.clone(), levels.clone())
        }
    }
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a class declaration.
    ///
    /// Classes are elaborated as structures, then registered as type classes.
    /// Parent class fields from `extends` clauses are prepended to the field list,
    /// and `toParent` instances are generated for each parent.
    pub(super) fn elab_class(
        &mut self,
        name: &str,
        _universe_params: &[String],
        binders: &[SurfaceBinder],
        extends: &[Box<SurfaceExpr>],
        ty: Option<&SurfaceExpr>,
        fields: &[SurfaceField],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        // Build fields list: parent fields from extends prepended, then declared fields.
        let mut all_fields: Vec<SurfaceField> = Vec::new();

        for parent_expr in extends.iter() {
            let parent_name = match parent_expr.as_ref() {
                SurfaceExpr::App(_, f, _) => {
                    let mut current = f.as_ref();
                    while let SurfaceExpr::App(_, inner, _) = current {
                        current = inner.as_ref();
                    }
                    if let SurfaceExpr::Ident(_, n) = current {
                        n.clone()
                    } else {
                        "Parent".to_string()
                    }
                }
                SurfaceExpr::Ident(_, n) => n.clone(),
                _ => "Parent".to_string(),
            };

            let field_name = format!("to{parent_name}");
            all_fields.push(SurfaceField {
                span: Span::dummy(),
                name: field_name,
                ty: parent_expr.as_ref().clone(),
                default: None,
                is_default_override: false,
            });
        }

        all_fields.extend(fields.iter().cloned());

        // The class path prepends its own `toParent` fields into `all_fields`
        // and generates `toParent` instances below, so pass an empty `extends`
        // to `elab_structure` — it must not additionally flatten parent fields.
        let mut result = self.elab_structure(
            name,
            _universe_params,
            binders,
            &[],
            ty,
            None,
            &all_fields,
            &[],
            modifiers,
            StructureKind::Class,
        )?;

        let out_params: Vec<usize> = binders
            .iter()
            .enumerate()
            .filter_map(|(idx, b)| {
                if let Some(ty) = &b.ty {
                    if is_out_param_type(ty) {
                        return Some(idx);
                    }
                }
                None
            })
            .collect();

        let semi_out_params: Vec<usize> = binders
            .iter()
            .enumerate()
            .filter_map(|(idx, b)| {
                if let Some(ty) = &b.ty {
                    if is_semi_out_param_type(ty) {
                        return Some(idx);
                    }
                }
                None
            })
            .collect();

        let class_name = Name::from_string(name);

        self.instances.register_class_full(
            class_name.clone(),
            binders.len(),
            out_params.clone(),
            semi_out_params.clone(),
        );

        // Generate toParent instances for extends clause.
        // Re-push binders because elab_structure popped them.
        let mut param_fvars: Vec<(String, clean_kernel::FVarId, Expr)> = Vec::new();
        for binder in binders.iter() {
            let binder_ty = if let Some(t) = &binder.ty {
                self.elaborate(t)?
            } else {
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());
            param_fvars.push((binder.name.clone(), fvar, binder_ty));
        }

        // The structure's FINAL universe parameters, as `elab_structure` (already
        // run above) computed and registered them: the declared list filtered to
        // those actually used. This is the only correct level list for a
        // self-occurrence of the class inside its own derived parent instances.
        //
        // It cannot be reconstructed here. `mk_const` resolves through the
        // ENVIRONMENT, where the class is not registered yet, so it yields
        // `Const(C, [])` — zero level arguments — and the kernel rejects the
        // derived instance with "Level count mismatch for C: declared N level
        // params, got 0". Nor is `self.universe_params` right: it accumulates
        // fresh universe metas minted during field elaboration, giving "got 3"
        // where the declaration keeps one. Both were measured and reverted; see
        // `tests/fixtures/universes/p33_class_extends_upoly_MUST_FAIL.lean`.
        let struct_universe_params: Vec<Name> = match &result {
            ElabResult::Structure {
                universe_params, ..
            } => universe_params.clone(),
            _ => Vec::new(),
        };

        let mut parent_instances: Vec<DerivedInstance> = Vec::new();
        for parent_expr in extends.iter() {
            if let Ok(parent_ty) = self.elaborate(parent_expr) {
                if let Some((parent_class_name, _parent_args)) = extract_class_app(&parent_ty) {
                    let parent_suffix = parent_class_name
                        .last_component()
                        .unwrap_or_else(|| "Parent".to_string());
                    let instance_name = Name::append(&class_name, &format!("to{}", parent_suffix));

                    // Build instance type: {params} → [ChildClass params] → ParentClass params
                    let mut child_class_ty = self.mk_const(&class_name);
                    for (_, fvar, _) in param_fvars.iter() {
                        child_class_ty = Expr::app(child_class_ty, Expr::fvar(*fvar));
                    }

                    let mut inst_type =
                        Expr::pi(BinderInfo::InstImplicit, child_class_ty, parent_ty.clone());

                    // Abstract over fvars, building implicit Pi binders
                    let mut abstracted_binder_types = Vec::new();
                    for (i, (_name, fvar, fvar_ty)) in param_fvars.iter().enumerate() {
                        inst_type = inst_type.abstract_fvar(*fvar);
                        let mut binder_ty = fvar_ty.clone();
                        for (_, prev_fvar, _) in param_fvars.iter().take(i) {
                            binder_ty = binder_ty.abstract_fvar(*prev_fvar);
                        }
                        abstracted_binder_types.push(binder_ty.clone());
                        inst_type = Expr::pi(BinderInfo::Implicit, binder_ty, inst_type);
                    }

                    // Instance expr: λ {params} [inst] => Proj(class, parent_idx, inst)
                    let parent_idx = extends
                        .iter()
                        .position(|e| {
                            if let Ok(e_ty) = self.elaborate(e) {
                                if let Some((e_class, _)) = extract_class_app(&e_ty) {
                                    return e_class == parent_class_name;
                                }
                            }
                            false
                        })
                        .unwrap_or(0) as u32;

                    let mut instance_expr =
                        Expr::proj(class_name.clone(), parent_idx, Expr::bvar(0));

                    // Build abstracted child class type using BVars
                    let mut child_class_ty_abstracted = self.mk_const(&class_name);
                    for i in 0..param_fvars.len() {
                        child_class_ty_abstracted = Expr::app(
                            child_class_ty_abstracted,
                            Expr::bvar((param_fvars.len() - 1 - i) as u32),
                        );
                    }
                    instance_expr = Expr::lam(
                        BinderInfo::InstImplicit,
                        child_class_ty_abstracted,
                        instance_expr,
                    );

                    for binder_ty in abstracted_binder_types.iter().rev() {
                        instance_expr =
                            Expr::lam(BinderInfo::Implicit, binder_ty.clone(), instance_expr);
                    }

                    self.instances.add_instance(
                        instance_name.clone(),
                        parent_class_name.clone(),
                        instance_expr.clone(),
                        inst_type.clone(),
                        DEFAULT_PRIORITY,
                    );

                    // Rewrite every self-occurrence of the class (and its
                    // members, e.g. `C.toParent`) to carry EXACTLY the struct's
                    // surviving params — the same treatment `elab_structure`
                    // gives `ctor_ty` and `projections`, which the derived parent
                    // instances were never given. Doing it by folding the
                    // FINISHED expressions, rather than by constructing the
                    // levels up front, is what makes it robust to the
                    // universe pollution described above: the folder replaces
                    // the level list outright instead of positionally filtering
                    // a polluted one.
                    let mut folder = FilterStructSelfLevels {
                        struct_name: &class_name,
                        keep_params: &struct_universe_params,
                    };
                    let inst_type = folder.fold_expr(&inst_type);
                    let instance_expr = folder.fold_expr(&instance_expr);

                    // The instance is polymorphic in exactly the class's
                    // parameters. `collect_level_params` over the folded
                    // expressions would also miss any param that survives in the
                    // declaration but happens not to occur syntactically here.
                    let level_params = struct_universe_params.clone();
                    parent_instances.push(DerivedInstance {
                        name: instance_name,
                        class_name: parent_class_name,
                        ty: inst_type,
                        val: instance_expr,
                        priority: DEFAULT_PRIORITY,
                        level_params,
                    });
                }
            }
        }

        // B24 — class `extends` subobject metadata + derived parent-field
        // projections. `elab_class` embeds each parent as a `toParent` field (it
        // prepended them into `all_fields` above and passed empty `extends` to
        // `elab_structure`, so the structure path recorded NO parent metadata and
        // built NO inherited projections — unlike the B10 structure `extends`
        // path). We reconstruct both here, over the parameterized parents the
        // class path supports:
        //   - `parents` metadata `(toParent, Parent)` so the instance-`where`
        //     (struct-literal) path and anonymous-ctor flattening can assemble
        //     the parent subobject from the flattened inherited fields
        //     (`rewrite_parent_subobject_construction`,
        //     `flatten_anon_ctor_subobjects`).
        //   - derived projections `Child.f := @Parent.f <args> (@Child.toParent
        //     self)` so inherited-field access resolves through the chain and
        //     `inherited_field_parent_proj` recognizes `f` as reached via
        //     `toParent`.
        // The `to_field` name is read back from the just-built field table (the
        // first `extends.len()` entries are the prepended subobjects, in order),
        // so it matches the prepended field exactly.
        let (parent_meta, inherited_projs) = if extends.is_empty() {
            (Vec::new(), Vec::new())
        } else {
            let (class_ups, class_field_names): (Vec<Name>, Vec<Name>) = match &result {
                ElabResult::Structure {
                    universe_params,
                    field_names,
                    ..
                } => (universe_params.clone(), field_names.clone()),
                _ => (Vec::new(), Vec::new()),
            };
            self.build_class_parent_projections(
                &class_name,
                &class_ups,
                &param_fvars,
                extends,
                &class_field_names,
            )
        };

        // Pop the re-pushed class parameter locals (mirrors the push at the top
        // of the extends handling; keeps the local stack balanced).
        for _ in 0..param_fvars.len() {
            self.pop_local();
        }

        if let ElabResult::Structure {
            ref mut derived_instances,
            ref mut class_info,
            ref mut projections,
            ref mut parents,
            ..
        } = result
        {
            derived_instances.extend(parent_instances);
            projections.extend(inherited_projs);
            *parents = parent_meta;
            *class_info = Some(ClassRegistration {
                num_params: binders.len(),
                out_params,
                semi_out_params,
            });
        }

        Ok(result)
    }

    /// Build the `(toParent, Parent)` subobject metadata and the derived
    /// parent-field projections for a CLASS that `extends` one or more parent
    /// classes (B24). The structure `extends` path
    /// (`resolve_parent_subobjects` + `build_inherited_projections`) can't be
    /// reused directly because it fails closed on *parameterized* parents
    /// (`class B extends A α`), which is exactly the class-extends shape; the
    /// class path instead embeds each parent as a prepended `toParent` field
    /// (done in `elab_class`), so here we synthesize, per parent field `f`:
    ///
    ///   `Child.f : {params} → [self : Child params] → T_f`
    ///        `:= fun {params} [self] => @Parent.f <parent_args> (@Child.toParent params self)`
    ///
    /// with class binder infos (params implicit, `self` inst-implicit — matching
    /// the direct class projections `elab_structure` builds). `T_f` is obtained
    /// by instantiating `Parent.f`'s own type telescope with `<parent_args>` then
    /// the `toParent` value, so a parameterized parent's field type is
    /// specialized to the child's parameters.
    ///
    /// Scope of what is built (everything else descopes LOUD — no projection is
    /// emitted, so the inherited field is a loud unknown/missing field at the
    /// use site, never a silent-wrong or mis-typed one):
    /// - **Universe-monomorphic only.** If the class OR a parent field constant
    ///   carries universe parameters, no derived projection is emitted for it
    ///   (a mis-leveled projection would be a kernel-reject at registration).
    /// - **Direct parent fields only.** `Parent`'s own field table drives this;
    ///   a grandparent field (multi-level `extends`) has no entry there, so it
    ///   is not re-exposed on the child — multi-level access descopes LOUD.
    /// - **First-claim wins** on a name shared by an own field or an earlier
    ///   parent (no duplicate projection; the shadowing field keeps the name).
    ///
    /// Every emitted projection is a closed term re-checked by the kernel at
    /// registration, so an incorrectly-shaped one fails the whole declaration
    /// loudly rather than passing silently.
    fn build_class_parent_projections(
        &mut self,
        class_name: &Name,
        class_universe_params: &[Name],
        param_fvars: &[(String, clean_kernel::FVarId, Expr)],
        extends: &[Box<SurfaceExpr>],
        class_field_names: &[Name],
    ) -> (Vec<(Name, Name)>, Vec<(Name, Expr, Expr)>) {
        use std::collections::HashSet;

        let struct_levels: Vec<Level> = class_universe_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();

        let mut parent_meta: Vec<(Name, Name)> = Vec::new();
        let mut projs: Vec<(Name, Expr, Expr)> = Vec::new();
        // Names already claimed by a direct constructor field (incl. every
        // `toParent`) or by an earlier parent's re-exposed field.
        let mut already: HashSet<Name> = class_field_names.iter().cloned().collect();

        for (i, parent_expr) in extends.iter().enumerate() {
            // The prepended subobject field for parent `i` is the i-th field of
            // the just-built table (parents precede declared fields, in order),
            // so its name matches the embedded `toParent` field exactly.
            let Some(to_field) = class_field_names.get(i) else {
                continue;
            };
            let Ok(parent_ty) = self.elaborate(parent_expr) else {
                continue;
            };
            let Some((parent_class_name, parent_args)) = extract_class_app(&parent_ty) else {
                continue;
            };
            parent_meta.push((to_field.clone(), parent_class_name.clone()));

            // Universe-monomorphic gate (see doc): polymorphic classes descope.
            if !class_universe_params.is_empty() {
                continue;
            }
            // The extends application must be saturated (`parent_args.len()` ==
            // parent's parameter count) for the telescope instantiation to line
            // up; otherwise skip (the declaration itself is malformed and will
            // be caught elsewhere — do not emit a wrong projection).
            let parent_num_params = self
                .env
                .get_inductive(&parent_class_name)
                .map(|ind| ind.num_params as usize)
                .unwrap_or(0);
            if parent_args.len() != parent_num_params {
                continue;
            }
            // Full projectable set (declared + inherited grandparent fields via
            // subobject links), so a class re-exposes fields from a PARAMETERIZED
            // grandparent through the chain (Mathlib's `Monoid extends Semigroup
            // extends Mul`). Each inherited field `f` has an existing projection
            // `parent.f` re-exposed when the parent class was declared, with the
            // same telescope shape as a direct field; propagates transitively.
            let parent_fields = self.all_projectable_field_names(&parent_class_name);
            if parent_fields.is_empty() {
                continue;
            }
            let to_field_const = Name::from_string(&format!("{class_name}.{to_field}"));

            for pf in &parent_fields {
                if already.contains(pf) {
                    continue;
                }
                let parent_field_const = Name::from_string(&format!("{parent_class_name}.{pf}"));
                let Some(pf_info) = self.env.get_const(&parent_field_const) else {
                    continue;
                };
                // A universe-polymorphic parent projection can't be referenced
                // with the class's (empty) level set — descope LOUD.
                if !pf_info.level_params.is_empty() {
                    continue;
                }
                let pf_type = pf_info.type_.clone();

                // self : Child <params>
                let mut self_ty = Expr::const_(class_name.clone(), struct_levels.clone());
                for (_, fv, _) in param_fvars {
                    self_ty = Expr::app(self_ty, Expr::fvar(*fv));
                }
                let self_fvar = self.push_local("self".to_string(), self_ty.clone());

                // to_parent = @Child.toParent <params> self
                let mut to_parent = Expr::const_(to_field_const.clone(), struct_levels.clone());
                for (_, fv, _) in param_fvars {
                    to_parent = Expr::app(to_parent, Expr::fvar(*fv));
                }
                to_parent = Expr::app(to_parent, Expr::fvar(self_fvar));

                // body = @Parent.pf <parent_args> to_parent; and the field's
                // result type is `pf_type` instantiated over the same arguments.
                let mut body = Expr::const_(parent_field_const.clone(), Vec::new());
                let mut telescope_ty = pf_type;
                let mut telescope_ok = true;
                for arg in parent_args.iter().chain(std::iter::once(&to_parent)) {
                    match telescope_ty.kind() {
                        clean_kernel::ExprKind::Pi(_, _, tbody) => {
                            telescope_ty = tbody.instantiate(arg)
                        }
                        _ => {
                            telescope_ok = false;
                            break;
                        }
                    }
                    body = Expr::app(body, arg.clone());
                }
                if !telescope_ok {
                    self.pop_local(); // self
                    continue;
                }
                let result_ty = telescope_ty;

                // Abstract over `self` (inst-implicit), then the class params
                // (implicit — class projection binder infos, matching the direct
                // projections `elab_structure` emits).
                let proj_val_inner = body.abstract_fvar(self_fvar);
                let proj_ty_inner = result_ty.abstract_fvar(self_fvar);
                self.pop_local(); // self

                let mut proj_val =
                    Expr::lam(BinderInfo::InstImplicit, self_ty.clone(), proj_val_inner);
                let mut proj_ty =
                    Expr::pi(BinderInfo::InstImplicit, self_ty.clone(), proj_ty_inner);
                for k in (0..param_fvars.len()).rev() {
                    let (_, fv, fv_ty) = &param_fvars[k];
                    proj_val = proj_val.abstract_fvar(*fv);
                    proj_ty = proj_ty.abstract_fvar(*fv);
                    // A later param's type may reference earlier params.
                    let mut binder_ty = fv_ty.clone();
                    for (_, prev_fv, _) in param_fvars.iter().take(k) {
                        binder_ty = binder_ty.abstract_fvar(*prev_fv);
                    }
                    proj_val = Expr::lam(BinderInfo::Implicit, binder_ty.clone(), proj_val);
                    proj_ty = Expr::pi(BinderInfo::Implicit, binder_ty, proj_ty);
                }

                // Fail closed: only emit fully-closed projections.
                if proj_val.has_fvar_quick() || proj_ty.has_fvar_quick() {
                    continue;
                }
                already.insert(pf.clone());
                let proj_name = Name::from_string(&format!("{class_name}.{pf}"));
                projs.push((proj_name, proj_ty, proj_val));
            }
        }

        (parent_meta, projs)
    }

    /// Resolve the parent subobjects a structure embeds via its `extends`
    /// parents, mirroring Lean's subobject layout
    /// (`src/Lean/Elab/Structure.lean` `withParents`/`mkToParentName`, lines
    /// ~785-866): each parent is embedded as ONE constructor field
    /// `toParent : Parent` (NOT flattened), and every field projectable on the
    /// parent is recorded so the child can re-expose it as a derived projection
    /// composed through `toParent`.
    ///
    /// Each parent type expression is elaborated (so namespace/qualification is
    /// handled exactly as any other type reference) and its head constant taken
    /// as the parent structure name. Returns one [`ParentSubobject`] per parent.
    ///
    /// Supported parent shapes (everything else fails closed LOUD):
    /// - **Parameter-less parent** (`extends Base`): the common case; the
    ///   subobject field type is `Const(Base)`.
    /// - **Parameterized parent** (`extends Inh α`): the subobject field type is
    ///   the applied `Inh α` and every DIRECT parent field is re-exposed with
    ///   its result type specialized to the child's parameters (via
    ///   `parent_args`). This handles the Mathlib base shape
    ///   `Unique (α : Sort u) extends Inhabited α`. Must be **saturated** —
    ///   the number of arguments equals the parent's parameter count.
    ///
    /// Deferred sophistication (reported LOUD, never silently wrong):
    /// - **Under/over-applied parameterized parent** (arg count ≠ parent param
    ///   count): rejected with `NotImplemented` — the telescope instantiation
    ///   would not line up. (Elaboration of `extends` itself usually catches a
    ///   malformed application first.)
    /// - **Transitive parameterized grandparent fields** (a parameterized parent
    ///   that itself `extends` another): only the parent's DIRECT fields are
    ///   re-exposed; a grandparent field has no derived projection (LOUD unknown
    ///   at the use site) — parity with the class-extends path.
    /// - **Dependent inherited fields** (the parent field's result type still
    ///   mentions the subobject value): skipped per-field (no derived
    ///   projection) rather than mis-typed.
    /// - **Diamond copy semantics** (Lean `withStruct` case (C),
    ///   Elab/Structure:811-832): when two parents expose the same field name,
    ///   Lean copies the field instead of nesting a second subobject. Here the
    ///   first parent to expose a name wins for the derived projection (a value-
    ///   preserving approximation for genuine diamonds; the ctor still embeds
    ///   both subobjects). Full copy/reuse is not yet modelled.
    ///
    /// Called AFTER the structure's binders are pushed, so a parameterized
    /// parent's argument (`α` in `extends Inh α`) resolves to the structure's
    /// own parameter fvar (not a throwaway auto-bound implicit).
    fn resolve_parent_subobjects(
        &mut self,
        extends: &[Box<SurfaceExpr>],
    ) -> Result<Vec<ParentSubobject>, ElabError> {
        let mut resolved: Vec<ParentSubobject> = Vec::new();

        for parent_expr in extends {
            let parent_ty = self.elaborate(parent_expr)?;
            // Resolve metavariables/level-metavariables introduced when the
            // parent head was applied to the child's arguments, so the stored
            // subobject type and the extracted args/levels are concrete.
            let parent_ty = self.metas.instantiate(&parent_ty);
            let parent_ty = self.metas.instantiate_levels(&parent_ty);
            let Some((parent_name, parent_args)) = extract_class_app(&parent_ty) else {
                return Err(ElabError::NotImplemented(format!(
                    "structure extends: parent `{parent_ty}` is not a named structure"
                )));
            };

            // Parent must be a registered structure (single-constructor
            // inductive with a field-name table). `extends` on a non-structure
            // is rejected by Lean (`getStructureName`); mirror that.
            if self.env.get_structure_field_names(&parent_name).is_none() {
                return Err(ElabError::UnknownStruct {
                    name: parent_name.to_string(),
                });
            }

            let inductive =
                self.env
                    .get_inductive(&parent_name)
                    .ok_or_else(|| ElabError::UnknownStruct {
                        name: parent_name.to_string(),
                    })?;
            let parent_num_params = inductive.num_params as usize;

            let leaf = parent_name
                .last_component()
                .unwrap_or_else(|| parent_name.to_string());
            let to_field = Name::from_string(&format!("to{leaf}"));

            let (parent_args, parent_levels, flattened) = if parent_num_params == 0 {
                // Parameter-less parent: transitive flattening (own + subobject
                // + inherited fields). No args/levels to thread.
                (
                    Vec::new(),
                    Vec::new(),
                    self.collect_flattened_projectable(&parent_name, true),
                )
            } else {
                // Parameterized parent: the application must be saturated so the
                // projection telescope instantiation lines up.
                if parent_args.len() != parent_num_params {
                    return Err(ElabError::NotImplemented(format!(
                        "structure extends: parameterized parent `{parent_name}` \
                         must be fully applied ({parent_num_params} argument(s)), \
                         got {}",
                        parent_args.len()
                    )));
                }
                let parent_levels = head_const_levels(&parent_ty);
                let flattened = self.collect_flattened_projectable_instantiated(
                    &parent_name,
                    &parent_args,
                    &parent_levels,
                );
                (parent_args, parent_levels, flattened)
            };

            resolved.push(ParentSubobject {
                to_field,
                parent_name,
                parent_ty,
                parent_args,
                parent_levels,
                flattened,
            });
        }

        Ok(resolved)
    }

    /// Collect the DIRECT fields projectable on a parameterized `parent`, with
    /// each result type specialized to the child's `parent_args`. For a parent
    /// projection `@Parent.f : {parent_params} → Parent parent_params → T`, the
    /// telescope is instantiated with `parent_args` (the actual arguments in
    /// `extends Parent args…`), then the `self` binder is stripped, yielding the
    /// child-specialized result type `T[parent_args]`. The result type still
    /// references the child's own parameter fvars (through `parent_args`).
    ///
    /// Fail-closed per field (no derived projection emitted, so the inherited
    /// field is a LOUD unknown at the use site rather than a mis-typed one):
    /// - a projection constant whose level-parameter count differs from the
    ///   parent's (so it can't be referenced at `parent_levels`);
    /// - an under-shaped telescope (fewer binders than `parent_args` + self);
    /// - a **dependent** field whose result type still mentions the `self`
    ///   value after instantiation (loose de Bruijn index remains).
    ///
    /// Only the parent's OWN direct fields are considered — a parameterized
    /// parent's transitive (grandparent) fields are not re-exposed here (matches
    /// the class-extends path).
    fn collect_flattened_projectable_instantiated(
        &self,
        parent: &Name,
        parent_args: &[Expr],
        parent_levels: &[Level],
    ) -> Vec<(Name, Expr)> {
        let mut out: Vec<(Name, Expr)> = Vec::new();
        // Full projectable field set: the parent's own fields PLUS its inherited
        // (grandparent) fields reachable through subobject links. Each inherited
        // field `f` has an existing projection `parent.f` (re-exposed when the
        // parent was declared) sharing the parent's level params, so it
        // instantiates exactly like a direct field. This lets a child re-expose
        // grandparent fields through a PARAMETERIZED chain (Mathlib's
        // `Monoid extends Semigroup extends Mul`), matching the parameter-less
        // path — the fix propagates transitively, since fixing this makes every
        // parameterized parent re-expose its inherited fields in turn.
        let field_names = self.all_projectable_field_names(parent);
        for field in &field_names {
            let proj_const = Name::from_string(&format!("{parent}.{field}"));
            let Some(info) = self.env.get_const(&proj_const) else {
                continue;
            };
            // The parent's projections share the parent's universe params; if
            // the count does not match `parent_levels` we cannot reference this
            // projection well-formedly — descope LOUD.
            if info.level_params.len() != parent_levels.len() {
                continue;
            }
            // Instantiate the parent-parameter binders with the child's args,
            // then strip the `self : Parent parent_args` binder.
            let mut ty = info.type_.clone();
            let mut telescope_ok = true;
            for arg in parent_args {
                match ty.kind() {
                    clean_kernel::ExprKind::Pi(_, _, body) => ty = body.instantiate(arg),
                    _ => {
                        telescope_ok = false;
                        break;
                    }
                }
            }
            if !telescope_ok {
                continue;
            }
            let result_ty = match ty.kind() {
                clean_kernel::ExprKind::Pi(_, _, body) => body.as_ref().clone(),
                _ => continue,
            };
            // A self-dependent field's result type still mentions `self` after
            // stripping (loose bvar 0). Because the parent params were
            // INSTANTIATED above (not merely stripped), `self` is the only
            // possible loose bvar, and `build_inherited_projections` retargets it
            // onto `Child.toParent` — exactly as in the monomorphic path. (An
            // unexpected deeper loose bvar would make the derived projection type
            // ill-formed and be rejected LOUD by the kernel, never silently.)
            out.push((field.clone(), result_ty));
        }
        out
    }

    /// Collect every field projectable on `parent` — its own fields, its own
    /// subobject links, and (transitively) its inherited fields — as
    /// `(field_name, result_type)`. Each name `f` corresponds to an existing
    /// projection constant `parent.f`, so a child that `extends parent` can
    /// re-expose it as `Child.f := parent.f (Child.toParent self)`.
    ///
    /// A field whose projection result type is self-dependent (a loose bvar 0 =
    /// `self`, e.g. `w : Wrap n`) is kept only when `allow_self_dep` is set (the
    /// immediate parent); `build_inherited_projections` then retargets that bvar
    /// onto `Child.toParent`. Otherwise such fields are dropped fail-closed
    /// (no re-exposed projection) rather than emitting a malformed one.
    /// `allow_self_dep`: keep DIRECT fields whose result type is self-dependent
    /// (a loose bvar 0 = the parent's `self`, e.g. `w : Wrap n`). The inherited
    /// projection builder re-targets that bvar onto the child via
    /// `Child.toParent`. Only safe for the child's IMMEDIATE parent — a
    /// grandparent field's self-dependency is on the grandparent's `self`, which
    /// the direct `toParent` can't retarget, so the recursion drops those
    /// (`false`), matching the prior always-drop behavior for grandparents.
    fn collect_flattened_projectable(
        &self,
        parent: &Name,
        allow_self_dep: bool,
    ) -> Vec<(Name, Expr)> {
        use std::collections::HashSet;
        let mut out: Vec<(Name, Expr)> = Vec::new();
        let mut seen: HashSet<Name> = HashSet::new();
        let Some(field_names) = self.env.get_structure_field_names(parent) else {
            return out;
        };
        let field_names: Vec<Name> = field_names.to_vec();
        for field in &field_names {
            if let Some(result_ty) = self.projection_result_type(parent, field, allow_self_dep) {
                if seen.insert(field.clone()) {
                    out.push((field.clone(), result_ty));
                }
            }
            // If `field` is itself a subobject of `parent`, expose the
            // grandparent's fields too (`parent.<grandField>` exists as a
            // composition constant generated when `parent` was declared).
            if let Some(grandparent) = self.subobject_parent_of(parent, field) {
                for (gf, gty) in self.collect_flattened_projectable(&grandparent, false) {
                    if seen.insert(gf.clone()) {
                        out.push((gf, gty));
                    }
                }
            }
        }
        out
    }

    /// If `field` is a subobject link of `parent` (`extends`), return the
    /// grandparent structure it embeds. Reads the elaborator-only subobject
    /// metadata recorded at declaration time.
    fn subobject_parent_of(&self, parent: &Name, field: &Name) -> Option<Name> {
        self.env
            .get_structure_parents(parent)
            .and_then(|parents| parents.iter().find(|(f, _)| f == field))
            .map(|(_, p)| p.clone())
    }

    /// All field names projectable on `parent` — its OWN declared fields plus,
    /// transitively through subobject (`extends`) links, its inherited
    /// (grandparent…) fields. Each returned name `f` has an existing projection
    /// constant `parent.f`. De-duplicated, first occurrence wins (matching the
    /// diamond-copy approximation).
    fn all_projectable_field_names(&self, parent: &Name) -> Vec<Name> {
        use std::collections::HashSet;
        let mut out: Vec<Name> = Vec::new();
        let mut seen: HashSet<Name> = HashSet::new();
        let Some(field_names) = self.env.get_structure_field_names(parent) else {
            return out;
        };
        for field in field_names {
            if seen.insert(field.clone()) {
                out.push(field.clone());
            }
            if let Some(grandparent) = self.subobject_parent_of(parent, field) {
                for gf in self.all_projectable_field_names(&grandparent) {
                    if seen.insert(gf.clone()) {
                        out.push(gf);
                    }
                }
            }
        }
        out
    }

    /// The result type of the projection constant `struct.field`, i.e. the
    /// codomain of `struct.field : (params) → Struct params → T`, for a
    /// parameter-less `struct`. Returns `None` if the constant is missing or the
    /// telescope is too short.
    ///
    /// If `T` is dependent (has loose bvars) it is normally dropped. When
    /// `allow_self_dep` is set AND `struct` is monomorphic (`num_params == 0`),
    /// the ONLY possible loose bvar is bvar 0 = `self`, so the self-dependent
    /// result type (`w : Wrap n` ⇒ `Wrap (Struct.n self)`) is returned with that
    /// bvar intact for the inherited-projection builder to retarget via
    /// `Child.toParent`. A parameterized `struct` with loose bvars could leave
    /// param bvars that this path can't retarget, so it is still dropped.
    fn projection_result_type(
        &self,
        struct_name: &Name,
        field: &Name,
        allow_self_dep: bool,
    ) -> Option<Expr> {
        let proj_name = Name::from_string(&format!("{struct_name}.{field}"));
        let info = self.env.get_const(&proj_name)?;
        let num_params = self
            .env
            .get_inductive(struct_name)
            .map(|ind| ind.num_params as usize)
            .unwrap_or(0);
        // Strip the parent params (0 for a parameter-less parent) plus the
        // single `self : Struct …` binder to reach the field's result type.
        let mut ty = &info.type_;
        for _ in 0..(num_params + 1) {
            match ty.kind() {
                clean_kernel::ExprKind::Pi(_, _, body) => ty = body,
                _ => return None,
            }
        }
        if ty.has_loose_bvars() && !(allow_self_dep && num_params == 0) {
            return None;
        }
        Some(ty.clone())
    }

    /// Synthesize the derived projections a child structure exposes for the
    /// fields it inherits through its parent subobjects — Lean's on-the-fly
    /// `mkBaseProjections` composition (`src/Lean/Elab/App.lean` ~1700-1710),
    /// materialized here as reducible definitions so field access, method dot
    /// notation, and structure-literal parent assembly all resolve them exactly
    /// as they do for `.olean`-imported subobject structures.
    ///
    /// For each subobject `toParent : Parent` at constructor index `to_idx`, and
    /// each field `f` projectable on `Parent` (from
    /// [`ParentSubobject::flattened`]), generates
    /// `Child.f : (params) → Child params → T_f`
    /// `      := fun params self => Parent.f (Child.toParent params self)`.
    /// The inner `Child.toParent` is referenced as a constant (a direct kernel
    /// projection registered earlier), giving the exact body shape
    /// `Parent.f (Child.toParent self)` that `inherited_field_parent_proj`
    /// recognizes. `already` holds names already claimed by own fields, direct
    /// projections, or earlier parents (first parent wins on overlap).
    #[allow(clippy::too_many_arguments)]
    fn build_inherited_projections(
        &mut self,
        struct_name: &Name,
        struct_levels: &[Level],
        binders: &[SurfaceBinder],
        binder_types: &[Expr],
        param_fvars: &[clean_kernel::FVarId],
        subobjects: &[ParentSubobject],
        already: &mut std::collections::HashSet<Name>,
    ) -> Vec<(Name, Expr, Expr)> {
        let mut out: Vec<(Name, Expr, Expr)> = Vec::new();

        for sub in subobjects {
            let to_field_name = Name::from_string(&format!("{struct_name}.{}", sub.to_field));
            for (field, result_ty) in &sub.flattened {
                if !already.insert(field.clone()) {
                    continue;
                }
                let proj_name = Name::from_string(&format!("{struct_name}.{field}"));
                let parent_field_name = Name::from_string(&format!("{}.{field}", sub.parent_name));
                // Level list for the parent-field reference. For a PARAMETERIZED
                // parent the projection shares the parent's universe params (the
                // levels the child applied to the parent — `sub.parent_levels`),
                // vetted equal-arity in `collect_flattened_projectable_instantiated`.
                // For a monomorphic parent, use the parent projection's own
                // declared level params (fresh when universe-polymorphic) so the
                // reference is well-formed.
                let parent_field_levels: Vec<Level> = if sub.parent_args.is_empty() {
                    self.env
                        .get_const(&parent_field_name)
                        .map(|info| {
                            info.level_params
                                .iter()
                                .map(|_| self.fresh_universe_param())
                                .collect()
                        })
                        .unwrap_or_default()
                } else {
                    sub.parent_levels.clone()
                };

                // Rebuild the parameter scope (mirrors the direct-projection
                // loop): each param binder type may reference earlier params.
                let mut proj_param_fvars = Vec::with_capacity(binders.len());
                let mut proj_param_types = Vec::with_capacity(binders.len());
                for (i, binder) in binders.iter().enumerate() {
                    let mut bty = binder_types[i].clone();
                    for (j, pf) in proj_param_fvars.iter().enumerate() {
                        bty = bty.subst_fvar(param_fvars[j], &Expr::fvar(*pf));
                    }
                    let fv = self.push_local(binder.name.clone(), bty.clone());
                    proj_param_types.push(bty);
                    proj_param_fvars.push(fv);
                }

                let mut struct_applied = Expr::const_(struct_name.clone(), struct_levels.to_vec());
                for pf in &proj_param_fvars {
                    struct_applied = Expr::app(struct_applied, Expr::fvar(*pf));
                }
                let self_fvar = self.push_local("self".to_string(), struct_applied.clone());

                // `Child.toParent params self`
                let mut to_parent = Expr::const_(to_field_name.clone(), struct_levels.to_vec());
                for pf in &proj_param_fvars {
                    to_parent = Expr::app(to_parent, Expr::fvar(*pf));
                }
                to_parent = Expr::app(to_parent, Expr::fvar(self_fvar));

                // `@Parent.field <parent_args> (Child.toParent params self)`.
                // `sub.parent_args` reference the ORIGINAL structure param fvars;
                // rebind them (and the field's result type) onto this
                // projection's own param scope. For a monomorphic parent
                // `parent_args` is empty and `result_ty` is closed, so both
                // rebinds are no-ops and the body is `Parent.field (toParent …)`.
                let rebind = |e: &Expr| -> Expr {
                    let mut r = e.clone();
                    for (j, pf) in proj_param_fvars.iter().enumerate() {
                        r = r.subst_fvar(param_fvars[j], &Expr::fvar(*pf));
                    }
                    r
                };
                let mut body = Expr::const_(parent_field_name.clone(), parent_field_levels.clone());
                for arg in &sub.parent_args {
                    body = Expr::app(body, rebind(arg));
                }
                // For a SELF-DEPENDENT inherited field (`w : Wrap n` on the parent
                // ⇒ `result_ty = Wrap (Parent.n self)`, loose bvar 0 = the parent
                // `self`), retarget that `self` onto this child by substituting
                // `Child.toParent params self` for the bvar — giving
                // `Wrap (Parent.n (Child.toParent … self))`, which matches the
                // type of the body `Parent.w (Child.toParent … self)`. A
                // non-dependent (closed) `result_ty` has no loose bvar, so
                // `instantiate` is a no-op. Computed before `to_parent` is moved
                // into `body` so the retargeting can borrow it.
                let result_ty_rebound = rebind(result_ty);
                let result_ty_self = if result_ty_rebound.has_loose_bvars() {
                    result_ty_rebound.instantiate(&to_parent)
                } else {
                    result_ty_rebound
                };
                body = Expr::app(body, to_parent);

                let proj_val_inner = body.abstract_fvar(self_fvar);
                let proj_val_lam =
                    Expr::lam(BinderInfo::Default, struct_applied.clone(), proj_val_inner);
                // For a closed `result_ty` abstracting `self` is a no-op; for a
                // retargeted self-dependent type it binds the `Child.toParent …
                // self` occurrences into the projection's `self` Pi binder.
                let proj_ty_inner = result_ty_self.abstract_fvar(self_fvar);
                let proj_ty_arrow = Expr::pi(BinderInfo::Default, struct_applied, proj_ty_inner);

                self.pop_local(); // self

                let mut proj_ty = proj_ty_arrow;
                let mut proj_val = proj_val_lam;
                for i in (0..binders.len()).rev() {
                    proj_ty = proj_ty.abstract_fvar(proj_param_fvars[i]);
                    proj_val = proj_val.abstract_fvar(proj_param_fvars[i]);
                    // The structure parameters are IMPLICIT in a derived
                    // inherited projection (Lean's `mkProjections` makes structure
                    // params implicit). A direct projection is dot-notation-
                    // resolved via the field-table metadata, which inserts its
                    // (even explicit) params from the receiver's type; a derived
                    // projection is a plain def with no such metadata, so its
                    // params must be implicit for `x.field` to infer them from
                    // `x`'s type (`@Child.field {α} x` — `α` from `x : Child α`).
                    proj_ty = Expr::pi(BinderInfo::Implicit, proj_param_types[i].clone(), proj_ty);
                    proj_val =
                        Expr::lam(BinderInfo::Implicit, proj_param_types[i].clone(), proj_val);
                }
                for _ in 0..binders.len() {
                    self.pop_local();
                }

                out.push((proj_name, proj_ty, proj_val));
            }
        }

        out
    }

    fn infer_implicit_structure_result_ty(&self, field_types: &[Expr]) -> Result<Expr, ElabError> {
        let Some((first_field_ty, rest_field_tys)) = field_types.split_first() else {
            return Ok(Expr::type_());
        };

        let mut result_level = self.infer_sort(first_field_ty)?;
        for field_ty in rest_field_tys {
            result_level = Level::max(result_level, self.infer_sort(field_ty)?);
        }

        Ok(Expr::sort(result_level))
    }

    /// Elaborate a structure declaration
    ///
    /// A structure is syntactic sugar for a single-constructor inductive with named fields.
    /// `structure Point where x : Nat  y : Nat`
    /// becomes:
    /// - Inductive `Point : Type` with constructor `Point.mk : Nat → Nat → Point`
    /// - Field names registered: ["x", "y"]
    #[allow(clippy::too_many_arguments)] // mirrors the surface decl's components
    pub(super) fn elab_structure(
        &mut self,
        name: &str,
        universe_params: &[String],
        binders: &[SurfaceBinder],
        extends: &[Box<SurfaceExpr>],
        ty: Option<&SurfaceExpr>,
        custom_ctor: Option<&str>,
        fields: &[SurfaceField],
        deriving: &[String],
        modifiers: &DeclModifiers,
        kind: StructureKind,
    ) -> Result<ElabResult, ElabError> {
        let struct_name = Name::from_string(name);
        // Constructor name: the explicit `structCtor` (`structure P where make ::`)
        // when present, else the default `mk` (Lean `mkConstructorName`).
        let ctor_name = Name::from_string(&format!("{name}.{}", custom_ctor.unwrap_or("mk")));

        // SAFETY: Number of params bounded by practical limits (no structure has billions of params)
        let num_params = u32::try_from(binders.len()).unwrap_or(u32::MAX);

        // Cache elaborated binder types so we can rebuild the declaration shape
        // after field elaboration without re-elaborating under the field scope.
        let mut binder_types = Vec::with_capacity(binders.len());
        let mut param_fvars = Vec::with_capacity(binders.len());

        for binder in binders {
            let binder_ty = if let Some(t) = &binder.ty {
                self.elaborate(t)?
            } else {
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());
            binder_types.push(binder_ty);
            param_fvars.push(fvar);
        }

        // Resolve `extends` parents into embedded subobjects (Lean's subobject
        // layout — `src/Lean/Elab/Structure.lean` `withParents`). Done AFTER the
        // structure's binders are pushed so a parameterized parent's argument
        // (`α` in `extends Inh α`) resolves to the structure's own parameter
        // fvar. Parameter-less and (saturated) parameterized parents are both
        // supported; residual shapes fail closed LOUD.
        let parent_subobjects = self.resolve_parent_subobjects(extends)?;

        // Bare `name := value` field-default OVERRIDES (B90): each re-defaults
        // an inherited field for this structure. An override is NOT a
        // constructor field — it gets no projection and no field fvar; it only
        // mints a `<Struct>.<field>._default` definition (plus a native
        // default-table entry) that literal-time filling prefers over the
        // parent's own default. `own_fields` is the untouched `fields` slice
        // when no override is present (engagement gate: previously-working
        // shapes take a byte-identical path).
        let has_overrides = fields.iter().any(|f| f.is_default_override);
        let own_fields_storage: Vec<SurfaceField>;
        let own_fields: &[SurfaceField] = if has_overrides {
            own_fields_storage = fields
                .iter()
                .filter(|f| !f.is_default_override)
                .cloned()
                .collect();
            &own_fields_storage
        } else {
            fields
        };
        let mut override_default_fns: Vec<(Name, Expr, Expr)> = Vec::new();
        let mut override_field_defaults: Vec<(Name, Expr)> = Vec::new();
        for field in fields.iter().filter(|f| f.is_default_override) {
            // Resolve the overridden field's type from the parents' projectable
            // fields. A name that is not inherited is a LOUD error — this is
            // also the path a class-body override lands on (the class path
            // passes extends = [], so `parent_subobjects` is empty there).
            let inherited_ty = parent_subobjects
                .iter()
                .flat_map(|sub| sub.flattened.iter())
                .find(|(pf_name, _)| pf_name.to_string() == field.name)
                .map(|(_, pf_ty)| pf_ty.clone());
            let Some(pf_ty) = inherited_ty else {
                let inherited_names: Vec<String> = parent_subobjects
                    .iter()
                    .flat_map(|sub| sub.flattened.iter())
                    .map(|(pf_name, _)| pf_name.to_string())
                    .collect();
                return Err(ElabError::UnknownStructureField {
                    struct_name: struct_name.clone(),
                    field: field.name.clone(),
                    suggestions: crate::agent_diagnostics::nearest_string_candidates(
                        &field.name,
                        inherited_names.iter().map(String::as_str),
                        5,
                    ),
                });
            };
            // The parser always attaches the override's value; a missing one
            // is an internal invariant break, reported loudly rather than
            // silently treated as "no default".
            let Some(default_expr) = &field.default else {
                return Err(ElabError::NotImplemented(format!(
                    "structure default override `{}.{}` has no value",
                    name, field.name
                )));
            };
            let val = self.elaborate_with_expected_type(default_expr, Some(pf_ty.clone()))?;
            let val = self.metas.instantiate(&val);
            let val = self.metas.instantiate_levels(&val);
            let pf_ty = self.metas.instantiate_levels(&pf_ty);
            if val.has_fvar_quick() || pf_ty.has_fvar_quick() {
                // Only CLOSED override values are supported: a value (or an
                // inherited field type) referencing the structure's parameters
                // or earlier fields would need the `_default`-fn abstraction
                // pass. Descope LOUDLY rather than register a leaking term.
                return Err(ElabError::NotImplemented(format!(
                    "structure default override `{}.{}` referencing fields or \
                     parameters is not supported yet",
                    name, field.name
                )));
            }
            override_default_fns.push((
                Name::from_string(&format!("{}.{}._default", struct_name, field.name)),
                pf_ty,
                val.clone(),
            ));
            override_field_defaults.push((Name::from_string(&field.name), val));
        }

        // Unified constructor-field list: one embedded `toParent : Parent`
        // subobject field per parent first (Lean flatten order: parents precede
        // own fields — `withParents … withFields`, Elab/Structure:1526-1527),
        // then locally declared fields. The parent's OWN fields are NOT
        // flattened into the child constructor; they are re-exposed as derived
        // projections after the constructor and direct projections are built.
        let all_fields: Vec<FieldSpec<'_>> = parent_subobjects
            .iter()
            .map(|sub| FieldSpec::Inherited {
                name: sub.to_field.to_string(),
                ty: sub.parent_ty.clone(),
                default: None,
            })
            .chain(own_fields.iter().map(FieldSpec::Own))
            .collect();

        let explicit_result_ty = ty.map(|t| self.elaborate(t)).transpose()?;

        let mut field_types = Vec::with_capacity(all_fields.len());
        let mut field_fvars = Vec::with_capacity(all_fields.len());
        let mut field_names = Vec::with_capacity(all_fields.len());
        // In-file field defaults (`b : Nat := 0`), elaborated against the field
        // type so the omitted-field fill in `elab_struct_lit` can consult them.
        // Only defaults that are closed w.r.t. the field/parameter locals are
        // recorded — a default that still references an earlier field free
        // variable is skipped (treated as no default), which fails closed: the
        // field is then reported missing exactly as before rather than filled
        // with an fvar-leaking term. Every recorded default is re-checked by the
        // kernel when the completed constructor application is elaborated.
        // Inherited defaults are already elaborated closed kernel terms.
        // Seeded with the bare-override defaults resolved above (B90) so the
        // native table also carries the overridden values.
        let mut field_defaults: Vec<(Name, Expr)> = override_field_defaults;
        // Own-field defaults that reference earlier fields/params — a default
        // METHOD like `greet := fun a => base a + 1` — cannot be stored as a
        // closed value; record `(field_index, field_name, default_val)` here to
        // emit a `<Struct>.<field>._default` function below (Lean
        // `mkDefaultFnOfStructField`). The index is the field's position among
        // all fields (aligned with `field_fvars`/`field_types`).
        let mut dependent_field_defaults: Vec<(usize, String, Expr)> = Vec::new();
        // Names bound in `meta_value_bindings` so that inherited parent fields
        // resolve as BARE identifiers in later field types (`uq : ∀ a, a =
        // deflt` where `deflt` is inherited from `Inh` through `toInh`). Each is
        // bound to `@Parent.field parent_args (toParent_fvar)`, so a reference
        // splices the projection-through-the-subobject directly (Lean brings
        // parent fields into the field-elaboration scope). Removed after the
        // field loop so they never leak to sibling declarations.
        let mut inherited_field_bindings: Vec<String> = Vec::new();

        for (field_idx, spec) in all_fields.iter().enumerate() {
            let field_ty = match spec {
                FieldSpec::Inherited { ty, default, .. } => {
                    if let Some(default_val) = default {
                        if !default_val.has_fvar_quick() {
                            field_defaults
                                .push((Name::from_string(spec.name()), default_val.clone()));
                        }
                    }
                    ty.clone()
                }
                FieldSpec::Own(field) => {
                    let field_ty = self.elaborate(&field.ty)?;
                    if let Some(default_expr) = &field.default {
                        let default_val = self
                            .elaborate_with_expected_type(default_expr, Some(field_ty.clone()))?;
                        let default_val = self.metas.instantiate(&default_val);
                        let default_val = self.metas.instantiate_levels(&default_val);
                        if !default_val.has_fvar_quick() {
                            field_defaults.push((Name::from_string(&field.name), default_val));
                        } else {
                            // References earlier fields/params (or, defensively, a
                            // residual metavariable). Defer to `_default`-fn
                            // generation below, which re-checks closedness and
                            // fails closed (skips) if any fvar/meta survives
                            // abstraction — preserving the old "no default"
                            // behavior in the pathological case. B12 (`p04`).
                            dependent_field_defaults.push((
                                field_idx,
                                field.name.clone(),
                                default_val,
                            ));
                        }
                    }
                    field_ty
                }
            };
            let fvar = self.push_local(spec.name().to_string(), field_ty.clone());
            field_types.push(field_ty);
            field_fvars.push(fvar);
            field_names.push(Name::from_string(spec.name()));

            // For each embedded parent subobject (the first `parent_subobjects`
            // entries of `all_fields`, in order), bind the parent's projectable
            // fields as bare identifiers to their projection through the
            // just-pushed `toParent` fvar, so a later own field can reference an
            // inherited field by name. The spliced term references only the
            // `toParent` fvar and the structure's parameter fvars (all in
            // scope), so it is captured by the constructor/projection
            // abstraction exactly like any other earlier-field reference.
            if field_idx < parent_subobjects.len() {
                let sub = &parent_subobjects[field_idx];
                for (pf_name, _) in &sub.flattened {
                    let key = pf_name.to_string();
                    if self.meta_value_bindings.contains_key(&key) {
                        // First parent to expose a name wins (matches the
                        // derived-projection `already` shadowing rule).
                        continue;
                    }
                    let parent_field_const =
                        Name::from_string(&format!("{}.{}", sub.parent_name, pf_name));
                    let mut val = Expr::const_(parent_field_const, sub.parent_levels.clone());
                    for arg in &sub.parent_args {
                        val = Expr::app(val, arg.clone());
                    }
                    val = Expr::app(val, Expr::fvar(fvar));
                    self.meta_value_bindings.insert(key.clone(), val);
                    inherited_field_bindings.push(key);
                }
            }
        }

        // The inherited-field bare bindings are scoped to this structure's field
        // elaboration only — drop them before building the constructor /
        // projections and before any sibling declaration is elaborated.
        for key in &inherited_field_bindings {
            self.meta_value_bindings.remove(key);
        }

        let result_ty = if let Some(result_ty) = explicit_result_ty {
            result_ty
        } else {
            self.infer_implicit_structure_result_ty(&field_types)?
        };

        // Build the structure type: (param1 : T1) → ... → (paramN : TN) → Type
        let mut struct_ty = result_ty.clone();
        for i in (0..binders.len()).rev() {
            struct_ty = struct_ty.abstract_fvar(param_fvars[i]);
            let bi = convert_binder_info(binders[i].info);
            struct_ty = Expr::pi(bi, binder_types[i].clone(), struct_ty);
        }

        let struct_levels: Vec<Level> = self
            .universe_params
            .iter()
            .map(|s| Level::param(Name::from_string(s)))
            .collect();
        let mut ctor_result = Expr::const_(struct_name.clone(), struct_levels.clone());
        for fvar in &param_fvars {
            ctor_result = Expr::app(ctor_result, Expr::fvar(*fvar));
        }

        // Build constructor type: (field1 : T1) → ... → (fieldN : TN) → StructName params
        let mut ctor_ty = ctor_result.clone();
        for i in (0..all_fields.len()).rev() {
            ctor_ty = ctor_ty.abstract_fvar(field_fvars[i]);
            ctor_ty = Expr::pi(BinderInfo::Default, field_types[i].clone(), ctor_ty);
        }

        // Emit `<Struct>.<field>._default` functions for the dependent defaults
        // recorded above. Each is abstracted over the structure parameters and
        // the PRECEDING fields (constructor order), so its Pi-arity is
        // `num_params + field_idx`; `elab_struct_lit::field_default_value`
        // applies it to `param_args ++ preceding_field_values` truncated to that
        // arity to reconstruct the omitted field's value. Lean shape:
        // `mkDefaultFnOfStructField` (`src/Lean/Elab/StructInst.lean`). The
        // preceding-field/param abstraction mirrors the constructor-type build
        // (above) so earlier-field references inside later field-type domains are
        // captured by the subsequent abstraction passes. Field fvars are still in
        // scope here (popped just below). A default that does NOT close under
        // this abstraction (a stray metavariable) is dropped — fail-closed to the
        // pre-existing "no default" behavior. B12 (`p04`/`p13`).
        let mut default_fns: Vec<(Name, Expr, Expr)> = Vec::new();
        for (field_idx, field_name, default_val) in &dependent_field_defaults {
            let default_fn_name =
                Name::from_string(&format!("{}.{}._default", struct_name, field_name));
            let mut dval = default_val.clone();
            let mut dty = field_types[*field_idx].clone();
            for j in (0..*field_idx).rev() {
                dval = Expr::lam(
                    BinderInfo::Default,
                    field_types[j].clone(),
                    dval.abstract_fvar(field_fvars[j]),
                );
                dty = Expr::pi(
                    BinderInfo::Default,
                    field_types[j].clone(),
                    dty.abstract_fvar(field_fvars[j]),
                );
            }
            for i in (0..binders.len()).rev() {
                let bi = convert_binder_info(binders[i].info);
                dval = Expr::lam(
                    bi,
                    binder_types[i].clone(),
                    dval.abstract_fvar(param_fvars[i]),
                );
                dty = Expr::pi(
                    bi,
                    binder_types[i].clone(),
                    dty.abstract_fvar(param_fvars[i]),
                );
            }
            if !dval.has_fvar_quick() && !dty.has_fvar_quick() {
                default_fns.push((default_fn_name, dty, dval));
            }
        }

        // Bare-override `_default` definitions (B90) ride the same registration
        // as the dependent-default fns; their values were required closed above,
        // so no abstraction pass is needed here.
        default_fns.extend(override_default_fns);

        // Pop field fvars
        for _ in 0..all_fields.len() {
            self.pop_local();
        }

        // Generate projection functions
        // For each field i with type Ti, generate:
        //   StructName.fieldname : (params...) → StructName params → Ti
        //   StructName.fieldname = λ params s => s.i
        //
        // We reuse the field types already elaborated above (`field_types`),
        // which cover both inherited and own fields uniformly. Those types still
        // reference the original parameter fvars (`param_fvars`) and earlier
        // field fvars (`field_fvars`); we rebind params to the projection scope
        // and replace earlier-field references with projections of `self`.
        //
        // Binder infos follow Lean 4's `mkProjections` (see [`StructureKind`]):
        // for a CLASS the params are implicit and `self` is instance-implicit,
        // so `C.f x` gets `{α}`/`[self]` inserted by the application
        // elaborator; for a structure `self` stays explicit.
        let self_binder_info = match kind {
            StructureKind::Class => BinderInfo::InstImplicit,
            StructureKind::Structure => BinderInfo::Default,
        };
        let mut projections = Vec::new();

        for (field_idx, spec) in all_fields.iter().enumerate() {
            let proj_name = Name::from_string(&format!("{}.{}", name, spec.name()));

            // Recreate the parameter scope using the cached binder types.
            let mut proj_param_fvars = Vec::with_capacity(binders.len());
            let mut proj_param_types = Vec::with_capacity(binders.len());
            for (i, binder) in binders.iter().enumerate() {
                let mut binder_ty = binder_types[i].clone();
                for (j, proj_fvar) in proj_param_fvars.iter().enumerate() {
                    binder_ty = binder_ty.subst_fvar(param_fvars[j], &Expr::fvar(*proj_fvar));
                }
                let fvar = self.push_local(binder.name.clone(), binder_ty.clone());
                proj_param_types.push(binder_ty);
                proj_param_fvars.push(fvar);
            }

            // Build struct type applied to params: StructName.{u1, ..., un} param1 ... paramN
            let mut struct_applied = Expr::const_(struct_name.clone(), struct_levels.clone());
            for fvar in &proj_param_fvars {
                struct_applied = Expr::app(struct_applied, Expr::fvar(*fvar));
            }

            // Push a local for the structure value FIRST
            // This is needed so that we can refer to it in field types
            let struct_fvar = self.push_local("self".to_string(), struct_applied.clone());

            // Start from the already-elaborated field type. Rebind the original
            // parameter fvars to the projection scope's params so the projection
            // return type is expressed over the projection's own binders.
            let mut proj_field_ty = field_types[field_idx].clone();
            for (j, &proj_fvar) in proj_param_fvars.iter().enumerate() {
                proj_field_ty = proj_field_ty.subst_fvar(param_fvars[j], &Expr::fvar(proj_fvar));
            }

            // Replace earlier field references with projections of struct_fvar.
            // For each earlier field j, replace FVar(field_fvars[j]) with s.j.
            for j in (0..field_idx).rev() {
                // SAFETY: Field indices bounded by number of fields in structure
                let j_u32 = u32::try_from(j).unwrap_or(u32::MAX);
                let projection = Expr::proj(struct_name.clone(), j_u32, Expr::fvar(struct_fvar));
                proj_field_ty = proj_field_ty.subst_fvar(field_fvars[j], &projection);
            }

            // Build projection value: Expr::proj(struct_name, field_idx, self)
            // SAFETY: Field index bounded by number of fields in structure
            let field_idx_u32 = u32::try_from(field_idx).unwrap_or(u32::MAX);
            let proj_body = Expr::proj(struct_name.clone(), field_idx_u32, Expr::fvar(struct_fvar));

            // Abstract over the struct value
            let proj_val_inner = proj_body.abstract_fvar(struct_fvar);
            let proj_val_lam = Expr::lam(self_binder_info, struct_applied.clone(), proj_val_inner);

            // Build return type: StructName params → FieldType
            let proj_ty_inner = proj_field_ty.abstract_fvar(struct_fvar);
            let proj_ty_arrow = Expr::pi(self_binder_info, struct_applied, proj_ty_inner);

            self.pop_local(); // pop struct_fvar

            // Abstract over params for both type and value
            let mut proj_ty = proj_ty_arrow;
            let mut proj_val = proj_val_lam;
            for i in (0..binders.len()).rev() {
                proj_ty = proj_ty.abstract_fvar(proj_param_fvars[i]);
                proj_val = proj_val.abstract_fvar(proj_param_fvars[i]);
                // Class params are ALWAYS implicit in projections (Lean
                // `mkProjections`; even `[inst]` params become `{inst}` —
                // v4.30.0-rc2 ground truth in [`StructureKind`]).
                let bi = match kind {
                    StructureKind::Class => BinderInfo::Implicit,
                    StructureKind::Structure => convert_binder_info(binders[i].info),
                };
                proj_ty = Expr::pi(bi, proj_param_types[i].clone(), proj_ty);
                proj_val = Expr::lam(bi, proj_param_types[i].clone(), proj_val);
            }

            // Pop param fvars
            for _ in 0..binders.len() {
                self.pop_local();
            }

            projections.push((proj_name, proj_ty, proj_val));
        }

        // Abstract constructor type over parameters. Lean 4 makes structure
        // parameters IMPLICIT in the constructor (`@Prod.mk : {α : Type u} →
        // {β : Type v} → α → β → α × β`), exactly as `elab_inductive` already
        // does for inductive constructors; the application elaborator's
        // skip-loop fits-probe keeps legacy explicit-param call sites
        // (`S.mk Nat x`) working unchanged (U2 rung 2).
        for i in (0..binders.len()).rev() {
            ctor_ty = ctor_ty.abstract_fvar(param_fvars[i]);
            ctor_ty = Expr::pi(BinderInfo::Implicit, binder_types[i].clone(), ctor_ty);
        }

        // Pop param fvars
        for _ in 0..binders.len() {
            self.pop_local();
        }

        // Re-expose each parent subobject's fields as derived projections
        // `Child.f := Parent.f (Child.toParent self)` (Lean's on-the-fly
        // `mkBaseProjections`, materialized here as reducible defs so field
        // access / dot notation / struct-literal assembly resolve them exactly
        // as for imported subobject structures). Seed `already` with the direct
        // constructor field names so an own field that shadows an inherited one
        // wins and no duplicate projection is emitted.
        if !parent_subobjects.is_empty() {
            let mut already: std::collections::HashSet<Name> =
                field_names.iter().cloned().collect();
            let inherited_projs = self.build_inherited_projections(
                &struct_name,
                &struct_levels,
                binders,
                &binder_types,
                &param_fvars,
                &parent_subobjects,
                &mut already,
            );
            projections.extend(inherited_projs);
        }

        // Register the dependent-default `_default` functions as reducible
        // definitions alongside the projections, so `elab_struct_lit` can find
        // them by name (`<Struct>.<field>._default`) when filling an omitted
        // defaulted field. They ride the same `instantiate_levels` /
        // `FilterStructSelfLevels` / surviving-level-param treatment below. B12.
        projections.extend(default_fns);

        // Snapshot universe_params before deriving — derive handlers call
        // mk_const/fresh_universe_param which would otherwise pollute the
        // struct's declared universe params with internal levels (#1828).
        let struct_universe_params_len = self.universe_params.len();

        // Generate derived instances from deriving clause. Overrides are not
        // constructor fields, so derive handlers see only `own_fields`.
        let derived_instances = self.generate_derived_instances(
            &struct_name,
            universe_params,
            binders,
            own_fields,
            &struct_ty,
            deriving,
        )?;

        // Restore universe_params to pre-derive state — the fresh params
        // allocated by derive handlers are internal to instance bodies and
        // must not leak into the struct declaration's level params.
        self.universe_params.truncate(struct_universe_params_len);

        // Substitute level constraints collected during unification
        let struct_ty = self.metas.instantiate_levels(&struct_ty);
        let ctor_ty = self.metas.instantiate_levels(&ctor_ty);
        let projections: Vec<_> = projections
            .into_iter()
            .map(|(name, ty, val)| {
                (
                    name,
                    self.metas.instantiate_levels(&ty),
                    self.metas.instantiate_levels(&val),
                )
            })
            .collect();

        // Fix for #3390: collect only level params that actually survive after
        // instantiate_levels resolves concrete assignments. Function-typed fields
        // (e.g., `Nat -> Option Nat`) introduce universe params for polymorphic
        // constants that unify to concrete levels; these must not be declared as
        // the structure's universe params.
        let mut used_level_params = Vec::new();
        collect_struct_level_params(&struct_ty, &mut used_level_params);
        collect_struct_level_params(&ctor_ty, &mut used_level_params);
        for (_, ty, val) in &projections {
            collect_struct_level_params(ty, &mut used_level_params);
            collect_struct_level_params(val, &mut used_level_params);
        }

        let surviving_universe_params: Vec<Name> = self
            .universe_params
            .iter()
            .map(|s| Name::from_string(s))
            .filter(|name| used_level_params.contains(name))
            .collect();

        // Rewrite self-references (Const(struct_name, all_levels)) to only carry
        // the surviving level params, preventing level count mismatches.
        let mut folder = FilterStructSelfLevels {
            struct_name: &struct_name,
            keep_params: &surviving_universe_params,
        };
        let ctor_ty = folder.fold_expr(&ctor_ty);
        let projections: Vec<_> = projections
            .into_iter()
            .map(|(name, ty, val)| {
                let mut f = FilterStructSelfLevels {
                    struct_name: &struct_name,
                    keep_params: &surviving_universe_params,
                };
                (name, f.fold_expr(&ty), f.fold_expr(&val))
            })
            .collect();

        // Parent subobject metadata (elaborator-only): drives anonymous-ctor
        // flattening and structure-literal parent assembly.
        let parents: Vec<(Name, Name)> = parent_subobjects
            .iter()
            .map(|sub| (sub.to_field.clone(), sub.parent_name.clone()))
            .collect();

        // Named-argument binder row shared by every projection: the struct's
        // binders then the receiver `self`, matching each projection's Pi
        // telescope built above (B92).
        let projection_param_infos: Vec<(String, BinderInfo)> = binders
            .iter()
            .map(|b| (b.name.clone(), convert_binder_info(b.info)))
            .chain(std::iter::once(("self".to_string(), self_binder_info)))
            .collect();

        // Use the surviving universe params, preserving declaration order while
        // dropping auto-bound params that unified to concrete levels.
        Ok(ElabResult::Structure {
            name: struct_name,
            universe_params: surviving_universe_params,
            num_params,
            ty: struct_ty,
            ctor_name,
            ctor_ty,
            field_names,
            field_defaults,
            projections,
            projection_param_infos,
            parents,
            derived_instances,
            class_info: None, // Set by caller for class declarations
            modifiers: *modifiers,
        })
    }
}

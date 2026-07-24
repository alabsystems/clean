// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual declaration elaboration.
//!
//! A `mutual ... end` block contains multiple definitions that may reference
//! each other. Elaboration proceeds in two passes:
//!
//! 1. **Type pass** — elaborate each declaration's type signature and register
//!    it as a local binding so subsequent declarations (and bodies) can resolve
//!    cross-references via `lookup_local`.
//! 2. **Body pass** — elaborate each declaration's body with all forward
//!    declarations in scope, then replace the temporary local references with
//!    proper `Const` expressions in the final output.

use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Constructor, Expr, ExprFolder, FVarId, InductiveDecl, InductiveType, Level};
use clean_parser::SurfaceDecl;

use super::{ElabCtx, ElabResult};

/// Per-declaration metadata collected during the type pass.
struct MutualEntry {
    /// Declaration name (qualified via namespace prefix).
    name: Name,
    /// Universe parameters for this declaration.
    universe_params: Vec<Name>,
    /// FVarId assigned when the forward declaration was pushed as a local.
    fvar: FVarId,
}

/// Per-type metadata collected during the type-head pass of a mutual
/// *inductive* block.
struct MutualIndEntry {
    /// Fully-qualified inductive type name (e.g. `Even`).
    name: Name,
    /// FVarId of the forward type-head local pushed before constructor
    /// elaboration, so sibling references (`Even.succ : Odd → Even`) resolve.
    fvar: FVarId,
    /// The elaborated inductive type (its arity/sort).
    ind_ty: Expr,
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a `mutual ... end` block.
    ///
    /// `Def`/`Theorem` members go through the forward-declaration scheme below.
    /// A block of `inductive` members is routed to [`Self::elab_mutual_inductive`],
    /// which registers the whole family in one kernel `add_inductive` call so
    /// cross-references resolve. Other declaration kinds are skipped.
    pub(super) fn elab_mutual(&mut self, decls: &[SurfaceDecl]) -> Result<ElabResult, ElabError> {
        if decls.is_empty() {
            return Ok(ElabResult::Skipped);
        }

        // Route inductive-bearing mutual blocks to the dedicated inductive path.
        // A `mutual` block in Lean 4 is homogeneous in practice (all inductives
        // or all defs); if it MIXES inductives with non-inductives we fail closed
        // rather than silently dropping the inductive members.
        let has_inductive = decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Inductive { .. }));
        if has_inductive {
            return self.elab_mutual_inductive(decls);
        }

        // A `mutual` block whose members are ALL `partial def`s with explicit
        // result types: Lean compiles these to opaque/unsafe constants
        // (non-terminating, non-reducing), so — exactly like a single
        // self-recursive `partial def` — register each member's SIGNATURE
        // opaquely (each Inhabited-guarded by `elab_partial_def_opaque`) and
        // discard the bodies. The mutual cross-references (`evenP`↔`oddP`) are
        // moot once the bodies are dropped, which is why the ordinary
        // forward-declared-fvar path below cannot close them. Total mutual
        // recursion is NOT rerouted here — an opaque constant would be an
        // unfaithful, non-reducing stand-in for a total definition.
        if decls.iter().all(|d| {
            matches!(
                d,
                SurfaceDecl::Def { modifiers, ty: Some(_), .. } if modifiers.is_partial
            )
        }) {
            let mut results = Vec::with_capacity(decls.len());
            for decl in decls {
                if let SurfaceDecl::Def {
                    name,
                    universe_params,
                    binders,
                    ty: Some(ty),
                    attrs,
                    modifiers,
                    ..
                } = decl
                {
                    results.push(self.elab_partial_def_opaque(
                        name,
                        universe_params,
                        binders,
                        ty,
                        attrs,
                        modifiers,
                    )?);
                }
            }
            return Ok(ElabResult::Multiple(results));
        }

        // ── Pass 1: elaborate type signatures and register forward decls ──

        let mut entries: Vec<MutualEntry> = Vec::with_capacity(decls.len());

        for decl in decls {
            match decl {
                SurfaceDecl::Def {
                    name,
                    universe_params,
                    binders,
                    ty,
                    ..
                } => {
                    self.universe_params = universe_params.clone();

                    let ty_expr = if let Some(ty_surface) = ty {
                        self.elab_axiom_type(binders, ty_surface)?
                    } else {
                        // No explicit type annotation — elaborate binders as a
                        // Pi over a fresh metavariable (the body will constrain
                        // it during pass 2).
                        let hole = Expr::sort(self.fresh_universe_param());
                        let meta_ty = self.fresh_meta(hole);
                        self.elab_binders_as_pi(binders, meta_ty)?
                    };

                    let ty_expr = self.metas.instantiate(&ty_expr);
                    let ty_expr = self.metas.instantiate_levels(&ty_expr);

                    let decl_name = Name::from_string(&self.qualify_name(name));
                    let univ_names: Vec<Name> = self
                        .universe_params
                        .iter()
                        .map(|s| Name::from_string(s))
                        .collect();

                    let fvar = self.push_local(name.clone(), ty_expr);

                    entries.push(MutualEntry {
                        name: decl_name,
                        universe_params: univ_names,
                        fvar,
                    });
                }

                SurfaceDecl::Theorem {
                    name,
                    universe_params,
                    binders,
                    ty,
                    ..
                } => {
                    self.universe_params = universe_params.clone();

                    let ty_expr = self.elab_axiom_type(binders, ty)?;
                    let ty_expr = self.metas.instantiate(&ty_expr);
                    let ty_expr = self.metas.instantiate_levels(&ty_expr);

                    let decl_name = Name::from_string(&self.qualify_name(name));
                    let univ_names: Vec<Name> = self
                        .universe_params
                        .iter()
                        .map(|s| Name::from_string(s))
                        .collect();

                    let fvar = self.push_local(name.clone(), ty_expr);

                    entries.push(MutualEntry {
                        name: decl_name,
                        universe_params: univ_names,
                        fvar,
                    });
                }

                // Non-def/theorem decls inside mutual are unusual; skip them.
                _ => {}
            }
        }

        // ── Pass 2: elaborate bodies with forward declarations in scope ──

        let mut results: Vec<ElabResult> = Vec::with_capacity(entries.len());
        let mut entry_idx = 0;

        for decl in decls {
            match decl {
                SurfaceDecl::Def {
                    universe_params,
                    binders,
                    ty,
                    val,
                    attrs,
                    modifiers,
                    ..
                } => {
                    let entry = &entries[entry_idx];
                    self.universe_params = universe_params.clone();

                    let (ty_expr, val_expr) = self.elab_def_body(binders, ty.as_deref(), val)?;

                    let ty_expr = self.metas.instantiate(&ty_expr);
                    let val_expr = self.metas.instantiate(&val_expr);
                    let ty_expr = self.metas.instantiate_levels(&ty_expr);
                    let val_expr = self.metas.instantiate_levels(&val_expr);

                    let auto_implicits = self.take_auto_implicits();
                    let (ty_expr, val_expr) =
                        Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

                    // Replace forward-declaration fvars with Const references.
                    let ty_expr = self.replace_mutual_fvars(&entries, ty_expr);
                    let val_expr = self.replace_mutual_fvars(&entries, val_expr);

                    self.ensure_known_attributes(attrs)?;
                    self.collect_attributes(&entry.name, attrs);

                    results.push(ElabResult::Definition {
                        name: entry.name.clone(),
                        universe_params: entry.universe_params.clone(),
                        ty: ty_expr,
                        val: val_expr,
                        modifiers: *modifiers,
                    });

                    entry_idx += 1;
                }

                SurfaceDecl::Theorem {
                    universe_params,
                    binders,
                    ty,
                    proof,
                    attrs,
                    modifiers,
                    ..
                } => {
                    let entry = &entries[entry_idx];
                    self.universe_params = universe_params.clone();

                    let (ty_expr, proof_expr) = self.elab_def_body(binders, Some(ty), proof)?;

                    let ty_expr = self.metas.instantiate(&ty_expr);
                    let proof_expr = self.metas.instantiate(&proof_expr);
                    let ty_expr = self.metas.instantiate_levels(&ty_expr);
                    let proof_expr = self.metas.instantiate_levels(&proof_expr);

                    let auto_implicits = self.take_auto_implicits();
                    let (ty_expr, proof_expr) =
                        Self::wrap_with_auto_implicits(ty_expr, proof_expr, &auto_implicits);

                    let ty_expr = self.replace_mutual_fvars(&entries, ty_expr);
                    let proof_expr = self.replace_mutual_fvars(&entries, proof_expr);

                    self.ensure_known_attributes(attrs)?;
                    self.collect_attributes(&entry.name, attrs);

                    results.push(ElabResult::Theorem {
                        name: entry.name.clone(),
                        universe_params: entry.universe_params.clone(),
                        ty: ty_expr,
                        proof: proof_expr,
                        modifiers: *modifiers,
                    });

                    entry_idx += 1;
                }

                _ => {}
            }
        }

        // ── cleanup: pop all forward-declaration locals (LIFO order) ──
        for _ in &entries {
            self.pop_local();
        }

        Ok(ElabResult::Multiple(results))
    }

    /// Elaborate a `mutual … end` block of `inductive` declarations into ONE
    /// kernel [`InductiveDecl`] with several `types`.
    ///
    /// Two-pass mutual-inductive scheme (matching the kernel's expectation):
    ///
    /// 1. **Type-head pass** — elaborate each inductive's type signature and push
    ///    it as a local (under its SHORT name) so a sibling constructor
    ///    (`Even.succ : Odd → Even`) can resolve `Odd` before `Odd` exists in the
    ///    environment.
    /// 2. **Constructor pass** — with all heads in scope, elaborate every
    ///    constructor type, then replace all forward type-head fvars with `Const`
    ///    references to the family's types.
    ///
    /// The whole family is returned as a single [`ElabResult::MutualInductive`],
    /// which registration hands to `env.add_inductive` in one call — the kernel
    /// re-checks positivity, builds the mutual recursors, and rejects an
    /// ill-formed family (which surfaces as a real error, never a silent drop).
    ///
    /// Fail-closed scope: parameters and universe parameters on a mutual
    /// inductive member are not yet threaded here, so they are rejected with a
    /// clear [`ElabError::Unsupported`] rather than registering a half-formed
    /// type. The types-and-constructors path (sufficient to use the types in
    /// `def`s) is fully supported.
    pub(super) fn elab_mutual_inductive(
        &mut self,
        decls: &[SurfaceDecl],
    ) -> Result<ElabResult, ElabError> {
        // A mutual inductive block must be homogeneous in `inductive` members.
        // Anything else — a `def`/`theorem` mixed in, or a `coinductive` (whose
        // greatest-fixpoint semantics are not handled on this path) — is outside
        // the supported envelope: fail closed rather than silently dropping it.
        for decl in decls {
            if !matches!(decl, SurfaceDecl::Inductive { .. }) {
                return Err(ElabError::Unsupported {
                    feature: "mutual block mixing `inductive` with other declaration kinds"
                        .to_string(),
                });
            }
        }

        // ── Pass 1: elaborate type heads and push forward locals ──
        let mut entries: Vec<MutualIndEntry> = Vec::with_capacity(decls.len());
        for decl in decls {
            let SurfaceDecl::Inductive {
                name,
                universe_params,
                binders,
                ty,
                ..
            } = decl
            else {
                continue;
            };

            // Deferred (fail-closed) features: parameters and universe params.
            if !binders.is_empty() {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "parameters on mutual inductive '{name}' (parameterised mutual \
                         inductives not yet supported)"
                    ),
                });
            }
            if !universe_params.is_empty() {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "universe parameters on mutual inductive '{name}' (universe-polymorphic \
                         mutual inductives not yet supported)"
                    ),
                });
            }

            let ind_ty = self.elaborate(ty)?;
            let ind_ty = self.metas.instantiate(&ind_ty);
            let ind_ty = self.metas.instantiate_levels(&ind_ty);

            let qname = Name::from_string(&self.qualify_name(name));
            // Push under the SHORT name so sibling constructor types can refer to
            // the type by its unqualified spelling (as written in surface syntax).
            let short = name.rsplit('.').next().unwrap_or(name).to_string();
            let fvar = self.push_local(short, ind_ty.clone());
            entries.push(MutualIndEntry {
                name: qname,
                fvar,
                ind_ty,
            });
        }

        // ── Pass 2: elaborate constructors with all heads in scope ──
        let mut types: Vec<InductiveType> = Vec::with_capacity(entries.len());
        let mut entry_idx = 0;
        for decl in decls {
            let SurfaceDecl::Inductive { name: _, ctors, .. } = decl else {
                continue;
            };

            let entry_name = entries[entry_idx].name.clone();

            let mut constructors: Vec<Constructor> = Vec::with_capacity(ctors.len());
            for ctor in ctors {
                let ctor_name = Name::from_string(&format!("{entry_name}.{}", ctor.name));
                let ctor_ty = self.elaborate(&ctor.ty)?;
                let mut ctor_ty = self.metas.instantiate(&ctor_ty);
                ctor_ty = self.metas.instantiate_levels(&ctor_ty);
                // Replace every forward type-head fvar with a `Const` reference so
                // the registered constructor types are closed (no locals).
                ctor_ty = self.replace_mutual_ind_fvars(&entries, ctor_ty);
                constructors.push(Constructor {
                    name: ctor_name,
                    type_: ctor_ty,
                });
            }

            let entry = &entries[entry_idx];
            types.push(InductiveType {
                name: entry.name.clone(),
                type_: entry.ind_ty.clone(),
                constructors,
            });
            entry_idx += 1;
        }

        // ── cleanup: pop all forward type-head locals (LIFO order) ──
        for _ in &entries {
            self.pop_local();
        }

        let decl = InductiveDecl {
            level_params: Vec::new(),
            num_params: 0,
            types,
        };

        Ok(ElabResult::MutualInductive {
            decl,
            derived_instances: Vec::new(),
            modifiers: clean_parser::DeclModifiers::default(),
        })
    }

    /// Replace every forward inductive type-head fvar in `expr` with a `Const`
    /// reference to the corresponding family type.
    fn replace_mutual_ind_fvars(&self, entries: &[MutualIndEntry], expr: Expr) -> Expr {
        struct IndFvarFolder<'b> {
            entries: &'b [MutualIndEntry],
        }
        impl ExprFolder for IndFvarFolder<'_> {
            fn fold_fvar(&mut self, id: FVarId) -> Expr {
                for entry in self.entries {
                    if id == entry.fvar {
                        return Expr::const_(entry.name.clone(), Vec::new());
                    }
                }
                Expr::fvar(id)
            }
        }
        let mut folder = IndFvarFolder { entries };
        folder.fold_expr(&expr)
    }

    /// Elaborate binders into a Pi type wrapping `body_ty`.
    ///
    /// Used when a `def` inside a mutual block has no explicit return type
    /// annotation. The binders are processed into Pi abstractions around a
    /// fresh metavariable that the body elaboration will constrain.
    fn elab_binders_as_pi(
        &mut self,
        binders: &[clean_parser::SurfaceBinder],
        body_ty: Expr,
    ) -> Result<Expr, ElabError> {
        use super::convert_binder_info;
        use clean_kernel::BinderInfo;

        if binders.is_empty() {
            return Ok(body_ty);
        }

        let binder = &binders[0];
        let binder_ty = if let Some(ty) = &binder.ty {
            let elaborated = self.elaborate(ty)?;
            let instantiated = self.metas.instantiate(&elaborated);
            self.metas.instantiate_levels(&instantiated)
        } else {
            let binder_sort = Expr::sort(self.fresh_universe_param());
            self.fresh_meta(binder_sort)
        };

        let bi = convert_binder_info(binder.info);
        let fvar = self.push_local(binder.name.clone(), binder_ty.clone());

        let is_inst_implicit = bi == BinderInfo::InstImplicit;
        if is_inst_implicit {
            self.push_local_instance(fvar, binder_ty.clone());
        }

        let inner_ty = self.elab_binders_as_pi(&binders[1..], body_ty)?;

        if is_inst_implicit {
            self.pop_local_instance();
        }
        self.pop_local();

        let inner_abs = inner_ty.abstract_fvar(fvar);
        Ok(Expr::pi(bi, binder_ty, inner_abs))
    }

    /// Replace all forward-declaration fvars in `expr` with `Const` references
    /// to the corresponding mutual declarations.
    fn replace_mutual_fvars(&self, entries: &[MutualEntry], expr: Expr) -> Expr {
        struct MutualFvarFolder<'b> {
            entries: &'b [MutualEntry],
        }

        impl ExprFolder for MutualFvarFolder<'_> {
            fn fold_fvar(&mut self, id: FVarId) -> Expr {
                for entry in self.entries {
                    if id == entry.fvar {
                        let levels: Vec<Level> = entry
                            .universe_params
                            .iter()
                            .map(|n| Level::param(n.clone()))
                            .collect();
                        return Expr::const_(entry.name.clone(), levels);
                    }
                }
                Expr::fvar(id)
            }
        }

        let mut folder = MutualFvarFolder { entries };
        folder.fold_expr(&expr)
    }
}

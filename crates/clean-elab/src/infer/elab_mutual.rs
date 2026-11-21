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

use super::mutual_lift::PreDef;
use super::{ElabCtx, ElabResult};

/// Pass 2's output: each member's pre-definition, whether it is a theorem
/// with its modifiers, and how many auto-bound implicits its signature took
/// (`check_mutual_measure_types`).
type MutualPredefs = (
    Vec<PreDef>,
    Vec<(bool, clean_parser::DeclModifiers)>,
    Vec<usize>,
);

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

        // MUTUAL COINDUCTIVE PREDICATES ARE A FUTURE RUNG — refuse loudly.
        // Measured before this guard existed: a `mutual … end` holding
        // `coinductive` members was silently ACCEPTED and registered NOTHING
        // (the members fell through the def-shaped paths below), so the
        // whole family vanished and every downstream use failed with an
        // unrelated auto-bound artifact. Same treatment for the Type-level
        // codata/codef lanes, whose single-decl arms already refuse; a
        // mutual wrapper must not become a silent bypass.
        if let Some(member) = decls.iter().find(|d| {
            matches!(
                d,
                SurfaceDecl::Coinductive { .. }
                    | SurfaceDecl::Codata { .. }
                    | SurfaceDecl::Codef { .. }
            )
        }) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "a `mutual` block containing `{}` is not supported yet:                      mutual coinductive predicates are a planned rung of the                      full-gfp program (designs/2026-08-25-rank1-full-gfp-                     lowering.md, non-goals) — declare the family as a single                      `coinductive` over a sum/tagged index for now",
                    match member {
                        SurfaceDecl::Coinductive { .. } => "coinductive",
                        SurfaceDecl::Codata { .. } => "codata",
                        _ => "codef",
                    }
                ),
            });
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
                    modifiers,
                    ..
                } => {
                    self.set_decl_universe_params(universe_params);

                    let ty_expr = if let Some(ty_surface) = ty {
                        self.elab_def_header(binders, ty_surface)?.0
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

                    let decl_name = self.kernel_decl_name(
                        name,
                        modifiers,
                        super::elaborate_decl::PrivateNameKind::Definition,
                    );
                    let univ_names: Vec<Name> = self
                        .universe_params
                        .iter()
                        .map(|s| s.name().clone())
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
                    modifiers,
                    ..
                } => {
                    self.set_decl_universe_params(universe_params);

                    let ty_expr = self.elab_def_header(binders, ty)?.0;
                    let ty_expr = self.metas.instantiate(&ty_expr);
                    let ty_expr = self.metas.instantiate_levels(&ty_expr);

                    let decl_name = self.kernel_decl_name(
                        name,
                        modifiers,
                        super::elaborate_decl::PrivateNameKind::Theorem,
                    );
                    let univ_names: Vec<Name> = self
                        .universe_params
                        .iter()
                        .map(|s| s.name().clone())
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
        //
        // Each member's PRE-DEFINITION: its type and value with every member
        // (itself included) still a forward local.

        // The members are Lean's auxiliary declarations while their bodies
        // elaborate (`LocalDecl.isAuxDecl`): names resolve to them, but no
        // tactic that enumerates hypotheses sees them (brick B6 of
        // designs/2026-10-08-mutual-nested-recursion.md; `elab_tactic`'s
        // bridge leaves them out of a goal's visible context).
        for entry in &entries {
            self.aux_decl_locals.insert(entry.fvar);
        }
        let pass2 = self.elab_mutual_predefs(decls, &entries);
        for entry in &entries {
            self.aux_decl_locals.remove(&entry.fvar);
        }
        let (predefs, kinds, auto_implicit_counts) = pass2?;

        // Lean refuses well-founded measures of different types before any
        // lowering (`elab_mutual_measures`); the structural lift below never
        // reads a measure.
        if let Err(err) = self.check_mutual_measure_types(decls, &predefs, &auto_implicit_counts) {
            for _ in &entries {
                self.pop_local();
            }
            return Err(err);
        }

        // Strongly connected components in dependency order; a recursive one
        // is lifted onto its family's shared recursor (gap G23), the others
        // only have their forward locals replaced by the member constants.
        let lowered = self.lower_mutual_predefs(&predefs);
        let lowered = match lowered {
            Ok(lowered) => lowered,
            Err(err) => {
                for _ in &entries {
                    self.pop_local();
                }
                return Err(err);
            }
        };
        // Named equation lemmas of the lifted definition members, with the
        // forward locals still in scope (registered after the members).
        {
            let lifted: Vec<Name> = self
                .mutual_lift_entries
                .iter()
                .map(|entry| entry.member.clone())
                .collect();
            if !lifted.is_empty() {
                let mut final_defs = predefs.clone();
                for member in &lowered {
                    final_defs[member.index].universe_params = member.universe_params.clone();
                }
                self.queue_arm_equations(decls, &final_defs, &lifted);
            }
        }
        let mut results: Vec<ElabResult> = Vec::with_capacity(lowered.len());
        for member in lowered {
            let entry = &entries[member.index];
            let (is_theorem, modifiers) = kinds[member.index].clone();
            results.push(if is_theorem {
                ElabResult::Theorem {
                    name: entry.name.clone(),
                    universe_params: member.universe_params,
                    ty: member.ty,
                    proof: member.val,
                    modifiers,
                }
            } else {
                ElabResult::Definition {
                    name: entry.name.clone(),
                    universe_params: member.universe_params,
                    ty: member.ty,
                    val: member.val,
                    modifiers,
                }
            });
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
        // Auto-implicits are captured PER CONSTRUCTOR inside, but a `?`-return
        // from anywhere in the block would leave a partial packet behind. An
        // auto-implicit that survives the declaration that created it is also
        // pushed onto `self.locals`, so it would silently resolve a bare
        // identifier in the NEXT declaration. Drain unconditionally.
        let block_auto_start = self.auto_implicit_count();
        let result = self.elab_mutual_inductive_inner(decls);
        if self.auto_implicit_count() > block_auto_start {
            let _ = self.take_auto_implicits_since(block_auto_start);
        }
        result
    }

    fn elab_mutual_inductive_inner(
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
        let mut inferred_results = Vec::new();
        for decl in decls {
            let SurfaceDecl::Inductive {
                name,
                universe_params,
                binders,
                ty,
                modifiers,
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

            // Auto-implicits raised while elaborating the TYPE HEAD are a
            // different animal from constructor-level ones: Lean binds them as
            // implicit INDICES on the head itself (`inductive HA : α → Type 1`
            // registers `HA : {α : Type} → α → Type 1`, `number of parameters:
            // 0`) and every self-reference in every constructor must then
            // supply one. Threading that needs the single-inductive path's
            // header-meta machinery (`assign_header_metas` + ctor-local meta
            // promotion), which is not ported here. Refuse in the open, rather
            // than registering a head with a free variable in it and letting
            // the kernel report an fvar id.
            let head_auto_start = self.auto_implicit_count();
            let ind_ty = if matches!(ty.as_ref(), clean_parser::SurfaceExpr::Hole(_)) {
                let level = Level::succ(self.fresh_universe_param());
                inferred_results.push(level.clone());
                Expr::sort(level)
            } else {
                self.elaborate(ty)?
            };
            let head_auto_implicits = self.take_auto_implicits_since(head_auto_start);
            if !head_auto_implicits.is_empty() {
                let names: Vec<String> = head_auto_implicits
                    .iter()
                    .map(|(n, _, _)| n.source_spelling().unwrap_or_else(|| n.to_string()))
                    .collect();
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "auto-bound implicit(s) `{}` in the TYPE HEAD of mutual inductive \
                         '{name}' (Lean binds these as implicit indices on the head; the \
                         mutual path does not thread them yet — constructor-level \
                         auto-implicits ARE supported)",
                        names.join("`, `")
                    ),
                });
            }
            let ind_ty = self.metas.instantiate(&ind_ty);
            let ind_ty = self.metas.instantiate_levels(&ind_ty);

            // A `private` member is `_private.<module>.0.<name>` (G21 B3).
            let qname = self.family_decl_name(name, modifiers).into_name();
            // Push under the SHORT name so sibling constructor types can refer to
            // the type by its unqualified spelling (as written in surface syntax).
            let short = name.last_component();
            let fvar = self.push_local(short, ind_ty.clone());
            entries.push(MutualIndEntry {
                name: qname,
                fvar,
                ind_ty,
            });
        }

        // ── Pass 2: elaborate constructors with all heads in scope ──
        let mut types: Vec<InductiveType> = Vec::with_capacity(entries.len());
        let mut raw_ctor_types = Vec::new();
        let mut entry_idx = 0;
        for decl in decls {
            let SurfaceDecl::Inductive { name: _, ctors, .. } = decl else {
                continue;
            };

            let entry_name = entries[entry_idx].name.clone();

            let mut constructors: Vec<Constructor> = Vec::with_capacity(ctors.len());
            for ctor in ctors {
                let ctor_name = crate::namespace::append_names(&entry_name, ctor.name.name());

                // Bracket this constructor's elaboration and bind whatever it
                // auto-bound as its OWN implicit arguments — the single-inductive
                // path's `ctor_auto_implicit_start` / `take_auto_implicits_since`
                // pairing. Without it `| cons : Lift t y -> Env [t]` registers a
                // type still mentioning the `t`/`y` fvars and the kernel refuses
                // the family for containing free variables.
                //
                // The bracket is per CONSTRUCTOR, not per block: draining at
                // `take_auto_implicits_since` also removes the fvars from
                // `self.locals`, so a sibling's `| two : L2 s` cannot capture the
                // earlier `| one : L1 t`'s `t`, and vice versa.
                let ctor_auto_start = self.auto_implicit_count();
                let ctor_ty = self.elaborate(&ctor.ty)?;
                let ctor_auto_implicits = self.take_auto_implicits_since(ctor_auto_start);

                let mut ctor_ty = self.metas.instantiate(&ctor_ty);
                ctor_ty = self.metas.instantiate_levels(&ctor_ty);

                // Bind in creation order, as implicit Pi binders — matching
                // Lean's `Env.cons : {t : Bool} → {y : Type} → Lift t y → Env [t]`.
                ctor_ty = Self::wrap_type_with_auto_implicits(ctor_ty, &ctor_auto_implicits);

                // Keep the fvar-bearing form until every constructor has been
                // elaborated. Container applications can union their fresh
                // universe with a result hole; the final equivalence classes,
                // not the names minted before pass 2, decide whether a field is
                // recursive and therefore excluded from the lower bound.
                raw_ctor_types.push(ctor_ty.clone());

                // Replacement with recursive `Const`s waits until declaration
                // close, when the shared universe argument list is known. Keep
                // the wrapped form so a sibling reference inside an
                // auto-implicit's own TYPE is replaced along with one in the
                // constructor body.
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

        // Recursive field sorts contain the result holes themselves; they
        // impose no additional lower bound. Constructor elaboration may have
        // unioned those holes with fresh levels from `List`, `Prod`, or another
        // container, so canonicalize the ignored classes only after pass 2.
        let mut ignored = Vec::new();
        for level in &inferred_results {
            self.metas
                .instantiate_level(level)
                .collect_params(&mut ignored);
        }
        let mut inferred_bound = Level::succ(Level::zero());
        for ctor_ty in &raw_ctor_types {
            inferred_bound = Level::max(
                inferred_bound,
                self.constructor_universe_bound(ctor_ty, &ignored),
            );
        }
        let inferred_bound = inferred_bound.normalize();
        for level in &inferred_results {
            match crate::unify::level_solve::solve_level_eq(&mut self.metas, level, &inferred_bound)
            {
                crate::unify::UnifyResult::Success => {}
                crate::unify::UnifyResult::Failure(message) => {
                    return Err(ElabError::Unsupported {
                        feature: format!(
                            "mutual inductive result-universe inference failed: {message}"
                        ),
                    });
                }
                crate::unify::UnifyResult::Stuck => return Err(ElabError::CannotInfer),
            }
        }
        self.resolve_self_max_level_equations();
        if let Err(message) = self.metas.drain_postponed_levels() {
            return Err(ElabError::Unsupported { feature: message });
        }

        // A metavariable created while elaborating an EARLIER constructor can be
        // solved by a LATER sibling's constructor (the family shares one meta
        // store), so re-instantiate the whole family once at the end. Without
        // this the first constructor keeps the pre-solution form and the second
        // the post-solution one, and the kernel sees two spellings of the same
        // type. Idempotent when nothing moved.
        let mut types: Vec<InductiveType> = types
            .into_iter()
            .map(|ind| InductiveType {
                name: ind.name,
                type_: self
                    .metas
                    .canonicalize_levels_in_expr(&self.metas.instantiate(&ind.type_)),
                constructors: ind
                    .constructors
                    .into_iter()
                    .map(|ctor| {
                        let ty = self.metas.instantiate(&ctor.type_);
                        let ty = self.metas.canonicalize_levels_in_expr(&ty);
                        Constructor {
                            name: ctor.name,
                            type_: ty,
                        }
                    })
                    .collect(),
            })
            .collect();

        // Every rigid level that survives declaration close is part of the
        // shared mutual-inductive interface, and the same ordered list must be
        // supplied to every recursive Const. A minted metavariable left here
        // is not a parameter: Lean refuses a constructor-only hole rather than
        // exporting it (for example `| mk : Baz -> Foo`, where relaxed auto
        // implicit elaboration gives `Baz : Sort ?u`).
        let mut raw_level_params = Vec::new();
        for ind in &types {
            crate::level_params::collect_level_params_from_expr(&ind.type_, &mut raw_level_params);
            for ctor in &ind.constructors {
                crate::level_params::collect_level_params_from_expr(
                    &ctor.type_,
                    &mut raw_level_params,
                );
            }
        }
        if let Some(param) = raw_level_params
            .iter()
            .find(|param| !self.metas.is_rigid_level_param(param))
        {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "mutual inductive contains unresolved universe level metavariable `{param}`"
                ),
            });
        }
        let level_params = raw_level_params;

        let recursive_levels: Vec<Level> = level_params.iter().cloned().map(Level::param).collect();
        types = types
            .into_iter()
            .map(|ind| InductiveType {
                name: ind.name,
                type_: ind.type_,
                constructors: ind
                    .constructors
                    .into_iter()
                    .map(|ctor| Constructor {
                        name: ctor.name,
                        type_: self.replace_mutual_ind_fvars(
                            &entries,
                            ctor.type_,
                            &recursive_levels,
                        ),
                    })
                    .collect(),
            })
            .collect();

        // ── cleanup: pop all forward type-head locals (LIFO order) ──
        for _ in &entries {
            self.pop_local();
        }

        let decl = InductiveDecl {
            level_params,
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
    fn replace_mutual_ind_fvars(
        &self,
        entries: &[MutualIndEntry],
        expr: Expr,
        levels: &[Level],
    ) -> Expr {
        struct IndFvarFolder<'b> {
            entries: &'b [MutualIndEntry],
            levels: &'b [Level],
        }
        impl ExprFolder for IndFvarFolder<'_> {
            fn fold_fvar(&mut self, id: FVarId) -> Expr {
                for entry in self.entries {
                    if id == entry.fvar {
                        return Expr::const_(entry.name.clone(), self.levels.to_vec());
                    }
                }
                Expr::fvar(id)
            }
        }
        let mut folder = IndFvarFolder { entries, levels };
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

        // Any local whose type is a class is a local instance (Lean's rule;
        // see `binder_is_local_instance`), not only the `[…]` spelling.
        let is_inst_implicit = self.binder_is_local_instance(bi, &binder_ty);
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
}

impl ElabCtx<'_> {
    /// Pass 2 of [`Self::elab_mutual`]: each member's PRE-DEFINITION, its
    /// type and value with every member (itself included) still a forward
    /// local, and its kind.
    fn elab_mutual_predefs(
        &mut self,
        decls: &[SurfaceDecl],
        entries: &[MutualEntry],
    ) -> Result<MutualPredefs, ElabError> {
        let mut predefs: Vec<PreDef> = Vec::with_capacity(entries.len());
        let mut auto_implicit_counts: Vec<usize> = Vec::with_capacity(entries.len());
        let mut kinds: Vec<(bool, clean_parser::DeclModifiers)> = Vec::with_capacity(entries.len());
        let mut entry_idx = 0;

        for decl in decls {
            let (universe_params, binders, ty, val, attrs, modifiers, is_theorem) = match decl {
                SurfaceDecl::Def {
                    universe_params,
                    binders,
                    ty,
                    val,
                    attrs,
                    modifiers,
                    ..
                } => (
                    universe_params,
                    binders,
                    ty.as_deref(),
                    val,
                    attrs,
                    modifiers,
                    false,
                ),
                SurfaceDecl::Theorem {
                    universe_params,
                    binders,
                    ty,
                    proof,
                    attrs,
                    modifiers,
                    ..
                } => (
                    universe_params,
                    binders,
                    Some(&**ty),
                    proof,
                    attrs,
                    modifiers,
                    true,
                ),
                _ => continue,
            };
            let entry = &entries[entry_idx];
            self.set_decl_universe_params(universe_params);

            let (ty_expr, val_expr, _) = self.elab_decl_body(binders, ty, val)?;

            let ty_expr = self.metas.instantiate(&ty_expr);
            let val_expr = self.metas.instantiate(&val_expr);
            let ty_expr = self.metas.instantiate_levels(&ty_expr);
            let val_expr = self.metas.instantiate_levels(&val_expr);

            let auto_implicits = self.take_auto_implicits();
            auto_implicit_counts.push(auto_implicits.len());
            let (ty_expr, val_expr) =
                Self::wrap_with_auto_implicits(ty_expr, val_expr, &auto_implicits);

            if std::env::var_os("CLEAN_MUTUAL_LIFT_TRACE").is_some() {
                eprintln!("mutual-predef: {} : {ty_expr}\n  := {val_expr}", entry.name);
            }

            self.ensure_known_attributes(attrs)?;
            // Lean applies a member's attributes before it adds the members
            // after it: an `@[implemented_by]` naming one is "Unknown
            // constant".
            let later: Vec<Name> = entries[entry_idx + 1..]
                .iter()
                .map(|later| later.name.clone())
                .collect();
            self.collect_attributes_at(
                &entry.name,
                attrs,
                crate::declared_here::AttributeSite::Declaration,
                &later,
            );

            let termination = match decl {
                SurfaceDecl::Def { termination, .. } | SurfaceDecl::Theorem { termination, .. } => {
                    termination
                }
                _ => {
                    return Err(ElabError::InternalInvariant(
                        "non-definition reached mutual predefinitions".into(),
                    ))
                }
            };
            let mut total = 0usize;
            let mut cursor = &ty_expr;
            while let clean_kernel::ExprKind::Pi(_, _, body) = cursor.kind() {
                total += 1;
                cursor = body;
            }
            let autos = auto_implicits.len();
            let structural_major = termination
                .termination_by
                .as_ref()
                .map(|tb| Self::structural_hint_index(tb, binders, total.saturating_sub(autos)))
                .transpose()
                .map_err(|feature| ElabError::Unsupported { feature })?
                .flatten()
                .map(|i| autos + i);
            predefs.push(PreDef {
                name: entry.name.clone(),
                fvar: entry.fvar,
                is_theorem,
                universe_params: entry.universe_params.clone(),
                ty: ty_expr,
                val: val_expr,
                structural_major,
            });
            kinds.push((is_theorem, modifiers.clone()));
            entry_idx += 1;
        }
        Ok((predefs, kinds, auto_implicit_counts))
    }
}

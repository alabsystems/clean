// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ElabCtx internal context management utilities.
//!
//! Provides the core operations for managing the elaboration context:
//! - Local variable binding (push/pop/lookup)
//! - Fresh variable and metavariable creation
//! - Local context construction for type checking
//! - Free variable replacement (for inductive type elaboration)

use super::*;
use clean_kernel::ExprFolder;

/// State whose lifetime is tied to the active local-variable scope.
///
/// Nested-pattern elaboration is deliberately two-phase: binding a plan pushes
/// locals and applying it later pops those locals while constructing lambdas.
/// Either phase can fail after changing only part of that stack.  A length-only
/// checkpoint cannot recover from the apply direction because already-popped
/// entries (including let values and local instances) have been destroyed.
/// Keep an exact, cheap-to-clone snapshot of the scope-coupled state instead.
#[derive(Clone)]
struct LocalScopeSnapshot {
    locals: Vec<(String, FVarId, Expr)>,
    local_let_values: HashMap<FVarId, Expr>,
    shared_if_let_scrutinees: Vec<String>,
    local_instances: Vec<(FVarId, Expr)>,
    instance_cache: HashMap<String, Expr>,
    current_expected_type: Option<Expr>,
    recursive_def_ctx: Option<RecursiveDefContext>,
    match_dependent_motive: Option<Expr>,
    match_dependent_motive_indices: usize,
    match_index_discriminating_punit: Option<Level>,
    universe_params: Vec<String>,
    /// Moves WITH `universe_params`: auto-binding grows the rigid set during
    /// elaboration, so a failed term that minted `u` must not leave it rigid.
    rigid_level_params: std::collections::HashSet<Name>,
    pending_level_assigns: Vec<(Name, Level)>,
    hole_names: HashMap<MetaId, String>,
}

impl<'a> ElabCtx<'a> {
    fn local_scope_snapshot(&self) -> LocalScopeSnapshot {
        LocalScopeSnapshot {
            locals: self.locals.clone(),
            local_let_values: self.local_let_values.clone(),
            shared_if_let_scrutinees: self.shared_if_let_scrutinees.clone(),
            local_instances: self.local_instances.clone(),
            instance_cache: self.instance_cache.clone(),
            current_expected_type: self.current_expected_type.clone(),
            recursive_def_ctx: self.recursive_def_ctx.clone(),
            match_dependent_motive: self.match_dependent_motive.clone(),
            match_dependent_motive_indices: self.match_dependent_motive_indices,
            match_index_discriminating_punit: self.match_index_discriminating_punit.clone(),
            universe_params: self.universe_params.clone(),
            rigid_level_params: self.metas.rigid_level_params_snapshot(),
            pending_level_assigns: self.pending_level_assigns.borrow().clone(),
            hole_names: self.hole_names.clone(),
        }
    }

    fn restore_local_scope(&mut self, snapshot: LocalScopeSnapshot, restore_failed_state: bool) {
        self.locals = snapshot.locals;
        self.local_let_values = snapshot.local_let_values;
        self.shared_if_let_scrutinees = snapshot.shared_if_let_scrutinees;
        self.local_instances = snapshot.local_instances;
        self.instance_cache = snapshot.instance_cache;
        self.current_expected_type = snapshot.current_expected_type;
        self.recursive_def_ctx = snapshot.recursive_def_ctx;
        self.match_dependent_motive = snapshot.match_dependent_motive;
        self.match_dependent_motive_indices = snapshot.match_dependent_motive_indices;
        self.match_index_discriminating_punit = snapshot.match_index_discriminating_punit;
        if restore_failed_state {
            // A failed term may have minted declaration-level universe params or
            // left level-equality callback assignments buffered.  The monotone
            // fresh-universe counter intentionally is not rewound, but the
            // declaration's ordered parameter packet and pending assignments
            // must be exactly the entry state.
            self.universe_params = snapshot.universe_params;
            self.metas
                .restore_rigid_level_params(snapshot.rigid_level_params);
            self.pending_level_assigns
                .replace(snapshot.pending_level_assigns);
            self.hole_names = snapshot.hole_names;
        }

        // TypeChecker caches are authoritative only for the exact local/meta
        // context in which they were computed.  Every caller of this helper has
        // restored an earlier local context: failed transactional work also
        // rolls metas back, while a successful temporary scope removes locals
        // that may occur in cached WHNF/def-eq results.  TcCaches is
        // intentionally non-Clone, so invalidate it instead of attempting a
        // partial restore.  Successful `with_local_scope_rollback` work does
        // not call this helper because its scope remains active.
        self.tc_caches.replace(TcCaches::default());
    }

    fn finish_meta_scope(
        &mut self,
        token: OwnedMetaScopeToken,
        rollback: bool,
        scope_name: &'static str,
    ) -> Result<(), ElabError> {
        match self.metas.close_owned_scope(token, rollback) {
            Ok(()) => Ok(()),
            Err(OwnedMetaScopeCloseError::AccessAttempted) => {
                Err(ElabError::InternalInvariant(format!(
                    "nested work attempted to consume its enclosing {scope_name} metavariable marker"
                )))
            }
            Err(OwnedMetaScopeCloseError::Missing) => Err(ElabError::InternalInvariant(format!(
                "{scope_name} metavariable marker disappeared while closing the scope"
            ))),
            Err(OwnedMetaScopeCloseError::Obstructed) => {
                Err(ElabError::InternalInvariant(format!(
                    "nested work left an owned metavariable scope above its enclosing {scope_name} marker"
                )))
            }
        }
    }

    /// Run fallible work transactionally with respect to local-scope state.
    /// Successful work keeps its pushed/popped locals; an error restores the
    /// exact entry context and rolls back metavariable assignments/creation.
    pub(super) fn with_local_scope_rollback<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, ElabError>,
    ) -> Result<T, ElabError> {
        let snapshot = self.local_scope_snapshot();
        let meta_scope = self.metas.push_owned_scope();
        let result = f(self);
        let rollback = result.is_err();
        if let Err(scope_error) = self.finish_meta_scope(meta_scope, rollback, "local-scope") {
            self.restore_local_scope(snapshot, true);
            return Err(scope_error);
        }

        match result {
            Ok(value) => {
                // A successful transaction commits metavariable and universe-
                // level assignments even when its local context is byte-for-byte
                // unchanged. Cached WHNF/def-equality results computed before
                // those assignments are no longer authoritative (pending level
                // callback assignments are especially easy to miss by comparing
                // locals alone). Until MetaState exposes a revision key, clear
                // all TypeChecker caches at every successful commit.
                self.tc_caches.replace(TcCaches::default());
                // Resolution entries are currently restricted to ground goals,
                // but a successful transaction may also commit a different
                // local-instance context. Conservatively invalidate this cache
                // at the same authority boundary.
                self.instance_cache.clear();
                Ok(value)
            }
            Err(err) => {
                self.restore_local_scope(snapshot, true);
                Err(err)
            }
        }
    }

    /// Run work in a temporary local scope.  Local bindings, expected-type and
    /// recursive-IH state are restored on both success and failure.  Successful
    /// metavariable work is committed because it may occur in the returned
    /// expression; failed work is rolled back with the rest of the context.
    pub(super) fn with_temporary_local_scope<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, ElabError>,
    ) -> Result<T, ElabError> {
        let snapshot = self.local_scope_snapshot();
        let meta_scope = self.metas.push_owned_scope();
        let result = f(self);
        let restore_holes = result.is_err();
        if let Err(scope_error) =
            self.finish_meta_scope(meta_scope, restore_holes, "temporary-scope")
        {
            self.restore_local_scope(snapshot, true);
            return Err(scope_error);
        }
        self.restore_local_scope(snapshot, restore_holes);
        if !restore_holes {
            // Successful temporary work commits meta/level assignments. The
            // entry instance-cache snapshot is therefore not authoritative even
            // though all locals are restored; match the successful transaction
            // boundary above and rebuild instance results on demand.
            self.instance_cache.clear();
        }
        result
    }

    /// Run an optional probe in a temporary scope. `Ok(Some(_))` commits its
    /// metavariable work, while both `Ok(None)` (the probe declined/fell back)
    /// and `Err(_)` roll back every local/meta/level side effect. This is the
    /// correct boundary for speculative match-compilation lanes whose `None`
    /// result is intentionally ignored by the caller.
    pub(super) fn with_optional_temporary_local_scope<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<Option<T>, ElabError>,
    ) -> Result<Option<T>, ElabError> {
        let snapshot = self.local_scope_snapshot();
        let meta_scope = self.metas.push_owned_scope();
        let result = f(self);
        let rollback = !matches!(&result, Ok(Some(_)));
        if let Err(scope_error) =
            self.finish_meta_scope(meta_scope, rollback, "optional-temporary-scope")
        {
            self.restore_local_scope(snapshot, true);
            return Err(scope_error);
        }
        self.restore_local_scope(snapshot, rollback);
        if !rollback {
            self.instance_cache.clear();
        }
        result
    }

    /// Get the metavariable state
    pub fn metas(&self) -> &MetaState {
        &self.metas
    }

    /// Create a fresh free variable
    pub(crate) fn fresh_fvar(&mut self) -> FVarId {
        let id = FVarId::new(self.next_fvar);
        self.next_fvar += 1;
        id
    }

    /// Create a fresh metavariable
    pub fn fresh_meta(&mut self, ty: Expr) -> Expr {
        let id = self.metas.fresh_with_locals(ty, self.locals.clone());
        Expr::fvar(MetaState::to_fvar(id))
    }

    /// Create a fresh metavariable tagged with the source span of the surface
    /// hole that produced it.
    ///
    /// Behaves exactly like [`fresh_meta`] but records `span` on the underlying
    /// metavariable so IDE surfaces can map it back to the hole the user wrote.
    /// The span is informational only and never affects elaboration.
    pub fn fresh_meta_at(&mut self, ty: Expr, span: clean_parser::Span) -> Expr {
        let id = self
            .metas
            .fresh_with_locals_at(ty, self.locals.clone(), Some(span));
        Expr::fvar(MetaState::to_fvar(id))
    }

    /// Elaborate a surface hole (`_`, `?`, `?_`, or `?name`) to a fresh
    /// metavariable.
    ///
    /// Creates a fresh type metavariable and a value metavariable tagged with
    /// `span`, exactly as the anonymous-hole path always has. When `name` is
    /// `Some` (a `?name` synthetic hole), the value metavariable's id is
    /// recorded in `hole_names` so `refine` can later tag the goal produced for
    /// that hole with `name` (enabling `case name => …`). A named hole is
    /// otherwise elaborated identically to an anonymous one — the recorded name
    /// never affects unification, def-eq, or the produced term.
    pub(crate) fn elab_hole(&mut self, span: clean_parser::Span, name: Option<&str>) -> Expr {
        let ty_meta = self.fresh_meta(Expr::type_());
        let meta_id = self
            .metas
            .fresh_with_locals_at(ty_meta, self.locals.clone(), Some(span));
        if let Some(name) = name {
            self.hole_names.insert(meta_id, name.to_string());
        }
        Expr::fvar(MetaState::to_fvar(meta_id))
    }

    /// Snapshot the hole contexts recorded during elaboration.
    ///
    /// Iterates the metavariables created for user-written holes (`_`), i.e.
    /// those tagged with a source span (see [`MetaVar::span`]), and emits a
    /// [`HoleContext`] for each. The expected type and any captured local
    /// bindings are instantiated with the final metavariable assignments so
    /// solved parts are resolved; unsolved parts are reported as-is (that is the
    /// expected type to show at the hole).
    ///
    /// Results are sorted by metavariable id (creation order) for stable,
    /// deterministic output. This is read-only and has no effect on the kernel.
    ///
    /// [`MetaVar::span`]: crate::unify::MetaVar::span
    pub fn collect_hole_contexts(&self) -> Vec<HoleContext> {
        let mut holes: Vec<(u64, HoleContext)> = self
            .metas
            .iter()
            .filter_map(|(id, meta)| {
                let span = meta.span?;
                let expected_type = self.metas.instantiate(&meta.ty);
                let local_bindings = meta
                    .locals
                    .iter()
                    .map(|(name, _fvar, ty)| (name.clone(), self.metas.instantiate(ty)))
                    .collect();
                Some((
                    id.as_u64(),
                    HoleContext {
                        span,
                        expected_type,
                        local_bindings,
                    },
                ))
            })
            .collect();
        holes.sort_by_key(|(id, _)| *id);
        holes.into_iter().map(|(_, hole)| hole).collect()
    }

    /// Build `Expr::const_(name, levels)` with fresh universe params for each
    /// of the constant's declared level parameters.
    ///
    /// This is the correct way to reference a universe-polymorphic constant in
    /// the elaborator. Calling `Expr::const_(name, vec![])` for a constant that
    /// has universe parameters produces kernel-invalid terms (#1828, #1799).
    ///
    /// If the constant is not in the environment (e.g., forward reference
    /// during recursive definition elaboration), falls back to `vec![]`.
    /// This fallback is only correct for constants that genuinely have no
    /// universe parameters — callers referencing a universe-polymorphic
    /// constant not yet in the environment should supply levels explicitly.
    pub(crate) fn mk_const(&mut self, name: &Name) -> Expr {
        if let Some(info) = self.env.get_const(name) {
            let levels: Vec<Level> = info
                .level_params
                .iter()
                .map(|_| self.fresh_universe_param())
                .collect();
            Expr::const_(name.clone(), levels)
        } else {
            Expr::const_(name.clone(), vec![])
        }
    }

    /// Build `Expr::const_(name, levels)` for a constant looked up by string name.
    ///
    /// Convenience wrapper around `mk_const` that accepts `&str`.
    pub(crate) fn mk_const_str(&mut self, name: &str) -> Expr {
        self.mk_const(&Name::from_string(name))
    }

    /// Enter a declaration's universe scope.
    ///
    /// Installs the declaration's explicitly-declared universe parameters (from
    /// `def f.{u,v}`) as BOTH the active `universe_params` and the RIGID
    /// (never-unify-assigned) level set. Unification then treats each declared
    /// `u` as a fixed `Level.param`, not a metavariable it may solve — so an
    /// ascribed `def bad.{u} : Sort u := Nat` is a LOUD mismatch instead of a
    /// silent monomorphization to `Sort 1` (GAP_SWEEP universes/p16,p34). Fresh
    /// universe metavars minted later by `fresh_universe_param` are deliberately
    /// left OUT of the rigid set so they stay solvable.
    pub(crate) fn set_decl_universe_params(&mut self, params: &[String]) {
        self.universe_params = params.to_vec();
        self.metas
            .set_rigid_level_params(params.iter().map(|s| Name::from_string(s)));
    }

    /// Create a fresh universe parameter level
    ///
    /// This generates a new universe parameter name like `u_0`, `u_1`, etc.
    /// and returns a `Level::Param` with that name. The parameter is also
    /// added to `universe_params` so it's available for lookups.
    pub(crate) fn fresh_universe_param(&mut self) -> Level {
        // Generate a unique name that doesn't collide with explicit params.
        // Skip names already in self.universe_params (e.g., if user declared `.{u_0}`).
        let mut id = self.next_universe;
        let name = loop {
            let candidate = format!("u_{id}");
            id += 1;
            if !self.universe_params.contains(&candidate) {
                break candidate;
            }
        };
        self.next_universe = id;
        self.universe_params.push(name.clone());
        Level::param(Name::from_string(&name))
    }

    /// Push a local binding
    pub(crate) fn push_local(&mut self, name: String, ty: Expr) -> FVarId {
        let fvar = self.fresh_fvar();
        self.locals.push((name, fvar, ty));
        fvar
    }

    /// Push a local binding with an existing FVarId.
    ///
    /// Unlike `push_local`, this does not allocate a fresh FVarId —
    /// it reuses the caller-supplied one. Used by the ProofState → ElabCtx
    /// bridge to expose tactic-introduced hypotheses during term
    /// elaboration (#2212).
    pub(crate) fn push_local_with_fvar(&mut self, name: String, fvar: FVarId, ty: Expr) {
        self.locals.push((name, fvar, ty));
        // Ensure fresh_fvar() won't collide with the pushed FVar.
        self.next_fvar = self.next_fvar.max(fvar.as_u64() + 1);
    }

    /// Push a let-bound local definition (`let x : T := value`) with an existing
    /// FVarId. Like [`Self::push_local_with_fvar`], but additionally records the
    /// binding's `value` so it is body-visible (zeta-reducible) during term
    /// elaboration. Used by the ProofState → ElabCtx bridge to expose `let`
    /// tactic locals with their definitional value retained.
    pub(crate) fn push_local_let_with_fvar(
        &mut self,
        name: String,
        fvar: FVarId,
        ty: Expr,
        value: Expr,
    ) {
        self.push_local_with_fvar(name, fvar, ty);
        self.local_let_values.insert(fvar, value);
    }

    /// Pop a local binding
    pub(crate) fn pop_local(&mut self) {
        if let Some((_, fvar, _)) = self.locals.pop() {
            // Clear any let-value side-channel entry in lock-step so a popped
            // let-local cannot leak its value into a later, unrelated scope.
            self.local_let_values.remove(&fvar);
        }
    }

    /// Build a LocalContext containing both locals and metavariables
    pub(crate) fn build_local_ctx(&self) -> LocalContext {
        let mut ctx = LocalContext::new();
        for (name, fvar, ty) in &self.locals {
            let ty_inst = self.metas.instantiate(ty);
            let ty_inst = self.metas.instantiate_levels(&ty_inst);
            // Let-bound locals (`let x : T := v`) carry a value: emit them as
            // local definitions so the kernel WHNF can zeta-reduce `x` to `v`
            // during def-eq. Opaque hypotheses (`have`/binders) have no value
            // entry and stay rigid. See `ElabCtx::local_let_values`.
            if let Some(value) = self.local_let_values.get(fvar) {
                let val_inst = self.metas.instantiate(value);
                let val_inst = self.metas.instantiate_levels(&val_inst);
                ctx.push_let_with_id(*fvar, Name::from_string(name), ty_inst, val_inst);
            } else {
                ctx.push_with_id(*fvar, Name::from_string(name), ty_inst, BinderInfo::Default);
            }
        }

        for (meta_id, meta) in self.metas.iter() {
            let name = Name::from_string(&format!("?m{}", meta_id.0));
            let ty_inst = self.metas.instantiate(&meta.ty);
            let ty_inst = self.metas.instantiate_levels(&ty_inst);
            ctx.push_with_id(
                MetaState::to_fvar(meta_id),
                name,
                ty_inst,
                BinderInfo::Implicit,
            );
        }

        ctx
    }

    /// Look up a local by name
    pub(crate) fn lookup_local(&self, name: &str) -> Option<(FVarId, &Expr)> {
        // Search from innermost to outermost
        for (n, fvar, ty) in self.locals.iter().rev() {
            if n == name {
                return Some((*fvar, ty));
            }
        }
        None
    }

    /// Replace occurrences of a free variable with a constant applied to parameters.
    ///
    /// This is used when elaborating inductive types: the inductive type name is
    /// temporarily bound as a local during constructor elaboration, and then we need
    /// to replace references to it with the proper Const expression.
    ///
    /// Uses ExprFolder trait (#1824) — only `fold_fvar` is overridden; the trait
    /// handles structural recursion over all ExprKind variants (including Cubical/ZFC).
    pub(crate) fn replace_fvar_with_const(
        &self,
        expr: Expr,
        fvar_id: FVarId,
        const_name: &Name,
        level_params: &[Name],
        applied_args: &[Expr],
    ) -> Expr {
        struct ReplaceFvarFolder {
            fvar_id: FVarId,
            const_name: Name,
            levels: Vec<Level>,
            applied_args: Vec<Expr>,
        }
        impl ExprFolder for ReplaceFvarFolder {
            fn fold_fvar(&mut self, id: FVarId) -> Expr {
                if id == self.fvar_id {
                    let base = Expr::const_(self.const_name.clone(), self.levels.clone());
                    if self.applied_args.is_empty() {
                        base
                    } else {
                        Expr::apps(base, self.applied_args.iter().cloned())
                    }
                } else {
                    Expr::fvar(id)
                }
            }
        }

        let mut folder = ReplaceFvarFolder {
            fvar_id,
            const_name: const_name.clone(),
            levels: level_params
                .iter()
                .map(|name| Level::param(name.clone()))
                .collect(),
            applied_args: applied_args.to_vec(),
        };
        folder.fold_expr(&expr)
    }

    /// Expand macros in a surface expression using the macro context.
    pub(crate) fn expand_macros(
        &mut self,
        surface: &SurfaceExpr,
    ) -> Result<SurfaceExpr, ElabError> {
        expand_surface_macros(&mut self.macro_ctx, surface)
            .map_err(|e| ElabError::MacroError(e.to_string()))
    }

    /// Resolve a level using the pending assignments buffer and MetaState.
    ///
    /// Checks pending (uncommitted) assignments first, then falls back to
    /// MetaState's union-find. Used by the level_eq callback to see assignments
    /// made earlier within the same kernel call.
    fn resolve_level_with_pending(
        metas: &MetaState,
        pending: &[(Name, Level)],
        level: &Level,
    ) -> Level {
        match level {
            Level::Param(name) => {
                // Check pending assigns first (most recent wins)
                for (n, l) in pending.iter().rev() {
                    if n == name {
                        return Self::resolve_level_with_pending(metas, pending, l);
                    }
                }
                // Fall back to MetaState
                metas.instantiate_level(level)
            }
            Level::Succ(inner) => {
                Level::succ(Self::resolve_level_with_pending(metas, pending, inner))
            }
            Level::Max(l1, l2) => Level::max(
                Self::resolve_level_with_pending(metas, pending, l1),
                Self::resolve_level_with_pending(metas, pending, l2),
            ),
            Level::IMax(l1, l2) => Level::imax(
                Self::resolve_level_with_pending(metas, pending, l1),
                Self::resolve_level_with_pending(metas, pending, l2),
            ),
            Level::Zero => Level::Zero,
        }
    }

    /// Create a TypeChecker with the level_eq callback injected.
    ///
    /// The callback resolves fresh universe params through:
    /// 1. Fast path: kernel `Level::is_def_eq`
    /// 2. Resolve through MetaState union-find + pending buffer
    /// 3. Assign unresolved params when one side is concrete
    fn make_tc(&self, caches: TcCaches) -> TypeChecker<'_> {
        let mut tc = TypeChecker::with_context_and_caches(self.env, self.build_local_ctx(), caches);
        let metas = &self.metas;
        let pending = &self.pending_level_assigns;
        tc.set_level_eq_override(move |l1, l2| {
            // Fast path: rigid kernel equality
            if Level::is_def_eq(l1, l2) {
                return true;
            }
            // Resolve through union-find + pending buffer
            let pending_ref = pending.borrow();
            let l1r = Self::resolve_level_with_pending(metas, &pending_ref, l1);
            let l2r = Self::resolve_level_with_pending(metas, &pending_ref, l2);
            drop(pending_ref);
            if Level::is_def_eq(&l1r, &l2r) {
                return true;
            }
            // Try assignment: if one side is a param and the other is concrete
            match (&l1r, &l2r) {
                (Level::Param(n), _) if !l2r.has_params() => {
                    pending.borrow_mut().push((n.clone(), l2r));
                    true
                }
                (_, Level::Param(n)) if !l1r.has_params() => {
                    pending.borrow_mut().push((n.clone(), l1r));
                    true
                }
                (Level::Param(n1), Level::Param(_)) => {
                    pending.borrow_mut().push((n1.clone(), l2r));
                    true
                }
                (Level::Succ(a), Level::Succ(b)) => {
                    // Recurse under Succ: if Succ(Param(u)) vs Succ(Zero),
                    // the callback will be re-invoked by the kernel for the
                    // inner comparison. But if we reach here, the kernel
                    // already tried and failed, so attempt direct assignment.
                    let a_r = Self::resolve_level_with_pending(metas, &pending.borrow(), a);
                    let b_r = Self::resolve_level_with_pending(metas, &pending.borrow(), b);
                    if let Level::Param(n) = &a_r {
                        if !b_r.has_params() {
                            pending.borrow_mut().push((n.clone(), b_r));
                            return true;
                        }
                    }
                    if let Level::Param(n) = &b_r {
                        if !a_r.has_params() {
                            pending.borrow_mut().push((n.clone(), a_r));
                            return true;
                        }
                    }
                    false
                }
                _ => false,
            }
        });
        // B14: elaboration-time def-eq/WHNF honors reducibility hints, so an
        // `@[irreducible]` definition does not delta-unfold at the elaboration
        // `.default` transparency (a `theorem : f = v := rfl` through an
        // irreducible `f` now fails LOUDLY here instead of silently proving
        // through it). The kernel's own `add_decl` re-check leaves this off and
        // stays transparency-blind / Lean-faithful.
        tc.set_honor_reducibility(true);
        tc
    }

    /// Commit pending level assignments to MetaState.
    ///
    /// Called at `&mut self` boundaries after kernel operations that may have
    /// discovered new level constraints via the callback.
    pub(crate) fn commit_pending_level_assigns(&mut self) {
        let pending = self.pending_level_assigns.borrow().clone();
        for (name, level) in pending {
            let _ = self.metas.add_level_constraint(name, level);
        }
        self.pending_level_assigns.borrow_mut().clear();
    }

    /// Infer the type of an expression (delegating to kernel)
    pub(crate) fn infer_type(&self, expr: &Expr) -> Result<Expr, ElabError> {
        let caches = self.tc_caches.take();
        let tc = self.make_tc(caches);
        let instantiated = self.metas.instantiate(expr);
        let instantiated = self.metas.instantiate_levels(&instantiated);
        let result = tc
            .infer_type(&instantiated)
            .map(|ty| {
                let ty = self.metas.instantiate(&ty);
                self.metas.instantiate_levels(&ty)
            })
            .map_err(|e| ElabError::TypeMismatch {
                expected: "valid type".to_string(),
                actual: format!("{e:?}"),
            });
        self.tc_caches.replace(tc.take_caches());
        result
    }

    /// Strict (`infer_only=false`) type inference, delegating to the kernel's
    /// `infer_type_full`.
    ///
    /// The default `infer_type` runs the kernel in `infer_only=true` mode, which
    /// skips App-argument and Lam/Pi domain checks. `verify_tactic_proof` uses
    /// this strict variant so an assembled tactic proof is held to the same
    /// standard as `Environment::add_decl` — ill-typed App arguments (e.g. a
    /// mis-applied `Eq.trans`) are rejected at the elaboration boundary instead
    /// of slipping through to a later `add_decl` failure. Part of #38.
    pub(crate) fn infer_type_full(&self, expr: &Expr) -> Result<Expr, ElabError> {
        let caches = self.tc_caches.take();
        let tc = self.make_tc(caches);
        let instantiated = self.metas.instantiate(expr);
        let instantiated = self.metas.instantiate_levels(&instantiated);
        let result = tc
            .infer_type_full(&instantiated)
            .map(|ty| {
                let ty = self.metas.instantiate(&ty);
                self.metas.instantiate_levels(&ty)
            })
            .map_err(|e| ElabError::TypeMismatch {
                expected: "valid type".to_string(),
                actual: format!("{e:?}"),
            });
        self.tc_caches.replace(tc.take_caches());
        result
    }

    /// Infer the universe level `u` such that `expr : Sort u`.
    pub(crate) fn infer_sort(&self, expr: &Expr) -> Result<Level, ElabError> {
        let caches = self.tc_caches.take();
        let tc = self.make_tc(caches);
        let instantiated = self.metas.instantiate(expr);
        let instantiated = self.metas.instantiate_levels(&instantiated);
        let result = tc
            .infer_sort(&instantiated)
            .map_err(|e| ElabError::TypeMismatch {
                expected: "valid type".to_string(),
                actual: format!("{e:?}"),
            });
        self.tc_caches.replace(tc.take_caches());
        result
    }

    /// Ensure `expr` elaborates to a type and return its universe level.
    ///
    /// This mirrors Lean 4's `Meta.getLevel` behavior for assignable
    /// metavariables: if `expr` has type `?m` and `?m : Sort u`, promote `?m`
    /// to `Sort v` so later elaboration sees `expr` as a type.
    pub(crate) fn ensure_type_expr(&mut self, expr: &Expr) -> Result<Level, ElabError> {
        let ty = self.infer_type(expr)?;
        let ty = self.metas.instantiate(&ty);
        let ty = self.metas.instantiate_levels(&ty);

        match ty.kind() {
            ExprKind::Sort(level) => Ok(level.clone()),
            ExprKind::FVar(id) => {
                let Some(meta_id) = MetaState::from_fvar(*id) else {
                    return Err(ElabError::TypeMismatch {
                        expected: "valid type".to_string(),
                        actual: format!("ExpectedSort({ty:?})"),
                    });
                };
                let Some(meta) = self.metas.get(meta_id) else {
                    return Err(ElabError::TypeMismatch {
                        expected: "valid type".to_string(),
                        actual: format!("ExpectedSort({ty:?})"),
                    });
                };
                let meta_ty = self.metas.instantiate(&meta.ty);
                let meta_ty = self.metas.instantiate_levels(&meta_ty);
                if !matches!(meta_ty.kind(), ExprKind::Sort(_)) {
                    return Err(ElabError::TypeMismatch {
                        expected: "valid type".to_string(),
                        actual: format!("ExpectedSort({ty:?})"),
                    });
                }

                let level = self.fresh_universe_param();
                let promoted_sort = Expr::sort(level.clone());
                if !self.metas.assign(meta_id, promoted_sort) {
                    return Err(ElabError::TypeMismatch {
                        expected: "valid type".to_string(),
                        actual: format!("ExpectedSort({ty:?})"),
                    });
                }
                Ok(level)
            }
            _ => Err(ElabError::TypeMismatch {
                expected: "valid type".to_string(),
                actual: format!("ExpectedSort({ty:?})"),
            }),
        }
    }

    /// Compute weak-head normal form of an expression
    pub(crate) fn whnf(&self, expr: &Expr) -> Expr {
        let caches = self.tc_caches.take();
        let tc = self.make_tc(caches);
        let instantiated = self.metas.instantiate(expr);
        let instantiated = self.metas.instantiate_levels(&instantiated);
        let result = tc.whnf(&instantiated);
        self.tc_caches.replace(tc.take_caches());
        result
    }

    /// Check if two expressions are definitionally equal (delegating to kernel)
    pub(crate) fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        let caches = self.tc_caches.take();
        let tc = self.make_tc(caches);
        let a_inst = self.metas.instantiate(a);
        let a_inst = self.metas.instantiate_levels(&a_inst);
        let b_inst = self.metas.instantiate(b);
        let b_inst = self.metas.instantiate_levels(&b_inst);
        let result = tc.is_def_eq(&a_inst, &b_inst);
        self.tc_caches.replace(tc.take_caches());
        result
    }
}

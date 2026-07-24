// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metavariable state management with union-find level constraints and undo trail.

mod levels;
mod undo;

use crate::stack_safe;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolderOpt, FVarId, Level};
use hashbrown::{HashMap, HashSet};

use super::meta_id::{MetaId, MetaVar, UndoRecord};

/// Non-forgeable ownership token for an elaborator-managed metavariable scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct OwnedMetaScopeToken(u64);

/// Failure modes while closing an elaborator-managed metavariable scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OwnedMetaScopeCloseError {
    /// Ordinary scope code attempted to pop or commit the owned marker.
    AccessAttempted,
    /// The exact owned marker no longer exists.
    Missing,
    /// Another owned marker was incorrectly left open above this one.
    Obstructed,
}

#[derive(Debug, Clone)]
pub(super) struct MetaScopeMarker {
    pub(super) undo_len: usize,
    pub(super) owner: Option<OwnedMetaScopeToken>,
}

/// State for metavariable management
///
/// # Undo Trail (Part of #383)
///
/// MetaState supports efficient backtracking via an undo trail. Instead of
/// cloning the entire state for speculative operations, callers can:
///
/// 1. `push_scope()` - Mark the current position
/// 2. Make modifications (assign metavars, add constraints)
/// 3. Either `pop_scope()` to rollback, or `commit()` to keep changes
///
/// This is much more efficient than cloning for deep proof search trees.
///
/// ```text
/// // assign is pub(crate) — this example illustrates internal usage
/// use clean_elab::unify::MetaState;
/// use clean_kernel::Expr;
///
/// let mut state = MetaState::new();
/// let meta = state.fresh(Expr::prop());
///
/// state.push_scope();
/// state.assign(meta, Expr::type_()); // Assign within scope
/// assert!(state.is_assigned(meta));
///
/// state.pop_scope();
/// assert!(!state.is_assigned(meta)); // Assignment was undone
/// ```
#[derive(Debug, Clone)]
pub struct MetaState {
    /// All metavariables
    pub(super) metas: HashMap<MetaId, MetaVar>,
    /// Next fresh metavariable id
    pub(super) next_id: u64,
    /// Universe level constraints: param name -> assigned level
    /// DEPRECATED: Use level_parent and level_concrete instead (kept for backwards compat)
    pub(super) level_constraints: HashMap<Name, Level>,
    /// Union-find parent pointers for level params (param -> parent param)
    /// If a param is not in this map, it is its own root.
    pub(super) level_parent: HashMap<Name, Name>,
    /// Concrete level assignments for canonical (root) params
    /// When a param chain resolves to a concrete level, it's stored here.
    pub(super) level_concrete: HashMap<Name, Level>,
    /// RIGID universe parameters of the declaration currently being elaborated
    /// (those written in `def f.{u,v}` / auto-bound from `Type u`). These are
    /// genuine `Level.param`s, NOT universe metavariables, so unification must
    /// NEVER assign them (Lean's `levelMVarToParam` only ever solves
    /// metavariables; declared params are fixed — MutualDef.lean/Term.lean).
    /// Clean represents fresh universe metavariables as `Level::Param("u_N")`
    /// too, so this set is the ONLY way to tell a rigid declared param from an
    /// assignable metavar. Set once per declaration; never entered into the
    /// undo trail because a fresh `ElabCtx` (hence fresh `MetaState`) is built
    /// per declaration.
    pub(super) rigid_level_params: std::collections::HashSet<Name>,

    // Undo trail fields (Part of #383)
    /// Trail of changes for backtracking. Records are pushed when modifications
    /// are made and replayed in reverse when `pop_scope()` is called.
    pub(super) undo_trail: Vec<UndoRecord>,
    /// Positions in `undo_trail` marking scope boundaries, optionally protected
    /// by a non-forgeable elaborator ownership token.
    pub(super) scope_markers: Vec<MetaScopeMarker>,
    /// Owned markers on which ordinary `pop_scope`/`commit` was attempted.
    pub(super) owned_scope_access_attempts: HashSet<OwnedMetaScopeToken>,
    /// Monotone source for owned-scope tokens. Wrapping allocation skips every
    /// token still active, so a live token is never reused.
    pub(super) next_owned_scope_token: u64,
}

impl MetaState {
    /// High-bit tag to ensure metavariable FVars don't collide with user locals
    const META_FVAR_TAG: u64 = 1 << 63;

    pub fn new() -> Self {
        Self {
            metas: HashMap::new(),
            next_id: 0,
            level_constraints: HashMap::new(),
            level_parent: HashMap::new(),
            level_concrete: HashMap::new(),
            rigid_level_params: std::collections::HashSet::new(),
            undo_trail: Vec::new(),
            scope_markers: Vec::new(),
            owned_scope_access_attempts: HashSet::new(),
            next_owned_scope_token: 0,
        }
    }

    /// Declare the RIGID universe parameters of the declaration currently being
    /// elaborated. Unification will refuse to assign any of these — they are
    /// genuine `Level.param`s, not metavariables (see field docs). Replaces the
    /// previous set outright, so callers set it once at declaration entry.
    pub(crate) fn set_rigid_level_params<I: IntoIterator<Item = Name>>(&mut self, names: I) {
        self.rigid_level_params = names.into_iter().collect();
    }

    /// Whether `name` is a rigid declared universe parameter (never assignable).
    #[must_use]
    pub(crate) fn is_rigid_level_param(&self, name: &Name) -> bool {
        self.rigid_level_params.contains(name)
    }

    /// Create a fresh metavariable with the given type and an explicitly empty
    /// local scope.
    ///
    /// Callers that can see locals must use [`Self::fresh_with_locals`].  An
    /// absent snapshot is never reconstructed from a later unifier context.
    pub fn fresh(&mut self, ty: Expr) -> MetaId {
        self.fresh_internal(ty, Vec::new(), None)
    }

    /// Create a fresh metavariable with the given type and captured locals.
    pub fn fresh_with_locals(&mut self, ty: Expr, locals: Vec<(String, FVarId, Expr)>) -> MetaId {
        self.fresh_internal(ty, locals, None)
    }

    /// Create a fresh metavariable with the given type, captured locals, and an
    /// optional source span.
    ///
    /// The span is purely informational: it records the position of a
    /// user-written hole (`_`) so IDE surfaces can map the metavariable back to
    /// the hole. All other `fresh*` constructors funnel through here with
    /// `span = None`.
    pub fn fresh_with_locals_at(
        &mut self,
        ty: Expr,
        locals: Vec<(String, FVarId, Expr)>,
        span: Option<clean_parser::Span>,
    ) -> MetaId {
        self.fresh_internal(ty, locals, span)
    }

    fn fresh_internal(
        &mut self,
        ty: Expr,
        locals: Vec<(String, FVarId, Expr)>,
        span: Option<clean_parser::Span>,
    ) -> MetaId {
        let id = MetaId(self.next_id);
        let next_id = self
            .next_id
            .checked_add(1)
            .expect("metavariable id space exhausted");
        self.record_undo(UndoRecord::NextId {
            old_value: self.next_id,
        });
        self.next_id = next_id;
        self.metas.insert(
            id,
            MetaVar {
                ty,
                locals,
                assignment: None,
                span,
            },
        );
        // Record undo for backtracking
        self.record_undo(UndoRecord::MetaCreate { id });
        id
    }

    /// Ensure a metavariable with the given id exists, creating it if absent.
    ///
    /// Used when a goal's meta_id was created in a different MetaState (e.g.,
    /// a temporary proof state). Registers the meta and bumps `next_id` so
    /// that subsequent `fresh()` calls produce non-colliding IDs. Part of #2199.
    pub(crate) fn ensure_meta(&mut self, id: MetaId, ty: Expr) {
        self.ensure_meta_with_locals(id, ty, Vec::new());
    }

    /// Ensure a metavariable exists with an exact captured local context.
    ///
    /// This is used when a goal crosses between proof states.  If the meta is
    /// already present its original creation scope is retained; otherwise the
    /// supplied goal scope is the only authority for a new entry.
    pub(crate) fn ensure_meta_with_locals(
        &mut self,
        id: MetaId,
        ty: Expr,
        locals: Vec<(String, FVarId, Expr)>,
    ) {
        if self.metas.get(&id).is_none() {
            self.metas.insert(
                id,
                MetaVar {
                    ty,
                    locals,
                    assignment: None,
                    span: None,
                },
            );
            self.record_undo(UndoRecord::MetaCreate { id });
        }
        // Ensure next_id is above this meta to prevent collisions
        if id.0 >= self.next_id {
            let next_id =
                id.0.checked_add(1)
                    .expect("metavariable id space exhausted");
            self.set_next_id(next_id);
        }
    }

    /// Advance the fresh-id cursor, recording its exact previous value when a
    /// scope may need to restore it. No record is emitted for a no-op.
    fn set_next_id(&mut self, next_id: u64) {
        if next_id <= self.next_id {
            return;
        }
        self.record_undo(UndoRecord::NextId {
            old_value: self.next_id,
        });
        self.next_id = next_id;
    }

    /// Convert a metavariable id into the FVarId used in expressions
    pub fn to_fvar(id: MetaId) -> FVarId {
        FVarId::new(id.0 | Self::META_FVAR_TAG)
    }

    /// Try to decode a metavariable id from a free variable
    pub fn from_fvar(id: FVarId) -> Option<MetaId> {
        if id.as_u64() & Self::META_FVAR_TAG != 0 {
            Some(MetaId(id.as_u64() & !Self::META_FVAR_TAG))
        } else {
            None
        }
    }

    /// Get a metavariable by id
    pub fn get(&self, id: MetaId) -> Option<&MetaVar> {
        self.metas.get(&id)
    }

    /// Assign a value to a metavariable
    ///
    /// # Visibility
    /// Restricted to `pub(crate)` to prevent unchecked proof assignment from
    /// outside the elaboration crate. Tactic code should use `close_goal` (checked)
    /// instead of calling `metas.assign` directly. See #2202.
    pub(crate) fn assign(&mut self, id: MetaId, val: Expr) -> bool {
        // Check if assignable first (without holding mutable borrow)
        let can_assign = self.metas.get(&id).is_some_and(|m| m.assignment.is_none());

        if can_assign {
            // Occurs check: reject circular assignment where the target meta
            // appears in the value (after instantiation). Without this, a
            // tactic could create `?m := f(?m)` which loops during
            // instantiation. Part of #2199.
            if self.occurs(id, &val) {
                return false;
            }

            // Record undo for backtracking (capture old value = None)
            self.record_undo(UndoRecord::MetaAssign {
                id,
                old_value: None,
            });
            // Now do the assignment
            if let Some(meta) = self.metas.get_mut(&id) {
                meta.assignment = Some(val);
                return true;
            }
        }
        false
    }

    /// Check if a metavariable is assigned
    pub fn is_assigned(&self, id: MetaId) -> bool {
        self.metas.get(&id).is_some_and(|m| m.assignment.is_some())
    }

    /// Get the assignment of a metavariable
    pub fn get_assignment(&self, id: MetaId) -> Option<&Expr> {
        self.metas.get(&id).and_then(|m| m.assignment.as_ref())
    }

    /// Get all unassigned metavariables
    pub fn unassigned(&self) -> Vec<MetaId> {
        self.metas
            .iter()
            .filter(|(_, m)| m.assignment.is_none())
            .map(|(id, _)| *id)
            .collect()
    }

    /// Instantiate metavariables in an expression
    pub fn instantiate(&self, expr: &Expr) -> Expr {
        stack_safe(|| self.instantiate_inner(expr))
    }

    fn instantiate_inner(&self, expr: &Expr) -> Expr {
        /// Sharing-preserving folder that substitutes assigned metavar FVars.
        ///
        /// PERFORMANCE (measured, not speculative): the previous
        /// `ExprFolder`-based walk rebuilt EVERY node of the expression —
        /// fresh allocation + `compute_meta` hashing per node — on every
        /// `instantiate` call, even when the expression contained no
        /// metavariables at all. Elaboration calls `instantiate` on every
        /// unification step, so large ground statements (e.g. trust-ir
        /// `stepNWithContext` interpreter terms) went quadratic-plus in both
        /// time and allocation: a byte-identical `A = A` theorem proved by a
        /// zero-metavariable `@rfl` was killed at >12GB RSS, with 100% of
        /// profile samples inside this walk (see trust-clean's
        /// `dataloop_composed_wall_reproducer`). [`ExprFolderOpt`] is the
        /// purpose-built fix: `None` means "unchanged — reuse the existing
        /// Arc" (zero allocation for untouched subtrees), and
        /// `should_descend` skips whole subtrees via the O(1) cached
        /// `has_fvar` flag — elaborator metavariables are encoded as FVars,
        /// so an fvar-free subtree cannot contain one.
        struct InstantiateMetas<'a> {
            state: &'a MetaState,
        }

        impl ExprFolderOpt for InstantiateMetas<'_> {
            fn should_descend(&self, expr: &Expr) -> bool {
                expr.has_fvar_quick()
            }

            fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
                if let Some(meta_id) = MetaState::from_fvar(id) {
                    if let Some(meta) = self.state.get(meta_id) {
                        if let Some(val) = &meta.assignment {
                            // The assignment may itself mention assigned
                            // metas — instantiate it recursively (still
                            // sharing-preserving).
                            return Some(self.fold_expr_opt(val).unwrap_or_else(|| val.clone()));
                        }
                    }
                }
                None
            }
        }

        let mut folder = InstantiateMetas { state: self };
        folder.fold_expr_opt(expr).unwrap_or_else(|| expr.clone())
    }

    /// Check whether a metavariable occurs in an expression (after instantiation).
    /// Instantiates the expression first, then does a structural check.
    pub fn occurs(&self, meta: MetaId, expr: &Expr) -> bool {
        let inst = self.instantiate(expr);
        Self::occurs_in(&inst, meta)
    }

    /// Structural occurs check on an already-instantiated expression.
    /// Does not call instantiate — avoids redundant O(n) work per recursive call.
    /// Use this instead of `occurs()` when the expression has already been instantiated
    /// to avoid a redundant O(n) tree walk.
    pub(crate) fn occurs_in(expr: &Expr, meta: MetaId) -> bool {
        // DAG-aware occurs check (measured, not speculative): the
        // sharing-preserving `instantiate` above hands out expressions where
        // large subtrees are shared through many `Arc` paths. The previous
        // `ExprVisitor` tree-recursion revisited every shared subtree once
        // per PATH — exponential blowup on such DAGs (after the instantiate
        // fix, 100% of profile samples on the trust-clean
        // `dataloop_composed_wall_reproducer` moved HERE). Two guards keep
        // this linear in DISTINCT nodes:
        //   - O(1) prune via the cached `has_fvar` flag — elaborator
        //     metavariables are encoded as FVars, so an fvar-free subtree
        //     cannot contain one;
        //   - a pointer-identity visited set, mirroring the kernel
        //     `instantiate` DAG-memo (expr/subst.rs Track XX regression).
        let mut visited: hashbrown::HashSet<*const Expr> = hashbrown::HashSet::new();
        let mut stack: Vec<&Expr> = vec![expr];
        while let Some(e) = stack.pop() {
            if !e.has_fvar_quick() {
                continue;
            }
            if !visited.insert(e as *const Expr) {
                continue;
            }
            if let clean_kernel::ExprKind::FVar(id) = e.kind() {
                if MetaState::from_fvar(*id) == Some(meta) {
                    return true;
                }
            }
            push_expr_children(e, &mut stack);
        }
        false
    }

    /// Iterate over all metavariables
    pub fn iter(&self) -> impl Iterator<Item = (MetaId, &MetaVar)> {
        self.metas.iter().map(|(id, meta)| (*id, meta))
    }

    /// Merge assignments from another `MetaState` into this one.
    ///
    /// Copies over any new metavariable entries and assignments that exist
    /// in `other` but not in `self`. This is used by `all_goals`, `any_goals`,
    /// and `seq_focus` to propagate metavariable assignments from focused
    /// sub-proof-states back into the parent (#1802).
    pub fn merge_from(&mut self, other: &MetaState) {
        for (id, meta) in &other.metas {
            let Some(existing_assignment) = self
                .metas
                .get(id)
                .map(|existing| existing.assignment.clone())
            else {
                // New metavariable created during focused tactic execution.
                self.record_undo(UndoRecord::MetaCreate { id: *id });
                self.metas.insert(*id, meta.clone());
                continue;
            };

            if existing_assignment.is_none() && meta.assignment.is_some() {
                // Metavariable was assigned in the focused state.
                self.record_undo(UndoRecord::MetaAssign {
                    id: *id,
                    old_value: existing_assignment,
                });
                self.metas
                    .get_mut(id)
                    .expect("metavariable disappeared during merge")
                    .assignment = meta.assignment.clone();
            }
        }
        // Sync next_id to avoid collisions. A MetaState normally maintains
        // `next_id > max(meta id)`, but derive the lower bound from the imported
        // map too so a malformed/synthetic state cannot make the next fresh id
        // overwrite an imported metavariable.
        let merged_next_id = other.metas.keys().fold(other.next_id, |next_id, id| {
            next_id.max(
                id.0.checked_add(1)
                    .expect("metavariable id space exhausted"),
            )
        });
        self.set_next_id(merged_next_id);

        // Merge level unification state (#1847)
        // Copy new level_constraints entries from other
        for (name, level) in &other.level_constraints {
            if !self.level_constraints.contains_key(name) {
                self.record_undo(UndoRecord::LevelConstraint {
                    name: name.clone(),
                    old_value: None,
                });
                self.level_constraints.insert(name.clone(), level.clone());
            }
        }
        // Copy new union-find parent entries from other
        for (name, parent) in &other.level_parent {
            if !self.level_parent.contains_key(name) {
                self.record_undo(UndoRecord::LevelParent {
                    name: name.clone(),
                    old_parent: None,
                });
                self.level_parent.insert(name.clone(), parent.clone());
            }
        }
        // Copy new concrete level assignments from other
        for (name, level) in &other.level_concrete {
            if !self.level_concrete.contains_key(name) {
                self.record_undo(UndoRecord::LevelConcrete {
                    name: name.clone(),
                    old_level: None,
                });
                self.level_concrete.insert(name.clone(), level.clone());
            }
        }
    }
}

impl Default for MetaState {
    fn default() -> Self {
        Self::new()
    }
}

/// Push every direct child expression of `e` onto `stack`.
///
/// Shared driver for the DAG-aware iterative walks in this crate
/// ([`MetaState::occurs_in`], `ElabCtx::has_metavars`,
/// `ElabCtx::collect_meta_fvars`): pair it with an O(1) cached-flag prune and
/// a pointer-identity visited set so shared subtrees are examined once per
/// NODE, not once per PATH (the tree-recursive `ExprVisitor` walks were
/// measured path-exponential on the DAGs the sharing-preserving `instantiate`
/// produces).
///
/// Exhaustive on purpose (no `_` arm): a future `ExprKind` variant must
/// declare its children here or fail to compile.
pub(crate) fn push_expr_children<'a>(e: &'a Expr, stack: &mut Vec<&'a Expr>) {
    use clean_kernel::expr::ZFCSetExpr;
    use clean_kernel::ExprKind;

    match e.kind() {
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(..)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
        ExprKind::App(f, a) => {
            stack.push(f);
            stack.push(a);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            stack.push(ty);
            stack.push(body);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            stack.push(ty);
            stack.push(val);
            stack.push(body);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            stack.push(inner)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            stack.push(ty);
            stack.push(left);
            stack.push(right);
        }
        ExprKind::CubicalPathLam { body } => stack.push(body),
        ExprKind::CubicalPathApp { path, arg } => {
            stack.push(path);
            stack.push(arg);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            stack.push(ty);
            stack.push(phi);
            stack.push(u);
            stack.push(base);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            stack.push(ty);
            stack.push(phi);
            stack.push(base);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            stack.push(ty);
            stack.push(r);
            stack.push(s);
            stack.push(base);
        }
        ExprKind::ZFCMem { element, set } => {
            stack.push(element);
            stack.push(set);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            stack.push(domain);
            stack.push(pred);
        }
        ExprKind::ZFCSet(set_expr) => match set_expr {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
            ZFCSetExpr::Singleton(e1)
            | ZFCSetExpr::Union(e1)
            | ZFCSetExpr::PowerSet(e1)
            | ZFCSetExpr::Choice(e1) => stack.push(e1),
            ZFCSetExpr::Pair(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            ZFCSetExpr::Separation { set, pred } => {
                stack.push(set);
                stack.push(pred);
            }
            ZFCSetExpr::Replacement { set, func } => {
                stack.push(set);
                stack.push(func);
            }
        },
    }
}

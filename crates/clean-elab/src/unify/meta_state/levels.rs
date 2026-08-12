// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe level constraint management via union-find and level canonicalization.

use crate::stack_safe;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolderOpt, Level, LevelVec};

use super::super::meta_id::UndoRecord;
use super::MetaState;

impl MetaState {
    /// Add a universe level constraint: param_name = level.
    ///
    /// Uses union-find to handle param-to-param constraints (like `u_0 = u_1`).
    /// When a param is constrained to a concrete level, propagates to the canonical root.
    ///
    /// Returns `Err` when this would merge two universe classes with conflicting concrete
    /// assignments or would overwrite an existing concrete assignment with a different level.
    pub fn add_level_constraint(&mut self, param_name: Name, level: Level) -> Result<(), String> {
        // A param constrained to a member of its OWN equivalence class — most
        // importantly the literal reflexive `u := Param(u)` — is a vacuous,
        // already-satisfied constraint (`u = u`). The union-find already records
        // the relation, so there is nothing to do. Crucially, the legacy
        // `level_constraints` map (read by `instantiate_level` when a param is its
        // own root) would otherwise store a SELF-REFERENTIAL entry
        // `level_constraints[u] = Param(u)`, which makes `instantiate_level`
        // recurse on `Param(u)` forever (observed: foundation `Eq.substType`
        // elaboration looped on `u_0 := Param(u_0)` and OOM'd). Skipping the
        // already-satisfied case is behavior-preserving: re-unioning members of a
        // single class is a no-op, and the redundant legacy entry it would write
        // is never consulted in a way that changes the resolved level.
        if let Level::Param(other_name) = &level {
            if self.level_find_immut(other_name) == self.level_find_immut(&param_name) {
                return Ok(());
            }
        }

        // RIGID declared universe parameter: never assignable. Lean's
        // `levelMVarToParam`/level unification only ever solves universe
        // *metavariables*; a declared `.{u}` param is fixed. Clean stores both
        // as `Level::Param`, so `add_level_constraint` is the funnel where an
        // attempted assignment of a rigid param must be refused. Refusing here
        // is what makes `def bad.{u} : Sort u := Nat` a LOUD mismatch (the
        // ascribed `Sort u` never gets silently rewritten to `Sort 1`) instead
        // of a silently-monomorphized accept (GAP_SWEEP universes/p16,p34).
        // A rigid-to-rigid identity was already handled by the self-class
        // early-return above; any other target is a genuine conflict.
        if self.is_rigid_level_param(&param_name) {
            return Err(format!(
                "cannot assign rigid universe parameter {param_name:?} := {level:?}"
            ));
        }

        // Pre-check conflicts before mutating any state.
        match &level {
            Level::Param(other_name) => self.check_level_union_conflict(&param_name, other_name)?,
            _ if !level.has_params() => {
                let root = self.level_find_immut(&param_name);
                if let Some(existing) = self.level_concrete.get(&root) {
                    if existing != &level {
                        return Err(format!(
                            "universe level conflict for root {root:?}: existing {existing:?} vs new {level:?}"
                        ));
                    }
                }
            }
            _ => {}
        }

        // Record undo for legacy map
        let old_constraint = self.level_constraints.get(&param_name).cloned();
        self.record_undo(UndoRecord::LevelConstraint {
            name: param_name.clone(),
            old_value: old_constraint,
        });

        // Store in legacy map for backwards compatibility
        self.level_constraints
            .insert(param_name.clone(), level.clone());

        match &level {
            Level::Param(other_name) => {
                // Param-to-param constraint: union the two params
                self.level_union(&param_name, other_name)?;
            }
            _ if !level.has_params() => {
                // Concrete level: assign to the canonical root
                let root = self.level_find(&param_name);
                if self.level_concrete.get(&root) != Some(&level) {
                    // Record undo for concrete assignment
                    let old_concrete = self.level_concrete.get(&root).cloned();
                    self.record_undo(UndoRecord::LevelConcrete {
                        name: root.clone(),
                        old_level: old_concrete,
                    });
                    self.level_concrete.insert(root, level);
                }
            }
            _ => {
                // Compound level (contains params, not a bare param):
                // `?u := Succ(?v)`, `?u := Max(?v, w)`. U2 rung-1a: stored
                // FIRST-CLASS at the canonical root (`level_bound`) so the
                // assignment survives later re-rooting unions — the legacy
                // map above only ever resolved when the param stayed its own
                // root (the measured-dominant rung-0b histogram class).
                // Cyclic values are defended by `instantiate_level`'s chain
                // guard, exactly as for the legacy path.
                let root = self.level_find(&param_name);
                let old_bound = self.level_bound.get(&root).cloned();
                self.record_undo(UndoRecord::LevelBound {
                    name: root.clone(),
                    old_level: old_bound,
                });
                self.level_bound.insert(root, level.clone());
                crate::u2_histogram::u2_hist(
                    "compound-bound",
                    "add-constraint",
                    &format!("{param_name:?} := {level:?}"),
                );
            }
        }
        Ok(())
    }

    /// Get a universe level constraint (legacy interface)
    pub fn get_level_constraint(&self, param_name: &Name) -> Option<&Level> {
        self.level_constraints.get(param_name)
    }

    /// Find the canonical representative for a level param (union-find with path compression)
    pub(super) fn level_find(&mut self, name: &Name) -> Name {
        // Check if this param has a parent
        if let Some(parent) = self.level_parent.get(name).cloned() {
            if &parent != name {
                // Path compression: update to point directly to root
                let root = self.level_find(&parent);
                if root != parent {
                    // Record undo for path compression
                    let old_parent = Some(parent);
                    self.record_undo(UndoRecord::LevelParent {
                        name: name.clone(),
                        old_parent,
                    });
                    self.level_parent.insert(name.clone(), root.clone());
                }
                return root;
            }
        }
        // No parent or self-loop: this is the root
        name.clone()
    }

    /// Find canonical representative without mutation (for use in &self methods)
    pub(super) fn level_find_immut(&self, name: &Name) -> Name {
        let mut current = name.clone();
        // Follow parent chain to root
        while let Some(parent) = self.level_parent.get(&current) {
            if parent == &current {
                break;
            }
            current = parent.clone();
        }
        current
    }

    fn check_level_union_conflict(&self, name1: &Name, name2: &Name) -> Result<(), String> {
        let root1 = self.level_find_immut(name1);
        let root2 = self.level_find_immut(name2);

        if root1 == root2 {
            return Ok(());
        }

        let concrete1 = self.level_concrete.get(&root1);
        let concrete2 = self.level_concrete.get(&root2);
        if let (Some(c1), Some(c2)) = (concrete1, concrete2) {
            if c1 != c2 {
                return Err(format!(
                    "universe level conflict while unifying {root1:?} and {root2:?}: {c1:?} vs {c2:?}"
                ));
            }
        }
        Ok(())
    }

    /// Union two level params into the same equivalence class.
    ///
    /// Returns `Err` when both classes already have different concrete assignments.
    fn level_union(&mut self, name1: &Name, name2: &Name) -> Result<(), String> {
        self.check_level_union_conflict(name1, name2)?;

        let root1 = self.level_find(name1);
        let root2 = self.level_find(name2);

        if root1 == root2 {
            return Ok(()); // Already in same class
        }

        // Check if either root has a concrete assignment
        let concrete1 = self.level_concrete.get(&root1).cloned();
        let concrete2 = self.level_concrete.get(&root2).cloned();

        // Make root2 the parent of root1 (arbitrary choice)
        // Prefer to keep the root that has a concrete assignment
        match (&concrete1, &concrete2) {
            (Some(_), None) => {
                // root1 has concrete, make it the canonical root
                // Record undo for parent pointer
                let old_parent = self.level_parent.get(&root2).cloned();
                self.record_undo(UndoRecord::LevelParent {
                    name: root2.clone(),
                    old_parent,
                });
                self.level_parent.insert(root2.clone(), root1.clone());
                self.migrate_level_bound(&root2, &root1);
            }
            _ => {
                // root2 is canonical (or both have concrete, or neither)
                // Record undo for parent pointer
                let old_parent = self.level_parent.get(&root1).cloned();
                self.record_undo(UndoRecord::LevelParent {
                    name: root1.clone(),
                    old_parent,
                });
                self.level_parent.insert(root1.clone(), root2.clone());
                self.migrate_level_bound(&root1, &root2);

                // If root1 had concrete, propagate to root2
                if let Some(concrete) = concrete1 {
                    if concrete2.is_none() {
                        // Record undo for concrete assignment
                        let old_concrete = self.level_concrete.get(&root2).cloned();
                        self.record_undo(UndoRecord::LevelConcrete {
                            name: root2.clone(),
                            old_level: old_concrete,
                        });
                        self.level_concrete.insert(root2, concrete);
                    }
                }
            }
        }
        Ok(())
    }

    /// Migrate a compound (bound) level assignment from a root that just LOST
    /// canonicity to the new root (U2 rung-1a). The winner's existing bound is
    /// kept when both classes carried one (matching the legacy map's
    /// last-writer-wins tolerance; the produced term is kernel-rechecked).
    fn migrate_level_bound(&mut self, old_root: &Name, new_root: &Name) {
        let Some(bound) = self.level_bound.get(old_root).cloned() else {
            return;
        };
        self.record_undo(UndoRecord::LevelBound {
            name: old_root.clone(),
            old_level: Some(bound.clone()),
        });
        self.level_bound.remove(old_root);
        if !self.level_bound.contains_key(new_root) {
            self.record_undo(UndoRecord::LevelBound {
                name: new_root.clone(),
                old_level: None,
            });
            self.level_bound.insert(new_root.clone(), bound);
        }
    }

    /// Substitute level constraints into a level
    ///
    /// Uses union-find to resolve params to their canonical form:
    /// 1. If the param's equivalence class has a concrete level, return that
    /// 2. Otherwise, return the canonical param (ensuring `u_0` and `u_1` both
    ///    return the same param if they're unified)
    pub fn instantiate_level(&self, level: &Level) -> Level {
        // `chain` tracks the canonical roots we are CURRENTLY following through
        // concrete / legacy param assignments (a DFS path, not a global visited
        // set). It is the defensive cycle guard: see `instantiate_level_guarded`.
        let mut chain: Vec<Name> = Vec::new();
        self.instantiate_level_guarded(level, &mut chain)
    }

    /// Cycle-guarded core of [`Self::instantiate_level`].
    ///
    /// SOUNDNESS / DEFENSE-IN-DEPTH: a universe-level metavariable assignment
    /// whose value transitively references its own canonical root — e.g. the
    /// vacuous `u := Param(u)` legacy entry, or an (otherwise occurs-checked)
    /// `u := Succ(Param(u))` / `u := Max(Param(u), _)` — would make the previous
    /// implementation recurse forever (`instantiate_level` ↔ itself), spawning
    /// unbounded `stacker` growth threads until the process OOMs. `chain` records
    /// the roots on the current resolution path; re-entering a root already on the
    /// path means the assignment is cyclic, so we stop and return the canonical
    /// `Param(root)` (the only fixed point of a self-referential level).
    ///
    /// Behavior-preserving on ACYCLIC inputs: `chain` only ever contains roots
    /// strictly above the current node on a single follow-path, so a well-formed
    /// (acyclic) level never re-enters a root and the guard never fires — the
    /// branch structure is then identical to the original implementation. Sibling
    /// occurrences of the same param (e.g. `Max(Param(a), Param(a))`) are resolved
    /// independently because each root is popped off `chain` before the sibling is
    /// visited.
    fn instantiate_level_guarded(&self, level: &Level, chain: &mut Vec<Name>) -> Level {
        stack_safe(|| match level {
            Level::Param(name) => {
                // Find canonical representative
                let root = self.level_find_immut(name);

                // Cycle guard: we are already resolving this root further up the
                // current follow-path. Returning the canonical param breaks the
                // loop (a self-referential level's only fixed point is the param
                // itself); the produced expression is still kernel-rechecked.
                if chain.iter().any(|n| n == &root) {
                    return Level::Param(root);
                }

                // Check if root has a concrete assignment
                if let Some(concrete) = self.level_concrete.get(&root) {
                    chain.push(root);
                    let resolved = self.instantiate_level_guarded(concrete, chain);
                    chain.pop();
                    return resolved;
                }

                // Compound (bound) assignment at the root (U2 rung-1a): unlike
                // the legacy fallback below, this resolves REGARDLESS of
                // whether `name` is its own root, so `?u := Succ(?v)` survives
                // a later union that re-roots `?u`'s class.
                if let Some(bound) = self.level_bound.get(&root) {
                    chain.push(root);
                    let resolved = self.instantiate_level_guarded(&bound.clone(), chain);
                    chain.pop();
                    return resolved;
                }

                // No concrete assignment - return canonical param
                // This ensures u_0 and u_1 both become the same param if unified
                if &root != name {
                    Level::Param(root)
                } else {
                    // Fall back to legacy constraint lookup
                    if let Some(assigned) = self.level_constraints.get(name) {
                        chain.push(root);
                        let resolved = self.instantiate_level_guarded(assigned, chain);
                        chain.pop();
                        resolved
                    } else {
                        level.clone()
                    }
                }
            }
            Level::Succ(inner) => Level::succ(self.instantiate_level_guarded(inner, chain)),
            Level::Max(l1, l2) => Level::max(
                self.instantiate_level_guarded(l1, chain),
                self.instantiate_level_guarded(l2, chain),
            ),
            Level::IMax(l1, l2) => Level::imax(
                self.instantiate_level_guarded(l1, chain),
                self.instantiate_level_guarded(l2, chain),
            ),
            Level::Zero => Level::Zero,
        })
    }

    /// Substitute level constraints into an expression
    pub fn instantiate_levels(&self, expr: &Expr) -> Expr {
        if self.level_constraints.is_empty()
            && self.level_parent.is_empty()
            && self.level_concrete.is_empty()
            && self.level_bound.is_empty()
        {
            return expr.clone();
        }
        self.canonicalize_levels_in_expr_inner(expr)
    }

    /// Canonicalize all universe level params in an expression.
    ///
    /// Walks the full `Expr` tree and rewrites all universe levels using
    /// `instantiate_level`, ensuring unified params use the same representative.
    pub fn canonicalize_levels_in_expr(&self, expr: &Expr) -> Expr {
        stack_safe(|| self.canonicalize_levels_in_expr_inner(expr))
    }

    fn canonicalize_levels_in_expr_inner(&self, expr: &Expr) -> Expr {
        /// Sharing-preserving folder that rewrites `Sort` and `Const` levels via
        /// `MetaState::instantiate_level`.
        ///
        /// PERF (Track WW): the previous implementation used the eager `ExprFolder`,
        /// which unconditionally reconstructed *every* node of the expression on every
        /// call — even when no level actually changed. During elaboration of a large
        /// term (e.g. `semIntBinOp`'s 18-arm match), `infer_type` calls
        /// `instantiate_levels` repeatedly over the growing expected-type expression,
        /// so the full-tree rebuild became quadratic and the file timed out (>110s).
        ///
        /// This `ExprFolderOpt` version:
        ///   * uses the O(1) `has_level_param_quick()` metadata guard to skip whole
        ///     subtrees that contain no `Level::Param` (clean `Level` has no MVar
        ///     constructor, so a param-free subtree is canonicalization-invariant), and
        ///   * returns `None` ("unchanged, reuse the existing Arc") whenever a node's
        ///     levels are fixed points of `instantiate_level`.
        ///
        /// SOUNDNESS: the resulting expression is structurally identical to the eager
        /// version — the only difference is Arc sharing of unchanged subterms. Every
        /// `Sort`/`Const` level is still passed through `instantiate_level`; we merely
        /// avoid allocating a fresh-but-equal node when the level is unchanged.
        struct CanonicalizeLevels<'a> {
            state: &'a MetaState,
        }

        impl ExprFolderOpt for CanonicalizeLevels<'_> {
            #[inline]
            fn should_descend(&self, expr: &Expr) -> bool {
                // No level params anywhere in this subtree ⇒ `instantiate_level` is
                // the identity over all its levels ⇒ nothing to rewrite. O(1) check.
                expr.has_level_param_quick()
            }

            fn fold_sort_opt(&mut self, level: &Level) -> Option<Expr> {
                let new_level = self.state.instantiate_level(level);
                if &new_level == level {
                    None
                } else {
                    Some(Expr::sort(new_level))
                }
            }

            fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
                let mut changed = false;
                let new_levels: Vec<Level> = levels
                    .iter()
                    .map(|l| {
                        let nl = self.state.instantiate_level(l);
                        if &nl != l {
                            changed = true;
                        }
                        nl
                    })
                    .collect();
                if changed {
                    Some(Expr::const_(name.clone(), new_levels))
                } else {
                    None
                }
            }
        }

        expr.fold_opt_or_clone(&mut CanonicalizeLevels { state: self })
    }
}

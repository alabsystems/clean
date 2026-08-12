// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested inductive elimination (#3239, rebuilt per
//! `designs/2026-07-02-parameterized-nested-inductives.md` §1–§3).
//!
//! Lean 4's `elim_nested_inductive_fn` (inductive.cpp:882-1077) transforms
//! nested inductive types into mutual inductives by creating auxiliary mirror
//! types. For example:
//! ```text
//! inductive Tree where
//!   | node : List Tree → Tree
//! ```
//! becomes the mutual block
//! ```text
//! mutual
//!   inductive Tree where
//!     | node : _nested.List_1 → Tree
//!   inductive _nested.List_1 where
//!     | nil : _nested.List_1
//!     | cons : Tree → _nested.List_1 → _nested.List_1
//! end
//! ```
//!
//! Key properties (all Lean-parity, design §1.2–§3):
//! - **Worklist fixpoint**: aux constructors are themselves re-scanned, so
//!   multi-level nesting (`Array (Key × Trie α)` ⇒ Array → List → Prod)
//!   produces the whole aux chain; the queue grows while scanned.
//! - **Whole-mutual-block copy**: a nested occurrence of one member of a
//!   mutual container copies every sibling, with memo entries inserted for
//!   all of them before their constructors are processed.
//! - **Canonical dedup key** `(container, levels, lowered-args)`: the same
//!   instantiation at different Pi depths dedups to one aux type
//!   (depth-canonical via [`Expr::lower_loose_bvars`]); the same instantiation
//!   at different universe levels yields distinct aux types (level-inclusive).
//! - **Parameterized aux telescopes**: every aux type is prefixed with the
//!   outer declaration's `num_params` telescope (copied verbatim from the
//!   first type former), and the container's own parameters are eliminated by
//!   simultaneous substitution with the occurrence's canonicalized args. For
//!   `num_params = 0` this degenerates to the classic closed mirror. The
//!   `num_params > 0` path is unreachable in production until the guard in
//!   `inductive_builder.rs` is narrowed (design brick B5).
//!
//! The restore pass (design §4, brick B3) maps the checked mutual block back
//! to Lean's post-restore artifacts; until it lands, aux types remain
//! registered under their `_nested.*` names as before.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::expr::{Expr, ExprKind};
use crate::inductive::{
    mentions_name, Constructor, InductiveDecl, InductiveError, InductiveType, InductiveVal,
};
use crate::level::Level;
use crate::name::Name;

use super::Environment;

/// Per-declaration cap on auxiliary mirror types. This is the termination
/// guarantee for the worklist fixpoint (mutually-nesting containers make it
/// unbounded in principle — Lean has no cap); deepest observed corpus chain
/// is ≈ 8 (`Lean.Doc.Block`). Recorded in `docs/JUSTIFIED_EXCEPTIONS.md`.
const NESTED_AUX_LIMIT: usize = 64;

/// Everything the restore pass (design §4, brick B3) needs about one aux
/// mirror, in creation order (creation order fixes Lean's `rec_N` numbering).
#[derive(Debug, Clone)]
pub(crate) struct NestedAuxEntry {
    /// Fresh aux type name (`_nested.<container>_<idx>`)
    pub(crate) aux_name: Name,
    /// The container-block member this aux type mirrors
    pub(crate) sibling_name: Name,
    /// Concrete levels `Ls` substituted for the container's level params
    pub(crate) container_levels: Vec<Level>,
    /// Canonical parameter instantiation `Ds′` (over the outer telescope)
    pub(crate) canonical_args: Vec<Expr>,
    /// aux constructor name → container constructor name, in ctor order
    pub(crate) ctor_map: Vec<(Name, Name)>,
}

/// Working state for one elimination run (design §3).
struct NestedElimCtx<'e> {
    env: &'e Environment,
    /// Names of every block member — originals plus aux created so far.
    /// Rule 2 of the occurrence predicate: heads in this list are direct
    /// mutual references, never nested.
    block_names: Vec<Name>,
    /// The declaration's shared parameter count `p`.
    p: u32,
    /// The declaration's level parameter names (aux constants are applied at
    /// exactly these).
    level_params: Vec<Name>,
    /// First `p` Pi binders of the first type former, copied verbatim onto
    /// every aux type and aux constructor (design §1.3; INV-TEL(i)).
    telescope: Vec<(crate::expr::BinderData, Expr)>,
    /// Dedup memo: `(member, levels, canonical args)` → aux name. Entries
    /// for every sibling of a copied block are inserted at copy time.
    memo: HashMap<(Name, Vec<Level>, Vec<Expr>), Name>,
    /// Creation-ordered aux entries (drives `rec_N` numbering in restore).
    entries: Vec<NestedAuxEntry>,
    /// The growing block: originals (rewritten in place) followed by aux
    /// types in creation order. Scanned by index; grows while scanned.
    queue: Vec<InductiveType>,
    /// Next fresh-name counter (starts at 1; advances on collision probes,
    /// so suffixes are not necessarily dense — Lean parity).
    next_idx: u32,
    /// First original type name (for error payloads).
    decl_name: Name,
}

impl Environment {
    /// Eliminate nested inductive occurrences by transforming the declaration
    /// into a mutual inductive with auxiliary mirror types.
    ///
    /// Returns `Ok(None)` if the declaration has no nested occurrences,
    /// `Ok(Some(...))` with the transformed declaration and the
    /// creation-ordered aux entries (which drive `rec_N` numbering in the
    /// restore pass) otherwise.
    ///
    /// # Errors
    ///
    /// - [`InductiveError::NestedParamsContainLocals`] — a container's
    ///   parameter instantiation references a constructor-local binder
    ///   (Lean rejects identically, inductive.cpp:930-951).
    /// - [`InductiveError::NestedLevelArity`] — a container occurrence
    ///   supplies the wrong number of universe levels.
    /// - [`InductiveError::NestedAuxLimit`] — the worklist exceeded the
    ///   per-declaration aux cap (termination guarantee).
    /// - [`InductiveError::NestedRestoreInvariant`] — internal invariant
    ///   violation (a bug in this pass, not in the input).
    ///
    /// Reference: Lean 4 `elim_nested_inductive_fn` (inductive.cpp:882-1077).
    pub(crate) fn eliminate_nested_inductives(
        &self,
        decl: &InductiveDecl,
        nested_type_names: &HashSet<Name>,
    ) -> Result<Option<(InductiveDecl, Vec<NestedAuxEntry>)>, InductiveError> {
        if nested_type_names.is_empty() {
            return Ok(None);
        }

        let Some(first_type) = decl.types.first() else {
            return Ok(None);
        };

        // Copy the shared parameter telescope from the first type former
        // (design §1.3: aux domains are copied verbatim, which is what makes
        // INV-TEL(i) hold by construction).
        let mut telescope = Vec::with_capacity(decl.num_params as usize);
        let mut cursor: &Expr = &first_type.type_;
        for _ in 0..decl.num_params {
            match &cursor.kind {
                ExprKind::Pi(bi, domain, body) => {
                    telescope.push((*bi, (**domain).clone()));
                    cursor = body;
                }
                _ => return Err(InductiveError::InvalidParams),
            }
        }

        let mut ctx = NestedElimCtx {
            env: self,
            block_names: decl.types.iter().map(|t| t.name.clone()).collect(),
            p: decl.num_params,
            level_params: decl.level_params.clone(),
            telescope,
            memo: HashMap::new(),
            entries: Vec::new(),
            queue: decl.types.clone(),
            next_idx: 1,
            decl_name: first_type.name.clone(),
        };

        // Worklist fixpoint (design §3, Lean :1045-1076): the queue grows as
        // aux blocks are copied in; aux constructors are re-scanned so
        // multi-level nesting resolves fully.
        let mut qhead = 0;
        while qhead < ctx.queue.len() {
            let ctors = std::mem::take(&mut ctx.queue[qhead].constructors);
            let mut new_ctors = Vec::with_capacity(ctors.len());
            for ctor in ctors {
                let new_type = ctx.rewrite_ctor_type(&ctor.type_)?;
                new_ctors.push(Constructor {
                    name: ctor.name,
                    type_: new_type,
                });
            }
            ctx.queue[qhead].constructors = new_ctors;
            qhead += 1;
        }

        if ctx.entries.is_empty() {
            return Ok(None);
        }

        Ok(Some((
            InductiveDecl {
                level_params: decl.level_params.clone(),
                num_params: decl.num_params,
                types: ctx.queue,
            },
            ctx.entries,
        )))
    }
}

impl NestedElimCtx<'_> {
    /// Rewrite one constructor type: the first `p` Pi binders are the shared
    /// telescope and are rebuilt untouched (Lean strips params as fvars and
    /// scans only the remainder, inductive.cpp:1053-1073); the body is
    /// rewritten with the depth counter starting at `p`.
    fn rewrite_ctor_type(&mut self, ctor_type: &Expr) -> Result<Expr, InductiveError> {
        self.rewrite_skipping_params(ctor_type, 0)
    }

    fn rewrite_skipping_params(
        &mut self,
        e: &Expr,
        binders_seen: u32,
    ) -> Result<Expr, InductiveError> {
        if binders_seen >= self.p {
            return self.rewrite_nested(e, binders_seen);
        }
        match &e.kind {
            ExprKind::Pi(bi, domain, body) => {
                let new_body = self.rewrite_skipping_params(body, binders_seen + 1)?;
                Ok(Expr::pi(*bi, (**domain).clone(), new_body))
            }
            // Fewer binders than `num_params`: malformed constructor; leave
            // untouched for downstream validation to reject.
            _ => Ok(e.clone()),
        }
    }

    /// The single depth-tracked, top-down rewriter (design §1.2 + [R5]).
    ///
    /// `t` counts binders crossed from the constructor-type root (including
    /// the `p` parameter binders). On a match, the node is replaced and its
    /// children are NOT revisited (Lean `replace_fn` early-exit semantics).
    /// Traversal order — App fn-then-arg, Pi/Lam domain-then-body, Let
    /// type/value/body, MData/Proj descend into children — is load-bearing
    /// for aux creation order, which fixes `rec_N` numbering (design §4.3).
    fn rewrite_nested(&mut self, e: &Expr, t: u32) -> Result<Expr, InductiveError> {
        if let Some(replacement) = self.try_match_occurrence(e, t)? {
            return Ok(replacement);
        }
        match &e.kind {
            ExprKind::App(f, a) => {
                let new_f = self.rewrite_nested(f, t)?;
                let new_a = self.rewrite_nested(a, t)?;
                Ok(Expr::app(new_f, new_a))
            }
            ExprKind::Pi(bi, domain, body) => {
                let new_domain = self.rewrite_nested(domain, t)?;
                let new_body = self.rewrite_nested(body, t + 1)?;
                Ok(Expr::pi(*bi, new_domain, new_body))
            }
            ExprKind::Lam(bi, domain, body) => {
                let new_domain = self.rewrite_nested(domain, t)?;
                let new_body = self.rewrite_nested(body, t + 1)?;
                Ok(Expr::lam(*bi, new_domain, new_body))
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let new_ty = self.rewrite_nested(ty, t)?;
                let new_val = self.rewrite_nested(val, t)?;
                let new_body = self.rewrite_nested(body, t + 1)?;
                Ok(Expr::from_kind(ExprKind::Let(
                    name.clone(),
                    Arc::new(new_ty),
                    Arc::new(new_val),
                    Arc::new(new_body),
                    *non_dep,
                )))
            }
            // [R5] Lean's `replace` descends through MData and Proj
            // (replace_fn.cpp:48-55): an occurrence wholly wrapped in MData
            // IS rewritten at the inner App.
            ExprKind::MData(meta, inner) => {
                let new_inner = self.rewrite_nested(inner, t)?;
                Ok(Expr::from_kind(ExprKind::MData(
                    meta.clone(),
                    Arc::new(new_inner),
                )))
            }
            ExprKind::Proj(struct_name, idx, inner) => {
                let new_inner = self.rewrite_nested(inner, t)?;
                Ok(Expr::from_kind(ExprKind::Proj(
                    struct_name.clone(),
                    *idx,
                    Arc::new(new_inner),
                )))
            }
            _ => Ok(e.clone()),
        }
    }

    /// The occurrence predicate + replacement (design §1.2, Lean :919-992).
    ///
    /// Returns `Ok(Some(replacement))` when `e` is a nested occurrence,
    /// `Ok(None)` when it is not (traversal continues into children).
    fn try_match_occurrence(&mut self, e: &Expr, t: u32) -> Result<Option<Expr>, InductiveError> {
        // Rule 1: application spine with a bare-Const head (no whnf; a
        // MData-wrapped HEAD does not match — Lean parity; such occurrences
        // die in post-transform positivity).
        let head = e.get_app_fn();
        let ExprKind::Const(container, levels) = &head.kind else {
            return Ok(None);
        };
        // Rule 2: block members (originals and aux) are direct, never nested.
        if self.block_names.iter().any(|n| n == container) {
            return Ok(None);
        }
        let Some(container_val) = self.env.inductives.get(container) else {
            return Ok(None);
        };
        let args = e.get_app_args();
        let n = container_val.num_params as usize;
        // Rule 3: under-application over the container's params ⇒ not nested
        // (falls through to positivity if it mentions the block). A bare
        // occurrence (no args) can never instantiate params with block names.
        if args.is_empty() || args.len() < n {
            return Ok(None);
        }
        // Rule 4: only the first `n` (parameter) args are inspected.
        let mentions = args[..n]
            .iter()
            .any(|a| self.block_names.iter().any(|nm| mentions_name(a, nm)));
        if !mentions {
            return Ok(None);
        }

        if levels.len() != container_val.level_params.len() {
            return Err(InductiveError::NestedLevelArity {
                container: container.clone(),
                got: levels.len(),
                expected: container_val.level_params.len(),
            });
        }

        // Rule 5 + canonicalization: lower each parameter arg by the local
        // depth `k = t − p`. Failure means the instantiation references a
        // constructor-local binder — Lean rejects these identically.
        debug_assert!(t >= self.p, "rewriter entered above the param telescope");
        let k = t.saturating_sub(self.p);
        let mut canonical_args = Vec::with_capacity(n);
        for arg in &args[..n] {
            match arg.lower_loose_bvars(k) {
                Some(lowered) => canonical_args.push(lowered),
                None => return Err(InductiveError::NestedParamsContainLocals),
            }
        }

        let concrete_levels: Vec<Level> = levels.to_vec();
        let key = (
            container.clone(),
            concrete_levels.clone(),
            canonical_args.clone(),
        );
        let aux_name = match self.memo.get(&key) {
            Some(name) => name.clone(),
            None => {
                self.copy_container_block(container_val, &concrete_levels, &canonical_args)?;
                self.memo.get(&key).cloned().ok_or_else(|| {
                    InductiveError::NestedRestoreInvariant(format!(
                        "block copy for {container} did not register its own memo entry"
                    ))
                })?
            }
        };

        // Replacement spine (design §1.2): Aux at the declaration's level
        // params, applied to the shared params A₀…A_{p−1} = BVar(t−1)…BVar(t−p)
        // and then the occurrence's index args, transplanted verbatim (the
        // matched node's children are not revisited — Lean `replace_fn`).
        let aux_levels: Vec<Level> = self
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let mut replacement = Expr::const_(aux_name, aux_levels);
        for i in 0..self.p {
            replacement = Expr::app(replacement, Expr::bvar(t - 1 - i));
        }
        for index_arg in &args[n..] {
            replacement = Expr::app(replacement, (*index_arg).clone());
        }
        Ok(Some(replacement))
    }

    /// Copy the container's ENTIRE mutual block as aux mirrors (design §1.3,
    /// Lean :996-1026): one aux type per sibling, memo entries for every
    /// sibling inserted before constructor bodies are processed (sibling
    /// self-references inside aux ctors then memo-hit during the worklist
    /// re-scan).
    fn copy_container_block(
        &mut self,
        container_val: &InductiveVal,
        ls: &[Level],
        ds: &[Expr],
    ) -> Result<(), InductiveError> {
        // `instantiate_rev(vals)` maps BVar(depth+i) ↦ vals[i]: vals[0]
        // replaces the INNERMOST binder, so the outermost-first `ds` must be
        // passed reversed (design §1.3 ordering caveat).
        let ds_rev: Vec<Expr> = ds.iter().rev().cloned().collect();

        // Reserve aux names + memo entries for the whole block first.
        let mut planned: Vec<(Name, Name)> = Vec::with_capacity(container_val.all_names.len());
        for sibling in &container_val.all_names {
            if self.entries.len() + planned.len() >= NESTED_AUX_LIMIT {
                return Err(InductiveError::NestedAuxLimit {
                    decl: self.decl_name.clone(),
                    limit: NESTED_AUX_LIMIT,
                });
            }
            let aux_name = self.fresh_aux_name(sibling);
            self.memo.insert(
                (sibling.clone(), ls.to_vec(), ds.to_vec()),
                aux_name.clone(),
            );
            planned.push((sibling.clone(), aux_name));
        }

        for (sibling, aux_name) in planned {
            let sibling_val = self.env.inductives.get(&sibling).ok_or_else(|| {
                InductiveError::NestedRestoreInvariant(format!(
                    "mutual sibling {sibling} of a registered container is not itself registered"
                ))
            })?;
            let n = sibling_val.num_params as usize;

            // Aux type former: kill the container's level params, strip its
            // param telescope, substitute Ds′, re-wrap the OUTER telescope.
            let sibling_ty = sibling_val
                .type_
                .instantiate_level_params_direct(&sibling_val.level_params, ls);
            let stripped = strip_pi_binders(&sibling_ty, n).ok_or_else(|| {
                InductiveError::NestedRestoreInvariant(format!(
                    "container member {sibling} has fewer Pi binders than its num_params"
                ))
            })?;
            // Beta-normalize the const-map redex `(fun x => V) k ↦ V` at its
            // unique source (design 2026-07-05 §5.1): a dependent-parameter
            // container substitutes β with a const map `fun x => V`, leaving a
            // `Lam`-headed application that Clean's syntactic head-inspecting
            // passes (strict positivity, recursor-field classifier, IH-target)
            // cannot read. Lean whnfs the field at every check site; beta ⊆
            // whnf, so reducing it once here recovers Lean's verdict without
            // touching any acceptance gate. On a redex-free term (all
            // non-dependent-container families) this is the identity.
            let instantiated = stripped.instantiate_rev(&ds_rev).beta_normalize();
            let aux_type_expr = self.wrap_outer_telescope(instantiated);

            // Aux constructors: identical recipe per container ctor.
            let mut aux_ctors = Vec::with_capacity(sibling_val.constructor_names.len());
            let mut ctor_map = Vec::with_capacity(sibling_val.constructor_names.len());
            for ctor_name in &sibling_val.constructor_names {
                let ctor_val = self.env.constructors.get(ctor_name).ok_or_else(|| {
                    InductiveError::NestedRestoreInvariant(format!(
                        "constructor {ctor_name} of container member {sibling} is not registered"
                    ))
                })?;
                let ctor_ty = ctor_val
                    .type_
                    .instantiate_level_params_direct(&ctor_val.level_params, ls);
                let ctor_stripped = strip_pi_binders(&ctor_ty, n).ok_or_else(|| {
                    InductiveError::NestedRestoreInvariant(format!(
                        "constructor {ctor_name} has fewer Pi binders than its num_params"
                    ))
                })?;
                // Beta-normalize the const-map redex in the field types (the
                // dependent field `β k` becomes `(fun x => V) k`, contracted to
                // `V`); see the type-former note above (design 2026-07-05 §5.1).
                let ctor_instantiated = ctor_stripped.instantiate_rev(&ds_rev).beta_normalize();
                let aux_ctor_type = self.wrap_outer_telescope(ctor_instantiated);

                // Suffix transplant: J.c ↦ Aux.c (Lean :1016).
                let ctor_str = ctor_name.to_string();
                let suffix = ctor_str
                    .rsplit_once('.')
                    .map(|(_, s)| s)
                    .unwrap_or(&ctor_str);
                let aux_ctor_name = Name::from_string(&format!("{aux_name}.{suffix}"));
                ctor_map.push((aux_ctor_name.clone(), ctor_name.clone()));
                aux_ctors.push(Constructor {
                    name: aux_ctor_name,
                    type_: aux_ctor_type,
                });
            }

            self.queue.push(InductiveType {
                name: aux_name.clone(),
                type_: aux_type_expr,
                constructors: aux_ctors,
            });
            self.block_names.push(aux_name.clone());
            self.entries.push(NestedAuxEntry {
                aux_name,
                sibling_name: sibling,
                container_levels: ls.to_vec(),
                canonical_args: ds.to_vec(),
                ctor_map,
            });
        }
        Ok(())
    }

    /// Fresh aux name `_nested.<full member name>_<idx>` with a uniqueness
    /// probe against the environment and the current block (Lean
    /// `mk_unique_name` :898-904 + `g_nested`; the counter advances on
    /// collisions, so suffixes are not necessarily dense).
    fn fresh_aux_name(&mut self, sibling: &Name) -> Name {
        loop {
            let candidate = Name::from_string(&format!("_nested.{sibling}_{}", self.next_idx));
            self.next_idx += 1;
            let taken = self.env.constants.contains_key(&candidate)
                || self.env.inductives.contains_key(&candidate)
                || self.block_names.contains(&candidate)
                || self.queue.iter().any(|t| t.name == candidate);
            if !taken {
                return candidate;
            }
        }
    }

    /// Wrap the outer declaration's `p`-binder telescope around `body`
    /// (design §1.3: the aux telescope reuses the outer telescope's shape
    /// verbatim, so `Ds′`'s loose bvars in `[0, p)` resolve to it with no
    /// further shifting).
    fn wrap_outer_telescope(&self, body: Expr) -> Expr {
        let mut result = body;
        for (bi, domain) in self.telescope.iter().rev() {
            result = Expr::pi(*bi, domain.clone(), result);
        }
        result
    }
}

/// Strip exactly `n` Pi binders, or `None` if there are fewer.
pub(super) fn strip_pi_binders(e: &Expr, n: usize) -> Option<Expr> {
    let mut cursor = e;
    for _ in 0..n {
        match &cursor.kind {
            ExprKind::Pi(_, _, body) => cursor = body,
            _ => return None,
        }
    }
    Some(cursor.clone())
}

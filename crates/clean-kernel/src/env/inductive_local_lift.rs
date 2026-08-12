// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nested-local lifting — a Clean EXTENSION (not Lean parity) that accepts
//! nested inductive occurrences whose parameter instantiation captures
//! constructor-local binders: the exact shape Lean 4 rejects with
//! `NestedParamsContainLocals` (inductive.cpp:930-951) and Rocq accepts
//! natively (`designs/2026-07-29-rocq-features-into-clean.md`, rung 2).
//!
//! For example (Rocq's `Forall₂`-with-`∧` pattern, minimized):
//! ```text
//! inductive Wrap (P : Nat → Prop) : Prop
//!   | mk : P 0 → Wrap P
//! inductive Bad : Nat → Prop
//!   | step : (n : Nat) → Wrap (fun m => Bad (n + m)) → Bad n   -- Lean: rejected
//! ```
//! The `Wrap` occurrence instantiates `P` with a term capturing the local
//! `n`, so the standard nested-inductive elimination cannot canonicalize it
//! into a depth-independent aux type. This pass instead SPECIALIZES the
//! occurrence: the captured locals become leading INDICES of a fresh aux
//! family, and the occurrence is replaced by that family applied to them:
//! ```text
//! mutual
//!   inductive Bad : Nat → Prop
//!     | step : (n : Nat) → _lifted.Wrap_1 n → Bad n
//!   inductive _lifted.Wrap_1 : Nat → Prop
//!     | mk : (n : Nat) → Bad (n + 0) → _lifted.Wrap_1 n
//! end
//! ```
//!
//! Division of labor with [`super::inductive_nested_elim`]: occurrences whose
//! params mention block members WITHOUT capturing locals are left untouched
//! here — the kernel's Lean-parity elimination (with its restore pass)
//! handles them when the lifted block is re-submitted. This pass lifts ONLY
//! the capturing occurrences, i.e. exactly what Lean cannot express.
//!
//! Trust posture: NON-trust-bearing. The pass is invoked by the elaborator as
//! an opt-in retry (`set_option clean.inductive.liftNestedLocals true`) after
//! `add_inductive` fails; its output is an ordinary mutual `InductiveDecl`
//! that the kernel re-checks from scratch (positivity, universes, recursors).
//! A bug here can only produce a rejected declaration or a differently-shaped
//! accepted one — never an unchecked acceptance.
//!
//! v1 scope gates (each refusal is a loud [`LocalLiftError::Unsupported`]):
//! the declaration must have `num_params == 0` and no universe params; the
//! captured locals' types must be closed non-`let` binders; the container
//! must be a single (non-mutual) inductive whose specialized family lands in
//! `Prop`.

use std::collections::HashMap;

use crate::expr::{BinderData, Expr, ExprKind};
use crate::inductive::{mentions_name, Constructor, InductiveDecl, InductiveType, InductiveVal};
use crate::level::Level;
use crate::name::Name;

use super::inductive_nested_elim::strip_pi_binders;
use super::Environment;

/// Per-declaration cap on lifted aux families (termination guarantee for the
/// worklist fixpoint, mirroring `NESTED_AUX_LIMIT`). Deliberately tighter
/// than the nested-elim cap: capture chains beyond a handful of families are
/// not a shape v1 claims to support. Recorded in
/// `docs/JUSTIFIED_EXCEPTIONS.md`.
const LOCAL_LIFT_AUX_LIMIT: usize = 16;

/// Result of a successful lift: the fully-mutual declaration (originals with
/// capturing occurrences rewritten, followed by the lifted aux families in
/// creation order) plus the aux names for caller diagnostics.
#[derive(Debug, Clone)]
pub struct LocalLift {
    /// The rewritten declaration, ready for `add_inductive`.
    pub decl: InductiveDecl,
    /// Names of the lifted aux families (`_lifted.<container>_<idx>`).
    pub aux_names: Vec<Name>,
    /// Per-family synthesis records, in creation order
    /// (`families[i].aux_name == aux_names[i]`). Consumed by the round-trip
    /// guard and the bridge synthesizer (rung P3).
    pub families: Vec<LiftedFamilyInfo>,
}

/// Everything the round-trip guard and the bridge synthesizer need about one
/// lifted aux family, captured at synthesis time (the analog of
/// `NestedAuxEntry` for the nested-elim restore pass). The `canonical_args`
/// are verbatim (bvar-renumbered only) subterms of the PRE-rewrite spelling,
/// so bridge statements built from them show the user's original vocabulary.
#[derive(Debug, Clone)]
pub struct LiftedFamilyInfo {
    /// Fresh family name (`_lifted.<container>_<idx>`).
    pub aux_name: Name,
    /// The container this family specializes (single member; v1 gate).
    pub container: Name,
    /// Concrete levels at the matched occurrence.
    pub container_levels: Vec<Level>,
    /// The container's `n` param args in the minimal ℓ-context: loose bvars
    /// `m-1 … 0` address the ℓ-telescope outermost-first.
    pub canonical_args: Vec<Expr>,
    /// The `m` CLOSED captured-local types, outermost-first (the ℓ-telescope).
    pub captured_tys: Vec<Expr>,
    /// The container's param count `n` as used at match time (pinned; do not
    /// re-read the live container later).
    pub container_num_params: u32,
    /// The container's residual index arity `k` as used at match time.
    pub container_num_indices: u32,
    /// The synthesized family former: `m` ℓ-Pis, then `k` index Pis, then
    /// `Sort 0`. Registration's fixed-index promotion may re-split the
    /// param/index COUNTERS but never respells this telescope.
    pub aux_type: Expr,
    /// Aux constructor name → container constructor name, in ctor order.
    pub ctor_map: Vec<(Name, Name)>,
}

/// Errors from [`Environment::lift_nested_locals`]. Every variant is a
/// REFUSAL (the declaration is left untouched); none of them can register
/// anything.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LocalLiftError {
    /// The declaration or occurrence falls outside the v1 lift fragment.
    #[error("nested-local lift does not support {what}")]
    Unsupported {
        /// Human-readable description of the unsupported shape.
        what: String,
    },
    /// The worklist exceeded the per-declaration aux-family cap.
    #[error("nested-local lift exceeded the aux-family cap ({limit}) for {decl}")]
    AuxLimit {
        /// First type name of the declaration being lifted.
        decl: Name,
        /// The cap that was hit ([`LOCAL_LIFT_AUX_LIMIT`]).
        limit: usize,
    },
    /// No capturing occurrence was found — the caller's failure has another
    /// cause and the original error should be surfaced instead.
    #[error("nested-local lift found no local-capturing nested occurrence")]
    NothingToLift,
    /// Internal invariant violation (a bug in this pass, not in the input).
    #[error("nested-local lift invariant violated: {0}")]
    Invariant(String),
    /// The round-trip guard found the registered family disagreeing with its
    /// synthesis record — evidence of record drift or an in-registration
    /// respelling, either of which indicts the lift, never the kernel.
    #[error(
        "nested-local lift round-trip guard: re-derived type differs from the \
         registered one for {family}{}",
        ctor.as_ref().map(|c| format!(" (constructor {c})")).unwrap_or_default()
    )]
    RoundTrip {
        /// The family whose record failed to reproduce the registered type.
        family: Name,
        /// The specific constructor, when the mismatch is constructor-level.
        ctor: Option<Name>,
    },
}

/// A binder crossed by the rewriter, innermost last. `Typed` carries the
/// (already-rewritten) domain of a `Pi`/`Lam` binder; `Let`-bound locals
/// cannot be lifted (their value would have to travel with the type).
enum CrossedBinder {
    Typed(Expr),
    Opaque,
}

/// Dedup key: `(container, levels, canonical args, captured-local types)`.
/// The canonical args are remapped into the minimal ℓ-context (captured
/// locals renumbered `m-1 … 0` outermost-first), which makes the key — and
/// therefore the memo — depth-independent across occurrence sites. The
/// coherence between the original site and the aux-constructor re-scan site
/// is what collapses the fixpoint (a miss there would mint a redundant
/// duplicate family, bounded by the cap, never an unsound one).
type LiftKey = (Name, Vec<Level>, Vec<Expr>, Vec<Expr>);

struct LocalLiftCtx<'e> {
    env: &'e Environment,
    /// Every block member — originals plus aux created so far. Heads in this
    /// list are direct mutual references, never nested (Rule 2).
    block_names: Vec<Name>,
    memo: HashMap<LiftKey, Name>,
    /// Lifted aux names in creation order.
    aux_names: Vec<Name>,
    /// Per-family synthesis records, in creation order.
    families: Vec<LiftedFamilyInfo>,
    /// The growing block: originals (rewritten in place) followed by aux
    /// families. Scanned by index; grows while scanned.
    queue: Vec<InductiveType>,
    /// Fresh-name counter (advances on collision probes).
    next_idx: u32,
    /// First original type name (for error payloads).
    decl_name: Name,
    /// SEALED mode (round-trip guard): the memo is pre-seeded from stored
    /// records and every occurrence must memo-hit — a synthesis attempt means
    /// the record no longer explains the registered block and is an immediate
    /// round-trip failure (it would otherwise silently mint a fresh family
    /// against the now-populated environment).
    sealed: bool,
}

impl Environment {
    /// Lift constructor-local binders out of local-capturing nested inductive
    /// occurrences, producing a fully-mutual declaration in which each such
    /// occurrence is replaced by a specialized aux family indexed by the
    /// captured locals.
    ///
    /// Read-only on the environment; the caller decides whether to submit
    /// the returned declaration through the ordinary checked
    /// [`Environment::add_inductive`] path.
    ///
    /// # Errors
    ///
    /// [`LocalLiftError::Unsupported`] for shapes outside the v1 fragment,
    /// [`LocalLiftError::AuxLimit`] when the worklist exceeds the family cap,
    /// [`LocalLiftError::NothingToLift`] when no capturing occurrence exists,
    /// [`LocalLiftError::Invariant`] on internal bugs.
    pub fn lift_nested_locals(&self, decl: &InductiveDecl) -> Result<LocalLift, LocalLiftError> {
        if decl.num_params != 0 {
            return Err(LocalLiftError::Unsupported {
                what: format!(
                    "parameterized declarations (num_params = {}; v1 lifts only 0-param blocks)",
                    decl.num_params
                ),
            });
        }
        if !decl.level_params.is_empty() {
            return Err(LocalLiftError::Unsupported {
                what: "universe-polymorphic declarations".to_string(),
            });
        }
        let Some(first_type) = decl.types.first() else {
            return Err(LocalLiftError::NothingToLift);
        };

        let mut ctx = LocalLiftCtx {
            env: self,
            block_names: decl.types.iter().map(|t| t.name.clone()).collect(),
            memo: HashMap::new(),
            aux_names: Vec::new(),
            families: Vec::new(),
            queue: decl.types.clone(),
            next_idx: 1,
            decl_name: first_type.name.clone(),
            sealed: false,
        };

        // Worklist fixpoint: aux-family constructors are themselves
        // re-scanned (the queue grows while scanned), so captures that only
        // materialize after container-parameter substitution + beta — e.g.
        // `R a b ↦ And … (Bad …)` — are discovered and lifted too.
        let mut qhead = 0;
        while qhead < ctx.queue.len() {
            let ctors = std::mem::take(&mut ctx.queue[qhead].constructors);
            let mut new_ctors = Vec::with_capacity(ctors.len());
            for ctor in ctors {
                let mut binders = Vec::new();
                let new_type = ctx.rewrite(&ctor.type_, &mut binders)?;
                new_ctors.push(Constructor {
                    name: ctor.name,
                    type_: new_type,
                });
            }
            ctx.queue[qhead].constructors = new_ctors;
            qhead += 1;
        }

        if ctx.aux_names.is_empty() {
            return Err(LocalLiftError::NothingToLift);
        }

        Ok(LocalLift {
            decl: InductiveDecl {
                level_params: Vec::new(),
                num_params: 0,
                types: ctx.queue,
            },
            aux_names: ctx.aux_names,
            families: ctx.families,
        })
    }

    /// Round-trip guard for a REGISTERED lifted block: re-derive every aux
    /// family former and constructor type from its synthesis record — via the
    /// pass's own recipe (level-instantiate, strip, substitute, beta, wrap,
    /// rewrite in SEALED mode) so there is exactly one recipe and one drift
    /// point — and require syntactic (`Expr ==`) agreement with what the
    /// environment actually stores. Definitional equality would mask
    /// transform bugs; promotion only re-splits the param/index counters,
    /// never the telescope, so syntactic agreement is the right bar.
    ///
    /// `decl` is the ORIGINAL (pre-lift) declaration — its member names seed
    /// the sealed rewriter's block list exactly as the live run's did.
    ///
    /// # Errors
    ///
    /// [`LocalLiftError::RoundTrip`] on any disagreement,
    /// [`LocalLiftError::Invariant`] when the environment is missing pieces
    /// the records reference (a caller-order bug).
    pub fn verify_local_lift_anchor(
        &self,
        decl: &InductiveDecl,
        families: &[LiftedFamilyInfo],
    ) -> Result<(), LocalLiftError> {
        let mut block_names: Vec<Name> = decl.types.iter().map(|t| t.name.clone()).collect();
        block_names.extend(families.iter().map(|f| f.aux_name.clone()));
        let mut memo = HashMap::new();
        for f in families {
            memo.insert(
                (
                    f.container.clone(),
                    f.container_levels.clone(),
                    f.canonical_args.clone(),
                    f.captured_tys.clone(),
                ),
                f.aux_name.clone(),
            );
        }
        let mut ctx = LocalLiftCtx {
            env: self,
            block_names,
            memo,
            aux_names: Vec::new(),
            families: Vec::new(),
            queue: Vec::new(),
            next_idx: 1,
            decl_name: decl
                .types
                .first()
                .map(|t| t.name.clone())
                .unwrap_or_else(|| Name::from_string("<empty>")),
            sealed: true,
        };

        for f in families {
            let m = f.captured_tys.len() as u32;
            let k = f.container_num_indices;
            let stored = self.inductives.get(&f.aux_name).ok_or_else(|| {
                LocalLiftError::Invariant(format!(
                    "round-trip guard ran before {} was registered",
                    f.aux_name
                ))
            })?;
            // Boundary coherence: fixed-index promotion moves the split,
            // never the telescope.
            if stored.num_params + stored.num_indices != m + k || stored.type_ != f.aux_type {
                return Err(LocalLiftError::RoundTrip {
                    family: f.aux_name.clone(),
                    ctor: None,
                });
            }
            let args_rev: Vec<Expr> = f.canonical_args.iter().rev().cloned().collect();
            for (aux_ctor, container_ctor) in &f.ctor_map {
                let ctor_val = self.constructors.get(container_ctor).ok_or_else(|| {
                    LocalLiftError::Invariant(format!(
                        "container constructor {container_ctor} disappeared from the environment"
                    ))
                })?;
                let ctor_ty = ctor_val
                    .type_
                    .instantiate_level_params_direct(&ctor_val.level_params, &f.container_levels);
                let stripped = strip_pi_binders(&ctor_ty, f.container_num_params as usize)
                    .ok_or_else(|| LocalLiftError::RoundTrip {
                        family: f.aux_name.clone(),
                        ctor: Some(aux_ctor.clone()),
                    })?;
                let instantiated = stripped.instantiate_rev(&args_rev).beta_normalize();
                let wrapped = wrap_index_telescope(&f.captured_tys, instantiated);
                let mut binders = Vec::new();
                let rederived =
                    ctx.rewrite(&wrapped, &mut binders)
                        .map_err(|_| LocalLiftError::RoundTrip {
                            family: f.aux_name.clone(),
                            ctor: Some(aux_ctor.clone()),
                        })?;
                let registered = self.constructors.get(aux_ctor).ok_or_else(|| {
                    LocalLiftError::Invariant(format!(
                        "aux constructor {aux_ctor} is not registered"
                    ))
                })?;
                if rederived != registered.type_ {
                    return Err(LocalLiftError::RoundTrip {
                        family: f.aux_name.clone(),
                        ctor: Some(aux_ctor.clone()),
                    });
                }
            }
        }
        Ok(())
    }
}

impl LocalLiftCtx<'_> {
    /// Top-down rewriter with a crossed-binder stack (depth =
    /// `binders.len()`). On a match the node is replaced and its children are
    /// NOT revisited (same early-exit semantics as the nested-elim rewriter);
    /// traversal covers exactly the node shapes that pass descends into.
    fn rewrite(
        &mut self,
        e: &Expr,
        binders: &mut Vec<CrossedBinder>,
    ) -> Result<Expr, LocalLiftError> {
        if let Some(replacement) = self.try_match_occurrence(e, binders)? {
            return Ok(replacement);
        }
        match &e.kind {
            ExprKind::App(f, a) => {
                let new_f = self.rewrite(f, binders)?;
                let new_a = self.rewrite(a, binders)?;
                Ok(Expr::app(new_f, new_a))
            }
            ExprKind::Pi(bi, domain, body) => {
                let new_domain = self.rewrite(domain, binders)?;
                binders.push(CrossedBinder::Typed(new_domain.clone()));
                let new_body = self.rewrite(body, binders)?;
                binders.pop();
                Ok(Expr::pi(*bi, new_domain, new_body))
            }
            ExprKind::Lam(bi, domain, body) => {
                let new_domain = self.rewrite(domain, binders)?;
                binders.push(CrossedBinder::Typed(new_domain.clone()));
                let new_body = self.rewrite(body, binders)?;
                binders.pop();
                Ok(Expr::lam(*bi, new_domain, new_body))
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let new_ty = self.rewrite(ty, binders)?;
                let new_val = self.rewrite(val, binders)?;
                binders.push(CrossedBinder::Opaque);
                let new_body = self.rewrite(body, binders)?;
                binders.pop();
                Ok(Expr::let_named(
                    name.clone(),
                    new_ty,
                    new_val,
                    new_body,
                    *non_dep,
                ))
            }
            ExprKind::MData(meta, inner) => {
                let new_inner = self.rewrite(inner, binders)?;
                Ok(Expr::from_kind(ExprKind::MData(
                    meta.clone(),
                    std::sync::Arc::new(new_inner),
                )))
            }
            ExprKind::Proj(struct_name, idx, inner) => {
                let new_inner = self.rewrite(inner, binders)?;
                Ok(Expr::from_kind(ExprKind::Proj(
                    struct_name.clone(),
                    *idx,
                    std::sync::Arc::new(new_inner),
                )))
            }
            _ => Ok(e.clone()),
        }
    }

    /// The occurrence predicate + replacement. Returns `Ok(Some(_))` only for
    /// a LOCAL-CAPTURING nested occurrence; capture-free nested occurrences
    /// return `Ok(None)` and are left for the kernel's Lean-parity
    /// elimination when the lifted block is re-submitted.
    fn try_match_occurrence(
        &mut self,
        e: &Expr,
        binders: &[CrossedBinder],
    ) -> Result<Option<Expr>, LocalLiftError> {
        let head = e.get_app_fn();
        let ExprKind::Const(container, levels) = &head.kind else {
            return Ok(None);
        };
        if self.block_names.iter().any(|n| n == container) {
            return Ok(None);
        }
        let Some(container_val) = self.env.inductives.get(container) else {
            return Ok(None);
        };
        let args = e.get_app_args();
        let n = container_val.num_params as usize;
        if args.is_empty() || args.len() < n {
            return Ok(None);
        }
        let mentions = args[..n]
            .iter()
            .any(|a| self.block_names.iter().any(|nm| mentions_name(a, nm)));
        if !mentions {
            return Ok(None);
        }

        // Captured locals: loose bvars of the param args, outermost first
        // (descending index order = ℓ-telescope order).
        let k = u32::try_from(binders.len())
            .map_err(|_| LocalLiftError::Invariant("binder depth exceeds u32".to_string()))?;
        let captured: Vec<u32> = (0..k)
            .rev()
            .filter(|&j| args[..n].iter().any(|a| a.has_loose_bvar(j)))
            .collect();
        if captured.is_empty() {
            // Capture-free nested occurrence: the standard elimination
            // handles it (with restore) — not this pass's business.
            return Ok(None);
        }

        if container_val.all_names.len() != 1 {
            return Err(LocalLiftError::Unsupported {
                what: format!("capturing occurrence of mutual container block {container}"),
            });
        }
        if levels.len() != container_val.level_params.len() {
            return Err(LocalLiftError::Unsupported {
                what: format!(
                    "container {container} applied at {} levels (expects {})",
                    levels.len(),
                    container_val.level_params.len()
                ),
            });
        }

        // Captured-local types, from the crossed-binder stack. Each must be a
        // closed non-`let` binder so it can be transplanted verbatim into the
        // aux family's leading index telescope.
        let mut captured_tys = Vec::with_capacity(captured.len());
        for &j in &captured {
            match &binders[(k - 1 - j) as usize] {
                CrossedBinder::Typed(ty) => {
                    if ty.has_loose_bvars() {
                        return Err(LocalLiftError::Unsupported {
                            what: format!(
                                "a captured local whose type depends on other locals \
                                 (in an occurrence of {container})"
                            ),
                        });
                    }
                    captured_tys.push(ty.clone());
                }
                CrossedBinder::Opaque => {
                    return Err(LocalLiftError::Unsupported {
                        what: format!(
                            "a captured let-bound local (in an occurrence of {container})"
                        ),
                    });
                }
            }
        }

        // Canonicalize the param args into the minimal ℓ-context: captured
        // local `captured[i]` becomes `BVar(m-1-i)`. `instantiate_rev(vals)`
        // maps root-relative `BVar(j) ↦ vals[j]` (lifted under inner
        // binders), which is exactly this renumbering; non-captured slots are
        // unreferenced by construction (captured = every loose bvar).
        let m = u32::try_from(captured.len())
            .map_err(|_| LocalLiftError::Invariant("captured count exceeds u32".to_string()))?;
        let mut vals: Vec<Expr> = (0..k).map(|_| Expr::bvar(0)).collect();
        for (i, &j) in captured.iter().enumerate() {
            let i = u32::try_from(i)
                .map_err(|_| LocalLiftError::Invariant("capture index exceeds u32".to_string()))?;
            vals[j as usize] = Expr::bvar(m - 1 - i);
        }
        let canonical_args: Vec<Expr> = args[..n]
            .iter()
            .map(|arg| arg.instantiate_rev(&vals))
            .collect();

        let concrete_levels: Vec<Level> = levels.to_vec();
        let key = (
            container.clone(),
            concrete_levels.clone(),
            canonical_args.clone(),
            captured_tys.clone(),
        );
        let aux_name = match self.memo.get(&key) {
            Some(name) => name.clone(),
            None => self.synthesize_aux_family(
                container_val,
                &concrete_levels,
                &canonical_args,
                &captured_tys,
                key,
            )?,
        };

        // Replacement: the aux family applied to the captured locals at their
        // ORIGINAL indices (outermost first, matching the ℓ-telescope), then
        // the occurrence's index args transplanted verbatim (children of a
        // matched node are not revisited).
        let mut replacement = Expr::const_(aux_name, Vec::new());
        for &j in &captured {
            replacement = Expr::app(replacement, Expr::bvar(j));
        }
        for index_arg in &args[n..] {
            replacement = Expr::app(replacement, (*index_arg).clone());
        }
        Ok(Some(replacement))
    }

    /// Build the specialized aux family for one canonical capture: level-
    /// instantiate the container's type former and constructors, strip the
    /// container's param telescope, substitute the canonical args (whose
    /// loose bvars address the ℓ-telescope), beta-normalize (contracting
    /// `(fun x => V) a` param applications — the step that surfaces
    /// second-round captures), and wrap the ℓ-telescope of captured-local
    /// types. The family is pushed onto the worklist queue, so its
    /// constructors are re-scanned; its own recursive container occurrences
    /// memo-hit this entry (depth-canonical coherence).
    fn synthesize_aux_family(
        &mut self,
        container_val: &InductiveVal,
        ls: &[Level],
        canonical_args: &[Expr],
        captured_tys: &[Expr],
        key: LiftKey,
    ) -> Result<Name, LocalLiftError> {
        if self.sealed {
            // Round-trip guard mode: every occurrence must memo-hit; needing
            // a NEW family means the records no longer explain the block.
            return Err(LocalLiftError::RoundTrip {
                family: container_val.name.clone(),
                ctor: None,
            });
        }
        if self.aux_names.len() >= LOCAL_LIFT_AUX_LIMIT {
            return Err(LocalLiftError::AuxLimit {
                decl: self.decl_name.clone(),
                limit: LOCAL_LIFT_AUX_LIMIT,
            });
        }
        let container = &container_val.name;
        let n = container_val.num_params as usize;
        // `instantiate_rev(vals)` maps `BVar(i) ↦ vals[i]` with vals[0] the
        // INNERMOST binder; canonical args are outermost-first, so reverse.
        let args_rev: Vec<Expr> = canonical_args.iter().rev().cloned().collect();

        let former_ty = container_val
            .type_
            .instantiate_level_params_direct(&container_val.level_params, ls);
        let stripped = strip_pi_binders(&former_ty, n).ok_or_else(|| {
            LocalLiftError::Invariant(format!(
                "container {container} has fewer Pi binders than its num_params"
            ))
        })?;
        let instantiated = stripped.instantiate_rev(&args_rev).beta_normalize();
        let aux_ty = wrap_index_telescope(captured_tys, instantiated);

        // v1 Prop gate: the specialized family must land in Prop (mixed-sort
        // mutual blocks and Type-level specialization are out of scope).
        if !matches!(&final_codomain(&aux_ty).kind, ExprKind::Sort(l) if l.is_zero()) {
            return Err(LocalLiftError::Unsupported {
                what: format!("lifting non-Prop container {container} (v1 is Prop-only)"),
            });
        }

        let aux_name = self.fresh_aux_name(container);
        self.memo.insert(key, aux_name.clone());

        let mut aux_ctors = Vec::with_capacity(container_val.constructor_names.len());
        let mut ctor_map = Vec::with_capacity(container_val.constructor_names.len());
        for ctor_name in &container_val.constructor_names {
            let ctor_val = self.env.constructors.get(ctor_name).ok_or_else(|| {
                LocalLiftError::Invariant(format!(
                    "constructor {ctor_name} of container {container} is not registered"
                ))
            })?;
            let ctor_ty = ctor_val
                .type_
                .instantiate_level_params_direct(&ctor_val.level_params, ls);
            let ctor_stripped = strip_pi_binders(&ctor_ty, n).ok_or_else(|| {
                LocalLiftError::Invariant(format!(
                    "constructor {ctor_name} has fewer Pi binders than its num_params"
                ))
            })?;
            let ctor_instantiated = ctor_stripped.instantiate_rev(&args_rev).beta_normalize();
            let aux_ctor_ty = wrap_index_telescope(captured_tys, ctor_instantiated);

            // Suffix transplant: Container.c ↦ Aux.c.
            let ctor_str = ctor_name.to_string();
            let suffix = ctor_str
                .rsplit_once('.')
                .map(|(_, s)| s)
                .unwrap_or(&ctor_str);
            let aux_ctor_name = Name::from_string(&format!("{aux_name}.{suffix}"));
            ctor_map.push((aux_ctor_name.clone(), ctor_name.clone()));
            aux_ctors.push(Constructor {
                name: aux_ctor_name,
                type_: aux_ctor_ty,
            });
        }

        self.families.push(LiftedFamilyInfo {
            aux_name: aux_name.clone(),
            container: container.clone(),
            container_levels: ls.to_vec(),
            canonical_args: canonical_args.to_vec(),
            captured_tys: captured_tys.to_vec(),
            container_num_params: container_val.num_params,
            container_num_indices: container_val.num_indices,
            aux_type: aux_ty.clone(),
            ctor_map,
        });
        self.queue.push(InductiveType {
            name: aux_name.clone(),
            type_: aux_ty,
            constructors: aux_ctors,
        });
        self.block_names.push(aux_name.clone());
        self.aux_names.push(aux_name.clone());
        Ok(aux_name)
    }

    /// Fresh aux name `_lifted.<container>_<idx>` with a uniqueness probe
    /// against the environment and the current block.
    fn fresh_aux_name(&mut self, container: &Name) -> Name {
        loop {
            let candidate = Name::from_string(&format!("_lifted.{container}_{}", self.next_idx));
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
}

/// Wrap the captured-local types as leading Pi binders (all closed, so no
/// lifting is required; `body`'s loose bvars `[0, m)` address them).
fn wrap_index_telescope(captured_tys: &[Expr], body: Expr) -> Expr {
    let mut result = body;
    for ty in captured_tys.iter().rev() {
        result = Expr::pi(BinderData::default(), ty.clone(), result);
    }
    result
}

/// Final codomain of a Pi telescope (the expression after every binder).
fn final_codomain(e: &Expr) -> &Expr {
    let mut cursor = e;
    while let ExprKind::Pi(_, _, body) = &cursor.kind {
        cursor = body;
    }
    cursor
}

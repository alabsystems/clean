// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration addition with validation.
//!
//! Extracted from env/mod.rs for maintainability (see #307).
//! Contains `add_decl` (full type checking), `add_decl_if_absent` (skip
//! duplicates from .olean), `add_decl_unchecked` (trusted), and
//! `add_decl_structural` (structural validation only), plus the
//! `find_undef_level_param` helper functions they share.

use std::cell::Cell;

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

use super::types::{ConstantInfo, ConstantKind, Declaration, EnvError, Reducibility};
use super::Environment;

thread_local! {
    /// Metamath two-pass PASS-1 flag. When `true`, `add_decl` converts an
    /// incoming `Declaration::Theorem` into a `Declaration::Axiom` (DROPPING the
    /// proof value) BEFORE the dedup/type-check — so the theorem's schematic TYPE
    /// is registered as an axiom and the (expensive) proof check is SKIPPED.
    ///
    /// SOUNDNESS: this is a VERIFICATION-SKIP mode and, on its own, is UNSOUND — it
    /// admits a theorem's type without ever checking its proof. It is sound ONLY
    /// inside the Metamath two-pass verifier (`kernel_verify_two_pass_range`):
    ///   PASS 1 registers EVERY `$p` theorem's type as an axiom under this flag,
    ///           building the full type environment but PROVING NOTHING; pass-1
    ///           NEVER adds any theorem to `report.verified`.
    ///   PASS 2 turns the flag OFF, then for each theorem in its assigned range
    ///           `forget_decl`s the pass-1 axiom and re-adds it as a real
    ///           `Declaration::Theorem` — so `add_decl` TYPE-CHECKS the proof
    ///           against the pass-1 axiom environment. A theorem is added to
    ///           `report.verified` ONLY when pass-2's checked add succeeds.
    /// Only pass-2-verified theorems are ever exported as `KernelVerified`; the
    /// pass-1 axioms are scaffolding dependency-types that workers reuse. Across
    /// all ranges every `$p` theorem is re-verified by some worker, so the union
    /// of the per-range verified sets is exactly the set whose proofs the kernel
    /// checked. The flag is thread-local, so parallel pass-2 workers (each its own
    /// thread/process) never interfere; the default `false` keeps every other
    /// `add_decl` caller (the whole rest of the kernel) on the checked path.
    static MM_AXIOM_ONLY: Cell<bool> = const { Cell::new(false) };

    /// Pillar-1 gap G1 SENTINEL — proves the CURRENT THREAD is executing inside
    /// the sanctioned Metamath two-pass verifier (`kernel_verify_two_pass_range`).
    ///
    /// SOUNDNESS: `MM_AXIOM_ONLY` on its own is a verification-SKIP flag — the
    /// `add_decl` fast path it enables drops a `Theorem`'s proof value UNCHECKED
    /// and registers only its type. That is sound ONLY because the two-pass
    /// re-verifies every proof in PASS-2 and exports only PASS-2-verified results.
    /// Nothing but the flag guarded that discipline: any code that called
    /// `set_mm_axiom_only(true)` could smuggle a False-typed axiom in unchecked.
    /// This sentinel closes the hole: the proof-drop path now ALSO requires the
    /// two-pass to have established this sentinel via [`MmAxiomOnlyGuard`] (the
    /// RAII guard that owns the flag's lifetime). Absent the sentinel, the fast
    /// path FAILS CLOSED to `EnvError::AxiomOnlyMisuse` instead of dropping the
    /// value. The guard depth is a counter (not a bool) so nested/re-entrant
    /// two-pass scopes compose correctly.
    static MM_TWO_PASS_ACTIVE: Cell<u32> = const { Cell::new(0) };
}

/// Set the Metamath two-pass PASS-1 axiom-only flag for the CURRENT THREAD.
/// See [`MM_AXIOM_ONLY`]. MUST be reset to `false` before pass-2 verifies proofs.
///
/// NOTE (Pillar-1 G1): setting this flag `true` is NO LONGER sufficient to make
/// the `add_decl` proof-drop fast path fire. The caller must ALSO hold an
/// [`MmAxiomOnlyGuard`] (which establishes the two-pass sentinel); otherwise the
/// fast path fails closed with [`EnvError::AxiomOnlyMisuse`]. The two-pass
/// verifier constructs the guard for its whole run, so the sound path is
/// unaffected.
pub fn set_mm_axiom_only(on: bool) {
    MM_AXIOM_ONLY.with(|c| c.set(on));
}

/// Whether the current thread is in Metamath PASS-1 axiom-only mode.
#[must_use]
pub fn mm_axiom_only() -> bool {
    MM_AXIOM_ONLY.with(Cell::get)
}

/// Whether the current thread is provably inside a sanctioned Metamath two-pass
/// scope (i.e. an [`MmAxiomOnlyGuard`] is live). See [`MM_TWO_PASS_ACTIVE`].
#[must_use]
pub fn mm_two_pass_active() -> bool {
    MM_TWO_PASS_ACTIVE.with(|c| c.get() > 0)
}

/// RAII guard that marks the CURRENT THREAD as executing inside the sanctioned
/// Metamath two-pass verifier for its lifetime, establishing the G1 sentinel that
/// authorizes the `add_decl` axiom-only proof-drop fast path.
///
/// The two-pass verifier (`clean-olean`'s `kernel_verify_two_pass_range`) holds
/// one of these for its entire run — the same scope over which it toggles
/// [`set_mm_axiom_only`]. Construct it BEFORE any `set_mm_axiom_only(true)`; on
/// drop it decrements the sentinel AND clears the axiom-only flag, so the flag
/// can never leak ON past a completed (or `?`-early-returned) two-pass scope.
///
/// SOUNDNESS: this guard does not itself weaken any check — it is the token that
/// distinguishes "inside the two-pass, where PASS-2 re-verifies every proof" from
/// "a stray `set_mm_axiom_only(true)` elsewhere". Without it the proof-drop path
/// fails closed (G1). See [`MM_TWO_PASS_ACTIVE`].
#[must_use = "the guard must be held for the two-pass scope; dropping it immediately \
              clears the sentinel"]
#[derive(Debug)]
pub struct MmAxiomOnlyGuard {
    // Not `Send`/`Sync`-relevant: the sentinel is thread-local. Zero-sized.
    _private: (),
}

impl MmAxiomOnlyGuard {
    /// Enter a sanctioned two-pass scope on the current thread. The returned
    /// guard is `#[must_use]` (via the type): dropping it immediately clears the
    /// sentinel and the axiom-only flag.
    pub fn enter() -> Self {
        MM_TWO_PASS_ACTIVE.with(|c| c.set(c.get().saturating_add(1)));
        Self { _private: () }
    }
}

impl Drop for MmAxiomOnlyGuard {
    fn drop(&mut self) {
        // Decrement the sentinel and, when the outermost guard exits, force the
        // axiom-only flag OFF so it can never leak into later checked work.
        MM_TWO_PASS_ACTIVE.with(|c| {
            let next = c.get().saturating_sub(1);
            c.set(next);
            if next == 0 {
                MM_AXIOM_ONLY.with(|f| f.set(false));
            }
        });
    }
}

/// Find an undefined Level::Param in a level expression.
/// Returns the first Param name not in `allowed`.
fn find_undef_level_param_in_level(l: &Level, allowed: &[Name]) -> Option<Name> {
    let mut level_stack = vec![l];
    while let Some(curr) = level_stack.pop() {
        match curr {
            Level::Zero => {}
            Level::Param(n) => {
                if !allowed.contains(n) {
                    return Some(n.clone());
                }
            }
            Level::Succ(inner) => level_stack.push(inner),
            Level::Max(a, b) | Level::IMax(a, b) => {
                level_stack.push(b);
                level_stack.push(a);
            }
        }
    }
    None
}

/// Find an undefined Level::Param in an expression.
/// Returns the first Param name referenced in Sort or Const levels
/// that is not in `allowed`.
/// Lean 4: get_undef_param in level.cpp, called by check_level in type_checker.cpp
pub(super) fn find_undef_level_param(e: &Expr, allowed: &[Name]) -> Option<Name> {
    use crate::expr::ZFCSetExpr;
    let mut expr_stack = vec![e];
    while let Some(curr) = expr_stack.pop() {
        match curr.kind() {
            ExprKind::Sort(l) => {
                if let Some(undef) = find_undef_level_param_in_level(l, allowed) {
                    return Some(undef);
                }
            }
            ExprKind::Const(_, levels) => {
                for l in levels {
                    if let Some(undef) = find_undef_level_param_in_level(l, allowed) {
                        return Some(undef);
                    }
                }
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                expr_stack.push(a);
                expr_stack.push(f);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                expr_stack.push(body);
                expr_stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                expr_stack.push(body);
                expr_stack.push(val);
                expr_stack.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                expr_stack.push(inner);
            }
            ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
            ExprKind::CubicalPath { ty, left, right } => {
                expr_stack.push(right);
                expr_stack.push(left);
                expr_stack.push(ty);
            }
            ExprKind::CubicalPathLam { body } => expr_stack.push(body),
            ExprKind::CubicalPathApp { path, arg } => {
                expr_stack.push(arg);
                expr_stack.push(path);
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                expr_stack.push(base);
                expr_stack.push(u);
                expr_stack.push(phi);
                expr_stack.push(ty);
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                expr_stack.push(base);
                expr_stack.push(phi);
                expr_stack.push(ty);
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                expr_stack.push(base);
                expr_stack.push(s);
                expr_stack.push(r);
                expr_stack.push(ty);
            }
            ExprKind::ZFCSet(set_expr) => match set_expr {
                ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
                ZFCSetExpr::Singleton(a)
                | ZFCSetExpr::Union(a)
                | ZFCSetExpr::PowerSet(a)
                | ZFCSetExpr::Choice(a) => expr_stack.push(a),
                ZFCSetExpr::Pair(a, b)
                | ZFCSetExpr::Separation { set: a, pred: b }
                | ZFCSetExpr::Replacement { set: a, func: b } => {
                    expr_stack.push(b);
                    expr_stack.push(a);
                }
            },
            ExprKind::ZFCMem { element, set } => {
                expr_stack.push(set);
                expr_stack.push(element);
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                expr_stack.push(pred);
                expr_stack.push(domain);
            }
        }
    }
    None
}

impl Environment {
    /// Add a declaration to the environment with full type checking.
    ///
    /// Validates the declaration before insertion:
    /// 1. Name must not already exist in the environment
    /// 2. Universe level parameters must not contain duplicates
    /// 3. No free variables (FVar) in type or value
    /// 4. All Level::Param references must be in the declared level_params
    /// 5. The type must be well-formed (infer_type yields a Sort)
    /// 6. For theorems: type must live in Prop (Sort 0)
    /// 7. For definitions/theorems/opaques: value must have the declared type
    ///
    /// Use `add_decl_unchecked` for trusted .olean imports that skip validation.
    ///
    /// # Errors
    /// - `EnvError::DuplicateName` if a constant with the same name already exists
    /// - `EnvError::DuplicateLevelParam` if level_params contains duplicates
    /// - `EnvError::ContainsFreeVar` if type or value contains FVar
    /// - `EnvError::UndefinedLevelParam` if type or value uses undeclared level params
    /// - `EnvError::TypeCheckFailed` if the type or value fails type checking
    /// - `EnvError::TheoremTypeNotProp` if a theorem's type is not in Prop
    /// Read-only declaration validation: run EXACTLY the soundness gauntlet
    /// [`Environment::add_decl`] runs (no-metavar/no-fvar, level-param closure,
    /// type-is-a-Sort, theorem-type-in-Prop, and `check_type(value, type)`) but
    /// WITHOUT mutating the environment.
    ///
    /// This is the PARAGON parallel-verifier primitive: it takes `&self`, so a
    /// single `Arc<Environment>` base can be shared read-only across rayon
    /// worker threads, each constructing its own per-thread [`TypeChecker`]
    /// internally. `Ok(())` is returned IFF the kernel would have accepted this
    /// declaration's value through `add_decl`'s `check_type` — i.e. it is the
    /// SAME verdict the sequential `--single-pass` path mints via
    /// `add_decl(Declaration::Theorem{..})`, minus only the duplicate-name and
    /// duplicate-insertion bookkeeping (which are env-mutation concerns, not
    /// soundness checks). The MASQUERADE lint (Phase 3 of `add_decl`) is also
    /// out of scope: it is a proof-quality heuristic, not a type-soundness gate,
    /// and it only ever ROLLS BACK an insertion — it never accepts a term
    /// `check_type` rejected, so omitting it cannot make this verdict less sound.
    ///
    /// SOUNDNESS: the only paths to `Ok` are `infer_sort(type)` succeeding AND
    /// (for value-bearing decls) `check_type(value, type)` succeeding against
    /// `self`. No code path stamps a verdict without the kernel's checker
    /// returning `Ok`. The duplicate-name check is intentionally skipped: the
    /// caller checks a constant NOT yet present in the base env (the base holds
    /// only the trusted dependency closure, never the target's own decls), so a
    /// name collision here would be a caller bug, not a soundness hole — the
    /// term is still fully type-checked either way.
    ///
    /// # Errors
    /// Same variants as [`Environment::add_decl`] except `DuplicateName` (never
    /// raised here) and `MasqueradeProof` (lint not run on the read-only path).
    pub fn check_decl_readonly(&self, decl: &Declaration) -> Result<(), EnvError> {
        self.check_decl_readonly_with_heartbeat(decl, None)
    }

    /// Like [`Environment::check_decl_readonly`] but with an explicit
    /// `maxHeartbeats` override.
    ///
    /// This is the PARAGON two-tier escalation primitive. When
    /// `heartbeat_override` is `Some(limit)`, the per-call [`crate::tc::TypeChecker`]
    /// uses `limit` reduction ticks instead of the value in `self.options`; when
    /// `None`, it reads `maxHeartbeats` from `self.options` exactly as
    /// [`Environment::check_decl_readonly`] does (they share this body). NOTHING
    /// else differs.
    ///
    /// SOUNDNESS: identical to [`Environment::check_decl_readonly`]. The heartbeat
    /// is a RESOURCE bound, never a soundness gate — the kernel runs the same
    /// `infer_sort` + Prop-check + `check_type(value, type)` regardless of the
    /// cap; the cap only decides whether the check is allowed to *finish*. Raising
    /// it can only turn a would-be `HeartbeatExceeded` fallback into a genuine
    /// `Ok` (when the term really is def-eq); it can NEVER accept a non-def-eq
    /// term, because `check_type` still fully checks it. The shared `&self`
    /// environment is untouched (no clone, no option mutation): the override lives
    /// only in the per-call `TypeChecker`.
    ///
    /// # Errors
    /// Same variants as [`Environment::check_decl_readonly`].
    pub fn check_decl_readonly_with_heartbeat(
        &self,
        decl: &Declaration,
        heartbeat_override: Option<u32>,
    ) -> Result<(), EnvError> {
        self.check_decl_readonly_with_policy(decl, heartbeat_override, true, true)
    }

    /// Run the full read-only declaration check in a safe, total context.
    ///
    /// This is the certification-strength counterpart of
    /// [`Environment::check_decl_readonly`].  In addition to the same
    /// no-meta/no-free-variable, universe, sort, proposition, and value checks,
    /// it rejects every reference to declarations marked `unsafe` or `partial`.
    /// The ordinary declaration checker preserves Lean's caller-selected
    /// unsafe/partial context semantics; proof certification always uses this
    /// stricter entry point.
    pub fn check_decl_readonly_strict(&self, decl: &Declaration) -> Result<(), EnvError> {
        self.check_decl_readonly_with_policy(decl, None, false, false)
    }

    /// Install an initializer-owned declaration idempotently, accepting an
    /// existing entry only when its complete semantic payload exactly matches
    /// `decl` and passes a fresh strict kernel recheck.
    ///
    /// This closes the partial-initialization trap where a failed initializer
    /// left its first declaration behind and every retry then failed with a
    /// duplicate.  It also fails closed on name squatting: an existing name is
    /// never treated as completion unless kind, universe parameters, type,
    /// value, and reducibility intent all match the canonical declaration.
    pub(crate) fn ensure_exact_checked_decl(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let (name, level_params, type_, value, is_reducible, reducibility, kind) = match &decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                is_reducible,
            } => {
                let reducibility = if *is_reducible {
                    Reducibility::Reducible
                } else {
                    Reducibility::Regular(self.get_max_height(value) + 1)
                };
                (
                    name,
                    level_params,
                    type_,
                    Some(value),
                    *is_reducible,
                    reducibility,
                    ConstantKind::Definition,
                )
            }
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => (
                name,
                level_params,
                type_,
                None,
                false,
                Reducibility::Opaque,
                ConstantKind::Axiom,
            ),
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => (
                name,
                level_params,
                type_,
                Some(value),
                false,
                Reducibility::Opaque,
                ConstantKind::Theorem,
            ),
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => (
                name,
                level_params,
                type_,
                Some(value),
                false,
                Reducibility::Opaque,
                ConstantKind::Opaque,
            ),
        };

        let name = name.clone();
        if let Some(existing) = self.get_const(&name) {
            let exact = existing.kind == kind
                && existing.level_params == *level_params
                && existing.type_ == *type_
                && existing.value.as_ref() == value
                && existing.is_reducible == is_reducible
                && existing.reducibility == reducibility;
            if !exact {
                return Err(EnvError::InitializationConflict {
                    name,
                    detail: "existing kind/universes/type/value/reducibility differ from canonical declaration"
                        .to_string(),
                });
            }
            if self.is_unsafe(&name) || self.is_partial(&name) {
                return Err(EnvError::InitializationConflict {
                    name,
                    detail: "existing canonical payload is marked unsafe or partial".to_string(),
                });
            }
            self.check_decl_readonly_strict(&decl)?;
            self.declaration_verification
                .insert(name, super::DeclarationVerification::FullKernelCheck);
            return Ok(());
        }
        self.add_decl(decl)
    }

    fn check_decl_readonly_with_policy(
        &self,
        decl: &Declaration,
        heartbeat_override: Option<u32>,
        allow_unsafe: bool,
        allow_partial: bool,
    ) -> Result<(), EnvError> {
        // Extract name, level_params, type, optional value, and whether this is a
        // theorem — exactly as `add_decl`'s Phase-1 does.
        let (name, level_params, type_, opt_value, is_theorem) = match decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                ..
            } => (name, level_params, type_, Some(value), false),
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => (name, level_params, type_, None, false),
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), true),
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), false),
        };

        // (2) Duplicate universe level parameters.
        for (i, p) in level_params.iter().enumerate() {
            if level_params[..i].contains(p) {
                return Err(EnvError::DuplicateLevelParam {
                    name: name.clone(),
                    param: p.clone(),
                });
            }
        }

        // (3) Reject metavariables and free variables in type and value.
        if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: name.clone() });
        }
        if type_.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar { name: name.clone() });
        }
        if let Some(value) = opt_value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            if value.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: name.clone() });
            }
        }

        // (4) All Level::Param references must be in the declared level_params.
        if let Some(undef) = find_undef_level_param(type_, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: name.clone(),
                param: undef,
            });
        }
        if let Some(value) = opt_value {
            if let Some(undef) = find_undef_level_param(value, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
        }

        // (5)-(7) Type checking. A fresh per-call TypeChecker borrows `self`
        // immutably; nothing here mutates the environment.
        let mut tc = crate::tc::TypeChecker::with_mode(self, self.mode);
        tc.set_allow_unsafe(allow_unsafe);
        tc.set_allow_partial(allow_partial);
        // Coq lane: use cumulative subtyping (`Prop ≤ Set ≤ Type`). No-op
        // (== non-cumulative) when the env flag is off, i.e. the Lean/olean lane.
        tc.set_cumulative(self.cumulative);
        // Tier-2 escalation: an explicit override wins over `self.options`, so a
        // per-constant retry can raise the cap WITHOUT mutating the shared env.
        // Falls through to the env option when `None` (the Tier-1 / default path).
        match heartbeat_override {
            Some(limit) => tc.set_heartbeat_limit(limit),
            None => {
                if let Some(Some(val_str)) = self.options.get("maxHeartbeats") {
                    if let Ok(limit) = val_str.parse::<u32>() {
                        tc.set_heartbeat_limit(limit);
                    }
                }
            }
        }
        if let Some(Some(val_str)) = self.options.get("tcMaxCacheEntries") {
            if let Ok(max) = val_str.parse::<usize>() {
                tc.set_max_cache_entries(max);
            }
        }
        // Enable the heartbeat profiler if `profileHeartbeats` is set — mirrors
        // `add_decl`'s Phase-1 (the readonly check path had `set_profiler_active_
        // name` but never enabled the profiler, so HeartbeatExceeded errors from
        // this path carried no breakdown). Verdict-neutral: the profiler only
        // observes tick attribution; it never changes reduction or acceptance.
        if self
            .options
            .get("profileHeartbeats")
            .and_then(|v| v.as_deref())
            .is_some_and(|v| v == "true" || v == "1")
        {
            tc.enable_heartbeat_profiler();
        }
        let tc = tc;
        tc.set_profiler_active_name(name.clone());
        tc.set_expr_loc_decl_name(name.clone());

        // (5) The type must be well-formed: infer_sort yields a Sort.
        let sort = tc
            .infer_sort(type_)
            .map_err(|e| EnvError::TypeCheckFailed {
                name: name.clone(),
                source: e,
            })?;

        // (6) For theorems: type must live in Prop (Sort 0).
        if is_theorem && !sort.is_zero() {
            return Err(EnvError::TheoremTypeNotProp {
                name: name.clone(),
                sort,
            });
        }

        // (7) For value-bearing decls: value must have the declared type.
        if let Some(value) = opt_value {
            tc.check_type(value, type_)
                .map_err(|e| EnvError::TypeCheckFailed {
                    name: name.clone(),
                    source: e,
                })?;
        }

        Ok(())
    }

    pub fn add_decl(&mut self, decl: Declaration) -> Result<(), EnvError> {
        // Metamath two-pass PASS-1: convert an incoming Theorem into an Axiom
        // (drop its proof value) so only its schematic TYPE is registered and the
        // expensive proof type-check is SKIPPED. SOUND only inside the two-pass
        // (pass-2 re-verifies every theorem; only pass-2 results are exported) —
        // see `set_mm_axiom_only` / `MM_AXIOM_ONLY`. The flag is `false` for every
        // other caller, so this is a no-op outside the importer's pass-1.
        let decl = match decl {
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } if mm_axiom_only() => {
                // CHEAP PASS-1: drop `value` (the proof) and register the schematic
                // TYPE as an axiom WITHOUT type-checking it (add_decl_unchecked). The
                // type is produced by the SAME construction the real verifier uses
                // (verify_metamath_theorem_schematic*), so it is well-formed; the
                // embedding type-check would re-run the applySubstV/MMThm reductions —
                // ~as costly as the proof — and STALL pass-1 on the deep ax12-family
                // types. SOUNDNESS: sound ONLY inside the Metamath two-pass, where
                // pass-2 RE-VERIFIES every in-range proof (re-type-checking the type via
                // the proof) and ONLY pass-2-verified, dependency-closure-gated theorems
                // are exported. An ill-formed type (a construction bug) would make the
                // reusing proof FAIL pass-2 and the gate DROP it — never a false accept.
                // Validated by count-equivalence (two-pass+gate == sequential). The flag
                // is `false` for every non-two-pass caller, so this never runs elsewhere.
                //
                // G1 FAIL-CLOSE: the flag alone no longer authorizes dropping the proof.
                // The caller must be provably inside a sanctioned two-pass scope (an
                // `MmAxiomOnlyGuard` is live → `mm_two_pass_active()`), where PASS-2
                // re-verifies every proof. A stray `set_mm_axiom_only(true)` with no
                // guard now fails closed here instead of registering an unchecked type —
                // closing the "axiom-shaped smuggle" escape hatch. SOUNDNESS: this only
                // ADDS a precondition to the skip path; the checked path is unaffected.
                if !mm_two_pass_active() {
                    debug_assert!(
                        false,
                        "mm_axiom_only proof-drop reached without the two-pass sentinel \
                         (misuse of set_mm_axiom_only outside kernel_verify_two_pass_range)"
                    );
                    return Err(EnvError::AxiomOnlyMisuse { name });
                }
                let _ = value;
                self.add_decl_unchecked(Declaration::Axiom {
                    name,
                    level_params,
                    type_,
                });
                return Ok(());
            }
            other => other,
        };
        // Phase 1: Extract fields and validate with type checker.
        // The immutable borrow via TypeChecker is scoped so it's released
        // before we mutate self.constants in Phase 2.
        let info = {
            // Extract name, level_params, type, and optional value from the declaration
            let (name, level_params, type_, opt_value, reducibility, _is_reducible) = match &decl {
                Declaration::Definition {
                    name,
                    level_params,
                    type_,
                    value,
                    is_reducible,
                } => {
                    let reducibility = if *is_reducible {
                        Reducibility::Reducible
                    } else {
                        // Compute definition height from referenced constants
                        let h = self.get_max_height(value);
                        Reducibility::Regular(h + 1)
                    };
                    (
                        name.clone(),
                        level_params,
                        type_,
                        Some(value),
                        reducibility,
                        *is_reducible,
                    )
                }
                Declaration::Axiom {
                    name,
                    level_params,
                    type_,
                } => (
                    name.clone(),
                    level_params,
                    type_,
                    None,
                    Reducibility::Opaque,
                    false,
                ),
                Declaration::Theorem {
                    name,
                    level_params,
                    type_,
                    value,
                }
                | Declaration::Opaque {
                    name,
                    level_params,
                    type_,
                    value,
                } => (
                    name.clone(),
                    level_params,
                    type_,
                    Some(value),
                    Reducibility::Opaque,
                    false,
                ),
            };

            // Check for duplicate name
            if self.constants.contains_key(&name) {
                return Err(EnvError::DuplicateName(name));
            }

            // Check for duplicate universe level parameters
            for (i, p) in level_params.iter().enumerate() {
                if level_params[..i].contains(p) {
                    return Err(EnvError::DuplicateLevelParam {
                        name: name.clone(),
                        param: p.clone(),
                    });
                }
            }

            // Reject metavariables and free variables (Lean 4: check_no_metavar_no_fvar)
            // Uses O(1) metadata flags computed at expression construction time.
            if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            if type_.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: name.clone() });
            }
            if let Some(value) = opt_value {
                if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                    return Err(EnvError::ContainsMetavar { name: name.clone() });
                }
                if value.has_fvar_quick() {
                    return Err(EnvError::ContainsFreeVar { name: name.clone() });
                }
            }

            // Validate all Level::Param references are in the declared level_params
            if let Some(undef) = find_undef_level_param(type_, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
            if let Some(value) = opt_value {
                if let Some(undef) = find_undef_level_param(value, level_params) {
                    return Err(EnvError::UndefinedLevelParam {
                        name: name.clone(),
                        param: undef,
                    });
                }
            }

            // Type-check the declaration
            let is_theorem = matches!(&decl, Declaration::Theorem { .. });
            {
                let mut tc = crate::tc::TypeChecker::with_mode(&*self, self.mode);
                // Coq lane: cumulative subtyping (no-op off the Coq lane).
                tc.set_cumulative(self.cumulative);

                // Apply maxHeartbeats from file-scope `set_option` if present.
                // The option value is stored as `Option<String>` in env.options.
                if let Some(Some(val_str)) = self.options.get("maxHeartbeats") {
                    if let Ok(limit) = val_str.parse::<u32>() {
                        tc.set_heartbeat_limit(limit);
                    }
                }

                // Apply tcMaxCacheEntries from `set_option` if present. Bounding
                // the per-check TC cache is SOUND (a smaller cache can only change
                // which correct results are memoized — it can never accept an
                // unequal pair). The Metamath importer sets this to `0` because a
                // large cache retains an `Expr`-keyed reduction/inference entry
                // across a binder-context boundary in very deep proof terms and
                // returns it for a structurally-equal-but-context-distinct read,
                // producing a def-eq FALSE-negative (rejecting a valid proof).
                // See docs/METAMATH_KERNEL_VERIFICATION.md.
                if let Some(Some(val_str)) = self.options.get("tcMaxCacheEntries") {
                    if let Ok(max) = val_str.parse::<usize>() {
                        tc.set_max_cache_entries(max);
                    }
                }

                // Enable heartbeat profiler if `profileHeartbeats` option is set.
                // When enabled, HeartbeatExceeded errors include a breakdown of
                // where the budget was spent (by operation category and constant name).
                // Part of #3399.
                if self
                    .options
                    .get("profileHeartbeats")
                    .and_then(|v| v.as_deref())
                    .is_some_and(|v| v == "true" || v == "1")
                {
                    tc.enable_heartbeat_profiler();
                }

                // Rebind as immutable for the rest of the scope.
                let tc = tc;

                // Set profiler active name to the constant being checked.
                // This attributes heartbeat ticks to the specific constant,
                // enabling per-name breakdown in the profile report.
                // Part of #3399.
                tc.set_profiler_active_name(name.clone());

                // Label expression-location trails with the declaration being
                // checked. Gives `TypeError::TypeMismatch` / `NotAFunction` /
                // `ExpectedSort` a "in declaration 'foo', at ..." prefix so
                // users see WHICH declaration failed and WHERE inside its term.
                // Part of #3425.
                tc.set_expr_loc_decl_name(name.clone());

                // The type must be well-formed: infer_type(type_) must yield a Sort
                let sort = tc
                    .infer_sort(type_)
                    .map_err(|e| EnvError::TypeCheckFailed {
                        name: name.clone(),
                        source: e,
                    })?;

                // For theorems: type must live in Prop (Sort 0)
                // Lean 4: checker.is_prop(type) in environment.cpp:add_theorem
                if is_theorem && !sort.is_zero() {
                    return Err(EnvError::TheoremTypeNotProp {
                        name: name.clone(),
                        sort,
                    });
                }

                // For declarations with values, the value must have the declared type
                if let Some(value) = opt_value {
                    tc.check_type(value, type_)
                        .map_err(|e| EnvError::TypeCheckFailed {
                            name: name.clone(),
                            source: e,
                        })?;
                }
            } // TypeChecker dropped — immutable borrow released

            // Build ConstantInfo from the declaration
            match decl {
                Declaration::Definition {
                    name,
                    level_params,
                    type_,
                    value,
                    is_reducible,
                } => ConstantInfo {
                    name: name.clone(),
                    level_params,
                    type_,
                    value: Some(value),
                    reducibility,
                    is_reducible,
                    kind: ConstantKind::Definition,
                },
                Declaration::Axiom {
                    name,
                    level_params,
                    type_,
                } => ConstantInfo {
                    name: name.clone(),
                    level_params,
                    type_,
                    value: None,
                    is_reducible: false,
                    reducibility,
                    kind: ConstantKind::Axiom,
                },
                Declaration::Theorem {
                    name,
                    level_params,
                    type_,
                    value,
                } => ConstantInfo {
                    name: name.clone(),
                    level_params,
                    type_,
                    value: Some(value),
                    is_reducible: false,
                    reducibility,
                    kind: ConstantKind::Theorem,
                },
                Declaration::Opaque {
                    name,
                    level_params,
                    type_,
                    value,
                } => ConstantInfo {
                    name: name.clone(),
                    level_params,
                    type_,
                    value: Some(value),
                    is_reducible: false,
                    reducibility,
                    kind: ConstantKind::Opaque,
                },
            }
        };

        // Phase 2: Insert into environment (mutable access)
        use hashbrown::hash_map::Entry;
        let inserted_name = info.name.clone();
        let inserted_kind = info.kind;
        match self.constants.entry(info.name.clone()) {
            Entry::Occupied(_) => return Err(EnvError::DuplicateName(info.name)),
            Entry::Vacant(e) => {
                e.insert(info);
            }
        }
        self.declaration_verification.insert(
            inserted_name.clone(),
            super::DeclarationVerification::FullKernelCheck,
        );
        self.generation += 1;

        // Phase 3: MASQUERADE-prevention lint on freshly-registered theorems.
        // Gated on `CLEAN_STRICT_PROOF_QUALITY=1` so legacy tests are unaffected
        // until the Tier-C demasquerade sweep lands. On failure, roll back the
        // insertion so the environment never observes a MASQUERADE theorem.
        if inserted_kind == ConstantKind::Theorem && super::proof_quality::strict_mode_enabled() {
            if let Err(pq) = self.assert_proof_nontrivial(&inserted_name) {
                self.constants.remove(&inserted_name);
                self.declaration_verification.remove(&inserted_name);
                self.generation += 1;
                return Err(EnvError::MasqueradeProof {
                    name: inserted_name,
                    detail: pq.to_string(),
                });
            }
        }

        Ok(())
    }

    /// Add a declaration only if no constant with the same name already exists.
    ///
    /// Used by stub initialization to avoid collisions with declarations
    /// already loaded from .olean files. When a name exists (e.g., from
    /// Mathlib .olean), the .olean version is preferred and this is a no-op.
    pub fn add_decl_if_absent(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let name = match &decl {
            Declaration::Definition { name, .. }
            | Declaration::Axiom { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. } => name,
        };
        if self.get_const(name).is_some() {
            return Ok(());
        }
        self.add_decl(decl)
    }

    /// Upgrade an existing VALUE-FREE constant (an axiom stub) to a fully
    /// kernel-CHECKED value-bearing declaration of the same name and type.
    ///
    /// This is the CHECKED counterpart of the trusted-import healing in
    /// `upgrade_axiom_stubs` (registration.rs): where that path swaps the
    /// value in UNCHECKED (acceptable only in the trusted `.olean` loader
    /// lane), this one requires the incoming declaration to pass the exact
    /// `add_decl` soundness gauntlet before the swap, so it is usable from
    /// trust-sensitive lanes (e.g. the mathverse incremental verifier).
    ///
    /// Preconditions enforced (each with a typed error):
    /// 1. The incoming `decl` is value-bearing (`Definition`/`Theorem`/
    ///    `Opaque`) — [`EnvError::UpgradeValueMissing`] otherwise.
    /// 2. A constant with the SAME name already exists —
    ///    [`EnvError::UpgradeTargetMissing`] otherwise.
    /// 3. The existing constant is VALUE-FREE (`value.is_none()`) —
    ///    [`EnvError::UpgradeTargetHasValue`] otherwise.
    /// 4. The incoming declaration's type IS the existing constant's type,
    ///    compared alpha-insensitively on level params (level params are
    ///    positional binders: call sites instantiate them by position, never
    ///    by name): same arity, and the incoming type equals the existing one
    ///    after positionally renaming the incoming params to the existing
    ///    names (`instantiate_level_params_direct`). Structural equality is
    ///    tried first; the kernel's own `is_def_eq` is the fallback (it
    ///    ignores binder annotations and universe spellings structural `==`
    ///    distinguishes). [`EnvError::UpgradeTypeMismatch`] otherwise.
    /// 5. The incoming declaration passes the FULL `add_decl` check (type is a
    ///    Sort, theorem types live in Prop, `check_type(value, type)`) in the
    ///    current environment WITH THE STUB REMOVED — same error variants as
    ///    [`Environment::add_decl`].
    ///
    /// On success the constant entry is REPLACED by the checked declaration
    /// (new value, kind, and reducibility), and the environment generation is
    /// bumped. On any failure the environment is left exactly as it was.
    ///
    /// SOUNDNESS: the incoming value is fully kernel-checked before the swap —
    /// the check runs through `add_decl` itself (the same gauntlet every
    /// checked declaration passes), so no code path installs an unchecked
    /// value. The swap can therefore only replace an UNPROVEN, value-free
    /// axiom entry with a PROVEN declaration of an equivalent type: strictly
    /// trust-increasing (the set of assumed-without-proof constants shrinks by
    /// one; nothing else changes, since the stated type is preserved up to
    /// def-eq). Circular self-support is structurally impossible: the stub is
    /// REMOVED from the environment for the duration of the check, so a value
    /// that references the constant being upgraded fails with an
    /// unknown-constant type error rather than discharging the stub's trust
    /// with itself (independently, kernel terms have no self-reference without
    /// going through a recursor, and this name has none). If the check fails,
    /// the removed stub is restored verbatim.
    ///
    /// # Errors
    /// - [`EnvError::UpgradeValueMissing`] — incoming decl is an `Axiom`.
    /// - [`EnvError::UpgradeTargetMissing`] — no existing constant.
    /// - [`EnvError::UpgradeTargetHasValue`] — existing constant has a value.
    /// - [`EnvError::UpgradeTypeMismatch`] — level-param arity or type differs.
    /// - Any [`Environment::add_decl`] error — the value failed checking.
    pub fn upgrade_axiom_to_checked_decl(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let (name, level_params, type_) = match &decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                ..
            }
            | Declaration::Theorem {
                name,
                level_params,
                type_,
                ..
            }
            | Declaration::Opaque {
                name,
                level_params,
                type_,
                ..
            } => (name.clone(), level_params, type_),
            Declaration::Axiom { name, .. } => {
                return Err(EnvError::UpgradeValueMissing { name: name.clone() });
            }
        };

        // Preconditions 2+3: an existing, VALUE-FREE entry. Only the eagerly
        // owned map is consulted (`self.constants`, not `get_const`'s lazy
        // fallback) — the same map `add_decl`'s duplicate check reads, so the
        // upgrade replaces exactly the entry that made `add_decl` collide.
        {
            let Some(existing) = self.constants.get(&name) else {
                return Err(EnvError::UpgradeTargetMissing { name });
            };
            if existing.value.is_some() {
                return Err(EnvError::UpgradeTargetHasValue { name });
            }

            // Precondition 4: type identity, alpha-insensitive on level params.
            if existing.level_params.len() != level_params.len() {
                let detail = format!(
                    "level-param arity {} differs from existing arity {}",
                    level_params.len(),
                    existing.level_params.len()
                );
                return Err(EnvError::UpgradeTypeMismatch { name, detail });
            }
            let incoming_type = if existing.level_params == *level_params {
                type_.clone()
            } else {
                let renaming: Vec<Level> = existing
                    .level_params
                    .iter()
                    .map(|n| Level::param(n.clone()))
                    .collect();
                type_.instantiate_level_params_direct(level_params, &renaming)
            };
            if existing.type_ != incoming_type {
                let tc = crate::tc::TypeChecker::with_mode(&*self, self.mode);
                if !tc.is_def_eq(&existing.type_, &incoming_type) {
                    return Err(EnvError::UpgradeTypeMismatch {
                        name,
                        detail: "declared type is not definitionally equal to the existing \
                                 value-free constant's type"
                            .to_string(),
                    });
                }
            }
        } // immutable borrow of the existing entry released

        // Precondition 5 + the swap: remove the stub, then run the incoming
        // declaration through the FULL `add_decl` gauntlet (which now sees no
        // duplicate). On failure, restore the stub verbatim so the env is
        // unchanged. The generation is bumped on removal and restoration so no
        // generation-keyed cache can conflate the stub-absent intermediate
        // state with either endpoint.
        let Some(stub) = self.constants.remove(&name) else {
            // Unreachable in practice (`&mut self` — no interleaving since the
            // check above), but fail closed rather than panic.
            return Err(EnvError::UpgradeTargetMissing { name });
        };
        let stub_verification = self.declaration_verification.remove(&name);
        self.generation += 1;
        match self.add_decl(decl) {
            Ok(()) => Ok(()),
            Err(e) => {
                self.constants.insert(name.clone(), stub);
                if let Some(verification) = stub_verification {
                    self.declaration_verification.insert(name, verification);
                }
                self.generation += 1;
                Err(e)
            }
        }
    }

    /// Add a declaration to the environment, skipping duplicate check.
    ///
    /// This is faster than `add_decl` because it assumes the name
    /// does not already exist. Use only when loading trusted .olean files.
    #[inline]
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn add_decl_unchecked(&mut self, decl: Declaration) {
        let info = match decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                is_reducible,
            } => {
                let reducibility = if is_reducible {
                    Reducibility::Reducible
                } else {
                    let h = self.get_max_height(&value);
                    Reducibility::Regular(h + 1)
                };
                ConstantInfo {
                    name: name.clone(),
                    level_params,
                    type_,
                    value: Some(value),
                    reducibility,
                    is_reducible,
                    kind: ConstantKind::Definition,
                }
            }
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => ConstantInfo {
                name: name.clone(),
                level_params,
                type_,
                value: None,
                is_reducible: false,
                reducibility: Reducibility::Regular(0),
                kind: ConstantKind::Axiom,
            },
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => ConstantInfo {
                name: name.clone(),
                level_params,
                type_,
                value: Some(value),
                is_reducible: false,
                reducibility: Reducibility::Opaque,
                kind: ConstantKind::Theorem,
            },
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => ConstantInfo {
                name: name.clone(),
                level_params,
                type_,
                value: Some(value),
                is_reducible: false,
                reducibility: Reducibility::Opaque,
                kind: ConstantKind::Opaque,
            },
        };

        debug_assert!(
            !self.constants.contains_key(&info.name),
            "add_decl_unchecked duplicate constant: {}",
            info.name
        );
        let name = info.name.clone();
        self.constants.insert(name.clone(), info);
        self.declaration_verification
            .insert(name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Add a declaration with structural validation but without type checking.
    ///
    /// Performs cheap O(1) structural integrity checks:
    /// 1. Name must not already exist in the environment
    /// 2. Universe level parameters must not contain duplicates
    /// 3. No expression or level metavariables in type or value
    /// 4. No free variables (FVar) in type or value
    /// 5. All Level::Param references must be in the declared level_params
    ///
    /// Skips expensive type checking (infer_sort, check_type) which can also
    /// falsely reject valid elaborated terms with recursor-dependent types
    /// where is_def_eq doesn't fully reduce motive applications.
    ///
    /// Use this for declarations already validated by the elaborator, where
    /// full re-checking is redundant but structural invariants should still
    /// be enforced.
    pub fn add_decl_structural(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let info = {
            let (name, level_params, type_, opt_value, reducibility, is_reducible, kind) =
                match &decl {
                    Declaration::Definition {
                        name,
                        level_params,
                        type_,
                        value,
                        is_reducible,
                    } => {
                        let reducibility = if *is_reducible {
                            Reducibility::Reducible
                        } else {
                            let h = self.get_max_height(value);
                            Reducibility::Regular(h + 1)
                        };
                        (
                            name,
                            level_params,
                            type_,
                            Some(value),
                            reducibility,
                            *is_reducible,
                            ConstantKind::Definition,
                        )
                    }
                    Declaration::Axiom {
                        name,
                        level_params,
                        type_,
                    } => (
                        name,
                        level_params,
                        type_,
                        None,
                        Reducibility::Regular(0),
                        false,
                        ConstantKind::Axiom,
                    ),
                    Declaration::Theorem {
                        name,
                        level_params,
                        type_,
                        value,
                    } => (
                        name,
                        level_params,
                        type_,
                        Some(value),
                        Reducibility::Opaque,
                        false,
                        ConstantKind::Theorem,
                    ),
                    Declaration::Opaque {
                        name,
                        level_params,
                        type_,
                        value,
                    } => (
                        name,
                        level_params,
                        type_,
                        Some(value),
                        Reducibility::Opaque,
                        false,
                        ConstantKind::Opaque,
                    ),
                };

            // Check 1: duplicate name
            if self.constants.contains_key(name) {
                return Err(EnvError::DuplicateName(name.clone()));
            }

            // Check 2: duplicate universe level parameters
            for (i, p) in level_params.iter().enumerate() {
                if level_params[..i].contains(p) {
                    return Err(EnvError::DuplicateLevelParam {
                        name: name.clone(),
                        param: p.clone(),
                    });
                }
            }

            // Check 3: no metavariables
            if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            // Check 4: no free variables
            if type_.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: name.clone() });
            }
            if let Some(value) = opt_value {
                if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                    return Err(EnvError::ContainsMetavar { name: name.clone() });
                }
                if value.has_fvar_quick() {
                    return Err(EnvError::ContainsFreeVar { name: name.clone() });
                }
            }

            // Check 5: undefined level params
            if let Some(undef) = find_undef_level_param(type_, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
            if let Some(value) = opt_value {
                if let Some(undef) = find_undef_level_param(value, level_params) {
                    return Err(EnvError::UndefinedLevelParam {
                        name: name.clone(),
                        param: undef,
                    });
                }
            }

            // Build ConstantInfo (no type checking)
            ConstantInfo {
                name: name.clone(),
                level_params: level_params.clone(),
                type_: type_.clone(),
                value: opt_value.cloned(),
                reducibility,
                is_reducible,
                kind,
            }
        };

        // Insert into environment
        use hashbrown::hash_map::Entry;
        match self.constants.entry(info.name.clone()) {
            Entry::Occupied(_) => return Err(EnvError::DuplicateName(info.name)),
            Entry::Vacant(e) => {
                e.insert(info);
            }
        }
        self.declaration_verification.insert(
            match &decl {
                Declaration::Definition { name, .. }
                | Declaration::Axiom { name, .. }
                | Declaration::Theorem { name, .. }
                | Declaration::Opaque { name, .. } => name.clone(),
            },
            super::DeclarationVerification::StructuralOnly,
        );
        self.generation += 1;
        Ok(())
    }
}

#[cfg(test)]
mod mm_axiom_only_tests {
    use super::*;
    use crate::expr::Expr;

    /// Build an env with two distinct props `P`, `R` and a proof `r : R`, so that
    /// `bad : P := r` is a TYPE ERROR on the checked path (R is not a proof of P).
    fn env_with_mismatched_proof() -> (Environment, Declaration) {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("register P : Prop");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("R"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("register R : Prop");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("r"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
        })
        .expect("register r : R");
        // `bad : P := r` — value `r : R`, declared type `P`. Mismatch.
        let bad = Declaration::Theorem {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("P"), vec![]),
            value: Expr::const_(Name::from_string("r"), vec![]),
        };
        (env, bad)
    }

    #[test]
    fn test_checked_path_rejects_mismatched_proof() {
        set_mm_axiom_only(false);
        let (mut env, bad) = env_with_mismatched_proof();
        let res = env.add_decl(bad);
        assert!(
            matches!(res, Err(EnvError::TypeCheckFailed { .. })),
            "checked add_decl must reject a theorem whose value does not have its \
             declared type, got: {res:?}"
        );
    }

    #[test]
    fn test_axiom_only_skips_proof_check_and_registers_type() {
        // The SANCTIONED path: the two-pass sentinel is established (G1 guard) AND
        // the flag is ON, so the proof-drop fast path fires exactly as before.
        let _guard = MmAxiomOnlyGuard::enter();
        set_mm_axiom_only(true);
        let (mut env, bad) = env_with_mismatched_proof();
        let res = env.add_decl(bad);
        // Always reset the thread-local flag, even on assertion failure.
        set_mm_axiom_only(false);
        res.expect("axiom-only mode must register the TYPE without checking the proof");
        let info = env
            .get_const(&Name::from_string("bad"))
            .expect("bad registered");
        // Registered as an AXIOM (proof value DROPPED), keeping only the type `P`.
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "axiom-only must register a Theorem as an Axiom"
        );
        assert!(
            info.value.is_none(),
            "axiom-only must drop the (unchecked) proof value"
        );
    }

    /// G1 FAIL-CLOSE: with the flag ON but NO two-pass sentinel (no
    /// `MmAxiomOnlyGuard`), the proof-drop fast path must REFUSE to register an
    /// unchecked theorem type — it fails closed to `AxiomOnlyMisuse` rather than
    /// dropping the (false) proof. This closes the "axiom-shaped smuggle" hole:
    /// setting the flag alone is no longer enough to bypass the kernel check.
    #[test]
    fn test_g1_axiom_only_without_sentinel_fails_closed() {
        // No `MmAxiomOnlyGuard` here — the sentinel is absent.
        assert!(
            !mm_two_pass_active(),
            "precondition: no two-pass scope must be active"
        );
        set_mm_axiom_only(true);
        let (mut env, bad) = env_with_mismatched_proof();
        // In debug the branch also `debug_assert!(false, ..)`s; catch that so the
        // test observes the fail-closed behaviour on both debug and release builds.
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| env.add_decl(bad)));
        set_mm_axiom_only(false);
        match caught {
            // Release: no debug_assert; we get the fail-closed Err.
            Ok(res) => assert!(
                matches!(res, Err(EnvError::AxiomOnlyMisuse { .. })),
                "flag-ON without the two-pass sentinel must fail closed with \
                 AxiomOnlyMisuse, got: {res:?}"
            ),
            // Debug: the branch's `debug_assert!(false)` panicked FIRST — which is
            // itself the fail-closed outcome (misuse never silently succeeds).
            Err(_) => { /* debug_assert panic == fail-closed; acceptable */ }
        }
        // Crucially: `bad` must NOT have been registered under either build.
        assert!(
            env.get_const(&Name::from_string("bad")).is_none(),
            "misuse must not register the unchecked theorem type"
        );
    }

    /// The guard establishes and tears down the sentinel via RAII, and its drop
    /// also forces the axiom-only flag OFF (no leak into later checked work).
    #[test]
    fn test_g1_guard_establishes_and_clears_sentinel() {
        assert!(!mm_two_pass_active(), "sentinel starts inactive");
        {
            let _g = MmAxiomOnlyGuard::enter();
            assert!(mm_two_pass_active(), "guard establishes the sentinel");
            set_mm_axiom_only(true);
        }
        // Guard dropped: sentinel cleared AND flag forced off.
        assert!(!mm_two_pass_active(), "guard drop clears the sentinel");
        assert!(
            !mm_axiom_only(),
            "guard drop must force the axiom-only flag OFF (no leak)"
        );
    }

    #[test]
    fn test_axiom_only_flag_defaults_off() {
        // A fresh thread sees the default `false`; the other tests reset it too.
        set_mm_axiom_only(false);
        assert!(!mm_axiom_only(), "flag must default to OFF (checked path)");
    }
}

#[cfg(test)]
mod check_decl_readonly_tests {
    use super::*;
    use crate::expr::Expr;
    use std::sync::Arc;

    /// Build an env with `P`, `R : Prop` and `r : R`. Returns a GOOD theorem
    /// (`good : R := r`, value has its declared type) and a BAD one
    /// (`bad : P := r`, value `r : R` does not have type `P`).
    fn env_good_bad() -> (Environment, Declaration, Declaration) {
        let mut env = Environment::new();
        for n in ["P", "R"] {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(n),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("register prop");
        }
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("r"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
        })
        .expect("register r : R");
        let good = Declaration::Theorem {
            name: Name::from_string("good"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
            value: Expr::const_(Name::from_string("r"), vec![]),
        };
        let bad = Declaration::Theorem {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("P"), vec![]),
            value: Expr::const_(Name::from_string("r"), vec![]),
        };
        (env, good, bad)
    }

    #[test]
    fn test_check_decl_readonly_accepts_well_typed_value() {
        let (env, good, _bad) = env_good_bad();
        env.check_decl_readonly(&good)
            .expect("read-only check must accept a well-typed theorem value");
    }

    #[test]
    fn test_check_decl_readonly_rejects_mismatched_proof() {
        let (env, _good, bad) = env_good_bad();
        let res = env.check_decl_readonly(&bad);
        assert!(
            matches!(res, Err(EnvError::TypeCheckFailed { .. })),
            "read-only check must reject a value lacking its declared type, got: {res:?}"
        );
    }

    #[test]
    fn test_check_decl_readonly_does_not_mutate_env() {
        let (env, good, _bad) = env_good_bad();
        let before = env.num_constants();
        env.check_decl_readonly(&good).expect("accept");
        assert_eq!(
            env.num_constants(),
            before,
            "read-only check must not add the constant to the env"
        );
        assert!(
            env.get_const(&Name::from_string("good")).is_none(),
            "the checked constant must NOT appear in the env afterwards"
        );
    }

    #[test]
    fn test_check_decl_readonly_matches_add_decl_verdict() {
        // Parity: read-only Ok/Err must agree with what a mutating add_decl on a
        // clone would return (the soundness invariant the PARAGON path rests on).
        let (env, good, bad) = env_good_bad();
        for decl in [&good, &bad] {
            let ro = env.check_decl_readonly(decl).is_ok();
            let mut clone = env.clone();
            let added = clone.add_decl(decl.clone()).is_ok();
            assert_eq!(
                ro, added,
                "read-only verdict must match add_decl for {decl:?}: ro={ro} add={added}"
            );
        }
    }

    #[test]
    fn test_check_decl_readonly_is_thread_safe_over_arc() {
        // The whole point: ONE Arc<Environment> base shared read-only across
        // threads, each running its own type check concurrently.
        let (env, good, bad) = env_good_bad();
        let base = Arc::new(env);
        let handles: Vec<_> = (0..8)
            .map(|i| {
                let base = Arc::clone(&base);
                let good = good.clone();
                let bad = bad.clone();
                std::thread::spawn(move || {
                    if i % 2 == 0 {
                        base.check_decl_readonly(&good).is_ok()
                    } else {
                        base.check_decl_readonly(&bad).is_err()
                    }
                })
            })
            .collect();
        for h in handles {
            assert!(
                h.join().expect("worker thread panicked"),
                "each worker's read-only verdict must hold concurrently"
            );
        }
    }

    /// TWO-TIER ESCALATION PRIMITIVE: a heartbeat cap of 1 tick trips
    /// `HeartbeatExceeded` on an otherwise-well-typed value; re-running the SAME
    /// decl at an unlimited (0) cap RECOVERS it to `Ok`. This is the exact lever
    /// the PARAGON verifier uses — Tier-1 too-low cap fails on heartbeat, Tier-2
    /// higher cap passes — and it proves raising the cap turns a would-be
    /// fallback into a genuine acceptance WITHOUT mutating the env.
    #[test]
    fn test_check_decl_readonly_heartbeat_override_escalation_recovers() {
        let (env, good, _bad) = env_good_bad();

        // Tier 1: a 1-tick cap must trip the heartbeat on a real (non-trivial)
        // check — the SPECIFIC error the escalation site matches on.
        let tier1 = env.check_decl_readonly_with_heartbeat(&good, Some(1));
        assert!(
            matches!(
                tier1,
                Err(EnvError::TypeCheckFailed {
                    source: crate::tc::TypeError::HeartbeatExceeded { .. },
                    ..
                })
            ),
            "a 1-tick cap must fail SPECIFICALLY with HeartbeatExceeded, got: {tier1:?}"
        );

        // Tier 2: the SAME decl at an unlimited (0) cap must now VERIFY — raising
        // the cap recovered a genuine acceptance, not a relaxed one.
        env.check_decl_readonly_with_heartbeat(&good, Some(0))
            .expect("escalated (unlimited) cap must recover the well-typed value");

        // The env is untouched by either call (read-only).
        assert!(
            env.get_const(&Name::from_string("good")).is_none(),
            "neither tier may mutate the shared env"
        );
    }

    /// SOUNDNESS: escalation NEVER launders a broken proof. A `bad` value that
    /// lacks its declared type is rejected at BOTH the tiny and the unlimited
    /// cap — raising the heartbeat can only ever recover a valid-but-large check,
    /// never accept a non-def-eq term.
    #[test]
    fn test_check_decl_readonly_heartbeat_override_never_accepts_broken() {
        let (env, _good, bad) = env_good_bad();
        // Even at an unlimited cap, a value lacking its declared type is a
        // type_mismatch, NOT a heartbeat failure — so the escalation site (which
        // only fires on HeartbeatExceeded) would never even retry it, and if it
        // did, it would still be rejected here.
        let res = env.check_decl_readonly_with_heartbeat(&bad, Some(0));
        assert!(
            matches!(res, Err(EnvError::TypeCheckFailed { ref source, .. })
                if !matches!(source, crate::tc::TypeError::HeartbeatExceeded { .. })),
            "a broken proof must be a NON-heartbeat rejection at any cap, got: {res:?}"
        );
    }

    /// `None` override is byte-identical to reading `maxHeartbeats` from the env
    /// options: `check_decl_readonly` delegates to `..._with_heartbeat(_, None)`,
    /// so both must agree for the same decl.
    #[test]
    fn test_check_decl_readonly_none_override_matches_wrapper() {
        let (env, good, bad) = env_good_bad();
        for decl in [&good, &bad] {
            assert_eq!(
                env.check_decl_readonly(decl).is_ok(),
                env.check_decl_readonly_with_heartbeat(decl, None).is_ok(),
                "None override must match the wrapper verdict for {decl:?}"
            );
        }
    }
}

#[cfg(test)]
mod upgrade_axiom_to_checked_decl_tests {
    use super::*;
    use crate::expr::Expr;
    use crate::level::Level;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// Happy path: a value-free axiom `foo : Sort 1` is upgraded to the checked
    /// definition `foo : Sort 1 := Sort 0`. The entry must carry the new value,
    /// kind, and pass through with the type preserved.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_happy_path() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("register value-free stub foo : Sort 1");
        let gen_before = env.generation();

        env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("checked upgrade of a value-free stub must succeed");

        let ci = env.get_const(&n("foo")).expect("foo still present");
        assert_eq!(
            ci.value,
            Some(Expr::prop()),
            "upgraded entry must carry the checked value"
        );
        assert_eq!(
            ci.kind,
            ConstantKind::Definition,
            "upgraded entry must carry the new declaration kind"
        );
        assert!(
            env.generation() > gen_before,
            "the swap must bump the environment generation"
        );
    }

    /// Alpha-insensitive level params: stub `c.{u} : Sort (u+1)` accepts the
    /// definition `c.{v} : Sort (v+1) := Sort v` (positional renaming).
    #[test]
    fn test_upgrade_axiom_to_checked_decl_alpha_renamed_levels_accepted() {
        let mut env = Environment::new();
        let u = n("u");
        let v = n("v");
        env.add_decl(Declaration::Axiom {
            name: n("c"),
            level_params: vec![u.clone()],
            type_: Expr::sort(Level::succ(Level::param(u))),
        })
        .expect("register stub c.{u} : Sort (u+1)");

        env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("c"),
            level_params: vec![v.clone()],
            type_: Expr::sort(Level::succ(Level::param(v.clone()))),
            value: Expr::sort(Level::param(v.clone())),
            is_reducible: false,
        })
        .expect("alpha-renamed level params must be accepted (positional binders)");

        let ci = env.get_const(&n("c")).expect("c still present");
        assert_eq!(
            ci.level_params,
            vec![v.clone()],
            "the upgraded entry keeps the incoming declaration's own param names"
        );
        assert_eq!(ci.value, Some(Expr::sort(Level::param(v))));
    }

    /// A declared type that differs from the stub's (and is not def-eq) must be
    /// rejected with the typed mismatch error, leaving the stub untouched.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_wrong_type() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::succ(Level::zero()))), // Sort 2
        })
        .expect("register stub foo : Sort 2");

        let res = env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(), // Sort 1 != Sort 2
            value: Expr::prop(),
            is_reducible: false,
        });
        assert!(
            matches!(res, Err(EnvError::UpgradeTypeMismatch { .. })),
            "a divergent declared type must fail closed, got {res:?}"
        );
        let ci = env.get_const(&n("foo")).expect("stub still present");
        assert!(
            ci.value.is_none(),
            "failed upgrade must not install a value"
        );
    }

    /// Level-param ARITY differences are a type mismatch — alpha-insensitivity
    /// must not relax arity.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_arity_mismatch() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("register stub foo : Sort 1");

        let res = env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![n("u")],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        });
        assert!(
            matches!(res, Err(EnvError::UpgradeTypeMismatch { ref detail, .. })
                if detail.contains("arity")),
            "level-param arity mismatch must fail closed naming the arity, got {res:?}"
        );
    }

    /// An existing constant that already HAS a value is never overwritten.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_value_bearing_target() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("register value-bearing foo");

        let res = env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        });
        assert!(
            matches!(res, Err(EnvError::UpgradeTargetHasValue { .. })),
            "a value-bearing target must never be replaced, got {res:?}"
        );
    }

    /// A value that fails kernel checking must be rejected AND the stub must be
    /// restored verbatim (env unchanged).
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_ill_typed_value() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("register stub foo : Sort 1");

        // `Sort 1 : Sort 2`, not `Sort 1` — check_type must reject the value.
        let res = env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::type_(),
            is_reducible: false,
        });
        assert!(
            matches!(res, Err(EnvError::TypeCheckFailed { .. })),
            "an ill-typed value must be rejected by the add_decl gauntlet, got {res:?}"
        );
        let ci = env
            .get_const(&n("foo"))
            .expect("stub must be restored after a failed upgrade");
        assert!(ci.value.is_none(), "restored stub must remain value-free");
        assert_eq!(ci.type_, Expr::type_(), "restored stub keeps its type");
    }

    /// No existing constant → typed missing-target error (never a blind insert).
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_missing_target() {
        let mut env = Environment::new();
        let res = env.upgrade_axiom_to_checked_decl(Declaration::Definition {
            name: n("ghost"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        });
        assert!(
            matches!(res, Err(EnvError::UpgradeTargetMissing { .. })),
            "upgrading a non-existent constant must fail closed, got {res:?}"
        );
        assert!(
            env.get_const(&n("ghost")).is_none(),
            "a failed upgrade must not insert anything"
        );
    }

    /// An incoming Axiom brings no value — nothing to upgrade to.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_valueless_incoming() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("register stub foo : Sort 1");
        let res = env.upgrade_axiom_to_checked_decl(Declaration::Axiom {
            name: n("foo"),
            level_params: vec![],
            type_: Expr::type_(),
        });
        assert!(
            matches!(res, Err(EnvError::UpgradeValueMissing { .. })),
            "a valueless incoming declaration must be rejected, got {res:?}"
        );
    }

    /// SOUNDNESS: a value that references the constant being upgraded cannot
    /// discharge the stub's trust with itself — the stub is removed during the
    /// check, so the self-reference fails as an unknown constant and the stub
    /// is restored.
    #[test]
    fn test_upgrade_axiom_to_checked_decl_rejects_self_referencing_value() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("P"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("register P : Prop");
        env.add_decl(Declaration::Axiom {
            name: n("selfp"),
            level_params: vec![],
            type_: Expr::const_(n("P"), vec![]),
        })
        .expect("register stub selfp : P");

        // "Proof" of selfp that IS selfp: must fail (unknown constant during
        // the stub-removed check), never succeed.
        let res = env.upgrade_axiom_to_checked_decl(Declaration::Theorem {
            name: n("selfp"),
            level_params: vec![],
            type_: Expr::const_(n("P"), vec![]),
            value: Expr::const_(n("selfp"), vec![]),
        });
        assert!(
            matches!(res, Err(EnvError::TypeCheckFailed { .. })),
            "a self-referencing value must fail the stub-removed check, got {res:?}"
        );
        let ci = env.get_const(&n("selfp")).expect("stub restored");
        assert!(ci.value.is_none(), "stub must remain value-free");
    }
}

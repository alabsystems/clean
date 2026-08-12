// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cheap, sound structural-integrity audits over a built `.mathverse` shard —
//! release gates that catch corruption which would otherwise only surface as a
//! mass of kernel-verification failures much later (and much more expensively).
//!
//! # Level-parameter contiguity audit
//!
//! A constant's universe parameter names are stored as a CONTIGUOUS window
//! `strings[level_params_start .. level_params_start + level_params_count]`
//! (written via [`crate::shard::ShardWriter::add_string_block`], which bypasses
//! the string-dedup cache precisely to keep the window contiguous). A build that
//! instead interns level-param names through the deduplicating `add_string`
//! path records `level_params_start` as the *deduplicated* index of the FIRST
//! parameter; for any constant with ≥2 universe parameters the remaining window
//! slots then read unrelated strings (leaked constant names) as universe
//! parameters. Reconstruction hands those bogus names to the kernel, which
//! rejects the declaration with `UndefinedLevelParam` — silently failing every
//! multi-universe constant (i.e. most of a real Mathlib corpus).
//!
//! [`audit_level_param_integrity`] detects this WITHOUT running the kernel: a
//! genuine Lean universe parameter is either a plain identifier (`u`, `v`,
//! `u_1`, `u₁`, `w'`) or a hygienic name carrying Lean's macro-scope markers
//! (`._@.` / `._hyg`), e.g. a `noConfusion` motive universe
//! `v._@.Init.MetaTypes.502562599._hygCtx._hyg.13`. Anything else that contains
//! a namespace separator (`.`) — e.g. `Option.some`, `binderNameHint.eq_1` — is
//! a leaked constant name and hence a corruption. The check is SOUND (a valid
//! universe parameter, plain or hygienic, never trips it, so there are no false
//! positives); it is not complete (a leaked name that is dot-free, or that
//! happens to carry a hygiene marker, is not flagged), but on real corpora the
//! leaked slots are overwhelmingly plain dotted constant names, so it is a
//! strong, cheap release signal.

use crate::inductive_replay::reconstruct_constant;
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_level_params;
use crate::types::DeclKind;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::{Expr, Name};

/// A single corrupt constant surfaced by [`audit_level_param_integrity`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LevelParamCorruption {
    /// The constant whose reconstructed level parameters are corrupt.
    pub constant: String,
    /// The reconstructed level-parameter names (some of which are not valid
    /// universe identifiers).
    pub params: Vec<String>,
}

/// Result of a level-parameter contiguity audit over a shard.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct LevelParamIntegrityReport {
    /// Constants carrying at least one level parameter (the population audited).
    pub with_params: usize,
    /// Constants whose reconstructed level parameters include a name that is not
    /// a valid universe identifier (contains a `.`), i.e. a contiguity
    /// corruption.
    pub corrupt: usize,
    /// A bounded sample of corrupt constants (first [`SAMPLE_LIMIT`] by scan
    /// order) for diagnostics.
    pub sample: Vec<LevelParamCorruption>,
}

impl LevelParamIntegrityReport {
    /// Corruption rate over the population that actually carries level
    /// parameters (0.0 when no constant has any).
    #[must_use]
    pub fn corrupt_rate(&self) -> f64 {
        if self.with_params == 0 {
            0.0
        } else {
            self.corrupt as f64 / self.with_params as f64
        }
    }

    /// `true` when every level-parameter window reconstructs to valid universe
    /// identifiers — the invariant a correctly-built shard must satisfy.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.corrupt == 0
    }
}

/// Maximum number of corrupt constants retained in
/// [`LevelParamIntegrityReport::sample`].
pub const SAMPLE_LIMIT: usize = 32;

/// A genuine Lean universe parameter is either a plain identifier (`u`, `v`,
/// `u_1`, `u₁`, `w'`, …) or a HYGIENIC name that carries Lean's macro-scope
/// markers (`._@.` / `._hyg`), such as a `noConfusion` motive universe
/// `v._@.Init.MetaTypes.502562599._hygCtx._hyg.13`. Any OTHER name that contains
/// a namespace separator (`.`) is a leaked constant name from a non-contiguous
/// (dedup-corrupted) `level_params` window.
///
/// SOUND: valid universe parameters — plain or hygienic — never trip this, so it
/// never false-flags a correctly built shard. An empty name is invalid.
#[must_use]
fn is_valid_universe_param(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    if !name.contains('.') {
        // Plain universe identifier (the common case).
        return true;
    }
    // Dotted, but a hygienic universe name — Lean's macro hygiene stamps `._@.`
    // (scope) and/or `._hyg` (hygienic id) into generated universe parameters.
    name.contains("._@.") || name.contains("._hyg")
}

/// Audit every constant's level-parameter window for the contiguity corruption
/// described at the module level. Reads only the string table (no kernel, no
/// expression reconstruction), so it is cheap enough to run as a release gate on
/// a full corpus.
#[must_use]
pub fn audit_level_param_integrity(reader: &ShardReader) -> LevelParamIntegrityReport {
    let mut report = LevelParamIntegrityReport::default();
    for constant in &reader.constants {
        if constant.level_params_count == 0 {
            continue;
        }
        report.with_params += 1;
        let params = match reconstruct_level_params(
            &reader.strings,
            constant.level_params_start,
            constant.level_params_count,
        ) {
            Ok(p) => p,
            // An out-of-range window is itself a corruption; count it and, when
            // there is room, sample it with whatever name we can recover.
            Err(_) => {
                report.corrupt += 1;
                if report.sample.len() < SAMPLE_LIMIT {
                    let name = reader
                        .strings
                        .get(constant.name_idx as usize)
                        .cloned()
                        .unwrap_or_else(|| format!("<name_idx {}>", constant.name_idx));
                    report.sample.push(LevelParamCorruption {
                        constant: name,
                        params: vec!["<window out of range>".to_string()],
                    });
                }
                continue;
            }
        };
        let param_strings: Vec<String> = params.iter().map(ToString::to_string).collect();
        if param_strings.iter().any(|p| !is_valid_universe_param(p)) {
            report.corrupt += 1;
            if report.sample.len() < SAMPLE_LIMIT {
                let name = reader
                    .strings
                    .get(constant.name_idx as usize)
                    .cloned()
                    .unwrap_or_else(|| format!("<name_idx {}>", constant.name_idx));
                report.sample.push(LevelParamCorruption {
                    constant: name,
                    params: param_strings,
                });
            }
        }
    }
    report
}

/// A recursor member carries the same universe parameters as its inductive
/// family; kept `pub` so callers can filter the audit by kind if desired.
#[must_use]
pub fn is_recursor_kind(decl_kind: u8) -> bool {
    DeclKind::try_from(decl_kind) == Ok(DeclKind::Recursor)
}

// ===========================================================================
// In-memory level-parameter REPAIR
// ===========================================================================

/// Collect the universe parameters referenced in a `Level`, appending each new
/// name to `seen` in first-occurrence order.
fn collect_level_params_in_level(level: &Level, seen: &mut Vec<Name>) {
    match level {
        Level::Zero => {}
        Level::Succ(l) => collect_level_params_in_level(l, seen),
        Level::Max(a, b) | Level::IMax(a, b) => {
            collect_level_params_in_level(a, seen);
            collect_level_params_in_level(b, seen);
        }
        Level::Param(n) => {
            if !seen.contains(n) {
                seen.push(n.clone());
            }
        }
    }
}

/// Collect the free universe parameters referenced anywhere in an expression
/// (in `Sort` levels and `Const` universe arguments), in first-occurrence order.
/// This is exactly the set a declaration's `level_params` must contain, so it is
/// the authoritative source for reconstructing a corrupted `level_params`
/// window from the (intact) type/value expression.
fn collect_level_params_in_expr(expr: &Expr, seen: &mut Vec<Name>) {
    match expr.kind() {
        ExprKind::Sort(level) => collect_level_params_in_level(level, seen),
        ExprKind::Const(_, levels) => {
            for level in levels.iter() {
                collect_level_params_in_level(level, seen);
            }
        }
        ExprKind::App(f, a) => {
            collect_level_params_in_expr(f, seen);
            collect_level_params_in_expr(a, seen);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_level_params_in_expr(ty, seen);
            collect_level_params_in_expr(body, seen);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_level_params_in_expr(ty, seen);
            collect_level_params_in_expr(val, seen);
            collect_level_params_in_expr(body, seen);
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => {
            collect_level_params_in_expr(e, seen);
        }
        // BVar/FVar/Lit/SProp/Cubical* carry no universe parameters.
        _ => {}
    }
}

/// Outcome of an in-memory [`repair_level_params`] pass.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct LevelParamRepairStats {
    /// Constants carrying at least one level parameter (the population scanned).
    pub examined: usize,
    /// Corrupt constants whose `level_params` window was rewritten from the
    /// (intact) type/value universe references.
    pub repaired: usize,
    /// Corrupt constants that could not be repaired (type failed to reconstruct,
    /// or no universe parameter was recoverable from type or value).
    pub unrepairable: usize,
}

/// Repair the dedup-corrupted `level_params` windows of a shard **in memory**,
/// WITHOUT rebuilding from source. For each constant the level-param audit flags
/// as corrupt, the correct universe-parameter list is recomputed from the
/// (intact) reconstructed type/value: the free universe parameters of the type
/// (then value, for body-only params) in first-occurrence order.
///
/// ORDER matters: the corruption stores `level_params_start` at the deduplicated
/// index of the FIRST parameter and scrambles only the rest, so `strings[start]`
/// (the reconstructed first param) is RELIABLE. Lean's declared order does not
/// always equal first-occurrence-in-type order (e.g. `Quiver.{v,u}` — the
/// morphism universe `v` is declared first, but `u` occurs first in the type
/// `Type u`). A wrong order makes a constructor's self-reference
/// `Const(I, levels)` look like a *different* instance of `I`, which the kernel's
/// occurrence check rejects with "non valid occurrence of the datatypes being
/// declared". We therefore ANCHOR on the reliable stored first param and append
/// the remaining free params — recovering the exact order for every 2-parameter
/// declaration (the common structure case) and the correct leading param for the
/// rest.
///
/// This is exactly the set a well-formed declaration's `level_params` must
/// contain (`Lean.collectLevelParams`).
///
/// SOUNDNESS: the repair only supplies universe-parameter NAMES for
/// reconstruction; the kernel still fully re-typechecks every value through
/// `add_decl` afterwards. A mis-ordered or incomplete repair can only cause a
/// downstream false-REJECT (a `Const` reference whose positional level arguments
/// no longer line up), never a false KernelVerified — the kernel is still the
/// sole oracle. Clean (non-corrupt) constants are left untouched.
pub fn repair_level_params(reader: &mut ShardReader) -> LevelParamRepairStats {
    let mut stats = LevelParamRepairStats::default();

    // Phase 1 — compute corrections under an immutable borrow.
    let mut fixes: Vec<(usize, Vec<String>)> = Vec::new();
    for i in 0..reader.constants.len() {
        let constant = &reader.constants[i];
        if constant.level_params_count == 0 {
            continue;
        }
        stats.examined += 1;

        let current = reconstruct_level_params(
            &reader.strings,
            constant.level_params_start,
            constant.level_params_count,
        )
        .unwrap_or_default();
        let corrupt = current.len() != constant.level_params_count as usize
            || current
                .iter()
                .any(|p| !is_valid_universe_param(&p.to_string()));
        if !corrupt {
            continue;
        }

        let Some(name) = reader.strings.get(constant.name_idx as usize) else {
            stats.unrepairable += 1;
            continue;
        };
        let Ok(rc) = reconstruct_constant(name, reader, constant) else {
            stats.unrepairable += 1;
            continue;
        };
        let mut seen: Vec<Name> = Vec::new();
        collect_level_params_in_expr(&rc.type_expr, &mut seen);
        if let Some(value) = &rc.value_expr {
            collect_level_params_in_expr(value, &mut seen);
        }
        if seen.is_empty() {
            stats.unrepairable += 1;
            continue;
        }
        // Anchor on the reliably-stored first param (the corruption scrambles
        // only params [1..]): move it to the front of the recovered set so the
        // declared order is preserved for every ≤2-param declaration.
        if let Some(anchor) = current
            .first()
            .filter(|p| is_valid_universe_param(&p.to_string()))
        {
            if let Some(pos) = seen.iter().position(|p| p == anchor) {
                let a = seen.remove(pos);
                seen.insert(0, a);
            }
        }
        fixes.push((i, seen.iter().map(ToString::to_string).collect()));
    }

    // Phase 2 — apply corrections under a mutable borrow. Each block is appended
    // contiguously (no dedup), preserving the `[start..start+count)` invariant.
    for (i, params) in fixes {
        let start = reader.strings.len() as u32;
        for p in &params {
            reader.strings.push(p.clone());
        }
        reader.constants[i].level_params_start = start;
        reader.constants[i].level_params_count = params.len() as u16;
        stats.repaired += 1;
    }

    stats
}

#[cfg(test)]
#[path = "shard_integrity_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection mask for fast-path optimizations in reset/reuse expansion.
//!
//! Tracks which FVarIds are projections of the reset target object and their
//! field indices. Used to erase redundant `_inc` ops (Bug 16 / eraseProjIncFor)
//! and skip self-set stores (Bug 17 / partitionSelfSets).
//!
//! Reference: Lean 4 ExpandResetReuse.lean:75-107 (Mask type)
//! Part of #2059.

use std::collections::HashMap;

use crate::lcnf::{Alt, Arg, Code, LetValue};
use crate::rc::pseudo_op;
use clean_kernel::FVarId;

/// Projection mask: maps projected FVarId → field index.
///
/// Used on the fast path to:
/// - Erase redundant `_inc` for projected fields (Bug 16 / eraseProjIncFor)
/// - Skip self-set stores where a field is written back to its original position
///   (Bug 17 / partitionSelfSets)
pub(crate) type ProjMask = HashMap<FVarId, u32>;

/// Projection source metadata: `proj_fvar -> (structure, absolute field idx)`.
pub(crate) type ProjSources = HashMap<FVarId, (FVarId, u32)>;

/// Collect projection bindings from an arbitrary code tree.
pub(crate) fn build_proj_sources_for_code(code: &Code) -> ProjSources {
    let mut sources = ProjSources::new();
    collect_proj_sources_impl(code, &mut sources);
    sources
}

/// Filter declaration-scope projection sources down to one target object.
pub(crate) fn mask_for_target(sources: &ProjSources, target: FVarId) -> ProjMask {
    sources
        .iter()
        .filter_map(|(proj_fvar, (structure, idx))| {
            (*structure == target).then_some((*proj_fvar, *idx))
        })
        .collect()
}

fn collect_proj_sources_impl(code: &Code, sources: &mut ProjSources) {
    match code {
        Code::Let(decl, body) => {
            if let LetValue::Proj { structure, idx, .. } = &decl.value {
                sources.insert(decl.fvar_id, (*structure, *idx));
            }
            collect_proj_sources_impl(body, sources);
        }
        Code::Fun(fun_decl, body) => {
            collect_proj_sources_impl(&fun_decl.body, sources);
            collect_proj_sources_impl(body, sources);
        }
        Code::JoinPoint(jp_decl, body) => {
            collect_proj_sources_impl(&jp_decl.body, sources);
            collect_proj_sources_impl(body, sources);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_proj_sources_impl(body, sources),
                    Alt::Default(body) => collect_proj_sources_impl(body, sources),
                }
            }
        }
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => {}
    }
}

/// Check if a let-value is `_inc` of a variable in the projection mask.
///
/// On the fast path, `_inc` for projected fields is redundant: the object
/// has exclusive ownership (refcount == 1), so projected field values
/// already have correct refcounts without an extra increment.
#[cfg(test)]
pub(crate) fn is_inc_of_masked(value: &LetValue, mask: &ProjMask) -> bool {
    match value {
        LetValue::Const { name, args, .. } => {
            name.to_string() == pseudo_op::INC
                && matches!(args.first(), Some(Arg::FVar(fvar)) if mask.contains_key(fvar))
        }
        _ => false,
    }
}

/// Check if a let-value is `_dec` of a specific FVar.
///
/// Used on the fast path to convert `_dec token` → `_del token` (Bug 19 / #2059).
pub(crate) fn is_dec_of(value: &LetValue, target: FVarId) -> bool {
    match value {
        LetValue::Const { name, args, .. } => {
            name.to_string() == pseudo_op::DEC
                && matches!(args.first(), Some(Arg::FVar(fvar)) if *fvar == target)
        }
        _ => false,
    }
}

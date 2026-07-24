// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **subsingleton / large-elimination** gate (design §2, §5.2) — the
//! soundness-critical determination of whether a `Prop`-valued inductive may
//! eliminate into `Type u`.
//!
//! Transcribed from Lean's kernel `elim_only_at_universe_zero`
//! (`inductive.cpp`). The rule (design §2, stated as a rule, not by example):
//!
//! > A `Prop` inductive large-eliminates **iff** it has `<= 1` constructor AND
//! > every constructor argument is **either itself a `Prop`, or appears as a
//! > _bare index argument_ of the constructor's result type** — recovered by
//! > *matching*, never *computed*.
//!
//! `Eq` / `And` / `False` / `Acc` qualify. `Int.NonNeg` does **not** (its `Nat`
//! field sits *under* `Int.ofNat` in the index `Int.NonNeg (Int.ofNat n)`, so it
//! is not a *bare* index — the membership test is a direct-`BVar` match, not an
//! occurrence test). `Or` does **not** (two constructors).
//!
//! Over-permissiveness here is a false-*accept* with no differential oracle
//! (design §12), so this predicate is the highest-risk surface and is
//! adversarially tested.

use crate::budget::Budget;
use crate::inductive::{split_ctor_telescope, InductiveDecl};
use crate::level::Level;
use crate::term::{Term, TermKind};
use crate::validate::Env;

/// True iff the inductive may eliminate into an arbitrary universe (large
/// elimination); false iff it is restricted to `Prop`-only elimination.
///
/// Returns `false` (the conservative / fail-closed answer) whenever a field's
/// sort cannot be inferred — too-restrictive is sound (we merely forbid a legal
/// large recursor), whereas too-permissive would break proof irrelevance.
pub(crate) fn large_eliminates(env: &dyn Env, decl: &InductiveDecl, ind_sort: &Level) -> bool {
    !elim_only_at_universe_zero(env, decl, ind_sort)
}

/// Block-aware large-elimination determination (design §5.2: "the subsingleton
/// gate must account for the whole block"). The block large-eliminates iff
/// **every** type in it would large-eliminate on its own AND the block has a
/// single type. A mutual block of more than one type is conservatively
/// Prop-only-eliminating: Lean restricts large elimination for genuinely mutual
/// Prop families, and over-permissiveness here is a false-*accept* with no
/// differential oracle — so we take the sound, conservative direction (at worst
/// we forbid a legal large recursor). A non-`Prop` block always large-eliminates
/// (the `Prop` gate does not apply).
pub(crate) fn block_large_eliminates(
    env: &dyn Env,
    block: &crate::mutual::MutualBlock,
    ind_sorts: &[Level],
) -> bool {
    // If no type is in Prop, large elimination is unconditionally allowed.
    let any_prop = ind_sorts.iter().any(Level::is_zero);
    if !any_prop {
        return true;
    }
    // Some type is in Prop. A genuinely mutual (N > 1) Prop block is Prop-only
    // (conservative + sound). A single-element block defers to the standard
    // single-type subsingleton predicate.
    if block.decls.len() != 1 {
        return false;
    }
    let decl = &block.decls[0];
    let sort = &ind_sorts[0];
    !elim_only_at_universe_zero(env, decl, sort)
}

/// Mirror of Lean's `elim_only_at_universe_zero`. `true` ⇒ Prop-only
/// elimination (no extra motive universe param); `false` ⇒ large elimination.
fn elim_only_at_universe_zero(env: &dyn Env, decl: &InductiveDecl, ind_sort: &Level) -> bool {
    // Not in Prop → large elimination always allowed.
    if !ind_sort.is_zero() {
        return false;
    }

    // M2 is single (non-mutual); mutual Prop predicates would be Prop-only here.
    if decl.constructors.len() > 1 {
        return true; // multiple constructors (e.g. Or) → Prop-only
    }
    if decl.constructors.is_empty() {
        return false; // empty type (e.g. False) → large elimination
    }

    // Exactly one constructor. Infer each non-param field's sort.
    let ctor = &decl.constructors[0];
    let (field_tys, _ret) = split_ctor_telescope(&ctor.type_, decl.num_params);

    let mut budget = Budget::default_budget();
    let mut field_sorts: Vec<Level> = Vec::with_capacity(field_tys.len());
    // Context: [params..., earlier fields...] for de-Bruijn-correct sort inference.
    let mut ctx: Vec<Term> = Vec::new();
    for param_ty in pi_param_domains(&ctor.type_, decl.num_params) {
        ctx.push(param_ty);
    }
    for field_ty in &field_tys {
        match crate::infer::infer_sort_in_context(env, &ctx, field_ty, &mut budget) {
            Ok(l) => field_sorts.push(l),
            Err(_) => {
                // Type checking failed — conservatively restrict to Prop-only
                // (sound: at worst too-restrictive). Matches Lean returning true.
                return true;
            }
        }
        ctx.push(field_ty.clone());
    }

    // Non-Prop field positions (0-indexed from first non-param field).
    let non_prop_fields: Vec<u32> = field_sorts
        .iter()
        .enumerate()
        .filter(|(_, level)| !level.is_zero())
        .filter_map(|(i, _)| u32::try_from(i).ok())
        .collect();

    if non_prop_fields.is_empty() {
        return false; // all fields in Prop → large elimination allowed
    }

    // Condition 2: every non-Prop field must appear as a BARE INDEX argument of
    // the constructor's result type. Collect the result-type args (after params).
    let ret = crate::inductive::return_type(&ctor.type_);
    let (_head, ret_args) = ret.unfold_apps();
    let np = usize::try_from(decl.num_params).unwrap_or(usize::MAX);
    let index_args: Vec<&Term> = ret_args.iter().skip(np).collect();

    // Total fields = number of constructor binders after params. Under the full
    // constructor telescope (params + fields), field f (0-indexed) is bound at
    // de Bruijn index `total_fields - 1 - f` inside the result type (which sits
    // under all binders). The bare-index test is a DIRECT BVar match (Lean's
    // `std::find(result_args, arg)`), never an occurrence-anywhere test — this is
    // exactly what rejects `Int.NonNeg` (its `n` is under `Int.ofNat`).
    let total_fields = match u32::try_from(field_sorts.len()) {
        Ok(n) => n,
        Err(_) => return true, // pathological field count → conservative
    };
    for field_pos in &non_prop_fields {
        let bvar_idx = total_fields.saturating_sub(1).saturating_sub(*field_pos);
        let found = index_args
            .iter()
            .any(|arg| matches!(arg.kind(), TermKind::BVar(idx) if *idx == bvar_idx));
        if !found {
            return true; // non-Prop field is not a bare index → Prop-only
        }
    }

    false // every non-Prop field is a bare index → large elimination allowed
}

/// The first `num_params` Pi domain types of a constructor type (its parameters).
fn pi_param_domains(ctor_ty: &Term, num_params: u32) -> Vec<Term> {
    let mut out = Vec::new();
    let mut cur = ctor_ty.clone();
    let mut got: u32 = 0;
    while got < num_params {
        match cur.kind() {
            TermKind::Pi(_, dom, codom) => {
                out.push(dom.clone());
                cur = codom.clone();
                got = got.saturating_add(1);
            }
            _ => break,
        }
    }
    out
}

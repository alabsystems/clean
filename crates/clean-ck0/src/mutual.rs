// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Mutual** inductive admission (design §5.2, milestone M3) — the
//! [`add_inductive_mutual`] entry point that admits a block of `N` inductives
//! defined together, lifting the M2 `Unsupported` rejection.
//!
//! The recursor for the block has `N` **motives** (one per type) and **minor**
//! premises covering *all* constructors of *all* types. A constructor field is
//! **recursive** if it mentions *any* type in the mutual block — not just its
//! own (design M3). Each type's recursor is derived with the correct
//! motive/minor/level signature and ι-rules, and every generated recursor type
//! is kernel-CHECKED at admission.
//!
//! Positivity, the universe constraint, and the subsingleton / large-elim gate
//! account for the whole block: positivity rejects a non-strictly-positive
//! occurrence of *any* block type; the universe constraint is checked per
//! constructor against its own type's sort; and the large-elim determination
//! treats the block as Prop-only-eliminating unless *every* type is a
//! subsingleton (the conservative, sound direction — a single non-subsingleton
//! type forbids large elimination for the whole block).
//!
//! A single-element block (`N == 1`) is admissible here and produces exactly
//! the same recursor the M2 [`crate::add_inductive`] path produces (the
//! multi-motive builder degenerates to the single-motive one); M2 remains the
//! entry point for genuinely single inductives so its behaviour is untouched.

use crate::budget::Budget;
use crate::elim_analysis::block_large_eliminates;
use crate::inductive::{
    check_universe_constraint_block, inductive_result_level, split_ctor_telescope, AdmitError,
    InductiveDecl,
};
use crate::inductive_params::validate_num_params_block;
use crate::level::Level;
use crate::name::Name;
use crate::positivity::check_positivity_ctor_block;
use crate::recursor::RecursorData;
use crate::recursor_mutual::build_block_recursors;
use crate::staging_env::MutualStagingEnv;
use crate::term::{Term, TermKind};

/// A mutual inductive block: `N` inductives sharing `num_params` leading
/// parameters and `num_level_params` universe params, defined together. The
/// individual [`InductiveDecl`]s carry each type's own type former and
/// constructors; `num_params`/`num_level_params` must agree across the block
/// (Lean requires a mutual block to share its parameter and level telescope).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutualBlock {
    /// The inductive declarations, in block order. Their order fixes the motive
    /// order in every derived recursor.
    pub decls: Vec<InductiveDecl>,
}

impl MutualBlock {
    /// The shared parameter count (taken from the first decl; agreement is
    /// checked in [`add_inductive_mutual`]).
    #[must_use]
    pub fn num_params(&self) -> u32 {
        self.decls.first().map_or(0, |d| d.num_params)
    }

    /// The shared universe-param count.
    #[must_use]
    pub fn num_level_params(&self) -> u32 {
        self.decls.first().map_or(0, |d| d.num_level_params)
    }

    /// The names of every type in the block, in order.
    #[must_use]
    pub fn type_names(&self) -> Vec<Name> {
        self.decls.iter().map(|d| d.name.clone()).collect()
    }
}

/// The full record of an admitted mutual block: each type's derived recursor,
/// the per-type large-elim flag (uniform across the block), and the block decls.
/// Stored so the env can read the recursors back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedMutual {
    /// The block declarations.
    pub block: MutualBlock,
    /// Whether the block large-eliminates (uniform: all-or-none).
    pub large_elim: bool,
    /// One derived recursor per type, in block order.
    pub recursors: Vec<RecursorData>,
}

/// The env-write surface for mutual admission. Like
/// [`crate::inductive::MutableEnv`] there is **no** `_unchecked` path: the only
/// way to register a block is [`add_inductive_mutual`], which derives and
/// kernel-checks every recursor.
pub trait MutableMutualEnv: crate::inductive::MutableEnv {
    /// Commit a fully-derived, kernel-checked mutual block (its decls, derived
    /// recursors, constructors and ι-rules) into the env atomically. Called only
    /// by [`add_inductive_mutual`] after every check has passed.
    fn commit_mutual(&mut self, admitted: AdmittedMutual);
}

/// Admit a mutual inductive block into `env`, deriving and kernel-checking each
/// type's recursor. **One total function**; every failure is a `Rejected`
/// [`AdmitError`]. Idempotent re-admission of a structurally-identical block is
/// `Ok(())`.
pub fn add_inductive_mutual(
    env: &mut dyn MutableMutualEnv,
    block: MutualBlock,
) -> Result<(), AdmitError> {
    if block.decls.is_empty() {
        return Err(AdmitError::Derivation {
            ind: Name::anonymous(),
            detail: "empty mutual block".to_string(),
        });
    }

    // A genuinely single inductive routes through the dedicated M2 entry point so
    // its behaviour is byte-identical; here we still admit N == 1 (used by the
    // nested→mutual auxiliary path), where the multi-motive builder degenerates.
    let block_names = block.type_names();

    // (0) Shared-telescope agreement: every decl must declare the same
    // num_params and num_level_params (a mutual block shares them).
    let np = block.num_params();
    let nlp = block.num_level_params();
    for d in &block.decls {
        if d.num_params != np || d.num_level_params != nlp {
            return Err(AdmitError::Derivation {
                ind: d.name.clone(),
                detail: "mutual block decls disagree on num_params/num_level_params".to_string(),
            });
        }
    }

    // (1) idempotency / conflict over the whole block (structural identity).
    let mut all_known = true;
    let mut any_known = false;
    for d in &block.decls {
        if env.has_inductive(&d.name) {
            any_known = true;
            match env.admitted_mutual_decl(&d.name) {
                Some(prev) if prev == *d => {}
                _ => {
                    return Err(AdmitError::Conflict {
                        name: d.name.clone(),
                    })
                }
            }
        } else {
            all_known = false;
        }
    }
    if any_known && all_known {
        return Ok(()); // idempotent re-add of the identical block
    }
    if any_known {
        // A partial overlap (some names exist, some don't) is a conflict: the
        // block is not the one already admitted.
        return Err(AdmitError::Conflict {
            name: block.decls[0].name.clone(),
        });
    }

    // (1b) structural num_params validation for every type (fail-closed).
    for d in &block.decls {
        validate_num_params_block(d, &block_names)?;
    }

    // (2) strict positivity over the WHOLE block: a field may not mention ANY
    // block type non-strictly-positively.
    for d in &block.decls {
        for ctor in &d.constructors {
            check_positivity_ctor_block(&*env, &block_names, &ctor.type_).map_err(|()| {
                AdmitError::NonPositive {
                    ind: d.name.clone(),
                    ctor: ctor.name.clone(),
                }
            })?;
        }
    }

    // Staging env knows every block type former + every constructor (none are
    // committed yet) so field-sort inference / the gate / the recursor
    // kernel-check can resolve them.
    let staging = MutualStagingEnv::new(env, &block);

    // (3) universe constraint per type (is_geq on canonical levels).
    let mut ind_sorts: Vec<Level> = Vec::with_capacity(block.decls.len());
    for d in &block.decls {
        let s = inductive_result_level(d).ok_or_else(|| AdmitError::Derivation {
            ind: d.name.clone(),
            detail: "inductive result type is not a Sort".to_string(),
        })?;
        ind_sorts.push(s);
    }
    for (d, s) in block.decls.iter().zip(ind_sorts.iter()) {
        check_universe_constraint_block(&staging, d, s)?;
    }

    // (4) subsingleton / large-elim for the block (all-or-none, conservative).
    let large_elim = block_large_eliminates(&staging, &block, &ind_sorts);

    // (5) build + kernel-check every type's recursor against the staging env.
    let recursors = build_block_recursors(&staging, &block, &ind_sorts, large_elim)?;
    drop(staging);

    env.commit_mutual(AdmittedMutual {
        block,
        large_elim,
        recursors,
    });
    Ok(())
}

/// True iff constructor field `field_ty`'s return-type head (after stripping its
/// own Pi binders) is a *block* type applied directly — i.e. the field is
/// recursive in the mutual sense (mentions ANY block type as its recursive
/// target). Mirrors [`crate::recursor`]'s single-inductive `is_recursive_field`,
/// generalized to the block.
pub(crate) fn is_recursive_field_block(block_names: &[Name], field_ty: &Term) -> bool {
    let mut cur = field_ty.clone();
    while let TermKind::Pi(_, _, body) = cur.kind() {
        cur = body.clone();
    }
    let (head, _args) = cur.unfold_apps();
    matches!(head.kind(), TermKind::Const(c) if block_names.iter().any(|n| n == c.name()))
}

/// The motive index (position in the block) a recursive field targets: the
/// block-type its return-type head names. Mirrors the reference
/// `field_motive_index`. Returns `0` if the head is not a block type (shouldn't
/// happen for a field already classified recursive).
pub(crate) fn field_motive_index_block(block_names: &[Name], field_ty: &Term) -> usize {
    let mut cur = field_ty.clone();
    while let TermKind::Pi(_, _, body) = cur.kind() {
        cur = body.clone();
    }
    let (head, _args) = cur.unfold_apps();
    if let TermKind::Const(c) = head.kind() {
        if let Some(idx) = block_names.iter().position(|n| n == c.name()) {
            return idx;
        }
    }
    0
}

/// Per-constructor info for one constructor of one block type, tagged with the
/// motive (type) index it belongs to. The "global" constructor list (all
/// constructors of all types, in block-then-declaration order) drives the minor
/// premises.
pub(crate) struct BlockCtorInfo {
    /// The constructor name.
    pub(crate) name: Name,
    /// The index (in the block) of the type this constructor belongs to.
    pub(crate) owner_type_idx: usize,
    /// Field domain types (after params), level-shifted into the recursor's
    /// telescope by the caller.
    pub(crate) field_tys: Vec<Term>,
    /// Per-field recursive flag.
    pub(crate) recursive: Vec<bool>,
    /// Per-field motive index a recursive field targets (only meaningful where
    /// `recursive[i]`).
    pub(crate) field_motive: Vec<usize>,
    /// The constructor's result-type indices (after params).
    pub(crate) return_indices: Vec<Term>,
    /// The constructor's field count.
    pub(crate) num_fields: u32,
}

/// Gather the global ordered constructor list for the whole block, tagging each
/// constructor with its owner-type index and the block-recursive analysis. The
/// `ind_level_subst` is applied to lift field types / indices into the
/// recursor's level telescope (identity when small-elim).
pub(crate) fn gather_block_ctor_infos(
    block: &MutualBlock,
    ind_level_subst: &[Level],
) -> Result<Vec<BlockCtorInfo>, AdmitError> {
    let block_names = block.type_names();
    let np = block.num_params();
    let mut out = Vec::new();
    for (type_idx, d) in block.decls.iter().enumerate() {
        for ctor in &d.constructors {
            let (field_tys, ret) = split_ctor_telescope(&ctor.type_, np);
            let recursive: Vec<bool> = field_tys
                .iter()
                .map(|f| is_recursive_field_block(&block_names, f))
                .collect();
            let field_motive: Vec<usize> = field_tys
                .iter()
                .map(|f| field_motive_index_block(&block_names, f))
                .collect();
            let field_tys: Vec<Term> = field_tys
                .into_iter()
                .map(|t| t.instantiate_levels(ind_level_subst))
                .collect();
            let num_fields =
                u32::try_from(field_tys.len()).map_err(|_| AdmitError::Derivation {
                    ind: d.name.clone(),
                    detail: "too many fields".to_string(),
                })?;
            let (_h, ret_args) = ret.unfold_apps();
            let np_us = usize::try_from(np).unwrap_or(usize::MAX);
            let return_indices: Vec<Term> = ret_args
                .into_iter()
                .skip(np_us)
                .map(|t| t.instantiate_levels(ind_level_subst))
                .collect();
            out.push(BlockCtorInfo {
                name: ctor.name.clone(),
                owner_type_idx: type_idx,
                field_tys,
                recursive,
                field_motive,
                return_indices,
                num_fields,
            });
        }
    }
    Ok(out)
}

/// The (immutable) budget the block admission uses for kernel-checks.
pub(crate) fn admission_budget() -> Budget {
    Budget::default_budget()
}

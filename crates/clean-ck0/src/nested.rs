// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Nested** inductive admission (design §5.2, §7, milestone M3): a constructor
//! field that nests the inductive being defined inside another type's
//! strictly-positive argument — e.g. `RoseTree` with `mk : List RoseTree ->
//! RoseTree`. Compiled to a **mutual** block via the *auxiliary construction*
//! (mirroring the Lean-faithful reference
//! `crates/clean-kernel/src/env/inductive_nested_{replace,elim}.rs`):
//!
//! 1. **Collect** distinct nested container occurrences `Container args…` where
//!    some `arg` mentions the type being defined.
//! 2. **Build an auxiliary inductive** per occurrence that unfolds the container:
//!    substitute the container's parameters with the occurrence's actual args and
//!    its level params with the occurrence's level args, then replace
//!    `Container args` self-references with the auxiliary type.
//! 3. **Rewrite** the original constructors to reference the auxiliary types.
//! 4. **Admit the mutual block** `[original, aux…]` via
//!    [`crate::add_inductive_mutual`]; the nested type's recursor is the
//!    block-recursor of the original type. **Every derived recursor type is
//!    kernel-checked** — a wrong auxiliary encoding is a false-*accept*, so it is
//!    caught there and rejected (design §5.2).
//!
//! **Nested positivity.** The nesting must occur in a **strictly-positive**
//! position of the nesting container; a non-strictly-positive nesting is
//! rejected ([`NestedError::NonStrictlyPositiveNesting`]) — never compiled to a
//! weak recursor. The strict-positivity of the *unfolded* block is additionally
//! re-checked by `add_inductive_mutual`.

use std::sync::Arc;

use crate::inductive::{AdmitError, InductiveDecl};
use crate::level::Level;
use crate::mutual::{add_inductive_mutual, MutableMutualEnv, MutualBlock};
use crate::name::Name;
use crate::nested_replace::{args_key, OccIndex};
use crate::recursor::MAX_DERIVED_ARITY;
use crate::term::{Term, TermKind};
use crate::validate::Env;

mod auxiliary;
mod closure;
mod collect;
mod names;
mod size;
use auxiliary::build_auxiliary;
pub use size::MAX_AUX_SIZE;
use size::{rewrite_growth, At, Room};

/// Errors specific to nested-inductive admission. Every variant is a *reject*.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum NestedError {
    /// The declaration has no nested occurrence — callers should use
    /// [`crate::add_inductive`] (single) instead. Surfaced so a mis-routed
    /// non-nested decl is an explicit reject, not a silent mutual block of one.
    #[error("inductive '{name}': no nested occurrence found (use add_inductive)")]
    NotNested {
        /// The inductive name.
        name: Name,
    },
    /// A nesting container is not a known inductive in the env, so its
    /// constructors cannot be unfolded faithfully. Fail-closed (a guessed
    /// encoding would be a false-accept).
    #[error("inductive '{ind}': nesting container '{container}' is not a known inductive")]
    UnknownContainer {
        /// The inductive being defined.
        ind: Name,
        /// The unknown container.
        container: Name,
    },
    /// The nesting occurs in a non-strictly-positive position of the container
    /// (e.g. nested under an arrow's domain). Rejected — never compiled to a
    /// weak recursor (design §5.2 nested positivity).
    #[error("inductive '{ind}': non-strictly-positive nesting of '{ind}' inside '{container}'")]
    NonStrictlyPositiveNesting {
        /// The inductive being defined.
        ind: Name,
        /// The container the nesting is non-positive in.
        container: Name,
    },
    /// A nested container occurrence is not *uniform* in the parent's
    /// parameters: one of its arguments depends on a constructor field/index
    /// binder (not just on the parent parameters), so a single parametric
    /// auxiliary type cannot faithfully mirror it. Fail-closed (a guessed,
    /// non-parametric aux would be unsound). Lean's nested encoding likewise
    /// only abstracts the *parameters*.
    #[error(
        "inductive '{ind}': nested occurrence of '{container}' is not uniform in the \
         parameters (an argument depends on a constructor field/index)"
    )]
    NonUniformNesting {
        /// The inductive being defined.
        ind: Name,
        /// The container whose nesting is non-uniform.
        container: Name,
    },
    /// The auxiliary mutual construction failed admission (positivity, universe,
    /// recursor kernel-check, …). Carries the underlying [`AdmitError`].
    #[error("inductive '{ind}': auxiliary mutual construction rejected: {source}")]
    Aux {
        /// The inductive being defined.
        ind: Name,
        /// The underlying admission error.
        #[source]
        source: AdmitError,
    },
}

/// A distinct nested container occurrence.
#[derive(Clone, Debug)]
pub(crate) struct Occurrence {
    pub(crate) container: Name,
    /// The container parameter arguments, excluding its indices,
    /// **canonicalized into the parent-parameter frame** (design §5.2): every
    /// reference to a parent parameter is expressed in a context whose only
    /// binders are the `num_params` parent parameters (`below = 0`), so the same
    /// logical occurrence is recognized identically regardless of how deep in a
    /// constructor telescope it appears. For a parameterless parent this is just
    /// the closed argument list (unchanged from the parameterless path).
    pub(crate) args: Vec<Term>,
    /// the container's level args in the occurrence.
    pub(crate) levels: Vec<Level>,
    /// the auxiliary type name (e.g. `RoseTree._List`).
    pub(crate) aux_name: Name,
}

/// Admit a nested inductive by compiling it to a mutual block via the auxiliary
/// construction, then deriving the block's recursors. The nested type's recursor
/// is the derived recursor of `decl.name` in the resulting block.
///
/// Returns [`NestedError::NotNested`] if `decl` has no nested occurrence (it
/// should then go through [`crate::add_inductive`]).
pub fn add_inductive_nested(
    env: &mut dyn MutableMutualEnv,
    decl: InductiveDecl,
) -> Result<(), NestedError> {
    derive_nested_for_export(env, decl).map(|_| ())
}

/// The same checked derivation, retaining its independently collected recipe.
/// Export comparison must not obtain auxiliary names or substitutions from input.
pub(crate) fn derive_nested_for_export(
    env: &mut dyn MutableMutualEnv,
    decl: InductiveDecl,
) -> Result<Vec<Occurrence>, NestedError> {
    derive_nested_block_for_export(env, std::slice::from_ref(&decl))
}

pub(crate) struct Family<'a> {
    main: &'a InductiveDecl,
    originals: &'a [InductiveDecl],
    names: Vec<Name>,
}
impl<'a> Family<'a> {
    fn new(originals: &'a [InductiveDecl]) -> Self {
        Self {
            main: &originals[0],
            originals,
            names: originals.iter().map(|d| d.name.clone()).collect(),
        }
    }
}

pub(crate) fn derive_nested_block_for_export(
    env: &mut dyn MutableMutualEnv,
    originals: &[InductiveDecl],
) -> Result<Vec<Occurrence>, NestedError> {
    if originals.is_empty() {
        return Err(NestedError::NotNested {
            name: Name::anonymous(),
        });
    }
    let family = Family::new(originals);
    let decl = family.main;
    // Phase 1: collect distinct nested occurrences across the decl's ctors,
    // each new one compared only with those of its key (R176). The index
    // names occurrences by their place in the list, which nothing after
    // phase 1 reorders (`disambiguate` renames in place).
    let mut occurrences: Vec<Occurrence> = Vec::new();
    let mut index = OccIndex::default();
    for original in originals {
        for ctor in &original.constructors {
            collect::collect_in_ctor(env, &family, &ctor.type_, &mut occurrences, &mut index)?;
        }
    }
    if occurrences.is_empty() {
        return Err(NestedError::NotNested {
            name: decl.name.clone(),
        });
    }

    // The block's level-param vector `Param 0 .. Param (nlp-1)`, which every
    // auxiliary self-reference carries. `num_level_params` is a `u32` header
    // field, not the length of anything in memory: a forged `u32::MAX` used to
    // size a level vector at EVERY rewritten occurrence site (tens of GB each)
    // before the mutual admission below refused the input (about 100 GB per
    // site for a count of `u32::MAX`). Refuse it here with the reject recursor derivation gives the same
    // count (`Derivation`, wrapped in `Aux`), and build the vector once.
    let num_level_params = decl.num_level_params;
    if num_level_params > MAX_DERIVED_ARITY {
        return Err(NestedError::Aux {
            ind: decl.name.clone(),
            source: AdmitError::Derivation {
                ind: decl.name.clone(),
                detail: format!(
                    "too many universe level params ({num_level_params} > {MAX_DERIVED_ARITY})"
                ),
            },
        });
    }
    let aux_levels: Arc<[Level]> = (0..num_level_params).map(Level::param).collect();

    let mut room = Room::new();
    let needs_cross_rewrite = closure::expand_occurrences(
        env,
        &family,
        &mut occurrences,
        &mut index,
        &aux_levels,
        &mut room,
    )?;

    // Phase 1b: disambiguate aux names (distinct instantiations of the same
    // container under one parent get a numeric suffix).
    closure::disambiguate(&mut occurrences);

    // The block's widest ι rule binds its params, a motive per type and every
    // minor premise: the parent's constructors and each auxiliary's, which
    // copies its container's. All are known now, so a block that cannot fit
    // is refused before any auxiliary is built (R172), with the check
    // admission makes later.
    check_block_width(env, &family, &occurrences)?;
    names::freshen(env, &family, &mut occurrences)?;

    // Phase 2: build auxiliary inductive types. Every type the rewrite builds,
    // and admission then walks, is charged to one budget before it is built
    // (R172): the parent's constructors here, rewritten in phase 3, and each
    // auxiliary's types in `build_auxiliary`.
    let growth = rewrite_growth(decl.num_params);
    for original in originals {
        for ctor in &original.constructors {
            let nodes = room.measure(&ctor.type_).saturating_mul(growth);
            room.take(nodes, decl, &original.name, At::ParentCtor(&ctor.name))?;
        }
    }
    let mut aux_decls: Vec<InductiveDecl> = Vec::with_capacity(occurrences.len());
    for occ in &occurrences {
        aux_decls.push(build_auxiliary(env, decl, occ, &aux_levels, &mut room)?);
    }

    if needs_cross_rewrite {
        closure::rewrite_auxiliaries(
            env,
            &family,
            &occurrences,
            &index,
            &aux_levels,
            &mut aux_decls,
            &mut room,
        )?;
    }

    // Phase 3: rewrite the original ctors to reference the aux types. Each
    // node built and each pair of nodes compared to match a site is charged
    // to the same budget before it is built or compared (R174, R176).
    let mut decls = Vec::with_capacity(originals.len().saturating_add(aux_decls.len()));
    for original in originals {
        let mut rewritten = original.clone();
        for c in &mut rewritten.constructors {
            let mut charge =
                |nodes: u64| room.take(nodes, decl, &original.name, At::Matching(&c.name));
            c.type_ = crate::nested_replace::replace_nested_block(
                env,
                &c.type_,
                &family.names,
                &occurrences,
                &index,
                &aux_levels,
                decl.num_params,
                &mut charge,
            )?;
        }
        decls.push(rewritten);
    }
    decls.extend(aux_decls);
    let block = MutualBlock { decls };
    add_inductive_mutual(env, block).map_err(|source| NestedError::Aux {
        ind: decl.name.clone(),
        source,
    })?;
    Ok(occurrences)
}

/// The refusal of a nested block too wide for the depth bound, before its
/// auxiliaries are built (R172).
fn block_too_wide(decl: &InductiveDecl, detail: String) -> NestedError {
    NestedError::Aux {
        ind: decl.name.clone(),
        source: AdmitError::Derivation {
            ind: decl.name.clone(),
            detail,
        },
    }
}

/// Refuse a nested block whose ι rules cannot fit the depth bound, from its
/// counts alone: params, one motive per type, and the minor premises of the
/// parent and of every auxiliary (R172). Fields only widen a rule, so this is
/// the refusal `check_rule_width` makes after the block is built.
fn check_block_width(
    env: &dyn Env,
    family: &Family<'_>,
    occurrences: &[Occurrence],
) -> Result<(), NestedError> {
    let decl = family.main;
    let count = |n: usize| u32::try_from(n).unwrap_or(u32::MAX);
    let mut minors = family
        .originals
        .iter()
        .fold(0u32, |n, d| n.saturating_add(count(d.constructors.len())));
    for occ in occurrences {
        let ctors = env
            .inductive_constructors(&occ.container)
            .map_or(0, |c| c.len());
        minors = minors.saturating_add(count(ctors));
    }
    let motives = count(occurrences.len()).saturating_add(count(family.originals.len()));
    crate::recursor::check_rule_width(decl.num_params, motives, minors, 0).map_err(|detail| {
        block_too_wide(decl, format!("before its auxiliaries are built, {detail}"))
    })
}

#[cfg(test)]
fn collect_in_ctor(
    env: &dyn Env,
    decl: &InductiveDecl,
    ty: &Term,
    out: &mut Vec<Occurrence>,
    index: &mut OccIndex,
) -> Result<(), NestedError> {
    let family = Family::new(std::slice::from_ref(decl));
    collect::collect_in_ctor(env, &family, ty, out, index)
}

#[cfg(test)]
mod tests;

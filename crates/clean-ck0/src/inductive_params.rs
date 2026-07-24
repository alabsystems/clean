// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural `num_params` validation (the gate-level soundness pre-check,
//! design §2, §12). Extracted from [`crate::inductive`] to keep both files
//! under the 500-line convention. Establishes the "parameters are uniform"
//! invariant the subsingleton / large-elim gate relies on, fail-closed, BEFORE
//! the gate runs — so an over-declared `num_params` cannot hide a non-`Prop`
//! data field from the bare-index analysis.

use crate::inductive::{count_pi, return_type, AdmitError, InductiveDecl};
use crate::name::Name;
use crate::term::TermKind;
// ---------------------------------------------------------------------------
// Structural num_params validation (the gate-level soundness pre-check).
// ---------------------------------------------------------------------------

/// Validate the producer-supplied `decl.num_params` against the inductive's own
/// type and every constructor's shape, fail-closed. Until this passes, the
/// `num_params` value is untrusted advice; after it passes, the standard
/// "parameters are uniform" invariant holds — which is exactly what the
/// subsingleton / large-elim gate ([`split_ctor_telescope`] skipping the first
/// `num_params` binders) relies on to be sound.
///
/// Two structural facts are established:
///
/// 1. **Arity.** `num_params <= count_pi(decl.type_)`: the inductive declares at
///    least `num_params` leading Π binders (params come before indices).
/// 2. **Uniformity, per constructor.** Each constructor `c` has at least
///    `num_params` leading Π binders, and its result type is the inductive `I`
///    applied — with its first `num_params` arguments being exactly the
///    constructor's leading binders as *bare, in-order* de Bruijn variables.
///    Concretely, if a constructor has `total` leading Π binders then, inside
///    its result type, leading binder `p` (`0 <= p < num_params`) is the
///    variable `BVar(total - 1 - p)`, and that must be the `p`-th argument of
///    the result-type spine whose head is `Const(I)`.
///
/// The bare-`BVar` match (not an "occurrence anywhere" test) is deliberate and
/// mirrors Lean's constructor check: a parameter that appears *computed* (e.g.
/// under another head) in the result-type prefix is **not** a uniform parameter
/// and must be rejected, exactly so it cannot later be mistaken for a droppable
/// param by the gate.
pub(crate) fn validate_num_params(decl: &InductiveDecl) -> Result<(), AdmitError> {
    validate_num_params_block(decl, std::slice::from_ref(&decl.name))
}

/// Block-aware [`validate_num_params`]: the per-constructor result-type head may
/// be *any* type in the mutual block (a constructor of type `T_i` returns
/// `T_i ...`), and the uniform-parameter / bare-index check is otherwise
/// identical. For a single-element block this is exactly the M2 check.
pub(crate) fn validate_num_params_block(
    decl: &InductiveDecl,
    block_names: &[Name],
) -> Result<(), AdmitError> {
    let np = decl.num_params;
    if np == 0 {
        // No parameters claimed: nothing to drop, nothing to validate. (The
        // gate then treats every constructor binder as a field, which is the
        // sound conservative direction.)
        return Ok(());
    }

    // (1) Arity: the inductive type must have at least `num_params` leading Π
    // binders for the params to exist at all.
    if np > count_pi(&decl.type_) {
        return Err(AdmitError::MalformedParams {
            ind: decl.name.clone(),
            detail: format!(
                "num_params = {np} exceeds the inductive type's {} leading Pi binders",
                count_pi(&decl.type_)
            ),
        });
    }

    // (2) Per-constructor uniformity.
    for ctor in &decl.constructors {
        let total = count_pi(&ctor.type_);
        if np > total {
            return Err(AdmitError::MalformedParams {
                ind: decl.name.clone(),
                detail: format!(
                    "constructor '{}' has only {total} leading binders, fewer than num_params = {np}",
                    ctor.name
                ),
            });
        }

        // Head + args of the constructor's result type (after stripping ALL of
        // its leading Π binders). The first `num_params` args must be the
        // leading binders as bare, in-order BVars.
        let ret = return_type(&ctor.type_);
        let (head, ret_args) = ret.unfold_apps();

        // Head must be a block inductive (its own type in the single case, any
        // block type in the mutual case — a constructor of `T_i` returns `T_i`).
        let head_is_ind =
            matches!(head.kind(), TermKind::Const(c) if block_names.iter().any(|n| n == c.name()));
        if !head_is_ind {
            return Err(AdmitError::MalformedParams {
                ind: decl.name.clone(),
                detail: format!(
                    "constructor '{}' result type head is not a block inductive",
                    ctor.name
                ),
            });
        }

        let np_usize = usize::try_from(np).unwrap_or(usize::MAX);
        if ret_args.len() < np_usize {
            return Err(AdmitError::MalformedParams {
                ind: decl.name.clone(),
                detail: format!(
                    "constructor '{}' result type applies '{}' to {} args, fewer than num_params = {np}",
                    ctor.name,
                    decl.name,
                    ret_args.len()
                ),
            });
        }

        // Check the first `num_params` result-type args are the leading binders
        // as bare, in-order BVars. Leading binder `p` is bound at de Bruijn
        // index `total - 1 - p` inside the result type (it sits under all
        // `total` binders). Iterate via `.zip` so no index arithmetic is needed.
        for (p, arg) in (0..np).zip(ret_args.iter()) {
            let expected = total.saturating_sub(1).saturating_sub(p);
            let ok = matches!(arg.kind(), TermKind::BVar(idx) if *idx == expected);
            if !ok {
                return Err(AdmitError::MalformedParams {
                    ind: decl.name.clone(),
                    detail: format!(
                        "constructor '{}' parameter #{p} is not the uniform bare index BVar({expected}) in the result type \
                         (over-/mis-declared num_params would hide a field from the subsingleton gate)",
                        ctor.name
                    ),
                });
            }
        }
    }

    Ok(())
}

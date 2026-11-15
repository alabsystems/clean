// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Building a nested occurrence's auxiliary inductive.

use std::sync::Arc;

use super::size::{rewrite_growth, At, Room};
use super::{NestedError, Occurrence};
use crate::inductive::{AdmitError, Constructor, InductiveDecl};
use crate::level::{Level, LevelTooDeep};
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;

/// Build the auxiliary inductive mirroring `container`'s structure with the
/// container's params substituted by the occurrence's args and its level params
/// by the occurrence's levels, and `Container args` self-refs replaced by the
/// aux type.
pub(super) fn build_auxiliary(
    env: &dyn Env,
    decl: &InductiveDecl,
    occ: &Occurrence,
    aux_levels: &Arc<[Level]>,
    room: &mut Room,
) -> Result<InductiveDecl, NestedError> {
    let n_container_params =
        env.inductive_num_params(&occ.container)
            .ok_or_else(|| NestedError::UnknownContainer {
                ind: decl.name.clone(),
                container: occ.container.clone(),
            })?;
    let ctors = env.inductive_constructors(&occ.container).ok_or_else(|| {
        NestedError::UnknownContainer {
            ind: decl.name.clone(),
            container: occ.container.clone(),
        }
    })?;

    // The aux is itself PARAMETRIC over the parent's parameters (design §5.2):
    // for `Tree (A)`, the aux is `Tree._List (A : Type)`, not a parameterless
    // `Tree._List` with `A` substituted away. The parent's parameter binders
    // (taken from the parent type former, over the shared level params) are
    // prepended to the aux type former and to every aux constructor; the
    // container's own params are substituted by the (canonical) occurrence args,
    // which reference exactly those prepended binders. For a parameterless parent
    // (`num_params == 0`) this degenerates to the original parameterless path.
    let np = decl.num_params;
    let param_binders: Vec<(BinderInfo, Term)> =
        crate::inductive::pi_domains_with_info(&decl.type_, np);

    // Aux type former: container type, strip its params (substituted by the
    // canonical occurrence args), level-instantiate, then prepend the parent
    // parameter binders. Result: `(params...) -> (container indices...) -> Sort u`.
    let container_ty =
        env.const_type(&occ.container)
            .ok_or_else(|| NestedError::UnknownContainer {
                ind: decl.name.clone(),
                container: occ.container.clone(),
            })?;
    // What the substitutions and the rewrite below can build, charged before
    // they build it (R172): each use of a container parameter receives a copy
    // of its argument, each self-reference becomes the auxiliary applied to
    // the parent's parameters, and every type gets the parent's parameter
    // binders: one Π node for each, and its type (R174 counts the Π nodes).
    let copy = occ
        .args
        .iter()
        .take(usize::try_from(n_container_params).unwrap_or(usize::MAX))
        .map(|a| room.measure(a))
        .max()
        .unwrap_or(0)
        .saturating_add(1);
    let binders = room.binders(&param_binders);
    let growth = rewrite_growth(np);
    let nodes = room
        .measure(&container_ty)
        .saturating_mul(copy)
        .saturating_add(binders);
    room.take(nodes, decl, &occ.aux_name, At::AuxType)?;
    let container_params = &occ.args[..occ
        .args
        .len()
        .min(usize::try_from(n_container_params).unwrap_or(usize::MAX))];
    let too_few_binders = |what: &str| {
        aux_refused(
            decl,
            occ,
            format!(
                "{what} has fewer leading Pi binders than the parameter arguments \
                 container '{}' is given ({})",
                occ.container,
                container_params.len()
            ),
        )
    };
    let mut aux_type = substitute_params(&container_ty, container_params)
        .ok_or_else(|| too_few_binders(&format!("the type of '{}'", occ.container)))?;
    let too_deep = |e: LevelTooDeep| aux_refused(decl, occ, e.to_string());
    check_aux_depth(decl, occ, &aux_type)?;
    aux_type = aux_type.instantiate_levels(&occ.levels).map_err(too_deep)?;
    aux_type = prepend_param_binders(&param_binders, aux_type);
    check_aux_depth(decl, occ, &aux_type)?;

    // Aux constructors: each container ctor, container params substituted by the
    // canonical occurrence args (which reference the canonical parameter frame),
    // level-instantiated, self-refs replaced by the aux applied to the parent
    // parameters, then the parent parameter binders prepended.
    let mut aux_ctors = Vec::with_capacity(ctors.len());
    for (idx, (ctor_name, ctor_ty)) in ctors.iter().enumerate() {
        let nodes = room
            .measure(ctor_ty)
            .saturating_mul(copy)
            .saturating_mul(growth)
            .saturating_add(binders);
        room.take(nodes, decl, &occ.aux_name, At::AuxCtor(ctor_name))?;
        let mut ct = substitute_params(ctor_ty, container_params)
            .ok_or_else(|| too_few_binders(&format!("the constructor type of '{ctor_name}'")))?;
        // Substituting the occurrence's arguments into the container's
        // constructor type can build a term about as deep as both together,
        // which `replace_container_self_ref` and admission's `infer` walk
        // natively: refused here first (R166).
        check_aux_depth(decl, occ, &ct)?;
        ct = ct.instantiate_levels(&occ.levels).map_err(too_deep)?;
        // Each node built and each pair of nodes compared to match a
        // self-reference is charged before it is built or compared (R176).
        let mut charge =
            |nodes: u64| room.take(nodes, decl, &occ.aux_name, At::Matching(ctor_name));
        ct = crate::nested_replace::replace_container_self_ref(
            &ct,
            &occ.container,
            n_container_params,
            &occ.args,
            &occ.aux_name,
            aux_levels,
            np,
            &mut charge,
        )?;
        ct = prepend_param_binders(&param_binders, ct);
        check_aux_depth(decl, occ, &ct)?;
        let aux_ctor_name = constructor_name(occ, ctor_name, idx).ok_or_else(|| {
            aux_refused(
                decl,
                occ,
                "anonymous or oversized container constructor".into(),
            )
        })?;
        aux_ctors.push(Constructor {
            name: aux_ctor_name,
            type_: ct,
        });
    }

    Ok(InductiveDecl {
        name: occ.aux_name.clone(),
        num_level_params: decl.num_level_params,
        num_params: decl.num_params,
        type_: aux_type,
        constructors: aux_ctors,
    })
}

/// Refuse an auxiliary type or constructor type deeper than the depth bound
/// (R166). The auxiliary is built from the container's declarations and the
/// occurrence's arguments, each within the bound, so it can be up to about
/// twice as deep, and admission walks it natively before deriving anything.
/// Lean admits such a nested inductive; ck0 refuses it, which is fail-closed.
fn check_aux_depth(decl: &InductiveDecl, occ: &Occurrence, t: &Term) -> Result<(), NestedError> {
    if t.depth > crate::MAX_VALIDATE_DEPTH {
        let detail = format!(
            "an auxiliary term has depth {}, past the depth bound {}",
            t.depth,
            crate::MAX_VALIDATE_DEPTH
        );
        return Err(aux_refused(decl, occ, detail));
    }
    Ok(())
}

/// The refusal of `occ`'s auxiliary, `detail` saying why.
fn aux_refused(decl: &InductiveDecl, occ: &Occurrence, detail: String) -> NestedError {
    NestedError::Aux {
        ind: decl.name.clone(),
        source: AdmitError::Derivation {
            ind: occ.aux_name.clone(),
            detail,
        },
    }
}

/// Prepend the parent's parameter binders around `body` (which is already in the
/// canonical parameter frame: its free references to parameter `p` sit at
/// `BVar(num_params-1-p)`). Wraps innermost-parameter-first so parameter `p`
/// (0 = outermost) becomes the binder at de Bruijn distance `num_params-1-p`.
fn prepend_param_binders(param_binders: &[(BinderInfo, Term)], body: Term) -> Term {
    let mut result = body;
    for (bi, ty) in param_binders.iter().rev() {
        result = Term::pi(*bi, ty.clone(), result);
    }
    result
}

/// `ty` with one leading Π binder for each of `args` replaced by `args`, the
/// first the outermost, in one pass (R176), or `None` when `ty` has fewer
/// leading Π binders than `args`, which Lean's `instantiate_pi_params`
/// refuses as ill-formed. Substituting one argument at a time rebuilt the
/// copies of the earlier arguments at each later one, up to about `n / 2`
/// times the tree charged for `n` parameters, and with too few binders it
/// went on into a Π an argument brought in (a test pins that shape).
/// Admission (`validate_num_params`) gives a container's type and each of its
/// constructor types at least `num_params` leading Π binders when it is
/// admitted, and no more than `num_params` arguments are passed. That does not
/// make this unreachable: ck0 does not refuse a later constructor named like
/// an admitted container, whose stored type it then replaces, and a container
/// registered by hand (`MinimalEnv::with_container_inductive`) is not
/// validated. So the count is checked here.
fn substitute_params(ty: &Term, args: &[Term]) -> Option<Term> {
    let mut body = ty;
    for _ in args {
        let TermKind::Pi(_, _, codom) = body.kind() else {
            return None;
        };
        body = codom;
    }
    Some(body.instantiate_many(args))
}

#[cfg(test)]
mod tests;

/// Keep normal constructor names; qualified or reserved suffixes receive a
/// distinct private component instead of collapsing to their final spelling.
pub(super) fn constructor_name(
    occ: &Occurrence,
    source: &crate::Name,
    index: usize,
) -> Option<crate::Name> {
    if source.is_anonymous() {
        return None;
    }
    if source.parent().as_ref() == Some(&occ.container) && source.last_str() != Some("rec") {
        source.with_parent(&occ.aux_name)
    } else {
        Some(occ.aux_name.str("\0ctor").num(u64::try_from(index).ok()?))
    }
}

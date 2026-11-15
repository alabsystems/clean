//! Collect occurrences across every original family member.
use super::*;
use crate::positivity::term_mentions;

/// Collect nested occurrences in one constructor type. A field domain whose head
/// is a known env inductive `C` (not the type being defined) and some argument
/// mentions the type being defined is a nested occurrence; `index` is `out`'s
/// [`OccIndex`] (R176).
pub(super) fn collect_in_ctor(
    env: &dyn Env,
    family: &Family<'_>,
    ctor_ty: &Term,
    out: &mut Vec<Occurrence>,
    index: &mut OccIndex,
) -> Result<(), NestedError> {
    let decl = family.main;
    // Walk the ctor telescope; for each field domain (after params), inspect.
    // `depth` counts binders descended; the parent params are the first
    // `num_params` of them, so a field domain at `depth` sits `depth - num_params`
    // binders inside the parameter block.
    let mut cur =
        crate::inductive::fields::constructor_view(env, ctor_ty, decl.num_params, &family.names)
            .map_err(|e| NestedError::Aux {
                ind: decl.name.clone(),
                source: AdmitError::Derivation {
                    ind: decl.name.clone(),
                    detail: format!("constructor field reduction: {e}"),
                },
            })?
            .type_;
    let mut depth: u32 = 0;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        if depth >= decl.num_params {
            collect_in_domain(env, family, dom, depth, out, index)?;
        }
        depth = depth.saturating_add(1);
        cur = codom.clone();
    }
    Ok(())
}

/// Inspect a field-domain expression for a nested container application. `depth`
/// is the number of binders enclosing `expr` (counted from the constructor top),
/// used to canonicalize occurrence args into the parent-parameter frame.
fn collect_in_domain(
    env: &dyn Env,
    family: &Family<'_>,
    expr: &Term,
    depth: u32,
    out: &mut Vec<Occurrence>,
    index: &mut OccIndex,
) -> Result<(), NestedError> {
    let decl = family.main;
    let (head, args) = expr.unfold_apps();
    if let TermKind::Const(cref) = head.kind() {
        let cname = cref.name();
        // Skip the type being defined (a direct recursive field, not nesting).
        if !family.names.contains(cname) {
            let mentions = args
                .iter()
                .any(|a| family.names.iter().any(|n| term_mentions(a, n)));
            if mentions {
                // It is a container nesting. It must be a known inductive.
                let np = env.inductive_num_params(cname).ok_or_else(|| {
                    NestedError::UnknownContainer {
                        ind: decl.name.clone(),
                        container: cname.clone(),
                    }
                })?;
                // Nested positivity: the nesting argument(s) must occur
                // strictly-positively in the container's constructors. We reject
                // the obvious negative shape (the nesting arg is a function type
                // mentioning `decl` in its domain) eagerly; the unfolded-block
                // positivity re-check in add_inductive_mutual is the authoritative
                // gate and catches container-internal negativity too.
                let parameter_args = args
                    .get(..usize::try_from(np).unwrap_or(usize::MAX))
                    .ok_or_else(|| NestedError::UnknownContainer {
                        ind: decl.name.clone(),
                        container: cname.clone(),
                    })?;
                check_nested_positivity(env, family, cname, parameter_args)?;
                // Canonicalize the args into the parent-parameter frame so the
                // occurrence is recognized uniformly wherever it appears in the
                // telescope. `below = depth - num_params` (occurrences only sit in
                // field domains, where `depth >= num_params`). A `None` here means
                // an argument depends on a constructor field/index binder — a
                // non-uniform nesting a parametric aux cannot represent: reject.
                let below = depth.checked_sub(decl.num_params).ok_or_else(|| {
                    NestedError::NonUniformNesting {
                        ind: decl.name.clone(),
                        container: cname.clone(),
                    }
                })?;
                let canon_args: Vec<Term> = parameter_args
                    .iter()
                    .map(|a| crate::nested_replace::lower_params(a, below, decl.num_params))
                    .collect::<Option<Vec<Term>>>()
                    .ok_or_else(|| NestedError::NonUniformNesting {
                        ind: decl.name.clone(),
                        container: cname.clone(),
                    })?;
                let levels: Vec<Level> = cref.levels().to_vec();
                // Only an occurrence of this one's key can equal it (R176):
                // comparing it with every occurrence of its container walked
                // an equal leading argument held in another allocation whole,
                // about m²/2 times its size for m occurrences. Phase 1 runs
                // before the budget exists, so the comparison is not charged:
                // a site is compared with the occurrences of its key, which
                // are one at most unless two distinct argument lists hash
                // alike, and sites are disjoint subterms of the constructor.
                let key = args_key(&canon_args);
                let mut free = |_: u64| Ok::<(), NestedError>(());
                let known = index
                    .find(out.as_slice(), cname, &canon_args, key, &mut free)?
                    .is_some();
                if !known {
                    // Each occurrence adds a motive to the block's recursor,
                    // so past the bound its refusal is certain: stop here,
                    // before collection and the auxiliaries go on (R172).
                    let containers = env.inductive_family(cname).ok_or_else(|| {
                        NestedError::UnknownContainer {
                            ind: decl.name.clone(),
                            container: cname.clone(),
                        }
                    })?;
                    for container in containers {
                        if index
                            .find(out.as_slice(), &container, &canon_args, key, &mut free)?
                            .is_some()
                        {
                            continue;
                        }
                        if out.len()
                            >= usize::try_from(crate::MAX_VALIDATE_DEPTH).unwrap_or(usize::MAX)
                        {
                            return Err(block_too_wide(
                            decl,
                            format!(
                                "more than {} distinct nested occurrences, each a motive of the block's recursor, past the depth bound",
                                out.len()
                            ),
                        ));
                        }
                        let aux_name = decl.name.str(&format!(
                            "_{}",
                            crate::nested_replace::last_component(&container)
                        ));
                        index.insert(&container, &canon_args, out.len());
                        out.push(Occurrence {
                            container,
                            args: canon_args.clone(),
                            levels: levels.clone(),
                            aux_name,
                        });
                    }
                }
            }
        }
    }
    // Recurse into Pi structure (nested containers can appear in inner domains).
    if let TermKind::Pi(_, dom, codom) = expr.kind() {
        collect_in_domain(env, family, dom, depth, out, index)?;
        collect_in_domain(env, family, codom, depth.saturating_add(1), out, index)?;
    }
    Ok(())
}

/// Reject a non-strictly-positive nesting. The nesting `decl` appears as an arg
/// of container `C`; we require that, in each of `C`'s constructors, the
/// corresponding container parameter is used only strictly-positively (never to
/// the left of an arrow). We approximate the authoritative check by unfolding
/// `C`'s constructors with the occurrence args and verifying `decl` never lands
/// in a NoOccur (left-of-arrow) position — which the subsequent mutual-block
/// positivity check enforces precisely. Here we catch the direct case where the
/// nesting argument itself is a function type mentioning `decl` in its domain.
fn check_nested_positivity(
    env: &dyn Env,
    family: &Family<'_>,
    container: &Name,
    args: &[Term],
) -> Result<(), NestedError> {
    // If any container argument that mentions `decl` does so under an arrow's
    // domain, that is a negative nesting — reject up front. (The unfolded block
    // positivity is the full gate; this is the eager, clear rejection.)
    let decl = family.main;
    for a in args {
        if family
            .names
            .iter()
            .any(|n| mentions_in_negative_position(a, n))
        {
            return Err(NestedError::NonStrictlyPositiveNesting {
                ind: decl.name.clone(),
                container: container.clone(),
            });
        }
    }
    let _ = env;
    Ok(())
}

/// True iff `name` occurs to the LEFT of any arrow inside `t` (a negative /
/// non-strictly-positive position).
fn mentions_in_negative_position(t: &Term, name: &Name) -> bool {
    match t.kind() {
        TermKind::Pi(_, dom, codom) => {
            term_mentions(dom, name)
                || mentions_in_negative_position(dom, name)
                || mentions_in_negative_position(codom, name)
        }
        TermKind::App(f, a) => {
            mentions_in_negative_position(f, name) || mentions_in_negative_position(a, name)
        }
        TermKind::Lam(_, ty, b) => {
            mentions_in_negative_position(ty, name) || mentions_in_negative_position(b, name)
        }
        TermKind::Let(ty, v, b) => {
            mentions_in_negative_position(ty, name)
                || mentions_in_negative_position(v, name)
                || mentions_in_negative_position(b, name)
        }
        TermKind::Proj(_, _, e) => mentions_in_negative_position(e, name),
        _ => false,
    }
}

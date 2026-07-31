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

use crate::inductive::{AdmitError, Constructor, InductiveDecl};
use crate::level::Level;
use crate::mutual::{add_inductive_mutual, MutableMutualEnv, MutualBlock};
use crate::name::Name;
use crate::positivity::term_mentions;
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;

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
    /// the full argument list applied to the container in the occurrence,
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
    // Phase 1: collect distinct nested occurrences across the decl's ctors.
    let mut occurrences: Vec<Occurrence> = Vec::new();
    for ctor in &decl.constructors {
        collect_in_ctor(env, &decl, &ctor.type_, &mut occurrences)?;
    }
    if occurrences.is_empty() {
        return Err(NestedError::NotNested { name: decl.name });
    }

    // Phase 1b: disambiguate aux names (distinct instantiations of the same
    // container under one parent get a numeric suffix).
    disambiguate(&mut occurrences);

    // Phase 2: build auxiliary inductive types.
    let mut aux_decls: Vec<InductiveDecl> = Vec::with_capacity(occurrences.len());
    for occ in &occurrences {
        aux_decls.push(build_auxiliary(env, &decl, occ)?);
    }

    // Phase 3: rewrite the original ctors to reference the aux types.
    let rewritten_ctors: Vec<Constructor> = decl
        .constructors
        .iter()
        .map(|c| Constructor {
            name: c.name.clone(),
            type_: crate::nested_replace::replace_nested(
                env,
                &c.type_,
                &decl.name,
                &occurrences,
                decl.num_level_params,
                decl.num_params,
            ),
        })
        .collect();
    let original = InductiveDecl {
        name: decl.name.clone(),
        num_level_params: decl.num_level_params,
        num_params: decl.num_params,
        type_: decl.type_.clone(),
        constructors: rewritten_ctors,
    };

    // Phase 4: form the mutual block [original, aux…] and admit it. The aux
    // types share the original's params/level params (the auxiliary construction
    // substituted the container's params with the occurrence args, so the aux
    // types carry NO extra params — they live in the block's level telescope).
    let mut decls = vec![original];
    decls.extend(aux_decls);
    let block = MutualBlock { decls };
    add_inductive_mutual(env, block).map_err(|source| NestedError::Aux {
        ind: decl.name,
        source,
    })
}

/// Collect nested occurrences in one constructor type. A field domain whose head
/// is a known env inductive `C` (not the type being defined) and some argument
/// mentions the type being defined is a nested occurrence.
fn collect_in_ctor(
    env: &dyn Env,
    decl: &InductiveDecl,
    ctor_ty: &Term,
    out: &mut Vec<Occurrence>,
) -> Result<(), NestedError> {
    // Walk the ctor telescope; for each field domain (after params), inspect.
    // `depth` counts binders descended; the parent params are the first
    // `num_params` of them, so a field domain at `depth` sits `depth - num_params`
    // binders inside the parameter block.
    let mut cur = ctor_ty.clone();
    let mut depth: u32 = 0;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        if depth >= decl.num_params {
            collect_in_domain(env, decl, dom, depth, out)?;
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
    decl: &InductiveDecl,
    expr: &Term,
    depth: u32,
    out: &mut Vec<Occurrence>,
) -> Result<(), NestedError> {
    let (head, args) = expr.unfold_apps();
    if let TermKind::Const(cref) = head.kind() {
        let cname = cref.name();
        // Skip the type being defined (a direct recursive field, not nesting).
        if cname != &decl.name {
            let mentions = args.iter().any(|a| term_mentions(a, &decl.name));
            if mentions {
                // It is a container nesting. It must be a known inductive.
                let _ = env.inductive_num_params(cname).ok_or_else(|| {
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
                check_nested_positivity(env, decl, cname, &args)?;
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
                let canon_args: Vec<Term> = args
                    .iter()
                    .map(|a| crate::nested_replace::lower_params(a, below, decl.num_params))
                    .collect::<Option<Vec<Term>>>()
                    .ok_or_else(|| NestedError::NonUniformNesting {
                        ind: decl.name.clone(),
                        container: cname.clone(),
                    })?;
                let levels: Vec<Level> = cref.levels().to_vec();
                if !out
                    .iter()
                    .any(|o| o.container == *cname && o.args == canon_args)
                {
                    let aux_name = Name::from_dotted(&format!(
                        "{}._{}",
                        decl.name,
                        crate::nested_replace::last_component(cname)
                    ));
                    out.push(Occurrence {
                        container: cname.clone(),
                        args: canon_args,
                        levels,
                        aux_name,
                    });
                }
            }
        }
    }
    // Recurse into Pi structure (nested containers can appear in inner domains).
    if let TermKind::Pi(_, dom, codom) = expr.kind() {
        collect_in_domain(env, decl, dom, depth, out)?;
        collect_in_domain(env, decl, codom, depth.saturating_add(1), out)?;
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
    decl: &InductiveDecl,
    container: &Name,
    args: &[Term],
) -> Result<(), NestedError> {
    // If any container argument that mentions `decl` does so under an arrow's
    // domain, that is a negative nesting — reject up front. (The unfolded block
    // positivity is the full gate; this is the eager, clear rejection.)
    for a in args {
        if mentions_in_negative_position(a, &decl.name) {
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

/// Disambiguate aux names: the first occurrence of a base name keeps it,
/// subsequent distinct occurrences get a `_<n>` suffix.
fn disambiguate(occurrences: &mut [Occurrence]) {
    let mut counts: std::collections::HashMap<Name, usize> = std::collections::HashMap::new();
    for occ in occurrences.iter_mut() {
        let c = counts.entry(occ.aux_name.clone()).or_insert(0);
        if *c > 0 {
            occ.aux_name = Name::from_dotted(&format!("{}_{}", occ.aux_name, *c));
        }
        *c = c.saturating_add(1);
    }
}

/// Build the auxiliary inductive mirroring `container`'s structure with the
/// container's params substituted by the occurrence's args and its level params
/// by the occurrence's levels, and `Container args` self-refs replaced by the
/// aux type.
fn build_auxiliary(
    env: &dyn Env,
    decl: &InductiveDecl,
    occ: &Occurrence,
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
    let mut aux_type = container_ty;
    for arg in occ
        .args
        .iter()
        .take(usize::try_from(n_container_params).unwrap_or(usize::MAX))
    {
        if let TermKind::Pi(_, _, codom) = aux_type.kind() {
            aux_type = codom.instantiate(arg);
        } else {
            break;
        }
    }
    aux_type = aux_type.instantiate_levels(&occ.levels);
    aux_type = prepend_param_binders(&param_binders, aux_type);

    // Aux constructors: each container ctor, container params substituted by the
    // canonical occurrence args (which reference the canonical parameter frame),
    // level-instantiated, self-refs replaced by the aux applied to the parent
    // parameters, then the parent parameter binders prepended.
    let mut aux_ctors = Vec::with_capacity(ctors.len());
    for (ctor_name, ctor_ty) in &ctors {
        let mut ct = ctor_ty.clone();
        for arg in occ
            .args
            .iter()
            .take(usize::try_from(n_container_params).unwrap_or(usize::MAX))
        {
            if let TermKind::Pi(_, _, codom) = ct.kind() {
                ct = codom.instantiate(arg);
            } else {
                break;
            }
        }
        ct = ct.instantiate_levels(&occ.levels);
        ct = crate::nested_replace::replace_container_self_ref(
            &ct,
            &occ.container,
            n_container_params,
            &occ.args,
            &occ.aux_name,
            decl.num_level_params,
            np,
        );
        ct = prepend_param_binders(&param_binders, ct);
        let suffix = crate::nested_replace::last_component(ctor_name);
        let aux_ctor_name = Name::from_dotted(&format!("{}.{}", occ.aux_name, suffix));
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

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phases 2 and 3 — type-level declarations, then the staged header index.
//!
//! # Why the header index is a FIXED POINT, and why it is CONFIRMED
//!
//! The ruling requires signatures elaborated "against the complete name index".
//! That is circular on its face: you cannot know the complete index until every
//! signature has elaborated, and a signature can mention a name only another
//! signature introduces.
//!
//! Elaborating in source order and stopping would reintroduce exactly the defect
//! this module exists to remove, one level down — header *k* would see headers
//! *1..k-1* and no more. So instead each ITERATION elaborates every signature
//! against the COMPLETE header set produced by the previous iteration, and the
//! loop ends only when an iteration reproduces its input exactly. At that point
//! every header is, by construction, the header you get with all headers
//! present.
//!
//! That confirming iteration is what makes this different in kind from the
//! rejected fixpoint-retry. Retry keeps the first successful interpretation and
//! never revisits it. This recomputes every header, every round, from a complete
//! index, and REFUSES ([`BatchRejection::HeaderNotStable`]) if the answer will
//! not settle — fail-closed, rather than picking whichever answer arrived first.
//!
//! # Why `inductive` / `structure` / `class` are not staged
//!
//! They have no type/body seam at all: the constructors' and fields' types ARE
//! the declaration. A partial family — the type name resolvable while its
//! constructors are not — is worse than no header, because a body would resolve
//! the type and then fail on the constructor with an error about the wrong
//! thing. A type-level declaration also cannot depend on any BODY, only on other
//! types, so it can simply be elaborated COMPLETELY first and registered as a
//! real declaration. That removes the problem instead of working around it.

use clean_kernel::{Declaration, Environment, Expr, Name};
use clean_parser::{SurfaceBinder, SurfaceDecl, SurfaceExpr};

use super::exec::{elaborate_node, introduced_names, referenced_names, OptionScope};
use super::plan::{Node, NodeClass, NodeStatus, Plan};
use super::{BatchRejection, DeclHeader, HeaderKind, InstanceHeader, NoHeaderReason};
use crate::ElabError;

/// How many times the header index may be recomputed before the batch is
/// refused. Convergence is normally reached on iteration 2 (round 1 produces
/// the headers, round 2 confirms them against the complete index); a third is
/// needed only when a signature mentions a name whose own signature mentions a
/// forward name.
const MAX_HEADER_ITERATIONS: usize = 8;

/// Phase 2 — elaborate every type-level declaration completely and register it.
///
/// Best effort: a type declaration whose elaboration fails here (because it
/// mentions a `def` that has not been registered yet, say) is left `Pending` and
/// re-attempted by the body worklist. Degrading to today's source-order
/// semantics for such a declaration can only lose a forward reference; it cannot
/// manufacture one.
pub(super) fn elaborate_type_declarations(base: &mut Environment, plan: &mut Plan) {
    let mut options = OptionScope::default();
    for index in 0..plan.nodes.len() {
        if plan.nodes[index].class != NodeClass::TypeLevel
            || !matches!(plan.nodes[index].status, NodeStatus::Pending)
        {
            continue;
        }
        options.enter(base, &plan.nodes[index]);
        let elaboration = elaborate_node(&*base, &plan.nodes[index]);
        let Ok(result) = elaboration.result else {
            continue;
        };
        let node = &mut plan.nodes[index];
        node.hole_contexts = elaboration.hole_contexts;
        if super::exec::register_node(base, node, &result, elaboration.attributes).is_ok() {
            introduced_names(&result, &mut node.introduces);
            let mut referenced = std::collections::HashSet::new();
            referenced_names(&result, &mut referenced);
            node.depends_on = referenced
                .into_iter()
                .filter(|name| !node.introduces.contains(name))
                .collect();
            node.status = NodeStatus::Registered;
        }
    }
    options.leave(base);
}

/// Phase 3 — stage every remaining signature into a NON-AUTHORITATIVE
/// environment, and return it.
///
/// The returned environment is `base` plus one staged header per stageable
/// declaration. It is the elaboration environment for the body phase and
/// nothing else: it is never returned to the caller of
/// [`super::elaborate_module`], never handed to an audit, and never registered
/// into.
///
/// # Errors
/// [`BatchRejection::HeaderNotStable`] when the index will not settle.
pub(super) fn stage_headers(
    base: &Environment,
    plan: &mut Plan,
) -> Result<Environment, BatchRejection> {
    let count = plan.nodes.len();
    let mut previous: Vec<Option<DeclHeader>> = vec![None; count];

    for _iteration in 1..=MAX_HEADER_ITERATIONS {
        // Every iteration starts from `base` and installs the PREVIOUS
        // iteration's complete header set. No header of this iteration is
        // visible to any other, so the round is order-independent by
        // construction, not by care.
        let mut env = base.clone();
        install_headers(&mut env, &previous);

        let mut current: Vec<Option<DeclHeader>> = vec![None; count];
        let mut current_reasons: Vec<Option<NoHeaderReason>> = vec![None; count];
        let mut options = OptionScope::default();
        for index in 0..count {
            if plan.nodes[index].class != NodeClass::Value
                || !matches!(plan.nodes[index].status, NodeStatus::Pending)
            {
                continue;
            }
            options.enter(&mut env, &plan.nodes[index]);
            match elaborate_header(&env, &plan.nodes[index]) {
                Ok(header) => current[index] = Some(header),
                Err(reason) => current_reasons[index] = Some(reason),
            }
        }
        options.leave(&mut env);

        if converged(&previous, &current) {
            // `env` is `base` + `previous`, and `previous == current`, so it is
            // already the staging environment for the CONFIRMED header set.
            for (index, header) in current.iter().enumerate() {
                match header {
                    Some(header) => {
                        // The canonical name a header carries is the one the
                        // authoritative pass will register under, so it is the
                        // one recorded — never re-derived later.
                        plan.nodes[index].name = Some(header.name.clone());
                        plan.nodes[index].header = Some(header.clone());
                    }
                    None => {
                        // No header is RECORDED, not refused: such a
                        // declaration still elaborates in the body phase, it
                        // just cannot be forward-referenced, so it keeps
                        // source-order semantics. Its canonical name is still
                        // in the collision index and its dependencies are still
                        // graph edges.
                        plan.nodes[index].no_header = current_reasons[index];
                    }
                }
            }
            return Ok(env);
        }

        previous = current;
    }

    // The loop ran out of iterations without the index settling. Fail closed:
    // an unsettled index means at least one signature's meaning depends on
    // which other signatures happen to be present, which is the source-order
    // dependence this module exists to remove. Refuse rather than publish
    // whichever answer the last iteration produced.
    Err(BatchRejection::HeaderNotStable {
        names: previous
            .iter()
            .flatten()
            .map(|header| header.name.clone())
            .collect(),
        iterations: MAX_HEADER_ITERATIONS,
    })
}

/// Install every staged header into `env`.
///
/// A header whose TYPE mentions another header can only be installed after it,
/// because `add_staged_header` runs the kernel's own type check. Passes repeat
/// while any header installs. This is insertion ordering only — the header set
/// is already fixed, and every pass is deterministic — so it is not a retry over
/// elaboration.
fn install_headers(env: &mut Environment, headers: &[Option<DeclHeader>]) {
    let mut remaining: Vec<&DeclHeader> = headers.iter().flatten().collect();
    while !remaining.is_empty() {
        let mut deferred = Vec::new();
        let mut installed_any = false;
        for header in remaining {
            let decl = Declaration::Axiom {
                name: header.name.clone(),
                level_params: header.universe_params.clone(),
                type_: header.ty.clone(),
            };
            if env.add_staged_header(decl).is_ok() {
                installed_any = true;
                // Ruling step 3: freeze instance metadata at header time.
                // Without this, an instance reaches the resolution table only
                // when its real declaration lands, so instance selection would
                // depend on registration order — the same defect as name
                // resolution, one level down.
                if let Some(instance) = &header.instance {
                    env.register_instance(clean_kernel::KernelInstanceInfo {
                        name: header.name.clone(),
                        class_name: instance.class_name.clone(),
                        priority: instance.priority,
                        type_: None,
                        value: None,
                    });
                }
            } else {
                deferred.push(header);
            }
        }
        if !installed_any {
            break;
        }
        remaining = deferred;
    }
}

/// True when two header sets name exactly the same signatures.
fn converged(previous: &[Option<DeclHeader>], current: &[Option<DeclHeader>]) -> bool {
    previous.len() == current.len()
        && previous
            .iter()
            .zip(current)
            .all(|(before, after)| match (before, after) {
                (None, None) => true,
                (Some(before), Some(after)) => before.same_signature(after),
                _ => false,
            })
}

/// Elaborate one declaration's SIGNATURE against `env`.
fn elaborate_header(env: &Environment, node: &Node) -> Result<DeclHeader, NoHeaderReason> {
    let shape = match header_shape(&node.decl) {
        Ok(shape) => shape,
        // `def f := e` has no written signature: its type comes from its body.
        // That does NOT mean it must stay out of the index — it means its type
        // has to be READ OFF a full elaboration rather than a signature-only
        // one. Doing that inside the fixed point is what makes it safe: the
        // type is recomputed against the complete header set every iteration,
        // and the loop only ends when it stops changing, so what is staged is
        // the type `f` has with every header present. A single up-front pass
        // would stage whatever the first, partial index produced.
        //
        // This matters more than it looks. A `def` outside the index is a name
        // no body can forward-reference, so every reference to it stays
        // order-dependent — the exact property this module exists to remove.
        Err(NoHeaderReason::TypeInferredFromBody) => return header_from_inferred_type(env, node),
        Err(reason) => return Err(reason),
    };
    let mut ctx = super::exec::elab_ctx_for(env, node);
    let (name, universe_params, ty) = ctx
        .elab_decl_header_inner(shape.name, shape.universe_params, shape.binders, shape.ty)
        .map_err(classify_header_error)?;

    // A staged header carrying `?m` or an unsolved level is provisional in the
    // one way a header may never be: those are solved FROM THE BODY, so the
    // signature other declarations would resolve against is not yet the
    // signature the kernel will hold. Hard reject rather than stage it.
    if ty.has_expr_mvar_quick() || ty.has_level_mvar_quick() {
        return Err(NoHeaderReason::ResidualMetavariable);
    }

    let instance = shape.instance_priority.map(|priority| InstanceHeader {
        class_name: class_of(&ty).unwrap_or_else(|| name.clone()),
        priority,
        synth_order: node.order,
    });

    Ok(DeclHeader {
        name,
        universe_params,
        ty,
        kind: shape.kind,
        instance,
        origin: node.site(),
    })
}

/// Stage a `def f := e` by elaborating it in full and keeping only its TYPE.
///
/// Nothing is registered and the value is dropped on the floor: what is staged
/// is a name and a type, exactly as for a written signature. The elaboration is
/// pure with respect to the environment — `elaborate_node` takes `&Environment`
/// — so running it once per fixed-point iteration costs time and nothing else.
fn header_from_inferred_type(env: &Environment, node: &Node) -> Result<DeclHeader, NoHeaderReason> {
    let elaboration = elaborate_node(env, node);
    let result = elaboration.result.map_err(classify_header_error)?;
    let crate::infer::ElabResult::Definition {
        name,
        universe_params,
        ty,
        ..
    } = result
    else {
        return Err(NoHeaderReason::UnsupportedShape);
    };
    if ty.has_expr_mvar_quick() || ty.has_level_mvar_quick() {
        return Err(NoHeaderReason::ResidualMetavariable);
    }
    Ok(DeclHeader {
        name,
        universe_params,
        ty,
        kind: HeaderKind::Definition,
        instance: None,
        origin: node.site(),
    })
}

/// Map an elaboration failure to the reason a header is absent.
fn classify_header_error(error: ElabError) -> NoHeaderReason {
    match error {
        ElabError::Unsupported { .. } => NoHeaderReason::UnsupportedShape,
        _ => NoHeaderReason::SignatureDidNotElaborate,
    }
}

/// The class an instance header registers under, read off its type's
/// conclusion exactly as registration reads it.
fn class_of(ty: &Expr) -> Option<Name> {
    let mut conclusion = ty;
    while let clean_kernel::ExprKind::Pi(_, _, body) = conclusion.kind() {
        conclusion = body;
    }
    crate::instances::extract_class_app(conclusion).map(|(class_name, _)| class_name)
}

/// The pieces of a surface declaration a header needs.
struct HeaderShape<'a> {
    name: &'a str,
    universe_params: &'a [String],
    binders: &'a [SurfaceBinder],
    ty: &'a SurfaceExpr,
    kind: HeaderKind,
    instance_priority: Option<u32>,
}

/// Decide whether a declaration has an elaborable signature, and pull it out.
fn header_shape(decl: &SurfaceDecl) -> Result<HeaderShape<'_>, NoHeaderReason> {
    match decl {
        // `def f := e` has no signature: its type is inferred FROM the body,
        // which is exactly what header-first must not look at.
        SurfaceDecl::Def { ty: None, .. } => Err(NoHeaderReason::TypeInferredFromBody),
        SurfaceDecl::Def {
            name,
            universe_params,
            binders,
            ty: Some(ty),
            ..
        } => Ok(HeaderShape {
            name,
            universe_params,
            binders,
            ty,
            kind: HeaderKind::Definition,
            instance_priority: None,
        }),
        SurfaceDecl::Theorem {
            name,
            universe_params,
            binders,
            ty,
            ..
        } => Ok(HeaderShape {
            name,
            universe_params,
            binders,
            ty,
            kind: HeaderKind::Theorem,
            instance_priority: None,
        }),
        SurfaceDecl::Axiom {
            name,
            universe_params,
            binders,
            ty,
            ..
        } => Ok(HeaderShape {
            name,
            universe_params,
            binders,
            ty,
            kind: HeaderKind::Axiom,
            instance_priority: None,
        }),
        SurfaceDecl::Opaque {
            name,
            universe_params,
            binders,
            ty,
            ..
        } => Ok(HeaderShape {
            name,
            universe_params,
            binders,
            ty,
            kind: HeaderKind::Opaque,
            instance_priority: None,
        }),
        // An ANONYMOUS instance's canonical name is minted by probing the
        // environment for a free `instFooBar_N`, so it depends on what is
        // already registered — which differs between the staging environment
        // and the publish environment. Staging it would freeze a name the
        // authoritative pass then does not use. Named instances are stable.
        SurfaceDecl::Instance { name: None, .. } => Err(NoHeaderReason::UnsupportedShape),
        SurfaceDecl::Instance {
            name: Some(name),
            universe_params,
            binders,
            class_type,
            priority,
            ..
        } => Ok(HeaderShape {
            name,
            universe_params,
            binders,
            ty: class_type,
            kind: HeaderKind::Instance,
            instance_priority: Some(priority.unwrap_or(crate::instances::DEFAULT_PRIORITY)),
        }),
        SurfaceDecl::Inductive { .. }
        | SurfaceDecl::Structure { .. }
        | SurfaceDecl::Class { .. } => Err(NoHeaderReason::TypeLevelDeclaration),
        _ => Err(NoHeaderReason::UnsupportedShape),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phases 4 and 6 — bodies in dependency order, then the publish audit.
//!
//! # The two environments
//!
//! `staging` holds the confirmed header index and is what bodies ELABORATE
//! against. `publish` is authoritative and is what they REGISTER into. `publish`
//! never holds a header at any moment, so a term that names one fails
//! `add_decl` with an unknown constant — the kernel's own fail-closed check is
//! the firewall, and no new code is trusted for it.
//!
//! # Why the worklist is not the rejected retry loop
//!
//! The rejected design elaborated bodies against a PARTIAL name index and kept
//! whichever interpretation succeeded first. Here the name index is COMPLETE
//! before the first body elaborates: every stageable declaration in the batch is
//! already a resolvable name with a confirmed type. What the worklist orders is
//! only WHEN a body is committed, and a deferred body is re-elaborated from
//! scratch against the same complete index plus more real definitions.
//!
//! The scheduling signal is exact rather than syntactic: a body's elaborated
//! term is scanned for staged names, and a term that still mentions one is
//! deferred, because its dependency is a signature and not yet a definition.
//! Only a term that mentions no staged header is committed — which is also the
//! condition under which `publish` would accept it, so the scheduler and the
//! kernel agree by construction rather than by coincidence.

use std::collections::{BTreeSet, HashMap, HashSet};

use clean_kernel::{Environment, Name};

use super::exec::{elaborate_node, introduced_names, referenced_names, register_node, OptionScope};
use super::plan::{NodeClass, NodeStatus, Plan};
use super::{BatchOptions, BatchRejection, HeaderAgreement, PublishAuditIssue};
use crate::register;

/// Phase 4 — elaborate and register every remaining declaration.
pub(super) fn elaborate_bodies(
    staging: &mut Environment,
    publish: &mut Environment,
    plan: &mut Plan,
    options: BatchOptions,
) -> Vec<BatchRejection> {
    let mut rejections = Vec::new();
    let mut blocked: HashMap<usize, BTreeSet<Name>> = HashMap::new();
    let mut errors: HashMap<usize, Box<crate::ElabError>> = HashMap::new();
    let mut staging_options = OptionScope::default();

    loop {
        let pending: Vec<usize> = plan
            .pending()
            .into_iter()
            .filter(|&i| plan.nodes[i].class != NodeClass::Command)
            .collect();
        if pending.is_empty() {
            break;
        }
        let mut progressed = false;

        for index in pending {
            staging_options.enter(staging, &plan.nodes[index]);
            let elaboration = elaborate_node(&*staging, &plan.nodes[index]);
            let result = match elaboration.result {
                Ok(result) => result,
                Err(error) => {
                    // Deferred, not refused. A body can fail simply because a
                    // dependency is still a signature rather than a definition
                    // — `rfl` cannot reduce through an axiom — so a failure is
                    // only final once a whole round commits nothing.
                    errors.insert(index, Box::new(error));
                    continue;
                }
            };

            let mut introduces = BTreeSet::new();
            introduced_names(&result, &mut introduces);
            let mut referenced = HashSet::new();
            referenced_names(&result, &mut referenced);

            let still_staged: BTreeSet<Name> = referenced
                .iter()
                .filter(|name| staging.is_staged_header(name) && !introduces.contains(*name))
                .cloned()
                .collect();
            if !still_staged.is_empty() {
                blocked.insert(index, still_staged);
                continue;
            }
            blocked.remove(&index);
            errors.remove(&index);

            let node = &mut plan.nodes[index];
            node.hole_contexts = elaboration.hole_contexts;

            // Ruling step 3 has a matching obligation at registration time: the
            // declaration the kernel is about to hold must be the one every
            // other declaration was elaborated against. Without this check a
            // `def` whose declared type's level metavariables are solved FROM
            // ITS BODY registers a different level signature than it staged,
            // and nothing notices.
            //
            // Checked BEFORE registration, against the elaborated result rather
            // than the registered constant: a divergent declaration must not
            // reach the authoritative environment at all, not even transiently
            // and not even under an atomicity mode that would have rolled it
            // back.
            if options.enforce_header_agreement == HeaderAgreement::Required {
                if let Some(divergence) = header_divergence(publish, node, &result) {
                    rejections.push(divergence.clone());
                    node.status = NodeStatus::Refused(divergence);
                    progressed = true;
                    continue;
                }
            }

            // COMMIT. Registration goes into the authoritative environment,
            // which has never held a header.
            if let Err(error) = register_node(publish, node, &result, elaboration.attributes) {
                let rejection = BatchRejection::Elaboration {
                    name: node.name.clone(),
                    site: node.site(),
                    error: Box::new(error),
                };
                rejections.push(rejection.clone());
                node.status = NodeStatus::Refused(rejection);
                progressed = true;
                continue;
            }

            node.introduces = introduces.clone();
            node.depends_on = referenced
                .into_iter()
                .filter(|name| !introduces.contains(name))
                .collect();
            node.status = NodeStatus::Registered;
            progressed = true;

            // Mirror into staging so LATER bodies see a real definition where a
            // header used to be. The header is DISCHARGED first: leaving it in
            // place would let the name resolve to a value-free axiom that
            // shadows the definition, and `forget_decl` alone would not prune
            // the instance / class / parameter-name rows a header can seed.
            for name in &introduces {
                staging.discharge_staged_header(name);
            }
            if let Err(error) = register::register_elab_result(staging, &result) {
                // The same declaration was just accepted by the authoritative
                // kernel check, so this can only be a staging-side bookkeeping
                // failure. Report it rather than continue with a staging
                // environment that disagrees with what was published.
                rejections.push(BatchRejection::Elaboration {
                    name: plan.nodes[index].name.clone(),
                    site: plan.nodes[index].site(),
                    error: Box::new(error),
                });
            }
        }

        if !progressed {
            break;
        }
    }
    staging_options.leave(staging);

    // Whatever is still pending could not be scheduled. Classify it.
    let stuck: Vec<usize> = plan
        .pending()
        .into_iter()
        .filter(|&i| plan.nodes[i].class != NodeClass::Command)
        .collect();
    if !stuck.is_empty() {
        rejections.extend(super::schedule::classify(plan, &blocked, &errors, &stuck));
    }

    // Commands (`example`, `#check`, `attribute`, `deriving`) run last and in
    // authored order: they name declarations this batch introduced, and they
    // register nothing themselves.
    let mut publish_options = OptionScope::default();
    for index in 0..plan.nodes.len() {
        if plan.nodes[index].class != NodeClass::Command
            || !matches!(plan.nodes[index].status, NodeStatus::Pending)
        {
            continue;
        }
        publish_options.enter(publish, &plan.nodes[index]);
        let elaboration = elaborate_node(&*publish, &plan.nodes[index]);
        let node = &mut plan.nodes[index];
        node.hole_contexts = elaboration.hole_contexts;
        match elaboration.result {
            Ok(result) => {
                if let Err(error) = register_node(publish, node, &result, elaboration.attributes) {
                    let rejection = BatchRejection::Elaboration {
                        name: node.name.clone(),
                        site: node.site(),
                        error: Box::new(error),
                    };
                    rejections.push(rejection.clone());
                    node.status = NodeStatus::Refused(rejection);
                } else {
                    node.status = NodeStatus::LexicalOrCommand;
                }
            }
            Err(error) => {
                let rejection = BatchRejection::Elaboration {
                    name: node.name.clone(),
                    site: node.site(),
                    error: Box::new(error),
                };
                rejections.push(rejection.clone());
                node.status = NodeStatus::Refused(rejection);
            }
        }
    }
    publish_options.leave(publish);

    rejections
}

/// Does the declaration about to be registered disagree with the signature that
/// was staged under its name?
///
/// Compares what `register_elab_result` would install — not a constant read back
/// out of the environment — so the answer is available BEFORE anything is
/// written, and a divergent declaration never reaches the authoritative
/// environment at all.
fn header_divergence(
    publish: &Environment,
    node: &super::plan::Node,
    result: &crate::infer::ElabResult,
) -> Option<BatchRejection> {
    let header = node.header.as_ref()?;
    let (universe_params, ty) = registered_signature(result, &header.name)?;
    let levels_agree = universe_params == header.universe_params.as_slice();
    let types_agree = clean_kernel::TypeChecker::new(publish).is_def_eq(&header.ty, ty);
    if levels_agree && types_agree {
        return None;
    }
    Some(BatchRejection::HeaderTypeDivergence {
        name: header.name.clone(),
        site: node.site(),
        staged: render_signature(&header.universe_params, &header.ty),
        registered: render_signature(universe_params, ty),
    })
}

/// The level parameters and type an elaboration result will be registered with,
/// for the leaf named `name`.
fn registered_signature<'a>(
    result: &'a crate::infer::ElabResult,
    name: &Name,
) -> Option<(&'a [Name], &'a clean_kernel::Expr)> {
    use crate::infer::ElabResult;
    match result {
        ElabResult::Definition {
            name: found,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Theorem {
            name: found,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Axiom {
            name: found,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Opaque {
            name: found,
            universe_params,
            ty,
            ..
        }
        | ElabResult::Instance {
            name: found,
            universe_params,
            ty,
            ..
        } if found == name => Some((universe_params, ty)),
        ElabResult::Multiple(inner) => inner
            .iter()
            .find_map(|leaf| registered_signature(leaf, name)),
        _ => None,
    }
}

fn render_signature(universe_params: &[Name], ty: &clean_kernel::Expr) -> String {
    let levels = universe_params
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{levels}}} {ty}")
}

/// Phase 6 — the audit that must pass before authority is published.
///
/// Runs on the AUTHORITATIVE environment only. The staging environment is not
/// reachable from here and never will be: it is a local of
/// [`super::elaborate_module`].
pub(super) fn audit(publish: &Environment, plan: &Plan) -> Vec<PublishAuditIssue> {
    let mut issues = Vec::new();

    // The tripwire. Unreachable by construction — a header is only ever added
    // to the staging environment — so this firing means a refactor broke the
    // invariant, and it must fail loudly rather than quietly.
    if publish.has_staged_headers() {
        issues.push(PublishAuditIssue::StagedHeaderInPublishEnv {
            names: publish.staged_header_names(),
        });
    }

    for node in &plan.nodes {
        if !matches!(node.status, NodeStatus::Registered) {
            continue;
        }
        for name in &node.introduces {
            let Some(info) = publish.get_const(name) else {
                issues.push(PublishAuditIssue::MissingDeclaration { name: name.clone() });
                continue;
            };
            // Zero placeholders, zero trust debt: a declaration this batch
            // registered may not reach an incomplete-proof marker.
            let mut closure = HashSet::new();
            info.type_.collect_constants_into(&mut closure);
            if let Some(value) = &info.value {
                value.collect_constants_into(&mut closure);
            }
            for reached in closure {
                if clean_kernel::env::is_trust_marker(&reached) {
                    issues.push(PublishAuditIssue::TrustDebt {
                        name: name.clone(),
                        marker: reached,
                    });
                }
            }
        }
    }

    issues
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaborating one planned node, and registering the result.
//!
//! This is where the two environments meet and stay apart. A node is
//! ELABORATED against whatever environment the caller passes — during the body
//! phase that is the staging environment, which holds provisional headers — and
//! REGISTERED into a different one, which never has. The split is a function
//! signature, not a discipline: [`register_node`] takes `&mut Environment` and
//! [`elaborate_node`] takes `&Environment`, and they are called with different
//! values.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::{Environment, Name};

use super::plan::{LexicalDirective, Node, TemplateDeclaration};
use crate::decl_attributes::CtxAttributes;
use crate::infer::{ElabResult, UnstagedSibling};
use crate::namespace::NamespaceState;
use crate::{register, ElabCtx, ElabError, HoleContext};

/// One node's elaboration, drained out of the `ElabCtx` that produced it so the
/// context (which borrows the environment immutably) can be dropped before
/// registration needs `&mut`.
pub(super) struct NodeElaboration {
    pub result: Result<ElabResult, ElabError>,
    pub attributes: CtxAttributes,
    pub hole_contexts: Vec<HoleContext>,
}

/// Environment options set for one node, and how to put them back.
///
/// `set_option` is lexical, so a node's option state is part of its snapshot.
/// The kernel environment holds options globally, and `apply_options_to_env`
/// only ever ADDS — so without this an option set by an earlier node would be
/// in force for a later one that never wrote it, which is the same
/// leak-forward bug in a different table.
#[derive(Default)]
pub(super) struct OptionScope {
    /// Option name → its value before this batch first touched it.
    original: HashMap<String, Option<Option<String>>>,
    /// Options currently applied on behalf of some node.
    applied: Vec<String>,
}

impl OptionScope {
    /// Make `env`'s options exactly the ones in force at `node`'s source
    /// position: its snapshot's file-scope options, then any `set_option … in`
    /// wrappers, outermost first.
    pub(super) fn enter(&mut self, env: &mut Environment, node: &Node) {
        for name in std::mem::take(&mut self.applied) {
            self.restore_one(env, &name);
        }
        let mut want: Vec<(String, Option<String>)> = node
            .lex
            .options()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        want.sort_by(|a, b| a.0.cmp(&b.0));
        want.extend(node.option_overrides.iter().cloned());
        for (name, value) in want {
            self.original
                .entry(name.clone())
                .or_insert_with(|| env.get_option(&name).cloned());
            env.set_option(name.clone(), value);
            self.applied.push(name);
        }
    }

    /// Put every option this scope ever touched back the way it was.
    pub(super) fn leave(&mut self, env: &mut Environment) {
        for name in std::mem::take(&mut self.applied) {
            self.restore_one(env, &name);
        }
        for (name, original) in std::mem::take(&mut self.original) {
            match original {
                Some(value) => env.set_option(name, value),
                None => env.remove_option(&name),
            }
        }
    }

    fn restore_one(&self, env: &mut Environment, name: &str) {
        match self.original.get(name) {
            Some(Some(value)) => env.set_option(name.to_string(), value.clone()),
            Some(None) | None => env.remove_option(name),
        }
    }
}

/// Build an `ElabCtx` carrying `node`'s frozen lexical context.
///
/// Every lexical channel is read by REFERENCE out of the snapshot, never taken
/// from it: a deferred node is re-elaborated in a later round against the same
/// snapshot, and a take would leave it empty from the second round on.
/// `siblings` names the same-batch declarations that contributed no
/// forward-resolvable header. It is DIAGNOSTIC ONLY: the elaborator reads it
/// exclusively on the path where a name has already failed to resolve, to say
/// which sibling the name matched instead of offering nearest theorem names.
/// Pass an empty slice wherever the question does not arise (the header and
/// type phases, where no body is looking for a sibling yet).
pub(super) fn elab_ctx_for<'a>(
    env: &'a Environment,
    node: &Node,
    siblings: &[UnstagedSibling],
) -> Result<ElabCtx<'a>, ElabError> {
    let lex = &node.lex;
    let world = lex
        .import_world()
        .map(|_| lex.lean_world())
        .transpose()
        .map_err(|error| ElabError::SourceWorld(error.to_string()))?;
    let mut ctx = ElabCtx::new(env);
    if let Some(world) = world {
        ctx.set_source_world(world);
    }
    ctx.set_unstaged_siblings(
        siblings
            .iter()
            .filter(|sibling| node.name.as_ref().is_none_or(|own| own != &sibling.name))
            .cloned()
            .collect(),
    );
    ctx.set_term_info_capture(lex.term_info_capture());
    ctx.set_namespace_state(replay_directives(
        env,
        lex.namespace_state(),
        &node.directives,
    ));
    let instance_view = lex.instance_view(env);
    ctx.set_instance_scope_state(
        instance_view.hidden(),
        lex.scoped_instance_map().clone(),
        lex.default_instance_entries(),
    );
    ctx.set_instance_view(instance_view);
    ctx.set_foreign_private_decls(lex.foreign_private_decls());
    // U2 rung-4 explicitness channel: the file-scope `universe` names FROZEN
    // with this node. `plan.rs` preprocessed the node against the same
    // context, and preprocessing merges those names into the declaration's
    // `universe_params` vector; without them here the elaborator would read a
    // merged `universe u` as a written `.{u}` list and close a declaration
    // whose author closed nothing. Taking them from the node's own snapshot
    // (not from the live context) keeps a re-elaborated deferred node reading
    // the same set it was planned with.
    ctx.set_file_universe_params(lex.current_universe_params().to_vec());
    let mut macro_ctx = lex.macro_ctx().clone();
    macro_ctx.set_active_variable_bindings(
        lex.active_variable_bindings()
            .map(|(name, id)| (name.to_owned(), id)),
    );
    ctx.set_macro_ctx(macro_ctx);
    if let Some(registry) = lex.tactic_registry() {
        ctx.set_tactic_registry(registry.clone());
    }
    ctx.set_user_term_elabs(lex.user_term_elabs().clone());
    // The batch's templates pre-resolved their free names while the plan
    // walked past them, against an environment without the batch and under
    // none of its `open`s; resolve them again against this one.
    replay_templates(env, &mut ctx, &node.templates);
    Ok(ctx)
}

/// Make again, against `env`, the pre-resolution of each of `templates` that
/// `ctx`'s namespace state records, from where the template was declared:
/// its namespace state there, with the directives in force there replayed
/// against `env` exactly as a declaration's own are ([`replay_directives`]).
///
/// So a template's free name means what an ordinary name written at the
/// template's declaration means under header-first checking: it sees every
/// declaration of the batch, the batch's `open`s as written around the
/// template, and nothing of the use's.
fn replay_templates(
    env: &Environment,
    ctx: &mut ElabCtx<'_>,
    templates: &[Arc<TemplateDeclaration>],
) {
    for template in templates {
        let declared_under =
            replay_directives(env, &template.namespace_state, &template.directives);
        ctx.re_resolve_template_site(template.site, declared_under);
    }
}

/// [`replay_templates`] into the caller's own namespace state, against the
/// published environment, once the batch has published: a later batch then
/// reads what each of this batch's templates names, not what the plan saw.
pub(super) fn replay_trailing_templates(
    env: &Environment,
    file_ctx: &crate::FileContext,
    base: NamespaceState,
    templates: &[Arc<TemplateDeclaration>],
) -> NamespaceState {
    if templates.is_empty() {
        return base;
    }
    let mut ctx = ElabCtx::new(env);
    ctx.set_foreign_private_decls(file_ctx.foreign_private_decls());
    ctx.set_namespace_state(base);
    replay_templates(env, &mut ctx, templates);
    ctx.take_namespace_state()
}

/// Replay every `open` / `export` in force at a node's source position against
/// `env`, producing the namespace state the declaration is elaborated under.
///
/// `open Foo` expands eagerly into one short-name alias per constant already
/// under `Foo.`, so WHEN it is applied decides WHAT it opens. Applying it while
/// walking the source — before any of the batch's own declarations exist —
/// opens an empty namespace. Replaying it here, against an environment that
/// already holds the complete header index, is what makes `open` mean the same
/// thing regardless of where in the batch the opened declarations were written.
///
/// A failed directive is skipped rather than propagated: it will fail again,
/// loudly and with a span, when the ordinary path reports it. Silently
/// dropping the alias can only cause an unresolved name — a refusal — never a
/// wrong resolution.
fn replay_directives(
    env: &Environment,
    base: &NamespaceState,
    directives: &[LexicalDirective],
) -> NamespaceState {
    let mut state = base.clone();
    if directives.is_empty() {
        return state;
    }
    let node_namespace = state.current_namespace().clone();
    for directive in directives {
        match directive {
            LexicalDirective::Open { scoped: true, .. } => {
                // `open scoped` affects scoped notations and attributes only;
                // it brings no names into scope.
            }
            LexicalDirective::Open {
                paths, issued_in, ..
            } => {
                set_current_namespace(&mut state, issued_in);
                let _ = crate::namespace::process_open(env, paths, &mut state);
            }
            LexicalDirective::Export {
                namespace,
                names,
                issued_in,
            } => {
                set_current_namespace(&mut state, issued_in);
                let current = clean_parser::SurfaceName::from_name(issued_in.clone());
                let current = if issued_in.is_anon() {
                    None
                } else {
                    Some(&current)
                };
                let _ =
                    crate::namespace::process_export(env, namespace, names, current, &mut state);
            }
        }
    }
    set_current_namespace(&mut state, &node_namespace);
    state
}

/// Replay the directives still in force at the end of a batch into the
/// caller's own context, against the published environment.
pub(super) fn replay_trailing(
    env: &Environment,
    base: &NamespaceState,
    directives: &[LexicalDirective],
) -> NamespaceState {
    replay_directives(env, base, directives)
}

/// Move `state`'s current namespace to `target`.
///
/// A directive is resolved from the namespace it was WRITTEN in, which is an
/// ancestor of (or equal to) the namespace of the declaration it applies to.
fn set_current_namespace(state: &mut NamespaceState, target: &Name) {
    while !state.current_namespace().is_anon() {
        state.exit_namespace();
    }
    if target.is_anon() {
        return;
    }
    state.enter_resolved_namespace(target.clone());
}

/// Elaborate `node` against `env`. Registers nothing.
///
/// See [`elab_ctx_for`] for `siblings`; it changes no resolution, only which
/// refusal an already-failed one carries.
pub(super) fn elaborate_node(
    env: &Environment,
    node: &Node,
    siblings: &[UnstagedSibling],
) -> NodeElaboration {
    let mut ctx = match elab_ctx_for(env, node, siblings) {
        Ok(ctx) => ctx,
        Err(error) => {
            return NodeElaboration {
                result: Err(error),
                attributes: CtxAttributes::default(),
                hole_contexts: Vec::new(),
            };
        }
    };
    let result = ctx.elab_decl(&node.decl);
    ctx.finish_term_info();
    let hole_contexts = ctx.collect_hole_contexts();
    let attributes = CtxAttributes::collect(&mut ctx, result.as_ref().ok());
    NodeElaboration {
        result,
        attributes,
        hole_contexts,
    }
}

/// Register an already-elaborated node into the AUTHORITATIVE environment.
///
/// `env` here is never the staging environment: a header is never registered,
/// and a real declaration is never registered into staging by this path (the
/// body phase mirrors it separately, after discharging the header).
pub(super) fn register_node<'a>(
    env: &mut Environment,
    node: &mut Node,
    result: &'a ElabResult,
    mut attributes: CtxAttributes,
) -> Result<crate::source_family_authority::PublishedSourceResult<'a>, ElabError> {
    let publication = crate::source_family_authority::register_source_with_matchers(
        env,
        result,
        std::mem::take(&mut attributes.matchers),
    )?;
    // The batch is one elaboration run: every node's lexical snapshot keeps
    // the caller's run, so an `attribute [..]` command of the batch may name
    // a declaration of the batch (`crate::declared_here`).
    crate::declared_here::record_declared(
        env,
        node.lex.elab_unit(),
        register::leaf_own_names(result),
    );
    node.warning = register::registration_warning_for_result(env, result);
    register::register_param_names(env, &node.decl, result);
    attributes.apply(env, Some(&mut node.lex))?;
    crate::record_instance_scopes(&mut node.lex, env, result);
    Ok(publication)
}

/// Split a node's elaboration result into what registers and the `deriving`
/// classes that failed beside its type, and retain source diagnostics as
/// rejections of the node. A source error does not discard a registered value.
///
/// A failed class is an error beside its type, never instead of it
/// (`crate::infer::deriving_log`): the type registers without it, as in the
/// one-declaration-at-a-time driver, and each failure is reported. Callers
/// report the rejections only once the type has registered.
pub(super) fn split_logged_source_rejections(
    node: &Node,
    result: ElabResult,
) -> (ElabResult, Vec<super::BatchRejection>) {
    let (registrable, logged) = crate::infer::split_logged_deriving_failures(result);
    let mut rejections: Vec<_> = logged
        .into_iter()
        .filter_map(|leaf| match leaf {
            ElabResult::Failed { error, .. } => Some(super::BatchRejection::Elaboration {
                name: node.name.clone(),
                site: node.site(),
                error,
            }),
            _ => None,
        })
        .collect();
    if let Some(message) = registrable.source_error_message() {
        rejections.push(super::BatchRejection::Elaboration {
            name: node.name.clone(),
            site: node.site(),
            error: Box::new(ElabError::CommandFailed { message }),
        });
    }
    (registrable, rejections)
}

/// Every constant name an elaboration result introduces.
pub(super) fn introduced_names(result: &ElabResult, out: &mut std::collections::BTreeSet<Name>) {
    match result {
        ElabResult::Diagnosed { result, .. } => introduced_names(result, out),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Instance { name, .. } => {
            out.insert(name.clone());
        }
        ElabResult::Inductive {
            name,
            constructors,
            derived_instances,
            ..
        } => {
            out.insert(name.clone());
            out.extend(constructors.iter().map(|(n, _)| n.clone()));
            out.insert(name.clone().str("rec"));
            out.insert(name.clone().str("casesOn"));
            for derived in derived_instances {
                out.insert(derived.name.clone());
            }
        }
        ElabResult::MutualInductive {
            decl,
            derived_instances,
            ..
        } => {
            for ty in &decl.types {
                out.insert(ty.name.clone());
                out.extend(ty.constructors.iter().map(|c| c.name.clone()));
                out.insert(ty.name.clone().str("rec"));
                out.insert(ty.name.clone().str("casesOn"));
            }
            for derived in derived_instances {
                out.insert(derived.name.clone());
            }
        }
        ElabResult::Structure {
            name,
            ctor_name,
            projections,
            derived_instances,
            ..
        } => {
            out.insert(name.clone());
            out.insert(ctor_name.clone());
            out.extend(projections.iter().map(|(n, _, _)| n.clone()));
            out.insert(name.clone().str("rec"));
            out.insert(name.clone().str("casesOn"));
            for derived in derived_instances {
                out.insert(derived.name.clone());
            }
        }
        ElabResult::Multiple(inner) => {
            for r in inner {
                introduced_names(r, out);
            }
        }
        _ => {}
    }
}

/// Every constant name an elaboration result's TYPES and VALUES mention.
///
/// Read off the ELABORATED term, so it is exact: implicit arguments, resolved
/// instances and macro-expanded references are all present, which a syntactic
/// scan of the surface declaration could not see.
pub(super) fn referenced_names(result: &ElabResult, out: &mut std::collections::HashSet<Name>) {
    match result {
        ElabResult::Diagnosed { result, .. } => referenced_names(result, out),
        ElabResult::Definition { ty, val, .. } | ElabResult::Instance { ty, val, .. } => {
            ty.collect_constants_into(out);
            val.collect_constants_into(out);
        }
        ElabResult::Theorem { ty, proof, .. } => {
            ty.collect_constants_into(out);
            proof.collect_constants_into(out);
        }
        ElabResult::Axiom { ty, .. } => ty.collect_constants_into(out),
        ElabResult::Opaque { ty, val, .. } => {
            ty.collect_constants_into(out);
            if let Some(val) = val {
                val.collect_constants_into(out);
            }
        }
        ElabResult::Example { ty, val } => {
            ty.collect_constants_into(out);
            val.collect_constants_into(out);
        }
        ElabResult::Inductive {
            ty, constructors, ..
        } => {
            ty.collect_constants_into(out);
            for (_, ctor_ty) in constructors {
                ctor_ty.collect_constants_into(out);
            }
        }
        ElabResult::MutualInductive { decl, .. } => {
            for ty in &decl.types {
                ty.type_.collect_constants_into(out);
                for ctor in &ty.constructors {
                    ctor.type_.collect_constants_into(out);
                }
            }
        }
        ElabResult::Structure {
            ty,
            ctor_ty,
            projections,
            ..
        } => {
            ty.collect_constants_into(out);
            ctor_ty.collect_constants_into(out);
            for (_, proj_ty, proj_val) in projections {
                proj_ty.collect_constants_into(out);
                proj_val.collect_constants_into(out);
            }
        }
        ElabResult::Multiple(inner) => {
            for r in inner {
                referenced_names(r, out);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod source_world_tests {
    use super::*;
    use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
    use crate::FileContext;
    use std::path::Path;

    #[test]
    fn unknown_selected_world_refuses_written_and_inferred_declarations() {
        let _lock = crate::module_driver::module_elaboration_lock();
        let declarations = clean_parser::parse_file(
            "def refusedWritten : Nat := Nat.zero\ndef refusedInferred := Nat.zero\n",
        )
        .expect("parse declarations");
        let mut context = FileContext::new();
        context.set_import_context(
            Path::new("Unknown.lean"),
            Ok(clean_olean::ImportWorld::Project {
                world: "v0.0.0-unknown-source",
                lean_toolchain: "lean-toolchain".into(),
                lib: "unused".into(),
            }),
        );
        let mut env = Environment::with_prelude();
        let units = [SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }];
        let outcome = elaborate_module(
            &mut env,
            &mut context,
            &units,
            BatchOptions::per_declaration(),
        );
        assert!(!outcome.is_clean(), "{outcome:#?}");
        for name in ["refusedWritten", "refusedInferred"] {
            assert!(env.get_const(&clean_kernel::Name::from_string(name)).is_none());
        }
    }
}

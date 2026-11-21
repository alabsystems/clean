// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1 — the plan: one authored-order walk that fixes canonical names,
//! detects collisions, and SNAPSHOTS each declaration's lexical context at its
//! own source position.
//!
//! The snapshot is the point. `open`, `notation`, `set_option` and scoped
//! instances are LEXICAL: they are in force from where they are written
//! onward. Elaborating bodies out of authored order against one shared mutable
//! `FileContext` would leak later lexical state BACKWARD — a declaration would
//! see an `open` written after it. Freezing the context per declaration closes
//! that structurally rather than by discipline.
//!
//! Lexical effects are contributed by ELABORATION, not only by
//! [`crate::preprocess_decl_with_context`]: `open`, `export`, `syntax`,
//! `macro`, `notation` and `elab` all mutate the context and return
//! `ElabResult::Skipped`. So this walk runs them, in authored order, through
//! the ordinary driver — which is why no separate discovery pass (and no second
//! elaboration of every body) is needed.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use clean_kernel::Name;
use clean_parser::{OpenPath, Span, SurfaceDecl, SurfaceName, TemplateSiteId};

use super::{
    BatchRejection, CheckedJudgment, DeclHeader, DeclOutcome, DeclStatus, NoHeaderReason, Site,
    SourceUnit, UnitId,
};
use crate::namespace::NamespaceState;
use crate::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context,
    FileContext, HoleContext, RegistrationWarning,
};

/// An `open` or `export` in force at some source position.
///
/// These are NOT applied when the plan phase walks past them, and that is the
/// point. `open Foo` is not a note in a table: it EXPANDS, eagerly, into one
/// short-name alias per constant already under `Foo.` — so applying it before
/// the batch's own declarations exist opens an empty namespace, and a body
/// written under it then cannot see its own siblings. Header-first checking
/// has an answer to that which source order does not: the directive is
/// REPLAYED against the elaboration environment, which by then holds the
/// complete header index.
///
/// `issued_in` is the namespace that was current where the directive was
/// written. Replaying with the *node's* namespace instead would re-resolve the
/// opened namespace from a different starting point — `open Foo` written at
/// file level would become `M.Foo` inside `namespace M` — so it is carried
/// rather than reconstructed.
#[derive(Debug, Clone)]
pub(super) enum LexicalDirective {
    /// `open A B (c) hiding d renaming e -> f`.
    Open {
        /// The opened paths, with their selective/hiding/renaming clauses.
        paths: Vec<OpenPath>,
        /// `open scoped`, which brings no names into scope.
        scoped: bool,
        /// The namespace current where this was written.
        issued_in: Name,
    },
    /// `export A (b)`. Export aliases are permanent for the rest of the file —
    /// Lean stores them in the environment alias table — so these are recorded
    /// scope-immune and survive an `end`.
    Export {
        /// The source namespace.
        namespace: SurfaceName,
        /// The exported short names.
        names: Vec<SurfaceName>,
        /// The namespace current where this was written.
        issued_in: Name,
    },
}

/// A `notation`, `macro` or `macro_rules` template this batch declares, and
/// where it was declared.
///
/// Its declaration pre-resolves the template's free names, as Lean
/// pre-resolves a quotation's identifiers (`crate::namespace::
/// TemplateResolution`), and this walk runs that declaration — against
/// `base`, which holds none of the batch's declarations, and under none of
/// its `open`s, which the walk does not apply. So the record the declaration
/// leaves in every later snapshot names what the template would mean with an
/// empty batch: `def Satisfies …` then `notation:50 M " ⊨ " F:50 =>
/// Satisfies M F` in the same namespace recorded nothing for `Satisfies`.
/// Like an `open`, the record is therefore made again for each declaration,
/// against the environment it is elaborated in
/// ([`super::exec::elab_ctx_for`]), from the namespace state and the
/// directives in force HERE.
pub(super) struct TemplateDeclaration {
    /// The declaring command, under which the template's record is kept.
    pub(super) site: TemplateSiteId,
    /// The namespace state where the template was declared.
    pub(super) namespace_state: NamespaceState,
    /// Every `open` / `export` in force where the template was declared.
    pub(super) directives: Vec<LexicalDirective>,
}

/// What role a node plays in scheduling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeClass {
    /// `inductive` / `structure` / `class` / `coinductive`. Elaborated
    /// COMPLETELY in the type phase: a type-level declaration cannot depend on
    /// any BODY, only on other types, and a partially staged family (the type
    /// name visible without its constructors) is worse than none.
    TypeLevel,
    /// Everything that has a body: `def`, `theorem`, `axiom`, `opaque`,
    /// `instance`, `mutual`, and instances generated by a standalone derive.
    Value,
    /// `example`, `#check`, `attribute` — elaborated in authored
    /// order after the batch has registered, and registering nothing itself.
    Command,
    /// A lexical effect already applied by this walk.
    Lexical,
}

/// Where a node is in the pipeline.
#[derive(Debug)]
pub(super) enum NodeStatus {
    /// Not yet elaborated.
    Pending,
    /// Kernel-registered.
    Registered,
    /// Refused.
    Refused(BatchRejection),
    /// A lexical effect or a command; registers nothing.
    LexicalOrCommand,
}

/// One planned declaration.
pub(super) struct Node {
    /// Unit it was written in.
    pub(super) unit: UnitId,
    /// Its span.
    pub(super) span: Span,
    /// Position in authored order across the whole batch.
    pub(super) order: usize,
    /// The declaration to elaborate, after `variable`/`universe` threading.
    pub(super) decl: SurfaceDecl,
    /// Lexical context frozen at this declaration's source position.
    pub(super) lex: FileContext,
    /// `set_option … in` overrides wrapping this declaration, outermost first.
    pub(super) option_overrides: Vec<(String, Option<String>)>,
    /// Every `open` / `export` in force at this declaration's source position,
    /// in the order written. Replayed against the elaboration environment; see
    /// [`LexicalDirective`].
    pub(super) directives: Vec<LexicalDirective>,
    /// Every template this batch declared before this declaration, in the
    /// order written: their records in `lex` are made again where it is
    /// elaborated ([`TemplateDeclaration`]).
    pub(super) templates: Vec<Arc<TemplateDeclaration>>,
    /// What role it plays.
    pub(super) class: NodeClass,
    /// Canonical name, assigned HERE and never re-derived. Anonymous
    /// declarations (an unnamed `instance`, a `mutual` block) have none.
    pub(super) name: Option<Name>,
    /// Its staged signature, once the header phase runs.
    pub(super) header: Option<DeclHeader>,
    /// Why it has no staged signature, when it has none.
    pub(super) no_header: Option<NoHeaderReason>,
    /// Constants it introduced.
    pub(super) introduces: BTreeSet<Name>,
    /// Constants its elaborated term named.
    pub(super) depends_on: BTreeSet<Name>,
    /// Registration warning, if any.
    pub(super) warning: Option<RegistrationWarning>,
    /// Hole contexts captured while elaborating it.
    pub(super) hole_contexts: Vec<HoleContext>,
    /// Anonymous proof judgments retained after successful command registration.
    pub(super) checked_judgments: Vec<CheckedJudgment>,
    /// Where it is in the pipeline.
    pub(super) status: NodeStatus,
}

impl Node {
    /// Where this node was written.
    pub(super) fn site(&self) -> Site {
        Site {
            unit: self.unit,
            span: self.span,
        }
    }

    /// A name for diagnostics, even when no canonical name was assigned.
    pub(super) fn display_name(&self) -> String {
        match &self.name {
            Some(name) => name.to_string(),
            None => format!("<anonymous declaration at {:?}>", self.span),
        }
    }
}

/// Every node of the batch, plus whatever the plan phase already refused.
pub(super) struct Plan {
    /// Nodes in authored order.
    pub(super) nodes: Vec<Node>,
    /// Plan-phase refusals — today, name collisions.
    pub(super) rejections: Vec<BatchRejection>,
    /// The `open` / `export` directives still in force at the end of the batch.
    /// Replayed into the caller's context once the batch has published, so the
    /// caller resumes with the aliases the source actually established.
    pub(super) trailing_directives: Vec<LexicalDirective>,
    /// Every template the batch declares, in the order written. Their records
    /// are made again in the caller's context once the batch has published,
    /// so a later batch reads what each template names.
    pub(super) templates: Vec<Arc<TemplateDeclaration>>,
}

impl Plan {
    /// Index of every node that is still awaiting elaboration.
    pub(super) fn pending(&self) -> Vec<usize> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| matches!(n.status, NodeStatus::Pending))
            .map(|(i, _)| i)
            .collect()
    }

    /// Convert to the caller-facing outcome list, preserving authored order.
    pub(super) fn into_outcomes(self) -> Vec<DeclOutcome> {
        self.nodes
            .into_iter()
            .map(|node| DeclOutcome {
                unit: node.unit,
                span: node.span,
                name: node.name,
                status: match node.status {
                    // A node that never left Pending was never scheduled. It is
                    // reported as unschedulable rather than as a success with no
                    // evidence behind it.
                    NodeStatus::Pending => DeclStatus::NoHeader {
                        reason: node
                            .no_header
                            .unwrap_or(NoHeaderReason::SignatureDidNotElaborate),
                    },
                    NodeStatus::Registered => DeclStatus::Registered,
                    NodeStatus::Refused(rejection) => DeclStatus::Refused(rejection),
                    NodeStatus::LexicalOrCommand => DeclStatus::LexicalOrCommand,
                },
                introduces: node.introduces,
                depends_on: node.depends_on,
                warning: node.warning,
                hole_contexts: node.hole_contexts,
                checked_judgments: node.checked_judgments,
            })
            .collect()
    }
}

/// Walk every unit in AUTHORED order, applying lexical effects and recording
/// one node per declaration.
///
/// `base` receives only what the lexical pass produces — imports, option state,
/// aesop rule sets. No declaration of this batch is registered here.
pub(super) fn plan(
    base: &mut clean_kernel::Environment,
    file_ctx: &mut FileContext,
    units: &[SourceUnit<'_>],
) -> Plan {
    let mut ctx = Walk {
        base,
        fc: file_ctx,
        nodes: Vec::new(),
        rejections: Vec::new(),
        claimed: HashMap::new(),
        directives: vec![Vec::new()],
        templates: Vec::new(),
    };
    for unit in units {
        ctx.walk(unit.id, unit.decls);
    }
    let trailing_directives = ctx.directives_in_force();
    Plan {
        nodes: ctx.nodes,
        rejections: ctx.rejections,
        trailing_directives,
        templates: ctx.templates,
    }
}

struct Walk<'a> {
    base: &'a mut clean_kernel::Environment,
    fc: &'a mut FileContext,
    nodes: Vec<Node>,
    rejections: Vec<BatchRejection>,
    claimed: HashMap<Name, Site>,
    /// One frame per lexical scope. Frame 0 is scope-immune: `export` aliases
    /// live there because Lean keeps them for the rest of the file.
    directives: Vec<Vec<LexicalDirective>>,
    /// Every template declared so far, in the order written. Not scoped: a
    /// template's record outlives the `section` it was declared in.
    templates: Vec<Arc<TemplateDeclaration>>,
}

impl Walk<'_> {
    fn walk(&mut self, unit: UnitId, decls: &[SurfaceDecl]) {
        for decl in decls {
            self.walk_one(unit, decl, &[]);
        }
    }

    fn walk_one(
        &mut self,
        unit: UnitId,
        decl: &SurfaceDecl,
        option_overrides: &[(String, Option<String>)],
    ) {
        match decl {
            SurfaceDecl::Namespace { name, decls, .. } => {
                let namespace = name
                    .qualify_under(&SurfaceName::from_name(
                        self.fc.namespace_state().current_namespace().clone(),
                    ))
                    .into_name();
                self.fc
                    .namespace_state_mut()
                    .enter_resolved_namespace(namespace);
                self.fc.namespace_state_mut().push_scope();
                self.fc.enter_section();
                self.directives.push(Vec::new());
                self.walk(unit, decls);
                self.directives.pop();
                self.fc.exit_section_restoring_env_options(self.base);
                self.fc.namespace_state_mut().pop_scope();
                self.fc.namespace_state_mut().exit_namespace();
            }
            SurfaceDecl::Section { decls, .. } => {
                self.fc.enter_section();
                self.fc.namespace_state_mut().push_scope();
                self.directives.push(Vec::new());
                self.walk(unit, decls);
                self.directives.pop();
                self.fc.namespace_state_mut().pop_scope();
                self.fc.exit_section_restoring_env_options(self.base);
            }
            SurfaceDecl::SetOption {
                name,
                value,
                body: Some(inner),
                ..
            } => {
                let mut overrides = option_overrides.to_vec();
                let key = match crate::options_registry::surface_option_key(name) {
                    Ok(key) => key,
                    Err(error) => {
                        // Retain the authored wrapper as a refused node. Do not
                        // execute its inner declaration under a different key.
                        self.push_lexical_marker(
                            unit,
                            decl,
                            NodeStatus::Refused(BatchRejection::Elaboration {
                                name: None,
                                site: Site {
                                    unit,
                                    span: decl.span(),
                                },
                                error: Box::new(error),
                            }),
                        );
                        return;
                    }
                };
                overrides.push((key, value.clone()));
                self.walk_one(unit, inner, &overrides);
            }
            // A `mutual … end` block is ONE atomic node. Its members already
            // resolve against each other, and the supported mutual-inductive
            // path registers the whole family in a single `add_inductive`, so
            // splitting the block would manufacture a cycle that is not one.
            SurfaceDecl::Mutual { .. } => {
                self.push_node(unit, decl, option_overrides, NodeClass::Value);
            }
            SurfaceDecl::Def { .. }
            | SurfaceDecl::Theorem { .. }
            | SurfaceDecl::Axiom { .. }
            | SurfaceDecl::Opaque { .. }
            | SurfaceDecl::Instance { .. }
            | SurfaceDecl::DerivingInstance { .. } => {
                self.push_node(unit, decl, option_overrides, NodeClass::Value);
            }
            SurfaceDecl::Inductive { .. }
            | SurfaceDecl::Coinductive { .. }
            | SurfaceDecl::Structure { .. }
            | SurfaceDecl::Class { .. } => {
                self.push_node(unit, decl, option_overrides, NodeClass::TypeLevel);
            }
            // Commands: elaborated in authored order AFTER the batch registers,
            // because commands such as `attribute` name declarations this batch
            // introduces.
            //
            // `#guard_msgs … in cmd` is one command whatever `cmd` is: the
            // messages it compares are the ones `cmd` produces when it runs.
            SurfaceDecl::Example { .. }
            | SurfaceDecl::Check { .. }
            | SurfaceDecl::Eval { .. }
            | SurfaceDecl::Reduce { .. }
            | SurfaceDecl::Print { .. }
            | SurfaceDecl::PrintAxioms { .. }
            | SurfaceDecl::PrintEquations { .. }
            | SurfaceDecl::Guard { .. }
            | SurfaceDecl::GuardMsgs { .. }
            | SurfaceDecl::Attribute { .. }
            | SurfaceDecl::Prelude { .. }
            | SurfaceDecl::RawDecl { .. } => {
                self.push_node(unit, decl, option_overrides, NodeClass::Command);
            }
            // `open Foo in <decl>`: the open is in force for exactly one
            // declaration. Recorded as a one-declaration scope rather than
            // left on the wrapper, so the wrapped declaration is an ordinary
            // node — it gets a canonical name, a header, and a place in the
            // dependency graph like any other.
            SurfaceDecl::Open {
                paths,
                scoped,
                body: Some(inner),
                ..
            } => {
                self.directives.push(vec![LexicalDirective::Open {
                    paths: paths.clone(),
                    scoped: *scoped,
                    issued_in: self.fc.namespace_state().current_namespace().clone(),
                }]);
                self.walk_one(unit, inner, option_overrides);
                self.directives.pop();
            }
            SurfaceDecl::Open {
                paths,
                scoped,
                body: None,
                ..
            } => {
                let directive = LexicalDirective::Open {
                    paths: paths.clone(),
                    scoped: *scoped,
                    issued_in: self.fc.namespace_state().current_namespace().clone(),
                };
                if let Some(frame) = self.directives.last_mut() {
                    frame.push(directive);
                }
                self.push_lexical_marker(unit, decl, NodeStatus::LexicalOrCommand);
            }
            // `include x` / `omit x`: a lexical directive on the FILE CONTEXT,
            // applied in authored order, like `variable`.
            SurfaceDecl::IncludeVars { names, .. } => {
                self.fc.include_variables(names);
                self.push_lexical_marker(unit, decl, NodeStatus::LexicalOrCommand);
            }
            SurfaceDecl::OmitVars { names, .. } => {
                self.fc.omit_variables(names);
                self.push_lexical_marker(unit, decl, NodeStatus::LexicalOrCommand);
            }
            SurfaceDecl::Export {
                namespace, names, ..
            } => {
                let directive = LexicalDirective::Export {
                    namespace: namespace.clone(),
                    names: names.clone(),
                    issued_in: self.fc.namespace_state().current_namespace().clone(),
                };
                // Frame 0: an `export` alias survives `end`.
                self.directives[0].push(directive);
                self.push_lexical_marker(unit, decl, NodeStatus::LexicalOrCommand);
            }
            // Everything else lexical — `import`, `variable`, `universe`,
            // file-scope `set_option`, `notation`, `macro`, `syntax`, `elab`.
            // These are applied HERE, in authored order, so every snapshot
            // taken after this point carries them and no snapshot taken before
            // it does. Unlike `open`, none of them expands against the set of
            // declarations that exist, so applying them early is exact — but
            // for the pre-resolution of a template's free names, which is made
            // again where each declaration is elaborated
            // ([`TemplateDeclaration`]).
            _ => {
                self.apply_lexical(unit, decl);
            }
        }
    }

    /// Every directive in force at the current position, outermost first.
    fn directives_in_force(&self) -> Vec<LexicalDirective> {
        self.directives.iter().flatten().cloned().collect()
    }

    /// Record an `open` / `export` as a node so it is reported in authored
    /// order, without applying it: it is replayed at elaboration time instead.
    fn push_lexical_marker(&mut self, unit: UnitId, decl: &SurfaceDecl, status: NodeStatus) {
        self.nodes.push(Node {
            unit,
            span: decl.span(),
            order: self.nodes.len(),
            decl: decl.clone(),
            lex: self.fc.lexical_snapshot(),
            option_overrides: Vec::new(),
            directives: self.directives_in_force(),
            templates: self.templates.clone(),
            class: NodeClass::Lexical,
            name: None,
            header: None,
            no_header: None,
            introduces: BTreeSet::new(),
            depends_on: BTreeSet::new(),
            warning: None,
            hole_contexts: Vec::new(),
            checked_judgments: Vec::new(),
            status,
        });
    }

    fn apply_lexical(&mut self, unit: UnitId, decl: &SurfaceDecl) {
        let processed = preprocess_decl_with_context(decl, self.fc);
        // `preprocess_decl_with_context` handles `variable` / `universe`; the
        // rest (`open`, `export`, `notation`, `macro`, `syntax`, `elab`,
        // `import`, file-scope `set_option`) are contributed by elaboration and
        // must go through the driver to reach the context.
        //
        // A failure here is recorded and the walk continues: a bad `open`
        // must not silently delete every declaration after it.
        //
        // A template's declaration records its pre-resolution under its own
        // span; a record made by this call is a `TemplateDeclaration` (the
        // `Arc` held across the call tells a new record from an old one, which
        // another unit's declaration at the same span may have left).
        let site = TemplateSiteId::of_span(processed.span());
        let before = self.fc.namespace_state().template_site(site).cloned();
        let status = match elaborate_decl_and_register_with_context_and_warning(
            self.base, &processed, self.fc,
        ) {
            Ok(registered) => match registered.result.source_error_message() {
                Some(message) => NodeStatus::Refused(BatchRejection::Elaboration {
                    name: None,
                    site: Site {
                        unit,
                        span: decl.span(),
                    },
                    error: Box::new(crate::ElabError::CommandFailed { message }),
                }),
                None => NodeStatus::LexicalOrCommand,
            },
            Err(error) => NodeStatus::Refused(BatchRejection::Elaboration {
                name: None,
                site: Site {
                    unit,
                    span: decl.span(),
                },
                error: Box::new(error),
            }),
        };
        let recorded = self
            .fc
            .namespace_state()
            .template_site(site)
            .is_some_and(|after| {
                before
                    .as_ref()
                    .is_none_or(|before| !Arc::ptr_eq(before, after))
            });
        if recorded {
            self.templates.push(Arc::new(TemplateDeclaration {
                site,
                namespace_state: self.fc.namespace_state().clone(),
                directives: self.directives_in_force(),
            }));
        }
        self.nodes.push(Node {
            unit,
            span: decl.span(),
            order: self.nodes.len(),
            decl: processed,
            lex: self.fc.lexical_snapshot(),
            option_overrides: Vec::new(),
            directives: self.directives_in_force(),
            templates: self.templates.clone(),
            class: NodeClass::Lexical,
            name: None,
            header: None,
            no_header: None,
            introduces: BTreeSet::new(),
            depends_on: BTreeSet::new(),
            warning: None,
            hole_contexts: Vec::new(),
            checked_judgments: Vec::new(),
            status,
        });
    }

    fn push_node(
        &mut self,
        unit: UnitId,
        decl: &SurfaceDecl,
        option_overrides: &[(String, Option<String>)],
        class: NodeClass,
    ) {
        let span = decl.span();
        let processed = preprocess_decl_with_context(decl, self.fc);
        // Match the ordinary declaration driver's session preparation before
        // freezing this node's instance view. Imports/lexical declarations use
        // their own authored-order driver above; seeding at batch entry would
        // preempt imported bridges. `base` is the private transactional clone,
        // so a rejected all-or-nothing batch publishes none of this support.
        crate::prepare_declaration_environment(self.base, &processed);
        let name = if class == NodeClass::Command {
            None
        } else {
            self.canonical_name(&processed)
        };
        let site = Site { unit, span };

        // Ruling step 1: detect collisions. Silently skipping the second
        // claimant is what lets two declarations disagree about what a name
        // means with no diagnostic at all.
        let mut status = NodeStatus::Pending;
        if let Some(name) = &name {
            if let Some(first) = self.claimed.get(name) {
                let rejection = BatchRejection::NameCollision {
                    name: name.clone(),
                    first: *first,
                    second: site,
                };
                self.rejections.push(rejection.clone());
                status = NodeStatus::Refused(rejection);
            } else {
                self.claimed.insert(name.clone(), site);
            }
        }
        self.nodes.push(Node {
            unit,
            span,
            order: self.nodes.len(),
            decl: processed,
            lex: self.fc.lexical_snapshot(),
            option_overrides: option_overrides.to_vec(),
            directives: self.directives_in_force(),
            templates: self.templates.clone(),
            class,
            name,
            header: None,
            no_header: None,
            introduces: BTreeSet::new(),
            depends_on: BTreeSet::new(),
            warning: None,
            hole_contexts: Vec::new(),
            checked_judgments: Vec::new(),
            status,
        });
    }

    /// The name this declaration will be registered under, qualified exactly as
    /// the authoritative pass qualifies it.
    ///
    /// `None` for a declaration whose canonical name is minted against the
    /// environment (an anonymous `instance`, whose generated `instFooBar_1`
    /// depends on what is already registered) or that introduces a family
    /// (`mutual`). Those cannot be staged, and saying so here is what keeps
    /// them out of the header index instead of staging an unstable name.
    fn canonical_name(&self, decl: &SurfaceDecl) -> Option<Name> {
        let short = crate::preprocess_ext::decl_name(decl)?;
        if short.is_anonymous() {
            return None;
        }
        let ns = self.fc.namespace_state().current_namespace();
        Some(
            short
                .qualify_under(&SurfaceName::from_name(ns.clone()))
                .into_name(),
        )
    }
}

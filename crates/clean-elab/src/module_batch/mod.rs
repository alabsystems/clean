// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Header-first batch elaboration — the whole module's signatures before any
//! body (Trust I1).
//!
//! # Why this exists
//!
//! Clean's one-declaration-at-a-time driver elaborates each declaration's type
//! AND body against the environment the previous declarations built. Name
//! resolution therefore depends on source order, and the failure that causes is
//! not "a name was unknown" — it is the WRONG MEANING, kernel-certified:
//!
//! ```lean
//! namespace Imported
//! def pick : Nat := 0
//! end Imported
//!
//! namespace M
//! open Imported
//! def early : Nat := pick        -- resolves to Imported.pick = 0 …
//! theorem locked : early = 0 := rfl
//! end M
//!
//! namespace M
//! def pick : Nat := 1            -- … but THIS is what `pick` means
//! end M
//! ```
//!
//! Clean's own resolver takes candidates from the current namespace outward
//! BEFORE consulting `open` declarations (`infer/elab_core.rs`), so with the
//! complete name index `early` means `M.pick = 1` and `locked` is false. Under
//! source order it is accepted. The kernel is not at fault: it certified
//! exactly the term it was handed. The term is not the one the source denotes.
//!
//! A retry loop cannot fix this. Elaboration is NOT monotone —
//! `elab(source, partial_env)` can produce a different term from
//! `elab(source, full_header_env)` — so the defect is in the declarations that
//! SUCCEED, and a retry loop never revisits a success. It implements "first
//! successful interpretation wins", which is a different language semantics.
//! The ruling of record is
//! `docs/design/2026-08-05-i1-ruling-header-elaboration.md` in the Trust
//! superproject.
//!
//! # The shape
//!
//! [`elaborate_module`] runs six phases, one per step of the ruling:
//!
//! 1. **plan** ([`plan`]) — parse-order walk of every unit. Lexical effects
//!    (`open`, `notation`, `set_option`, `variable`, namespace/section
//!    structure) are applied in AUTHORED order, and each declaration's lexical
//!    context is SNAPSHOT at its own source position. A shared mutable
//!    `FileContext` would leak later lexical state backward — an `open` written
//!    after a declaration would be in force for it.
//! 2. **types** ([`stage::elaborate_type_declarations`]) — `inductive`,
//!    `structure` and `class` have no type/body seam at all: their
//!    constructors' and fields' types ARE the declaration. They are elaborated
//!    COMPLETELY and registered as real declarations, not staged as a partial
//!    family.
//! 3. **headers** ([`stage::stage_headers`]) — every remaining signature is
//!    elaborated against the complete header index, to a FIXED POINT that is
//!    then CONFIRMED: the last iteration must reproduce the previous one
//!    exactly. That confirmation is what makes "elaborated against the complete
//!    index" a checked property rather than an assumption.
//! 4. **bodies** ([`publish::elaborate_bodies`]) — bodies elaborate against the
//!    staging environment (complete index) and register into a SEPARATE
//!    authoritative environment, in dependency order, recording resolved
//!    dependencies.
//! 5. **cycles** ([`schedule`]) — whatever cannot be scheduled is classified
//!    into proof cycles, signature cycles and unsupported mutual groups, each
//!    with a diagnostic that names the fix WITH OPTIONS.
//! 6. **publish** ([`publish::audit`]) — a zero-placeholder,
//!    zero-staged-header, zero-cycle audit runs before the caller's environment
//!    is advanced at all.
//!
//! # The binding invariant
//!
//! **A staged header is never citable.** It lives only in the staging
//! environment, which is a local of [`elaborate_module`], has no accessor, is
//! never returned and is dropped at return. The authoritative environment never
//! holds one at any moment. Four independent mechanisms, strongest first:
//!
//! 1. **Absence.** A body elaborates against `staging` but registers into
//!    `publish`. If the elaborated term names a staged header, `add_decl` fails
//!    with an unknown-constant type error. The kernel's own fail-closed check
//!    is the firewall; no new code is trusted for it.
//! 2. **Named diagnostic.** Before registering, the elaborated term's constants
//!    are scanned against the live staged set, and a node naming one is
//!    DEFERRED (it is waiting on a sibling) or, if nothing can progress,
//!    reported as a cycle. This is the scheduler and the message; (1) is the
//!    safety.
//! 3. **Kernel marker.** [`clean_kernel::Environment::add_staged_header`]
//!    records the name, and `audit_certification` reports a blocking
//!    `CertificationIssue::Staged` for any reachable member. Even if a staging
//!    environment escaped, nothing it supports can grade above `Rejected`.
//! 4. **Publish gate.** [`publish::audit`] refuses outright if the
//!    authoritative environment has any staged header. It is never reached; it
//!    is the tripwire that fails a future refactor loudly instead of quietly.
//!
//! # What is still order-dependent
//!
//! Order independence is exactly as wide as the header index. A declaration
//! reported as [`DeclStatus::NoHeader`] contributed no signature, so references
//! to it are resolved by the body worklist in whatever order it manages to
//! schedule — which is today's semantics, not a new hazard, but not the
//! guarantee either. A caller that needs the full property should refuse a batch
//! whose outcome contains one; the status is reported per declaration precisely
//! so it can.
//!
//! Two shapes reach it, and only two:
//!
//! * [`NoHeaderReason::UnsupportedShape`] — an ANONYMOUS `instance`. Its
//!   canonical name is minted by probing the environment for a free
//!   `instFooBar_N`, so it differs between the staging and publish
//!   environments; staging it would freeze a name the authoritative pass does
//!   not use. Give the instance an explicit name and it stages like anything
//!   else.
//! * [`NoHeaderReason::ResidualMetavariable`] — the elaborated signature still
//!   carried `?m` or an unsolved level, which are solved FROM THE BODY. Staging
//!   it would publish a provisional signature, which is the one thing the
//!   binding invariant forbids.
//!
//! `def f := e` with no written type is NOT in that list: its type is read off
//! a full elaboration performed inside the header fixed point, so it is staged
//! like any other declaration. See [`stage`].

mod exec;
mod plan;
mod publish;
pub mod render;
mod schedule;
mod stage;

use std::collections::BTreeSet;

use clean_kernel::{Expr, Name};
use clean_parser::{Span, SurfaceDecl};

use crate::{ElabError, FileContext, HoleContext, RegistrationWarning};

pub use plan::NodeClass;

/// Caller-assigned identity of one source region — a Clean island, a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnitId(pub u32);

/// One parsed source region.
///
/// The slice is in AUTHORED order and stays so: only BODY elaboration is
/// reordered, never lexical effects. Parsing policy — island framing, tactic
/// patterns, byte offsets into a host file — belongs to the caller; this module
/// takes parsed declarations and does not acquire it.
#[derive(Debug, Clone, Copy)]
pub struct SourceUnit<'a> {
    /// Caller-assigned identity, echoed back on every outcome.
    pub id: UnitId,
    /// The unit's declarations, in authored order.
    pub decls: &'a [SurfaceDecl],
}

/// What a refusal costs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchAtomicity {
    /// A refusal commits NOTHING. Correct for Clean islands inside a Rust file:
    /// the island either means what it says or it is not there.
    AllOrNothing,
    /// Register the acyclic, non-refused part. Correct for a file being checked
    /// interactively, where per-declaration reporting is the product.
    PerDeclaration,
}

/// Whether a staged header may disagree with the declaration finally
/// registered under its name.
///
/// There is exactly one variant, on purpose. A header that disagrees with the
/// registered constant means other declarations were elaborated against a
/// signature the kernel does not hold — a source-to-kernel fidelity failure of
/// precisely the class this module exists to close. The type exists so the
/// obligation is visible at every call site, not so it can be waived.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeaderAgreement {
    /// The registered constant's level parameters must be equal as a sequence
    /// and its type definitionally equal to the staged header's.
    Required,
}

/// Options for one [`elaborate_module`] call.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct BatchOptions {
    /// See [`BatchAtomicity`].
    pub atomicity: BatchAtomicity,
    /// See [`HeaderAgreement`].
    pub enforce_header_agreement: HeaderAgreement,
}

impl BatchOptions {
    /// Island defaults: a refusal commits nothing, header agreement enforced.
    #[must_use]
    pub fn islands() -> Self {
        Self {
            atomicity: BatchAtomicity::AllOrNothing,
            enforce_header_agreement: HeaderAgreement::Required,
        }
    }

    /// File defaults: report per declaration, header agreement enforced.
    #[must_use]
    pub fn per_declaration() -> Self {
        Self {
            atomicity: BatchAtomicity::PerDeclaration,
            enforce_header_agreement: HeaderAgreement::Required,
        }
    }
}

impl Default for BatchOptions {
    fn default() -> Self {
        Self::islands()
    }
}

/// Where a declaration was written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Site {
    /// The unit the declaration was written in.
    pub unit: UnitId,
    /// Its span within that unit's source.
    pub span: Span,
}

/// What happened to one top-level declaration.
#[derive(Debug)]
pub enum DeclStatus {
    /// Kernel-registered into the authoritative environment.
    Registered,
    /// Elaborated and scheduled, but contributed no signature to the name
    /// index. Still a graph node: its canonical name participates in collision
    /// detection and its dependencies are still edges.
    NoHeader {
        /// Why no header could be produced.
        reason: NoHeaderReason,
    },
    /// Refused. Under [`BatchAtomicity::AllOrNothing`] one of these refuses the
    /// whole batch.
    Refused(BatchRejection),
    /// A lexical effect (`open`, `notation`, `set_option`), an `example`, or a
    /// `#check`-class command. Applied in authored order; registers nothing.
    LexicalOrCommand,
}

/// Why a declaration contributed no header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NoHeaderReason {
    /// `def f := e` with no `: T`. The type is inferred from the body, which is
    /// exactly what a header may not look at. There is no signature to
    /// elaborate.
    TypeInferredFromBody,
    /// The elaborated type still carried a metavariable or an unsolved level.
    /// Those are solved from the body, so the header would be provisional in
    /// the one way a header may never be.
    ResidualMetavariable,
    /// `coinductive`, an anonymous `instance` (whose canonical name is minted
    /// against the environment and so is not stable across staging), or a shape
    /// header elaboration does not model.
    UnsupportedShape,
    /// A type-level declaration (`inductive`, `structure`, `class`). These are
    /// not staged: they are elaborated COMPLETELY in the type phase, because a
    /// partial family — the type name visible without its constructors — is
    /// worse than none.
    TypeLevelDeclaration,
    /// The signature did not elaborate on its own. The declaration keeps
    /// source-order semantics and cannot be forward-referenced.
    SignatureDidNotElaborate,
}

/// A batch-level refusal.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum BatchRejection {
    /// Two declarations claim the same canonical name.
    NameCollision {
        /// The contested name.
        name: Name,
        /// Where it was first claimed.
        first: Site,
        /// Where it was claimed again.
        second: Site,
    },
    /// Headers did not reach a fixed point: re-elaborating every signature
    /// against the complete index kept changing the answer.
    HeaderNotStable {
        /// Names whose staged signature changed on the last iteration.
        names: Vec<Name>,
        /// Iterations attempted.
        iterations: usize,
    },
    /// A cycle among declaration TYPES. Types cannot legitimately depend on
    /// each other at the declaration level; a mutual inductive family is one
    /// atomic node, so it is not a cycle in this graph at all.
    SignatureCycle {
        /// Shortest cycle witness.
        witness: Vec<Site>,
        /// The names on the witness, in the same order.
        names: Vec<Name>,
    },
    /// A cycle among THEOREMS. `a` is only as proved as `b`, and `b` only as
    /// `a`; neither is proved.
    ProofCycle {
        /// Shortest cycle witness.
        witness: Vec<Site>,
        /// The names on the witness, in the same order.
        names: Vec<Name>,
    },
    /// A dependency cycle Clean cannot check as a mutual group.
    UnsupportedScc {
        /// Shortest cycle witness.
        witness: Vec<Site>,
        /// The names on the witness, in the same order.
        names: Vec<Name>,
        /// The ways forward, in order of preference.
        options: &'static [&'static str],
    },
    /// The registered declaration's type or level signature is not the one
    /// other declarations were elaborated against.
    HeaderTypeDivergence {
        /// The name whose signature diverged.
        name: Name,
        /// Where it was declared.
        site: Site,
        /// The staged signature, rendered.
        staged: String,
        /// The registered signature, rendered.
        registered: String,
    },
    /// A term reached the authoritative environment naming a staged header.
    /// Defence in depth: the kernel already refuses this by absence.
    StagedReference {
        /// The declaration whose term named a header.
        subject: Name,
        /// The headers it named.
        staged: Vec<Name>,
        /// Where it was declared.
        site: Site,
    },
    /// Elaboration or kernel registration failed.
    Elaboration {
        /// The declaration's canonical name, when one was assigned.
        name: Option<Name>,
        /// Where it was declared.
        site: Site,
        /// The underlying error.
        error: Box<ElabError>,
    },
    /// The publish audit refused: placeholders, staged headers, unsanctioned
    /// axioms, a cycle in the published constant graph, or trust debt.
    PublishAudit {
        /// Every issue found.
        issues: Vec<PublishAuditIssue>,
    },
}

/// A problem the publish audit found in the authoritative environment.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PublishAuditIssue {
    /// A staged header reached the authoritative environment. Unreachable by
    /// construction; this is the tripwire.
    StagedHeaderInPublishEnv {
        /// The offending names.
        names: Vec<Name>,
    },
    /// A declaration this batch registered carries an incomplete-proof or
    /// solver trust marker (`sorry` and friends).
    TrustDebt {
        /// The declaration.
        name: Name,
        /// The marker it reached.
        marker: Name,
    },
    /// A declaration this batch registered depends on an axiom that is neither
    /// a certification foundation nor written by the author in this batch.
    UnsanctionedAxiom {
        /// The declaration.
        name: Name,
        /// The axiom it reached.
        axiom: Name,
    },
    /// A declaration this batch registered is missing from the authoritative
    /// environment, or one of its dependencies is.
    MissingDeclaration {
        /// The absent name.
        name: Name,
    },
}

/// What happened to one top-level declaration, in authored order.
#[derive(Debug)]
pub struct DeclOutcome {
    /// The unit it was written in.
    pub unit: UnitId,
    /// Its span.
    pub span: Span,
    /// Canonical name, assigned in the plan phase and never re-derived.
    pub name: Option<Name>,
    /// What happened.
    pub status: DeclStatus,
    /// Every constant this declaration introduced, including an inductive's
    /// constructors, recursors and projections.
    pub introduces: BTreeSet<Name>,
    /// Resolved dependencies, read off the ELABORATED term, so exact wherever
    /// elaboration succeeded.
    pub depends_on: BTreeSet<Name>,
    /// Trust warning recorded at registration, if any.
    pub warning: Option<RegistrationWarning>,
    /// Hole contexts captured during elaboration, for IDE surfaces.
    pub hole_contexts: Vec<HoleContext>,
}

impl DeclOutcome {
    /// Where this declaration was written.
    #[must_use]
    pub fn site(&self) -> Site {
        Site {
            unit: self.unit,
            span: self.span,
        }
    }
}

/// The result of one [`elaborate_module`] call.
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct ModuleOutcome {
    /// One entry per top-level declaration, in AUTHORED order.
    pub decls: Vec<DeclOutcome>,
    /// Batch-level refusals: collisions, cycles, the publish audit.
    pub rejections: Vec<BatchRejection>,
    /// Whether the caller's environment was advanced. `false` means it is
    /// byte-identical to what was passed in.
    pub committed: bool,
}

impl ModuleOutcome {
    /// True when nothing was refused.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.rejections.is_empty()
            && self
                .decls
                .iter()
                .all(|d| !matches!(d.status, DeclStatus::Refused(_)))
    }

    /// Every refusal, batch-level and per-declaration, in report order.
    #[must_use]
    pub fn all_rejections(&self) -> Vec<&BatchRejection> {
        let mut out: Vec<&BatchRejection> = self.rejections.iter().collect();
        for decl in &self.decls {
            if let DeclStatus::Refused(rejection) = &decl.status {
                out.push(rejection);
            }
        }
        out
    }

    /// A human-and-agent readable rendering of every refusal.
    #[must_use]
    pub fn render_rejections(&self) -> String {
        self.all_rejections()
            .iter()
            .map(|r| render::rejection(r))
            .collect::<Vec<_>>()
            .join("\n\n")
    }
}

/// What kind of declaration a header stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeaderKind {
    /// `def` / `abbrev` with a written result type.
    Definition,
    /// `theorem`.
    Theorem,
    /// `axiom`.
    Axiom,
    /// `opaque`.
    Opaque,
    /// `instance` with an explicit name.
    Instance,
}

/// Instance metadata frozen at header time.
///
/// Instances are otherwise registered only when the real declaration lands, so
/// instance resolution would depend on registration order — the same defect as
/// name resolution, one level down. Freezing the class and priority in the
/// header phase makes the instance set complete before any body elaborates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceHeader {
    /// The class this instance implements.
    pub class_name: Name,
    /// Resolution priority.
    pub priority: u32,
    /// Position in canonical source order, used to break priority ties exactly
    /// as sequential registration would.
    pub synth_order: usize,
}

/// A declaration's SIGNATURE, elaborated without its body.
#[derive(Debug, Clone)]
pub struct DeclHeader {
    /// Canonical, namespace-qualified name — assigned once, in the plan phase.
    pub name: Name,
    /// The universe parameters that survive in `ty`.
    pub universe_params: Vec<Name>,
    /// The elaborated type. Meta-free and level-closed, or there is no header.
    pub ty: Expr,
    /// What the header stands for.
    pub kind: HeaderKind,
    /// Frozen instance metadata, for an `instance`.
    pub instance: Option<InstanceHeader>,
    /// Where it was written.
    pub origin: Site,
}

impl DeclHeader {
    /// Two headers agree when they name the same signature. Used to decide
    /// whether the header fixed point has converged.
    fn same_signature(&self, other: &Self) -> bool {
        self.name == other.name
            && self.universe_params == other.universe_params
            && self.ty == other.ty
            && self.kind == other.kind
            && self.instance == other.instance
    }
}

/// Elaborate every declaration of `units` header-first.
///
/// `env` is advanced only if every phase and the publish audit pass; on refusal
/// under [`BatchAtomicity::AllOrNothing`] it is not touched at all. `file_ctx`
/// is advanced to the end-of-batch lexical state exactly as the
/// one-declaration-at-a-time driver would leave it.
///
/// **No staged header is ever written into `env`.** See the module docs for the
/// four mechanisms that hold that invariant, three of them structural.
#[must_use]
pub fn elaborate_module(
    env: &mut clean_kernel::Environment,
    file_ctx: &mut FileContext,
    units: &[SourceUnit<'_>],
    options: BatchOptions,
) -> ModuleOutcome {
    // PHASE 1 — plan. Lexical effects in authored order; per-declaration
    // lexical snapshots; canonical names; collisions.
    //
    // `base` accumulates only what the lexical pass produces (imports, option
    // state, aesop rule sets). It is the common ancestor of both environments
    // below, and holds no declaration of this batch.
    let mut base = env.clone();
    let mut plan = plan::plan(&mut base, file_ctx, units);

    let mut outcome = ModuleOutcome {
        decls: Vec::new(),
        rejections: std::mem::take(&mut plan.rejections),
        committed: false,
    };

    if !outcome.rejections.is_empty() && options.atomicity == BatchAtomicity::AllOrNothing {
        outcome.decls = plan.into_outcomes();
        return outcome;
    }

    // PHASE 2 — type-level declarations, elaborated COMPLETELY (never staged as
    // a partial family) into `base`, so both environments below inherit them.
    stage::elaborate_type_declarations(&mut base, &mut plan);

    // PHASE 3 — headers, to a CONFIRMED fixed point in a staging environment
    // that is a local of this function and never escapes it: it has no
    // accessor, is never returned, is never handed to an audit, and is dropped
    // when this function returns.
    let mut staging = match stage::stage_headers(&base, &mut plan) {
        Ok(staging) => staging,
        Err(rejection) => {
            outcome.rejections.push(rejection);
            outcome.decls = plan.into_outcomes();
            return outcome;
        }
    };

    // PHASE 4 + 5 — bodies in dependency order, registered into an environment
    // that has never held a header; then cycle classification for whatever
    // could not be scheduled.
    let mut publish_env = base;
    let body_rejections =
        publish::elaborate_bodies(&mut staging, &mut publish_env, &mut plan, options);
    outcome.rejections.extend(body_rejections);

    // PHASE 6 — the audit runs BEFORE the caller's environment is advanced.
    let issues = publish::audit(&publish_env, &plan);
    // The tripwire, mechanism 4. This is UNCONDITIONAL: a staged header in the
    // authoritative environment refuses the commit whatever the atomicity mode
    // says, because "register the good part" is not a meaningful response to
    // "the two environments got merged". It is unreachable by construction; if
    // a refactor ever reaches it, it must fail loudly rather than publish.
    let staged_leak = issues
        .iter()
        .any(|issue| matches!(issue, PublishAuditIssue::StagedHeaderInPublishEnv { .. }));
    debug_assert!(
        !staged_leak,
        "a provisional header reached the authoritative environment: {:?}",
        publish_env.staged_header_names()
    );
    if !issues.is_empty() {
        outcome
            .rejections
            .push(BatchRejection::PublishAudit { issues });
    }

    let refused = staged_leak
        || !outcome.rejections.is_empty()
        || plan
            .nodes
            .iter()
            .any(|n| matches!(n.status, plan::NodeStatus::Refused(_)));

    let trailing = std::mem::take(&mut plan.trailing_directives);
    outcome.decls = plan.into_outcomes();

    match options.atomicity {
        _ if staged_leak => outcome.committed = false,
        BatchAtomicity::AllOrNothing if refused => {
            // `env` is untouched: nothing was ever written to it, only to the
            // clones this function owns. The staging environment is dropped
            // here, with every header still in it and nothing citable escaping.
            outcome.committed = false;
        }
        _ => {
            // The caller resumes with the `open` / `export` aliases the source
            // established, expanded against the environment that now holds the
            // batch's declarations — not against the one that existed while the
            // directives were being read.
            let resumed =
                exec::replay_trailing(&publish_env, file_ctx.namespace_state(), &trailing);
            *file_ctx.namespace_state_mut() = resumed;
            *env = publish_env;
            outcome.committed = true;
        }
    }
    outcome
}

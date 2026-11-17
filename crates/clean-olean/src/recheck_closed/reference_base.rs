// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR1 slice 1: a [`ReferenceKernel`] whose base is pinned Lean `Init`, every
//! declaration of it re-checked THROUGH the entry.
//!
//! KR0's entry took its base by value and checked only provenance stamps and
//! expression forms: a `FullKernelCheck` stamp earned under `Extended` or
//! `Classical`, or on a false axiom, passed (R107, "Not fenced until KR1").
//! [`reference_base_closed`] closes that for a base built from `.olean`s: it
//! starts the entry EMPTY and drives the dependency-closed replay of
//! [`super::recheck_closed`] — the same planner, the same order, the same
//! extension-binding gate, the same recursor and ι-rule comparisons — with
//! every admission going through the entry itself:
//!
//! * an ordinary constant through [`ReferenceKernel::add_checked`] (the
//!   pre-kernel form, citation and tripwire walk, then `add_decl` in
//!   `LeanReference` / `Constructive`);
//! * an inductive family through [`ReferenceKernel::add_inductive_checked`]
//!   (`add_inductive_core`; Clean's `add_inductive` is refused);
//! * the quotient primitives through [`ReferenceKernel::add_quot_checked`]
//!   (Lean's `add_quot`, after `Eq` was admitted through the entry).
//!
//! Nothing is served lazily and nothing is taken from the imported
//! environment as given: the entry's environment holds exactly what the
//! entry admitted. A declaration the entry refuses is reported (typed, in
//! [`ReferenceBase::entry_refusals`], and as a replay refusal), and every
//! unit that depends on it is refused in turn.

use std::collections::BTreeSet;

use clean_kernel::env::{Declaration, Environment, Reducibility};
use clean_kernel::inductive::InductiveDecl;
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, ReferenceRefusal};

use super::drive::ReplayTarget;
use super::{run_closed, ClosedRecheckOptions, ClosedRecheckReport};

/// A reference entry built from a closed replay, with what the replay
/// measured.
#[derive(Debug)]
pub struct ReferenceBase {
    /// The replay's report: the same shape and refusals as
    /// [`super::recheck_closed`]'s.
    pub report: ClosedRecheckReport,
    /// Each refusal the ENTRY issued (as opposed to the replay's own gates),
    /// typed, with the unit it refused.
    pub entry_refusals: Vec<(String, ReferenceRefusal)>,
    /// Exactly the names admitted through the entry.
    pub admitted: BTreeSet<Name>,
    kernel: ReferenceKernel,
    // Original completion is private authority; public diagnostics may be
    // edited by a caller and cannot turn a partial replay into a complete one.
    // Retain the genuine original failure report so even forged diagnostics
    // cannot make an Err carry a misleading successful verdict.
    completion_failure: Option<Box<ClosedRecheckReport>>,
}

impl ReferenceBase {
    /// The entry, but only when the replay refused nothing and its by-name
    /// keys were gated against the pinned table; otherwise the report.
    ///
    /// # Errors
    ///
    /// The report, when the replay did not pass or was not pinned.
    #[allow(clippy::result_large_err)]
    pub fn into_kernel(self) -> Result<ReferenceKernel, ClosedRecheckReport> {
        if let Some(original_failure) = self.completion_failure {
            return Err(*original_failure);
        }
        if self.report.passed()
            && self.report.extension_bindings_pinned
            && self.entry_refusals.is_empty()
        {
            Ok(self.kernel)
        } else {
            Err(self.report)
        }
    }

    /// The entry as built so far, whatever the report says (every constant in
    /// it was admitted through the entry; a refused unit is simply absent).
    #[must_use]
    pub fn kernel(&self) -> &ReferenceKernel {
        &self.kernel
    }
}

/// The admissions of [`super::drive::replay_in_order`], routed through the
/// entry.
struct EntryTarget {
    kernel: ReferenceKernel,
    refused: Vec<(String, ReferenceRefusal)>,
}

impl EntryTarget {
    fn refuse(&mut self, unit: String, refusal: ReferenceRefusal) -> String {
        let message = format!("reference entry: {refusal}");
        self.refused.push((unit, refusal));
        message
    }
}

impl ReplayTarget for EntryTarget {
    fn env(&self) -> &Environment {
        self.kernel.environment()
    }

    fn admit_decl(&mut self, decl: Declaration, hint: Option<Reducibility>) -> Result<(), String> {
        let unit = match &decl {
            Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Axiom { name, .. } => name.to_string(),
        };
        let result = match hint {
            Some(hint) => self.kernel.add_checked_with_reducibility(decl, hint),
            None => self.kernel.add_checked(decl),
        };
        match result {
            Ok(_token) => Ok(()),
            Err(refusal) => Err(self.refuse(unit, refusal)),
        }
    }

    fn admit_family(&mut self, decl: InductiveDecl, clean_built: bool) -> Result<(), String> {
        let unit = decl
            .types
            .first()
            .map(|t| format!("inductive {}", t.name))
            .unwrap_or_default();
        if clean_built {
            return Err(format!(
                "reference entry: {unit} carries Clean-built recursors; the entry admits a family \
                 only through Lean's add_inductive_core"
            ));
        }
        match self.kernel.add_inductive_checked(decl) {
            Ok(_token) => Ok(()),
            Err(refusal) => Err(self.refuse(unit, refusal)),
        }
    }

    fn install_quot(&mut self) -> Result<(), String> {
        match self.kernel.add_quot_checked() {
            Ok(_token) => Ok(()),
            Err(refusal) => Err(self.refuse("Quot".to_string(), refusal)),
        }
    }
}

/// Build a [`ReferenceKernel`] over the dependency-closed cone of `targets`
/// in `env` (typically a `.olean` import of pinned Lean `Init`), every
/// member re-checked through the entry (module docs).
///
/// # Errors
///
/// The entry's own refusal of its empty starting base (it carries only the
/// heartbeat budget, so this does not happen in practice). Refusals of cone
/// members are not errors: they are in the returned report, and
/// [`ReferenceBase::into_kernel`] withholds the entry when there are any.
pub fn reference_base_closed(
    env: &Environment,
    targets: &BTreeSet<Name>,
    options: &ClosedRecheckOptions,
) -> Result<ReferenceBase, ReferenceRefusal> {
    let mut start = Environment::default();
    start.set_option(
        "maxHeartbeats".to_string(),
        Some(options.max_heartbeats.to_string()),
    );
    let mut target = EntryTarget {
        kernel: ReferenceKernel::new(start)?,
        refused: Vec::new(),
    };
    let (report, admitted) = run_closed(env, targets, options, &mut target);
    let completion_failure =
        if report.passed() && report.extension_bindings_pinned && target.refused.is_empty() {
            None
        } else {
            Some(Box::new(report.clone()))
        };
    Ok(ReferenceBase {
        report,
        entry_refusals: target.refused,
        admitted,
        kernel: target.kernel,
        completion_failure,
    })
}

/// Untrusted ordinary advice emitted by the actual observing replay caller.
/// Neither variant is a checker acceptance or changes the reference verdict.
#[cfg(feature = "kcheck-trace")]
#[derive(Debug, serde::Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum AdviceCandidateObservation {
    /// Candidate bytes still require replay against the original declaration.
    Candidate {
        /// Untrusted supplied checker depth, independent of the model bound N.
        depth: u64,
        /// A single declaration's token bytes, without an outer frame prefix.
        bytes: Vec<u8>,
    },
    /// No partial candidate is exported on search exhaustion or coverage failure.
    Refused {
        /// Actual candidate-search refusal, distinct from diagnostic tracing.
        reason: String,
    },
}

/// One C4 observation, in the reference entry's actual replay order.
#[cfg(feature = "kcheck-trace")]
#[derive(Debug, serde::Serialize)]
pub struct TraceObservation {
    /// Primary name of the ordinary declaration or atomic block.
    pub name: String,
    /// All names in an atomic inductive/quotient admission.
    pub members: Vec<String>,
    /// Ordinary declaration, inductive block, or quotient primitive block.
    pub kind: String,
    /// Full tracing including the annotated dependency prefix was available.
    pub core_complete: bool,
    /// Explicit tracing refusal, distinct from the reference verdict.
    pub trace_refusal: Option<String>,
    /// Independent reference entry verdict.
    pub reference_accepted: bool,
    /// Ordinary candidate/refusal from this caller; None for atomic blocks.
    /// This is never the diagnostic journal and never an admission verdict.
    pub advice_candidate: Option<AdviceCandidateObservation>,
    /// Candidate advice from the feature-gated tracing journal beside the
    /// fenced reference entry, not from the production checker.
    #[serde(skip)]
    pub advice_frame: Vec<u8>,
    /// Successful-path token count (a partial prefix when tracing refused).
    pub partial_tokens: usize,
    /// Alternative charge with a REFL certificate per identity-walk argument.
    pub uncompressed_spine_tokens: u64,
    /// Tags named as in design section 3.2.
    pub partial_tokens_by_kind: std::collections::BTreeMap<String, u64>,
    /// Beta observations, including speculative paths.
    pub beta: Vec<clean_kernel::kcheck_trace::DomainClass>,
    /// Actual conversion head reductions, in completed beta-comparison order.
    pub beta_conversion_head_steps: Vec<u64>,
    /// Every failed or absent domain pair exposed by the tracer.
    pub domain_problems: Vec<clean_kernel::kcheck_trace::core::DomainProblem>,
    /// Iota major-domain observations, by recursor.
    pub iota: Vec<(String, clean_kernel::kcheck_trace::DomainClass)>,
    /// K major-domain observations, by recursor.
    pub k: Vec<(String, clean_kernel::kcheck_trace::DomainClass)>,
    /// Applications inferAnn had to compare.
    pub infer_ann_comparisons: u64,
    /// Comparisons attributed to eta, proof irrelevance, K and iota.
    pub infer_ann_by_source: std::collections::BTreeMap<String, u64>,
    /// Stored label classes at inferAnn applications, by caller.
    pub infer_ann_classes: Vec<(String, clean_kernel::kcheck_trace::DomainClass)>,
    /// Revision 1/2 call-depth and inference-node census.
    pub volume: clean_kernel::kcheck_trace::core::Volume,
    /// Full recursor/constructor telescope classifications.
    pub spines: Vec<clean_kernel::kcheck_trace::core::SpineComparison>,
    /// Recursor spines originally built with a different head.
    pub recursor_spines_other_head: u64,
    /// Minor-premise beta subclasses.
    pub minor_beta: std::collections::BTreeMap<String, u64>,
    /// Literal expansion attempts declined by canonical-definition admission.
    pub literal_admission_skips: std::collections::BTreeMap<String, u64>,
    /// Canonically admitted literal expansion counts, including conversion.
    pub literal_expansions: std::collections::BTreeMap<String, u64>,
    /// Constructor/recursor level-argument comparisons at iota.
    pub constructor_levels: std::collections::BTreeMap<String, u64>,
    /// Actual head-step work, including speculative conversions.
    pub attempted_head_steps: u64,
    /// Actual existing-kernel operation heartbeats, one fresh profile per comparison.
    pub oracle_conversions: Vec<clean_kernel::kcheck_trace::core::OracleConversion>,
    /// Failed cyclic producer-search branches; no equality answers are cached.
    pub conversion_cycles_cut: u64,
    /// Primitive Nat extension folds, separately named from core rules.
    pub native_nat_steps: std::collections::BTreeMap<String, u64>,
    /// Applications the existing kernel leaves stuck rather than unary grinding.
    pub native_nat_stops: std::collections::BTreeMap<String, u64>,
    /// Earlier untraced entries reannotated locally; these are coverage holes.
    pub reannotated_dependencies: Vec<String>,
}

#[cfg(feature = "kcheck-trace")]
fn observe(
    name: String,
    members: Vec<String>,
    kind: &str,
    tracer: &mut clean_kernel::kcheck_trace::core::CoreTracer<'_>,
    refusal: Option<String>,
) -> TraceObservation {
    use clean_kernel::kcheck_trace::Token;
    tracer.finish_journal();
    let mut counts = std::collections::BTreeMap::new();
    for token in tracer.journal.tokens() {
        let tag = match token {
            Token::Depth(_) => "DEPTH",
            Token::Iota => "IOTA",
            Token::K => "K",
            Token::SpineRefl(_) => "SPINE_REFL",
            Token::SpineCerts(_) => "SPINE",
            Token::Refl => "REFL",
            Token::Sort => "SORT",
            Token::Const => "CONST",
            Token::App => "APP",
            Token::Lam => "LAM",
            Token::Pi => "PI",
            Token::CoreL(_) => "CORE_L",
            Token::CoreR(_) => "CORE_R",
            Token::Dom => "DOM",
            Token::DeltaL => "DELTA_L",
            Token::DeltaR => "DELTA_R",
            Token::DeltaBoth => "DELTA_BOTH",
            Token::EtaL => "ETA_L",
            Token::EtaR => "ETA_R",
            Token::Irrel => "IRREL",
            Token::Memo(_) => "MEMO",
            Token::Stop => "STOP",
        };
        *counts.entry(tag.to_string()).or_insert(0) += 1;
    }
    TraceObservation {
        name,
        members,
        kind: kind.into(),
        core_complete: refusal.is_none() && tracer.reannotated_dependencies.is_empty(),
        trace_refusal: refusal,
        reference_accepted: false,
        advice_candidate: None,
        advice_frame: clean_kernel::kcheck_trace::advice::encode_frame(tracer.journal.tokens()),
        partial_tokens: tracer.journal.tokens().len(),
        uncompressed_spine_tokens: tracer.journal.tokens().len() as u64
            + tracer
                .journal
                .tokens()
                .iter()
                .map(|t| match t {
                    Token::SpineRefl(n) => *n,
                    _ => 0,
                })
                .sum::<u64>(),
        partial_tokens_by_kind: counts,
        beta: std::mem::take(&mut tracer.beta_classes),
        beta_conversion_head_steps: std::mem::take(&mut tracer.beta_conversion_head_steps),
        domain_problems: std::mem::take(&mut tracer.domain_problems),
        iota: std::mem::take(&mut tracer.iota_classes),
        k: std::mem::take(&mut tracer.k_classes),
        infer_ann_comparisons: tracer.infer_ann_comparisons,
        infer_ann_by_source: std::mem::take(&mut tracer.infer_ann_by_source),
        infer_ann_classes: std::mem::take(&mut tracer.infer_ann_classes),
        volume: std::mem::take(&mut tracer.volume),
        spines: std::mem::take(&mut tracer.spine_comparisons),
        recursor_spines_other_head: tracer.recursor_spines_other_head,
        minor_beta: std::mem::take(&mut tracer.minor_beta),
        literal_admission_skips: std::mem::take(&mut tracer.literal_admission_skips),
        literal_expansions: std::mem::take(&mut tracer.literal_expansions),
        constructor_levels: std::mem::take(&mut tracer.constructor_levels),
        attempted_head_steps: tracer.attempted_head_steps,
        oracle_conversions: std::mem::take(&mut tracer.oracle_conversions),
        conversion_cycles_cut: tracer.conversion_cycles_cut,
        native_nat_steps: std::mem::take(&mut tracer.native_nat_steps),
        native_nat_stops: std::mem::take(&mut tracer.native_nat_stops),
        reannotated_dependencies: std::mem::take(&mut tracer.reannotated_dependencies)
            .into_iter()
            .collect(),
    }
}

#[cfg(feature = "kcheck-trace")]
struct TracingTarget<'a> {
    entry: EntryTarget,
    observation_count: usize,
    observer: &'a mut dyn FnMut(&TraceObservation),
    operations: u64,
    labelled: clean_kernel::kcheck_trace::core::LabelledEnvironment,
    checkpoint: Option<std::io::BufWriter<std::fs::File>>,
    checkpoint_error: Option<String>,
}

#[cfg(feature = "kcheck-trace")]
impl TracingTarget<'_> {
    fn record(&mut self, row: TraceObservation) {
        use std::io::Write;
        if self.checkpoint_error.is_none() {
            if let Some(writer) = &mut self.checkpoint {
                let result = serde_json::to_writer(&mut *writer, &row)
                    .map_err(|e| e.to_string())
                    .and_then(|()| writer.write_all(b"\n").map_err(|e| e.to_string()))
                    .and_then(|()| writer.flush().map_err(|e| e.to_string()));
                if let Err(error) = result {
                    self.checkpoint_error = Some(error);
                }
            }
        }
        if self.observation_count.is_multiple_of(100) {
            eprintln!(
                "C4 tracing row {}: {} complete={} refusal={:?}",
                self.observation_count, row.name, row.core_complete, row.trace_refusal
            );
        }
        (self.observer)(&row);
        self.observation_count += 1;
    }

    fn trace_new_group(&mut self, name: String, kind: &str, before: BTreeSet<Name>) {
        use clean_kernel::kcheck_trace::core::CoreTracer;
        let names: Vec<_> = self
            .entry
            .env()
            .constants()
            .map(|c| c.name.clone())
            .filter(|n| !before.contains(n))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let mut tracer = CoreTracer::with_labelled_environment(
            self.entry.env(),
            &self.labelled,
            self.operations,
        );
        let annotation = tracer.annotate_group(&names);
        let row = observe(
            name,
            names.iter().map(Name::to_unambiguous_string).collect(),
            kind,
            &mut tracer,
            annotation.as_ref().err().map(ToString::to_string),
        );
        drop(tracer);
        let mut row = row;
        row.reference_accepted = true;
        if row.core_complete {
            if let Ok(annotation) = annotation {
                self.labelled.extend(annotation);
            }
        }
        self.record(row);
    }
}

#[cfg(feature = "kcheck-trace")]
impl ReplayTarget for TracingTarget<'_> {
    fn env(&self) -> &Environment {
        self.entry.env()
    }
    fn admit_decl(&mut self, decl: Declaration, hint: Option<Reducibility>) -> Result<(), String> {
        use clean_kernel::kcheck_trace::core::CoreTracer;
        let name = match &decl {
            Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Axiom { name, .. } => name.clone(),
        };
        let mut tracer = CoreTracer::with_labelled_environment(
            self.entry.env(),
            &self.labelled,
            self.operations,
        );
        let annotation = tracer.declaration_labelled(&decl);
        let row = observe(
            name.to_unambiguous_string(),
            vec![name.to_unambiguous_string()],
            "ordinary",
            &mut tracer,
            annotation.as_ref().err().map(ToString::to_string),
        );
        drop(tracer);
        // Keep candidate search separate from the diagnostic journal and from
        // admission. Its conservative supplied depth is an untrusted proposal,
        // not an interpretation/model bound or a completeness measurement.
        let candidate = clean_kernel::kcheck_trace::core::advice::produce_ordinary_with_labelled(
            self.entry.env(),
            &self.labelled,
            &decl,
            self.operations,
            self.operations,
        );
        let advice_candidate = match candidate {
            Ok(candidate) => AdviceCandidateObservation::Candidate {
                depth: self.operations,
                bytes: candidate.bytes,
            },
            Err(error) => AdviceCandidateObservation::Refused {
                reason: error.to_string(),
            },
        };
        let result = self.entry.admit_decl(decl, hint);
        let mut row = row;
        row.advice_candidate = Some(advice_candidate);
        row.reference_accepted = result.is_ok();
        if row.core_complete && row.reference_accepted {
            if let Ok(annotation) = annotation {
                self.labelled.insert(name, annotation);
            }
        }
        self.record(row);
        result
    }
    fn admit_family(&mut self, decl: InductiveDecl, clean_built: bool) -> Result<(), String> {
        let before = self
            .entry
            .env()
            .constants()
            .map(|c| c.name.clone())
            .collect();
        let name = decl.types.first().map_or_else(
            || "<empty inductive>".into(),
            |t| format!("inductive {}", t.name),
        );
        let result = self.entry.admit_family(decl, clean_built);
        if result.is_ok() {
            self.trace_new_group(name, "inductive", before);
        }
        result
    }
    fn install_quot(&mut self) -> Result<(), String> {
        let before = self
            .entry
            .env()
            .constants()
            .map(|c| c.name.clone())
            .collect();
        let result = self.entry.install_quot();
        if result.is_ok() {
            self.trace_new_group("Quot".into(), "quotient", before);
        }
        result
    }
}

/// A separately constructed observing replay. It never changes admission policy
/// or treats a tracing result as authority. Its persistent table contains only
/// annotated syntax admitted by both tracers; equation caches remain absent.
/// Each completed observation is checkpointed and borrowed by the observer,
/// then dropped, so event history does not accumulate across declarations.
#[cfg(feature = "kcheck-trace")]
pub fn reference_base_core_tracing(
    env: &Environment,
    targets: &BTreeSet<Name>,
    options: &ClosedRecheckOptions,
    operations: u64,
    checkpoint: Option<&std::path::Path>,
    observer: &mut dyn FnMut(&TraceObservation),
) -> Result<ClosedRecheckReport, Box<dyn std::error::Error>> {
    let mut start = Environment::default();
    start.set_option(
        "maxHeartbeats".into(),
        Some(options.max_heartbeats.to_string()),
    );
    let mut target = TracingTarget {
        entry: EntryTarget {
            kernel: ReferenceKernel::new(start)?,
            refused: vec![],
        },
        observation_count: 0,
        observer,
        operations,
        labelled: Default::default(),
        checkpoint: checkpoint
            .map(std::fs::File::create)
            .transpose()?
            .map(std::io::BufWriter::new),
        checkpoint_error: None,
    };
    let (report, _) = run_closed(env, targets, options, &mut target);
    if let Some(error) = target.checkpoint_error {
        return Err(format!("tracing checkpoint: {error}").into());
    }
    Ok(report)
}

/// Ordinary fenced replay with progress messages, constructed solely for the
/// experiment. The ordinary entry and its reduction configuration are unchanged.
#[cfg(feature = "kcheck-trace")]
pub fn reference_base_progress(
    env: &Environment,
    targets: &BTreeSet<Name>,
    options: &ClosedRecheckOptions,
) -> Result<ClosedRecheckReport, ReferenceRefusal> {
    struct Progress {
        entry: EntryTarget,
        count: usize,
    }
    impl Progress {
        fn next(&mut self, name: &str) {
            if self.count.is_multiple_of(100) {
                eprintln!("C4 ordinary row {}: {name}", self.count);
            }
            self.count += 1;
        }
    }
    impl ReplayTarget for Progress {
        fn env(&self) -> &Environment {
            self.entry.env()
        }
        fn admit_decl(
            &mut self,
            decl: Declaration,
            hint: Option<Reducibility>,
        ) -> Result<(), String> {
            let name = match &decl {
                Declaration::Definition { name, .. }
                | Declaration::Theorem { name, .. }
                | Declaration::Opaque { name, .. }
                | Declaration::Axiom { name, .. } => name.to_unambiguous_string(),
            };
            self.next(&name);
            self.entry.admit_decl(decl, hint)
        }
        fn admit_family(&mut self, decl: InductiveDecl, clean_built: bool) -> Result<(), String> {
            self.next(&format!(
                "inductive {:?}",
                decl.types.first().map(|t| &t.name)
            ));
            self.entry.admit_family(decl, clean_built)
        }
        fn install_quot(&mut self) -> Result<(), String> {
            self.next("Quot");
            self.entry.install_quot()
        }
    }
    let mut start = Environment::default();
    start.set_option(
        "maxHeartbeats".into(),
        Some(options.max_heartbeats.to_string()),
    );
    let mut target = Progress {
        entry: EntryTarget {
            kernel: ReferenceKernel::new(start)?,
            refused: vec![],
        },
        count: 0,
    };
    let (report, _) = run_closed(env, targets, options, &mut target);
    Ok(report)
}

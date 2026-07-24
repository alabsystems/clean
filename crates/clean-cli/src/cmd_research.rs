// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean research ...` command group (#3674).

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clap::{Args, Subcommand};
use clean_auto::cli::{
    rank_premise_goal, PremiseClassification, PremiseEnvironment, RankedPremise,
};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_verify::proof_artifact_v1::{
    CertificatePayloadEncoding, ProofArtifactV1, ProofArtifactV1Error, PROOF_ARTIFACT_V1_VERSION,
};
use clean_verify::research_manifest::{
    load_research_manifest, validate_research_manifest, PromotionGate, ResearchArtifactState,
    ResearchManifest, ResearchManifestError, ResearchManifestItem, ResearchStatus,
    DEFAULT_RESEARCH_MANIFEST_PATH,
};
use serde::Serialize;

const KEY_ENTRY_LIMIT: usize = 12;

/// Verbs under `clean research`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum ResearchCommands {
    /// Print the research program status dashboard.
    Status(ResearchStatusArgs),
    /// Validate a proof artifact JSON envelope.
    ValidateArtifact(ResearchValidateArtifactArgs),
    /// Run the Gamma-Crown proof-assistance benchmark.
    ProofAssistBench(ResearchProofAssistBenchArgs),
}

/// Arguments accepted by `clean research status`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ResearchStatusArgs {
    /// Emit JSON instead of a compact human-readable dashboard.
    #[arg(long)]
    pub json: bool,
    /// Path to the research program manifest.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_RESEARCH_MANIFEST_PATH)]
    pub manifest: PathBuf,
}

/// Arguments accepted by `clean research validate-artifact`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ResearchValidateArtifactArgs {
    /// Path to a proof-artifact-v1 JSON file.
    pub path: PathBuf,
    /// Emit JSON instead of a compact human-readable summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean research proof-assist-bench`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ResearchProofAssistBenchArgs {
    /// Emit JSON instead of a compact human-readable report.
    #[arg(long)]
    pub json: bool,
    /// Number of ranked premise candidates to keep per proof packet.
    #[arg(long, value_name = "N", default_value_t = 5)]
    pub limit: usize,
}

/// Errors surfaced by `clean research`.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ResearchError {
    /// Manifest loading or structural validation failed.
    #[error("research manifest error at {path}: {source}")]
    Manifest {
        path: PathBuf,
        source: ResearchManifestError,
    },
    /// A guarded demasquerade-sensitive item was promoted without the trust
    /// report API needed to justify that promotion.
    #[error(
        "research manifest marks guarded item `{id}` as KernelProved; \
         C004/C006/T60 require trust-report agreement before promotion"
    )]
    GuardedPromotion { id: String },
    /// Serializing the report failed.
    #[error("failed to serialize research JSON report: {0}")]
    Serialize(#[from] serde_json::Error),
    /// Reading a proof artifact file failed.
    #[error("failed to read proof artifact at {path}: {source}")]
    ArtifactRead { path: PathBuf, source: io::Error },
    /// Parsing or validating a proof artifact failed.
    #[error("invalid proof artifact at {path}: {source}")]
    Artifact {
        path: PathBuf,
        source: ProofArtifactV1Error,
    },
    /// clean premise ranking failed for a proof packet.
    #[error("proof-assist premise ranking failed for packet `{id}`: {source}")]
    ProofAssist {
        id: &'static str,
        source: clean_auto::cli::PremiseCliError,
    },
    /// Writing output failed.
    #[error("failed to write research output: {0}")]
    Io(#[from] io::Error),
}

/// Dispatch entry point for `clean research`.
pub(crate) fn handle_research_command(command: ResearchCommands) -> Result<(), ResearchError> {
    match command {
        ResearchCommands::Status(args) => run_status(args),
        ResearchCommands::ValidateArtifact(args) => run_validate_artifact(args),
        ResearchCommands::ProofAssistBench(args) => run_proof_assist_bench(args),
    }
}

fn run_status(args: ResearchStatusArgs) -> Result<(), ResearchError> {
    let manifest_path = resolve_manifest_path(&args.manifest);
    let manifest =
        load_research_manifest(&manifest_path).map_err(|source| ResearchError::Manifest {
            path: manifest_path.clone(),
            source,
        })?;
    validate_manifest_for_cli(&manifest_path, &manifest)?;
    let report = ResearchStatusReport::from_manifest(&manifest_path, &manifest);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_human(&mut out, &report)?;
    }
    Ok(())
}

fn run_validate_artifact(args: ResearchValidateArtifactArgs) -> Result<(), ResearchError> {
    let report = load_artifact_report(&args.path)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_artifact_human(&mut out, &report)?;
    }
    Ok(())
}

fn run_proof_assist_bench(args: ResearchProofAssistBenchArgs) -> Result<(), ResearchError> {
    let report = ProofAssistBenchReport::run(args.limit)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_proof_assist_human(&mut out, &report)?;
    }
    Ok(())
}

fn load_artifact_report(path: &Path) -> Result<ProofArtifactReport, ResearchError> {
    let json = std::fs::read_to_string(path).map_err(|source| ResearchError::ArtifactRead {
        path: path.to_owned(),
        source,
    })?;
    let artifact = ProofArtifactV1::from_json(&json).map_err(|source| ResearchError::Artifact {
        path: path.to_owned(),
        source,
    })?;
    Ok(ProofArtifactReport::from_artifact(path, &artifact))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
enum ProofAssistProgramPhase {
    Original,
    StructuralDichotomy,
}

impl ProofAssistProgramPhase {
    fn as_str(self) -> &'static str {
        match self {
            Self::Original => "original",
            Self::StructuralDichotomy => "structural-dichotomy",
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ProofAssistPacket {
    id: &'static str,
    phase: ProofAssistProgramPhase,
    title: &'static str,
    goal: &'static str,
    clean_target: &'static str,
    solver_impact: &'static str,
}

const PROOF_ASSIST_PACKETS: &[ProofAssistPacket] = &[
    ProofAssistPacket {
        id: "C007",
        phase: ProofAssistProgramPhase::Original,
        title: "Streaming Farkas certificate composition",
        goal: "NNVerify C007 Farkas certificate composition entailment transitivity ExternalEntailmentCert chain",
        clean_target: "Promote replayable block certificates to a kernel-checked composition theorem.",
        solver_impact: "Reusable proof-carrying bounds for blockwise GPU-BaB pruning.",
    },
    ProofAssistPacket {
        id: "GC_CERT_FARKAS",
        phase: ProofAssistProgramPhase::Original,
        title: "Gamma-Crown Farkas artifact replay",
        goal: "ExternalFarkasCert nonnegative multipliers linear constraints interval bounds certificate replay",
        clean_target: "Replay real Gamma-Crown Farkas multipliers through clean artifact validation.",
        solver_impact: "Trust cached linear bounds without re-running expensive propagation.",
    },
    ProofAssistPacket {
        id: "C004",
        phase: ProofAssistProgramPhase::Original,
        title: "CROWN through LayerNorm degeneracy",
        goal: "NNVerify C004 Crown LayerNorm IBP bridge backward bound equality faithful carrier",
        clean_target: "Replace guarded axioms with a faithful carrier theorem or weaken the statement.",
        solver_impact: "Choose IBP/blockwise domains when LayerNorm destroys useful CROWN structure.",
    },
    ProofAssistPacket {
        id: "C006",
        phase: ProofAssistProgramPhase::Original,
        title: "Blockwise CROWN equivalence",
        goal: "NNVerify C006 blockwise CROWN equivalence monolithic CROWN compose blocks",
        clean_target: "Prove the carrier-correct blockwise equivalence or demote to a conditional theorem.",
        solver_impact: "Run cheaper blockwise verification when equivalence hypotheses are detected.",
    },
    ProofAssistPacket {
        id: "C010",
        phase: ProofAssistProgramPhase::Original,
        title: "Zonotope-CROWN linear-region equivalence",
        goal: "NNVerify C010 Zonotope CROWN linear region exact affine equivalence fixed activation pattern",
        clean_target: "State and prove the exact linear-region domain equivalence with explicit hypotheses.",
        solver_impact: "Switch to the cheaper abstract domain when the linear-region test passes.",
    },
    ProofAssistPacket {
        id: "C012",
        phase: ProofAssistProgramPhase::Original,
        title: "ReLU stability proof packet",
        goal: "NNVerify C012 ReLU stability pattern certificate active inactive branching pruning",
        clean_target: "Close solver-facing ReLU stability lemmas with exact branch-pruning preconditions.",
        solver_impact: "Reduce GPU-BaB splits by certifying stable activations early.",
    },
    ProofAssistPacket {
        id: "DICHOTOMY_WIDTH",
        phase: ProofAssistProgramPhase::StructuralDichotomy,
        title: "Bounded interaction width gives polynomial certificates",
        goal: "piecewise linear neural network activation region interaction graph bounded treewidth rank polynomial certificate Farkas BaB",
        clean_target: "Define activation-region interaction width and prove polynomial-size compositional certificates.",
        solver_impact: "Detect low-width networks and route them to proof-carrying dynamic programming.",
    },
    ProofAssistPacket {
        id: "LOWER_BOUND_EXP",
        phase: ProofAssistProgramPhase::StructuralDichotomy,
        title: "Unbounded interaction width forces exponential certificates",
        goal: "CROWN IBP BaB LP Farkas certificate proof complexity exponential lower bound activation interaction graph",
        clean_target: "Formalize the verifier proof system and prove an exponential lower-bound family.",
        solver_impact: "Avoid doomed certificate strategies and trigger alternative search policies.",
    },
    ProofAssistPacket {
        id: "CERT_CALCULUS",
        phase: ProofAssistProgramPhase::StructuralDichotomy,
        title: "Compositional certificate calculus",
        goal: "unifying certificate calculus CROWN zonotope star set LP dual Farkas BaB pruning soundness completeness",
        clean_target: "Show existing verifier domains are instances of one compositional certificate calculus.",
        solver_impact: "Normalize proof artifacts across domains and compose/cache them uniformly.",
    },
];

#[derive(Debug, Serialize)]
struct ProofAssistBenchReport {
    schema_version: &'static str,
    environment: &'static str,
    limit: usize,
    packet_count: usize,
    rows: Vec<ProofAssistBenchRow>,
    artifact_checks: Vec<ProofAssistArtifactCheck>,
}

impl ProofAssistBenchReport {
    fn run(limit: usize) -> Result<Self, ResearchError> {
        let mut rows = Vec::with_capacity(PROOF_ASSIST_PACKETS.len());
        for packet in PROOF_ASSIST_PACKETS {
            let ranked = rank_premise_goal(
                packet.goal,
                PremiseEnvironment::GammaCrown,
                PremiseClassification::All,
                limit,
            )
            .map_err(|source| ResearchError::ProofAssist {
                id: packet.id,
                source,
            })?;
            rows.push(ProofAssistBenchRow::from_ranked(packet, ranked));
        }

        Ok(Self {
            schema_version: "clean-proof-assist-bench-v1",
            environment: "gamma-crown",
            limit,
            packet_count: rows.len(),
            rows,
            artifact_checks: proof_assist_artifact_checks(),
        })
    }
}

#[derive(Debug, Serialize)]
struct ProofAssistBenchRow {
    id: &'static str,
    phase: &'static str,
    title: &'static str,
    goal: &'static str,
    clean_target: &'static str,
    solver_impact: &'static str,
    candidate_count: usize,
    top_candidates: Vec<ProofAssistCandidate>,
}

impl ProofAssistBenchRow {
    fn from_ranked(packet: &ProofAssistPacket, ranked: Vec<RankedPremise>) -> Self {
        Self {
            id: packet.id,
            phase: packet.phase.as_str(),
            title: packet.title,
            goal: packet.goal,
            clean_target: packet.clean_target,
            solver_impact: packet.solver_impact,
            candidate_count: ranked.len(),
            top_candidates: ranked.into_iter().map(ProofAssistCandidate::from).collect(),
        }
    }
}

#[derive(Debug, Serialize)]
struct ProofAssistCandidate {
    name: String,
    kind: String,
    quality: String,
    score: f64,
}

impl From<RankedPremise> for ProofAssistCandidate {
    fn from(candidate: RankedPremise) -> Self {
        Self {
            name: candidate.name,
            kind: candidate.kind,
            quality: candidate.quality,
            score: candidate.score,
        }
    }
}

#[derive(Debug, Serialize)]
struct ProofAssistArtifactCheck {
    path: String,
    status: String,
    source_system: Option<String>,
    artifact_kind: Option<String>,
    certificate_format: Option<String>,
    error: Option<String>,
}

fn proof_assist_artifact_checks() -> Vec<ProofAssistArtifactCheck> {
    [
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_entailment_valid.json",
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json",
    ]
    .into_iter()
    .map(|path| {
        let resolved = resolve_manifest_path(Path::new(path));
        match load_artifact_report(&resolved) {
            Ok(report) => ProofAssistArtifactCheck {
                path: resolved.display().to_string(),
                status: "valid".to_owned(),
                source_system: Some(report.source_system),
                artifact_kind: Some(report.artifact_kind),
                certificate_format: Some(report.certificate_format),
                error: None,
            },
            Err(error) => ProofAssistArtifactCheck {
                path: resolved.display().to_string(),
                status: "invalid".to_owned(),
                source_system: None,
                artifact_kind: None,
                certificate_format: None,
                error: Some(error.to_string()),
            },
        }
    })
    .collect()
}

fn validate_manifest_for_cli(
    path: &Path,
    manifest: &ResearchManifest,
) -> Result<(), ResearchError> {
    validate_research_manifest(manifest).map_err(|source| ResearchError::Manifest {
        path: path.to_owned(),
        source,
    })?;
    for item in &manifest.items {
        if item.status == ResearchStatus::KernelProved
            && item.promotion_gate == PromotionGate::TrustReportAgreement
        {
            return Err(ResearchError::GuardedPromotion {
                id: item.id.clone(),
            });
        }
    }
    Ok(())
}

fn resolve_manifest_path(input: &Path) -> PathBuf {
    if input.is_absolute() || input.exists() {
        return input.to_owned();
    }

    let Ok(cwd) = std::env::current_dir() else {
        return input.to_owned();
    };
    let mut dir: &Path = &cwd;
    loop {
        let candidate = dir.join(input);
        if candidate.is_file() {
            return candidate;
        }
        match dir.parent() {
            Some(parent) => dir = parent,
            None => return input.to_owned(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct ManifestEntry {
    id: String,
    title: String,
    owner_repo: String,
    domain: String,
    family: String,
    status: String,
    status_class: StatusClass,
    artifact_state: String,
    promotion_gate: String,
    summary: String,
    dependency_count: usize,
    evidence_count: usize,
    reference_count: usize,
}

impl From<&ResearchManifestItem> for ManifestEntry {
    fn from(item: &ResearchManifestItem) -> Self {
        Self {
            id: item.id.clone(),
            title: item.title.clone(),
            owner_repo: item.owner_repo.clone(),
            domain: item.domain.clone(),
            family: item.family.clone(),
            status: research_status_label(item.status).to_owned(),
            status_class: item.status.into(),
            artifact_state: artifact_state_label(item.artifact_state).to_owned(),
            promotion_gate: promotion_gate_label(item.promotion_gate).to_owned(),
            summary: item.summary.clone(),
            dependency_count: item.dependencies.len(),
            evidence_count: item.evidence.len(),
            reference_count: item.references.len(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
enum StatusClass {
    Refuted,
    EmpiricalTested,
    ExecutableChecked,
    ProofCarrying,
    KernelProved,
    Axiomatized,
    DerivedPending,
}

impl StatusClass {
    fn as_str(self) -> &'static str {
        match self {
            Self::Refuted => "Refuted",
            Self::EmpiricalTested => "EmpiricalTested",
            Self::ExecutableChecked => "ExecutableChecked",
            Self::ProofCarrying => "ProofCarrying",
            Self::KernelProved => "KernelProved",
            Self::Axiomatized => "Axiomatized",
            Self::DerivedPending => "DerivedPending",
        }
    }
}

impl From<ResearchStatus> for StatusClass {
    fn from(status: ResearchStatus) -> Self {
        match status {
            ResearchStatus::Refuted => Self::Refuted,
            ResearchStatus::EmpiricalTested => Self::EmpiricalTested,
            ResearchStatus::ExecutableChecked => Self::ExecutableChecked,
            ResearchStatus::ProofCarrying => Self::ProofCarrying,
            ResearchStatus::KernelProved => Self::KernelProved,
            ResearchStatus::Axiomatized => Self::Axiomatized,
            ResearchStatus::DerivedPending => Self::DerivedPending,
        }
    }
}

#[derive(Debug, Serialize)]
struct ResearchStatusReport {
    manifest_path: String,
    manifest_schema_version: u32,
    generated_at: String,
    source: String,
    total_entries: usize,
    status_counts: BTreeMap<String, usize>,
    domain_counts: BTreeMap<String, usize>,
    family_counts: BTreeMap<String, usize>,
    key_entries: Vec<ManifestEntry>,
    entries: Vec<ManifestEntry>,
    registries: RegistrySnapshot,
}

impl ResearchStatusReport {
    fn from_manifest(path: &Path, manifest: &ResearchManifest) -> Self {
        let entries: Vec<ManifestEntry> = manifest.items.iter().map(ManifestEntry::from).collect();
        let mut status_counts = BTreeMap::new();
        let mut domain_counts = BTreeMap::new();
        let mut family_counts = BTreeMap::new();
        for entry in &entries {
            *status_counts.entry(entry.status.clone()).or_insert(0) += 1;
            *domain_counts.entry(entry.domain.clone()).or_insert(0) += 1;
            *family_counts.entry(entry.family.clone()).or_insert(0) += 1;
        }

        Self {
            manifest_path: path.display().to_string(),
            manifest_schema_version: manifest.schema_version,
            generated_at: manifest.generated_at.clone(),
            source: manifest.source.clone(),
            total_entries: entries.len(),
            status_counts,
            domain_counts,
            family_counts,
            key_entries: select_key_entries(&entries),
            entries,
            registries: RegistrySnapshot::current(),
        }
    }
}

fn select_key_entries(entries: &[ManifestEntry]) -> Vec<ManifestEntry> {
    let mut selected: Vec<ManifestEntry> = entries
        .iter()
        .filter(|entry| {
            entry.promotion_gate == promotion_gate_label(PromotionGate::TrustReportAgreement)
        })
        .cloned()
        .collect();
    for entry in entries {
        if selected.len() >= KEY_ENTRY_LIMIT {
            break;
        }
        if !selected.iter().any(|existing| existing.id == entry.id) {
            selected.push(entry.clone());
        }
    }
    selected.truncate(KEY_ENTRY_LIMIT);
    selected
}

#[derive(Debug, Serialize)]
struct ProofArtifactReport {
    path: String,
    schema_version: String,
    canonical_version: &'static str,
    producer_repo: String,
    producer_commit: String,
    source_system: String,
    artifact_kind: String,
    problem_hash: String,
    model_hash: String,
    proof_hash: String,
    verifier_constant_count: usize,
    metadata_count: usize,
    certificate_format: String,
    certificate_encoding: &'static str,
    validation_status: &'static str,
}

impl ProofArtifactReport {
    fn from_artifact(path: &Path, artifact: &ProofArtifactV1) -> Self {
        Self {
            path: path.display().to_string(),
            schema_version: artifact.version.clone(),
            canonical_version: PROOF_ARTIFACT_V1_VERSION,
            producer_repo: artifact.producer.repo.clone(),
            producer_commit: artifact.producer.commit.clone(),
            source_system: artifact.source_system.clone(),
            artifact_kind: artifact.artifact_kind.clone(),
            problem_hash: artifact.problem_hash.clone(),
            model_hash: artifact.model_hash.clone(),
            proof_hash: artifact.proof_hash.clone(),
            verifier_constant_count: artifact.verifier_constants.len(),
            metadata_count: artifact.metadata.len(),
            certificate_format: artifact.certificate.format.clone(),
            certificate_encoding: certificate_encoding_label(artifact.certificate.encoding),
            validation_status: "valid",
        }
    }
}

fn certificate_encoding_label(encoding: CertificatePayloadEncoding) -> &'static str {
    match encoding {
        CertificatePayloadEncoding::Json => "json",
        CertificatePayloadEncoding::Base64 => "base64",
        CertificatePayloadEncoding::Hex => "hex",
        CertificatePayloadEncoding::Text => "text",
    }
}

#[derive(Debug, Serialize)]
struct RegistrySnapshot {
    proof_library: ProofLibrarySnapshot,
    sat_frontier: SatFrontierSnapshot,
    gamma_crown: GammaCrownSnapshot,
}

impl RegistrySnapshot {
    fn current() -> Self {
        Self {
            proof_library: ProofLibrarySnapshot::current(),
            sat_frontier: SatFrontierSnapshot::current(),
            gamma_crown: GammaCrownSnapshot::current(),
        }
    }
}

#[derive(Debug, Serialize)]
struct ProofLibrarySnapshot {
    total_proofs: usize,
    sample_properties: Vec<String>,
}

impl ProofLibrarySnapshot {
    fn current() -> Self {
        let library = clean_verify::ProofLibrary::new();
        let mut names: Vec<String> = library.all_proofs().map(|(name, _)| name.clone()).collect();
        names.sort();
        let total_proofs = names.len();
        names.truncate(8);
        Self {
            total_proofs,
            sample_properties: names,
        }
    }
}

#[derive(Debug, Serialize)]
struct SatFrontierSnapshot {
    total_entries: usize,
    status_counts: BTreeMap<String, usize>,
    entries: Vec<SatFrontierEntry>,
}

#[derive(Debug, Serialize)]
struct SatFrontierEntry {
    id: &'static str,
    description: &'static str,
    status: &'static str,
}

impl SatFrontierSnapshot {
    fn current() -> Self {
        let entries: Vec<SatFrontierEntry> = clean_verify::sat_verify::frontier::all_entries()
            .into_iter()
            .map(|entry| SatFrontierEntry {
                id: entry.id,
                description: entry.description,
                status: proof_status_label(entry.status),
            })
            .collect();
        let mut status_counts = BTreeMap::new();
        for entry in &entries {
            *status_counts.entry(entry.status.to_owned()).or_insert(0) += 1;
        }
        Self {
            total_entries: entries.len(),
            status_counts,
            entries,
        }
    }
}

#[derive(Debug, Serialize)]
struct GammaCrownSnapshot {
    total_conjectures: usize,
    key_conjectures: Vec<GammaCrownEntry>,
}

#[derive(Debug, Serialize)]
struct GammaCrownEntry {
    id: &'static str,
    description: &'static str,
}

impl GammaCrownSnapshot {
    fn current() -> Self {
        use clean_kernel::env::gamma_crown_verify::{conjecture_description, CONJECTURE_IDS};

        let key_conjectures = ["C004", "C006", "C010"]
            .into_iter()
            .map(|id| GammaCrownEntry {
                id,
                description: conjecture_description(id),
            })
            .collect();
        Self {
            total_conjectures: CONJECTURE_IDS.len(),
            key_conjectures,
        }
    }
}

fn research_status_label(status: ResearchStatus) -> &'static str {
    match status {
        ResearchStatus::Refuted => "Refuted",
        ResearchStatus::EmpiricalTested => "EmpiricalTested",
        ResearchStatus::ExecutableChecked => "ExecutableChecked",
        ResearchStatus::ProofCarrying => "ProofCarrying",
        ResearchStatus::KernelProved => "KernelProved",
        ResearchStatus::Axiomatized => "Axiomatized",
        ResearchStatus::DerivedPending => "DerivedPending",
    }
}

fn artifact_state_label(state: ResearchArtifactState) -> &'static str {
    state.as_str()
}

fn promotion_gate_label(gate: PromotionGate) -> &'static str {
    gate.as_str()
}

fn proof_status_label(status: clean_verify::ProofStatus) -> &'static str {
    match status {
        clean_verify::ProofStatus::Axiom => "Axiom",
        clean_verify::ProofStatus::DerivedPending => "DerivedPending",
        clean_verify::ProofStatus::DerivedProved => "DerivedProved",
        _ => "Unknown",
    }
}

fn render_human(out: &mut impl Write, report: &ResearchStatusReport) -> io::Result<()> {
    writeln!(out, "Research program status")?;
    writeln!(out, "manifest: {}", report.manifest_path)?;
    writeln!(out, "schema: v{}", report.manifest_schema_version)?;
    writeln!(out, "generated_at: {}", report.generated_at)?;
    writeln!(out, "entries: {}", report.total_entries)?;
    writeln!(out)?;
    writeln!(out, "status counts:")?;
    for (status, count) in &report.status_counts {
        writeln!(out, "  {status}: {count}")?;
    }
    writeln!(out, "domains:")?;
    for (domain, count) in &report.domain_counts {
        writeln!(out, "  {domain}: {count}")?;
    }
    writeln!(out, "key entries:")?;
    for entry in &report.key_entries {
        writeln!(
            out,
            "  {:<12} {:<28} {:<16} {:<15} {:<22} {:<28} {}",
            entry.id,
            entry.owner_repo,
            entry.domain,
            entry.status_class.as_str(),
            entry.artifact_state,
            entry.promotion_gate,
            entry.title
        )?;
    }
    writeln!(out, "registries:")?;
    writeln!(
        out,
        "  proof library: {} proofs",
        report.registries.proof_library.total_proofs
    )?;
    writeln!(
        out,
        "  SAT frontier: {} entries",
        report.registries.sat_frontier.total_entries
    )?;
    writeln!(
        out,
        "  gamma-crown: {} conjectures",
        report.registries.gamma_crown.total_conjectures
    )?;
    Ok(())
}

fn render_artifact_human(out: &mut impl Write, report: &ProofArtifactReport) -> io::Result<()> {
    writeln!(out, "Proof artifact validation")?;
    writeln!(out, "path: {}", report.path)?;
    writeln!(out, "status: {}", report.validation_status)?;
    writeln!(out, "schema: {}", report.schema_version)?;
    writeln!(out, "canonical: {}", report.canonical_version)?;
    writeln!(
        out,
        "producer: {} @ {}",
        report.producer_repo, report.producer_commit
    )?;
    writeln!(out, "source_system: {}", report.source_system)?;
    writeln!(out, "artifact_kind: {}", report.artifact_kind)?;
    writeln!(out, "hashes:")?;
    writeln!(out, "  problem: {}", report.problem_hash)?;
    writeln!(out, "  model: {}", report.model_hash)?;
    writeln!(out, "  proof: {}", report.proof_hash)?;
    writeln!(
        out,
        "verifier_constants: {}",
        report.verifier_constant_count
    )?;
    writeln!(out, "metadata: {}", report.metadata_count)?;
    writeln!(
        out,
        "certificate: {} ({})",
        report.certificate_format, report.certificate_encoding
    )?;
    Ok(())
}

fn render_proof_assist_human(
    out: &mut impl Write,
    report: &ProofAssistBenchReport,
) -> io::Result<()> {
    writeln!(out, "Clean proof-assistance benchmark")?;
    writeln!(out, "schema: {}", report.schema_version)?;
    writeln!(out, "environment: {}", report.environment)?;
    writeln!(out, "packets: {}", report.packet_count)?;
    writeln!(out)?;
    writeln!(
        out,
        "{:<20} {:<22} {:<10} {:<46} title",
        "packet", "phase", "candidates", "top premise"
    )?;
    for row in &report.rows {
        let top = row
            .top_candidates
            .first()
            .map(|candidate| candidate.name.as_str())
            .unwrap_or("-");
        writeln!(
            out,
            "{:<20} {:<22} {:<10} {:<46} {}",
            row.id,
            row.phase,
            row.candidate_count,
            truncate_for_research(top, 46),
            row.title
        )?;
    }
    writeln!(out)?;
    writeln!(out, "artifact checks:")?;
    for check in &report.artifact_checks {
        writeln!(
            out,
            "  {:<8} {:<28} {}",
            check.status,
            check.artifact_kind.as_deref().unwrap_or("-"),
            check.path
        )?;
    }
    Ok(())
}

fn truncate_for_research(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_owned()
    } else {
        let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
        out.push('…');
        out
    }
}

/// Feature descriptors surfaced by `clean research`.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["research", "status"],
        summary: "Print the research program status dashboard (Experimental)",
        description: "\
Experimental headless dashboard for the clean/Mathverse research program. Loads \
`data/research_program_manifest.json` by default through \
`clean_verify::research_manifest`, validates the manifest, prints aggregate \
status counts, and highlights key entries such as C004, C006, and T60. \
`--json` emits a machine-readable report with manifest entries including \
`owner_repo`, `artifact_state`, and `promotion_gate`, plus current clean \
registry snapshots for the proof library, SAT frontier registry, and \
gamma-crown conjecture catalog.\n\n\
Items gated on `TrustReportAgreement`, including C004, C006, and T60, are \
guarded against accidental promotion: if the manifest marks one of them \
`KernelProved`, the command fails until the trust report agrees with that \
promotion.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean research status",
                what: "print a compact human-readable research dashboard",
            },
            Example {
                cmd: "clean research status --json",
                what: "emit the research dashboard as JSON for agents and CI",
            },
        ],
        see_also: &["kernel verify-gamma-crown", "sorry-trace"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "clean/Mathverse research program execution plan",
                target: "designs/2026-04-23-clean-mathverse-research-program-execution-plan.md",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Research W0 status dashboard #3674",
                target: "#3674",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("research"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["research", "validate-artifact"],
        summary: "Validate a proof-artifact-v1 JSON envelope (Experimental)",
        description: "\
Experimental proof-artifact validator for cross-repo research artifacts. Reads \
a JSON file, parses and validates it through \
`clean_verify::proof_artifact_v1::ProofArtifactV1::from_json`, and prints a \
compact summary by default. `--json` emits stable fields for automation: \
schema version, canonical version, producer repo/commit, source system, \
artifact kind, problem/model/proof hashes, verifier constant and metadata \
counts, certificate format/encoding, and validation status.\n\n\
Invalid artifacts return a clear non-zero CLI error without replaying opaque \
certificate payloads or panicking.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean research validate-artifact tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_entailment_valid.json",
                what: "validate a checked-in gamma-crown proof-artifact wrapper and print a human summary",
            },
            Example {
                cmd: "clean research validate-artifact tests/fixtures/external_certificates/proof_artifact_v1/ay_alethe_envelope.json --json",
                what: "emit JSON metadata for a checked-in ay proof-artifact wrapper",
            },
        ],
        see_also: &["research status", "kernel verify-gamma-crown"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "Proof artifact validation CLI #3677",
                target: "#3677",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-verify",
                target: "clean-verify",
            },
        ],
        domain_root: Some("research"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["research", "proof-assist-bench"],
        summary: "Run the Gamma-Crown proof-assistance benchmark (Experimental)",
        description: "\
Experimental clean-native proof-factory benchmark for the Gamma-Crown research \
program. The bench starts with the original Gamma-Crown theorem packets \
(C007 certificate composition, C004/C006 CROWN structure, C010 domain \
equivalence, C012 ReLU stability), then includes the longer-range structural \
dichotomy and certificate-calculus packets. Each row ranks premises from the \
Gamma-Crown / NNVerify clean environment and validates checked-in \
proof-artifact-v1 certificate wrappers. The purpose is to make proof-assistance \
progress measurable before theorem promotion or solver-impact claims.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean research proof-assist-bench",
                what: "print a compact proof-assistance benchmark over Gamma-Crown packets",
            },
            Example {
                cmd: "clean research proof-assist-bench --json --limit 8",
                what: "emit machine-readable rows with eight premise candidates per packet",
            },
        ],
        see_also: &["research status", "research validate-artifact", "auto premise"],
        references: &[
            Reference {
                kind: RefKind::Issue,
                label: "AI proof search with kernel verification loop #3386",
                target: "#3386",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-auto",
                target: "clean-auto",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-verify",
                target: "clean-verify",
            },
        ],
        domain_root: Some("research"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use clean_verify::research_manifest::RESEARCH_MANIFEST_SCHEMA_VERSION;
    use std::path::PathBuf;

    fn item(id: &str, status: ResearchStatus, domain: &str) -> ResearchManifestItem {
        let mut item = ResearchManifestItem::new(
            id,
            format!("{id} title"),
            domain,
            "test-family",
            status,
            format!("{id} summary"),
        );
        if matches!(id, "C004" | "C006" | "T60") {
            item = item.with_promotion_gate(PromotionGate::TrustReportAgreement);
        }
        item
    }

    fn manifest(items: Vec<ResearchManifestItem>) -> ResearchManifest {
        ResearchManifest {
            schema_version: RESEARCH_MANIFEST_SCHEMA_VERSION,
            generated_at: "2026-04-23T00:00:00Z".to_owned(),
            source: "test".to_owned(),
            items,
        }
    }

    fn valid_artifact_json() -> String {
        r#"{
  "version": "proof-artifact-v1",
  "producer": {
    "repo": "alabsystems/gamma-crown",
    "commit": "0123456789abcdef"
  },
  "source_system": "gamma-crown",
  "problem_hash": "blake3:problem",
  "model_hash": "blake3:model",
  "proof_hash": "blake3:proof",
  "artifact_kind": "gamma_crown_entailment",
  "verifier_constants": [
    {
      "name": "rhs_block_3_356",
      "role": "constraint_rhs",
      "value": "-236774564/1000000000"
    }
  ],
  "certificate": {
    "format": "gamma-crown-linear-entailment-v1",
    "encoding": "json",
    "payload": {
      "type": "linear_entailment",
      "constraints": []
    }
  },
  "metadata": {
    "fixture": "valid"
  }
}"#
        .to_owned()
    }

    fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate dir should have workspace parent")
            .parent()
            .expect("workspace root should exist")
            .to_path_buf()
    }

    fn checked_in_artifact_fixture(name: &str) -> PathBuf {
        workspace_root()
            .join("tests/fixtures/external_certificates/proof_artifact_v1")
            .join(name)
    }

    #[test]
    fn manifest_counts_statuses_and_domains() {
        let manifest = manifest(vec![
            item("C004", ResearchStatus::Axiomatized, "gamma-crown"),
            item("S40", ResearchStatus::ExecutableChecked, "sat-frontier"),
            item("GF01", ResearchStatus::ProofCarrying, "gf2"),
        ]);
        let report = ResearchStatusReport::from_manifest(Path::new("manifest.json"), &manifest);

        assert_eq!(report.total_entries, 3);
        assert_eq!(report.status_counts["Axiomatized"], 1);
        assert_eq!(report.status_counts["ExecutableChecked"], 1);
        assert_eq!(report.status_counts["ProofCarrying"], 1);
        assert_eq!(report.domain_counts["gamma-crown"], 1);
        assert_eq!(report.key_entries[0].id, "C004");
    }

    #[test]
    fn guarded_kernel_proved_item_is_rejected() {
        let guarded = item("T60", ResearchStatus::KernelProved, "gamma-crown")
            .with_promotion_gate(PromotionGate::TrustReportAgreement);
        let manifest = manifest(vec![guarded]);
        let err = validate_manifest_for_cli(Path::new("manifest.json"), &manifest)
            .expect_err("T60 KernelProved should fail");
        assert!(matches!(err, ResearchError::GuardedPromotion { ref id } if id == "T60"));
    }

    #[test]
    fn human_render_includes_counts_and_key_entries() {
        let manifest = manifest(vec![item(
            "C006",
            ResearchStatus::Axiomatized,
            "gamma-crown",
        )]);
        let report = ResearchStatusReport::from_manifest(Path::new("manifest.json"), &manifest);
        let mut buf = Vec::new();
        render_human(&mut buf, &report).expect("render human");
        let text = String::from_utf8(buf).expect("utf8");

        assert!(text.contains("Research program status"));
        assert!(text.contains("Axiomatized: 1"));
        assert!(text.contains("C006"));
        assert!(text.contains("C006 title"));
        assert!(text.contains("alabsystems/clean"));
        assert!(text.contains("TrustReportAgreement"));
    }

    #[test]
    fn validate_artifact_report_from_checked_in_fixture() {
        let path = checked_in_artifact_fixture("gamma_crown_entailment_valid.json");
        let report = load_artifact_report(&path).expect("valid artifact");

        assert_eq!(report.schema_version, "proof-artifact-v1");
        assert_eq!(report.canonical_version, PROOF_ARTIFACT_V1_VERSION);
        assert_eq!(report.producer_repo, "tests/fixtures/external_certificates");
        assert_eq!(
            report.producer_commit,
            "fixture-gamma-crown-entailment-valid"
        );
        assert_eq!(report.source_system, "gamma-crown");
        assert_eq!(report.artifact_kind, "gamma_crown_entailment");
        assert_eq!(
            report.problem_hash,
            "blake3:fixture-gamma-crown-entailment-problem"
        );
        assert_eq!(
            report.model_hash,
            "blake3:fixture-gamma-crown-entailment-model"
        );
        assert_eq!(
            report.proof_hash,
            "blake3:fixture-gamma-crown-entailment-proof"
        );
        assert_eq!(report.verifier_constant_count, 3);
        assert_eq!(report.metadata_count, 0);
        assert_eq!(
            report.certificate_format,
            "gamma-crown-linear-entailment-v1"
        );
        assert_eq!(report.certificate_encoding, "json");
        assert_eq!(report.validation_status, "valid");
    }

    #[test]
    fn validate_artifact_rejects_invalid_temp_file() {
        let tempdir = tempfile::tempdir().expect("tempdir");
        let path = tempdir.path().join("artifact.invalid.json");
        let invalid = valid_artifact_json().replace(
            r#"  "model_hash": "blake3:model",
"#,
            "",
        );
        std::fs::write(&path, invalid).expect("write invalid fixture");

        let err = load_artifact_report(&path).expect_err("invalid artifact");

        assert!(matches!(err, ResearchError::Artifact { .. }));
        assert!(err.to_string().contains("invalid proof artifact"));
        assert!(err.to_string().contains("model_hash"));
    }

    #[test]
    fn artifact_human_render_includes_validation_summary() {
        let artifact = ProofArtifactV1::from_json(&valid_artifact_json()).expect("artifact");
        let report =
            ProofArtifactReport::from_artifact(Path::new("artifact.valid.json"), &artifact);
        let mut buf = Vec::new();
        render_artifact_human(&mut buf, &report).expect("render artifact");
        let text = String::from_utf8(buf).expect("utf8");

        assert!(text.contains("Proof artifact validation"));
        assert!(text.contains("status: valid"));
        assert!(text.contains("schema: proof-artifact-v1"));
        assert!(text.contains("certificate: gamma-crown-linear-entailment-v1 (json)"));
    }

    #[test]
    fn status_json_includes_owner_repo_artifact_state_and_promotion_gate() {
        let report = ResearchStatusReport::from_manifest(
            Path::new("manifest.json"),
            &manifest(vec![item(
                "GC_CERT_ENTAILMENT",
                ResearchStatus::ProofCarrying,
                "gamma-crown",
            )
            .with_owner_repo("alabsystems/gamma-crown")
            .with_artifact_state(ResearchArtifactState::Replayable)
            .with_promotion_gate(PromotionGate::ArtifactReplayAndKernelImport)]),
        );

        let json = serde_json::to_value(&report).expect("serialize report");
        let entry = json["entries"]
            .as_array()
            .expect("entries array")
            .first()
            .expect("first entry");

        assert_eq!(entry["owner_repo"], "alabsystems/gamma-crown");
        assert_eq!(entry["artifact_state"], "Replayable");
        assert_eq!(entry["promotion_gate"], "ArtifactReplayAndKernelImport");
    }
}

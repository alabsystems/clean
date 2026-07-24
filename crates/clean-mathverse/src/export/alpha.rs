// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Training data export pipeline for the Mathverse Library.
//!
//! Exports verified theorem data in formats suitable for AI training:
//! proof generation, premise selection, and statement-level datasets.

use serde::{Deserialize, Serialize};

use crate::error::MathverseResult;
use crate::library::MathverseLibrary;
use crate::types::{AxiomProfile, ConstantIdx, ContentDomain, ImportConfidence, SourceSystem};
use crate::verify::TrustGate;

/// Output format for exported training data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExportFormat {
    /// JSON Lines (one JSON object per line).
    JsonLines,
    /// CSV with escaped fields.
    Csv,
    /// MessagePack binary.
    MsgPack,
}

/// Configuration for training data export.
#[derive(Clone, Debug)]
pub struct ExportConfig {
    /// Trust gate -- what trust levels are eligible.
    pub trust_gate: TrustGate,
    /// Maximum axiom profile bits allowed (0 = kernel-verified only).
    pub max_axiom_bits: u64,
    /// Include proof sketches (if available).
    pub include_proofs: bool,
    /// Include dependency lists.
    pub include_deps: bool,
    /// Output format.
    pub format: ExportFormat,
    /// Maximum number of records to export (0 = unlimited).
    pub limit: usize,
    /// Source system filter (None = all systems).
    pub source_filter: Option<Vec<SourceSystem>>,
    /// Content domain filter (None = all domains).
    pub domain_filter: Option<Vec<ContentDomain>>,
}

impl ExportConfig {
    /// Preset: proof generation (kernel-verified only, no axioms, with proofs).
    #[must_use]
    pub fn proof_gen() -> Self {
        Self {
            trust_gate: TrustGate::ProofGenEligible,
            max_axiom_bits: 0,
            include_proofs: true,
            include_deps: false,
            format: ExportFormat::JsonLines,
            limit: 0,
            source_filter: None,
            domain_filter: None,
        }
    }

    /// Preset: premise selection (kernel-verified + translated, with deps).
    #[must_use]
    pub fn premise_selection() -> Self {
        Self {
            trust_gate: TrustGate::PremiseSelectEligible,
            max_axiom_bits: u64::MAX,
            include_proofs: false,
            include_deps: true,
            format: ExportFormat::JsonLines,
            limit: 0,
            source_filter: None,
            domain_filter: None,
        }
    }

    /// Preset: statement-only (all trust levels, minimal data).
    #[must_use]
    pub fn statement_only() -> Self {
        Self {
            trust_gate: TrustGate::StatementOnly,
            max_axiom_bits: u64::MAX,
            include_proofs: false,
            include_deps: false,
            format: ExportFormat::JsonLines,
            limit: 0,
            source_filter: None,
            domain_filter: None,
        }
    }
}

/// A single training data record ready for serialization.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExportRecord {
    pub name: String,
    pub type_expr: String,
    pub source: String,
    pub confidence: String,
    pub axiom_bits: u64,
    pub axiom_names: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_sketch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub deps: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub domain: Option<String>,
}

/// Statistics from an export run.
#[derive(Clone, Debug, Default)]
pub struct ExportStats {
    pub total_eligible: usize,
    pub exported: usize,
    pub filtered_by_trust: usize,
    pub filtered_by_axioms: usize,
    pub filtered_by_source: usize,
    pub filtered_by_domain: usize,
    pub by_source: hashbrown::HashMap<String, usize>,
    pub by_confidence: hashbrown::HashMap<String, usize>,
}

/// All axiom profile bits paired with their human-readable names.
/// Canonical axiom bit names — no aliases (CLASSICAL==CHOICE, HOL_EMBEDDING==HOL_AXIOMS, etc.)
const AXIOM_BIT_NAMES: &[(u64, &str)] = &[
    (AxiomProfile::CHOICE.0, "choice"),
    (AxiomProfile::LEM.0, "lem"),
    (AxiomProfile::PROP_EXT.0, "propext"),
    (AxiomProfile::FUNC_EXT.0, "funext"),
    (AxiomProfile::QUOT.0, "quot"),
    (AxiomProfile::UNIVALENCE.0, "univalence"),
    (AxiomProfile::LARGE_ELIM.0, "large_elim"),
    (AxiomProfile::HOL_AXIOMS.0, "hol_axioms"),
    (AxiomProfile::MIZAR_TG.0, "mizar_tg"),
    (AxiomProfile::UNIVERSE_INCON.0, "universe_incon"),
    (AxiomProfile::AXIOMATIZED.0, "axiomatized"),
    (AxiomProfile::BRIDGE_AXIOM.0, "bridge_axiom"),
    (AxiomProfile::REAL_AXIOMS.0, "real_axioms"),
    (AxiomProfile::LRA_TRUSTED.0, "lra_trusted"),
    (AxiomProfile::FLOAT_APPROX.0, "float_approx"),
    (AxiomProfile::NN_ABSTRACTION.0, "nn_abstraction"),
];

/// Convert axiom profile bits to human-readable names.
#[must_use]
pub fn axiom_names(bits: u64) -> Vec<String> {
    AXIOM_BIT_NAMES
        .iter()
        .filter(|(bit, _)| bits & bit != 0)
        .map(|(_, name)| (*name).into())
        .collect()
}

/// Training data exporter.
pub struct Exporter<'a> {
    library: &'a MathverseLibrary,
    config: ExportConfig,
}

impl<'a> Exporter<'a> {
    pub fn new(library: &'a MathverseLibrary, config: ExportConfig) -> Self {
        Self { library, config }
    }

    /// Check if a constant is eligible for export under the current config.
    pub fn is_eligible(&self, idx: ConstantIdx) -> bool {
        let header = match self.library.get_constant(idx) {
            Some(h) => h,
            None => return false,
        };
        let confidence = match header.confidence() {
            Ok(c) => c,
            Err(_) => return false,
        };
        if !trust_gate_allows(self.config.trust_gate, confidence) {
            return false;
        }
        if self.config.max_axiom_bits == 0 {
            if header.axiom_profile != 0 {
                return false;
            }
        } else if header.axiom_profile & !self.config.max_axiom_bits != 0 {
            return false;
        }
        if let Some(ref allowed) = self.config.source_filter {
            match header.source() {
                Ok(src) if allowed.contains(&src) => {}
                _ => return false,
            }
        }
        if let Some(ref allowed) = self.config.domain_filter {
            match header.domain() {
                Ok(dom) if allowed.contains(&dom) => {}
                _ => return false,
            }
        }
        true
    }

    /// Export a single constant to an [`ExportRecord`].
    pub fn export_one(&self, idx: ConstantIdx) -> Option<ExportRecord> {
        if !self.is_eligible(idx) {
            return None;
        }
        let header = self.library.get_constant(idx)?;
        let name = self.library.get_name(idx).unwrap_or("?").to_owned();
        let source = header
            .source()
            .map_or_else(|v| format!("Unknown({v})"), |s| format!("{s:?}"));
        let confidence = header
            .confidence()
            .map_or_else(|v| format!("Unknown({v})"), |c| format!("{c:?}"));
        let domain = header.domain().ok().map(|d| format!("{d:?}"));
        // Proof sketches are not yet stored; placeholder for future integration.
        let proof_sketch = None;
        let deps = if self.config.include_deps {
            self.library.deps().get(idx as usize).map(|ds| {
                ds.iter()
                    .filter_map(|&d| self.library.get_name(d).map(|n| n.to_owned()))
                    .collect()
            })
        } else {
            None
        };
        Some(ExportRecord {
            name,
            type_expr: format!("type@{}", header.type_idx),
            source,
            confidence,
            axiom_bits: header.axiom_profile.0,
            axiom_names: axiom_names(header.axiom_profile.0),
            proof_sketch,
            deps,
            domain,
        })
    }

    /// Export all eligible constants.
    pub fn export_all(&self) -> Vec<ExportRecord> {
        let limit = if self.config.limit == 0 {
            usize::MAX
        } else {
            self.config.limit
        };
        let mut records = Vec::new();
        for idx in 0..self.library.constant_count() as ConstantIdx {
            if records.len() >= limit {
                break;
            }
            if let Some(r) = self.export_one(idx) {
                records.push(r);
            }
        }
        records
    }

    /// Export to a writer in the configured format.
    pub fn export_to_writer(
        &self,
        writer: &mut impl std::io::Write,
    ) -> MathverseResult<ExportStats> {
        let limit = if self.config.limit == 0 {
            usize::MAX
        } else {
            self.config.limit
        };
        let mut stats = self.build_stats_internal();
        let mut exported = 0usize;
        for idx in 0..self.library.constant_count() as ConstantIdx {
            if exported >= limit {
                break;
            }
            if let Some(record) = self.export_one(idx) {
                match self.config.format {
                    ExportFormat::JsonLines | ExportFormat::MsgPack => {
                        serde_json::to_writer(&mut *writer, &record)?;
                        writer.write_all(b"\n")?;
                    }
                    ExportFormat::Csv => {
                        let line = format!(
                            "{},{},{},{},{}\n",
                            csv_escape(&record.name),
                            csv_escape(&record.type_expr),
                            csv_escape(&record.source),
                            csv_escape(&record.confidence),
                            record.axiom_bits
                        );
                        writer.write_all(line.as_bytes())?;
                    }
                }
                exported += 1;
            }
        }
        stats.exported = exported;
        Ok(stats)
    }

    /// Get export statistics without actually exporting.
    pub fn preview_stats(&self) -> ExportStats {
        let mut stats = self.build_stats_internal();
        stats.exported = stats.total_eligible;
        if self.config.limit > 0 && stats.exported > self.config.limit {
            stats.exported = self.config.limit;
        }
        stats
    }

    fn build_stats_internal(&self) -> ExportStats {
        let mut stats = ExportStats::default();
        for idx in 0..self.library.constant_count() as ConstantIdx {
            let header = match self.library.get_constant(idx) {
                Some(h) => h,
                None => continue,
            };
            let confidence = match header.confidence() {
                Ok(c) => c,
                Err(_) => continue,
            };
            if !trust_gate_allows(self.config.trust_gate, confidence) {
                stats.filtered_by_trust += 1;
                continue;
            }
            if self.config.max_axiom_bits == 0 {
                if header.axiom_profile != 0 {
                    stats.filtered_by_axioms += 1;
                    continue;
                }
            } else if header.axiom_profile & !self.config.max_axiom_bits != 0 {
                stats.filtered_by_axioms += 1;
                continue;
            }
            if let Some(ref allowed) = self.config.source_filter {
                match header.source() {
                    Ok(src) if allowed.contains(&src) => {}
                    _ => {
                        stats.filtered_by_source += 1;
                        continue;
                    }
                }
            }
            if let Some(ref allowed) = self.config.domain_filter {
                match header.domain() {
                    Ok(dom) if allowed.contains(&dom) => {}
                    _ => {
                        stats.filtered_by_domain += 1;
                        continue;
                    }
                }
            }
            stats.total_eligible += 1;
            let src = header
                .source()
                .map_or_else(|v| format!("Unknown({v})"), |s| format!("{s:?}"));
            *stats.by_source.entry(src).or_insert(0) += 1;
            *stats
                .by_confidence
                .entry(format!("{confidence:?}"))
                .or_insert(0) += 1;
        }
        stats
    }
}

fn trust_gate_allows(gate: TrustGate, confidence: ImportConfidence) -> bool {
    match gate {
        TrustGate::ProofGenEligible => confidence == ImportConfidence::KernelVerified,
        TrustGate::PremiseSelectEligible => {
            confidence == ImportConfidence::KernelVerified
                || confidence == ImportConfidence::SourceVerified
                || confidence == ImportConfidence::Translated
        }
        TrustGate::StatementOnly => true,
    }
}

fn csv_escape(field: &str) -> String {
    if field.contains(',') || field.contains('"') || field.contains('\n') {
        format!("\"{}\"", field.replace('"', "\"\""))
    } else {
        field.to_owned()
    }
}

// ---------------------------------------------------------------------------
// CSV export
// ---------------------------------------------------------------------------

/// Export records to CSV format with proper escaping.
///
/// Writes a header row followed by one row per record. Returns the number
/// of records written.
pub fn export_to_csv(
    writer: &mut impl std::io::Write,
    records: &[ExportRecord],
) -> MathverseResult<usize> {
    writer.write_all(b"name,type_expr,source,confidence,axiom_bits,axiom_names,domain\n")?;
    for record in records {
        let axiom_names_joined = record.axiom_names.join(";");
        let domain = record.domain.as_deref().unwrap_or("");
        let line = format!(
            "{},{},{},{},{},{},{}\n",
            csv_escape(&record.name),
            csv_escape(&record.type_expr),
            csv_escape(&record.source),
            csv_escape(&record.confidence),
            record.axiom_bits,
            csv_escape(&axiom_names_joined),
            csv_escape(domain),
        );
        writer.write_all(line.as_bytes())?;
    }
    Ok(records.len())
}

// ---------------------------------------------------------------------------
// Statistics summary
// ---------------------------------------------------------------------------

/// Produce a human-readable summary of export statistics.
#[must_use]
pub fn export_statistics_summary(stats: &ExportStats) -> String {
    let mut lines = Vec::new();
    lines.push("Export Statistics".to_string());
    lines.push(format!("  Total eligible:     {}", stats.total_eligible));
    lines.push(format!("  Exported:           {}", stats.exported));
    lines.push(format!("  Filtered by trust:  {}", stats.filtered_by_trust));
    lines.push(format!(
        "  Filtered by axioms: {}",
        stats.filtered_by_axioms
    ));
    lines.push(format!(
        "  Filtered by source: {}",
        stats.filtered_by_source
    ));
    lines.push(format!(
        "  Filtered by domain: {}",
        stats.filtered_by_domain
    ));
    if !stats.by_source.is_empty() {
        lines.push("  By source:".to_string());
        let mut sources: Vec<_> = stats.by_source.iter().collect();
        sources.sort_by_key(|(k, _)| (*k).clone());
        for (src, count) in sources {
            lines.push(format!("    {src}: {count}"));
        }
    }
    if !stats.by_confidence.is_empty() {
        lines.push("  By confidence:".to_string());
        let mut confs: Vec<_> = stats.by_confidence.iter().collect();
        confs.sort_by_key(|(k, _)| (*k).clone());
        for (conf, count) in confs {
            lines.push(format!("    {conf}: {count}"));
        }
    }
    lines.join("\n")
}

// ---------------------------------------------------------------------------
// ExportFilter builder
// ---------------------------------------------------------------------------

/// Declarative filter for selecting constants to export.
///
/// Constructed via the builder pattern:
/// ```text
/// let filter = ExportFilter::new()
///     .source_systems(&[SourceSystem::Lean4])
///     .min_confidence(ImportConfidence::Translated)
///     .domains(&[ContentDomain::PureMath])
///     .max_axiom_bits(0)
///     .build();
/// ```
#[derive(Clone, Debug, Default)]
pub struct ExportFilter {
    pub source_systems: Option<Vec<SourceSystem>>,
    pub min_confidence: Option<ImportConfidence>,
    pub domains: Option<Vec<ContentDomain>>,
    pub max_axiom_bits: Option<u64>,
}

impl ExportFilter {
    /// Start building a new filter with no constraints.
    ///
    /// `new()` returns the builder (not `Self`) intentionally — call
    /// `.build()` on the result to produce an `ExportFilter`.
    #[allow(clippy::new_ret_no_self)]
    #[must_use]
    pub fn new() -> ExportFilterBuilder {
        ExportFilterBuilder {
            source_systems: None,
            min_confidence: None,
            domains: None,
            max_axiom_bits: None,
        }
    }

    /// Check if a constant header passes this filter.
    pub fn matches(&self, header: &crate::types::MathverseConstantHeader) -> bool {
        if let Some(ref systems) = self.source_systems {
            match header.source() {
                Ok(src) if systems.contains(&src) => {}
                _ => return false,
            }
        }
        if let Some(min_conf) = self.min_confidence {
            match header.confidence() {
                Ok(conf) if conf <= min_conf => {}
                _ => return false,
            }
        }
        if let Some(ref doms) = self.domains {
            match header.domain() {
                Ok(dom) if doms.contains(&dom) => {}
                _ => return false,
            }
        }
        if let Some(max_bits) = self.max_axiom_bits {
            if max_bits == 0 {
                if header.axiom_profile != 0 {
                    return false;
                }
            } else if header.axiom_profile & !max_bits != 0 {
                return false;
            }
        }
        true
    }
}

/// Builder for [`ExportFilter`].
#[derive(Clone, Debug)]
pub struct ExportFilterBuilder {
    source_systems: Option<Vec<SourceSystem>>,
    min_confidence: Option<ImportConfidence>,
    domains: Option<Vec<ContentDomain>>,
    max_axiom_bits: Option<u64>,
}

impl ExportFilterBuilder {
    /// Filter to specific source systems.
    #[must_use]
    pub fn source_systems(mut self, systems: &[SourceSystem]) -> Self {
        self.source_systems = Some(systems.to_vec());
        self
    }

    /// Require at least this confidence level (inclusive).
    #[must_use]
    pub fn min_confidence(mut self, confidence: ImportConfidence) -> Self {
        self.min_confidence = Some(confidence);
        self
    }

    /// Filter to specific content domains.
    #[must_use]
    pub fn domains(mut self, domains: &[ContentDomain]) -> Self {
        self.domains = Some(domains.to_vec());
        self
    }

    /// Maximum allowed axiom bits (0 = pure only).
    #[must_use]
    pub fn max_axiom_bits(mut self, bits: u64) -> Self {
        self.max_axiom_bits = Some(bits);
        self
    }

    /// Build the filter.
    #[must_use]
    pub fn build(self) -> ExportFilter {
        ExportFilter {
            source_systems: self.source_systems,
            min_confidence: self.min_confidence,
            domains: self.domains,
            max_axiom_bits: self.max_axiom_bits,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::trust::policy::TrustPolicy;
    use crate::types::{AxiomProfile, MathverseConstantHeader};
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use ContentDomain as CD;
    use ImportConfidence as IC;
    use SourceSystem as SS;
    type E = (&'static str, SS, IC, CD, AxiomProfile);
    const KV: IC = IC::KernelVerified;
    const PM: CD = CD::PureMath;

    fn mk(name: &'static str, src: SS, conf: IC, dom: CD, ax: AxiomProfile) -> E {
        (name, src, conf, dom, ax)
    }
    fn build_shard(entries: &[E]) -> crate::shard::ShardReader {
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let e0 = w.add_expr(FlatExpr::sort(l0));
        for &(name, src, conf, dom, ax) in entries {
            let ni = w.add_string(name);
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e0,
                value_idx: e0,
                source_system: src as u8,
                import_confidence: conf as u8,
                content_domain: dom as u8,
                decl_kind: 0,
                axiom_profile: ax,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        crate::shard::ShardReader::from_bytes(&buf).unwrap()
    }
    fn lib(entries: &[E]) -> MathverseLibrary {
        let s = build_shard(entries);
        let mut l = MathverseLibrary::new(TrustPolicy::permissive());
        l.load_shard(&s).unwrap();
        l
    }

    #[test]
    fn test_config_presets() {
        let pg = ExportConfig::proof_gen();
        assert_eq!(pg.trust_gate, TrustGate::ProofGenEligible);
        assert_eq!(pg.max_axiom_bits, 0);
        assert!(pg.include_proofs && !pg.include_deps);
        assert_eq!(pg.format, ExportFormat::JsonLines);
        let ps = ExportConfig::premise_selection();
        assert_eq!(ps.trust_gate, TrustGate::PremiseSelectEligible);
        assert!(ps.include_deps && !ps.include_proofs);
        let so = ExportConfig::statement_only();
        assert_eq!(so.trust_gate, TrustGate::StatementOnly);
        assert!(!so.include_proofs && !so.include_deps);
    }

    #[test]
    fn test_is_eligible() {
        let l = lib(&[
            mk("kv", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("tr", SS::Coq, IC::Translated, PM, AxiomProfile::NONE),
            mk("uv", SS::Isabelle, IC::Unverified, PM, AxiomProfile::NONE),
        ]);
        let pg = Exporter::new(&l, ExportConfig::proof_gen());
        assert!(pg.is_eligible(0) && !pg.is_eligible(1) && !pg.is_eligible(2));
        assert!(!pg.is_eligible(999)); // out of range
        let ps = Exporter::new(&l, ExportConfig::premise_selection());
        assert!(ps.is_eligible(0) && ps.is_eligible(1) && !ps.is_eligible(2));
        let so = Exporter::new(&l, ExportConfig::statement_only());
        assert!(so.is_eligible(0) && so.is_eligible(1) && so.is_eligible(2));
        // Axiom bits: proof_gen rejects any axioms; custom mask allows them.
        let la = lib(&[mk(
            "t",
            SS::Lean4,
            KV,
            PM,
            AxiomProfile::CHOICE | AxiomProfile::LEM,
        )]);
        assert!(!Exporter::new(&la, ExportConfig::proof_gen()).is_eligible(0));
        let mut c = ExportConfig::proof_gen();
        c.max_axiom_bits = (AxiomProfile::CHOICE | AxiomProfile::LEM).0;
        assert!(Exporter::new(&la, c).is_eligible(0));
        // Source + domain filters.
        let lf = lib(&[
            mk("lean", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("coq", SS::Coq, KV, PM, AxiomProfile::NONE),
            mk("sw", SS::Lean4, KV, CD::Software, AxiomProfile::NONE),
        ]);
        let mut cs = ExportConfig::proof_gen();
        cs.source_filter = Some(vec![SS::Lean4]);
        let es = Exporter::new(&lf, cs);
        assert!(es.is_eligible(0) && !es.is_eligible(1) && es.is_eligible(2));
        let mut cd = ExportConfig::proof_gen();
        cd.domain_filter = Some(vec![CD::Software]);
        let ed = Exporter::new(&lf, cd);
        assert!(!ed.is_eligible(0) && ed.is_eligible(2));
    }

    #[test]
    fn test_export_one_and_all() {
        // Record fields.
        let l = lib(&[mk("Nat.add", SS::Lean4, KV, PM, AxiomProfile::CHOICE)]);
        let mut c = ExportConfig::statement_only();
        c.max_axiom_bits = u64::MAX;
        let r = Exporter::new(&l, c).export_one(0).unwrap();
        assert_eq!(
            (r.name.as_str(), r.source.as_str(), r.confidence.as_str()),
            ("Nat.add", "Lean4", "KernelVerified")
        );
        assert_eq!(r.axiom_bits, AxiomProfile::CHOICE);
        assert_eq!(r.axiom_names, vec!["choice"]);
        assert!(r.proof_sketch.is_none() && r.deps.is_none());
        // Not eligible returns None.
        let l2 = lib(&[mk("t", SS::Coq, IC::Translated, PM, AxiomProfile::NONE)]);
        assert!(Exporter::new(&l2, ExportConfig::proof_gen())
            .export_one(0)
            .is_none());
        // export_all filters + limit.
        let l3 = lib(&[
            mk("v", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("t", SS::Coq, IC::Translated, PM, AxiomProfile::NONE),
        ]);
        assert_eq!(
            Exporter::new(&l3, ExportConfig::proof_gen())
                .export_all()
                .len(),
            1
        );
        let l4 = lib(&[
            mk("a", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("b", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("c", SS::Lean4, KV, PM, AxiomProfile::NONE),
        ]);
        let mut cl = ExportConfig::proof_gen();
        cl.limit = 2;
        assert_eq!(Exporter::new(&l4, cl).export_all().len(), 2);
        // Deps included under premise_selection.
        let l5 = lib(&[mk("base", SS::Lean4, KV, PM, AxiomProfile::NONE)]);
        assert!(Exporter::new(&l5, ExportConfig::premise_selection())
            .export_one(0)
            .unwrap()
            .deps
            .is_some());
        // Statement-only includes unverified.
        let l6 = lib(&[
            mk("v", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("u", SS::Lean4, IC::Unverified, PM, AxiomProfile::NONE),
        ]);
        assert_eq!(
            Exporter::new(&l6, ExportConfig::statement_only())
                .export_all()
                .len(),
            2
        );
    }

    #[test]
    fn test_axiom_names_coverage() {
        assert!(axiom_names(0).is_empty());
        assert_eq!(axiom_names(AxiomProfile::CHOICE.0), vec!["choice"]);
        assert_eq!(
            axiom_names(AxiomProfile::NN_ABSTRACTION.0),
            vec!["nn_abstraction"]
        );
        let all = AxiomProfile::CHOICE
            | AxiomProfile::LEM
            | AxiomProfile::PROP_EXT
            | AxiomProfile::FUNC_EXT
            | AxiomProfile::QUOT
            | AxiomProfile::UNIVALENCE
            | AxiomProfile::LARGE_ELIM
            | AxiomProfile::HOL_AXIOMS
            | AxiomProfile::MIZAR_TG
            | AxiomProfile::UNIVERSE_INCON
            | AxiomProfile::AXIOMATIZED
            | AxiomProfile::BRIDGE_AXIOM
            | AxiomProfile::REAL_AXIOMS
            | AxiomProfile::LRA_TRUSTED
            | AxiomProfile::FLOAT_APPROX
            | AxiomProfile::NN_ABSTRACTION;
        // 16 canonical names (aliases like CLASSICAL==CHOICE excluded from table)
        assert_eq!(axiom_names(all.0).len(), 16);
    }

    #[test]
    fn test_export_to_writer() {
        // JSON Lines
        let l = lib(&[
            mk("a", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("b", SS::Lean4, KV, PM, AxiomProfile::NONE),
        ]);
        let mut buf = Vec::new();
        let stats = Exporter::new(&l, ExportConfig::proof_gen())
            .export_to_writer(&mut buf)
            .unwrap();
        assert_eq!(stats.exported, 2);
        let out = String::from_utf8(buf).unwrap();
        assert_eq!(out.lines().count(), 2);
        let r: ExportRecord = serde_json::from_str(out.lines().next().unwrap()).unwrap();
        assert_eq!(r.name, "a");
        // CSV
        let l2 = lib(&[mk("thm", SS::Lean4, KV, PM, AxiomProfile::NONE)]);
        let mut c = ExportConfig::proof_gen();
        c.format = ExportFormat::Csv;
        let mut buf2 = Vec::new();
        assert_eq!(
            Exporter::new(&l2, c)
                .export_to_writer(&mut buf2)
                .unwrap()
                .exported,
            1
        );
        let csv = String::from_utf8(buf2).unwrap();
        assert!(csv.contains("thm") && csv.contains("Lean4"));
    }

    #[test]
    fn test_preview_stats() {
        let l = lib(&[
            mk("v", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("t", SS::Coq, IC::Translated, PM, AxiomProfile::NONE),
            mk("u", SS::Isabelle, IC::Unverified, PM, AxiomProfile::NONE),
        ]);
        let s = Exporter::new(&l, ExportConfig::proof_gen()).preview_stats();
        assert_eq!(
            (s.total_eligible, s.exported, s.filtered_by_trust),
            (1, 1, 2)
        );
        assert_eq!(*s.by_source.get("Lean4").unwrap(), 1);
        // Axiom, source, domain filtering
        let l2 = lib(&[
            mk("p", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("a", SS::Lean4, KV, PM, AxiomProfile::CHOICE),
        ]);
        assert_eq!(
            Exporter::new(&l2, ExportConfig::proof_gen())
                .preview_stats()
                .filtered_by_axioms,
            1
        );
        let l3 = lib(&[
            mk("l", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("c", SS::Coq, KV, PM, AxiomProfile::NONE),
        ]);
        let mut c3 = ExportConfig::proof_gen();
        c3.source_filter = Some(vec![SS::Lean4]);
        assert_eq!(Exporter::new(&l3, c3).preview_stats().filtered_by_source, 1);
        let l4 = lib(&[
            mk("m", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("s", SS::Lean4, KV, CD::Software, AxiomProfile::NONE),
        ]);
        let mut c4 = ExportConfig::proof_gen();
        c4.domain_filter = Some(vec![PM]);
        assert_eq!(Exporter::new(&l4, c4).preview_stats().filtered_by_domain, 1);
        // Limit
        let l5 = lib(&[
            mk("a", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("b", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("c", SS::Lean4, KV, PM, AxiomProfile::NONE),
        ]);
        let mut c5 = ExportConfig::proof_gen();
        c5.limit = 1;
        assert_eq!(
            (Exporter::new(&l5, c5).preview_stats().total_eligible, 1),
            (3, 1)
        );
    }

    #[test]
    fn test_empty_library() {
        let l = MathverseLibrary::new(TrustPolicy::permissive());
        let e = Exporter::new(&l, ExportConfig::proof_gen());
        assert!(e.export_all().is_empty());
        let mut buf = Vec::new();
        assert_eq!(e.export_to_writer(&mut buf).unwrap().exported, 0);
    }

    #[test]
    fn test_export_to_csv_basic() {
        let l = lib(&[
            mk("Nat.add", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("Bool.true", SS::Lean4, KV, CD::Logic, AxiomProfile::NONE),
        ]);
        let records = Exporter::new(&l, ExportConfig::proof_gen()).export_all();
        let mut buf = Vec::new();
        let count = export_to_csv(&mut buf, &records).unwrap();
        assert_eq!(count, 2);
        let csv = String::from_utf8(buf).unwrap();
        let lines: Vec<&str> = csv.lines().collect();
        assert_eq!(
            lines[0],
            "name,type_expr,source,confidence,axiom_bits,axiom_names,domain"
        );
        assert!(lines[1].starts_with("Nat.add,"));
        assert!(lines[2].starts_with("Bool.true,"));
    }

    #[test]
    fn test_export_to_csv_escaping() {
        let record = ExportRecord {
            name: "name,with,commas".to_string(),
            type_expr: "type \"quoted\"".to_string(),
            source: "Lean4".to_string(),
            confidence: "KernelVerified".to_string(),
            axiom_bits: 0,
            axiom_names: vec![],
            proof_sketch: None,
            deps: None,
            domain: Some("PureMath".to_string()),
        };
        let mut buf = Vec::new();
        export_to_csv(&mut buf, &[record]).unwrap();
        let csv = String::from_utf8(buf).unwrap();
        let data_line = csv.lines().nth(1).unwrap();
        assert!(data_line.contains("\"name,with,commas\""));
        assert!(data_line.contains("\"type \"\"quoted\"\"\""));
    }

    #[test]
    fn test_export_to_csv_empty() {
        let mut buf = Vec::new();
        let count = export_to_csv(&mut buf, &[]).unwrap();
        assert_eq!(count, 0);
        let csv = String::from_utf8(buf).unwrap();
        assert_eq!(csv.lines().count(), 1);
    }

    #[test]
    fn test_export_statistics_summary() {
        let mut stats = ExportStats {
            total_eligible: 100,
            exported: 80,
            filtered_by_trust: 10,
            filtered_by_axioms: 5,
            filtered_by_source: 3,
            filtered_by_domain: 2,
            ..Default::default()
        };
        stats.by_source.insert("Lean4".to_string(), 60);
        stats.by_source.insert("Coq".to_string(), 20);
        stats.by_confidence.insert("KernelVerified".to_string(), 60);
        stats.by_confidence.insert("Translated".to_string(), 20);

        let summary = export_statistics_summary(&stats);
        assert!(summary.contains("Total eligible:     100"));
        assert!(summary.contains("Exported:           80"));
        assert!(summary.contains("Filtered by trust:  10"));
        assert!(summary.contains("Lean4: 60"));
        assert!(summary.contains("Coq: 20"));
        assert!(summary.contains("KernelVerified: 60"));
    }

    #[test]
    fn test_export_statistics_summary_empty() {
        let stats = ExportStats::default();
        let summary = export_statistics_summary(&stats);
        assert!(summary.contains("Total eligible:     0"));
        assert!(summary.contains("Exported:           0"));
        assert!(!summary.contains("By source:"));
    }

    #[test]
    fn test_export_filter_builder() {
        let filter = ExportFilter::new()
            .source_systems(&[SS::Lean4])
            .min_confidence(IC::Translated)
            .domains(&[PM])
            .max_axiom_bits(0)
            .build();

        assert_eq!(filter.source_systems.as_ref().unwrap(), &[SS::Lean4]);
        assert_eq!(filter.min_confidence, Some(IC::Translated));
        assert_eq!(filter.domains.as_ref().unwrap(), &[PM]);
        assert_eq!(filter.max_axiom_bits, Some(0));
    }

    #[test]
    fn test_export_filter_matches() {
        let l = lib(&[
            mk("lean_pure", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("coq_pure", SS::Coq, KV, PM, AxiomProfile::NONE),
            mk("lean_sw", SS::Lean4, KV, CD::Software, AxiomProfile::NONE),
            mk("lean_axiom", SS::Lean4, KV, PM, AxiomProfile::CHOICE),
            mk(
                "isabelle_uv",
                SS::Isabelle,
                IC::Unverified,
                PM,
                AxiomProfile::NONE,
            ),
        ]);

        let f_lean = ExportFilter::new().source_systems(&[SS::Lean4]).build();
        assert!(f_lean.matches(l.get_constant(0).unwrap()));
        assert!(!f_lean.matches(l.get_constant(1).unwrap()));
        assert!(f_lean.matches(l.get_constant(2).unwrap()));

        let f_math = ExportFilter::new().domains(&[PM]).build();
        assert!(f_math.matches(l.get_constant(0).unwrap()));
        assert!(!f_math.matches(l.get_constant(2).unwrap()));

        let f_pure = ExportFilter::new().max_axiom_bits(0).build();
        assert!(f_pure.matches(l.get_constant(0).unwrap()));
        assert!(!f_pure.matches(l.get_constant(3).unwrap()));

        let f_conf = ExportFilter::new().min_confidence(IC::Translated).build();
        assert!(f_conf.matches(l.get_constant(0).unwrap()));
        assert!(f_conf.matches(l.get_constant(1).unwrap()));
        assert!(!f_conf.matches(l.get_constant(4).unwrap()));

        let f_all = ExportFilter::default();
        for i in 0..5 {
            assert!(
                f_all.matches(l.get_constant(i).unwrap()),
                "default filter should match idx {i}"
            );
        }
    }

    #[test]
    fn test_export_filter_combined() {
        let l = lib(&[
            mk("lean_pm", SS::Lean4, KV, PM, AxiomProfile::NONE),
            mk("lean_sw", SS::Lean4, KV, CD::Software, AxiomProfile::NONE),
            mk(
                "coq_pm",
                SS::Coq,
                IC::Translated,
                PM,
                AxiomProfile::BRIDGE_AXIOM,
            ),
        ]);

        let f = ExportFilter::new()
            .source_systems(&[SS::Lean4])
            .domains(&[PM])
            .max_axiom_bits(0)
            .build();
        assert!(f.matches(l.get_constant(0).unwrap()));
        assert!(!f.matches(l.get_constant(1).unwrap()));
        assert!(!f.matches(l.get_constant(2).unwrap()));
    }

    #[test]
    fn test_csv_escape_edge_cases() {
        assert_eq!(csv_escape("simple"), "simple");
        assert_eq!(csv_escape("has,comma"), "\"has,comma\"");
        assert_eq!(csv_escape("has\"quote"), "\"has\"\"quote\"");
        assert_eq!(csv_escape("has\nnewline"), "\"has\nnewline\"");
        assert_eq!(csv_escape(""), "");
        assert_eq!(csv_escape("a,b\"c\nd"), "\"a,b\"\"c\nd\"");
    }
}

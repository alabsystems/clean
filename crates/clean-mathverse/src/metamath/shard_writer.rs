// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shard writer for Metamath `.mm` databases.
//!
//! Converts a parsed [`MmDatabase`] into an `.mathverse` shard with proper
//! constant headers, ZFC axiom profile bits, and metadata sidecar.
//!
//! Metamath's `set.mm` is built on ZFC set theory. We tag all imported
//! constants with the `CHOICE | LEM` axiom profile (classical logic + AC),
//! which is the standard profile for ZFC-based mathematics.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use clean_kernel::flat::FlatExpr;

use crate::error::MathverseResult;
use crate::shard::ShardWriter;
use crate::shard_metadata::{DeclKind, MetadataEntry, ShardMetadata};
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind as HeaderDeclKind, ImportConfidence,
    MathverseConstantHeader, SourceSystem, NO_VALUE,
};

use super::types::{MmDatabase, MmImportStats, MmProofFormat, MmStatementKind};

// ════════════════════════════════════════════════════════════════════════════
// Shard statistics
// ════════════════════════════════════════════════════════════════════════════

/// Statistics returned after writing a Metamath database to a shard.
#[derive(Debug, Clone, Default)]
pub struct ShardStats {
    /// Axiom entries written.
    pub axioms_written: usize,
    /// Theorem entries written.
    pub theorems_written: usize,
    /// Hypothesis entries written.
    pub hypotheses_written: usize,
    /// Total entries written.
    pub total_written: usize,
}

// ════════════════════════════════════════════════════════════════════════════
// Axiom profile for Metamath/ZFC
// ════════════════════════════════════════════════════════════════════════════

/// Default axiom profile for Metamath's set.mm: classical logic + choice.
///
/// set.mm is built on ZFC which requires the axiom of choice and the law
/// of excluded middle (classical logic).
#[must_use]
pub(crate) fn zfc_axiom_profile() -> AxiomProfile {
    AxiomProfile::new(AxiomProfile::CHOICE.0 | AxiomProfile::LEM.0)
}

/// Axiom-profile bits contributed by a single Metamath axiom label.
///
/// Maps set.mm's non-constructive axioms to their [`AxiomProfile`] bits: `ax-3`
/// (the classical double-negation / excluded-middle axiom) contributes `LEM`,
/// and the choice axioms (`ax-ac`/`ax-ac2`/`ax-ac3`/`ax-cc`/`ax-dc`) contribute
/// `CHOICE`. Every other axiom — and constructive databases such as iset.mm,
/// which omit `ax-3` — contributes nothing. Comparison is case-insensitive.
///
/// This is intentionally a superset-conservative allow-list keyed to the
/// standard set.mm/iset.mm axiom names: an axiom *not* listed here contributes
/// no non-constructive bits, so a database using a differently-named choice or
/// classical axiom would need an entry added. The profile is import metadata
/// (which axioms a theorem's proof depends on), not a proof-checking gate.
fn metamath_axiom_bits(label: &str) -> u64 {
    let l = label.to_ascii_lowercase();
    let mut bits = 0u64;
    if l == "ax-3" {
        bits |= AxiomProfile::LEM.0;
    }
    if matches!(
        l.as_str(),
        "ax-ac" | "ax-ac2" | "ax-ac3" | "ax-cc" | "ax-dc"
    ) {
        bits |= AxiomProfile::CHOICE.0;
    }
    bits
}

/// Compute each statement's **transitive** axiom-dependency profile.
///
/// Metamath labels are declared before use and proofs form a DAG, so a single
/// forward pass over `db.statements` (which are in declaration order) suffices:
/// an axiom seeds its own bits ([`metamath_axiom_bits`]); a theorem's profile is
/// the union over every assertion label its proof references, each of which is
/// already resolved earlier in the pass. Referenced labels are the proof's step
/// labels (normal proof) or the parenthesized label list (compressed proof — the
/// encoded step-index tail is dropped). Hypotheses contribute nothing. The
/// result is keyed by statement label.
///
/// This replaces the coarse database-wide [`zfc_axiom_profile`] with an accurate
/// per-theorem one: a set.mm theorem proved without the axiom of choice gets no
/// `CHOICE` bit, and a theorem that avoids classical logic gets no `LEM` bit.
#[must_use]
fn compute_mm_axiom_profiles(db: &MmDatabase) -> HashMap<String, u64> {
    let mut profiles: HashMap<String, u64> = HashMap::with_capacity(db.statements.len());
    for stmt in &db.statements {
        match stmt.kind {
            MmStatementKind::Axiom => {
                profiles.insert(stmt.label.clone(), metamath_axiom_bits(&stmt.label));
            }
            MmStatementKind::Theorem => {
                let mut bits = metamath_axiom_bits(&stmt.label);
                if let Some(proof) = &stmt.proof {
                    let refs: &[String] = match proof.format {
                        MmProofFormat::Normal => &proof.steps,
                        // Compressed: steps are [paren labels..., encoded]; the
                        // referenced assertions are exactly the paren labels.
                        MmProofFormat::Compressed => {
                            proof.steps.split_last().map_or(&[][..], |(_, rest)| rest)
                        }
                    };
                    for r in refs {
                        if let Some(&child) = profiles.get(r) {
                            bits |= child;
                        }
                    }
                }
                profiles.insert(stmt.label.clone(), bits);
            }
            MmStatementKind::FloatingHyp | MmStatementKind::EssentialHyp => {}
        }
    }
    profiles
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Write a Metamath database to a shard file at `output_path`.
///
/// Creates both `output_path` (the `.mathverse` binary shard) and
/// `output_path.json` (the metadata sidecar).
///
/// Each axiom and theorem produces one shard entry. Floating and essential
/// hypotheses are also written as auxiliary declarations.
///
/// # Errors
///
/// Returns an error if the shard cannot be written to disk.
pub fn write_mm_to_shard(
    db: &MmDatabase,
    verified: &HashSet<String>,
    output_path: &Path,
) -> MathverseResult<ShardStats> {
    let mut writer = ShardWriter::new();
    let mut metadata = ShardMetadata::new("Metamath");
    let mut stats = ShardStats::default();

    write_database_to_writer(db, verified, &mut writer, &mut metadata, &mut stats);

    // Write the shard binary.
    let mut shard_bytes = Vec::new();
    writer.write(&mut shard_bytes)?;
    std::fs::write(output_path, &shard_bytes)?;

    // Write the metadata sidecar.
    crate::shard_metadata::write_metadata(output_path, &metadata)?;

    Ok(stats)
}

/// Write a Metamath database to a [`ShardWriter`] without touching disk.
///
/// Useful for integration with other importers that combine multiple sources
/// into a single shard.
pub fn write_mm_to_writer(
    db: &MmDatabase,
    verified: &HashSet<String>,
    writer: &mut ShardWriter,
) -> MmImportStats {
    let mut metadata = ShardMetadata::new("Metamath");
    let mut stats = ShardStats::default();

    write_database_to_writer(db, verified, writer, &mut metadata, &mut stats);

    MmImportStats {
        constant_count: db.constants.len(),
        variable_count: db.variables.len(),
        axiom_count: stats.axioms_written,
        theorem_count: stats.theorems_written,
        float_hyp_count: db.float_hyp_count(),
        essential_hyp_count: db.essential_hyp_count(),
        entries_written: stats.total_written,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Internal
// ════════════════════════════════════════════════════════════════════════════

/// Write all statements from the database to a shard writer.
fn write_database_to_writer(
    db: &MmDatabase,
    verified: &HashSet<String>,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
    stats: &mut ShardStats,
) {
    // Per-statement axiom profiles via transitive proof closure — replaces the
    // coarse database-wide CHOICE|LEM tag (zfc_axiom_profile) so each theorem
    // honestly carries only the non-constructive axioms its proof depends on.
    // A label absent from the map (e.g. a hypothesis) carries the empty profile.
    let profiles = compute_mm_axiom_profiles(db);
    let profile_of = |label: &str| AxiomProfile::new(profiles.get(label).copied().unwrap_or(0));
    let source_system = SourceSystem::Metamath as u8;

    for stmt in &db.statements {
        match stmt.kind {
            MmStatementKind::Axiom => {
                write_axiom_entry(
                    stmt,
                    source_system,
                    profile_of(&stmt.label),
                    writer,
                    metadata,
                );
                stats.axioms_written += 1;
                stats.total_written += 1;
            }
            MmStatementKind::Theorem => {
                write_theorem_entry(
                    stmt,
                    source_system,
                    profile_of(&stmt.label),
                    verified,
                    writer,
                    metadata,
                );
                stats.theorems_written += 1;
                stats.total_written += 1;
            }
            MmStatementKind::FloatingHyp | MmStatementKind::EssentialHyp => {
                write_hypothesis_entry(
                    stmt,
                    source_system,
                    profile_of(&stmt.label),
                    writer,
                    metadata,
                );
                stats.hypotheses_written += 1;
                stats.total_written += 1;
            }
        }
    }
}

/// Write an axiom (`$a`) as a shard entry.
fn write_axiom_entry(
    stmt: &super::types::MmStatement,
    source_system: u8,
    profile: AxiomProfile,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name = format!("mm.{}", stmt.label);
    let name_idx = writer.add_string(&name);

    let type_sig = stmt.expression.to_string_repr();
    let type_str_idx = writer.add_string(&type_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(type_str_idx));

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE, // axiom: no proof term
        source_system,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: HeaderDeclKind::Axiom as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name,
        kind: Some(DeclKind::Axiom),
        type_signature: Some(type_sig),
        source_file: None,
        line_number: None,
    });
}

/// Write a theorem (`$p`) as a shard entry.
fn write_theorem_entry(
    stmt: &super::types::MmStatement,
    source_system: u8,
    profile: AxiomProfile,
    verified: &HashSet<String>,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name = format!("mm.{}", stmt.label);
    let name_idx = writer.add_string(&name);

    let type_sig = stmt.expression.to_string_repr();
    let type_str_idx = writer.add_string(&type_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(type_str_idx));

    // Encode the proof value. For NORMAL proofs, build a structured App/Const
    // spine over the RPN step labels — each label becomes a const ref to the
    // sibling `mm.<label>` declaration — so the value is a real proof-skeleton
    // term in the expr arena that cross-references its premises, not an opaque
    // string blob. Compressed proofs (a packed step encoding, not plain labels)
    // keep the string form. (Structural import only — not yet kernel-rechecked.)
    let value_idx = match &stmt.proof {
        Some(proof) if proof.format == MmProofFormat::Normal => {
            let mut spine: Option<u32> = None;
            for label in &proof.steps {
                let leaf_name_idx = writer.add_string(&format!("mm.{label}"));
                let leaf = writer.add_expr(FlatExpr::const_ref(leaf_name_idx, u32::MAX));
                spine = Some(match spine {
                    None => leaf,
                    Some(acc) => writer.add_expr(FlatExpr::app(acc, leaf)),
                });
            }
            spine.unwrap_or(NO_VALUE)
        }
        Some(proof) => {
            let proof_str = proof.steps.join(" ");
            let proof_str_idx = writer.add_string(&proof_str);
            writer.add_expr(FlatExpr::lit_str(proof_str_idx))
        }
        None => NO_VALUE,
    };

    // Theorems whose RPN proof was checked by Metamath's own verifier get
    // `SourceVerified`; the rest (compressed/unverified proofs) stay `Translated`.
    let import_confidence = if verified.contains(&stmt.label) {
        ImportConfidence::SourceVerified as u8
    } else {
        ImportConfidence::Translated as u8
    };
    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system,
        import_confidence,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: HeaderDeclKind::Theorem as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name,
        kind: Some(DeclKind::Theorem),
        type_signature: Some(type_sig),
        source_file: None,
        line_number: None,
    });
}

/// Write a hypothesis (`$f` or `$e`) as a shard entry.
fn write_hypothesis_entry(
    stmt: &super::types::MmStatement,
    source_system: u8,
    profile: AxiomProfile,
    writer: &mut ShardWriter,
    metadata: &mut ShardMetadata,
) {
    let name = format!("mm.{}", stmt.label);
    let name_idx = writer.add_string(&name);

    let type_sig = stmt.expression.to_string_repr();
    let type_str_idx = writer.add_string(&type_sig);
    let type_idx = writer.add_expr(FlatExpr::lit_str(type_str_idx));

    // Classify the hypothesis: floating hypotheses introduce typed variables
    // (definitional), essential hypotheses assert propositions (axiomatic).
    let (header_kind, kind) = match stmt.kind {
        MmStatementKind::FloatingHyp => (HeaderDeclKind::Definition, DeclKind::Definition),
        MmStatementKind::EssentialHyp => (HeaderDeclKind::Axiom, DeclKind::Axiom),
        _ => (HeaderDeclKind::Axiom, DeclKind::Axiom),
    };

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: type_idx, // hypothesis: value = type (declaration)
        source_system,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: header_kind as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    writer.add_constant(header);

    metadata.push(MetadataEntry {
        name,
        kind: Some(kind),
        type_signature: Some(type_sig),
        source_file: None,
        line_number: None,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::parser::parse_mm;

    #[test]
    fn test_zfc_axiom_profile_has_choice_and_lem() {
        let profile = zfc_axiom_profile();
        assert!(profile.has(AxiomProfile::CHOICE));
        assert!(profile.has(AxiomProfile::LEM));
        assert!(!profile.has(AxiomProfile::FLOAT_APPROX));
    }

    #[test]
    fn test_per_theorem_axiom_profiles_are_accurate_and_transitive() {
        use crate::metamath::types::{MmExpression, MmProof, MmStatement};

        let stmt = |label: &str, kind, proof| MmStatement {
            label: label.to_string(),
            kind,
            expression: MmExpression { tokens: Vec::new() },
            proof,
            hypotheses: Vec::new(),
        };
        let normal = |steps: &[&str]| {
            Some(MmProof {
                format: MmProofFormat::Normal,
                steps: steps.iter().map(|s| (*s).to_string()).collect(),
            })
        };

        let mut db = MmDatabase::default();
        // Two seed axioms: one choice axiom, one ordinary axiom.
        db.statements
            .push(stmt("ax-ac", MmStatementKind::Axiom, None));
        db.statements
            .push(stmt("ax-1", MmStatementKind::Axiom, None));
        // Direct dependant of the choice axiom -> CHOICE.
        db.statements.push(stmt(
            "thm_choice",
            MmStatementKind::Theorem,
            normal(&["ax-ac"]),
        ));
        // Choice-free theorem -> no CHOICE bit (the whole point vs blanket tagging).
        db.statements.push(stmt(
            "thm_plain",
            MmStatementKind::Theorem,
            normal(&["ax-1"]),
        ));
        // Transitive dependant: references thm_choice, so inherits CHOICE.
        db.statements.push(stmt(
            "thm_downstream",
            MmStatementKind::Theorem,
            normal(&["thm_plain", "thm_choice"]),
        ));

        let profiles = compute_mm_axiom_profiles(&db);
        let bits = |label: &str| *profiles.get(label).expect("label present in profile map");
        let choice = AxiomProfile::CHOICE.0;

        assert_eq!(bits("ax-ac") & choice, choice, "choice axiom seeds CHOICE");
        assert_eq!(bits("ax-1") & choice, 0, "ordinary axiom carries no CHOICE");
        assert_eq!(
            bits("thm_choice") & choice,
            choice,
            "direct dependant of choice axiom carries CHOICE"
        );
        assert_eq!(
            bits("thm_plain") & choice,
            0,
            "choice-free theorem must NOT be tagged CHOICE (honest profile)"
        );
        assert_eq!(
            bits("thm_downstream") & choice,
            choice,
            "CHOICE propagates transitively through proof dependencies"
        );
    }

    #[test]
    fn test_write_mm_to_writer_empty_db() {
        let db = MmDatabase::default();
        let mut writer = ShardWriter::new();
        let stats = write_mm_to_writer(&db, &HashSet::new(), &mut writer);
        assert_eq!(stats.entries_written, 0);
        assert_eq!(stats.axiom_count, 0);
        assert_eq!(stats.theorem_count, 0);
    }

    #[test]
    fn test_write_mm_to_writer_basic() {
        let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
mp $e |- ph $.
a1i $p |- ( ps -> ph ) $= wph wps ax-1 mp $.";
        let db = parse_mm(input).expect("parse");
        let mut writer = ShardWriter::new();
        let stats = write_mm_to_writer(&db, &HashSet::new(), &mut writer);

        assert_eq!(stats.axiom_count, 1);
        assert_eq!(stats.theorem_count, 1);
        assert_eq!(stats.float_hyp_count, 2);
        assert_eq!(stats.essential_hyp_count, 1);
        // 2 float hyps + 1 axiom + 1 essential hyp + 1 theorem = 5
        assert_eq!(stats.entries_written, 5);
    }

    #[test]
    fn test_write_mm_to_shard_creates_files() {
        let input = "$c wff |- $.
$v ph $.
wph $f wff ph $.
ax-1 $a |- ph $.";
        let db = parse_mm(input).expect("parse");

        let dir = std::env::temp_dir().join("clean_mm_test");
        let _ = std::fs::create_dir_all(&dir);
        let shard_path = dir.join("test_mm.mathverse");

        let stats = write_mm_to_shard(&db, &HashSet::new(), &shard_path).expect("write shard");
        assert_eq!(stats.total_written, 2); // 1 float hyp + 1 axiom

        // Verify both files exist
        assert!(shard_path.exists());
        assert!(shard_path.with_extension("mathverse.json").exists());

        // clean up
        let _ = std::fs::remove_file(&shard_path);
        let _ = std::fs::remove_file(shard_path.with_extension("mathverse.json"));
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_shard_metadata_names_prefixed() {
        let input = "$c wff |- $.
$v ph $.
wph $f wff ph $.
ax-1 $a |- ph $.";
        let db = parse_mm(input).expect("parse");
        let mut writer = ShardWriter::new();
        let mut metadata = ShardMetadata::new("Metamath");
        let mut stats = ShardStats::default();

        write_database_to_writer(&db, &HashSet::new(), &mut writer, &mut metadata, &mut stats);

        assert_eq!(metadata.declarations.len(), 2);
        assert!(metadata
            .declarations
            .iter()
            .all(|d| d.name.starts_with("mm.")));
        assert_eq!(metadata.declarations[0].name, "mm.wph");
        assert_eq!(metadata.declarations[1].name, "mm.ax-1");
    }

    /// Regression for #3522: Metamath shard headers must carry the correct
    /// `decl_kind` derived from `MmStatementKind`, not the hardcoded 0 byte.
    #[test]
    fn test_metamath_shard_decl_kind_round_trip() {
        use crate::shard::ShardReader;

        let input = "$c wff |- $.
$v ph ps $.
wph $f wff ph $.
hyp-e $e |- ph $.
ax-1 $a |- ( ph -> ph ) $.
thm-1 $p |- ph $= wph hyp-e $.";
        let db = parse_mm(input).expect("parse");
        let mut writer = ShardWriter::new();
        let stats = write_mm_to_writer(&db, &HashSet::new(), &mut writer);
        assert_eq!(stats.axiom_count, 1);
        assert_eq!(stats.theorem_count, 1);
        assert_eq!(stats.float_hyp_count, 1);
        assert_eq!(stats.essential_hyp_count, 1);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");

        // Axiom ($a) -> DeclKind::Axiom.
        let (_, hdr) = reader.lookup_name("mm.ax-1").expect("ax-1");
        assert_eq!(hdr.decl_kind, HeaderDeclKind::Axiom as u8);

        // Theorem ($p) -> DeclKind::Theorem.
        let (_, hdr) = reader.lookup_name("mm.thm-1").expect("thm-1");
        assert_eq!(hdr.decl_kind, HeaderDeclKind::Theorem as u8);

        // Floating hypothesis ($f) -> DeclKind::Definition (typed variable).
        let (_, hdr) = reader.lookup_name("mm.wph").expect("wph");
        assert_eq!(hdr.decl_kind, HeaderDeclKind::Definition as u8);

        // Essential hypothesis ($e) -> DeclKind::Axiom (asserted proposition).
        let (_, hdr) = reader.lookup_name("mm.hyp-e").expect("hyp-e");
        assert_eq!(hdr.decl_kind, HeaderDeclKind::Axiom as u8);

        // Non-theorem entries must not retain the legacy 0 default that
        // would misread them as `DeclKind::Theorem`.
        let (_, wph_hdr) = reader.lookup_name("mm.wph").expect("wph");
        assert_ne!(wph_hdr.decl_kind, HeaderDeclKind::Theorem as u8);
    }

    #[test]
    fn test_rpn_verified_theorem_marked_source_verified() {
        use crate::shard::ShardReader;
        use crate::types::ImportConfidence;
        let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
mp $e |- ph $.
a1i $p |- ( ps -> ph ) $= wph wps ax-1 mp $.";
        let db = parse_mm(input).expect("parse");

        let confidence_of = |verified: &HashSet<String>| -> u8 {
            let mut writer = ShardWriter::new();
            write_mm_to_writer(&db, verified, &mut writer);
            let mut buf = Vec::new();
            writer.write(&mut buf).expect("write");
            let reader = ShardReader::from_bytes(&buf).expect("read");
            reader
                .lookup_name("mm.a1i")
                .expect("a1i")
                .1
                .import_confidence
        };

        // A theorem whose RPN proof verified -> SourceVerified (checked by
        // Metamath's own verifier), not merely Translated.
        let mut verified = HashSet::new();
        verified.insert("a1i".to_string());
        assert_eq!(
            confidence_of(&verified),
            ImportConfidence::SourceVerified as u8,
            "RPN-verified theorem should be SourceVerified"
        );

        // Not verified -> stays Translated.
        assert_eq!(
            confidence_of(&HashSet::new()),
            ImportConfidence::Translated as u8,
            "unverified theorem should stay Translated"
        );
    }
}

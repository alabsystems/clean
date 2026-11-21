// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The figure registry: one entry per figure, with the adapter that reads its
//! existing record. `list`, `check`, `status` and `explain` all dispatch here.

use super::checker_source::{CHECKER_SOURCES, CHECKER_SOURCE_FIGURE};
use super::contracted::{NATIVE_EXEC, NATIVE_EXEC_FIGURE, TACTIC_PARITY, TACTIC_PARITY_FIGURE};
use super::elaboration::{ELABORATION_BASELINE, ELABORATION_FIGURE};
use super::evaluate::STALE_FIGURE;
use super::island_gaps::{ISLAND_GAPS, ISLAND_GAPS_FIGURE};
use super::k3_scoreboard::{ACCEPTED_FIGURE, DECIDED_FIGURE};
use super::lean_families::{LEAN_FAMILIES_FIGURE, RULE_RATCHET};
use super::provenance::ReportProvenance;
use super::python_minters;
use super::reading::Outcome;
use super::rule_families::{RULE_FAMILIES_FIGURE, RULE_INVENTORY};
use super::seams::{ROUTE_LANES_FIGURE, ROUTE_LANES_INPUTS, SEAMS_FIGURE, SEAMS_TOML};
use super::source_elab::{SOURCE_ELAB_FIGURE, SOURCE_ELAB_RATCHET};
use super::suite::{SUITE_FIGURE, SUITE_STATE};
use super::trustcore_receipts::{TRUSTCORE_FIGURE, TRUSTCORE_INPUTS};
use super::{checker_source, elaboration, rule_families};
use super::{
    clean_p3, contracted, evaluate, historical, island_gaps, k3_reading, k3_scoreboard,
    lean_families, provenance, seams, source_elab, suite, trustcore_receipts,
};
use super::{CLEAN_FIGURE, CLEAN_PINS, SCOREBOARD, TRUST_FIGURE, TRUST_PINS};
use crate::EvidenceCheckError;
use clean_evidence::envelope::python_minters as python_tooling;
use serde::Serialize;
use std::path::Path;

type Reader = fn(&Path) -> Result<Outcome, EvidenceCheckError>;
type ProvenanceReader = fn(&Path) -> Result<ReportProvenance, EvidenceCheckError>;

#[derive(Serialize)]
#[serde(untagged)]
enum FigureSource {
    Record {
        #[serde(skip)]
        read: Reader,
    },
    Absent {
        absent_reason: &'static str,
    },
}

#[derive(Serialize)]
pub(super) struct Figure {
    pub(super) id: &'static str,
    pub(super) plan_unit: &'static str,
    pub(super) producer_module: Option<&'static str>,
    pub(super) input_scope: &'static [&'static str],
    pub(super) cost_class: &'static str,
    pub(super) headline: bool,
    pub(super) ratchet_direction: Option<&'static str>,
    pub(super) lane: &'static str,
    pub(super) historical: bool,
    #[serde(flatten)]
    source: FigureSource,
    /// Recorded provenance beyond the reading, where the record has more.
    #[serde(skip)]
    pub(super) provenance: Option<ProvenanceReader>,
}

impl Figure {
    pub(super) fn read(&self, root: &Path) -> Result<Outcome, EvidenceCheckError> {
        match self.source {
            FigureSource::Record { read } => read(root),
            FigureSource::Absent { absent_reason } => Ok(Outcome::Absent {
                reason: absent_reason.to_owned(),
            }),
        }
    }

    pub(super) fn absent_reason(&self) -> Option<&'static str> {
        match self.source {
            FigureSource::Absent { absent_reason } => Some(absent_reason),
            FigureSource::Record { .. } => None,
        }
    }
}

/// Defaults shared by every offline record reader.
const fn figure(
    id: &'static str,
    plan_unit: &'static str,
    lane: &'static str,
    read: Reader,
) -> Figure {
    Figure {
        id,
        plan_unit,
        producer_module: None,
        input_scope: &[],
        cost_class: "offline",
        headline: false,
        ratchet_direction: None,
        lane,
        historical: true,
        source: FigureSource::Record { read },
        provenance: None,
    }
}

const fn absent(
    id: &'static str,
    plan_unit: &'static str,
    lane: &'static str,
    absent_reason: &'static str,
) -> Figure {
    Figure {
        id,
        plan_unit,
        producer_module: None,
        input_scope: &[],
        cost_class: "offline",
        headline: true,
        ratchet_direction: None,
        lane,
        historical: false,
        source: FigureSource::Absent { absent_reason },
        provenance: None,
    }
}

const TRUST_MODEL_RECORD: &str = "Trust's census verb in wave 6 owes the canonical model record";

pub(super) const FIGURES: &[Figure] = &[
    Figure {
        input_scope: k3_scoreboard::INPUTS,
        producer_module: Some("scripts/kcheck_coverage.py"),
        headline: true,
        provenance: Some(k3_scoreboard::read_provenance),
        ..figure(DECIDED_FIGURE, "K3", "K", k3_reading::decided)
    },
    Figure {
        input_scope: k3_scoreboard::INPUTS,
        producer_module: Some("scripts/kcheck_coverage.py"),
        provenance: Some(k3_scoreboard::read_provenance),
        ..figure(ACCEPTED_FIGURE, "K3", "K", k3_reading::accepted)
    },
    Figure {
        producer_module: Some("scripts/patched_kernel_control.py"),
        input_scope: &[CLEAN_PINS, SCOREBOARD],
        headline: true,
        provenance: Some(clean_p3::read_provenance),
        ..figure(CLEAN_FIGURE, "P3", "P", historical::planted_false_clean)
    },
    Figure {
        producer_module: Some("scripts/patched_kernel_control_trust.py"),
        input_scope: &[TRUST_PINS, SCOREBOARD],
        headline: true,
        provenance: Some(provenance::read_trust),
        ..figure(TRUST_FIGURE, "P3", "P", historical::planted_false_trust)
    },
    Figure {
        input_scope: &[ISLAND_GAPS, SCOREBOARD],
        provenance: Some(island_gaps::read_provenance),
        ..figure(ISLAND_GAPS_FIGURE, "W2", "W", historical::island_gaps)
    },
    Figure {
        producer_module: Some("scripts/self_proof_elab_probe.py"),
        input_scope: &[ELABORATION_BASELINE, SCOREBOARD],
        provenance: Some(elaboration::read_provenance),
        ..figure(
            ELABORATION_FIGURE,
            "E4",
            "E",
            historical::theories_elaborated,
        )
    },
    Figure {
        input_scope: &[RULE_INVENTORY, SCOREBOARD],
        provenance: Some(rule_families::read_provenance),
        ..figure(
            RULE_FAMILIES_FIGURE,
            "S7",
            "S",
            historical::lean_kernel_rule_families,
        )
    },
    Figure {
        producer_module: Some("scripts/check_cic_l_rule_inventory.py"),
        input_scope: &[RULE_INVENTORY, RULE_RATCHET],
        headline: true,
        ratchet_direction: Some("falls"),
        provenance: Some(rule_families::read_provenance),
        ..figure(LEAN_FAMILIES_FIGURE, "EV5", "S", lean_families::read)
    },
    Figure {
        producer_module: Some("scripts/self_proof_scoreboard.py"),
        input_scope: &[CHECKER_SOURCES, SCOREBOARD],
        provenance: Some(checker_source::read_provenance),
        ..figure(
            CHECKER_SOURCE_FIGURE,
            "C3",
            "C",
            historical::checker_soundness,
        )
    },
    Figure {
        producer_module: Some("scripts/source_elab_gate.sh"),
        input_scope: &[SOURCE_ELAB_RATCHET],
        ratchet_direction: Some("rises"),
        ..figure(SOURCE_ELAB_FIGURE, "T4", "frontend", source_elab::read)
    },
    Figure {
        producer_module: Some("crates/clean/tests/native_exec_battery.rs"),
        input_scope: &[NATIVE_EXEC],
        ..figure(
            NATIVE_EXEC_FIGURE,
            "T4",
            "frontend",
            contracted::native_exec_battery,
        )
    },
    Figure {
        producer_module: Some("crates/clean-cli/src/cmd_replacement/generated_cases.rs"),
        input_scope: &[TACTIC_PARITY],
        ..figure(
            TACTIC_PARITY_FIGURE,
            "T4",
            "frontend",
            contracted::tactic_parity,
        )
    },
    Figure {
        producer_module: Some("scripts/verify_runner.py"),
        input_scope: &[SUITE_STATE],
        ..figure(SUITE_FIGURE, "T3", "suite", suite::read)
    },
    Figure {
        producer_module: Some("crates/clean-evidence/src/trustcore.rs"),
        input_scope: TRUSTCORE_INPUTS,
        historical: false,
        ..figure(TRUSTCORE_FIGURE, "EV0", "tooling", trustcore_receipts::read)
    },
    Figure {
        producer_module: Some(python_tooling::PRODUCER_SOURCE),
        input_scope: &[
            python_tooling::RECORD_PATH,
            python_tooling::TRACKED_INPUT,
            python_tooling::REGISTRY,
        ],
        headline: true,
        ratchet_direction: Some("falls"),
        historical: false,
        provenance: Some(python_minters::read_provenance),
        ..figure(
            python_tooling::FIGURE,
            "EV3",
            "tooling",
            python_minters::read,
        )
    },
    Figure {
        producer_module: Some("crates/clean-cli/src/cmd_evidence/evaluate.rs"),
        input_scope: &["every other registered figure"],
        headline: true,
        historical: false,
        ..figure(STALE_FIGURE, "EV1", "tooling", evaluate::stale_figures)
    },
    absent(
        "selfproof.planted_false.inside_fragment",
        "T7",
        "P",
        "the T7 Rust driver owes a planted-False site count split by fragment",
    ),
    absent(
        "alignment.functions",
        "Ph5",
        "alignment",
        "Ph5 owes the island build record and per-function alignment",
    ),
    Figure {
        ratchet_direction: Some("falls"),
        ..absent(
            "alignment.premises",
            "Ph7",
            "alignment",
            "Ph7 owes the aligned function premises from the island build record",
        )
    },
    absent(
        "alignment.instance",
        "AI",
        "alignment",
        "the AI unit owes the instance alignment record for the W4 island",
    ),
    absent(
        "lean_model.compiled_by_trust",
        "I.4",
        "compiled",
        "Trust's census verb owes the mounted modules and compiled body census",
    ),
    absent(
        "compiled.kcheck_bodies",
        "XK.3",
        "compiled",
        "XK.3 owes the checker body licence census",
    ),
    absent(
        "rust_to_trustir.functions_bound",
        "RB1",
        "RB",
        "the Trust census verb owes the function binding record from RB0 and RB1",
    ),
    absent(
        "island.pin_lag_commits",
        "I.4",
        "island",
        "Trust's census verb owes the measurement of its Clean pin",
    ),
    absent("model.rust.instg_in_semr", "I.4", "RM", TRUST_MODEL_RECORD),
    absent(
        "model.rust.minitests_in_core",
        "I.4",
        "RM",
        TRUST_MODEL_RECORD,
    ),
    absent(
        "model.rust.divergence_rows_with_lemma",
        "I.4",
        "RM",
        TRUST_MODEL_RECORD,
    ),
    absent(
        "model.rust.prod_equiv_bodies",
        "I.4",
        "RM",
        TRUST_MODEL_RECORD,
    ),
    absent("model.rust.rm_accept", "I.4", "RM", TRUST_MODEL_RECORD),
    absent(
        "model.trustir.referees",
        "D1",
        "model",
        "D1 and RM4+ owe the TrustIR referee record",
    ),
    absent(
        "diff.kernel",
        "S+",
        "S",
        "S+ owes a recorded differential kernel run",
    ),
    Figure {
        producer_module: Some("crates/clean-cli/src/cmd_evidence/seams.rs"),
        input_scope: &[SEAMS_TOML],
        headline: true,
        ratchet_direction: Some("rises"),
        historical: false,
        ..figure(SEAMS_FIGURE, "D4", "tooling", seams::read_seams)
    },
    Figure {
        producer_module: Some("crates/clean-cli/src/cmd_evidence/seams.rs"),
        input_scope: ROUTE_LANES_INPUTS,
        historical: false,
        ..figure(
            ROUTE_LANES_FIGURE,
            "EV6",
            "tooling",
            seams::read_route_lanes,
        )
    },
];

pub(super) fn find_figure(figure: &str) -> Result<&'static Figure, EvidenceCheckError> {
    FIGURES
        .iter()
        .find(|entry| entry.id == figure)
        .ok_or_else(|| {
            EvidenceCheckError::Usage(format!(
                "unknown evidence figure {figure:?}. \
                 Run `clean evidence list` for supported figures"
            ))
        })
}

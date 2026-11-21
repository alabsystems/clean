// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean evidence`: the figure registry, its per-schema read adapters over
//! existing records, the section-4 board, and offline checks.
//!
//! Exit codes of `check`: 0 ok, 1 red (an inconsistent or stale record),
//! 2 usage, 3 not knowable here (an input is unavailable).

mod age;
mod board;
mod catalog;
mod checker_source;
mod clean_p3;
mod contracted;
mod cpp_anchors;
mod elaboration;
mod evaluate;
mod git_record;
mod historical;
mod island_gaps;
mod k3_export;
mod k3_inputs;
mod k3_json;
mod k3_packet;
mod k3_reading;
mod k3_receipt;
mod k3_scoreboard;
mod k3_sources;
mod lean_families;
mod lean_rule_references;
mod measurement;
mod provenance;
mod python_minters;
mod reading;
mod rule_families;
mod rule_inventory;
mod seams;
mod source_elab;
mod status;
mod suite;
mod trustcore_receipts;
mod w0_scoreboard;

use crate::cli_args::K3PacketSyntaxArgs;
use crate::EvidenceCheckError;
use catalog::{find_figure, Figure, FIGURES};
use clean_evidence::envelope::FreshnessState;
use evaluate::evaluate;
use measurement::{Measurement, MeasurementProvenance};
use provenance::ReportProvenance;
use reading::Outcome;
use serde::de::{self, DeserializeOwned, MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use std::collections::{btree_map::Entry, BTreeMap, HashSet};
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::marker::PhantomData;
use std::path::Path;

const TRUST_FIGURE: &str = "selfproof.planted_false.trust";
const TRUST_PINS: &str = "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json";
const CLEAN_FIGURE: &str = "selfproof.planted_false.clean";
const CLEAN_PINS: &str = "reports/self-proof-p3-2026-11-12/patched_kernel_control.json";
const SCOREBOARD: &str = "data/self_proof_scoreboard.json";

#[derive(Deserialize)]
enum TrustPinsSchema {
    #[serde(rename = "clean.p3-trust-leg/v2")]
    V2,
}

#[derive(Deserialize)]
struct TrustPins {
    #[serde(rename = "schema")]
    _schema: TrustPinsSchema,
    measured_at: String,
    trust: TrustRevision,
    clean_pin_in_trust: String,
    #[serde(deserialize_with = "read_pin_groups")]
    pins: Vec<SitePin>,
}

#[derive(Deserialize)]
struct TrustRevision {
    commit: String,
}

#[derive(Deserialize)]
struct SitePin {
    site: String,
    mutant: MutantVerdict,
}

#[derive(Deserialize, PartialEq, Eq)]
enum MutantVerdict {
    Minted,
    Refused,
}

fn read_pin_groups<'de, D: Deserializer<'de>>(input: D) -> Result<Vec<SitePin>, D::Error> {
    struct PinGroups;

    impl<'de> Visitor<'de> for PinGroups {
        type Value = Vec<SitePin>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a map from test names to site pins")
        }

        fn visit_map<M: MapAccess<'de>>(self, mut groups: M) -> Result<Self::Value, M::Error> {
            let mut tests = HashSet::new();
            let mut pins = Vec::new();
            while let Some((test, test_pins)) = groups.next_entry::<String, Vec<SitePin>>()? {
                if !tests.insert(test.clone()) {
                    return Err(de::Error::custom(format!("duplicate test group {test:?}")));
                }
                pins.extend(test_pins);
            }
            Ok(pins)
        }
    }

    input.deserialize_map(PinGroups)
}

#[derive(Deserialize)]
enum ScoreboardSchema {
    #[serde(rename = "clean.self_proof_scoreboard.v1")]
    V1,
}

#[derive(Deserialize)]
struct Scoreboard<H> {
    #[serde(rename = "schema")]
    _schema: ScoreboardSchema,
    headline: H,
}

#[derive(Deserialize)]
struct RouteScoreboard<R> {
    #[serde(rename = "schema")]
    _schema: ScoreboardSchema,
    route: R,
}

#[derive(Deserialize)]
struct TrustHeadline {
    planted_false_mints_trust: TrustFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct TrustFigure {
    sites: usize,
    minted_under_mutant: usize,
    measured_at: String,
    source: String,
}

fn read_unique_map<'de, D, V>(
    input: D,
    description: &'static str,
) -> Result<BTreeMap<String, V>, D::Error>
where
    D: Deserializer<'de>,
    V: Deserialize<'de>,
{
    struct UniqueEntries<V> {
        description: &'static str,
        value_type: PhantomData<V>,
    }

    impl<'de, V: Deserialize<'de>> Visitor<'de> for UniqueEntries<V> {
        type Value = BTreeMap<String, V>;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "a map with unique {} keys", self.description)
        }

        fn visit_map<A: MapAccess<'de>>(self, mut input: A) -> Result<Self::Value, A::Error> {
            let mut entries = BTreeMap::new();
            while let Some((name, value)) = input.next_entry()? {
                match entries.entry(name) {
                    Entry::Vacant(entry) => {
                        entry.insert(value);
                    }
                    Entry::Occupied(entry) => {
                        return Err(de::Error::custom(format!(
                            "duplicate {} {:?}",
                            self.description,
                            entry.key()
                        )));
                    }
                }
            }
            Ok(entries)
        }
    }

    input.deserialize_map(UniqueEntries {
        description,
        value_type: PhantomData,
    })
}

fn read_json<T: DeserializeOwned>(root: &Path, path: &str) -> Result<T, EvidenceCheckError> {
    let path = root.join(path);
    let bytes = fs::read(&path)
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{}: {error}", path.display())))
}

fn trust_figure(report: &TrustPins) -> Result<TrustFigure, EvidenceCheckError> {
    if report.measured_at.trim().is_empty() || report.pins.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{TRUST_PINS} requires a measurement date and at least one site"
        )));
    }
    let mut sites = HashSet::new();
    let mut minted_under_mutant = 0;
    for pin in &report.pins {
        if pin.site.trim().is_empty() || !sites.insert(&pin.site) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{TRUST_PINS} has a blank or duplicate site name {:?}",
                pin.site
            )));
        }
        if pin.mutant == MutantVerdict::Minted {
            minted_under_mutant += 1;
        }
    }
    Ok(TrustFigure {
        sites: sites.len(),
        minted_under_mutant,
        measured_at: report.measured_at.clone(),
        source: TRUST_PINS.to_owned(),
    })
}

fn derive_trust(root: &Path) -> Result<(TrustFigure, TrustPins), EvidenceCheckError> {
    let report = read_json(root, TRUST_PINS)?;
    let figure = trust_figure(&report)?;
    Ok((figure, report))
}

fn measure_trust(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let (derived, report) = derive_trust(root)?;
    let scoreboard: Scoreboard<TrustHeadline> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.headline.planted_false_mints_trust;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} headline.planted_false_mints_trust differs from {TRUST_PINS}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::PlantedFalse {
        sites: derived.sites,
        minted_under_mutant: derived.minted_under_mutant,
        source: derived.source,
        provenance: MeasurementProvenance::Trust {
            measured_at: derived.measured_at,
            trust_commit: report.trust.commit,
            clean_pin_in_trust: report.clean_pin_in_trust,
        },
    })
}

pub(crate) fn list(json: bool) -> anyhow::Result<()> {
    let mut output = io::stdout().lock();
    if json {
        serde_json::to_writer_pretty(&mut output, FIGURES)?;
        writeln!(output)?;
    } else {
        for figure in FIGURES {
            writeln!(output, "{}", figure.id)?;
            writeln!(
                output,
                "  Plan {} (lane {}), {} check, headline {}, historical {}, ratchet {}",
                figure.plan_unit,
                figure.lane,
                figure.cost_class,
                figure.headline,
                figure.historical,
                figure.ratchet_direction.unwrap_or("none")
            )?;
            if let Some(reason) = figure.absent_reason() {
                writeln!(output, "  absent: {reason}")?;
                continue;
            }
            writeln!(
                output,
                "  Producer  {}",
                figure.producer_module.unwrap_or("manual inventory")
            )?;
            writeln!(output, "  Inputs    {}", figure.input_scope.join(", "))?;
        }
    }
    Ok(())
}

/// The verdict `check` gives one figure.
fn verdict(
    figure: &Figure,
    result: Result<Outcome, EvidenceCheckError>,
) -> Result<String, EvidenceCheckError> {
    match result? {
        Outcome::Absent { reason } => Ok(format!("{} — absent: {reason}", figure.id)),
        Outcome::Measured(reading) => {
            if reading.freshness.state == FreshnessState::Stale {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{} is stale against its inputs: {}",
                    figure.id, reading.freshness.reason
                )));
            }
            Ok(format!(
                "{} — {}; freshness {} ({})",
                figure.id,
                reading.summary,
                reading.freshness.label(),
                reading.freshness.reason
            ))
        }
    }
}

/// Check the named figures, or every registered figure. One figure keeps its
/// own error. Several print one line each and then exit with the worst
/// verdict: red before not knowable here.
pub(crate) fn run(figures: &[String], all: bool, repo_root: Option<&Path>) -> anyhow::Result<()> {
    let selected: Vec<&'static Figure> = if all {
        FIGURES.iter().collect()
    } else {
        figures
            .iter()
            .map(|figure| find_figure(figure))
            .collect::<Result<_, _>>()?
    };
    if selected.is_empty() {
        return Err(EvidenceCheckError::Usage("name a figure or pass --all".to_owned()).into());
    }
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    let verdicts: Vec<Result<String, EvidenceCheckError>> = selected
        .iter()
        .zip(evaluate(root, &selected))
        .map(|(figure, result)| verdict(figure, result))
        .collect();
    let mut output = io::stdout().lock();
    if let [_] = selected.as_slice() {
        for verdict in verdicts {
            writeln!(output, "{}", verdict?)?;
        }
        return Ok(());
    }
    let (mut red, mut unknowable) = (Vec::new(), Vec::new());
    for (figure, verdict) in selected.iter().zip(verdicts) {
        match verdict {
            Ok(line) => writeln!(output, "{line}")?,
            Err(EvidenceCheckError::Invalid(reason)) => {
                writeln!(output, "{} — RED: {}", figure.id, reason.escape_debug())?;
                red.push(figure.id);
            }
            Err(EvidenceCheckError::Unavailable(reason)) => {
                writeln!(
                    output,
                    "{} — not knowable here: {}",
                    figure.id,
                    reason.escape_debug()
                )?;
                unknowable.push(figure.id);
            }
            Err(error @ EvidenceCheckError::Usage(_)) => return Err(error.into()),
        }
    }
    let checked = selected.len();
    if !red.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{} of {checked} figures are red: {}",
            red.len(),
            red.join(", ")
        ))
        .into());
    }
    if !unknowable.is_empty() {
        return Err(EvidenceCheckError::Unavailable(format!(
            "{} of {checked} figures are not knowable here: {}",
            unknowable.len(),
            unknowable.join(", ")
        ))
        .into());
    }
    Ok(())
}

pub(crate) fn status(
    json: bool,
    markdown: Option<&Path>,
    scoreboard: bool,
    check: bool,
    write: bool,
    repo_root: Option<&Path>,
) -> anyhow::Result<()> {
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    if write {
        return w0_scoreboard::publish(root, &mut io::stdout().lock());
    }
    if check {
        return w0_scoreboard::check(root, &mut io::stdout().lock());
    }
    if scoreboard {
        return w0_scoreboard::write(root, json, &mut io::stdout().lock());
    }
    let rows = status::survey(root)?;
    if let Some(path) = markdown {
        let mut rendered = Vec::new();
        status::write_markdown(&rows, &mut rendered)?;
        fs::write(path, rendered)
            .map_err(|error| anyhow::anyhow!("cannot write {}: {error}", path.display()))?;
        println!("wrote {}", path.display());
        return Ok(());
    }
    let mut output = io::stdout().lock();
    if json {
        serde_json::to_writer_pretty(&mut output, &rows)?;
        writeln!(output)?;
        return Ok(());
    }
    status::write_text(&rows, &mut output)
}

pub(crate) fn check_k3_sources(repo_root: Option<&Path>) -> anyhow::Result<()> {
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    k3_sources::run(root).map_err(Into::into)
}

pub(crate) fn check_rule_lean_references(repo_root: Option<&Path>) -> anyhow::Result<()> {
    lean_rule_references::run(repo_root.unwrap_or_else(|| Path::new(".")))
}

pub(crate) fn check_rule_cpp_anchors(
    repo_root: Option<&Path>,
    coverage: bool,
) -> anyhow::Result<()> {
    cpp_anchors::run(repo_root.unwrap_or_else(|| Path::new(".")), coverage)
}

pub(crate) fn check_rule_inventory(
    repo_root: Option<&Path>,
    require_complete: bool,
) -> anyhow::Result<()> {
    rule_inventory::run(
        repo_root.unwrap_or_else(|| Path::new(".")),
        require_complete,
    )
}

pub(crate) fn check_k3_coverage(repo_root: Option<&Path>) -> anyhow::Result<()> {
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    k3_receipt::run(root, &mut io::stdout().lock())
}

pub(crate) fn check_k3_packet_syntax(args: K3PacketSyntaxArgs) -> anyhow::Result<()> {
    let root = args.repo_root.as_deref().unwrap_or_else(|| Path::new("."));
    let check = if args.coverage_figures {
        k3_packet::Check::CoverageFigures
    } else if args.check_dependency_refusals {
        k3_packet::Check::DependencyRefusals
    } else if args.check_fragment_classes {
        k3_packet::Check::FragmentClasses
    } else if args.check_base_families {
        k3_packet::Check::BaseFamilies
    } else if args.check_accepted_statements {
        k3_packet::Check::AcceptedStatements
    } else if args.check_declaration_names {
        k3_packet::Check::DeclarationNames
    } else if args.check_declaration_bodies {
        k3_packet::Check::DeclarationBodies
    } else if args.check_non_inductive_bodies {
        k3_packet::Check::NonInductiveBodies
    } else if args.check_declaration_index {
        k3_packet::Check::DeclarationIndex
    } else if args.check_consistency {
        k3_packet::Check::Consistency
    } else {
        k3_packet::Check::Syntax
    };
    k3_packet::run(root, args.json, check, &mut io::stdout().lock())
}

pub(crate) fn check_k3_export_syntax(
    check_names: bool,
    check_levels: bool,
    check_expressions: bool,
    repo_root: Option<&Path>,
) -> anyhow::Result<()> {
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    k3_export::run(root, check_names, check_levels, check_expressions).map_err(Into::into)
}

pub(crate) fn explain(figure: &str, repo_root: Option<&Path>) -> anyhow::Result<()> {
    let entry = find_figure(figure)?;
    let root = repo_root.unwrap_or_else(|| Path::new("."));
    provenance::write_explanation(entry, root, &mut io::stdout().lock())
}

#[cfg(test)]
mod tests;

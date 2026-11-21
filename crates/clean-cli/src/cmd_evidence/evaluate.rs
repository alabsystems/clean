// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evaluate registered figures, and board row 17, `evidence.stale_figures`,
//! which is derived from the other figures' readings in the same run.

use super::catalog::{Figure, FIGURES};
use super::reading::{DenominatorReading, FreshnessReading, Outcome, Reading};
use crate::EvidenceCheckError;
use clean_evidence::envelope::FreshnessState;
use serde_json::json;
use std::path::Path;

pub(super) const STALE_FIGURE: &str = "evidence.stale_figures";

pub(super) type FigureResult = Result<Outcome, EvidenceCheckError>;

/// Read every figure in `selected`, in order. When the staleness figure is
/// selected, every other registered figure is read once and shared.
pub(super) fn evaluate(root: &Path, selected: &[&'static Figure]) -> Vec<FigureResult> {
    if !selected.iter().any(|figure| figure.id == STALE_FIGURE) {
        return selected.iter().map(|figure| figure.read(root)).collect();
    }
    let others: Vec<(&'static str, FigureResult)> = FIGURES
        .iter()
        .filter(|figure| figure.id != STALE_FIGURE)
        .map(|figure| (figure.id, figure.read(root)))
        .collect();
    let mut stale = Some(summarize(&others));
    let mut others: Vec<(&'static str, Option<FigureResult>)> = others
        .into_iter()
        .map(|(id, result)| (id, Some(result)))
        .collect();
    selected
        .iter()
        .map(|figure| {
            let taken = if figure.id == STALE_FIGURE {
                stale.take()
            } else {
                others
                    .iter_mut()
                    .find(|(id, _)| *id == figure.id)
                    .and_then(|(_, result)| result.take())
            };
            taken.unwrap_or_else(|| figure.read(root))
        })
        .collect()
}

/// The `read` of the staleness figure when it is asked for on its own.
pub(super) fn stale_figures(root: &Path) -> FigureResult {
    let others: Vec<(&'static str, FigureResult)> = FIGURES
        .iter()
        .filter(|figure| figure.id != STALE_FIGURE)
        .map(|figure| (figure.id, figure.read(root)))
        .collect();
    summarize(&others)
}

fn summarize(results: &[(&'static str, FigureResult)]) -> FigureResult {
    let (mut fresh, mut unknown, mut absent, mut unreadable) = (0u64, 0u64, 0u64, 0u64);
    let mut stale = Vec::new();
    for (id, result) in results {
        match result {
            Ok(Outcome::Measured(reading)) => match reading.freshness.state {
                FreshnessState::Fresh => fresh += 1,
                FreshnessState::Stale => stale.push(*id),
                _ => unknown += 1,
            },
            Ok(Outcome::Absent { .. }) => absent += 1,
            Err(_) => unreadable += 1,
        }
    }
    let mut reading = Reading::new(
        json!({
            "stale": stale.len(),
            "unknown": unknown,
            "fresh": fresh,
            "absent": absent,
            "unreadable": unreadable,
        }),
        format!(
            "{} stale, {unknown} unknown, {fresh} fresh, {absent} absent and {unreadable} unreadable of {} registered figures",
            stale.len(),
            results.len()
        ),
        FreshnessReading::fresh("derived in this run from the current readings"),
    );
    reading.denominator = Some(DenominatorReading::counting(
        "registered figures other than this one",
        results.iter().map(|(id, _)| *id),
    )?);
    reading.labels = stale.iter().map(|id| format!("stale: {id}")).collect();
    reading.non_claims = vec![
        "unknown means no recorded input digest, never fresh".to_owned(),
        "absent counts registered figures with no evidence reading".to_owned(),
    ];
    Ok(Outcome::Measured(Box::new(reading)))
}

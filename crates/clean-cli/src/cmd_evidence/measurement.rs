// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The typed recounts of the historical W0 figures.

use super::{
    checker_source::CheckerSourceFigure,
    elaboration::ElaborationFigure,
    k3_scoreboard::{Accepted, Decided},
    rule_families::RuleFamilyFigure,
    w0_scoreboard::RowValue,
};
use serde::Serialize;
use std::fmt;

#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Measurement {
    PlantedFalse {
        sites: usize,
        minted_under_mutant: usize,
        source: String,
        #[serde(flatten)]
        provenance: MeasurementProvenance,
    },
    IslandGaps {
        rows: usize,
        open: usize,
        source: String,
    },
    TheoriesElaborated(ElaborationFigure),
    RuleFamilies(RuleFamilyFigure),
    CheckerSource(CheckerSourceFigure),
    K3Decided(RowValue<Decided>),
    K3Accepted(RowValue<Accepted>),
}

#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum MeasurementProvenance {
    Clean {
        measured_commit: String,
    },
    Trust {
        measured_at: String,
        trust_commit: String,
        clean_pin_in_trust: String,
    },
}

impl fmt::Display for Measurement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PlantedFalse {
                sites,
                minted_under_mutant,
                provenance,
                ..
            } => {
                write!(
                    f,
                    "{minted_under_mutant} of {sites} sites minted under the historical mutant"
                )?;
                match provenance {
                    MeasurementProvenance::Clean { measured_commit } => {
                        write!(f, " (measured at Clean commit {measured_commit:?})")
                    }
                    MeasurementProvenance::Trust {
                        measured_at,
                        trust_commit,
                        clean_pin_in_trust,
                    } => write!(
                        f,
                        " (measured {measured_at:?}, Trust {trust_commit:?}, Clean pin {clean_pin_in_trust:?})"
                    ),
                }
            }
            Self::IslandGaps { rows, open, .. } => {
                write!(f, "{open} of {rows} recorded island gaps open")
            }
            Self::TheoriesElaborated(figure) => fmt::Display::fmt(figure, f),
            Self::RuleFamilies(figure) => fmt::Display::fmt(figure, f),
            Self::CheckerSource(figure) => fmt::Display::fmt(figure, f),
            Self::K3Decided(figure) => fmt::Display::fmt(figure, f),
            Self::K3Accepted(figure) => fmt::Display::fmt(figure, f),
        }
    }
}

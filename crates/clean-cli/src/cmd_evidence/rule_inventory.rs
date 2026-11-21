// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Read-only inventory consistency across C++ sources, Lean references and row statuses.

mod rows;

use std::{
    io::{self, Write},
    path::Path,
};

use serde::Serialize;

use super::{cpp_anchors, k3_inputs, lean_rule_references};
use crate::EvidenceCheckError;

#[derive(Default, Serialize)]
struct Report<'a> {
    rows: Option<rows::Report>,
    cpp: Option<cpp_anchors::Report<'a>>,
    lean: Option<lean_rule_references::Report>,
    findings: Vec<String>,
    unreadable: Vec<String>,
}

impl Report<'_> {
    fn record<T>(
        &mut self,
        section: &str,
        result: Result<T, EvidenceCheckError>,
    ) -> Result<Option<T>, EvidenceCheckError> {
        match result {
            Ok(section) => Ok(Some(section)),
            Err(EvidenceCheckError::Invalid(reason)) => {
                self.findings.push(format!("{section}: {reason}"));
                Ok(None)
            }
            Err(EvidenceCheckError::Unavailable(reason)) => {
                self.unreadable.push(format!("{section}: {reason}"));
                Ok(None)
            }
            Err(error @ EvidenceCheckError::Usage(_)) => Err(error),
        }
    }

    fn verdict(&self, require_complete: bool) -> Result<(), EvidenceCheckError> {
        let mut invalid =
            !self.findings.is_empty() || self.rows.as_ref().is_some_and(|r| !r.findings.is_empty());
        let mut unavailable = !self.unreadable.is_empty()
            || self.rows.as_ref().is_some_and(|r| !r.unreadable.is_empty());
        let source_verdicts = [
            self.cpp.as_ref().map(cpp_anchors::Report::verdict),
            self.lean
                .as_ref()
                .map(lean_rule_references::Report::verdict),
        ];
        for error in source_verdicts
            .into_iter()
            .flatten()
            .filter_map(Result::err)
        {
            match error {
                EvidenceCheckError::Invalid(_) => invalid = true,
                EvidenceCheckError::Unavailable(_) => unavailable = true,
                error @ EvidenceCheckError::Usage(_) => return Err(error),
            }
        }
        if invalid {
            return Err(EvidenceCheckError::Invalid(
                "rule inventory has findings".to_owned(),
            ));
        }
        if unavailable {
            return Err(EvidenceCheckError::Unavailable(
                "required rule inventory inputs were unavailable".to_owned(),
            ));
        }
        if require_complete {
            let incomplete = self
                .rows
                .as_ref()
                .map_or(0, |rows| rows.not_specified.len());
            if incomplete > 0 {
                return Err(EvidenceCheckError::Invalid(format!(
                    "--require-complete: {incomplete} rule families are in the ratchet"
                )));
            }
        }
        Ok(())
    }
}

pub(super) fn run(root: &Path, require_complete: bool) -> anyhow::Result<()> {
    let root = k3_inputs::canonical_root(root)?;
    let bytes = cpp_anchors::read_inventory_bytes(&root)?;
    let inventory = cpp_anchors::decode_inventory(&bytes, true);

    let mut report = Report::default();
    report.rows = report.record("Rows", rows::check(&root, &bytes))?;
    let cpp = inventory
        .as_ref()
        .map_err(Clone::clone)
        .and_then(|inventory| cpp_anchors::inspect(&root, inventory, true));
    report.cpp = report.record("C++", cpp)?;
    report.lean = report.record(
        "Lean",
        lean_rule_references::report_from_snapshot(&root, &bytes),
    )?;

    let mut output = io::stdout().lock();
    serde_json::to_writer_pretty(&mut output, &report)?;
    writeln!(output)?;
    report.verdict(require_complete)?;
    Ok(())
}

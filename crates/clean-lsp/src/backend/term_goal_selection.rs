// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-info selection: children precede ancestors; sibling priorities use
//! the cursor boundary, range, variable and partial-info properties.

use std::collections::{HashMap, HashSet};

use tower_lsp::lsp_types::Position;

use crate::document::{Document, SourceInfo};

fn ancestors<'a>(
    info: &'a SourceInfo,
    by_id: &HashMap<u64, &'a SourceInfo>,
) -> Option<Vec<&'a SourceInfo>> {
    let mut current = info;
    let mut parents = Vec::new();
    while let Some(id) = current.parent_id {
        // Producer IDs increase down each branch. Reject malformed links
        // instead of looping or treating them as independent source nodes.
        if id >= current.id {
            return None;
        }
        current = *by_id.get(&id)?;
        parents.push(current);
    }
    Some(parents)
}

pub(super) fn at_position(doc: &Document, position: Position) -> Option<&SourceInfo> {
    let infos = &doc.elaborated.as_ref()?.term_infos;
    let by_id: HashMap<_, _> = infos.iter().map(|info| (info.id, info)).collect();
    if by_id.len() != infos.len() {
        return None;
    }
    let mut candidates = Vec::new();
    let mut parents_with_matches = HashSet::new();
    for info in infos {
        if !super::recorded_span_contains(doc, info.start, info.end, position) {
            continue;
        }
        let parents = ancestors(info, &by_id)?;
        // As in Lean's termGoalAt?, an identifier head answers for its full
        // application. This does not suppress argument or nested-term info.
        // Expected-type elaboration can observe the same application twice.
        // An inner applied-head node still answers for the application; only
        // its partial function observation is superseded by an ancestor.
        if info.application_head != Some((info.start, info.end))
            && parents
                .iter()
                .any(|parent| parent.application_head == Some((info.start, info.end)))
        {
            continue;
        }
        parents_with_matches.extend(parents.iter().map(|parent| parent.id));
        candidates.push(info);
    }
    candidates
        .into_iter()
        .filter(|info| !parents_with_matches.contains(&info.id))
        .min_by_key(|info| {
            (
                position == doc.offset_to_position(info.end),
                info.end - info.start,
                info.is_variable,
                info.is_partial,
            )
        })
}

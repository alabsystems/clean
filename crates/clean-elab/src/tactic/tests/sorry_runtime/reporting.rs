// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Format sorry locations into a human-readable diagnostic report.
pub(super) fn format_sorry_locations() -> String {
    let Some(locations) = sorry_locations() else {
        return "  (location tracking not enabled)".to_string();
    };
    if locations.is_empty() {
        return "  (no sorry locations recorded)".to_string();
    }

    let mut entries: Vec<_> = locations.into_iter().collect();
    entries.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));

    let mut out = String::new();
    for (loc, count) in &entries {
        out.push_str(&format!("  {count:>3}x  {loc}\n"));
    }
    out
}

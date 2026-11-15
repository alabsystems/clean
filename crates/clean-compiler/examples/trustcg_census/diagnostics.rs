// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Linker diagnostic extraction for the explicit TrustCG census utility.

use std::collections::HashSet;

/// Symbols the linker reports as undefined, with the Mach-O leading `_` stripped
/// (so they read like the mangled `l_*` / `clean_*` source names).
pub(super) fn undefined_symbols(stderr: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for line in stderr.lines() {
        // macOS ld64: `  "_l_Int_decLt", referenced from:`
        // Also handles GNU ld `undefined reference to `_l_Int_decLt'`.
        let mut push = |raw: &str| {
            let sym = raw.strip_prefix('_').unwrap_or(raw).to_string();
            if !sym.is_empty() && seen.insert(sym.clone()) {
                out.push(sym);
            }
        };
        if let Some(q0) = line.find('"') {
            if let Some(q1) = line[q0 + 1..].find('"') {
                let inner = &line[q0 + 1..q0 + 1 + q1];
                if inner.starts_with('_') || inner.starts_with("l_") || inner.starts_with("clean_")
                {
                    push(inner);
                    continue;
                }
            }
        }
        if let Some(idx) = line.find("undefined reference to") {
            let rest = &line[idx..];
            if let Some(b0) = rest.find('`') {
                if let Some(b1) = rest[b0 + 1..].find('\'') {
                    push(&rest[b0 + 1..b0 + 1 + b1]);
                }
            }
        }
    }
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::undefined_symbols;

    #[test]
    fn macos_and_gnu_diagnostics_keep_sorted_distinct_source_symbols() {
        let stderr = "  \"_l_Int_decLt\", referenced from:\n\
                      undefined reference to `_clean_inc'\n\
                      undefined reference to `l_Int_decLt'\n\
                      \"clean_box\" referenced from:\n";
        assert_eq!(
            undefined_symbols(stderr),
            ["clean_box", "clean_inc", "l_Int_decLt"]
        );
    }

    #[test]
    fn unrelated_empty_and_incomplete_diagnostics_do_not_create_symbols() {
        let stderr = "ld: warning: \"unrelated\"\n\
                      undefined reference to `'\n\
                      undefined reference to `unfinished\n\
                      \"_\", referenced from:\n";
        assert!(undefined_symbols(stderr).is_empty());
    }
}

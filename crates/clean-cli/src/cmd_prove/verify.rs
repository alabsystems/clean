// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local verification of a remote/automated prover's output.
//!
//! The providers' own "success" report is **not** authoritative (mirror the
//! aristotle skill's discipline: *"Never treat Aristotle's success message as
//! final. The final authority is local verification"*). After a backend writes
//! a candidate proof into a Lean project, the workflow re-checks it locally
//! before reporting success:
//!
//! 1. `lake build` must exit cleanly.
//! 2. No `sorry` / `admit` may remain in the project's `.lean` sources.
//! 3. `#print axioms <theorem>` must show an axiom set that is a subset of a
//!    foundational allowlist (no domain-specific axioms snuck in).
//!
//! This module owns the typed, network-free verification logic; it is the
//! library-style portion of the `clean prove` workflow and therefore uses a
//! `thiserror` error enum rather than `anyhow`. The binary glue in
//! `super` shells out to `lake` and feeds the captured output here.

use std::collections::BTreeSet;

/// Foundational axioms a `prove`d theorem may transitively depend on.
///
/// Sorry/admit-style markers that must not survive into a verified proof.
///
/// `sorryAx` is the elaborated form Lean lowers `sorry` to; it can also surface
/// in a `#print axioms` listing, so the axiom-closure check rejects it too.
const SORRY_MARKERS: &[&str] = &["sorry", "admit", "sorryAx"];

/// Typed failure modes of local proof verification.
///
/// Library-style (`thiserror`) so the binary glue can match on the variant and
/// so the verification logic stays unit-testable without spawning `lake`.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ProveError {
    /// `lake build` exited non-zero. Carries the captured combined output tail
    /// so the caller can surface a useful diagnostic.
    #[error("lake build failed for the retrieved proof (exit {code}):\n{tail}")]
    LakeBuildFailed {
        /// Process exit code (or `-1` when terminated by a signal).
        code: i32,
        /// Bounded tail of the captured build output.
        tail: String,
    },

    /// A `sorry` / `admit` marker remained in a retrieved `.lean` source.
    #[error("retrieved proof still contains `{marker}` in {file} — not a real proof")]
    SorryRemains {
        /// The offending marker (`sorry`, `admit`, …).
        marker: String,
        /// Project-relative path of the file that still contains it.
        file: String,
    },

    /// `#print axioms` reported axioms outside the foundational allowlist.
    #[error(
        "theorem `{theorem}` depends on non-foundational axiom(s): {}; \
         a `prove`d theorem's axiom closure must be ⊆ the foundational allowlist",
        .offending.join(", ")
    )]
    NonFoundationalAxioms {
        /// The theorem whose axiom closure was inspected.
        theorem: String,
        /// Axioms present in the closure but absent from the allowlist.
        offending: Vec<String>,
    },

    /// The `#print axioms` output could not be located / parsed, so the axiom
    /// closure is unknown. Fail closed rather than assume foundational.
    #[error(
        "could not determine the axiom closure of `{theorem}` from the build output; \
         refusing to report success on an unverifiable proof"
    )]
    AxiomClosureUnknown {
        /// The theorem whose axiom closure was being checked.
        theorem: String,
    },
}

/// Outcome of a `#print axioms` inspection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AxiomReport {
    /// `#print axioms <thm>` reported the theorem depends on no axioms.
    DependsOnNoAxioms,
    /// `#print axioms <thm>` listed the given axiom names.
    Axioms(BTreeSet<String>),
}

/// Parse the axiom set a `#print axioms <theorem>` command reported.
///
/// Lean's `#print axioms foo` emits one of two shapes on stdout/stderr:
///
/// ```text
/// 'foo' depends on axioms: [propext, Classical.choice, Quot.sound]
/// ```
///
/// or, when fully constructive:
///
/// ```text
/// 'foo' does not depend on any axioms
/// ```
///
/// Returns `None` when no matching line is found (caller fails closed via
/// [`ProveError::AxiomClosureUnknown`]).
pub(crate) fn parse_print_axioms(output: &str, theorem: &str) -> Option<AxiomReport> {
    // Match on the unqualified leaf name too: `#print axioms M.foo` reports
    // `'M.foo'` but a caller may pass the bare `foo`.
    let leaf = theorem.rsplit('.').next().unwrap_or(theorem);
    for line in output.lines() {
        let line = line.trim();
        let mentions_theorem = line.contains(&format!("'{theorem}'"))
            || line.contains(&format!("'{leaf}'"))
            || line.contains(theorem);
        if !mentions_theorem {
            continue;
        }
        if line.contains("does not depend on any axioms") || line.contains("depends on no axioms") {
            return Some(AxiomReport::DependsOnNoAxioms);
        }
        if let Some(idx) = line.find("depends on axioms:") {
            let rest = &line[idx + "depends on axioms:".len()..];
            let inside = rest
                .trim()
                .trim_start_matches('[')
                .trim_end_matches(']')
                .trim();
            let axioms: BTreeSet<String> = inside
                .split([',', ' '])
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(str::to_owned)
                .collect();
            return Some(AxiomReport::Axioms(axioms));
        }
    }
    None
}

/// Validate a parsed [`AxiomReport`] against the foundational allowlist.
///
/// Returns `Ok(())` when every reported axiom is foundational (or there are
/// none), else [`ProveError::NonFoundationalAxioms`]. Any `sorry`-style marker
/// in the closure is treated as non-foundational (it never appears in the
/// allowlist), so a `sorryAx`-bearing closure fails here.
pub(crate) fn check_axioms_foundational(
    theorem: &str,
    report: &AxiomReport,
) -> Result<(), ProveError> {
    let axioms = match report {
        AxiomReport::DependsOnNoAxioms => return Ok(()),
        AxiomReport::Axioms(set) => set,
    };
    // Delegate foundational classification to the kernel's single source of
    // truth (`clean_kernel::is_foundational_axiom` over the canonical
    // `FOUNDATIONAL_AXIOMS` in `axiom_audit.rs`) instead of a local copy — a
    // duplicated allowlist can silently drift from the TCB definition (#3561,
    // enforced by `test_no_drifted_foundational_axioms_const_array`). The kernel
    // check additionally short-circuits trust markers (`sorry`/`sorryAx`/…) and
    // admitted domain axioms to non-foundational, so a sorry- or domain-bearing
    // closure still fails here.
    let offending: Vec<String> = axioms
        .iter()
        .filter(|name| {
            !clean_kernel::is_foundational_axiom(&clean_kernel::name::Name::from_string(name))
        })
        .cloned()
        .collect();
    if offending.is_empty() {
        Ok(())
    } else {
        Err(ProveError::NonFoundationalAxioms {
            theorem: theorem.to_owned(),
            offending,
        })
    }
}

/// Scan a single Lean source body for a residual `sorry` / `admit` marker.
///
/// Word-boundary aware so identifiers that merely *contain* the substring
/// (e.g. `sorryFree`, a hypothetical `adminted`) do not trip the check. Returns
/// the first marker found, if any.
pub(crate) fn find_sorry_marker(source: &str) -> Option<&'static str> {
    SORRY_MARKERS
        .iter()
        .copied()
        .find(|&marker| source_contains_word(source, marker))
}

/// Whether `needle` occurs in `haystack` delimited by non-identifier
/// characters on both sides (a Lean-identifier word boundary).
fn source_contains_word(haystack: &str, needle: &str) -> bool {
    let bytes = haystack.as_bytes();
    let nlen = needle.len();
    let mut search_from = 0usize;
    while let Some(rel) = haystack[search_from..].find(needle) {
        let start = search_from + rel;
        let end = start + nlen;
        let before_ok = start == 0 || !is_ident_byte(bytes[start - 1]);
        let after_ok = end >= bytes.len() || !is_ident_byte(bytes[end]);
        if before_ok && after_ok {
            return true;
        }
        search_from = start + 1;
    }
    false
}

/// Whether `b` can appear inside a Lean identifier (letters, digits, `_`, `.`,
/// `'`, and `!`/`?` which Lean permits in identifiers).
fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'\'' | b'!' | b'?')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_print_axioms_constructive_returns_no_axioms() {
        let out = "'M.foo' does not depend on any axioms";
        let report = parse_print_axioms(out, "M.foo").expect("line should parse");
        assert_eq!(report, AxiomReport::DependsOnNoAxioms);
    }

    #[test]
    fn test_parse_print_axioms_lists_named_axioms() {
        let out = "'foo' depends on axioms: [propext, Classical.choice, Quot.sound]";
        let report = parse_print_axioms(out, "foo").expect("line should parse");
        match report {
            AxiomReport::Axioms(set) => {
                assert!(set.contains("propext"));
                assert!(set.contains("Classical.choice"));
                assert!(set.contains("Quot.sound"));
                assert_eq!(set.len(), 3);
            }
            other => panic!("expected Axioms, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_print_axioms_matches_leaf_when_passed_qualified() {
        // `#print axioms` reported the leaf name; caller asked for the
        // fully-qualified one (or vice versa).
        let out = "'foo' depends on axioms: [propext]";
        let report = parse_print_axioms(out, "Mod.Path.foo").expect("leaf should match");
        assert!(matches!(report, AxiomReport::Axioms(_)));
    }

    #[test]
    fn test_parse_print_axioms_absent_returns_none() {
        let out = "lake build succeeded\nnothing relevant here";
        assert!(parse_print_axioms(out, "foo").is_none());
    }

    #[test]
    fn test_check_axioms_foundational_accepts_allowlisted() {
        let mut set = BTreeSet::new();
        set.insert("propext".to_owned());
        set.insert("Classical.choice".to_owned());
        set.insert("Quot.sound".to_owned());
        let report = AxiomReport::Axioms(set);
        check_axioms_foundational("foo", &report).expect("allowlisted axioms must pass");
    }

    #[test]
    fn test_check_axioms_foundational_accepts_no_axioms() {
        check_axioms_foundational("foo", &AxiomReport::DependsOnNoAxioms)
            .expect("no axioms must pass");
    }

    #[test]
    fn test_check_axioms_foundational_rejects_domain_axiom() {
        let mut set = BTreeSet::new();
        set.insert("propext".to_owned());
        set.insert("Crownproof.myBespokeAxiom".to_owned());
        let report = AxiomReport::Axioms(set);
        let err =
            check_axioms_foundational("foo", &report).expect_err("a domain axiom must be rejected");
        match err {
            ProveError::NonFoundationalAxioms { theorem, offending } => {
                assert_eq!(theorem, "foo");
                assert_eq!(offending, vec!["Crownproof.myBespokeAxiom".to_owned()]);
            }
            other => panic!("expected NonFoundationalAxioms, got {other:?}"),
        }
    }

    #[test]
    fn test_check_axioms_foundational_rejects_sorry_ax() {
        let mut set = BTreeSet::new();
        set.insert("sorryAx".to_owned());
        let report = AxiomReport::Axioms(set);
        check_axioms_foundational("foo", &report)
            .expect_err("a sorryAx-bearing closure must be rejected");
    }

    #[test]
    fn test_find_sorry_marker_detects_bare_sorry() {
        let src = "theorem foo : True := by\n  sorry";
        assert_eq!(find_sorry_marker(src), Some("sorry"));
    }

    #[test]
    fn test_find_sorry_marker_detects_admit() {
        let src = "theorem foo : True := by\n  admit";
        assert_eq!(find_sorry_marker(src), Some("admit"));
    }

    #[test]
    fn test_find_sorry_marker_ignores_identifier_substring() {
        // `sorryFree` is an ordinary identifier, not a `sorry`.
        let src = "def sorryFree : Bool := true";
        assert_eq!(find_sorry_marker(src), None);
    }

    #[test]
    fn test_find_sorry_marker_clean_source() {
        let src = "theorem foo : True := trivial";
        assert_eq!(find_sorry_marker(src), None);
    }

    #[test]
    fn test_prove_error_lake_build_message_includes_code() {
        let err = ProveError::LakeBuildFailed {
            code: 1,
            tail: "error: unknown identifier".to_owned(),
        };
        let msg = err.to_string();
        assert!(msg.contains("exit 1"));
        assert!(msg.contains("unknown identifier"));
    }

    /// The default foundational allowlist must, at minimum, carry the four
    /// `CLAUDE.md` foundational axioms. Guards against an accidental edit that
    /// would silently widen or narrow the trust boundary.
    #[test]
    fn test_foundational_allowlist_contains_claude_md_set() {
        for required in ["propext", "Quot.sound", "Classical.choice"] {
            assert!(
                clean_kernel::is_foundational_axiom(&clean_kernel::name::Name::from_string(
                    required
                )),
                "foundational allowlist must contain {required}"
            );
        }
    }
}

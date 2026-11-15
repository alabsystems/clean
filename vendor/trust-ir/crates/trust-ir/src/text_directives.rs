// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The ONE vocabulary of `; #<word>` comment directives in the TrustIr text
//! format (roadmap WS4.2, finding F-065).
//!
//! The printer (`display.rs`) spells every directive it writes through the
//! constants below, and the parser (`parser.rs`, `parser` feature) dispatches
//! on the same table and REFUSES any word that is not in it:
//!
//! ```text
//! unknown directive `#frobnicate` — refusing rather than dropping it
//! ```
//!
//! Until WS4.2 the parser silently skipped an unknown directive (and an
//! unknown top-level line), so a text written by a newer printer — or a
//! printer that grew a directive without a parser arm — lost that field with
//! no error. A directive is therefore either in [`TEXT_DIRECTIVES`], and has a
//! parser arm, or it is a parse error. The conformance corpus asserts every
//! entry here round-trips through at least one fixture
//! (`crates/trust-ir-conformance/tests/conformance.rs`,
//! `every_text_directive_round_trips_through_the_corpus`), so a printer-only
//! directive cannot be added silently.
//!
//! [`LOSSY`] is deliberately NOT in the table: it is the marker the printer
//! writes when [`crate::text_loss::text_losses`] is non-empty, and the parser
//! refuses it unconditionally (the text cannot be parsed back into the module
//! it was printed from).
//!
//! Plain comments — a `;` NOT followed (after spaces) by `#` — are still
//! skipped everywhere a comment is admitted.

/// Function-level optimization attribute flags (`; #attrs: readonly cold`).
pub const ATTRS: &str = "#attrs";
/// Function-level v41 summary backing (`; #backed-by: extern 0 "f" obligation 3`),
/// WS4.4. Part of the contiguous summary block that `#summary` opens.
pub const BACKED_BY: &str = "#backed-by";
/// Function-level v41 codegen license (`; #body-gate: ungated`).
pub const BODY_GATE: &str = "#body-gate";
/// Function-level v41 termination measure (`; #decreases: formula ..`), WS4.4.
pub const DECREASES: &str = "#decreases";
/// Function-level v41 human definition path (`; #display-path: "a::b"`).
pub const DISPLAY_PATH: &str = "#display-path";
/// Function-level v59 effect summary (`; #effects: reads nothing writes
/// places [param(0)] allocates false frees false may_unwind false io false`),
/// WS1.14. The LAST directive of the contiguous summary block, at most once.
pub const EFFECTS: &str = "#effects";
/// Function-level summary postcondition (`; #ensures: formula ..`), WS4.4.
pub const ENSURES: &str = "#ensures";
/// Function-level summary precondition (`; #requires: formula ..`), WS4.4.
pub const REQUIRES: &str = "#requires";
/// Function-level v45 return-slot ABI facts (`; #ret_attrs: zeroext`), WS3.11.
pub const RET_ATTRS: &str = "#ret_attrs";
/// Function-level v45 `#[used]`-style retention (`; #retained: true`), WS3.10.
pub const RETAINED: &str = "#retained";
/// Function-level v45 output section (`; #section: ".text.startup"`), WS3.10.
pub const SECTION: &str = "#section";
/// Function-level v45 symbol visibility (`; #visibility: hidden`), WS3.10.
pub const VISIBILITY: &str = "#visibility";
/// Node-level source span (`; #loc: <file> <line> <col>`).
pub const LOC: &str = "#loc";
/// Function-level v32 debug value names (`; #names: %0="x"`).
pub const NAMES: &str = "#names";
/// Function-level per-parameter attributes (`; #param_attrs 0: nonnull`).
pub const PARAM_ATTRS: &str = "#param_attrs";
/// Function-level v23 producer provenance (`; #producer: trust`).
pub const PRODUCER: &str = "#producer";
/// Function- and node-level proof annotations (`; #proof: pure`).
pub const PROOF: &str = "#proof";
/// Node-level per-call proof context (`; #proof_ctx: assumes[..] establishes[..]`).
pub const PROOF_CTX: &str = "#proof_ctx";
/// Function-level v33 scope-tree entry AND node-level scope index.
pub const SCOPE: &str = "#scope";
/// Function-level v35 source binding row.
pub const SOURCE_BINDING: &str = "#source-binding";
/// Function-level v35 source loop row.
pub const SOURCE_LOOP: &str = "#source-loop";
/// Function-level v35 source provenance header.
pub const SOURCE_PROVENANCE: &str = "#source-provenance";
/// Function-level `FunctionSummary` header (`; #summary: proved params ["a"]`),
/// WS4.4. Opens the contiguous summary block: `#requires`*, `#ensures`*,
/// `#decreases`*, at most one `#backed-by` and at most one `#effects` (v59)
/// follow it, in that order.
pub const SUMMARY: &str = "#summary";
/// Function-level v41 target features (`; #target_features: "neon"`).
pub const TARGET_FEATURES: &str = "#target_features";

/// The lossy-print marker: `; #lossy: <summaries>` immediately after the
/// `; TrustIr text format v1` header. Always REFUSED by the parser.
pub const LOSSY: &str = "#lossy";

/// Every directive the printer may write and the parser accepts. Measured
/// at 1c4602b1 by grep over `display.rs`, extended by the v45 function symbol
/// attributes (WS3.10) and return slot (WS3.11) and by the WS4.4 function
/// summary block (`#summary`, `#requires`, `#ensures`, `#decreases`,
/// `#backed-by`) and by its v59 `#effects` line (WS1.14); order is
/// alphabetical.
pub const TEXT_DIRECTIVES: &[&str] = &[
    ATTRS,
    BACKED_BY,
    BODY_GATE,
    DECREASES,
    DISPLAY_PATH,
    EFFECTS,
    ENSURES,
    LOC,
    NAMES,
    PARAM_ATTRS,
    PRODUCER,
    PROOF,
    PROOF_CTX,
    REQUIRES,
    RET_ATTRS,
    RETAINED,
    SCOPE,
    SECTION,
    SOURCE_BINDING,
    SOURCE_LOOP,
    SOURCE_PROVENANCE,
    SUMMARY,
    TARGET_FEATURES,
    VISIBILITY,
];

/// True iff `c` may appear in a directive word after the `#`. Deliberately
/// wider than any word in the table (ASCII alphanumerics, `_`, `-`), so an
/// unknown directive is read WHOLE and named in the refusal.
#[must_use]
pub fn is_directive_word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '-'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_is_sorted_unique_and_excludes_lossy() {
        let mut sorted = TEXT_DIRECTIVES.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted, TEXT_DIRECTIVES, "sorted and duplicate-free");
        assert!(!TEXT_DIRECTIVES.contains(&LOSSY));
        for word in TEXT_DIRECTIVES.iter().chain([&LOSSY]) {
            let body = word.strip_prefix('#').expect("leading #");
            assert!(!body.is_empty() && body.chars().all(is_directive_word_char));
        }
    }

    /// The exact set the spec measured (roadmap WS4.2 step 5). A directive
    /// added to the printer must be added here AND get a parser arm.
    #[test]
    fn table_is_the_measured_vocabulary() {
        assert_eq!(
            TEXT_DIRECTIVES.join(" "),
            "#attrs #backed-by #body-gate #decreases #display-path #effects #ensures #loc #names \
             #param_attrs #producer #proof #proof_ctx #requires #ret_attrs #retained #scope \
             #section #source-binding #source-loop #source-provenance #summary \
             #target_features #visibility"
        );
    }
}

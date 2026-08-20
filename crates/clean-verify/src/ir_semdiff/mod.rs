// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **GAP 2 — turning "Clean's `IRInst` semantics means what trust-ir's does"
//! from an assumption into a measured, fail-closed claim.**
//!
//! ## The gap
//!
//! `crystal_a1_lineage.rs` says of itself, verbatim:
//!
//! > It is a STRUCTURAL correspondence, not a semantic proof that Clean's
//! > `IRInst` encoding of `switch`/`br` means what trust-ir's does. The two
//! > agree by construction of `eval_ir_syntax`, which this does not re-derive.
//!
//! Even granting link 2a in full — that the module Clean proved about IS the
//! module the compiler emitted — nothing said that *running* that module under
//! Clean's `ir_eval` computes what *running* it under trust-ir computes. Both
//! `switch` rules were written by the same hand and were never compared.
//!
//! ## Is trust-ir's semantics written down at all?
//!
//! **Yes — twice, and neither one is the compiler.** This is stated first
//! because it bounds everything below.
//!
//! * `trust:first-party/trust-ir/lean/trust_ir-semantics/` — 22,419 lines of
//!   Lean 4 monadic small-step operational semantics; `Semantics/Step.lean`
//!   dispatches every `Inst`. `docs/roadmap/B3-lean-ir-parity.md` calls Lean
//!   "the source of truth" and records name-level parity as CLOSED for `Inst`,
//!   `CastOp` and `Ty`. But the gate that establishes that,
//!   `crates/trust-ir/tests/lean_schema_parity.rs`, says in its own header:
//!   *"There is no Lean toolchain in CI here to* prove *parity, but we CAN
//!   mechanically detect drift"*, and *"The gate matches constructor NAMES. It
//!   cannot see semantic depth."* So the written semantics is joined to the
//!   shipped compiler by a **name check**, not by a refinement proof.
//! * `trust:first-party/trust-ir/crates/trust-ir/src/interpret.rs` — 12,493
//!   lines of executable Rust reference interpreter, whose own header says
//!   *"Lean remains the source of truth for the full operational semantics"*
//!   and that it covers a deliberately bounded subset.
//!
//! Neither is the semantics *of the compiler*: `to_mir.rs` and LLVM are what
//! give an emitted module its meaning in the shipped binary. **So agreement
//! cannot be PROVED against trust-ir's semantics** — there is no single formal
//! object holding the authoritative meaning that both sides could be proved to
//! refine, and any claim to have proved one would be a proof against a phantom.
//! What can be done, and is what this module does, is MEASURE agreement against
//! every executor that does exist, over a real input set, with every
//! disagreement printed rather than smoothed.
//!
//! ## The three executors
//!
//! * **E1 — Clean's `ir_eval`, checked by the Clean kernel.** Not a Rust
//!   re-implementation: the obligation is an `Eq.refl` that the kernel
//!   discharges by *reducing* `ir_eval` over the registered module. Acceptance
//!   is the verdict, so this leg cannot be fudged by the harness.
//! * **E2 — trust-ir's reference interpreter**, run over the *committed emitted
//!   body* (`tests/fixtures/*.trust-ir.txt`), parsed by trust-ir's own parser.
//! * **E3 — the shipped compiled function**, called directly. `clean-verify`
//!   already depends on `clean-kernel`, so this is the real machine code,
//!   reached through `to_mir` + the rustc pass pipeline + LLVM. It is the only
//!   executor that cannot share a misunderstanding with the other two.
//!
//! ## Why this is sharper than "both said true"
//!
//! Output equality alone is weak — two encodings can differ in a way that a
//! compensating second difference hides. Two things narrow it.
//!
//! **Cost is compared, not just value.** Clean's fuel threshold is *measured*
//! by probing (the least `k` for which `ir_eval k … = ret v` is kernel-accepted)
//! and compared against trust-ir's reported step count. A mis-encoded `switch`
//! that still reaches the right answer almost always reaches it in a different
//! number of steps. The threshold is measured rather than asserted so that a
//! systematic difference in what "one step" means is *reported as an offset*
//! instead of being baked into the template and hidden.
//!
//! **The expected value is never hand-written.** The existing witnesses
//! (`ir_h2_on_cubical` and friends) are `Eq.refl` against a constant a human
//! typed. Here the right-hand side is derived from E2 and cross-checked against
//! E3, so the kernel confirms someone else's measurement rather than its
//! author's intention.
//!
//! ## Where the trust boundary moves — and where it does not
//!
//! Nothing here enters the TCB. trust-ir's parser and interpreter are used only
//! to *pose* questions the Clean kernel then answers; if either is wrong the
//! generated obligation is REJECTED and the row goes RED. **A wrong E2 can
//! produce a spurious failure, never a spurious pass** — the only direction of
//! error a measuring instrument may have.
//!
//! ## What this is NOT
//!
//! A measured agreement is **not a proof**, and this module is built to make
//! that impossible to overstate: it reports a coverage fraction over a real
//! denominator and a totality flag that is never rounded up. On a chain whose
//! domain is finite and fully enumerated the honest label is *total extensional
//! agreement on that body* — still not a proof that the two `IRInst` encodings
//! denote the same function in general, because agreement on one body's
//! instruction mix says nothing about the forms that body never uses.

pub mod obligations;
pub mod report;

pub use obligations::{
    fuel_out_obligation, ir_numeral, ptr_cell_call, value_arg_call, value_obligation, ArgShape,
    RunResult, MAX_IR_NUMERAL,
};
pub use report::{summarize, Agreement, ChainReport, DiffRow};

/// How the subject's return value is encoded on the Clean side.
///
/// The trust-ir harness always yields a `u8` (it projects the tag of an
/// enum-returning subject), so this is what turns that one wire format back
/// into the right Clean scalar. Declared per chain rather than guessed, because
/// `int 4` and `enum tag 4` are different Clean terms and comparing the wrong
/// one would be a spurious disagreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultKind {
    /// `IRScalar.bool_` — a `0`/`1` wire value.
    Bool,
    /// `IRScalar.int_`.
    Int,
    /// `ir_var <tag> ir_sp0` — a fieldless-enum aggregate.
    EnumTag,
}

impl ResultKind {
    /// Reinterpret the harness's `u8` observation in this chain's vocabulary.
    #[must_use]
    pub fn decode(self, raw: &RunResult) -> RunResult {
        let RunResult::Int(n) = raw else {
            return raw.clone();
        };
        match self {
            ResultKind::Bool => RunResult::Bool(*n != 0),
            ResultKind::Int => RunResult::Int(*n),
            ResultKind::EnumTag => RunResult::EnumTag(*n),
        }
    }
}

/// How faithfully the harness's enum declaration models the real Rust type.
///
/// Recorded per chain and printed, because it bounds what the measurement
/// means. Never inferred optimistically.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumModel {
    /// The Rust enum really is fieldless, so a tag-only declaration is exact.
    Exact,
    /// The Rust enum carries payloads this harness elides. Sound only when the
    /// body provably never reads the payload — see [`payload_is_unread`], which
    /// is a hard precondition checked mechanically, not a comment.
    TagSurrogate,
}

/// Errors that make a differential row REFUSE rather than pass.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DiffError {
    /// A numeral outside the `ir_d0..ir_d16` range the spec defines.
    #[error("no ir_d<N> numeral for {0}: the EvalIR spec defines only 0..=16")]
    NumeralOutOfRange(u32),
    /// A returned value shape with no agreed Clean encoding.
    #[error("no Clean IRScalar encoding for result `{0}`")]
    UnmappedResult(String),
    /// A `TagSurrogate` chain whose body does read the elided payload.
    #[error("chain `{chain}` elides an enum payload the body READS ({detail}); refusing")]
    PayloadRead {
        /// The chain that was refused.
        chain: String,
        /// The offending source line, verbatim.
        detail: String,
    },
}

/// Does the emitted body provably never read the elided enum payload?
///
/// The mechanical side-condition that makes [`EnumModel::TagSurrogate`] sound
/// for a given body. Deliberately syntactic and conservative: the loaded
/// aggregate may flow only into `extractfield <ty> %v, 0`. Any other use — a
/// projection at a nonzero index, a `gep`, a `store`, a call argument — means
/// the payload could be observed and the surrogate is refused.
///
/// This is what keeps "we declared a 5-variant fieldless `Level` because only
/// the tag is read" from being a hopeful assumption: it is checked against the
/// committed emitted text, and a body that grows a payload read turns the row
/// RED instead of quietly measuring the wrong function.
///
/// # Errors
/// [`DiffError::PayloadRead`] when the body does something with the loaded
/// aggregate other than project field 0.
pub fn payload_is_unread(
    chain: &str,
    body_text: &str,
    loaded_value: &str,
) -> Result<(), DiffError> {
    let defines = format!("{loaded_value} =");
    let field0 = format!("{loaded_value}, 0");
    for line in body_text.lines() {
        let code = line.split(';').next().unwrap_or("").trim();
        if code.is_empty() || !code.contains(loaded_value) {
            continue;
        }
        // The defining occurrence (`%2 = load ...`) is fine.
        if code.starts_with(&defines) {
            continue;
        }
        // The only permitted use is a field-0 projection.
        if !(code.contains("extractfield") && code.contains(&field0)) {
            return Err(DiffError::PayloadRead {
                chain: chain.to_owned(),
                detail: code.to_owned(),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_payload_elision_accepts_a_field0_only_body() {
        let body = "bb0(%0: ptr):\n    %2 = load enum.2, ptr %0\n    %3 = extractfield u8 %2, 0\n";
        payload_is_unread("k", body, "%2").expect("only field 0 is projected");
    }

    #[test]
    fn test_payload_elision_refuses_a_body_that_reads_field_1() {
        let body = "bb0(%0: ptr):\n    %2 = load enum.2, ptr %0\n    %3 = extractfield ptr %2, 1\n";
        let err = payload_is_unread("k", body, "%2").expect_err("field 1 is a payload read");
        assert!(matches!(err, DiffError::PayloadRead { .. }));
    }

    #[test]
    fn test_payload_elision_refuses_a_gep_through_the_aggregate() {
        let body = "bb0(%0: ptr):\n    %2 = load enum.2, ptr %0\n    %9 = gep u8 %2, [0]\n";
        assert!(payload_is_unread("k", body, "%2").is_err());
    }

    #[test]
    fn test_payload_elision_ignores_comment_text() {
        // A `#loc` trailer mentioning the value must not be read as a use.
        let body = "bb0(%0: ptr):\n    %2 = load enum.2, ptr %0\n    \
                    %3 = extractfield u8 %2, 0  ; #loc: %2 is fine here\n";
        payload_is_unread("k", body, "%2").expect("comments are not uses");
    }
}

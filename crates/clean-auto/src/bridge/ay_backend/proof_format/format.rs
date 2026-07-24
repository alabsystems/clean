// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof format types and version constants for SMT verification.
//!
//! Defines `ProofFormat` (Alethe, LRAT) and the `proof_formats` constants module.

/// Proof format for SMT verification
///
/// Defines what proof format ay should produce for UNSAT results.
/// See `designs/2026-03-01-smt-proof-verification-pipeline.md` for rationale.
///
/// # ay Solver Flags (Part of #616)
///
/// Each proof format requires specific ay configuration:
///
/// | Format | ay Executor Method | SMT-LIB Option | Notes |
/// |--------|-------------------|----------------|-------|
/// | None | (default) | - | No proof production |
/// | Alethe | `set_produce_proofs(true)` | `(set-option :produce-proofs true)` | Standard SMT proof |
/// | LRAT | `set_produce_proofs(true)` + bit-blast | - | SAT-level only |
///
/// ## Alethe Configuration
///
/// For Alethe proofs using ay Executor directly:
/// ```text
/// let mut executor = ay::executor::Executor::new();
/// executor.set_produce_proofs(true);
/// // ... execute commands ...
/// if let Some(proof) = executor.get_last_proof() {
///     let assertions = &executor.context().assertions;
///     let alethe_str = ay_proof::export_alethe_with_problem_scope(proof, executor.terms(), assertions);
/// }
/// ```
///
/// Note: This example shows ay API usage. For clean integration, use
/// `clean_auto::bridge::ay_contract::{AyProofBackend, ProofProfile}` instead.
///
/// ## LRAT Configuration
///
/// LRAT proofs require bit-blasting to pure SAT. The ay SAT solver produces
/// DRAT/LRAT traces via `ClauseTrace` which can be converted to LRAT format.
/// Currently not directly exposed; use `ProofFormat::Alethe` for theory proofs.
///
/// ## Version Compatibility
///
/// - Alethe 2.0: Current ay export format, compatible with Carcara 1.1+
/// - LRAT: Standard format, compatible with verified checkers (cake_lpr, etc.)
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub(crate) enum ProofFormat {
    /// No proof production (fastest, trusts ay)
    ///
    /// ay flags: None required (default configuration)
    #[default]
    None,
    /// Alethe format proof (standard SMT proof format)
    ///
    /// ay flags: `Executor::set_produce_proofs(true)`
    ///
    /// After UNSAT, retrieve via `Executor::get_last_proof()` and convert
    /// using `ay_proof::export_alethe_with_problem_scope()`.
    Alethe {
        /// Alethe version (e.g., "2.0")
        version: String,
    },
    /// LRAT format proof (for SAT-level verification)
    ///
    /// ay flags: Requires bit-blasting to SAT + `ClauseTrace` extraction
    ///
    /// Note: Direct LRAT export is not yet fully integrated. For theory
    /// proofs, use Alethe format with Carcara verification instead.
    Lrat {
        /// Use binary LRAT format (more compact)
        binary: bool,
    },
}

// =============================================================================
// Expected Proof Format Constants (Part of #615)
// =============================================================================

/// Expected proof format versions and standards
///
/// Part of #615: Enumerate expected proof formats and versions.
/// Part of #619: Document proof format/flags for Carcara compatibility.
///
/// These constants document the proof formats that clean can produce/verify:
///
/// # Alethe Format
///
/// - Version: 2.0 (current standard)
/// - Source: SMT-LIB standard extension
/// - Spec: <https://cvc5.github.io/docs/cvc5-1.0.0/proofs/output_alethe.html>
/// - Verifier: Carcara 1.1+
///
/// ## Carcara Format Requirements
///
/// ay's Alethe export must satisfy these requirements for Carcara acceptance:
///
/// ### Theory-to-Rule Mapping
///
/// | Theory Lemma | Alethe Rule | Carcara Support |
/// |--------------|-------------|-----------------|
/// | EUF transitive | `eq_transitive` | Full |
/// | EUF congruent | `eq_congruent` | Full |
/// | EUF congruent pred | `eq_congruent_pred` | Full |
/// | LRA Farkas | `la_generic` | Full |
/// | LIA generic | `lia_generic` | Full |
/// | BV bitblast | `trust` | Fallback only |
/// | Array axiom | `trust` | Fallback only |
///
/// ### Rule Format Requirements
///
/// **`eq_transitive`:**
/// - Last literal MUST be positive equality (conclusion)
/// - All preceding literals MUST be negated equalities
/// - Example: `(cl (not (= a b)) (not (= b c)) (= a c))`
///
/// **`eq_congruent`:**
/// - Last clause is conclusion: `(= (f a1..an) (f b1..bn))`
/// - Preceding clauses are negated arg equalities: `(not (= ai bi))`
/// - Number of premises MUST equal function arity
///
/// **`eq_congruent_pred`:**
/// - Last two clauses: predicate apps (one positive, one negative)
/// - Preceding clauses: negated arg equalities
///
/// **`la_generic`:**
/// - Coefficients MUST use Real literals: `(/ 1.0 2.0)` not `(/ 1 2)`
/// - Integer coefficients: plain integers (`1`, `2`)
/// - Sum of scaled inequalities must yield `0 >= d` where `d < 0`
///
/// ### Known Compatibility Gaps
///
/// | Feature | Status | Workaround |
/// |---------|--------|------------|
/// | BV bitblast | Uses `trust` | Bit-blast to SAT + LRAT |
/// | Arrays | Uses `trust` | No Alethe standard rule |
/// | XOR rules | Missing | Add `xor_pos1`, `xor_neg1`, etc. |
///
/// See: `reports/research/2026-02-01-r1-carcara-evaluation.md` for full analysis.
///
/// # DRAT/LRAT Formats
///
/// - DRAT: Delete Resolution Asymmetric Tautology (SAT proof format)
/// - LRAT: DRAT + explicit clause deletion hints (verifiable)
/// - Spec: <https://www.cs.utexas.edu/~marijn/drat-trim/>
/// - Verifiers: drat-trim (DRAT), cake_lpr (LRAT, verified)
///
/// # CLRAT Format
///
/// - Compressed LRAT (binary format)
/// - More compact than text LRAT
/// - Same verification semantics
pub(crate) mod proof_formats {
    /// Current Alethe version supported by ay
    pub const ALETHE_VERSION: &str = "2.0";

    /// Minimum Carcara version for Alethe verification
    pub const CARCARA_MIN_VERSION: &str = "1.1.0";

    /// DRAT format identifier (text mode)
    pub const DRAT_TEXT: &str = "drat";

    /// DRAT format identifier (binary mode)
    pub const DRAT_BINARY: &str = "drat-binary";

    /// LRAT format identifier (text mode)
    pub const LRAT_TEXT: &str = "lrat";

    /// LRAT format identifier (binary mode)
    pub const LRAT_BINARY: &str = "lrat-binary";

    /// CLRAT format identifier (compressed LRAT)
    pub const CLRAT: &str = "clrat";

    /// File extension for Alethe proofs
    pub const ALETHE_EXT: &str = ".alethe";

    /// File extension for CLRAT proofs
    pub const CLRAT_EXT: &str = ".clrat";

    /// File extension for DRAT proofs
    pub const DRAT_EXT: &str = ".drat";

    /// File extension for LRAT proofs
    pub const LRAT_EXT: &str = ".lrat";

    // =========================================================================
    // Carcara Compatibility Constants (Part of #619)
    // =========================================================================

    /// Theories with full Carcara support (no `trust` rule fallback)
    ///
    /// These theories have complete Alethe rule coverage in Carcara:
    /// - QF_LIA: Linear Integer Arithmetic (`lia_generic`)
    /// - QF_LRA: Linear Real Arithmetic (`la_generic`)
    /// - QF_UF: Uninterpreted Functions (`eq_transitive`, `eq_congruent`, `eq_congruent_pred`)
    /// - QF_UFLIA: UF + LIA combination
    /// - QF_UFLRA: UF + LRA combination
    pub const CARCARA_VERIFIED_THEORIES: &[&str] =
        &["QF_LIA", "QF_LRA", "QF_UF", "QF_UFLIA", "QF_UFLRA"];

    /// Theories with partial Carcara support (may use `trust` rule)
    ///
    /// These theories may fall back to `trust` for some lemmas:
    /// - QF_BV: Bitvectors (operation-specific rules only, no generic `bv_bitblast`)
    /// - QF_ABV: Arrays + BV (no standard array axiom rule)
    /// - QF_AUFLIA: Arrays + UF + LIA (no standard array axiom rule)
    pub const CARCARA_PARTIAL_THEORIES: &[&str] = &["QF_BV", "QF_ABV", "QF_AUFLIA"];

    /// Alethe rules that indicate unverified content (Carcara accepts but doesn't check)
    ///
    /// When proofs contain these rules, the corresponding lemma is trusted, not verified.
    pub const UNVERIFIED_ALETHE_RULES: &[&str] = &["trust", "hole"];
}

impl ProofFormat {
    /// Create an Alethe format with the current standard version
    pub fn alethe() -> Self {
        Self::Alethe {
            version: proof_formats::ALETHE_VERSION.to_string(),
        }
    }

    /// Create an LRAT format with text output
    #[cfg(test)]
    pub fn lrat_text() -> Self {
        Self::Lrat { binary: false }
    }

    /// Create an LRAT format with binary output
    #[cfg(test)]
    pub fn lrat_binary() -> Self {
        Self::Lrat { binary: true }
    }

    /// Get the format identifier string
    #[cfg(test)]
    pub fn format_id(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Alethe { .. } => "alethe",
            Self::Lrat { binary: false } => proof_formats::LRAT_TEXT,
            Self::Lrat { binary: true } => proof_formats::LRAT_BINARY,
        }
    }

    /// Get the file extension for this format
    #[cfg(test)]
    pub fn file_extension(&self) -> &'static str {
        match self {
            Self::None => "",
            Self::Alethe { .. } => proof_formats::ALETHE_EXT,
            Self::Lrat { .. } => proof_formats::LRAT_EXT,
        }
    }
}

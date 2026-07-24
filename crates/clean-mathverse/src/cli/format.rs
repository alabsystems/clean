// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared display helpers for `clean mathverse <verb>` output.
//!
//! Keeps the enum-to-string mappings in one place so JSON and table writers
//! agree byte-for-byte. Preserves the labels used by the deprecated
//! `mathverse_search` binary so downstream scripts that parse its output keep
//! working through the compat shim.

use crate::types::{ContentDomain, DeclKind, ImportConfidence, SourceSystem};

/// Return a stable human-readable name for a source-system byte.
///
/// Falls back to `"Unknown"` when the byte is outside the live
/// [`SourceSystem`] range. This must match `mathverse_search`'s output
/// character-for-character — scripts downstream parse these labels.
pub(crate) fn source_system_name(byte: u8) -> &'static str {
    match SourceSystem::try_from(byte) {
        Ok(sys) => source_system_str(sys),
        Err(_) => "Unknown",
    }
}

/// Helper: map a concrete [`SourceSystem`] to its display label.
fn source_system_str(sys: SourceSystem) -> &'static str {
    match sys {
        SourceSystem::Lean4 => "Lean4",
        SourceSystem::Coq => "Coq",
        SourceSystem::Agda => "Agda",
        SourceSystem::Idris2 => "Idris2",
        SourceSystem::FStar => "F*",
        SourceSystem::Cedille => "Cedille",
        SourceSystem::Isabelle => "Isabelle",
        SourceSystem::HolLight => "HOL Light",
        SourceSystem::Hol4 => "HOL4",
        SourceSystem::Metamath => "Metamath",
        SourceSystem::Mizar => "Mizar",
        SourceSystem::Dafny => "Dafny",
        SourceSystem::Why3 => "Why3",
        SourceSystem::Nuprl => "Nuprl",
        SourceSystem::Pvs => "PVS",
        SourceSystem::Acl2 => "ACL2",
        SourceSystem::LiquidHaskell => "LiquidHaskell",
        SourceSystem::Key => "KeY",
        SourceSystem::FramaC => "Frama-C",
        SourceSystem::Spark => "SPARK",
        SourceSystem::GammaCrown => "gamma-crown",
        SourceSystem::AlphaBetaCrown => "alpha-beta-CROWN",
        SourceSystem::Z3 => "Z3",
        SourceSystem::Cvc5 => "cvc5",
        SourceSystem::Vampire => "Vampire",
        SourceSystem::CaDiCaL => "CaDiCaL",
        SourceSystem::Tlc => "TLC",
        SourceSystem::CleanNative => "clean",
        SourceSystem::KeyFramacSpark => "KeY/Frama-C/SPARK",
        SourceSystem::SmtSolver => "SMT",
        SourceSystem::SatSolver => "SAT",
        SourceSystem::Atp => "ATP",
        SourceSystem::Arxiv => "arXiv",
        SourceSystem::Dedukti => "Dedukti",
        SourceSystem::Lambdapi => "Lambdapi",
        SourceSystem::Abella => "Abella",
        SourceSystem::Beluga => "Beluga",
        SourceSystem::Twelf => "Twelf",
        SourceSystem::Naproche => "Naproche",
        SourceSystem::Minlog => "Minlog",
        SourceSystem::Arend => "Arend",
        SourceSystem::Mm0 => "Metamath Zero",
        SourceSystem::Kind2 => "Kind2",
        SourceSystem::Rzk => "Rzk",
        SourceSystem::Ats2 => "ATS2",
        SourceSystem::Latte => "LaTTe",
        SourceSystem::CubicalTT => "cubicaltt",
        SourceSystem::Cooltt => "cooltt",
        SourceSystem::Redtt => "redtt",
        SourceSystem::Verus => "Verus",
        SourceSystem::Creusot => "Creusot",
        SourceSystem::Kani => "Kani",
        SourceSystem::Prusti => "Prusti",
        SourceSystem::Aeneas => "Aeneas",
        SourceSystem::Hax => "Hax",
        SourceSystem::CreuSat => "CreuSAT",
        SourceSystem::Stainless => "Stainless",
        SourceSystem::Lisa => "LISA",
        SourceSystem::MoveProver => "Move Prover",
        SourceSystem::Boogie => "Boogie",
        SourceSystem::Viper => "Viper",
        SourceSystem::VeriFast => "VeriFast",
        SourceSystem::Sail => "Sail",
        SourceSystem::KFramework => "K Framework",
        SourceSystem::Alloy => "Alloy",
        SourceSystem::PLang => "P",
        SourceSystem::EthAct => "Ethereum Act",
        SourceSystem::SvBenchmarks => "SV-COMP",
        SourceSystem::Matita => "Matita",
        SourceSystem::Cake => "Cake",
    }
}

/// Return a stable human-readable name for an [`ImportConfidence`] byte.
pub(crate) fn confidence_name(byte: u8) -> &'static str {
    match ImportConfidence::try_from(byte) {
        Ok(ImportConfidence::KernelVerified) => "KernelVerified",
        Ok(ImportConfidence::SourceVerified) => "SourceVerified",
        Ok(ImportConfidence::Translated) => "Translated",
        Ok(ImportConfidence::KernelCheckedConditional) => "KernelCheckedConditional",
        Ok(ImportConfidence::KernelBridged) => "KernelBridged",
        Ok(ImportConfidence::Axiomatized) => "Axiomatized",
        Ok(ImportConfidence::Unverified) => "Unverified",
        Err(_) => "Unknown",
    }
}

/// Return a stable human-readable name for a [`ContentDomain`] byte.
pub(crate) fn domain_name(byte: u8) -> &'static str {
    match ContentDomain::try_from(byte) {
        Ok(ContentDomain::PureMath) => "PureMath",
        Ok(ContentDomain::Software) => "Software",
        Ok(ContentDomain::Complexity) => "Complexity",
        Ok(ContentDomain::NnVerification) => "NnVerification",
        Ok(ContentDomain::Physics) => "Physics",
        Ok(ContentDomain::Logic) => "Logic",
        Ok(ContentDomain::Cryptography) => "Cryptography",
        Err(_) => "Unknown",
    }
}

/// Return a stable lowercase name for a [`DeclKind`] byte.
pub(crate) fn decl_kind_name(byte: u8) -> &'static str {
    match DeclKind::try_from(byte) {
        Ok(DeclKind::Theorem) => "theorem",
        Ok(DeclKind::Definition) => "definition",
        Ok(DeclKind::Axiom) => "axiom",
        Ok(DeclKind::Opaque) => "opaque",
        Ok(DeclKind::Inductive) => "inductive",
        Ok(DeclKind::Constructor) => "constructor",
        Ok(DeclKind::Recursor) => "recursor",
        Ok(DeclKind::Quot) => "quotient",
        Ok(_) => "other",
        Err(_) => "unknown",
    }
}

/// Truncate a string to `max_len` characters, appending `"..."` if truncated.
pub(crate) fn truncate(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len.saturating_sub(3)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_system_name_known_bytes_resolve() {
        assert_eq!(source_system_name(SourceSystem::Lean4 as u8), "Lean4");
        assert_eq!(source_system_name(SourceSystem::Metamath as u8), "Metamath");
    }

    #[test]
    fn test_source_system_name_unknown_byte() {
        assert_eq!(source_system_name(255), "Unknown");
    }

    #[test]
    fn test_confidence_name_variants() {
        assert_eq!(confidence_name(0), "KernelVerified");
        assert_eq!(confidence_name(255), "Unknown");
    }

    #[test]
    fn test_domain_name_variants() {
        assert_eq!(domain_name(0), "PureMath");
        assert_eq!(domain_name(255), "Unknown");
    }

    #[test]
    fn test_decl_kind_name_variants() {
        assert_eq!(decl_kind_name(0), "theorem");
        assert_eq!(decl_kind_name(255), "unknown");
    }

    #[test]
    fn test_truncate_short_stays_unchanged() {
        assert_eq!(truncate("hello", 10), "hello");
    }

    #[test]
    fn test_truncate_long_gets_ellipsis() {
        let result = truncate("abcdefghijklmnop", 10);
        assert!(result.ends_with("..."));
        assert!(result.len() <= 10);
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alethe rule-kind taxonomy for the SMT proof DAG.
//!
//! Split out of [`crate::smt_verify::dag`]: the rule enumeration and its
//! `Display` rendering are a self-contained taxonomy of the Alethe proof
//! format, independent of the DAG's term/step arenas. `dag` re-exports
//! [`AletheRuleKind`], so `smt_verify::dag::AletheRuleKind` keeps resolving.

/// Alethe rule kind classification.
///
/// Covers the Alethe proof format rules. Not all are semantically checked
/// in Phase 1; unchecked rules are structurally accepted or trusted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AletheRuleKind {
    // Boolean rules
    True,
    False,
    NotTrue,
    NotFalse,
    AndPos(u32),
    AndNeg,
    OrPos,
    OrNeg(u32),
    ImpliesPos,
    ImpliesNeg1,
    ImpliesNeg2,
    EquivPos1,
    EquivPos2,
    EquivNeg1,
    EquivNeg2,
    ItePos1,
    ItePos2,
    IteNeg1,
    IteNeg2,
    Contraction,

    // Resolution
    Resolution,
    ThResolution,

    // EUF step rules
    Refl,
    Symm,
    Trans,
    Cong,

    // EUF theory lemma step rules
    EqReflexive,
    EqTransitive,
    EqCongruent,
    EqCongruentPred,

    // LRA rules
    LaGeneric,
    LaTautology,
    LaDisequality,
    LaTotality,

    // LIA
    LiaGeneric,

    // BV
    BvBitblast,

    // Array
    ReadOverWritePos,
    ReadOverWriteNeg,
    Extensionality,

    // FP
    FpToBv,

    // String
    StringLength,
    StringDecompose,
    StringCodeInj,

    // Quantifier
    ForallInst,
    Skolem,

    // Subproof
    Subproof,
    Bind,

    // Simplification (structural)
    AllSimplify,
    BoolSimplify,
    ArithSimplify,

    // Trust / hole
    Trust,
    Hole,

    // DRUP
    Drup,

    /// Unknown or user-defined rule.
    Other(String),
}

impl std::fmt::Display for AletheRuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AletheRuleKind::True => write!(f, "true"),
            AletheRuleKind::False => write!(f, "false"),
            AletheRuleKind::Resolution => write!(f, "resolution"),
            AletheRuleKind::ThResolution => write!(f, "th_resolution"),
            AletheRuleKind::Refl => write!(f, "refl"),
            AletheRuleKind::Symm => write!(f, "symm"),
            AletheRuleKind::Trans => write!(f, "trans"),
            AletheRuleKind::Cong => write!(f, "cong"),
            AletheRuleKind::EqReflexive => write!(f, "eq_reflexive"),
            AletheRuleKind::EqTransitive => write!(f, "eq_transitive"),
            AletheRuleKind::EqCongruent => write!(f, "eq_congruent"),
            AletheRuleKind::EqCongruentPred => write!(f, "eq_congruent_pred"),
            AletheRuleKind::LaGeneric => write!(f, "la_generic"),
            AletheRuleKind::LaTautology => write!(f, "la_tautology"),
            AletheRuleKind::Trust => write!(f, "trust"),
            AletheRuleKind::Hole => write!(f, "hole"),
            AletheRuleKind::Other(name) => write!(f, "{name}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

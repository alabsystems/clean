// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ay_core → clean view-type conversion functions for the proof-trace adapter.
//!
//! Extracted from `trace.rs` to keep that module under the 500-line limit.
//! These are pure mapping functions with no proof/term-store state.

use ay_core::{
    AletheRule, Constant, CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, TheoryLemmaKind,
};

use super::trace::{ConstantView, FarkasView, LiaAnnotationView, RuleView, TheoryLemmaView};

pub(super) fn rule_view(rule: &AletheRule) -> RuleView {
    match rule {
        AletheRule::ThResolution => RuleView::ThResolution,
        AletheRule::Or => RuleView::Or,
        AletheRule::OrPos(_) => RuleView::OrPos,
        AletheRule::OrNeg => RuleView::OrNeg,
        AletheRule::EquivPos1 => RuleView::EquivPos1,
        AletheRule::EquivPos2 => RuleView::EquivPos2,
        AletheRule::EquivNeg1 => RuleView::EquivNeg1,
        AletheRule::EquivNeg2 => RuleView::EquivNeg2,
        AletheRule::XorPos1 => RuleView::XorPos1,
        AletheRule::XorPos2 => RuleView::XorPos2,
        AletheRule::XorNeg1 => RuleView::XorNeg1,
        AletheRule::XorNeg2 => RuleView::XorNeg2,
        AletheRule::AndPos(i) => RuleView::AndPos(*i),
        AletheRule::AndNeg => RuleView::AndNeg,
        AletheRule::EqReflexive => RuleView::EqReflexive,
        AletheRule::Trust => RuleView::Trust,
        AletheRule::Hole => RuleView::Hole,
        AletheRule::Symm => RuleView::Symm,
        AletheRule::Trans => RuleView::Trans,
        AletheRule::True => RuleView::True,
        AletheRule::False => RuleView::False,
        AletheRule::Resolution => RuleView::Resolution,
        AletheRule::Contraction => RuleView::Contraction,
        AletheRule::EqCongruent => RuleView::EqCongruent,
        AletheRule::Cong => RuleView::Cong,
        AletheRule::EqTransitive => RuleView::EqTransitive,
        AletheRule::Implies => RuleView::Implies,
        AletheRule::ImpliesPos => RuleView::ImpliesPos,
        AletheRule::ImpliesNeg1 => RuleView::ImpliesNeg1,
        AletheRule::ImpliesNeg2 => RuleView::ImpliesNeg2,
        AletheRule::NotImplies1 => RuleView::NotImplies1,
        AletheRule::NotImplies2 => RuleView::NotImplies2,
        _ => RuleView::Other,
    }
}

pub(super) fn theory_lemma_view(kind: &TheoryLemmaKind) -> TheoryLemmaView {
    match kind {
        TheoryLemmaKind::EufTransitive => TheoryLemmaView::EufTransitive,
        TheoryLemmaKind::EufCongruent => TheoryLemmaView::EufCongruent,
        TheoryLemmaKind::EufCongruentPred => TheoryLemmaView::EufCongruentPred,
        TheoryLemmaKind::LraFarkas => TheoryLemmaView::LraFarkas,
        TheoryLemmaKind::LiaGeneric => TheoryLemmaView::LiaGeneric,
        TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. } => {
            TheoryLemmaView::BvBitBlast
        }
        TheoryLemmaKind::ArraySelectStore { .. } | TheoryLemmaKind::ArrayExtensionality => {
            TheoryLemmaView::ArrayAxiom
        }
        TheoryLemmaKind::FpToBv { .. }
        | TheoryLemmaKind::StringLengthAxiom
        | TheoryLemmaKind::StringContentAxiom
        | TheoryLemmaKind::StringNormalForm => TheoryLemmaView::Other,
        TheoryLemmaKind::Generic => TheoryLemmaView::Generic,
        _ => TheoryLemmaView::Other,
    }
}

pub(super) fn farkas_view(ann: &FarkasAnnotation) -> FarkasView {
    FarkasView {
        coefficient_count: ann.coefficients.len(),
        is_valid: ann.is_valid(),
        all_unit_coefficients: ann.coefficients.iter().all(|c| *c == 1_i64.into()),
    }
}

pub(super) fn lia_annotation_view(ann: &LiaAnnotation) -> LiaAnnotationView {
    match ann {
        LiaAnnotation::BoundsGap => LiaAnnotationView::BoundsGap,
        LiaAnnotation::Divisibility => LiaAnnotationView::Divisibility,
        LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation { divisor, .. }) => {
            LiaAnnotationView::CuttingPlane { divisor: *divisor }
        }
        // LiaAnnotation is #[non_exhaustive] — future ay variants fall back
        // to BoundsGap as the most conservative LIA proof shape.
        _ => LiaAnnotationView::BoundsGap,
    }
}

pub(super) fn constant_view(c: &Constant) -> ConstantView<'_> {
    match c {
        Constant::Bool(b) => ConstantView::Bool(*b),
        Constant::Int(n) => ConstantView::Int(n),
        Constant::Rational(r) => ConstantView::Rational(r),
        Constant::BitVec { value, width } => ConstantView::BitVec {
            value,
            width: *width,
        },
        Constant::String(s) => ConstantView::String(s),
        _ => ConstantView::Unknown,
    }
}

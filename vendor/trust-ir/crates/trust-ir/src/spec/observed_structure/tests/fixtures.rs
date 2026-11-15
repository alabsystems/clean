// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn anchor(machine: &str, action: &str) -> SpecAnchor {
    SpecAnchor {
        machine: machine.into(),
        action: action.into(),
        rust_symbol: "symbolλ".into(),
        span: "opaque".into(),
        project: Some("project".into()),
        function: None,
        projection_target: None,
    }
}
pub(super) fn waiver(machine: &str, action: &str) -> SpecWaiver {
    SpecWaiver {
        machine: machine.into(),
        action: action.into(),
        reason: "reasonλ".into(),
    }
}
pub(super) fn proof(machine: &str, action: &str) -> SpecProof {
    SpecProof {
        machine: machine.into(),
        action: action.into(),
        proof_name: "proofλ".into(),
        kind: ProofKind::Kani,
    }
}
pub(super) fn valid() -> Vec<SpecModule> {
    let mut spec = SpecModule::new("M");
    spec.actions = vec!["a".into()];
    spec.vars = vec![SpecVar::new("x", "Int").with_sort(ClauseSort::Int)];
    spec.invariants = vec![
        SpecInvariant::new("I", "opaque")
            .with_typed(formula(ClausePlace::SpecVar { index: 0 }, ClauseSort::Int)),
    ];
    spec.anchors.push(anchor("M", "a"));
    vec![spec]
}
pub(super) fn compact() -> Vec<SpecModule> {
    let mut spec = SpecModule::new("M");
    spec.actions = vec!["".into()];
    vec![spec]
}
pub(super) fn formula(place: ClausePlace, sort: ClauseSort) -> ProofFormula {
    let mut formula = ProofFormula::new("opaque", "opaque");
    formula.bindings = vec![("x".into(), ClauseBinding { place, sort })];
    formula
}
pub(super) fn deep_sort() -> ClauseSort {
    ClauseSort::Datatype {
        name: "Dλ'\"\n\0".into(),
        constructors: vec![(
            "Cλ".into(),
            vec![(
                "fieldλ".into(),
                ClauseSort::Array(
                    Box::new(ClauseSort::BitVec(u32::MAX)),
                    Box::new(ClauseSort::Float {
                        eb: 0,
                        sb: u32::MAX,
                    }),
                ),
            )],
        )],
    }
}

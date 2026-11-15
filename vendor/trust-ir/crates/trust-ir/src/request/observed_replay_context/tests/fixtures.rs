// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn source(id: u32) -> NativeObligationSource {
    NativeObligationSource {
        obligation: ProofId::new(id),
        public_obligation_id: "source-data-only".into(),
        function: None,
        span: Some(SourceSpan {
            file: 0,
            line: 1,
            col: 2,
        }),
        assertion_id: Some(NativeAssertionId::new(7)),
        cause: NativeObligationCause::Assert,
        monomorphization: None,
        facts: vec![],
    }
}
pub(super) fn atom() -> NativeReplayAtom {
    NativeReplayAtom::assumption(
        NativeReplayAtomId::new(0),
        ProofFormula::smtlib2("true", "Bool"),
    )
}
pub(super) fn fixture() -> Input {
    let mut module = Module::new("replay-context-data");
    module.predicates = vec![Pred::Top, Pred::NonZero];
    Input {
        context: NativeReplayContext {
            atoms: vec![atom()],
            unsupported_modes: vec![],
        },
        obligations: vec![ProofId::new(1)],
        facts: NativeCompilerFacts {
            obligation_sources: vec![source(1)],
            ..NativeCompilerFacts::default()
        },
        module,
    }
}
pub(super) fn bad() -> Input {
    let mut i = fixture();
    i.context.unsupported_modes.push(NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::Other,
        "raw detail",
    ));
    let mut a = atom();
    a.formula = ProofFormula::smtlib2("true", "Bool");
    a.formula.smtlib = Some("false".into());
    a.payload_digest = ProofDigest::sha256([1; 32]);
    a.kind = NativeReplayAtomKind::Assertion;
    a.obligation = Some(ProofId::new(2));
    a.assertion_id = Some(NativeAssertionId::new(99));
    a.span = Some(SourceSpan {
        file: 0,
        line: 99,
        col: 4,
    });
    i.context.atoms.push(a);
    i.facts.obligation_sources.push(source(2));
    i
}
pub(super) fn fixed_digest(a: &mut NativeReplayAtom) {
    a.payload_digest = a.expected_payload_digest();
}

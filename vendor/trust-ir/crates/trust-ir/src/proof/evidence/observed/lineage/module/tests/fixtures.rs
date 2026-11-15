// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn fixture() -> (Module, ProofObligation, CertificateBinding) {
    let mut module = Module::new("");
    module.functions = vec![Function::new(
        FuncId::new(77),
        "owneré🦀",
        FuncTyId::new(0),
        BlockId::new(9),
    )];
    let mut row = ProofObligation::new(
        ProofId::new(999),
        ObligationKind::Custom {
            namespace: "n\0é".into(),
            name: "opaque".into(),
        },
        ProofStatus::Certified,
        "description",
    );
    row.function = Some(FuncId::new(77));
    row.site = Some(crate::proof::ObligationSite::new(
        FuncId::new(77),
        BlockId::new(9),
        u32::MAX,
    ));
    let mut f = ProofFormula::new("schema", "payload");
    f.smtlib = Some("smtlib".into());
    f.sort = Some("sort".into());
    f.bindings = vec![(
        "x".into(),
        ClauseBinding {
            sort: ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Int)),
            place: ClausePlace::Value(ValueId::new(41)),
        },
    )];
    row.formula = Some(f);
    row.spec = Some(SpecObligationRef::new("machine", "temporal"));
    row.source = Some(
        ProofObligationSourceIdentity::new("source\0é", "assertion")
            .with_range(ProofObligationSourceRange {
                file: 4,
                start_line: 9,
                start_col: 8,
                end_line: 1,
                end_col: 0,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "public".into(),
                semantic_digest: ProofDigest {
                    algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                    bytes: [9; 32],
                },
            }),
    );
    (
        module,
        row,
        CertificateBinding::new(ProofDigest::sha256([3; 32]), ProofDigest::sha256([4; 32])),
    )
}
pub(super) fn function(id: u32, name: &str) -> Function {
    Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0))
}
pub(super) fn evidence(lineage: ProofDigest, binding: Option<CertificateBinding>) -> ProofEvidence {
    ProofEvidence::CleanCic {
        term: vec![1],
        context: vec![2],
        lineage,
        kernel_recheck: binding.map(|b| CleanCicKernelRecheck {
            module: "raw".into(),
            theorems: vec!["whole theorem".into()],
            anchor: "raw-anchor".into(),
            allowed_axioms: vec![],
            binding: Some(Box::new(b)),
        }),
    }
}
pub(super) fn plain() -> (Module, ProofObligation) {
    let (m, mut row, _) = fixture();
    row.formula = None;
    row.source = None;
    row.spec = None;
    row.description.clear();
    row.kind = ObligationKind::Precondition;
    (m, row)
}

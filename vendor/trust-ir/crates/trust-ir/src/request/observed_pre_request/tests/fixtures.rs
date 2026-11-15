// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn clean() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.requests.clear();
    b.evidence_bundles.clear();
    b.module = Module::new("pre-request");
    b.module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(7),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "one",
        )
        .with_formula(ProofFormula::smtlib2("true", "Bool")),
    );
    b.compiler_facts = super::super::super::NativeCompilerFacts::default();
    b.trust_ir_module_digest = b.module.stable_digest();
    b.lineage.nodes[0].obligations = vec![ProofId::new(7)];
    b.lineage.nodes[0].certificates.clear();
    b.lineage.nodes[0].target_module = b.trust_ir_module_digest;
    b
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = clean();
    b.schema_version = u32::MAX;
    b.module.types.push(Ty::Error);
    b.module.completeness = Some(ModuleCompleteness::Complete);
    let mut f = Function::new(
        FuncId::new(9),
        "raw 'λ\0尾",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    f.producer = Some(Producer::TRust);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(InstrNode::new(Inst::Borrow {
        ptr: ValueId::new(0),
    }));
    f.blocks.push(block);
    b.module.functions.push(f);
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        },
    };
    b.provenance.producer_version.clear();
    b.provenance.source_languages.clear();
    b.provenance.toolchain[0].name = " \tλ".into();
    b.provenance.toolchain[0].version = Some("\u{2003}".into());
    b.serialization.canonical_order = false;
    b.serialization.sort_unordered_sets = false;
    b.serialization.messagepack_named_fields = false;
    b.diagnostics.include_source_spans = false;
    b.diagnostics.include_lineage = false;
    b.diagnostics.emit_counterexamples = true;
    b.diagnostics.max_counterexamples = 0;
    b.lineage.schema_version = u32::MAX;
    let f = b.module.proof_obligations[0].formula.as_mut().unwrap();
    f.payload = "false".into();
    let mono = crate::request::tests::native_bundle()
        .compiler_facts
        .monomorphizations
        .remove(0);
    b.compiler_facts.monomorphizations = vec![mono.clone(), mono];
    b
}

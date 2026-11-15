// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn digest(n: u8) -> ProofDigest {
    ProofDigest::sha256([n; 32])
}
pub(super) fn node(id: u32, source: u8, target: u8) -> ProofLineageNode {
    ProofLineageNode::new(
        ProofLineageId::new(id),
        ProofTransform::new(ProofTransformStage::Frontend, "raw", "producer", "1"),
        digest(source),
        digest(target),
    )
}
pub(super) fn fixture() -> NativeVerificationBundle {
    let mut m = Module::new("bundle-two-leaves");
    for id in [9, 1, 9] {
        let mut f = Function::new(
            FuncId::new(id),
            "raw' \0λ🦀".repeat(450),
            FuncTyId::new(0),
            BlockId::new(7),
        );
        f.producer = Some(Producer::TRust);
        for b in [u32::MAX, 0] {
            let mut block = Block::new(BlockId::new(b));
            for inst in [
                Inst::Borrow {
                    ptr: ValueId::new(0),
                },
                Inst::Copy {
                    ty: crate::Ty::Ptr,
                    operand: ValueId::new(0),
                },
                Inst::BorrowMut {
                    ptr: ValueId::new(0),
                },
                Inst::EndBorrow {
                    borrow_ptr: ValueId::new(0),
                },
            ] {
                block.body.push(InstrNode::new(inst));
            }
            f.blocks.push(block);
        }
        m.functions.push(f);
    }
    let mut b = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: digest(1),
        },
        digest(2),
        m,
        ProofLineageManifest::new(),
    );
    b.lineage.nodes = vec![node(9, 8, 9), node(1, 7, 8), node(9, 6, 7)];
    b
}
pub(super) fn state_run(
    state: &mut State,
    bundle: &NativeVerificationBundle,
    rule: Rule,
    w: &mut Work<'_, '_, Observer>,
) -> R {
    match rule {
        Rule::Reference => state.references(bundle, w),
        Rule::Lineage => state.lineage(bundle, w),
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn abi() -> SignatureAbi {
    SignatureAbi {
        target: AbiTarget {
            triple: "example-target".into(),
            data_layout: "e-p:64:64".into(),
            abi: "c".into(),
            cpu: "generic".into(),
            features: vec!["feature".into()],
            target_spec: "identity-only".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "producer λ".into(),
            revision: "revision".into(),
        },
        convention: "c".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    }
}

pub(super) fn module() -> Module {
    let mut module = Module::new("wire_λ");
    module.files = vec!["first.rs".into(), "second.rs".into(), "first.rs".into()];
    module.func_types.push(FuncTy::unrecorded(
        vec![Ty::Tuple(vec![Ty::I32, Ty::Ref(Box::new(Ty::U8))])],
        vec![],
        false,
    ));
    let mut function = Function::new(FuncId::new(17), "wire_λ", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(crate::Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module.functions.push(function);
    module.globals.push(Global {
        name: "wire_λ".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Record(vec![
            (
                "field".into(),
                Constant::Bytes {
                    data: (0..4097).map(|n| (n % 251) as u8).collect(),
                    utf8: false,
                },
            ),
            (
                "other".into(),
                Constant::Splat {
                    elem: Box::new(Constant::Int(-1)),
                    len: u64::MAX,
                },
            ),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: crate::Visibility::Default,
        retained: false,
    });
    module
}

pub(super) fn all() -> Module {
    let mut m = module();
    m.types = vec![Ty::Error, Ty::Tuple(vec![Ty::Error])];
    m.completeness = Some(ModuleCompleteness::Complete);
    m.functions[0].scopes = Some(vec![
        ScopeData::new(None, None),
        ScopeData {
            parent: Some(0),
            span: None,
            inlined_at: Some(crate::value::InlinedAt {
                span: SourceSpan {
                    file: 0,
                    line: 1,
                    col: 1,
                },
                callee: "first raw λ\0".into(),
            }),
        },
    ]);
    let mut a = abi();
    a.frontend.name = "x".repeat((1 << 20) + 1);
    m.func_types[0].abi = Some(a);
    m
}

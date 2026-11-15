// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;
use trust_ir::function_dependencies::{
    DependencyNode, DependencyRefusalKind, inspect_defined_function_dependencies,
    inspect_function_dependencies,
};
use trust_ir::value::{BlockId, FuncId, FuncTyId};
use trust_ir::{Block, Function, Inst, InstrNode, Module};

fn chain(count: u32) -> Module {
    let mut module = Module::new("defined-roots");
    module
        .func_types
        .push(trust_ir::ty::FuncTy::unrecorded(vec![], vec![], false));
    for index in 0..count {
        let mut function = Function::new(
            FuncId::new(index * 7 + 3),
            format!("f{index}"),
            FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        if index + 1 < count {
            block.body.push(InstrNode::new(Inst::Call {
                callee: FuncId::new((index + 1) * 7 + 3),
                args: vec![],
            }));
        }
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.functions.push(function);
    }
    module
}

#[test]
fn defined_roots_equal_single_root_union_without_rewalking_shared_suffixes() {
    for count in [1, 2, 16, 64] {
        let module = chain(count);
        let batch = inspect_defined_function_dependencies(&module);
        assert!(std::ptr::eq(batch.module(), &module));
        assert_eq!(batch.roots().len(), count as usize);
        assert!(batch.refusals().is_empty(), "{:?}", batch.refusals());
        let mut expected = BTreeSet::new();
        let mut separate_edges = 0;
        for function in &module.functions {
            let single = inspect_function_dependencies(&module, function.id);
            assert_eq!(single.root(), function.id);
            expected.extend(single.nodes().iter().copied());
            separate_edges += single.edges().len();
        }
        assert_eq!(batch.nodes(), &expected);
        assert_eq!(batch.nodes().len(), count as usize + 1);
        // N root edges, N signature edges and N-1 stored call edges. The
        // separate traversals record N*(N+1) edges over the same chain.
        assert_eq!(batch.edges().len(), 3 * count as usize - 1);
        assert_eq!(separate_edges, (count * (count + 1)) as usize);
    }
}

#[test]
fn bodyless_dependencies_are_not_roots_and_keep_their_named_refusal() {
    let mut module = chain(2);
    let external = FuncId::new(100);
    module.functions[1].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: external,
            args: vec![],
        }),
    );
    module.functions.push(Function::new(
        external,
        "external",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    module.functions.push(Function::new(
        FuncId::new(200),
        "unused_external",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    let batch = inspect_defined_function_dependencies(&module);
    assert_eq!(batch.roots(), &[FuncId::new(3), FuncId::new(10)]);
    assert!(batch.nodes().contains(&DependencyNode::Function(external)));
    assert!(
        !batch
            .nodes()
            .contains(&DependencyNode::Function(FuncId::new(200)))
    );
    assert_eq!(batch.refusals().len(), 1);
    assert_eq!(
        batch.refusals()[0].kind,
        DependencyRefusalKind::BodylessFunction(external)
    );
}

#[test]
fn empty_roots_and_ambiguous_ids_preserve_module_refusals() {
    let mut empty = Module::new("empty");
    empty.global_asm.push("opaque module assembly".into());
    let batch = inspect_defined_function_dependencies(&empty);
    assert!(batch.roots().is_empty());
    assert!(batch.nodes().is_empty());
    assert_eq!(batch.refusals().len(), 1);
    assert_eq!(
        batch.refusals()[0].kind,
        DependencyRefusalKind::GlobalAssembly
    );

    let mut ambiguous = chain(2);
    ambiguous.functions[1].id = ambiguous.functions[0].id;
    let batch = inspect_defined_function_dependencies(&ambiguous);
    assert!(batch.refusals().iter().any(|refusal| {
        refusal.kind == DependencyRefusalKind::Ambiguous(DependencyNode::Function(FuncId::new(3)))
    }));
}

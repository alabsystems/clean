// Copyright 2026 Andrew Yates. Apache-2.0.
//! Pending input to the canonical SemR body checker.
//!
//! This reader extracts an actual level-R Boolean conjunction body. It does
//! not interpret the body, prove its source correspondence, or mint evidence.
//! In particular a successful read remains pending until the original Clean
//! theorem checks a derivation over the canonical decoded module. Borrowing
//! the module prevents replacing its body between extraction and quotation.

use crate::inst::{BinOp, Inst};
use crate::{BlockId, FuncId, FuncTyId, Function, Module, Ty, ValueId};
use std::collections::BTreeMap;

mod candidate;

/// A named missing capability or malformed checker input, never a proof result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    EmptyRequest,
    DuplicateRequest,
    MissingFunction,
    DuplicateFunction,
    MissingSignature,
    Signature,
    BodyShape,
    Entry,
    Parameters,
    Operation,
    Result,
    Return,
}

/// Structural data read from an immutable actual module; not a certificate.
#[derive(Debug)]
pub struct PendingBoolBody<'a> {
    module: &'a Module,
    function: FuncId,
    signature: FuncTyId,
    entry: BlockId,
    parameters: [ValueId; 2],
    result: ValueId,
    operation: BinOp,
}

impl PendingBoolBody<'_> {
    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn signature(&self) -> FuncTyId {
        self.signature
    }
    pub fn entry(&self) -> BlockId {
        self.entry
    }
    pub fn parameters(&self) -> [ValueId; 2] {
        self.parameters
    }
    pub fn result(&self) -> ValueId {
        self.result
    }
    pub fn operation(&self) -> BinOp {
        self.operation
    }

    /// The existing canonical wire input for SemR's decoder. Encoding is
    /// deferred: an inventory must not serialize the whole module per body.
    /// Byte identity alone establishes no semantic correspondence.
    pub fn canonical_module_bytes(&self) -> Result<Vec<u8>, crate::BinaryProjectionError> {
        crate::binary::serialize_module(self.module)
    }
}

/// One immutable actual-module index for an entire body inventory. Duplicate
/// function IDs remain refusals, rather than selecting an arbitrary body.
pub struct BoolBodyReader<'a> {
    module: &'a Module,
    functions: BTreeMap<FuncId, Result<&'a Function, Refusal>>,
}

impl<'a> BoolBodyReader<'a> {
    pub fn new(module: &'a Module) -> Self {
        let mut functions = BTreeMap::new();
        for function in &module.functions {
            functions
                .entry(function.id)
                .and_modify(|entry| *entry = Err(Refusal::DuplicateFunction))
                .or_insert(Ok(function));
        }
        Self { module, functions }
    }

    pub fn derive(&self, function: FuncId) -> Result<PendingBoolBody<'a>, Refusal> {
        let f = self
            .functions
            .get(&function)
            .ok_or(Refusal::MissingFunction)?
            .as_ref()
            .map_err(|refusal| *refusal)?;
        derive_function(self.module, function, f)
    }
}

/// Read one leaf. A whole-module consumer should create one [`BoolBodyReader`]
/// instead of reconstructing its index for each body.
pub fn derive(module: &Module, function: FuncId) -> Result<PendingBoolBody<'_>, Refusal> {
    BoolBodyReader::new(module).derive(function)
}

/// Read the conjunction leaf used by the canonical SemR `evalBinop` semantics.
/// Other shapes remain explicit missing capabilities; they are not excluded
/// from the full model's population. No source or machine-code grade follows.
fn derive_function<'a>(
    module: &'a Module,
    function: FuncId,
    f: &'a Function,
) -> Result<PendingBoolBody<'a>, Refusal> {
    let signature = module
        .func_types
        .get(f.ty.index() as usize)
        .ok_or(Refusal::MissingSignature)?;
    if signature.is_vararg
        || signature.params != [Ty::Bool, Ty::Bool]
        || signature.returns != [Ty::Bool]
    {
        return Err(Refusal::Signature);
    }
    let [block] = f.blocks.as_slice() else {
        return Err(Refusal::BodyShape);
    };
    if block.id != f.entry {
        return Err(Refusal::Entry);
    }
    let [(left, Ty::Bool), (right, Ty::Bool)] = block.params.as_slice() else {
        return Err(Refusal::Parameters);
    };
    if left == right {
        return Err(Refusal::Parameters);
    }
    let [operation, ret] = block.body.as_slice() else {
        return Err(Refusal::BodyShape);
    };
    let Inst::BinOp {
        op: op @ (BinOp::And | BinOp::BAnd),
        ty: Ty::Bool,
        lhs,
        rhs,
    } = operation.inst
    else {
        return Err(Refusal::Operation);
    };
    if lhs != *left || rhs != *right {
        return Err(Refusal::Operation);
    }
    let [result] = operation.results.as_slice() else {
        return Err(Refusal::Result);
    };
    if result == left || result == right {
        return Err(Refusal::Result);
    }
    if !ret.results.is_empty()
        || ret.inst
            != (Inst::Return {
                values: vec![*result],
            })
    {
        return Err(Refusal::Return);
    }
    Ok(PendingBoolBody {
        module,
        function,
        signature: f.ty,
        entry: block.id,
        parameters: [*left, *right],
        result: *result,
        operation: op,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Block, FuncTy, Function, InstrNode};

    fn original() -> Module {
        let mut module = Module::new("actual_bool_and");
        module.func_types.push(FuncTy::unrecorded(
            vec![Ty::Bool, Ty::Bool],
            vec![Ty::Bool],
            false,
        ));
        let mut function = Function::new(
            FuncId::new(0),
            "conjunction",
            FuncTyId::new(0),
            BlockId::new(3),
        );
        let mut block = Block::new(BlockId::new(3))
            .with_param(ValueId::new(7), Ty::Bool)
            .with_param(ValueId::new(11), Ty::Bool);
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::BAnd,
                ty: Ty::Bool,
                lhs: ValueId::new(7),
                rhs: ValueId::new(11),
            })
            .with_result(ValueId::new(19)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(19)],
        }));
        function.blocks.push(block);
        module.functions.push(function);
        module
    }

    #[test]
    fn actual_ids_and_canonical_decoder_input_are_preserved() {
        let module = original();
        let pending = derive(&module, FuncId::new(0)).unwrap();
        assert_eq!(pending.function(), FuncId::new(0));
        assert_eq!(pending.signature(), FuncTyId::new(0));
        assert_eq!(pending.entry(), BlockId::new(3));
        assert_eq!(pending.parameters(), [ValueId::new(7), ValueId::new(11)]);
        assert_eq!(pending.result(), ValueId::new(19));
        assert_eq!(pending.operation(), BinOp::BAnd);
        assert_eq!(
            pending.canonical_module_bytes().unwrap(),
            crate::binary::serialize_module(&module).unwrap()
        );
        assert_eq!(
            crate::binary::deserialize_module(&pending.canonical_module_bytes().unwrap()).unwrap(),
            module
        );
    }

    #[test]
    fn implementation_only_mutants_are_not_the_original_derivation() {
        type Mutation = Box<dyn Fn(&mut Module)>;
        let changes: Vec<(Refusal, Mutation)> = vec![
            (
                Refusal::Operation,
                Box::new(|m| {
                    if let Inst::BinOp { op, .. } = &mut m.functions[0].blocks[0].body[0].inst {
                        *op = BinOp::BOr;
                    }
                }),
            ),
            (
                Refusal::Operation,
                Box::new(|m| {
                    if let Inst::BinOp { lhs, rhs, .. } = &mut m.functions[0].blocks[0].body[0].inst
                    {
                        std::mem::swap(lhs, rhs);
                    }
                }),
            ),
            (
                Refusal::Return,
                Box::new(|m| {
                    m.functions[0].blocks[0].body[1].inst = Inst::Return {
                        values: vec![ValueId::new(7)],
                    }
                }),
            ),
            (
                Refusal::Result,
                Box::new(|m| m.functions[0].blocks[0].body[0].results = vec![ValueId::new(7)]),
            ),
            (
                Refusal::Parameters,
                Box::new(|m| m.functions[0].blocks[0].params[1].0 = ValueId::new(7)),
            ),
            (
                Refusal::Signature,
                Box::new(|m| m.func_types[0].returns = vec![Ty::I8]),
            ),
            (
                Refusal::Signature,
                Box::new(|m| m.func_types[0].is_vararg = true),
            ),
            (
                Refusal::Entry,
                Box::new(|m| m.functions[0].entry = BlockId::new(4)),
            ),
            (
                Refusal::BodyShape,
                Box::new(|m| m.functions[0].blocks[0].body.pop().map(drop).unwrap()),
            ),
            (
                Refusal::DuplicateFunction,
                Box::new(|m| m.functions.push(m.functions[0].clone())),
            ),
        ];
        for (expected, change) in changes {
            let mut module = original();
            change(&mut module);
            assert_eq!(derive(&module, FuncId::new(0)).unwrap_err(), expected);
        }
    }

    #[test]
    fn indexed_inventory_preserves_duplicate_and_missing_refusals() {
        let mut module = original();
        let mut other = module.functions[0].clone();
        other.id = FuncId::new(9);
        module.functions.push(other);
        let reader = BoolBodyReader::new(&module);
        assert_eq!(
            reader.derive(FuncId::new(9)).unwrap().function(),
            FuncId::new(9)
        );
        assert_eq!(
            reader.derive(FuncId::new(5)).unwrap_err(),
            Refusal::MissingFunction
        );
        module.functions.push(module.functions[0].clone());
        let reader = BoolBodyReader::new(&module);
        assert_eq!(
            reader.derive(FuncId::new(0)).unwrap_err(),
            Refusal::DuplicateFunction
        );
        assert!(reader.derive(FuncId::new(9)).is_ok());
    }

    #[test]
    fn actual_and_opcode_is_preserved_without_normalization() {
        let mut module = original();
        if let Inst::BinOp { op, .. } = &mut module.functions[0].blocks[0].body[0].inst {
            *op = BinOp::And;
        }
        let reader = BoolBodyReader::new(&module);
        assert_eq!(
            reader.derive(FuncId::new(0)).unwrap().operation(),
            BinOp::And
        );
        let bytes = crate::binary::serialize_module(&module).unwrap();
        let decoded = crate::binary::deserialize_module(&bytes).unwrap();
        assert_eq!(decoded, module);
        assert_eq!(
            reader.candidate_source(&bytes, &[]).unwrap_err(),
            Refusal::EmptyRequest
        );
        assert_eq!(
            reader
                .candidate_source(&bytes, &[FuncId::new(0), FuncId::new(0)])
                .unwrap_err(),
            Refusal::DuplicateRequest
        );
    }
}

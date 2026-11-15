// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn function<'m, O: ExecutionObserver>(
    module: &'m Module,
    id: FuncId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<&'m Function>> {
    // Preserve the indexed-slot preference even on duplicate sparse IDs.
    admit(session, site, 2, 0)?;
    if let Some(function) = module.functions.get(id.as_usize())
        && function.id == id
    {
        return Ok(Some(function));
    }
    let mut index = 0;
    while index < module.functions.len() {
        admit(session, site, 1, 0)?;
        if module.functions[index].id == id {
            return Ok(Some(&module.functions[index]));
        }
        index += 1;
    }
    Ok(None)
}

fn contains<O: ExecutionObserver>(
    values: &[ValueId],
    value: ValueId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    let mut index = 0;
    while index < values.len() {
        admit(session, site, 1, 0)?;
        if values[index] == value {
            return Ok(true);
        }
        index += 1;
    }
    Ok(false)
}

pub(super) fn result_node<'a, O: ExecutionObserver>(
    function: &'a Function,
    result: ValueId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<&'a InstrNode>> {
    let mut first = None;
    let mut block = 0;
    while block < function.blocks.len() {
        admit(session, site, 1, 0)?;
        let mut index = 0;
        while index < function.blocks[block].body.len() {
            admit(session, site, 1, 0)?;
            let node = &function.blocks[block].body[index];
            if contains(&node.results, result, session, site)? {
                if first.is_some() {
                    return Ok(None);
                }
                first = Some(node);
            }
            index += 1;
        }
        block += 1;
    }
    admit(session, site, 1, 0)?;
    Ok(first.filter(|node| node.results.len() == 1))
}

pub(super) fn value_type<O: ExecutionObserver>(
    function: &Function,
    value: ValueId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<Ty>> {
    let mut block = 0;
    while block < function.blocks.len() {
        admit(session, site, 1, 0)?;
        let current = &function.blocks[block];
        let mut parameter = 0;
        while parameter < current.params.len() {
            admit(session, site, 1, 0)?;
            let (id, ty) = &current.params[parameter];
            if *id == value {
                return ty.clone_observed(session, site).map(Some);
            }
            parameter += 1;
        }
        let mut index = 0;
        while index < current.body.len() {
            admit(session, site, 1, 0)?;
            let node = &current.body[index];
            if contains(&node.results, value, session, site)?
                && let Some(ty) = inst_type(&node.inst, session, site)?
            {
                return Ok(Some(ty));
            }
            index += 1;
        }
        block += 1;
    }
    Ok(None)
}

pub(super) fn inst_type<O: ExecutionObserver>(
    inst: &Inst,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Option<Ty>> {
    admit(session, site, 1, 0)?;
    let borrowed = match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorMap { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => Some(ty),
        Inst::Cast { dst_ty, .. } => Some(dst_ty),
        Inst::PtrMetadata { metadata_ty, .. } => Some(metadata_ty),
        Inst::PtrFromParts { ptr_ty, .. } => Some(ptr_ty),
        Inst::DialectOp(op) if op.result_tys.len() == 1 => Some(&op.result_tys[0]),
        _ => None,
    };
    if let Some(ty) = borrowed {
        return ty.clone_observed(session, site).map(Some);
    }
    match inst {
        Inst::MakeClosure { ty, .. } => Ok(Some(Ty::Closure(*ty))),
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => {
            let bytes = size_of::<Ty>()
                .checked_mul(2)
                .and_then(|n| n.checked_add(2 * core::mem::align_of::<Ty>()))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            admit(session, site, 2, bytes)?;
            Ok(Some(match ty {
                Ty::Vector(_, lanes) => Ty::Vector(Box::new(Ty::Bool), *lanes),
                _ => Ty::Bool,
            }))
        }
        Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => {
            admit(session, site, 1, size_of::<Ty>())?;
            Ok(Some(Ty::Ptr))
        }
        Inst::IsUnique { .. } => {
            admit(session, site, 1, size_of::<Ty>())?;
            Ok(Some(Ty::Bool))
        }
        _ => Ok(None),
    }
}

impl Work {
    pub(super) fn value_matches<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        value: ValueId,
        expected: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        self.owned_ty = value_type(function, value, session, site)?;
        let equal = match &self.owned_ty {
            Some(actual) => actual.structural_eq_observed(expected, session, site)?,
            None => false,
        };
        self.retire_owned_ty(session, site);
        admit(session, site, 1, 0)?;
        Ok(equal)
    }
}

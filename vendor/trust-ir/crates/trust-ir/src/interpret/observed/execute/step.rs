// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn execute<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    node: &InstrNode,
    state: &mut ExecState,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<Option<Vec<InterpretValue>>> {
    let at = ExecutionSite::Instruction(site);
    let block = site.block;
    let mut outputs = Vec::new();
    // Numeric/validation helpers can emit only fixed-width scalar diagnostics
    // here. Prepay their bounded String/boxed panic storage before dispatch.
    event(session, at, ExecutionPhase::HostAllocation, 1, 512)?;
    reserve(&mut outputs, 2, session, at)?;
    match &node.inst {
        Inst::Const { ty, value } => outputs.push(constant(interpreter, ty, value, session, site)?),
        Inst::NullPtr => outputs.push(InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::NullPtr,
        }),
        Inst::Undef { ty } => {
            scalar(ty)?;
            if !partial_load_ty(ty) {
                return Err(Fault::Semantic(ub(
                    block,
                    "undef of non-scalar type is not executable (aggregate poison unmodelled)",
                )));
            }
            let (size, _) = memory::shape(interpreter, ty, session, at)?;
            let mut bytes = Vec::new();
            reserve(&mut bytes, size as usize, session, at)?;
            for _ in 0..size {
                event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
                bytes.push(None);
            }
            outputs.push(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::PartialBytes(bytes),
            });
        }
        Inst::Copy { ty, operand } => {
            flat(interpreter, ty, session, at)?;
            let operand = lookup(state, *operand, block, session, at)?;
            expect_ty(operand, ty, block)?;
            outputs.push(cloned(operand, session, at)?);
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            scalar(ty)?;
            let lhs = lookup(state, *lhs, block, session, at)?;
            let rhs = lookup(state, *rhs, block, session, at)?;
            outputs.push(interpreter.eval_binop(*op, ty, lhs, rhs, block)?);
        }
        Inst::UnOp { op, ty, operand } => {
            scalar(ty)?;
            outputs.push(interpreter.eval_unop(
                *op,
                ty,
                lookup(state, *operand, block, session, at)?,
                block,
            )?);
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            scalar(ty)?;
            let lhs = lookup(state, *lhs, block, session, at)?;
            let rhs = lookup(state, *rhs, block, session, at)?;
            let (value, overflow) = interpreter.eval_overflow(*op, ty, lhs, rhs, block)?;
            outputs.push(value);
            outputs.push(InterpretValue::bool(overflow));
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            scalar(ty)?;
            let lhs = lookup(state, *lhs, block, session, at)?;
            let rhs = lookup(state, *rhs, block, session, at)?;
            if matches!(ty, Ty::Ptr) {
                for operand in [lhs, rhs] {
                    if matches!(operand.kind, InterpretValueKind::Ptr(_)) {
                        event(
                            session,
                            at,
                            ExecutionPhase::SparseRun,
                            map_work(state.memory.allocations.len())?,
                            0,
                        )?;
                    }
                }
            }
            outputs.push(interpreter.eval_icmp(*op, ty, lhs, rhs, state, block)?);
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            scalar(ty)?;
            let lhs = lookup(state, *lhs, block, session, at)?;
            let rhs = lookup(state, *rhs, block, session, at)?;
            outputs.push(interpreter.eval_fcmp(*op, ty, lhs, rhs, block)?);
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            scalar(src_ty)?;
            scalar(dst_ty)?;
            if matches!(op, CastOp::IntToPtr | CastOp::PtrToInt | CastOp::Bitcast) {
                return Err(Fault::Unsupported("observed pointer or image cast"));
            }
            outputs.push(interpreter.eval_cast(
                *op,
                src_ty,
                dst_ty,
                lookup(state, *operand, block, session, at)?,
                state,
                block,
            )?);
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            flat(interpreter, ty, session, at)?;
            let cond = expect_bool_value(lookup(state, *cond, block, session, at)?, block)?;
            let then_value = lookup(state, *then_val, block, session, at)?;
            let else_value = lookup(state, *else_val, block, session, at)?;
            expect_ty(then_value, ty, block)?;
            expect_ty(else_value, ty, block)?;
            outputs.push(cloned(
                if cond { then_value } else { else_value },
                session,
                at,
            )?);
        }
        Inst::MakeClosure { .. } => {
            return Err(Fault::Unsupported("observed runtime closure construction"));
        }
        // A tensor never enters this path (`startup::check_type` refuses every
        // non-scalar, non-`[u8]` type); the contraction is refused by name.
        Inst::TensorContract { .. } => {
            return Err(Fault::Unsupported("observed tensor contraction"));
        }
        Inst::TensorMap { .. } => return Err(Fault::Unsupported("observed tensor map")),
        Inst::TensorReduce { .. } => return Err(Fault::Unsupported("observed tensor reduction")),
        Inst::TensorView { .. } => return Err(Fault::Unsupported("observed tensor view")),
        Inst::TensorGather { .. } => return Err(Fault::Unsupported("observed tensor gather")),
        Inst::TensorScatter { .. } => return Err(Fault::Unsupported("observed tensor scatter")),
        Inst::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            let len = array_length(interpreter, ty, session, at)?;
            if variant.is_some() || len != fields.len() as u64 {
                return Err(Fault::Unsupported(
                    "observed aggregate is not a flat U8 array",
                ));
            }
            let values = owned_values(fields.len(), session, at, |values, session| {
                for id in fields {
                    let value = lookup(state, *id, block, session, at)?;
                    byte_value(value, block)?;
                    values.push(cloned(value, session, at)?);
                }
                Ok(())
            })?;
            let rope = rope::Rope::dense_observed(values, &mut session.structural(at))?;
            outputs.push(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(ArrayValue::from_rope(rope)),
            });
        }
        Inst::ArraySplat { ty, value } => {
            let len = array_length(interpreter, ty, session, at)?;
            let value = lookup(state, *value, block, session, at)?;
            byte_value(value, block)?;
            let value = cloned(value, session, at)?;
            outputs.push(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(ArrayValue::splat_observed(
                    value, len, session, at,
                )?),
            });
        }
        Inst::ExtractElement { ty, array, index } => {
            if *ty != Ty::U8 {
                return Err(Fault::Unsupported("observed extracted element is not U8"));
            }
            let index = index_value(lookup(state, *index, block, session, at)?, block)?;
            let array = lookup(state, *array, block, session, at)?;
            array_length(interpreter, &array.ty, session, at)?;
            let InterpretValueKind::Array(array) = &array.kind else {
                return Err(Fault::Unsupported("array payload"));
            };
            let value = array
                .get_observed(index, session, at)?
                .ok_or_else(|| Fault::Semantic(ub(block, "ExtractElement: index out of bounds")))?;
            byte_value(value, block)?;
            outputs.push(cloned(value, session, at)?);
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            array_length(interpreter, ty, session, at)?;
            let array = lookup(state, *array, block, session, at)?;
            expect_ty(array, ty, block)?;
            let index = index_value(lookup(state, *index, block, session, at)?, block)?;
            let value = lookup(state, *value, block, session, at)?;
            byte_value(value, block)?;
            let value = cloned(value, session, at)?;
            let InterpretValueKind::Array(array) = &array.kind else {
                return Err(Fault::Unsupported("array payload"));
            };
            if index >= array.len() {
                value.retire_observed(session, at).ok();
                return Err(Fault::Semantic(ub(
                    block,
                    "InsertElement: index out of bounds",
                )));
            }
            outputs.push(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(array.set_observed(index, value, session, at)?),
            });
        }
        Inst::Alloca { ty, count, align } => {
            let (size, natural) = memory::shape(interpreter, ty, session, at)?;
            let count = match count {
                Some(id) => index_value(lookup(state, *id, block, session, at)?, block)?,
                None => 1,
            };
            if count == 0 {
                return Err(Fault::Semantic(ub(block, "Alloca: count must be positive")));
            }
            let size = size
                .checked_mul(count)
                .ok_or_else(|| Fault::Semantic(ub(block, "Alloca: allocation size overflow")))?;
            let align = checked_align(align.unwrap_or(natural), block)?;
            outputs.push(memory::allocate(
                &mut state.memory,
                size,
                align,
                session,
                site,
            )?);
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } => {
            outputs.push(gep(
                interpreter,
                state,
                pointee_ty,
                *base,
                indices,
                session,
                site,
            )?);
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            flat(interpreter, ty, session, at)?;
            let pointer = cloned(lookup(state, *ptr, block, session, at)?, session, at)?;
            let value = cloned(lookup(state, *value, block, session, at)?, session, at)?;
            let result = memory::store(
                interpreter,
                state,
                ty,
                &pointer,
                &value,
                *align,
                *volatile,
                session,
                site,
            );
            pointer.retire_observed(session, at).ok();
            value.retire_observed(session, at).ok();
            result?;
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            let pointer = lookup(state, *ptr, block, session, at)?;
            outputs.push(memory::load(
                interpreter,
                state,
                ty,
                pointer,
                *align,
                *volatile,
                session,
                site,
            )?);
        }
        Inst::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            let count = bulk_count(lookup(state, *bytes, block, session, at)?, block)?;
            let dst = cloned(lookup(state, *dst, block, session, at)?, session, at)?;
            let src = cloned(lookup(state, *src, block, session, at)?, session, at)?;
            let result = memory::copy(
                &mut state.memory,
                &dst,
                &src,
                count,
                *overlap,
                session,
                site,
            );
            dst.retire_observed(session, at).ok();
            src.retire_observed(session, at).ok();
            result?;
        }
        Inst::MemSet { dst, byte, bytes } => {
            let count = bulk_count(lookup(state, *bytes, block, session, at)?, block)?;
            let byte = byte_value(lookup(state, *byte, block, session, at)?, block)?;
            let dst = cloned(lookup(state, *dst, block, session, at)?, session, at)?;
            let result = memory::fill(&mut state.memory, &dst, byte, count, session, site);
            dst.retire_observed(session, at).ok();
            result?;
        }
        Inst::Dealloc { ptr } => {
            let ptr = expect_pointer(lookup(state, *ptr, block, session, at)?, block, "Dealloc")?;
            event(
                session,
                at,
                ExecutionPhase::SparseRun,
                map_work(state.memory.allocations.len())?,
                0,
            )?;
            state.memory.dealloc(ptr, block)?;
        }
        Inst::Assume { cond } => {
            if !expect_bool_value(lookup(state, *cond, block, session, at)?, block)? {
                return Err(Fault::Semantic(err(
                    InterpretErrorCode::AssumeViolated,
                    block,
                    "assume condition is false",
                )));
            }
        }
        Inst::Assert {
            cond,
            kind,
            site: panic_site,
        } => {
            if !expect_bool_value(lookup(state, *cond, block, session, at)?, block)? {
                // AssertKind is Copy and carries at most two integer IDs;
                // a Value panic location can add a third SSA lookup and one
                // allocation lookup. Decimal/hex rendering is u128-bounded.
                let operands = map_work(state.values.len())?
                    .checked_mul(3)
                    .ok_or(Fault::Representation)?;
                let work = operands
                    .checked_add(map_work(state.memory.allocations.len())?)
                    .and_then(|work| work.checked_add(1))
                    .ok_or(Fault::Representation)?;
                event(
                    session,
                    at,
                    ExecutionPhase::HostAllocation,
                    work,
                    256 + size_of::<InterpretPanic>(),
                )?;
                return Err(Fault::Semantic(assert_panic(
                    state,
                    block,
                    kind,
                    panic_site.as_ref(),
                )?));
            }
        }
        Inst::Return { values } => {
            let returns = owned_values(values.len(), session, at, |returns, session| {
                for id in values {
                    let value = lookup(state, *id, block, session, at)?;
                    reject_partial(value, block, "return")?;
                    returns.push(cloned(value, session, at)?);
                }
                Ok(())
            })?;
            if !node.results.is_empty() {
                retire_values(returns, &mut session.structural(at));
                return Err(Fault::Semantic(err(
                    InterpretErrorCode::MalformedInstruction,
                    block,
                    "Return cannot bind results",
                )));
            }
            return Ok(Some(returns));
        }
        Inst::Unreachable => return Err(Fault::Semantic(ub(block, "reached Unreachable"))),
        _ => {
            return Err(Fault::Unsupported(
                "instruction outside observed byte/scalar execution",
            ));
        }
    }
    bind(state, node, outputs, session, site)?;
    Ok(None)
}

fn scalar(ty: &Ty) -> RunResult<()> {
    if scalar_type(ty) {
        Ok(())
    } else {
        Err(Fault::Unsupported("non-scalar operation"))
    }
}

fn flat<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    startup::check_type(
        interpreter.module.ok_or(Fault::Unsupported("module"))?,
        ty,
        session,
        site,
    )
}

fn array_length<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<u64> {
    flat(interpreter, ty, session, site)?;
    match ty {
        Ty::Array(_, len) => Ok(*len),
        _ => Err(Fault::Unsupported("non-array byte operation")),
    }
}

fn byte_value(value: &InterpretValue, block: BlockId) -> RunResult<u8> {
    expect_ty(value, &Ty::U8, block)?;
    let int = expect_int_value(value, block)?;
    if int.bits != 8 || int.signed || int.raw > 255 {
        return Err(Fault::Unsupported("malformed U8 value"));
    }
    Ok(int.raw as u8)
}

fn index_value(value: &InterpretValue, block: BlockId) -> RunResult<u64> {
    let value = expect_int_value(value, block)?;
    if value.signed && value.as_signed() < 0 {
        return Err(Fault::Semantic(ub(block, "negative byte count or index")));
    }
    u64::try_from(value.as_unsigned())
        .map_err(|_| Fault::Semantic(ub(block, "byte count or index does not fit u64")))
}

fn bulk_count(value: &InterpretValue, block: BlockId) -> RunResult<u64> {
    let count = expect_int_value(value, block)?;
    if count.signed {
        return Err(Fault::Semantic(type_error(
            block,
            "bulk byte count must be unsigned",
        )));
    }
    index_value(value, block)
}

fn gep<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    base: ValueId,
    indices: &[ValueId],
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let at = ExecutionSite::Instruction(site);
    let (stride, _) = memory::shape(interpreter, ty, session, at)?;
    let mut delta = 0u64;
    for id in indices {
        event(session, at, ExecutionPhase::Instruction, 1, 0)?;
        let index = index_value(lookup(state, *id, site.block, session, at)?, site.block)?;
        delta = delta
            .checked_add(
                stride
                    .checked_mul(index)
                    .ok_or_else(|| Fault::Semantic(ub(site.block, "GEP: byte offset overflow")))?,
            )
            .ok_or_else(|| Fault::Semantic(ub(site.block, "GEP: pointer offset overflow")))?;
    }
    let base = lookup(state, base, site.block, session, at)?;
    let kind = match base.kind {
        InterpretValueKind::DanglingPtr(address) => InterpretValueKind::DanglingPtr(
            address
                .checked_add(delta)
                .ok_or_else(|| Fault::Semantic(ub(site.block, "GEP: address overflow")))?,
        ),
        _ => {
            let base = expect_pointer(base, site.block, "GEP")?;
            InterpretValueKind::Ptr(InterpretPointer {
                allocation: base.allocation,
                offset: base
                    .offset
                    .checked_add(delta)
                    .ok_or_else(|| Fault::Semantic(ub(site.block, "GEP: offset overflow")))?,
            })
        }
    };
    Ok(InterpretValue { ty: Ty::Ptr, kind })
}

fn constant<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    ty: &Ty,
    constant: &Constant,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let at = ExecutionSite::Instruction(site);
    flat(interpreter, ty, session, at)?;
    if scalar_type(ty) {
        if !matches!(
            constant,
            Constant::Int(_)
                | Constant::U128(_)
                | Constant::Bool(_)
                | Constant::Float(_)
                | Constant::PhantomData
        ) {
            return Err(Fault::Unsupported("non-scalar constant form"));
        }
        event(
            session,
            at,
            ExecutionPhase::LiteralElement,
            1,
            size_of::<InterpretValue>(),
        )?;
        return Ok(interpreter.constant_to_value_in(ty, constant, None, site.block)?);
    }
    let len = array_length(interpreter, ty, session, at)?;
    let values = match constant {
        Constant::Splat { elem, len: count } if *count == len => {
            let element = self_byte_constant(interpreter, elem, session, site)?;
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(ArrayValue::splat_observed(
                    element, len, session, at,
                )?),
            });
        }
        Constant::Array(elements) if elements.len() as u64 == len => {
            owned_values(elements.len(), session, at, |values, session| {
                for element in elements {
                    values.push(self_byte_constant(interpreter, element, session, site)?);
                }
                Ok(())
            })?
        }
        Constant::Bytes { data, .. } if data.len() as u64 == len => {
            owned_values(data.len(), session, at, |values, session| {
                for byte in data {
                    event(
                        session,
                        at,
                        ExecutionPhase::LiteralElement,
                        1,
                        size_of::<InterpretValue>(),
                    )?;
                    values.push(InterpretValue {
                        ty: Ty::U8,
                        kind: InterpretValueKind::Int(InterpretInt {
                            bits: 8,
                            signed: false,
                            raw: u128::from(*byte),
                        }),
                    });
                }
                Ok(())
            })?
        }
        _ => return Err(Fault::Unsupported("flat U8 constant shape")),
    };
    Ok(InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Array(ArrayValue::from_rope(rope::Rope::dense_observed(
            values,
            &mut session.structural(at),
        )?)),
    })
}

fn self_byte_constant<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    value: &Constant,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    if !matches!(value, Constant::Int(_) | Constant::U128(_)) {
        return Err(Fault::Unsupported("U8 literal form"));
    }
    event(
        session,
        ExecutionSite::Instruction(site),
        ExecutionPhase::LiteralElement,
        1,
        size_of::<InterpretValue>(),
    )?;
    Ok(interpreter.constant_to_value_in(&Ty::U8, value, None, site.block)?)
}

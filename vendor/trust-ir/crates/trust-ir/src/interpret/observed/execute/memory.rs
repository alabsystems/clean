// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The observed scalar / flat-U8 memory closure. All byte-store and rope
//! operations use the original session, including copies of initializedness.

use super::*;

pub(super) fn shape<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    ty: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<(u64, u64)> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("memory module"))?;
    startup::check_type(module, ty, session, site)?;
    Ok(match ty {
        Ty::Bool | Ty::I8 | Ty::U8 => (1, 1),
        Ty::I16 | Ty::U16 | Ty::F16 => (2, 2),
        Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => (4, 4),
        Ty::I64 | Ty::U64 | Ty::F64 | Ty::Ptr | Ty::Isize | Ty::Usize => (8, 8),
        Ty::I128 | Ty::U128 => (16, 16),
        Ty::Unit => (0, 1),
        Ty::Array(_, len) => (*len, 1),
        _ => return Err(Fault::Unsupported("observed memory shape")),
    })
}

pub(super) fn allocate<O: ExecutionObserver>(
    memory: &mut MemoryState,
    size: u64,
    align: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let at = ExecutionSite::Instruction(site);
    let exhausted = || {
        Fault::Semantic(err(
            InterpretErrorCode::OutOfMemory,
            site.block,
            "observed allocation exhausts target address space",
        ))
    };
    let base = align_addr(memory.next_addr, align).ok_or_else(exhausted)?;
    let next = base.checked_add(size.max(1)).ok_or_else(exhausted)?;
    let id = memory.next_alloc_id;
    let next_id = id.checked_add(1).ok_or_else(exhausted)?;
    map_insert::<u64, Allocation, O>(
        memory.allocations.len(),
        session,
        at,
        ExecutionPhase::HostAllocation,
    )?;
    let bytes = ByteStore::new_observed(size, None, &mut session.structural(at))?;
    memory.allocations.insert(
        id,
        Allocation {
            base,
            size,
            alive: true,
            bytes,
            ref_count: 1,
            origin: None,
            requested: size,
            live_borrows: 0,
        },
    );
    memory.next_alloc_id = next_id;
    memory.next_addr = next;
    Ok(InterpretValue {
        ty: Ty::Ptr,
        kind: InterpretValueKind::Ptr(InterpretPointer {
            allocation: id,
            offset: 0,
        }),
    })
}

fn access<'a, O: ExecutionObserver>(
    memory: &'a MemoryState,
    ptr: InterpretPointer,
    size: u64,
    align: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
    op: &'static str,
) -> RunResult<&'a Allocation> {
    event(
        session,
        ExecutionSite::Instruction(site),
        ExecutionPhase::SparseRun,
        map_work(memory.allocations.len())?,
        0,
    )?;
    Ok(memory.checked_access(ptr, size, align, site.block, op)?)
}

fn read<O: ExecutionObserver>(
    memory: &MemoryState,
    ptr: InterpretPointer,
    size: u64,
    align: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
    op: &'static str,
) -> RunResult<Image> {
    let allocation = access(memory, ptr, size, align, session, site, op)?;
    Ok(allocation.bytes.read_observed(
        ptr.offset,
        size,
        &mut session.structural(ExecutionSite::Instruction(site)),
    )?)
}

fn write<O: ExecutionObserver>(
    memory: &mut MemoryState,
    ptr: InterpretPointer,
    image: &Image,
    align: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
    op: &'static str,
) -> RunResult<()> {
    access(memory, ptr, image.len(), align, session, site, op)?;
    // No accepted observed instruction can create aggregate unwritten-lane
    // metadata. Never silently invoke the ordinary unobserved range walk.
    if !memory.unwritten_lane_bytes.is_empty() {
        return Err(Fault::Unsupported("aggregate unwritten-lane metadata"));
    }
    event(
        session,
        ExecutionSite::Instruction(site),
        ExecutionPhase::SparseRun,
        map_work(memory.allocations.len())?,
        0,
    )?;
    let allocation = memory
        .allocations
        .get_mut(&ptr.allocation)
        .ok_or_else(|| Fault::Semantic(ub(site.block, "observed write lost allocation")))?;
    allocation.bytes.write_observed(
        ptr.offset,
        image,
        &mut session.structural(ExecutionSite::Instruction(site)),
    )?;
    Ok(())
}

pub(super) fn copy<O: ExecutionObserver>(
    memory: &mut MemoryState,
    dst: &InterpretValue,
    src: &InterpretValue,
    count: u64,
    overlap: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    // Exact zero-byte semantics: no pointer dereference or range validation.
    if count == 0 {
        return Ok(());
    }
    let dst = expect_pointer(dst, site.block, "MemCopy destination")?;
    let src = expect_pointer(src, site.block, "MemCopy source")?;
    access(memory, src, count, 1, session, site, "MemCopy source")?;
    access(memory, dst, count, 1, session, site, "MemCopy destination")?;
    if !overlap
        && src.allocation == dst.allocation
        && src.offset < dst.offset.saturating_add(count)
        && dst.offset < src.offset.saturating_add(count)
    {
        return Err(Fault::Semantic(ub(
            site.block,
            "MemCopy: overlapping ranges require memmove",
        )));
    }
    // Snapshot the ENTIRE source before any write. Compressed images retain
    // both byte values and initializedness; length is not a host loop bound.
    let image = read(memory, src, count, 1, session, site, "MemCopy source")?;
    let result = write(memory, dst, &image, 1, session, site, "MemCopy destination");
    image.retire_observed(&mut session.structural(ExecutionSite::Instruction(site)));
    result
}

pub(super) fn fill<O: ExecutionObserver>(
    memory: &mut MemoryState,
    dst: &InterpretValue,
    byte: u8,
    count: u64,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    if count == 0 {
        return Ok(());
    }
    let ptr = expect_pointer(dst, site.block, "MemSet")?;
    access(memory, ptr, count, 1, session, site, "MemSet")?;
    let at = ExecutionSite::Instruction(site);
    let image = Image::uniform_observed(Some(byte), count, &mut session.structural(at))?;
    let result = write(memory, ptr, &image, 1, session, site, "MemSet");
    image.retire_observed(&mut session.structural(at));
    result
}

#[allow(
    clippy::too_many_arguments,
    reason = "the observed twin keeps the unobserved signature and adds the session"
)]
pub(super) fn store<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &mut ExecState,
    ty: &Ty,
    ptr: &InterpretValue,
    value: &InterpretValue,
    align: Option<u64>,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    let (_, natural) = shape(interpreter, ty, session, ExecutionSite::Instruction(site))?;
    if strict {
        reject_partial(value, site.block, "Store (atomic/volatile)")?;
    }
    if value.ty != *ty {
        return Err(Fault::Semantic(type_error(
            site.block,
            "observed Store type mismatch",
        )));
    }
    let align = checked_align(align.unwrap_or(natural), site.block)?;
    let ptr = expect_pointer(ptr, site.block, "Store")?;
    let image = encode(interpreter, state, value, session, site)?;
    let result = write(
        &mut state.memory,
        ptr,
        &image,
        align,
        session,
        site,
        "Store",
    );
    image.retire_observed(&mut session.structural(ExecutionSite::Instruction(site)));
    result
}

#[allow(
    clippy::too_many_arguments,
    reason = "the observed twin keeps the unobserved signature and adds the session"
)]
pub(super) fn load<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    ptr: &InterpretValue,
    align: Option<u64>,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let at = ExecutionSite::Instruction(site);
    let (size, natural) = shape(interpreter, ty, session, at)?;
    let ptr = expect_pointer(ptr, site.block, "Load")?;
    let align = checked_align(align.unwrap_or(natural), site.block)?;
    let image = read(&state.memory, ptr, size, align, session, site, "Load")?;
    let result = decode(interpreter, state, ty, &image, strict, session, site);
    image.retire_observed(&mut session.structural(at));
    result
}

fn encode<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    state: &ExecState,
    value: &InterpretValue,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<Image> {
    let at = ExecutionSite::Instruction(site);
    let (size, _) = shape(interpreter, &value.ty, session, at)?;
    if let InterpretValueKind::Array(array) = &value.kind {
        if !matches!(value.ty, Ty::Array(_, len) if len == array.len()) {
            return Err(Fault::Unsupported("array Store shape"));
        }
        return Ok(array.rope().try_map_observed(
            &mut session.structural(at),
            |element, progress| {
                progress.admit(ExecutionPhase::LiteralElement, 1, 1)?;
                match (&element.ty, &element.kind) {
                    (Ty::U8, InterpretValueKind::Int(int))
                        if int.bits == 8 && !int.signed && int.raw <= 255 =>
                    {
                        Ok(Some(int.raw as u8))
                    }
                    _ => Err(ObservedValueError::UnsupportedValue),
                }
            },
        )?);
    }
    if size > 16 {
        return Err(Fault::Unsupported("scalar image width"));
    }
    let mut bytes = Vec::new();
    reserve(&mut bytes, size as usize, session, at)?;
    if let InterpretValueKind::PartialBytes(partial) = &value.kind {
        if partial.len() as u64 != size {
            return Err(Fault::Unsupported("partial scalar image shape"));
        }
        for byte in partial {
            event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
            bytes.push(*byte);
        }
    } else {
        let raw = match value.kind {
            InterpretValueKind::Int(int) => int.raw,
            InterpretValueKind::FloatBits(bits) => u128::from(bits),
            InterpretValueKind::Bool(bit) => u128::from(bit),
            InterpretValueKind::Ptr(ptr) => {
                event(
                    session,
                    at,
                    ExecutionPhase::SparseRun,
                    map_work(state.memory.allocations.len())?,
                    0,
                )?;
                u128::from(state.memory.address(ptr, site.block, "Store")?)
            }
            InterpretValueKind::NullPtr | InterpretValueKind::Unit => 0,
            InterpretValueKind::DanglingPtr(address) => u128::from(address),
            _ => return Err(Fault::Unsupported("scalar Store payload")),
        };
        for index in 0..size as usize {
            event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
            bytes.push(Some((raw >> (8 * index)) as u8));
        }
    }
    Ok(Image::dense_observed(bytes, &mut session.structural(at))?)
}

fn decode<O: ExecutionObserver>(
    _interpreter: &Interpreter<'_>,
    state: &ExecState,
    ty: &Ty,
    image: &Image,
    strict: bool,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<InterpretValue> {
    let at = ExecutionSite::Instruction(site);
    if matches!(ty, Ty::Array(_, _)) {
        let mut uninit = false;
        image.try_for_each_stored_observed(&mut session.structural(at), |byte, _| {
            uninit |= byte.is_none();
            Ok(())
        })?;
        if uninit {
            return Err(Fault::Semantic(ub(
                site.block,
                "Load: uninitialized array byte",
            )));
        }
        let values = image.try_map_observed(&mut session.structural(at), |byte, progress| {
            progress.admit(
                ExecutionPhase::LiteralElement,
                1,
                size_of::<InterpretValue>(),
            )?;
            let byte = byte.ok_or(ObservedValueError::UnsupportedValue)?;
            Ok(InterpretValue {
                ty: Ty::U8,
                kind: InterpretValueKind::Int(InterpretInt {
                    bits: 8,
                    signed: false,
                    raw: u128::from(byte),
                }),
            })
        })?;
        return Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Array(ArrayValue::from_rope(values)),
        });
    }
    let size = image.len();
    if size > 16 {
        return Err(Fault::Unsupported("scalar Load width"));
    }
    let mut bytes = Vec::new();
    reserve(&mut bytes, size as usize, session, at)?;
    let mut raw = 0u128;
    let mut uninit = false;
    for index in 0..size {
        let byte = image
            .get_observed(index, &mut session.structural(at))?
            .copied()
            .ok_or(Fault::Representation)?;
        event(session, at, ExecutionPhase::LiteralElement, 1, 1)?;
        bytes.push(byte);
        uninit |= byte.is_none();
        raw |= u128::from(byte.unwrap_or(0)) << (8 * index);
    }
    if uninit {
        if strict {
            return Err(Fault::Semantic(ub(
                site.block,
                "Load: uninitialized strict scalar byte",
            )));
        }
        return Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::PartialBytes(bytes),
        });
    }
    let kind = if let Some((bits, signed)) = int_shape(ty) {
        InterpretValueKind::Int(
            InterpretInt::from_raw(bits, signed, raw).ok_or(Fault::Representation)?,
        )
    } else {
        match ty {
            Ty::Bool => InterpretValueKind::Bool(raw != 0),
            Ty::Unit => InterpretValueKind::Unit,
            Ty::F16 | Ty::F32 | Ty::F64 => InterpretValueKind::FloatBits(raw as u64),
            Ty::Ptr => resolve_pointer(&state.memory, raw as u64, session, at)?,
            _ => return Err(Fault::Unsupported("scalar Load type")),
        }
    };
    Ok(InterpretValue {
        ty: ty.clone(),
        kind,
    })
}

fn resolve_pointer<O: ExecutionObserver>(
    memory: &MemoryState,
    address: u64,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<InterpretValueKind> {
    if address == 0 {
        return Ok(InterpretValueKind::NullPtr);
    }
    // Preserve ordinary provenance's in-bounds-before-one-past preference.
    for one_past in [false, true] {
        for (id, allocation) in &memory.allocations {
            event(session, site, ExecutionPhase::SparseRun, 1, 0)?;
            let Some(end) = allocation.base.checked_add(allocation.size) else {
                continue;
            };
            if (!one_past && address >= allocation.base && address < end)
                || (one_past && address == end)
            {
                return Ok(InterpretValueKind::Ptr(InterpretPointer {
                    allocation: *id,
                    offset: address - allocation.base,
                }));
            }
        }
    }
    Ok(InterpretValueKind::DanglingPtr(address))
}

pub(super) fn retire<O: ExecutionObserver>(
    memory: &mut MemoryState,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while let Some((_, allocation)) = memory.allocations.pop_first() {
        session.retirement_poll(site);
        allocation
            .bytes
            .retire_observed(&mut session.structural(site));
    }
    while let Some((_, mut holes)) = memory.unwritten_lane_bytes.pop_first() {
        while holes.pop_first().is_some() {
            session.retirement_poll(site);
        }
    }
}

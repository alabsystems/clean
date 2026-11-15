// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn pair<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a Constant,
    b: &'a Constant,
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1 + 2 * size_of::<Constant>(), 2 * size_of::<Constant>())?;
    if tag(a) != tag(b) {
        s.last = false;
        return Ok(());
    }
    use crate::constant::ConstantG::*;
    match (a, b) {
        (Int(a), Int(b)) => s.last = a == b,
        (U128(a), U128(b)) => s.last = a == b,
        (Float(a), Float(b)) => s.last = a.to_bits() == b.to_bits(),
        (Bool(a), Bool(b)) => s.last = a == b,
        (Bytes { data: a, utf8: ua }, Bytes { data: b, utf8: ub }) => {
            s.last = w.text(a, b)? && ua == ub
        }
        (Aggregate(a), Aggregate(b))
        | (Array(a), Array(b))
        | (Vector(a), Vector(b))
        | (Sequence(a), Sequence(b))
        | (Set(a), Set(b)) => s.push(Task::Constants(a, b), w)?,
        (Splat { elem: a, len: na }, Splat { elem: b, len: nb }) => {
            s.last = na == nb;
            if s.last {
                s.push(Task::Constant(a, b), w)?;
            }
        }
        (Record(a), Record(b)) => s.push(Task::ConstantFields(a, b), w)?,
        (
            Closure {
                func: a,
                captures: ca,
            },
            Closure {
                func: b,
                captures: cb,
            },
        ) => {
            s.last = a == b;
            if s.last {
                s.push(Task::Constants(ca, cb), w)?;
            }
        }
        (FnDef(a), FnDef(b)) => s.last = a == b,
        (
            SymbolAddr {
                symbol: a,
                addend: aa,
            },
            SymbolAddr {
                symbol: b,
                addend: ab,
            },
        ) => s.last = w.text(a.as_bytes(), b.as_bytes())? && aa == ab,
        (PhantomData, PhantomData) | (Uninit, Uninit) => (),
        (
            TensorBlob {
                digest: da,
                dims: ma,
            },
            TensorBlob {
                digest: db,
                dims: mb,
            },
        ) => {
            w.admit(1 + ma.len(), 0)?;
            s.last = da == db && ma == mb;
        }
        (Ext(extension), _) => extension.unreachable(),
        _ => s.last = false,
    }
    Ok(())
}
pub(super) fn tail<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [Constant],
    b: &'a [Constant],
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(1, 2 * size_of::<Option<(&Constant, &[Constant])>>())?;
    if a.len() != b.len() {
        s.last = false;
        return Ok(());
    }
    if let (Some((a, rest_a)), Some((b, rest_b))) = (a.split_first(), b.split_first()) {
        s.push(Task::Constants(rest_a, rest_b), w)?;
        s.push(Task::Constant(a, b), w)?;
    }
    Ok(())
}
pub(super) fn fields<'a, O: ExecutionObserver>(
    s: &mut State<'a>,
    a: &'a [(String, Constant)],
    b: &'a [(String, Constant)],
    w: &mut Work<'_, '_, O>,
) -> R {
    w.admit(
        1,
        2 * size_of::<Option<(&(String, Constant), &[(String, Constant)])>>(),
    )?;
    if a.len() != b.len() {
        s.last = false;
        return Ok(());
    }
    if let (Some(((name_a, a), rest_a)), Some(((name_b, b), rest_b))) =
        (a.split_first(), b.split_first())
    {
        s.last = w.text(name_a.as_bytes(), name_b.as_bytes())?;
        if s.last {
            s.push(Task::ConstantFields(rest_a, rest_b), w)?;
            s.push(Task::Constant(a, b), w)?;
        }
    }
    Ok(())
}

// Exhaustive: a future literal spelling needs an explicit identity decision.
fn tag(value: &Constant) -> u8 {
    match value {
        Constant::Int(_) => 0,
        Constant::U128(_) => 1,
        Constant::Bytes { .. } => 2,
        Constant::Float(_) => 3,
        Constant::Bool(_) => 4,
        Constant::Aggregate(_) => 5,
        Constant::Array(_) => 6,
        Constant::Splat { .. } => 7,
        Constant::Vector(_) => 8,
        Constant::Sequence(_) => 9,
        Constant::Set(_) => 10,
        Constant::Record(_) => 11,
        Constant::Closure { .. } => 12,
        Constant::FnDef(_) => 13,
        Constant::SymbolAddr { .. } => 14,
        Constant::PhantomData => 15,
        Constant::Uninit => 16,
        Constant::TensorBlob { .. } => 17,
        Constant::Ext(extension) => extension.unreachable(),
    }
}

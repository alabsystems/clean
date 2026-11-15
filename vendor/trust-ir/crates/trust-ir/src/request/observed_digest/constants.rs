// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

enum ConstantTask<'a> {
    Value(&'a Constant),
    List(&'a [Constant]),
    Fields(&'a [(String, Constant)]),
    U64(u64),
}

pub(super) fn write_constant<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: &Constant,
) -> Result {
    walk(out, ConstantTask::Value(value))
}

fn walk<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, root: ConstantTask<'_>) -> Result {
    let mut tasks = Vec::new();
    let result: Result = (|| {
        out.push_value(&mut tasks, root)?;
        while !tasks.is_empty() {
            out.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                ConstantTask::Value(value) => write_head(out, value, &mut tasks)?,
                ConstantTask::List(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, ConstantTask::List(rest))?;
                        }
                        out.push_value(&mut tasks, ConstantTask::Value(first))?;
                    }
                }
                ConstantTask::Fields(rows) => {
                    if let Some(((name, first), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, ConstantTask::Fields(rest))?;
                        }
                        write_str(out, name)?;
                        out.push_value(&mut tasks, ConstantTask::Value(first))?;
                    }
                }
                ConstantTask::U64(value) => write_u64(out, value)?,
            }
        }
        Ok(())
    })();
    out.retire_value(tasks);
    result?;
    out.poll()
}

fn write_head<'a, O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    constant: &'a Constant,
    tasks: &mut Vec<ConstantTask<'a>>,
) -> Result {
    out.poll()?;

    match constant {
        Constant::Int(value) => {
            write_u8(out, 0)?;
            write_i128(out, *value)?;
        }
        // v24 U128: stable tag 13 (next free; matches the binary codec's tag).
        Constant::U128(value) => {
            write_u8(out, 13)?;
            write_u128(out, *value)?;
        }
        // v25 Bytes: stable tag 14 (matches the binary codec's tag).
        Constant::Bytes { data, utf8 } => {
            write_u8(out, 14)?;
            write_bool(out, *utf8)?;
            write_len(out, data.len())?;
            out.append(data)?;
        }
        Constant::Float(value) => {
            write_u8(out, 1)?;
            write_u64(out, value.to_bits())?;
        }
        Constant::Bool(value) => {
            write_u8(out, 2)?;
            write_bool(out, *value)?;
        }
        Constant::Aggregate(values) => {
            write_u8(out, 3)?;
            write_len(out, values.len())?;
            out.push_value(tasks, ConstantTask::List(values))?;
        }
        Constant::Array(values) => {
            write_u8(out, 4)?;
            write_len(out, values.len())?;
            out.push_value(tasks, ConstantTask::List(values))?;
        }
        Constant::Vector(values) => {
            write_u8(out, 11)?;
            write_len(out, values.len())?;
            out.push_value(tasks, ConstantTask::List(values))?;
        }
        Constant::Sequence(values) => {
            write_u8(out, 5)?;
            write_len(out, values.len())?;
            out.push_value(tasks, ConstantTask::List(values))?;
        }
        Constant::Set(values) => {
            write_u8(out, 6)?;
            write_len(out, values.len())?;
            out.push_value(tasks, ConstantTask::List(values))?;
        }
        Constant::Record(fields) => {
            write_u8(out, 7)?;
            write_len(out, fields.len())?;
            out.push_value(tasks, ConstantTask::Fields(fields))?;
        }
        Constant::Closure { func, captures } => {
            write_u8(out, 8)?;
            write_u32(out, func.index())?;
            write_len(out, captures.len())?;
            out.push_value(tasks, ConstantTask::List(captures))?;
        }
        Constant::FnDef(func) => {
            write_u8(out, 9)?;
            write_u32(out, func.index())?;
        }
        Constant::SymbolAddr { symbol, addend } => {
            write_u8(out, 12)?;
            write_str(out, symbol)?;
            write_u64(out, *addend as u64)?;
        }
        Constant::PhantomData => write_u8(out, 10)?,
        // Crystal lane (E3b, v49): stable tag 15, the next free one, matching the binary codec's tag.
        Constant::Uninit => write_u8(out, 15)?,
        // v50 Splat: stable tag 16 (next free; matches the binary codec's
        // tag). One element and the length — the digest input does not grow
        // with the length, and an equal list spells a different digest (the
        // §3 rule keeps a valid module to one spelling).
        Constant::Splat { elem, len } => {
            write_u8(out, 16)?;
            out.push_value(tasks, ConstantTask::U64(*len))?;
            out.push_value(tasks, ConstantTask::Value(elem))?;
        }
        // v70 TensorBlob: stable tag 18, the digest and the extents.
        Constant::TensorBlob { digest, dims } => {
            write_u8(out, 18)?;
            out.append(&digest.0)?;
            write_len(out, dims.len())?;
            for dim in dims {
                write_u64(out, *dim)?;
            }
        }
        Constant::Ext(e) => e.unreachable(),
    }
    Ok(())
}

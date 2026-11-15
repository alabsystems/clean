// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::Constant;

enum ConstantTask<'a> {
    Value(&'a Constant),
    List(&'a [Constant]),
    Fields(&'a [(String, Constant)]),
    U64(u64),
}

pub(super) fn observed_write_constant<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    value: &Constant,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        buf.push_value(&mut tasks, ConstantTask::Value(value))?;
        while !tasks.is_empty() {
            buf.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                ConstantTask::Value(c) => constant_head(buf, pool, c, &mut tasks)?,
                ConstantTask::List(rows) => {
                    if let Some((first, rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            buf.push_value(&mut tasks, ConstantTask::List(rest))?;
                        }
                        buf.push_value(&mut tasks, ConstantTask::Value(first))?;
                    }
                }
                ConstantTask::Fields(rows) => {
                    if let Some(((name, first), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            buf.push_value(&mut tasks, ConstantTask::Fields(rest))?;
                        }
                        observed_write_str(buf, pool, name)?;
                        buf.push_value(&mut tasks, ConstantTask::Value(first))?;
                    }
                }
                ConstantTask::U64(value) => observed_write_u64(buf, value)?,
            }
        }
        Ok(())
    })();
    buf.finish_child(result, tasks)
}

fn constant_head<'a, O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    c: &'a Constant,
    tasks: &mut Vec<ConstantTask<'a>>,
) -> R {
    buf.poll()?;

    match c {
        ConstantG::Int(v) => {
            observed_write_u8(buf, 0)?;
            observed_write_i128(buf, *v)?;
        }
        // v24: the 128-bit-faithful unsigned carrier (canonical iff the value
        // exceeds i128::MAX - the decoder REJECTS a non-canonical payload).
        ConstantG::U128(v) => {
            observed_write_u8(buf, 13)?;
            observed_write_u128(buf, *v)?;
        }
        // v25: raw byte-array constant (utf8 flag + length-prefixed payload).
        ConstantG::Bytes { data, utf8 } => {
            observed_write_u8(buf, 14)?;
            observed_write_bool(buf, *utf8)?;
            observed_write_count(buf, "Constant::Bytes data", data.len())?;
            buf.extend_from_slice(data)?;
        }
        ConstantG::Float(v) => {
            observed_write_u8(buf, 1)?;
            observed_write_f64(buf, *v)?;
        }
        ConstantG::Bool(v) => {
            observed_write_u8(buf, 2)?;
            observed_write_bool(buf, *v)?;
        }
        ConstantG::Aggregate(elems) => {
            observed_write_u8(buf, 3)?;
            observed_write_count(buf, "Constant::Aggregate elements", elems.len())?;
            buf.push_value(tasks, ConstantTask::List(elems))?;
        }
        ConstantG::Array(elems) => {
            observed_write_u8(buf, 8)?;
            observed_write_count(buf, "Constant::Array elements", elems.len())?;
            buf.push_value(tasks, ConstantTask::List(elems))?;
        }
        ConstantG::Vector(elems) => {
            observed_write_u8(buf, 11)?;
            observed_write_count(buf, "Constant::Vector elements", elems.len())?;
            buf.push_value(tasks, ConstantTask::List(elems))?;
        }
        ConstantG::Sequence(elems) => {
            observed_write_u8(buf, 4)?;
            observed_write_count(buf, "Constant::Sequence elements", elems.len())?;
            buf.push_value(tasks, ConstantTask::List(elems))?;
        }
        ConstantG::Set(elems) => {
            observed_write_u8(buf, 5)?;
            observed_write_count(buf, "Constant::Set elements", elems.len())?;
            buf.push_value(tasks, ConstantTask::List(elems))?;
        }
        ConstantG::Record(fields) => {
            observed_write_u8(buf, 6)?;
            observed_write_count(buf, "Constant::Record fields", fields.len())?;
            buf.push_value(tasks, ConstantTask::Fields(fields))?;
        }
        ConstantG::Closure { func, captures } => {
            observed_write_u8(buf, 7)?;
            observed_write_func_id(buf, *func)?;
            observed_write_count(buf, "Constant::Closure captures", captures.len())?;
            buf.push_value(tasks, ConstantTask::List(captures))?;
        }
        ConstantG::FnDef(func) => {
            observed_write_u8(buf, 9)?;
            observed_write_func_id(buf, *func)?;
        }
        ConstantG::SymbolAddr { symbol, addend } => {
            observed_write_u8(buf, 12)?;
            observed_write_str(buf, pool, symbol)?;
            observed_write_u64(buf, *addend as u64)?;
        }
        ConstantG::PhantomData => observed_write_u8(buf, 10)?,
        // Crystal lane (E3b): an unwritten struct/tuple lane. Tag only; the lane's type is its
        // position in the enclosing aggregate. Read-gated on v49.
        ConstantG::Uninit => observed_write_u8(buf, 15)?,
        // v50: one element and one fixed-width length, whatever the length.
        ConstantG::Splat { elem, len } => {
            observed_write_u8(buf, 16)?;
            buf.push_value(tasks, ConstantTask::U64(*len))?;
            buf.push_value(tasks, ConstantTask::Value(elem))?;
        }
        // v70: the 32 digest bytes, then the counted extents as fixed-width
        // `u64`s. Read-gated on v70.
        ConstantG::TensorBlob { digest, dims } => {
            observed_write_u8(buf, CONSTANT_TENSOR_BLOB_TAG)?;
            buf.extend_from_slice(&digest.0)?;
            observed_write_count(buf, "Constant::TensorBlob dims", dims.len())?;
            for dim in dims {
                observed_write_u64(buf, *dim)?;
            }
        }
        ConstantG::Ext(e) => {
            e.unreachable();
        }
    }
    Ok(())
}

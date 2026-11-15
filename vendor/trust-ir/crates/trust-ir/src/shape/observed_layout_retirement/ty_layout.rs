// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn consume<O: ExecutionObserver>(shape: TyLayoutShape, work: &mut Work<'_, '_, O>) {
    work.step(size_of::<TyLayoutShape>().saturating_add(1));
    let TyLayoutShape {
        size_bits,
        align_bits,
        kind,
    } = shape;
    work.fixed(size_bits);
    work.fixed(align_bits);
    work.step(size_of::<TyLayoutKind>().saturating_add(1));
    match kind {
        TyLayoutKind::Storage => work.fixed(()),
        TyLayoutKind::Scalar(shape) => work.fixed(shape),
        TyLayoutKind::ThinPointer => work.fixed(()),
        TyLayoutKind::FatPointer(metadata) => work.fixed(metadata),
        TyLayoutKind::Struct { id, fields } => {
            work.fixed(id);
            consume_fields(fields, work);
        }
        TyLayoutKind::Enum { id, variants } => {
            work.fixed(id);
            work.fixed(variants);
        }
        TyLayoutKind::Array {
            elem,
            len,
            stride_bits,
        } => {
            work.fixed(elem);
            work.fixed(len);
            work.fixed(stride_bits);
        }
        TyLayoutKind::Vector {
            elem_shape,
            lanes,
            lane_bits,
        } => {
            work.fixed(elem_shape);
            work.fixed(lanes);
            work.fixed(lane_bits);
        }
        TyLayoutKind::Unit => work.fixed(()),
        TyLayoutKind::Never => work.fixed(()),
        TyLayoutKind::Tuple { fields } => consume_fields(fields, work),
        TyLayoutKind::Closure { id, captures } => {
            work.fixed(id);
            consume_fields(captures, work);
        }
    }
    work.poll();
}

fn consume_fields<O: ExecutionObserver>(
    mut fields: Vec<FieldOffsetShape>,
    work: &mut Work<'_, '_, O>,
) {
    loop {
        work.step(size_of::<Option<FieldOffsetShape>>().saturating_add(1));
        let Some(field) = fields.pop() else { break };
        work.step(size_of::<FieldOffsetShape>().saturating_add(1));
        let FieldOffsetShape {
            field,
            name,
            ty_shape,
            offset_bits,
        } = field;
        work.fixed(field);
        work.text(name);
        work.fixed(ty_shape);
        work.fixed(offset_bits);
    }
    work.empty(fields);
}

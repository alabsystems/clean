// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PKG-U13d: the reference interpreter's tensor gather and scatter
//! (`Inst::TensorGather`, `Inst::TensorScatter`; SPEC_RATIFICATIONS §26) over
//! [`InterpretValueKind::Tensor`] values, in coordinate form: one integer
//! COORDINATE TENSOR per axis of the tensor indexed. Each runs its checks in
//! the order SemR (`lean/semr/SemR.lean`) spells: a poison operand, a handle
//! operand, the static rules on the instruction and the operand VALUE types
//! (`TypeError`, which `validate_module` refuses ahead of this), each tensor
//! operand's well-formedness ([`tensor_operand`], `TypeError`), then the
//! extents and bounds preconditions (undefined behaviour, by the normative
//! messages below, which SemR spells byte for byte), then the elements.

use super::*;

/// The undefined-behaviour message of a gather whose coordinate tensors do
/// not all have the first one's extents. NORMATIVE text: SemR spells it byte
/// for byte.
pub(super) const TENSOR_GATHER_EXTENT_MISMATCH: &str =
    "tensor gather: coordinate tensors have different extents";

/// The undefined-behaviour message of a gather coordinate outside its data
/// axis (negative, or at or past the extent) at some result position: the
/// gather's BOUNDS PRECONDITION. NORMATIVE text.
pub(super) const TENSOR_GATHER_OUT_OF_RANGE: &str =
    "tensor gather: a coordinate is outside its axis";

/// The undefined-behaviour message of a scatter whose coordinate tensors do
/// not all have the source's extents. NORMATIVE text.
pub(super) const TENSOR_SCATTER_EXTENT_MISMATCH: &str =
    "tensor scatter: coordinate tensor extents differ from the source's";

/// The undefined-behaviour message of a scatter coordinate outside its axis
/// of the initial tensor at some source position: the scatter's BOUNDS
/// PRECONDITION. NORMATIVE text.
pub(super) const TENSOR_SCATTER_OUT_OF_RANGE: &str =
    "tensor scatter: a coordinate is outside its axis";

/// A well-formed coordinate tensor: its extents, its elements and the
/// integer shape of its element type (each coordinate tensor has its own).
struct CoordTensor<'v> {
    dims: &'v [u64],
    elems: &'v ArrayValue,
    signed: bool,
}

impl CoordTensor<'_> {
    /// Whether the coordinate at flat position `p` is inside an axis of
    /// `extent`, and if so the coordinate. The element reads as the integer
    /// its type denotes: two's complement for a signed type (a residue at or
    /// above `2^(w-1)` is negative, so outside every axis), unsigned
    /// otherwise; `isize`/`usize` are at the module's pointer width already
    /// (`int_shape_at`).
    fn inside(
        &self,
        p: u64,
        extent: u64,
        op: &str,
        block: BlockId,
    ) -> InterpretResult<Option<u64>> {
        let int = self
            .elems
            .get(p)
            .and_then(InterpretValue::as_int)
            .ok_or_else(|| type_error(block, format!("{op}: a coordinate element is missing")))?;
        let at = if self.signed {
            u128::try_from(int.as_signed()).ok()
        } else {
            Some(int.as_unsigned())
        };
        Ok(at
            .filter(|at| *at < u128::from(extent))
            .and_then(|at| u64::try_from(at).ok()))
    }
}

/// Rule G3 / S3: `value` is a tensor of rank `rank` with an integer
/// element, and that element.
fn coordinate_element<'v>(
    value: &'v InterpretValue,
    rank: u32,
    op: &str,
    rule: &str,
    position: usize,
    block: BlockId,
) -> InterpretResult<&'v Ty> {
    match &value.ty {
        Ty::Tensor(elem, coord_rank) if *coord_rank == rank && elem.is_integer() => Ok(elem),
        other => Err(type_error(
            block,
            format!(
                "{op}: {rule}: coordinate operand {position} has type {other}, not an integer \
                 tensor of rank {rank}"
            ),
        )),
    }
}

/// The well-formedness of every coordinate tensor, in operand order, each
/// against ITS OWN element type and rank `rank`.
fn coordinate_tensors<'v>(
    coords: &[&'v InterpretValue],
    elems: &[&Ty],
    rank: u32,
    op: &str,
    pointer_bits: u32,
    block: BlockId,
) -> InterpretResult<Vec<CoordTensor<'v>>> {
    coords
        .iter()
        .zip(elems)
        .map(|(coord, elem)| {
            let (dims, values) =
                tensor_operand(coord, op, "coordinate", elem, rank, pointer_bits, block)?;
            let (_, signed) = int_shape_at(elem, pointer_bits).ok_or_else(|| {
                type_error(
                    block,
                    format!("{op}: coordinate element type {elem} has no integer shape"),
                )
            })?;
            Ok(CoordTensor {
                dims,
                elems: values,
                signed,
            })
        })
        .collect()
}

/// The row-major stride of each axis of `dims`, saturating. A stride is read
/// only at a coordinate inside every axis, which makes every extent nonzero:
/// each stride is then at most the element count, a `u64`, and so is the
/// offset. (Saturation only spares a tensor with a zero extent, whose strides
/// are never read.)
fn saturating_strides(dims: &[u64]) -> Vec<u64> {
    let mut strides = vec![0u64; dims.len()];
    let mut stride = 1u64;
    for (slot, &dim) in strides.iter_mut().zip(dims).rev() {
        *slot = stride;
        stride = stride.saturating_mul(dim);
    }
    strides
}

/// The flat offset, under `strides`, of the coordinates the coordinate
/// tensors hold at position `p`, or `None` when one is outside its axis of
/// `extents` (the bounds precondition).
fn indexed_offset(
    coords: &[CoordTensor<'_>],
    p: u64,
    extents: &[u64],
    strides: &[u64],
    op: &str,
    block: BlockId,
) -> InterpretResult<Option<u64>> {
    let mut offset = 0u64;
    for ((coord, &extent), &stride) in coords.iter().zip(extents).zip(strides) {
        let Some(at) = coord.inside(p, extent, op, block)? else {
            return Ok(None);
        };
        offset += at * stride;
    }
    Ok(Some(offset))
}

impl<'m> Interpreter<'m> {
    /// `TensorGather { ty, data, coords }` (PKG-U13d). The checks, in the
    /// order both engines share:
    ///
    /// 1. a poison operand (the data, then the coordinate tensors in order)
    ///    is undefined behaviour (`reject_partial`);
    /// 2. a runtime handle operand, in the same order, is refused
    ///    (`reject_handle`);
    /// 3. the static rules (`TypeError`; `InvalidTensorGather` in the
    ///    validator): G1, `ty` is `tensor<E, r>` and `data` a `tensor<E, s>`
    ///    for one integer `E`; G2, `s >= 1` and `coords` has exactly `s`
    ///    operands; G3, every coordinate operand is a tensor of rank `r` with
    ///    an integer element, checked in operand order;
    /// 4. the well-formedness of the data, then of each coordinate tensor
    ///    against its own element type;
    /// 5. extent agreement: every coordinate tensor's extents are the first's
    ///    (undefined behaviour, [`TENSOR_GATHER_EXTENT_MISMATCH`]);
    /// 6. the bounds precondition: at every result position, every
    ///    coordinate is inside its data axis (undefined behaviour,
    ///    [`TENSOR_GATHER_OUT_OF_RANGE`]);
    /// 7. the elements: the result's extents are the coordinate tensors',
    ///    and at each position `p` (row major) the element is `data`'s at
    ///    `(coords[0][p], .., coords[s-1][p])`, as ONE node.
    pub(super) fn eval_tensor_gather(
        &self,
        ty: &Ty,
        data: &InterpretValue,
        coords: &[&InterpretValue],
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        const OP: &str = "tensor gather";
        let operands = || core::iter::once(data).chain(coords.iter().copied());
        for operand in operands() {
            reject_partial(operand, block, "tensor_gather")?;
        }
        for operand in operands() {
            reject_handle(operand, block, "TensorGather")?;
        }

        // G1: two integer tensors of one element type.
        let (Ty::Tensor(elem, r), Ty::Tensor(data_elem, s)) = (ty, &data.ty) else {
            return Err(type_error(
                block,
                format!(
                    "{OP}: G1: the result {ty} and the data {} must be tensor types",
                    data.ty
                ),
            ));
        };
        let elem: &Ty = elem;
        if **data_elem != *elem || !elem.is_integer() {
            return Err(type_error(
                block,
                format!(
                    "{OP}: G1: the element types (result {elem}, data {data_elem}) are not one \
                     integer type"
                ),
            ));
        }
        // G2: one coordinate tensor per data axis, and at least one axis.
        if *s == 0 || coords.len() as u64 != u64::from(*s) {
            return Err(type_error(
                block,
                format!(
                    "{OP}: G2: {} coordinate operands for data of rank {s} (one per axis, at \
                     least one)",
                    coords.len()
                ),
            ));
        }
        // G3: every coordinate operand an integer tensor of the result rank.
        let coord_elems = coords
            .iter()
            .enumerate()
            .map(|(position, coord)| coordinate_element(coord, *r, OP, "G3", position, block))
            .collect::<InterpretResult<Vec<&Ty>>>()?;

        let pointer_bits = self.pointer_bits();
        let (data_dims, data_elems) =
            tensor_operand(data, OP, "data", elem, *s, pointer_bits, block)?;
        let coords = coordinate_tensors(coords, &coord_elems, *r, OP, pointer_bits, block)?;

        // The extents precondition. G2 makes `coords` non-empty.
        let dims = coords[0].dims;
        if coords.iter().any(|coord| coord.dims != dims) {
            return Err(ub(block, TENSOR_GATHER_EXTENT_MISMATCH));
        }
        // Well-formedness makes the count the first coordinate tensor's
        // element count, so it fits.
        let count = coords[0].elems.len();

        // The bounds precondition, at every position, before any element.
        let strides = saturating_strides(data_dims);
        for p in 0..count {
            if indexed_offset(&coords, p, data_dims, &strides, OP, block)?.is_none() {
                return Err(ub(block, TENSOR_GATHER_OUT_OF_RANGE));
            }
        }

        let elems = ArrayValue::try_from_elements((0..count).map(|p| -> InterpretResult<_> {
            let offset = indexed_offset(&coords, p, data_dims, &strides, OP, block)?
                .ok_or_else(|| ub(block, TENSOR_GATHER_OUT_OF_RANGE))?;
            data_elems
                .get(offset)
                .cloned()
                .ok_or_else(|| type_error(block, format!("{OP}: a data element is missing")))
        }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: dims.to_vec(),
                elems,
            },
        })
    }

    /// `TensorScatter { ty, init, src, coords }` (PKG-U13d). The checks, in
    /// the order both engines share:
    ///
    /// 1. a poison operand (the initial tensor, the source, then the
    ///    coordinate tensors in order) is undefined behaviour;
    /// 2. a runtime handle operand, in the same order, is refused;
    /// 3. the static rules (`TypeError`; `InvalidTensorScatter`): S1, `ty` is
    ///    `tensor<E, s>` with `E` an integer, `init` has type `ty`, and `src`
    ///    is a `tensor<E, r>`; S2, `s >= 1` and `coords` has exactly `s`
    ///    operands; S3, every coordinate operand is a tensor of rank `r` with
    ///    an integer element, checked in operand order;
    /// 4. the well-formedness of the initial tensor, the source, then each
    ///    coordinate tensor against its own element type;
    /// 5. extent agreement: every coordinate tensor's extents are the
    ///    source's (undefined behaviour, [`TENSOR_SCATTER_EXTENT_MISMATCH`]);
    /// 6. the bounds precondition: at every source position, every
    ///    coordinate is inside its axis of `init`, decided before any element
    ///    is written (undefined behaviour, [`TENSOR_SCATTER_OUT_OF_RANGE`]);
    /// 7. the elements: the result has `init`'s extents and starts as
    ///    `init`'s elements; then for each source position `p` in row-major
    ///    order, the element at `(coords[0][p], .., coords[s-1][p])` becomes
    ///    `src`'s at `p`, so the row-major-LAST write to a repeated
    ///    coordinate is the one the result holds. One node.
    pub(super) fn eval_tensor_scatter(
        &self,
        ty: &Ty,
        init: &InterpretValue,
        src: &InterpretValue,
        coords: &[&InterpretValue],
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        const OP: &str = "tensor scatter";
        let operands = || {
            core::iter::once(init)
                .chain(core::iter::once(src))
                .chain(coords.iter().copied())
        };
        for operand in operands() {
            reject_partial(operand, block, "tensor_scatter")?;
        }
        for operand in operands() {
            reject_handle(operand, block, "TensorScatter")?;
        }

        // S1: the result an integer tensor, `init` of its type, `src` an
        // integer tensor of its element.
        let Ty::Tensor(elem, s) = ty else {
            return Err(type_error(
                block,
                format!("{OP}: S1: the result {ty} must be a tensor type"),
            ));
        };
        let elem: &Ty = elem;
        if !elem.is_integer() {
            return Err(type_error(
                block,
                format!("{OP}: S1: the result element {elem} is not an integer type"),
            ));
        }
        if init.ty != *ty {
            return Err(type_error(
                block,
                format!(
                    "{OP}: S1: the initial tensor has type {}, not the result's {ty}",
                    init.ty
                ),
            ));
        }
        let Ty::Tensor(src_elem, r) = &src.ty else {
            return Err(type_error(
                block,
                format!("{OP}: S1: the source {} must be a tensor type", src.ty),
            ));
        };
        if **src_elem != *elem {
            return Err(type_error(
                block,
                format!("{OP}: S1: the source element {src_elem} is not the result's {elem}"),
            ));
        }
        // S2: one coordinate tensor per axis of `init`, and at least one.
        if *s == 0 || coords.len() as u64 != u64::from(*s) {
            return Err(type_error(
                block,
                format!(
                    "{OP}: S2: {} coordinate operands for a result of rank {s} (one per axis, \
                     at least one)",
                    coords.len()
                ),
            ));
        }
        // S3: every coordinate operand an integer tensor of the source rank.
        let coord_elems = coords
            .iter()
            .enumerate()
            .map(|(position, coord)| coordinate_element(coord, *r, OP, "S3", position, block))
            .collect::<InterpretResult<Vec<&Ty>>>()?;

        let pointer_bits = self.pointer_bits();
        let (init_dims, init_elems) =
            tensor_operand(init, OP, "initial", elem, *s, pointer_bits, block)?;
        let (src_dims, src_elems) =
            tensor_operand(src, OP, "source", elem, *r, pointer_bits, block)?;
        let coords = coordinate_tensors(coords, &coord_elems, *r, OP, pointer_bits, block)?;

        // The extents precondition.
        if coords.iter().any(|coord| coord.dims != src_dims) {
            return Err(ub(block, TENSOR_SCATTER_EXTENT_MISMATCH));
        }
        let count = src_elems.len();

        // The bounds precondition, at every source position, before any
        // element is written.
        let strides = saturating_strides(init_dims);
        let mut offsets = Vec::new();
        for p in 0..count {
            let offset = indexed_offset(&coords, p, init_dims, &strides, OP, block)?
                .ok_or_else(|| ub(block, TENSOR_SCATTER_OUT_OF_RANGE))?;
            offsets.push(offset);
        }

        // The writes, in the source's row-major order: the last one at a
        // coordinate is the one the result holds.
        let mut elems = init_elems.clone();
        for (p, offset) in (0..count).zip(offsets) {
            let value = src_elems
                .get(p)
                .cloned()
                .ok_or_else(|| type_error(block, format!("{OP}: a source element is missing")))?;
            elems = elems
                .set(offset, value)
                .ok_or_else(|| type_error(block, format!("{OP}: a written element is missing")))?;
        }
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: init_dims.to_vec(),
                elems,
            },
        })
    }
}

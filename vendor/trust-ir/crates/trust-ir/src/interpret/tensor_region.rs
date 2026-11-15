// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PKG-U13c: the reference interpreter's tensor map, reduction and view
//! (`Inst::TensorMap`, `Inst::TensorReduce`, `Inst::TensorView`) over
//! [`InterpretValueKind::Tensor`] values. Each runs its checks in the order
//! SemR (`lean/semr/SemR.lean`) spells: a poison operand, the static rules on
//! the instruction and the operand VALUE types (`TypeError`, which
//! `validate_module` refuses ahead of this), each tensor operand's
//! well-formedness ([`tensor_operand`], `TypeError`), then the preconditions
//! (undefined behaviour, by the normative messages below, which SemR spells
//! byte for byte), then the elements.

use super::*;
use crate::{TensorIndexExpr, TensorMapNode, TensorReduceOp, TensorReduceOrder};

/// The undefined-behaviour message of a map whose tensor operands have
/// different extents. NORMATIVE text: SemR spells it byte for byte.
pub(super) const TENSOR_MAP_EXTENT_MISMATCH: &str = "tensor map: operand extents differ";

/// The undefined-behaviour message of a reduction whose result count is
/// `2^pointer_bits` or more (reachable only when a reduced extent is 0, so
/// the source has no element). NORMATIVE text.
pub(super) const TENSOR_REDUCE_RESULT_TOO_LARGE: &str =
    "tensor reduction: the result has more elements than usize holds";

/// A view node's value outside `[-2^127, 2^127)`. NORMATIVE text.
pub(super) const TENSOR_VIEW_OVERFLOW: &str = "tensor view: an index expression overflows";
/// A view node's `Div` or `Rem` by zero. NORMATIVE text.
pub(super) const TENSOR_VIEW_DIVIDES_BY_ZERO: &str =
    "tensor view: an index expression divides by zero";
/// A view's result extent that is negative or at least `2^pointer_bits`.
/// NORMATIVE text.
pub(super) const TENSOR_VIEW_EXTENT_UNFIT: &str = "tensor view: a result extent does not fit usize";
/// A view's result count at or past `2^pointer_bits`. NORMATIVE text.
pub(super) const TENSOR_VIEW_RESULT_TOO_LARGE: &str =
    "tensor view: the result has more elements than usize holds";
/// A source coordinate outside its axis in a view with no fill. NORMATIVE
/// text.
pub(super) const TENSOR_VIEW_OUT_OF_RANGE: &str =
    "tensor view: a source coordinate is out of range";

/// A tensor view's coordinate function: its nodes, the node of each result
/// extent and the node of each source coordinate.
pub(super) struct ViewFunction<'a> {
    pub(super) exprs: &'a [TensorIndexExpr],
    pub(super) shape: &'a [u32],
    pub(super) index: &'a [u32],
}

/// Whether `ty` is a type a map lane or node may have: an integer or `Bool`.
fn is_scalar_lane_ty(ty: &Ty) -> bool {
    ty.is_integer() || matches!(ty, Ty::Bool)
}

/// The lanes `node` reads, each with the type the node requires of it.
fn node_lane_types(node: &TensorMapNode<crate::level::NoExt>) -> Vec<(u32, Ty)> {
    match node {
        TensorMapNode::BinOp { ty, lhs, rhs, .. } | TensorMapNode::ICmp { ty, lhs, rhs, .. } => {
            vec![(*lhs, ty.clone()), (*rhs, ty.clone())]
        }
        TensorMapNode::UnOp { ty, operand, .. } => vec![(*operand, ty.clone())],
        TensorMapNode::Select {
            ty,
            cond,
            then_lane,
            else_lane,
        } => vec![
            (*cond, Ty::Bool),
            (*then_lane, ty.clone()),
            (*else_lane, ty.clone()),
        ],
        TensorMapNode::Cast {
            src_ty, operand, ..
        } => vec![(*operand, src_ty.clone())],
    }
}

/// The operator's identity at an integer of `bits` bits: the value a fold
/// over no element yields.
fn reduce_identity(op: TensorReduceOp, bits: u32) -> u128 {
    let mask = int_mask(bits).expect("validated integer width");
    let sign = 1u128 << (bits - 1);
    match op {
        TensorReduceOp::Add | TensorReduceOp::Or | TensorReduceOp::Xor | TensorReduceOp::UMax => 0,
        TensorReduceOp::Mul => 1,
        TensorReduceOp::And | TensorReduceOp::UMin => mask,
        // The signed maximum, and the signed minimum (its residue `2^(w-1)`).
        TensorReduceOp::SMin => sign - 1,
        TensorReduceOp::SMax => sign,
    }
}

/// One fold step `acc OP x` at one integer type.
fn reduce_step(
    op: TensorReduceOp,
    acc: InterpretInt,
    x: InterpretInt,
    block: BlockId,
) -> InterpretResult<InterpretInt> {
    Ok(match op {
        TensorReduceOp::Add => eval_int_binop(BinOp::Add, acc, x, block)?,
        TensorReduceOp::Mul => eval_int_binop(BinOp::Mul, acc, x, block)?,
        TensorReduceOp::And => eval_int_binop(BinOp::And, acc, x, block)?,
        TensorReduceOp::Or => eval_int_binop(BinOp::Or, acc, x, block)?,
        TensorReduceOp::Xor => eval_int_binop(BinOp::Xor, acc, x, block)?,
        TensorReduceOp::SMin => {
            if x.as_signed() < acc.as_signed() {
                x
            } else {
                acc
            }
        }
        TensorReduceOp::SMax => {
            if x.as_signed() > acc.as_signed() {
                x
            } else {
                acc
            }
        }
        TensorReduceOp::UMin => {
            if x.raw < acc.raw {
                x
            } else {
                acc
            }
        }
        TensorReduceOp::UMax => {
            if x.raw > acc.raw {
                x
            } else {
                acc
            }
        }
    })
}

/// A view node's value checked against `[-2^127, 2^127)`: exactly the
/// `i128` range, so `None` (an `i128` operation that overflowed) is that
/// undefined behaviour.
fn view_value(value: Option<i128>, block: BlockId) -> InterpretResult<i128> {
    value.ok_or_else(|| ub(block, TENSOR_VIEW_OVERFLOW))
}

/// The value of view node `expr` from the values before it (`values[k]` is
/// node `k`'s, `None` where it is not computed in this phase) and the result
/// coordinate (`None` in the shape phase, where no `Coord` node is read).
/// Arithmetic is over the integers: `Div`/`Rem` are Euclidean (Rust's
/// `div_euclid`/`rem_euclid`, Lean's `Int.ediv`/`Int.emod`); a divisor of 0 is
/// undefined behaviour, and so is a value outside the `i128` range.
fn view_node(
    expr: &TensorIndexExpr,
    values: &[Option<i128>],
    params: &[i128],
    src_dims: &[u64],
    coord: Option<&[u64]>,
    block: BlockId,
) -> InterpretResult<i128> {
    let at = |node: u32| -> InterpretResult<i128> {
        values
            .get(node as usize)
            .copied()
            .flatten()
            .ok_or_else(|| type_error(block, "tensor view: a node reads an uncomputed node"))
    };
    let missing = || type_error(block, "tensor view: a node reads past its operands");
    Ok(match *expr {
        TensorIndexExpr::Lit(n) => i128::from(n),
        TensorIndexExpr::Param(k) => *params.get(k as usize).ok_or_else(missing)?,
        TensorIndexExpr::SrcExtent(j) => i128::from(*src_dims.get(j as usize).ok_or_else(missing)?),
        TensorIndexExpr::Coord(i) => {
            let coord = coord.ok_or_else(missing)?;
            i128::from(*coord.get(i as usize).ok_or_else(missing)?)
        }
        TensorIndexExpr::Add(a, b) => view_value(at(a)?.checked_add(at(b)?), block)?,
        TensorIndexExpr::Sub(a, b) => view_value(at(a)?.checked_sub(at(b)?), block)?,
        TensorIndexExpr::Mul(a, b) => view_value(at(a)?.checked_mul(at(b)?), block)?,
        TensorIndexExpr::Div(a, b) => {
            let (a, b) = (at(a)?, at(b)?);
            if b == 0 {
                return Err(ub(block, TENSOR_VIEW_DIVIDES_BY_ZERO));
            }
            // Only `i128::MIN / -1` overflows: its quotient is `2^127`.
            view_value(a.checked_div_euclid(b), block)?
        }
        TensorIndexExpr::Rem(a, b) => {
            let (a, b) = (at(a)?, at(b)?);
            if b == 0 {
                return Err(ub(block, TENSOR_VIEW_DIVIDES_BY_ZERO));
            }
            // A Euclidean remainder lies in `[0, |b|)`, always in range;
            // `wrapping_` only spares `i128::MIN % -1`, whose remainder is 0.
            a.wrapping_rem_euclid(b)
        }
        TensorIndexExpr::Min(a, b) => at(a)?.min(at(b)?),
        TensorIndexExpr::Max(a, b) => at(a)?.max(at(b)?),
    })
}

impl<'m> Interpreter<'m> {
    /// `TensorMap { ty, args, body }` (PKG-U13c). The checks, in the order
    /// both engines share:
    ///
    /// 1. a poison operand is undefined behaviour (`reject_partial`), and a
    ///    runtime handle is refused (`reject_handle`);
    /// 2. the static rules (`TypeError`; `InvalidTensorMap` in the
    ///    validator): `ty` is `tensor<E, r>` with `E` an integer; every
    ///    operand is a `tensor<E_i, r>` with `E_i` an integer, or an integer
    ///    or `Bool` scalar, and at least one is a tensor; the body is not
    ///    empty; every type a node names is an integer or `Bool`; node `j`
    ///    reads only lanes below `n + j`, each of the type the node requires;
    ///    the last node's type is `E`;
    /// 3. each tensor operand's well-formedness, in operand order;
    /// 4. extent agreement: every tensor operand's extents are the first's
    ///    (undefined behaviour, [`TENSOR_MAP_EXTENT_MISMATCH`]);
    /// 5. at each coordinate, in row-major order, the nodes in order through
    ///    the scalar instruction's own evaluator (`eval_binop`, `eval_unop`,
    ///    `eval_icmp`, `eval_select`, `eval_cast`), whose verdicts are the
    ///    node's; the element is the last node's value.
    pub(super) fn eval_tensor_map(
        &self,
        ty: &Ty,
        args: &[&InterpretValue],
        body: &[TensorMapNode<crate::level::NoExt>],
        state: &ExecState,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        for arg in args {
            reject_partial(arg, block, "tensor_map")?;
        }
        for arg in args {
            reject_handle(arg, block, "TensorMap")?;
        }
        let pointer_bits = self.pointer_bits();

        // M1: the result is an integer tensor.
        let Ty::Tensor(elem, rank) = ty else {
            return Err(type_error(
                block,
                format!("tensor map: the result type {ty} is not a tensor type"),
            ));
        };
        let elem: &Ty = elem;
        if !elem.is_integer() {
            return Err(type_error(
                block,
                format!("tensor map: element type {elem} is not an integer type"),
            ));
        }
        // M2: the operands, and the type of each operand lane.
        let n = args.len();
        let mut lane_tys: Vec<Ty> = Vec::with_capacity(n + body.len());
        let mut any_tensor = false;
        for (i, arg) in args.iter().enumerate() {
            match &arg.ty {
                Ty::Tensor(arg_elem, arg_rank) => {
                    if arg_rank != rank || !arg_elem.is_integer() {
                        return Err(type_error(
                            block,
                            format!(
                                "tensor map: operand {i} has type {}, not an integer tensor of \
                                 rank {rank}",
                                arg.ty
                            ),
                        ));
                    }
                    any_tensor = true;
                    lane_tys.push((**arg_elem).clone());
                }
                scalar if is_scalar_lane_ty(scalar) => lane_tys.push(scalar.clone()),
                other => {
                    return Err(type_error(
                        block,
                        format!(
                            "tensor map: operand {i} has type {other}, neither a tensor nor an \
                             integer or Bool scalar"
                        ),
                    ));
                }
            }
        }
        if !any_tensor {
            return Err(type_error(block, "tensor map: no operand is a tensor"));
        }
        // M3, M4: the body.
        if body.is_empty() {
            return Err(type_error(block, "tensor map: the body is empty"));
        }
        for (j, node) in body.iter().enumerate() {
            if let Some(bad) = node.types().into_iter().find(|t| !is_scalar_lane_ty(t)) {
                return Err(type_error(
                    block,
                    format!("tensor map: node {j} names {bad}, not an integer or Bool type"),
                ));
            }
            for (lane, want) in node_lane_types(node) {
                // `lane_tys` holds exactly the lanes below `n + j` here.
                let Some(have) = lane_tys.get(lane as usize) else {
                    return Err(type_error(
                        block,
                        format!("tensor map: node {j} reads lane {lane}, not before it"),
                    ));
                };
                if *have != want {
                    return Err(type_error(
                        block,
                        format!("tensor map: node {j} reads lane {lane} of type {have} as {want}"),
                    ));
                }
            }
            // M4's operation half: the one rule the validator applies.
            if let Some(reason) = node.op_refusal(pointer_bits) {
                return Err(type_error(block, format!("tensor map: node {j}: {reason}")));
            }
            lane_tys.push(node.value_ty());
        }
        // M5: the last node is an element.
        if lane_tys.last() != Some(elem) {
            return Err(type_error(
                block,
                format!("tensor map: the last node's type is not the element type {elem}"),
            ));
        }

        // Each tensor operand's well-formedness, in operand order.
        let mut tensors: Vec<Option<(&[u64], &ArrayValue)>> = Vec::with_capacity(n);
        for (i, arg) in args.iter().enumerate() {
            tensors.push(match &arg.ty {
                Ty::Tensor(arg_elem, arg_rank) => Some(tensor_operand(
                    arg,
                    "tensor map",
                    &format!("operand {i}"),
                    arg_elem,
                    *arg_rank,
                    pointer_bits,
                    block,
                )?),
                _ => None,
            });
        }
        // Extent agreement, against the first tensor operand.
        let mut shapes = tensors.iter().flatten();
        let (dims, first_elems) = *shapes.next().expect("M2: a tensor operand");
        if shapes.any(|(other, _)| *other != dims) {
            return Err(ub(block, TENSOR_MAP_EXTENT_MISMATCH));
        }

        let count = first_elems.len();
        let missing = || type_error(block, "tensor map: an operand element is missing");
        let elems = ArrayValue::try_from_elements((0..count).map(|flat| -> InterpretResult<_> {
            let mut lanes: Vec<InterpretValue> = Vec::with_capacity(n + body.len());
            for (arg, tensor) in args.iter().zip(&tensors) {
                lanes.push(match tensor {
                    Some((_, elems)) => elems.get(flat).cloned().ok_or_else(missing)?,
                    None => (*arg).clone(),
                });
            }
            for node in body {
                let lane = |k: u32| &lanes[k as usize];
                let value = match node {
                    TensorMapNode::BinOp { op, ty, lhs, rhs } => {
                        self.eval_binop(*op, ty, lane(*lhs), lane(*rhs), block)?
                    }
                    TensorMapNode::UnOp { op, ty, operand } => {
                        self.eval_unop(*op, ty, lane(*operand), block)?
                    }
                    TensorMapNode::ICmp { op, ty, lhs, rhs } => {
                        self.eval_icmp(*op, ty, lane(*lhs), lane(*rhs), state, block)?
                    }
                    TensorMapNode::Select {
                        ty,
                        cond,
                        then_lane,
                        else_lane,
                    } => self.eval_select(
                        ty,
                        lane(*cond),
                        lane(*then_lane),
                        lane(*else_lane),
                        block,
                    )?,
                    TensorMapNode::Cast {
                        op,
                        src_ty,
                        dst_ty,
                        operand,
                    } => self.eval_cast(*op, src_ty, dst_ty, lane(*operand), state, block)?,
                };
                lanes.push(value);
            }
            let element = lanes.pop().expect("M3: a non-empty body");
            if element.ty != *elem || element.as_int().is_none() {
                return Err(type_error(
                    block,
                    format!(
                        "tensor map: an element of type {} is not a {elem}",
                        element.ty
                    ),
                ));
            }
            Ok(element)
        }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: dims.to_vec(),
                elems,
            },
        })
    }

    /// `TensorReduce { ty, src, op, axes, order }` (PKG-U13c). The checks,
    /// in the order both engines share: a poison source (undefined
    /// behaviour) or a handle; the static rules (`TypeError`;
    /// `InvalidTensorReduce`): `ty` is `tensor<E, r>` and `src` a
    /// `tensor<E, s>` with `E` an integer, `axes` strictly ascending and each
    /// below `s`, and `r == s - |axes|`; the source's well-formedness; the
    /// result count, `2^pointer_bits` or more being undefined behaviour
    /// ([`TENSOR_REDUCE_RESULT_TOO_LARGE`]). The result's extents are the
    /// source's at the kept axes, ascending; each element, in row-major
    /// order, is a LEFT FOLD from `op`'s identity over the reduced
    /// multi-index in row-major order (the first reduced axis outermost), so
    /// an empty reduced extent gives the identity, as ONE uniform node.
    pub(super) fn eval_tensor_reduce(
        &self,
        ty: &Ty,
        src: &InterpretValue,
        op: TensorReduceOp,
        axes: &[u32],
        order: TensorReduceOrder,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        reject_partial(src, block, "tensor_reduce")?;
        reject_handle(src, block, "TensorReduce")?;
        let TensorReduceOrder::RowMajor = order;

        // R1: two integer tensors of one element type.
        let (Ty::Tensor(elem, r), Ty::Tensor(src_elem, s)) = (ty, &src.ty) else {
            return Err(type_error(
                block,
                format!(
                    "tensor reduction: the result {ty} and the source {} must be tensor types",
                    src.ty
                ),
            ));
        };
        let elem: &Ty = elem;
        if **src_elem != *elem || !elem.is_integer() {
            return Err(type_error(
                block,
                format!(
                    "tensor reduction: the element types (result {elem}, source {src_elem}) are \
                     not one integer type"
                ),
            ));
        }
        // R2: the axes are strictly ascending and in range.
        if axes.windows(2).any(|w| w[0] >= w[1]) || axes.iter().any(|axis| axis >= s) {
            return Err(type_error(
                block,
                format!(
                    "tensor reduction: the axes {axes:?} are not strictly ascending axes of rank \
                     {s}"
                ),
            ));
        }
        // R3: the result rank. R2 makes `|axes| <= s`.
        if u64::from(*r) != u64::from(*s) - axes.len() as u64 {
            return Err(type_error(
                block,
                format!(
                    "tensor reduction: the result rank is {r}, but rank {s} less {} reduced axes",
                    axes.len()
                ),
            ));
        }

        let pointer_bits = self.pointer_bits();
        let (src_dims, src_elems) = tensor_operand(
            src,
            "tensor reduction",
            "source",
            elem,
            *s,
            pointer_bits,
            block,
        )?;
        let reduced: Vec<u64> = axes.iter().map(|&axis| src_dims[axis as usize]).collect();
        let kept_axes: Vec<usize> = (0..*s as usize)
            .filter(|axis| !axes.contains(&(*axis as u32)))
            .collect();
        let result_dims: Vec<u64> = kept_axes.iter().map(|&axis| src_dims[axis]).collect();
        let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
        let count = exact_product_below(&result_dims, usize_limit)
            .ok_or_else(|| ub(block, TENSOR_REDUCE_RESULT_TOO_LARGE))?;

        let (bits, signed) = int_shape_at(elem, pointer_bits).ok_or_else(|| {
            type_error(
                block,
                format!("tensor reduction: element type {elem} has no integer shape"),
            )
        })?;
        let identity =
            InterpretInt::from_raw(bits, signed, reduce_identity(op, bits)).ok_or_else(|| {
                type_error(
                    block,
                    format!("tensor reduction: unsupported integer width {bits}"),
                )
            })?;
        let as_value = |int: InterpretInt| InterpretValue {
            ty: elem.clone(),
            kind: InterpretValueKind::Int(int),
        };
        if count == 0 || reduced.contains(&0) {
            // No element, or every fold empty: one uniform node.
            return Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Tensor {
                    dims: result_dims,
                    elems: ArrayValue::splat(as_value(identity), count),
                },
            });
        }

        // From here every extent is nonzero, so every stride and the term
        // count are at most the source's element count, a `u64`.
        let overflow = || {
            type_error(
                block,
                "tensor reduction: source strides exceed the element count",
            )
        };
        let strides = row_major_strides(src_dims).ok_or_else(overflow)?;
        let terms = exact_product_below(&reduced, 1u128 << 64).ok_or_else(overflow)?;
        let kept_strides: Vec<u64> = kept_axes.iter().map(|&axis| strides[axis]).collect();
        let reduced_strides: Vec<u64> = axes.iter().map(|&axis| strides[axis as usize]).collect();
        let elems = ArrayValue::try_from_elements((0..count).map(|flat| -> InterpretResult<_> {
            let (base, _) = row_major_offsets(flat, &result_dims, &kept_strides, &kept_strides);
            let mut acc = identity;
            for term in 0..terms {
                let (at, _) = row_major_offsets(term, &reduced, &reduced_strides, &reduced_strides);
                let x = src_elems
                    .get(base + at)
                    .and_then(InterpretValue::as_int)
                    .ok_or_else(|| {
                        type_error(block, "tensor reduction: a source element is missing")
                    })?;
                acc = reduce_step(op, acc, x, block)?;
            }
            Ok(as_value(acc))
        }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor {
                dims: result_dims,
                elems,
            },
        })
    }

    /// `TensorView { ty, src, params, exprs, shape, index, fill }`
    /// (PKG-U13c). The checks, in the order both engines share:
    ///
    /// 1. a poison operand (the source, the parameters in order, the fill) is
    ///    undefined behaviour, and a runtime handle is refused;
    /// 2. the static rules (`TypeError`; `InvalidTensorView`): `ty` is
    ///    `tensor<E, r>` and `src` a `tensor<E, s>` with `E` an integer;
    ///    every parameter is a `usize`; the fill, when present, is an `E`;
    ///    `|shape| == r`, `|index| == s`, each naming a node; an arithmetic
    ///    node reads only nodes before it, `Param(k)` names a parameter,
    ///    `SrcExtent(j)` a source axis and `Coord(i)` a result axis; every
    ///    shape node is shape-phase ([`crate::tensor_view_index_phase`]);
    /// 3. the source's well-formedness;
    /// 4. the shape-phase nodes, in id order ([`TENSOR_VIEW_OVERFLOW`],
    ///    [`TENSOR_VIEW_DIVIDES_BY_ZERO`]);
    /// 5. the extents, each in `[0, 2^pointer_bits)`
    ///    ([`TENSOR_VIEW_EXTENT_UNFIT`]), and their product below
    ///    `2^pointer_bits` ([`TENSOR_VIEW_RESULT_TOO_LARGE`]);
    /// 6. at each result coordinate, in row-major order, the index-phase
    ///    nodes in id order (the same two verdicts), then the source
    ///    coordinate: where some axis is out of range the element is the
    ///    fill, or with no fill undefined behaviour
    ///    ([`TENSOR_VIEW_OUT_OF_RANGE`]); else the source element there.
    pub(super) fn eval_tensor_view(
        &self,
        ty: &Ty,
        src: &InterpretValue,
        params: &[&InterpretValue],
        function: &ViewFunction<'_>,
        fill: Option<&InterpretValue>,
        block: BlockId,
    ) -> InterpretResult<InterpretValue> {
        let ViewFunction {
            exprs,
            shape,
            index,
        } = *function;
        let operands = || {
            core::iter::once(src)
                .chain(params.iter().copied())
                .chain(fill)
        };
        for operand in operands() {
            reject_partial(operand, block, "tensor_view")?;
        }
        for operand in operands() {
            reject_handle(operand, block, "TensorView")?;
        }

        // V1: two integer tensors of one element type.
        let (Ty::Tensor(elem, r), Ty::Tensor(src_elem, s)) = (ty, &src.ty) else {
            return Err(type_error(
                block,
                format!(
                    "tensor view: the result {ty} and the source {} must be tensor types",
                    src.ty
                ),
            ));
        };
        let elem: &Ty = elem;
        if **src_elem != *elem || !elem.is_integer() {
            return Err(type_error(
                block,
                format!(
                    "tensor view: the element types (result {elem}, source {src_elem}) are not \
                     one integer type"
                ),
            ));
        }
        // V2, V3: the parameters and the fill.
        if let Some(param) = params.iter().find(|param| param.ty != Ty::Usize) {
            return Err(type_error(
                block,
                format!("tensor view: a parameter has type {}, not usize", param.ty),
            ));
        }
        if let Some(fill) = fill.filter(|fill| fill.ty != *elem) {
            return Err(type_error(
                block,
                format!("tensor view: the fill has type {}, not {elem}", fill.ty),
            ));
        }
        // V4, V5: the node references.
        if shape.len() as u64 != u64::from(*r) || index.len() as u64 != u64::from(*s) {
            return Err(type_error(
                block,
                format!(
                    "tensor view: {} shape and {} index nodes for ranks {r} and {s}",
                    shape.len(),
                    index.len()
                ),
            ));
        }
        if shape
            .iter()
            .chain(index)
            .any(|node| *node as usize >= exprs.len())
        {
            return Err(type_error(
                block,
                "tensor view: a shape or index entry names no node",
            ));
        }
        for (id, expr) in exprs.iter().enumerate() {
            let fits = match *expr {
                TensorIndexExpr::Lit(_) => true,
                TensorIndexExpr::Param(k) => (k as usize) < params.len(),
                TensorIndexExpr::SrcExtent(j) => j < *s,
                TensorIndexExpr::Coord(i) => i < *r,
                _ => expr
                    .operands()
                    .is_some_and(|(a, b)| (a as usize) < id && (b as usize) < id),
            };
            if !fits {
                return Err(type_error(
                    block,
                    format!("tensor view: node {id} ({expr}) reads out of its scope"),
                ));
            }
        }
        // V6: no extent depends on a coordinate.
        let index_phase = crate::tensor_view_index_phase(exprs);
        if shape.iter().any(|node| index_phase[*node as usize]) {
            return Err(type_error(
                block,
                "tensor view: a result extent depends on a coordinate",
            ));
        }

        let pointer_bits = self.pointer_bits();
        let (src_dims, src_elems) =
            tensor_operand(src, "tensor view", "source", elem, *s, pointer_bits, block)?;
        let params: Vec<i128> = params
            .iter()
            .map(|param| {
                param
                    .as_int()
                    .map(|int| int.raw as i128)
                    .ok_or_else(|| type_error(block, "tensor view: a parameter is not an integer"))
            })
            .collect::<InterpretResult<_>>()?;

        // The shape phase, once.
        let mut values: Vec<Option<i128>> = Vec::with_capacity(exprs.len());
        for (expr, in_index_phase) in exprs.iter().zip(&index_phase) {
            values.push(if *in_index_phase {
                None
            } else {
                Some(view_node(expr, &values, &params, src_dims, None, block)?)
            });
        }
        // The extents and the count.
        let usize_limit = 1u128.checked_shl(pointer_bits).unwrap_or(u128::MAX);
        let dims = shape
            .iter()
            .map(|node| {
                let value = values[*node as usize].expect("V6: a shape-phase node");
                u64::try_from(value)
                    .ok()
                    .filter(|extent| u128::from(*extent) < usize_limit)
                    .ok_or_else(|| ub(block, TENSOR_VIEW_EXTENT_UNFIT))
            })
            .collect::<InterpretResult<Vec<u64>>>()?;
        let count = exact_product_below(&dims, usize_limit)
            .ok_or_else(|| ub(block, TENSOR_VIEW_RESULT_TOO_LARGE))?;

        // The source strides are read only at a coordinate in range on every
        // axis, which makes every source extent nonzero: each stride is then
        // at most the source's element count, a `u64`, and so is the offset.
        // (`saturating_` only spares a source with a zero extent, whose
        // strides are never read.)
        let mut src_strides = vec![0u64; src_dims.len()];
        let mut stride = 1u64;
        for (slot, &dim) in src_strides.iter_mut().zip(src_dims).rev() {
            *slot = stride;
            stride = stride.saturating_mul(dim);
        }
        let mut coord = vec![0u64; dims.len()];
        let elems = ArrayValue::try_from_elements((0..count).map(|flat| -> InterpretResult<_> {
            if flat > 0 {
                // The row-major successor: the last axis fastest.
                for (axis, extent) in coord.iter_mut().zip(&dims).rev() {
                    *axis += 1;
                    if *axis < *extent {
                        break;
                    }
                    *axis = 0;
                }
            }
            let mut point = values.clone();
            for (id, expr) in exprs.iter().enumerate() {
                if index_phase[id] {
                    point[id] = Some(view_node(
                        expr,
                        &point,
                        &params,
                        src_dims,
                        Some(&coord),
                        block,
                    )?);
                }
            }
            let source: Option<Vec<u64>> = index
                .iter()
                .zip(src_dims)
                .map(|(node, extent)| {
                    let at = point[*node as usize].expect("every node is computed");
                    u64::try_from(at).ok().filter(|at| at < extent)
                })
                .collect();
            match source {
                Some(source) => {
                    let offset: u64 = source.iter().zip(&src_strides).map(|(at, s)| at * s).sum();
                    src_elems.get(offset).cloned().ok_or_else(|| {
                        type_error(block, "tensor view: a source element is missing")
                    })
                }
                None => fill
                    .cloned()
                    .ok_or_else(|| ub(block, TENSOR_VIEW_OUT_OF_RANGE)),
            }
        }))?;
        Ok(InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Tensor { dims, elems },
        })
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Existing wire spellings with fallible actual inner emission.

use super::*;

pub(super) fn observed_write_inst<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    canonical: Option<Canonical<'_>>,
    inst: &InstG<NoExt>,
) -> R {
    if matches!(canonical, Some(Canonical::Ordinary(_))) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    buf.poll()?;
    match inst {
        InstG::BinOp { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 0)?;
            observed_write_binop(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *lhs)?;
            observed_write_projected_value_id(buf, canonical, *rhs)?;
        }
        InstG::UnOp { op, ty, operand } => {
            observed_write_u8(buf, 1)?;
            observed_write_unop(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *operand)?;
        }
        InstG::Overflow { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 2)?;
            observed_write_overflow_op(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *lhs)?;
            observed_write_projected_value_id(buf, canonical, *rhs)?;
        }
        InstG::ICmp { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 3)?;
            observed_write_icmp_op(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *lhs)?;
            observed_write_projected_value_id(buf, canonical, *rhs)?;
        }
        InstG::FCmp { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 4)?;
            observed_write_fcmp_op(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *lhs)?;
            observed_write_projected_value_id(buf, canonical, *rhs)?;
        }
        InstG::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            observed_write_u8(buf, 5)?;
            observed_write_cast_op(buf, op)?;
            observed_write_ty(buf, pool, src_ty)?;
            observed_write_ty(buf, pool, dst_ty)?;
            observed_write_projected_value_id(buf, canonical, *operand)?;
        }
        InstG::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            observed_write_u8(buf, 6)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_bool(buf, *volatile)?;
            observed_write_opt_u64(buf, *align)?;
        }
        InstG::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            observed_write_u8(buf, 7)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
            observed_write_bool(buf, *volatile)?;
            observed_write_opt_u64(buf, *align)?;
        }
        InstG::Drop { ty, ptr } => {
            // Crystal lane (wave-DS): tag 57, the first free instruction byte. Read-gated on
            // v47 (`DROP_INST_FORMAT_VERSION`), so a blob CLAIMING an older version that
            // carries it is malformed and refused rather than silently promoted -- the
            // discipline the v37 `Untagged` tag records.
            observed_write_u8(buf, 57)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        // v55 (amendment D): `Drop`'s payload, then `Invoke`'s successor
        // fields in `Invoke`'s order.
        InstG::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            observed_write_u8(buf, 68)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_block_id(buf, *normal_dest)?;
            observed_write_vec_value_id(buf, canonical, normal_args)?;
            observed_write_block_id(buf, *unwind_dest)?;
        }
        InstG::Alloca { ty, count, align } => {
            observed_write_u8(buf, 8)?;
            observed_write_ty(buf, pool, ty)?;
            match count {
                None => observed_write_u8(buf, 0)?,
                Some(v) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_projected_value_id(buf, canonical, *v)?;
                }
            }
            observed_write_opt_u64(buf, *align)?;
        }
        InstG::HeapAlloc {
            ty,
            count,
            align,
            origin,
        } => {
            observed_write_u8(buf, 49)?;
            observed_write_ty(buf, pool, ty)?;
            match count {
                None => observed_write_u8(buf, 0)?,
                Some(v) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_projected_value_id(buf, canonical, *v)?;
                }
            }
            observed_write_opt_u64(buf, *align)?;
            observed_write_u8(
                buf,
                match origin {
                    AllocOrigin::RustHeap => 0,
                    AllocOrigin::SwiftHeap => 1,
                    AllocOrigin::CMalloc => 2,
                    // v22: Clean Perceus RC heap. Old readers reject the blob
                    // at the header version check before seeing this byte.
                    AllocOrigin::CleanHeap => 3,
                },
            )?;
        }
        InstG::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            observed_write_u8(buf, 9)?;
            observed_write_ty(buf, pool, pointee_ty)?;
            observed_write_projected_value_id(buf, canonical, *base)?;
            observed_write_vec_value_id(buf, canonical, indices)?;
            observed_write_bool(buf, *inbounds)?;
        }
        InstG::AtomicLoad { ty, ptr, ordering } => {
            observed_write_u8(buf, 10)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_ordering(buf, ordering)?;
        }
        InstG::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            observed_write_u8(buf, 11)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
            observed_write_ordering(buf, ordering)?;
        }
        InstG::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            observed_write_u8(buf, 12)?;
            observed_write_atomic_rmw_op(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
            observed_write_ordering(buf, ordering)?;
        }
        InstG::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak,
        } => {
            // Crystal lane (D3): the strength is the TAG, not a trailing byte, so a strong
            // compare-exchange keeps tag 13 and its exact historical bytes. A weak one takes
            // tag 58, read-gated on v48: a blob CLAIMING an older version that carries it is
            // malformed and refused rather than silently read as strong -- which would delete
            // the spurious-failure executions the flag exists to keep.
            observed_write_u8(buf, if *weak { 58 } else { 13 })?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
            observed_write_projected_value_id(buf, canonical, *expected)?;
            observed_write_projected_value_id(buf, canonical, *desired)?;
            observed_write_ordering(buf, success)?;
            observed_write_ordering(buf, failure)?;
        }
        InstG::Fence { ordering } => {
            observed_write_u8(buf, 14)?;
            observed_write_ordering(buf, ordering)?;
        }
        InstG::Br { target, args } => {
            observed_write_u8(buf, 15)?;
            observed_write_block_id(buf, *target)?;
            observed_write_vec_value_id(buf, canonical, args)?;
        }
        InstG::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            observed_write_u8(buf, 16)?;
            observed_write_projected_value_id(buf, canonical, *cond)?;
            observed_write_block_id(buf, *then_target)?;
            observed_write_vec_value_id(buf, canonical, then_args)?;
            observed_write_block_id(buf, *else_target)?;
            observed_write_vec_value_id(buf, canonical, else_args)?;
        }
        InstG::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            observed_write_u8(buf, 17)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
            observed_write_block_id(buf, *default)?;
            observed_write_vec_value_id(buf, canonical, default_args)?;
            observed_write_count(buf, "Switch cases", cases.len())?;
            for sc in cases {
                buf.poll()?;
                observed_write_constant(buf, pool, &sc.value)?;
                observed_write_v32(buf, sc.target.0)?;
                observed_write_vec_value_id(buf, canonical, &sc.args)?;
            }
            // v15+: exhaustive-enum-unreachable flag; legacy modules default false.
            observed_write_bool(buf, *exhaustive_enum_unreachable)?;
        }
        InstG::Call { callee, args } => {
            observed_write_u8(buf, 18)?;
            observed_write_func_id(buf, *callee)?;
            observed_write_vec_value_id(buf, canonical, args)?;
        }
        InstG::CallCannotUnwind { callee, args } => {
            observed_write_u8(buf, 64)?;
            observed_write_func_id(buf, *callee)?;
            observed_write_vec_value_id(buf, canonical, args)?;
        }
        InstG::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            observed_write_u8(buf, 65)?;
            observed_write_projected_value_id(buf, canonical, *callee)?;
            observed_write_func_ty_id(buf, *sig)?;
            observed_write_vec_value_id(buf, canonical, args)?;
            observed_write_calling_conv(buf, calling_conv)?;
        }
        InstG::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            observed_write_u8(buf, 19)?;
            observed_write_projected_value_id(buf, canonical, *callee)?;
            observed_write_func_ty_id(buf, *sig)?;
            observed_write_vec_value_id(buf, canonical, args)?;
            // VERSION >= 12: indirect-call ABI. Read side defaults C on older.
            observed_write_calling_conv(buf, calling_conv)?;
        }
        InstG::Return { values } => {
            observed_write_u8(buf, 20)?;
            observed_write_vec_value_id(buf, canonical, values)?;
        }
        InstG::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            observed_write_u8(buf, 21)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *aggregate)?;
            observed_write_v32(buf, *field)?;
        }
        InstG::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            observed_write_u8(buf, 22)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *aggregate)?;
            observed_write_v32(buf, *field)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
        InstG::ExtractElement { ty, array, index } => {
            observed_write_u8(buf, 23)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *array)?;
            observed_write_projected_value_id(buf, canonical, *index)?;
        }
        InstG::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            observed_write_u8(buf, 24)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *array)?;
            observed_write_projected_value_id(buf, canonical, *index)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
        InstG::Const { ty, value } => {
            observed_write_u8(buf, 25)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_constant(buf, pool, value)?;
        }
        InstG::NullPtr => observed_write_u8(buf, 26)?,
        InstG::GlobalAddr { global } => {
            observed_write_u8(buf, 48)?;
            observed_write_v32(buf, global.index())?;
        }
        InstG::Undef { ty } => {
            observed_write_u8(buf, 27)?;
            observed_write_ty(buf, pool, ty)?;
        }
        InstG::Assume { cond } => {
            observed_write_u8(buf, 28)?;
            observed_write_projected_value_id(buf, canonical, *cond)?;
        }
        // v52 (plan item P): a kindless assert keeps tag 29 and its exact
        // historical bytes; a kinded one is tag 63, the condition, then the
        // kind (`observed_write_assert_kind`). One spelling per value: tag 63 never
        // carries `Unspecified` (the kind tag space has no byte for it).
        //
        // v54 (amendment P): a SITED assert of any kind is tag 66 — the
        // condition, a kind-presence byte (0 Unspecified, 1 a kind follows),
        // the kind, then the panic site (`observed_write_panic_site`). Tags 29 and 63
        // spell only siteless asserts, so each assert has one encoding.
        InstG::Assert {
            cond,
            kind,
            site: None,
        } if kind.is_unspecified() => {
            observed_write_u8(buf, 29)?;
            observed_write_projected_value_id(buf, canonical, *cond)?;
        }
        InstG::Assert {
            cond,
            kind,
            site: None,
        } => {
            observed_write_u8(buf, 63)?;
            observed_write_projected_value_id(buf, canonical, *cond)?;
            observed_write_assert_kind(buf, canonical, kind)?;
        }
        InstG::Assert {
            cond,
            kind,
            site: Some(site),
        } => {
            observed_write_u8(buf, 66)?;
            observed_write_sited_assert_payload(buf, canonical, *cond, kind, site)?;
        }
        // v54 (amendment P): tag 66's payload, then `Invoke`'s successor
        // fields in `Invoke`'s order.
        InstG::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            observed_write_u8(buf, 67)?;
            observed_write_sited_assert_payload(buf, canonical, *cond, kind, site)?;
            observed_write_block_id(buf, *normal_dest)?;
            observed_write_vec_value_id(buf, canonical, normal_args)?;
            observed_write_block_id(buf, *unwind_dest)?;
        }
        InstG::Unreachable => observed_write_u8(buf, 30)?,
        InstG::Copy { ty, operand } => {
            observed_write_u8(buf, 31)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *operand)?;
        }
        InstG::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            observed_write_u8(buf, 32)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *cond)?;
            observed_write_projected_value_id(buf, canonical, *then_val)?;
            observed_write_projected_value_id(buf, canonical, *else_val)?;
        }
        InstG::Borrow { ptr } => {
            observed_write_u8(buf, 33)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::BorrowMut { ptr } => {
            observed_write_u8(buf, 34)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::EndBorrow { borrow_ptr } => {
            observed_write_u8(buf, 35)?;
            observed_write_projected_value_id(buf, canonical, *borrow_ptr)?;
        }
        InstG::Retain { ptr } => {
            observed_write_u8(buf, 36)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::Release { ptr } => {
            observed_write_u8(buf, 37)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::IsUnique { ptr } => {
            observed_write_u8(buf, 38)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::Dealloc { ptr } => {
            observed_write_u8(buf, 39)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        // Binding frames (tags 40..=43)
        InstG::OpenFrame { def } => {
            observed_write_u8(buf, 40)?;
            observed_write_v32(buf, def.id.index())?;
            observed_write_str(buf, pool, &def.name)?;
            observed_write_count(buf, "BindingFrameDef.slots", def.slots.len())?;
            for slot in &def.slots {
                buf.poll()?;
                observed_write_str(buf, pool, &slot.name)?;
                observed_write_ty(buf, pool, &slot.ty)?;
            }
        }
        // Every `frame` below is an SSA handle, not the `BindingFrameId`
        // definition embedded by `OpenFrame`, so canonical projections remap it.
        InstG::BindSlot { frame, slot, value } => {
            observed_write_u8(buf, 41)?;
            observed_write_projected_value_id(buf, canonical, *frame)?;
            observed_write_v32(buf, *slot)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
        InstG::LoadSlot { frame, slot, ty } => {
            observed_write_u8(buf, 42)?;
            observed_write_projected_value_id(buf, canonical, *frame)?;
            observed_write_v32(buf, *slot)?;
            observed_write_ty(buf, pool, ty)?;
        }
        InstG::CloseFrame { frame } => {
            observed_write_u8(buf, 43)?;
            observed_write_projected_value_id(buf, canonical, *frame)?;
        }
        // Coroutine suspend (tag 50, v16+). New wire tags are never present in
        // pre-v16 blobs, so no read-side version gate is needed.
        InstG::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            observed_write_u8(buf, 50)?;
            observed_write_projected_value_id(buf, canonical, *frame)?;
            observed_write_v32(buf, *state_slot)?;
            observed_write_i128(buf, i128::from(*next_state))?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
        // Exception handling (tags 51..=53, v17+). New wire tags are never
        // present in pre-v17 blobs, so no read-side version gate is needed.
        InstG::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            observed_write_u8(buf, 51)?;
            observed_write_func_id(buf, *callee)?;
            observed_write_vec_value_id(buf, canonical, args)?;
            observed_write_block_id(buf, *normal_dest)?;
            observed_write_vec_value_id(buf, canonical, normal_args)?;
            observed_write_block_id(buf, *unwind_dest)?;
        }
        // v56 (amendment D, Part 2): `CallIndirect`'s tag-19 payload, then
        // `Invoke`'s successor fields in `Invoke`'s order.
        InstG::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            observed_write_u8(buf, 69)?;
            observed_write_projected_value_id(buf, canonical, *callee)?;
            observed_write_func_ty_id(buf, *sig)?;
            observed_write_vec_value_id(buf, canonical, args)?;
            observed_write_calling_conv(buf, calling_conv)?;
            observed_write_block_id(buf, *normal_dest)?;
            observed_write_vec_value_id(buf, canonical, normal_args)?;
            observed_write_block_id(buf, *unwind_dest)?;
        }
        InstG::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            observed_write_u8(buf, 52)?;
            observed_write_bool(buf, *is_cleanup)?;
            observed_write_count(
                buf,
                "LandingPad catch_type_indices",
                catch_type_indices.len(),
            )?;
            for idx in catch_type_indices {
                buf.poll()?;
                observed_write_v32(buf, *idx)?;
            }
        }
        InstG::Resume { exn } => {
            observed_write_u8(buf, 53)?;
            observed_write_projected_value_id(buf, canonical, *exn)?;
        }
        InstG::SeqMapAddK { ty, seq, k } => {
            observed_write_u8(buf, 54)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *seq)?;
            observed_write_u64(buf, *k)?;
        }
        InstG::SeqMapNot { ty, seq } => {
            observed_write_u8(buf, 55)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *seq)?;
        }
        InstG::SeqMap { ty, seq, fwd } => {
            // VERSION >= 21: general element-op loop (ty + seq + element FuncId).
            observed_write_u8(buf, 56)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *seq)?;
            observed_write_func_id(buf, *fwd)?;
        }
        // v50: `n` copies of one operand — the type carries `n`.
        InstG::ArraySplat { ty, value } => {
            observed_write_u8(buf, 59)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *value)?;
        }
        // v51 (INST wire batch, WS3.5): the aggregate type, the enum variant
        // as a presence byte plus a v32, then one operand per lane.
        InstG::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            observed_write_u8(buf, 60)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_opt_v32(buf, *variant)?;
            observed_write_vec_value_id(buf, canonical, fields)?;
        }
        InstG::MakeClosure { ty, func, captures } => {
            observed_write_u8(buf, 70)?;
            observed_write_v32(buf, ty.index())?;
            observed_write_func_id(buf, *func)?;
            observed_write_vec_value_id(buf, canonical, captures)?;
        }
        // v67 (tensor region): the result type, the operands in field order,
        // then the batch and the contracted axis-pair lists — byte for byte
        // the canonical writer's tag-71 spelling.
        InstG::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        } => {
            observed_write_u8(buf, 71)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *lhs)?;
            observed_write_projected_value_id(buf, canonical, *rhs)?;
            observed_write_axis_pairs(buf, "TensorContract batch pairs", batch)?;
            observed_write_axis_pairs(buf, "TensorContract contract pairs", contract)?;
        }
        // v68 (tensor map, reduce and view): byte for byte the canonical
        // writer's tag-72..=74 spellings.
        InstG::TensorMap { ty, args, body } => {
            observed_write_u8(buf, 72)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_vec_value_id(buf, canonical, args)?;
            observed_write_count(buf, "TensorMap body", body.len())?;
            for node in body {
                buf.poll()?;
                observed_write_tensor_map_node(buf, pool, node)?;
            }
        }
        InstG::TensorReduce {
            ty,
            src,
            op,
            axes,
            order,
        } => {
            observed_write_u8(buf, 73)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *src)?;
            observed_write_u8(buf, tensor_reduce_op_tag(*op))?;
            observed_write_v32_list(buf, "TensorReduce axes", axes)?;
            match order {
                crate::TensorReduceOrder::RowMajor => observed_write_u8(buf, 0)?,
            }
        }
        InstG::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        } => {
            observed_write_u8(buf, 74)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *src)?;
            observed_write_vec_value_id(buf, canonical, params)?;
            observed_write_count(buf, "TensorView exprs", exprs.len())?;
            for expr in exprs {
                buf.poll()?;
                observed_write_u8(buf, tensor_index_expr_tag(expr))?;
                match *expr {
                    crate::TensorIndexExpr::Lit(n) => observed_write_v64(buf, n)?,
                    crate::TensorIndexExpr::Param(k)
                    | crate::TensorIndexExpr::SrcExtent(k)
                    | crate::TensorIndexExpr::Coord(k) => observed_write_v32(buf, k)?,
                    crate::TensorIndexExpr::Add(a, b)
                    | crate::TensorIndexExpr::Sub(a, b)
                    | crate::TensorIndexExpr::Mul(a, b)
                    | crate::TensorIndexExpr::Div(a, b)
                    | crate::TensorIndexExpr::Rem(a, b)
                    | crate::TensorIndexExpr::Min(a, b)
                    | crate::TensorIndexExpr::Max(a, b) => {
                        observed_write_v32(buf, a)?;
                        observed_write_v32(buf, b)?;
                    }
                }
            }
            observed_write_v32_list(buf, "TensorView shape", shape)?;
            observed_write_v32_list(buf, "TensorView index", index)?;
            match fill {
                None => observed_write_u8(buf, 0)?,
                Some(fill) => {
                    observed_write_u8(buf, 1)?;
                    observed_write_projected_value_id(buf, canonical, *fill)?;
                }
            }
        }
        // v69 (tensor gather and scatter): byte for byte the canonical
        // writer's tag-75 and tag-76 spellings.
        InstG::TensorGather { ty, data, coords } => {
            observed_write_u8(buf, 75)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *data)?;
            observed_write_vec_value_id(buf, canonical, coords)?;
        }
        InstG::TensorScatter {
            ty,
            init,
            src,
            coords,
        } => {
            observed_write_u8(buf, 76)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_projected_value_id(buf, canonical, *init)?;
            observed_write_projected_value_id(buf, canonical, *src)?;
            observed_write_vec_value_id(buf, canonical, coords)?;
        }
        InstG::DialectOp(op) => {
            observed_write_u8(buf, 44)?;
            observed_write_dialect_inst(buf, pool, canonical, op)?;
        }
        InstG::PtrData { ptr_ty, ptr } => {
            observed_write_u8(buf, 45)?;
            observed_write_ty(buf, pool, ptr_ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            observed_write_u8(buf, 46)?;
            observed_write_ty(buf, pool, ptr_ty)?;
            observed_write_ty(buf, pool, metadata_ty)?;
            observed_write_projected_value_id(buf, canonical, *ptr)?;
        }
        InstG::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            observed_write_u8(buf, 47)?;
            observed_write_ty(buf, pool, ptr_ty)?;
            observed_write_ty(buf, pool, metadata_ty)?;
            observed_write_projected_value_id(buf, canonical, *data)?;
            observed_write_projected_value_id(buf, canonical, *metadata)?;
        }
        // v51 (INST wire batch, WS3.20): the three operands in field order,
        // then the memmove flag.
        InstG::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            observed_write_u8(buf, 61)?;
            observed_write_projected_value_id(buf, canonical, *dst)?;
            observed_write_projected_value_id(buf, canonical, *src)?;
            observed_write_projected_value_id(buf, canonical, *bytes)?;
            observed_write_bool(buf, *overlap)?;
        }
        // v51 (INST wire batch, WS3.20): the three operands in field order.
        InstG::MemSet { dst, byte, bytes } => {
            observed_write_u8(buf, 62)?;
            observed_write_projected_value_id(buf, canonical, *dst)?;
            observed_write_projected_value_id(buf, canonical, *byte)?;
            observed_write_projected_value_id(buf, canonical, *bytes)?;
        }
    }

    Ok(())
}

/// A tensor contraction's axis-pair list (v67), as `write_axis_pairs` spells
/// it: the count, then a `v32` left axis and a `v32` right axis per pair.
fn observed_write_axis_pairs<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    what: &'static str,
    pairs: &[(u32, u32)],
) -> R {
    buf.poll()?;
    observed_write_count(buf, what, pairs.len())?;
    for &(lhs, rhs) in pairs {
        buf.poll()?;
        observed_write_v32(buf, lhs)?;
        observed_write_v32(buf, rhs)?;
    }

    Ok(())
}

/// A v32 list (v68), as `write_v32_list` spells it: the count, then each item.
fn observed_write_v32_list<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    what: &'static str,
    items: &[u32],
) -> R {
    buf.poll()?;
    observed_write_count(buf, what, items.len())?;
    for &item in items {
        buf.poll()?;
        observed_write_v32(buf, item)?;
    }

    Ok(())
}

/// One tensor map node (v68), as `write_tensor_map_node` spells it.
fn observed_write_tensor_map_node<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    node: &crate::TensorMapNode<NoExt>,
) -> R {
    use crate::TensorMapNode as N;
    match node {
        N::BinOp { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 0)?;
            observed_write_binop(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_v32(buf, *lhs)?;
            observed_write_v32(buf, *rhs)?;
        }
        N::UnOp { op, ty, operand } => {
            observed_write_u8(buf, 1)?;
            observed_write_unop(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_v32(buf, *operand)?;
        }
        N::ICmp { op, ty, lhs, rhs } => {
            observed_write_u8(buf, 2)?;
            observed_write_icmp_op(buf, op)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_v32(buf, *lhs)?;
            observed_write_v32(buf, *rhs)?;
        }
        N::Select {
            ty,
            cond,
            then_lane,
            else_lane,
        } => {
            observed_write_u8(buf, 3)?;
            observed_write_ty(buf, pool, ty)?;
            observed_write_v32(buf, *cond)?;
            observed_write_v32(buf, *then_lane)?;
            observed_write_v32(buf, *else_lane)?;
        }
        N::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            observed_write_u8(buf, 4)?;
            observed_write_cast_op(buf, op)?;
            observed_write_ty(buf, pool, src_ty)?;
            observed_write_ty(buf, pool, dst_ty)?;
            observed_write_v32(buf, *operand)?;
        }
    }

    Ok(())
}

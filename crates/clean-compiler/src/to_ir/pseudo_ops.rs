// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pseudo-operation lowering for L5CNF → L5IR.
//!
//! Handles RC pseudo-ops (`_inc`, `_dec`, `_del`, `_setTag`), set pseudo-ops
//! (`_set`, `_uset`, `_sset`), reset/reuse pseudo-ops (`_reset`, `_reuse`),
//! and scalar field partitioning for constructor allocation.

use super::code::{lower_code, lower_let_value};
use super::state::ToIRState;
use super::types::name_to_ir_type;
use crate::error::CompilerError;
use crate::ir::{CtorInfo, IRArg, IRBody, IRExpr, IRType, VarId};
use crate::lcnf::{Arg, Code, LetDecl, LetValue};
use crate::rc::pseudo_op;
use clean_kernel::name::NameInner;
use clean_kernel::{Expr, ExprKind, FVarId, Name};

/// Convert an L5CNF LetDecl to IRBody.
pub(super) fn lower_let(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<IRBody, CompilerError> {
    // Check for RC pseudo-operations
    if is_rc_pseudo_op(&decl.value) {
        return lower_rc_op(decl, body, state);
    }

    // Check for set pseudo-operations
    if is_set_op(&decl.value) {
        return lower_set_op(decl, body, state);
    }

    // Check for reset/reuse pseudo-operations
    if is_reset_reuse_op(&decl.value) {
        return lower_reset_reuse_op(decl, body, state);
    }

    // C5b scalar-carrier CONSTRUCTION: a newtype-style constructor of a
    // scalar-repr inductive (`Char.mk`, `UIntN.ofBitVec`, `USize.ofBitVec`)
    // constructs the unboxed scalar itself, never a heap ctor.
    if let Some(lowered) = lower_scalar_carrier_ctor(decl, body, state)? {
        return Ok(lowered);
    }

    // R2 scalar-carrier CHAIN: `Fin.ofNat (2^w - 1) x` / `BitVec.ofNatLT w
    // n h` become the width-`w` scalar decode of their `Nat` operand, and
    // `BitVec.ofFin w f` over an already-scalar `f` is a pure alias — so the
    // downstream `UIntN.ofBitVec` sees a width-matched scalar carrier and
    // the C5b alias arm above claims it.
    if let Some(lowered) = lower_scalar_width_nat_decode(decl, body, state)? {
        return Ok(lowered);
    }
    if let Some(lowered) = lower_bitvec_of_fin_alias(decl, body, state)? {
        return Ok(lowered);
    }

    // Normal let binding
    let var_id = state.bind_var(decl.fvar_id);
    let (expr, ty) = lower_let_value(&decl.value, state)?;
    // Track variable types for scalar type inference in _sset. Part of #2123.
    state.record_var_type(var_id, ty.clone());
    // Track known compile-time Nat VALUES (R2 width evidence): literals, and
    // the value-preserving `OfNat.ofNat {Nat} (lit) (inst)` spelling the
    // elaborator threads width/modulus constants through (its runtime value
    // IS the literal operand). Pure bookkeeping — the emitted IR for these
    // bindings is unchanged.
    match &decl.value {
        LetValue::Lit(clean_kernel::Literal::Nat(n)) => {
            if let Some(value) = n.to_u64() {
                state.record_known_nat_value(var_id, value);
            }
        }
        LetValue::Const { name, args, .. }
            if name.to_string() == "OfNat.ofNat" && args.len() == 3 =>
        {
            if let Arg::FVar(lit_fvar) = &args[1] {
                if let Ok(IRArg::Var(lit_var)) = state.get_var(*lit_fvar) {
                    if let Some(value) = state.known_nat_value(lit_var) {
                        state.record_known_nat_value(var_id, value);
                    }
                }
            }
        }
        // `USize` platform-size width evidence: `System.Platform.numBits` is a
        // `Const`, so it carries no `known_nat_value`; mark the var so the
        // `BitVec.ofNatLT numBits n h` decode (the `USize.ofNatLT` carrier)
        // can target `USize`.
        LetValue::Const { name, .. } if name.to_string() == "System.Platform.numBits" => {
            state.record_numbits_var(var_id);
        }
        _ => {}
    }
    let rest = lower_code(body, state)?;

    // Fix #1993: For Ctor/Reuse with scalar fields, filter scalar args out
    // of the allocation call and generate SSet instructions to write them.
    // clean_alloc_ctor's varargs only consumes num_objects pointer fields;
    // scalar values must be written separately via typed setters.
    let (expr, rest) = split_scalar_ctor_args(var_id, expr, rest, state)?;

    Ok(IRBody::VDecl {
        var: var_id,
        ty,
        value: expr,
        rest: Box::new(rest),
    })
}

/// For Ctor/Reuse IR expressions with scalar fields, split the args into
/// object-only args (kept in the Ctor/Reuse) and scalar args (emitted as
/// SSet instructions chained before `rest`).
///
/// `clean_alloc_ctor`'s varargs only processes `num_objects` pointer fields.
/// Scalar values passed beyond that are silently ignored by the runtime.
/// This function generates SSet instructions so scalar values are written
/// to the correct byte offsets in the object's scalar data area.
///
/// Part of #1993.
fn split_scalar_ctor_args(
    ctor_var: VarId,
    expr: IRExpr,
    rest: IRBody,
    state: &ToIRState,
) -> Result<(IRExpr, IRBody), CompilerError> {
    Ok(match &expr {
        IRExpr::Ctor { info, args } if info.num_scalars > 0 && !info.field_types.is_empty() => {
            let (obj_args, sset_chain) = partition_ctor_fields(ctor_var, info, args, rest, state)?;
            let new_expr = IRExpr::Ctor {
                info: info.clone(),
                args: obj_args,
            };
            (new_expr, sset_chain)
        }
        IRExpr::Reuse { var, ctor, args }
            if ctor.num_scalars > 0 && !ctor.field_types.is_empty() =>
        {
            let (obj_args, sset_chain) = partition_ctor_fields(ctor_var, ctor, args, rest, state)?;
            let new_expr = IRExpr::Reuse {
                var: *var,
                ctor: ctor.clone(),
                args: obj_args,
            };
            (new_expr, sset_chain)
        }
        _ => (expr, rest),
    })
}

/// Partition constructor field args into object args and SSet instructions.
///
/// Returns (object_args, sset_chain) where:
/// - object_args: only the object-typed args (for clean_alloc_ctor varargs)
/// - sset_chain: SSet instructions for scalar fields, chained before `rest`
///
/// The byte offset for each scalar field in the SSet instruction is computed as:
///   sizeof(void*) * n + offset
/// where n = info.num_objects and offset = cumulative byte offset within
/// the scalar data area. This matches the Lean 4 IR convention.
fn partition_ctor_fields(
    ctor_var: VarId,
    info: &CtorInfo,
    args: &[IRArg],
    rest: IRBody,
    state: &ToIRState,
) -> Result<(Vec<IRArg>, IRBody), CompilerError> {
    let mut obj_args = Vec::new();
    // USize fields → (arg, usize_slot_idx) for USet generation
    let mut usize_fields: Vec<(IRArg, u32)> = Vec::new();
    // Non-USize scalar fields → (arg, ty, byte_offset) for SSet generation
    let mut scalar_fields: Vec<(IRArg, IRType, u32)> = Vec::new();
    let mut scalar_byte_offset: u32 = 0;
    let mut usize_slot_idx: u32 = 0;

    // HARD error in all profiles (never a debug_assert): the zip below pairs
    // `args[i]` with `field_types[i]`, so any length mismatch stores values
    // in the wrong field slots (and silently DROPS the surplus) — the
    // release-mode `Fin.ofNat` corruption. `lower_ctor_parts` builds the two
    // lists together (erased fields removed from both), so they are equal by
    // construction; this guard keeps any other producer honest.
    if args.len() != info.field_types.len() {
        return Err(CompilerError::CtorSpineMisaligned {
            ctor: info.name.clone(),
            args: args.len(),
            num_params: 0,
            num_fields: info.field_types.len(),
        });
    }

    for (arg, field_ty) in args.iter().zip(info.field_types.iter()) {
        if *field_ty == IRType::USize {
            // USize fields use USet, not SSet. USize occupies pointer-sized
            // slots after object pointers. Self-audit W1-1266 F1.
            usize_fields.push((arg.clone(), usize_slot_idx));
            usize_slot_idx += 1;
        } else if field_ty.scalar_byte_size() > 0 {
            // Non-USize scalar field — extract for SSet
            scalar_fields.push((arg.clone(), field_ty.clone(), scalar_byte_offset));
            scalar_byte_offset += field_ty.scalar_byte_size();
        } else {
            // Object field — keep in Ctor args
            obj_args.push(arg.clone());
        }
    }

    // If no scalar or USize fields found, return unchanged.
    if scalar_fields.is_empty() && usize_fields.is_empty() {
        return Ok((args.to_vec(), rest));
    }

    // FAIL-CLOSED (C4 containment): a scalar (or USize) field slot must be
    // fed by a value whose recorded L5IR type IS that scalar representation.
    // An object-typed value here would make the width-typed
    // `clean_ctor_set_uint*` store reinterpret a managed POINTER as the
    // field's bits: a silent miscompile in emit_c, an invalid-module refusal
    // in trust-ir. Refusing here (stage 2) keeps the mismatch out of every
    // backend and lets the per-decl compile probe demote the decl to an
    // extern fallback. (The newtype-style constructions of scalar-repr
    // inductives — `Char.mk`, `UIntN.ofBitVec` — are claimed upstream by
    // `lower_scalar_carrier_ctor` (C5b) and never reach this partition; this
    // guard keeps the genuinely unscalarizable residue refused.)
    // A var with NO recorded type keeps the historical fallback behavior
    // (hand-built IR in tests); scalar-width differences are left to the
    // backends' existing conventions.
    for (arg, _ty, byte_offset) in &scalar_fields {
        if let IRArg::Var(value_var) = arg {
            if let Some(vty) = state.get_var_type(*value_var) {
                if !vty.is_scalar() {
                    return Err(CompilerError::BoxedValueInScalarField {
                        ctor: info.name.clone(),
                        offset: *byte_offset,
                        value_ty: format!("{vty:?}"),
                    });
                }
            }
        }
    }
    for (arg, slot_idx) in &usize_fields {
        if let IRArg::Var(value_var) = arg {
            if let Some(vty) = state.get_var_type(*value_var) {
                if !vty.is_scalar() {
                    return Err(CompilerError::BoxedValueInScalarField {
                        ctor: info.name.clone(),
                        offset: *slot_idx,
                        value_ty: format!("{vty:?}"),
                    });
                }
            }
        }
    }

    // SSet n must account for both object AND USize pointer-sized slots,
    // matching the SProj convention: n = num_objects + num_usizes.
    // Self-audit W1-1266 F1.
    let num_usizes = info
        .field_types
        .iter()
        .filter(|t| **t == IRType::USize)
        .count() as u32;
    let sset_n = info.num_objects + num_usizes;

    // Build instruction chain from last to first (each wraps the rest).
    let mut chain = rest;

    // SSet for non-USize scalars
    for (arg, ty, byte_offset) in scalar_fields.into_iter().rev() {
        if let IRArg::Var(value_var) = arg {
            chain = IRBody::SSet {
                var: ctor_var,
                n: sset_n,
                offset: byte_offset,
                value: value_var,
                ty,
                rest: Box::new(chain),
            };
        }
    }

    // USet for USize fields (idx = num_objects + usize_slot_index)
    for (arg, slot_idx) in usize_fields.into_iter().rev() {
        if let IRArg::Var(value_var) = arg {
            chain = IRBody::USet {
                var: ctor_var,
                idx: info.num_objects + slot_idx,
                value: value_var,
                rest: Box::new(chain),
            };
        }
    }

    Ok((obj_args, chain))
}

/// The unboxed scalar type a newtype-style constructor CONSTRUCTS, keyed by
/// the ctor's parent inductive (its name prefix): `Char.mk` builds a
/// `UInt32`, `UIntN.ofBitVec` / `USize.ofBitVec` build the matching width.
///
/// Only the integer-scalar carriers participate (the C5b chain family).
/// `Bool` ctors never reach to_ir (rewritten to shims by `to_mono`) and
/// `Float` has no carrier-ctor chain, so both stay on the generic path.
/// The caller must have already established that `ctor_name` IS a registered
/// constructor (`lookup_ctor_meta`), so the prefix is its parent inductive.
///
/// `pub(crate)` so the L5CNF lowering (`to_lcnf::lower::eta_expand_partial_ctor`)
/// can gate on the SAME scalar-carrier recognition: a partially-applied
/// scalar-carrier ctor must NOT be eta-expanded (that would feed its carrier in
/// through a fresh Object-typed field binder, tripping the C5b
/// `ScalarCarrierObjectCarrier` refusal below).
pub(crate) fn scalar_carrier_target(ctor_name: &Name) -> Option<IRType> {
    let NameInner::Str(prefix, _) = ctor_name.inner() else {
        return None;
    };
    let ty = name_to_ir_type(prefix);
    matches!(
        ty,
        IRType::UInt8 | IRType::UInt16 | IRType::UInt32 | IRType::UInt64 | IRType::USize
    )
    .then_some(ty)
}

/// C5b scalar-carrier CONSTRUCTION (stage 2, the dual of the C2 carrier
/// PROJECTION in `emit_trust_ir` / `emit_c`): lower a newtype-style ctor of a
/// scalar-repr inductive to the scalar itself instead of a heap allocation.
///
/// The runtime convention (pinned by the emitters' projection direction) is
/// that a `Char` / `UIntN` value IS its unboxed integer carrier: `Char.val`
/// out of a `U32` is the identity. Construction must be the exact dual, so
/// for the ctor's single carrier field:
///
/// * carrier already recorded at the TARGET scalar type → pure renaming: the
///   ctor result is ALIASED to the carrier value (`Char.mk v h` = `v`), no
///   instruction emitted;
/// * carrier recorded as an OBJECT → hard refusal
///   ([`CompilerError::ScalarCarrierObjectCarrier`]). An earlier revision
///   emitted `IRExpr::Unbox { ty: target }` here on the assumption that the
///   object form of the carrier is always the tagged-`Nat` immediate. That
///   assumption is unfounded: `IRType::Object` cannot distinguish a tagged
///   immediate from a heap ctor pointer, and the real `Char.ofNat` chain
///   feeds this ctor `BitVec.ofNatLT`'s result — a HEAP `BitVec.ofFin` ctor
///   (which since the spine-alignment fix correctly stores its `Fin`, not a
///   scalar). Every runtime route `IRExpr::Unbox` can lower to decodes only
///   the boxed-SCALAR convention, never a ctor chain: `emit_c` /
///   `emit_trust_ir(ExternCalls)` route it to `clean_unbox` (a raw
///   `ptr >> 1` tag shift — garbage on a heap pointer), `clean_unbox_uint32`
///   (tag-checked, but the heap branch reads `*(uint32_t*)o->fields` — the
///   low half of the `Fin` POINTER), or `clean_unbox_uint64` (unconditional
///   field deref). With no faithful route the construction must refuse, and
///   the generic ctor path is no escape hatch either — it would heap-box a
///   value whose other consumers (the C2 projections, scalar arithmetic)
///   assume the unboxed-scalar representation. Refusing here keeps the
///   per-decl compile probe demoting the decl to an extern boundary.
///
/// Non-carrier fields of such a ctor are proof-class by construction (the
/// inductive's runtime representation is the scalar — `Char.valid`), so they
/// are dropped from the construction; the emitters already synthesize an
/// arbitrary boxed value when one is projected back out.
///
/// FAIL-CLOSED: any other shape returns `Ok(None)` and falls through to the
/// generic ctor path, where the spine-alignment guard
/// (`CtorSpineMisaligned`) and the C4 `BoxedValueInScalarField` guard still
/// refuse the unfaithful cases — this function only claims constructions
/// whose carrier is affirmatively at the target scalar width.
fn lower_scalar_carrier_ctor(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<Option<IRBody>, CompilerError> {
    let (name, args) = match &decl.value {
        LetValue::Const { name, args, .. } | LetValue::Ctor { name, args, .. } => (name, args),
        _ => return Ok(None),
    };
    let Some(meta) = state.lookup_ctor_meta(name) else {
        return Ok(None);
    };
    let Some(target) = scalar_carrier_target(name) else {
        return Ok(None);
    };

    // Align the spine with the ctor's field types: drop the leading
    // `num_params` inductive-parameter args (the same discipline as
    // `ctor_field_args` — value-level params like `Fin.mk`'s `n` included).
    // A misaligned spine falls through to the generic path, whose
    // `CtorSpineMisaligned` guard refuses it with the canonical error.
    let num_params = meta.num_params as usize;
    if args.len() != num_params + meta.field_types.len() {
        return Ok(None);
    }
    let field_args: Vec<&Arg> = args[num_params..].iter().collect();

    // The carrier field: the unique scalar field, which must be the target
    // width (`Char.mk`'s `val : UInt32`); a fieldless or multi-scalar shape
    // has no single carrier. A single all-object field (`UIntN.ofBitVec`'s
    // BitVec) is the carrier in its boxed form.
    let scalar_positions: Vec<usize> = meta
        .field_types
        .iter()
        .enumerate()
        .filter(|(_, t)| t.is_scalar())
        .map(|(i, _)| i)
        .collect();
    let carrier_idx = match scalar_positions.as_slice() {
        [i] if meta.field_types[*i] == target => *i,
        [] if meta.field_types.len() == 1 => 0,
        _ => return Ok(None),
    };

    let Arg::FVar(carrier_fvar) = field_args[carrier_idx] else {
        return Ok(None);
    };
    let IRArg::Var(carrier_var) = state.get_var(*carrier_fvar)? else {
        // Erased carrier: genuinely unscalarizable — generic path.
        return Ok(None);
    };

    match state.get_var_type(carrier_var) {
        Some(ty) if *ty == target => {
            // Identity: the construction is pure renaming, no IR emitted.
            state.bind_alias(decl.fvar_id, IRArg::Var(carrier_var));
            Ok(Some(lower_code(body, state)?))
        }
        // An object-typed carrier has NO affirmative boxed-scalar evidence:
        // it may be a heap ctor (`BitVec.ofFin`), and no runtime unbox route
        // decodes that — see the function doc. Hard refusal, not `Ok(None)`:
        // the generic path would silently heap-box a value whose consumers
        // assume the unboxed-scalar representation.
        Some(ty @ (IRType::Object | IRType::TObject)) => {
            Err(CompilerError::ScalarCarrierObjectCarrier {
                ctor: name.clone(),
                carrier_ty: format!("{ty:?}"),
            })
        }
        // Unknown or width-mismatched carrier: generic path (guard applies).
        _ => Ok(None),
    }
}

/// The scalar type whose value set an exact all-ones `Nat` modulus spans:
/// `Fin.ofNat m x` computes `x % (m + 1)`, so `m = 2^w - 1` makes the result
/// affirmatively `< 2^w` — decodable at width `w`.
///
/// Width 64 (`UInt64`, modulus `2^64 - 1`) is now included: since the
/// tagged-or-heap `clean_unbox_uint64` fix both emitters decode the tagged
/// `Nat` carrier faithfully (a small value is `(v << 1) | 1`, a large one the
/// `clean_box_uint64` heap payload). The value is exact: this runtime's `Nat`
/// is universally the tagged immediate capped below `2^63`, so
/// `x % 2^64 = x < 2^63` round-trips the decode with no truncation. USize
/// (platform-size) is handled by the `System.Platform.numBits` sentinel in
/// [`lower_scalar_width_nat_decode`], not by this literal-modulus table.
fn scalar_type_of_all_ones_modulus(m: u64) -> Option<IRType> {
    match m {
        0xFF => Some(IRType::UInt8),
        0xFFFF => Some(IRType::UInt16),
        0xFFFF_FFFF => Some(IRType::UInt32),
        0xFFFF_FFFF_FFFF_FFFF => Some(IRType::UInt64),
        _ => None,
    }
}

/// The scalar type of an exact bit WIDTH operand (`BitVec.ofNatLT w n h`).
/// Widths 8/16/32/64 (the `UIntN` family); the tagged-or-heap
/// `clean_unbox_uint64` fix brought 64 into range (see
/// [`scalar_type_of_all_ones_modulus`]). Platform-size `USize` is NOT here —
/// its width is `System.Platform.numBits` (a `Const`, never a literal), so it
/// is recognized by the sentinel in [`lower_scalar_width_nat_decode`].
fn scalar_type_of_width(w: u64) -> Option<IRType> {
    match w {
        8 => Some(IRType::UInt8),
        16 => Some(IRType::UInt16),
        32 => Some(IRType::UInt32),
        64 => Some(IRType::UInt64),
        _ => None,
    }
}

/// R2 scalar-carrier chain, step 1 — the `Nat -> scalar` DECODE: lower
/// `Fin.ofNat (2^w - 1) x` and `BitVec.ofNatLT w n h` (w in {8, 16, 32}) to
/// `Unbox {{ ty: U<w> }}` of the `Nat` operand instead of a runtime call.
///
/// Faithfulness rests on two facts, both affirmative:
///
/// * **Value bound.** `Fin.ofNat m x : Fin (m+1)` is `x % (m+1)` — with the
///   compile-time-known modulus `m = 2^w - 1` the value is `< 2^w` by
///   construction (the width evidence is the KNOWN literal, never the type).
///   `BitVec.ofNatLT w n h` carries the kernel-checked proof `n < 2^w` (and
///   the runtime cannot even represent a `Nat >= 2^63`, see below).
/// * **Representation.** This runtime's `Nat` is UNIVERSALLY the tagged
///   immediate `(v << 1) | 1`: every `Nat` shim (`l_Nat_add/sub/mul/div/mod`)
///   both consumes and produces via `clean_box`/`clean_unbox`, and literals
///   box the same way — there is no bignum path, so payloads are capped
///   below `2^63`. The `Unbox` routes for widths 8/16/32 decode exactly
///   this: `clean_unbox` (tag shift) + C/trust-ir truncation for 8/16,
///   tag-checked `clean_unbox_uint32` for 32 — and the truncation IS the
///   `% 2^w` the `Fin.ofNat` semantics require.
///
/// The replaced call is PURE (it computed the same value boxed), so dropping
/// it is behavior-preserving; the RC pseudo-ops the LCNF stage attached to
/// the (formerly object-typed) result land on a now-scalar var and are
/// dropped by the boxing pass's authoritative scalar-RC rule
/// (`boxing::visit`). Escaping uses of the scalar in object positions are
/// re-boxed by the boxing pass as the SAME tagged immediate a boxed
/// `Fin`/`Nat` is, so consumers beyond the `UIntN.ofBitVec` chain stay
/// faithful too.
///
/// FAIL-CLOSED: any other shape — unknown/mismatched modulus or width,
/// erased operands, a constructor spelling, an already-scalar operand —
/// returns `Ok(None)` and keeps the generic call path (where the C5b
/// object-carrier refusal still guards the chain's end).
fn lower_scalar_width_nat_decode(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<Option<IRBody>, CompilerError> {
    let LetValue::Const { name, args, .. } = &decl.value else {
        return Ok(None);
    };
    // Constructor applications are never decode sites.
    if state.lookup_ctor_meta(name).is_some() {
        return Ok(None);
    }
    let known_value_of = |state: &ToIRState, arg: &Arg| -> Option<u64> {
        let Arg::FVar(fvar) = arg else { return None };
        let Ok(IRArg::Var(var)) = state.get_var(*fvar) else {
            return None;
        };
        state.known_nat_value(var)
    };
    let is_numbits_of = |state: &ToIRState, arg: &Arg| -> bool {
        let Arg::FVar(fvar) = arg else { return false };
        let Ok(IRArg::Var(var)) = state.get_var(*fvar) else {
            return false;
        };
        state.is_numbits_var(var)
    };
    let (target, nat_arg) = match name.to_string().as_str() {
        // Fin.ofNat (m) (x) : Fin (m+1) — value = x % (m+1).
        "Fin.ofNat" if args.len() == 2 => {
            let Some(m) = known_value_of(state, &args[0]) else {
                return Ok(None);
            };
            let Some(target) = scalar_type_of_all_ones_modulus(m) else {
                return Ok(None);
            };
            (target, &args[1])
        }
        // BitVec.ofNatLT (w) (n) (h) : BitVec w — value = n, kernel-bounded.
        "BitVec.ofNatLT" if args.len() == 3 => {
            let target = if let Some(w) = known_value_of(state, &args[0]) {
                let Some(t) = scalar_type_of_width(w) else {
                    return Ok(None);
                };
                t
            } else if is_numbits_of(state, &args[0]) {
                // `BitVec System.Platform.numBits` IS `USize` — the platform-
                // size carrier (the `USize.ofNatLT` chain). `n` is a tagged
                // `Nat < 2^63`, decoded through the tagged-or-heap USize unbox.
                IRType::USize
            } else {
                return Ok(None);
            };
            (target, &args[1])
        }
        _ => return Ok(None),
    };
    let Arg::FVar(nat_fvar) = nat_arg else {
        return Ok(None);
    };
    let IRArg::Var(nat_var) = state.get_var(*nat_fvar)? else {
        return Ok(None);
    };
    // The operand must be (potentially) boxed: decoding a var already
    // recorded at a scalar type would tag-shift a raw integer.
    if state.get_var_type(nat_var).is_some_and(IRType::is_scalar) {
        return Ok(None);
    }

    let var_id = state.bind_var(decl.fvar_id);
    state.record_var_type(var_id, target.clone());
    let rest = lower_code(body, state)?;
    Ok(Some(IRBody::VDecl {
        var: var_id,
        ty: target.clone(),
        value: IRExpr::Unbox {
            ty: target,
            arg: IRArg::Var(nat_var),
        },
        rest: Box::new(rest),
    }))
}

/// R2 scalar-carrier chain, step 2 — `BitVec.ofFin w f` over an
/// already-scalar `f` is a PURE ALIAS (a `BitVec`'s runtime value IS its
/// `Fin`), so the decoded scalar flows through to the `UIntN.ofBitVec`
/// construction, whose existing C5b width-matched alias arm then claims it.
///
/// Alias-only, by the C5b discipline: claimed ONLY when the single `Fin`
/// field is AFFIRMATIVELY recorded at a scalar width (i.e. it came out of
/// [`lower_scalar_width_nat_decode`] or an equivalent scalar producer) — and
/// when the ctor's width parameter is compile-time known it must MATCH the
/// field's width. Every other `BitVec.ofFin` (the whole boxed `BitVec`
/// world) keeps today's heap-constructor path unchanged; there is no
/// object-carrier unboxing here and no hard refusal.
fn lower_bitvec_of_fin_alias(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<Option<IRBody>, CompilerError> {
    let (name, args) = match &decl.value {
        LetValue::Const { name, args, .. } | LetValue::Ctor { name, args, .. } => (name, args),
        _ => return Ok(None),
    };
    if name.to_string() != "BitVec.ofFin" {
        return Ok(None);
    }
    let Some(meta) = state.lookup_ctor_meta(name) else {
        return Ok(None);
    };
    // Spine: `num_params` leading parameter args (the width `w` — a
    // VALUE-level param the kernel spelling passes), then the single field.
    let num_params = meta.num_params as usize;
    if meta.field_types.len() != 1 || args.len() != num_params + 1 {
        return Ok(None);
    }
    let Arg::FVar(fin_fvar) = &args[num_params] else {
        return Ok(None);
    };
    let Ok(IRArg::Var(fin_var)) = state.get_var(*fin_fvar) else {
        return Ok(None);
    };
    let fin_width = match state.get_var_type(fin_var) {
        Some(IRType::UInt8) => 8u64,
        Some(IRType::UInt16) => 16,
        Some(IRType::UInt32) => 32,
        // Anything not affirmatively scalar-decoded (the boxed BitVec world)
        // keeps the generic heap-constructor path.
        _ => return Ok(None),
    };
    // Width-match when the width parameter's value is known; a mismatch is
    // ill-typed upstream, but decline rather than trust.
    if let Some(Arg::FVar(w_fvar)) = (num_params > 0).then(|| &args[0]) {
        if let Ok(IRArg::Var(w_var)) = state.get_var(*w_fvar) {
            if let Some(w) = state.known_nat_value(w_var) {
                if w != fin_width {
                    return Ok(None);
                }
            }
        }
    }

    state.bind_alias(decl.fvar_id, IRArg::Var(fin_var));
    Ok(Some(lower_code(body, state)?))
}

/// Check if a LetValue is an RC pseudo-operation.
fn is_rc_pseudo_op(value: &LetValue) -> bool {
    if let LetValue::Const { name, .. } = value {
        let s = name.to_string();
        s == pseudo_op::INC || s == pseudo_op::DEC || s == pseudo_op::DEL || s == pseudo_op::SET_TAG
    } else {
        false
    }
}

/// Check if a LetValue is a reset/reuse pseudo-operation.
fn is_reset_reuse_op(value: &LetValue) -> bool {
    if let LetValue::Const { name, .. } = value {
        let s = name.to_string();
        s == pseudo_op::RESET || s == pseudo_op::REUSE
    } else {
        false
    }
}

/// Check if a LetValue is a set pseudo-operation.
/// Matches `_set` (object field), `_uset` (USize), `_sset` (other scalar).
/// Part of #1995.
fn is_set_op(value: &LetValue) -> bool {
    if let LetValue::Const { name, .. } = value {
        let s = name.to_string();
        s == pseudo_op::SET || s == pseudo_op::USET || s == pseudo_op::SSET
    } else {
        false
    }
}

/// Lower an RC pseudo-operation to real IR.
fn lower_rc_op(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<IRBody, CompilerError> {
    let LetValue::Const { name, args, .. } = &decl.value else {
        return Err(CompilerError::MalformedPseudoOp {
            op: decl.name.clone(),
            detail: "RC pseudo-op lowering requires LetValue::Const",
        });
    };

    let s = name.to_string();
    if s == pseudo_op::INC {
        let fvar = expect_fvar_arg(args, 0, name, "expected _inc(x)")?;
        let var = require_runtime_var(state, fvar, name, "_inc target lowered to erased")?;
        let rest = lower_code(body, state)?;
        Ok(IRBody::Inc {
            var,
            n: 1,
            rest: Box::new(rest),
        })
    } else if s == pseudo_op::DEC || s == pseudo_op::DEL {
        let fvar = expect_fvar_arg(args, 0, name, "expected one runtime operand")?;
        let var = require_runtime_var(state, fvar, name, "_dec/_del target lowered to erased")?;
        let rest = lower_code(body, state)?;
        Ok(IRBody::Dec {
            var,
            rest: Box::new(rest),
        })
    } else if s == pseudo_op::SET_TAG {
        let obj_fvar = expect_fvar_arg(args, 0, name, "expected _setTag(obj, ctor)")?;
        let var = require_runtime_var(state, obj_fvar, name, "_setTag target lowered to erased")?;
        let ctor = expect_ctor_name_arg(args, 1, name)?;
        let tag = state
            .lookup_ctor_meta(&ctor)
            .map(|meta| meta.tag)
            .ok_or_else(|| CompilerError::UnsupportedSetTagLowering { ctor: ctor.clone() })?;
        let rest = lower_code(body, state)?;
        Ok(IRBody::SetTag {
            var,
            tag,
            rest: Box::new(rest),
        })
    } else {
        Err(CompilerError::MalformedPseudoOp {
            op: name.clone(),
            detail: "unsupported RC pseudo-op",
        })
    }
}

/// Lower a set pseudo-operation to real IR.
///
/// - `_set(obj, idx, val)` → IRBody::Set (object pointer field)
/// - `_uset(obj, idx, val)` → IRBody::USet (USize scalar field)
/// - `_sset(obj, n, offset, val)` → IRBody::SSet (other scalar field)
///
/// Part of #1995: previously only `_set` was handled, so scalar mutations via
/// `_uset`/`_sset` from reset-reuse would silently fall through.
fn lower_set_op(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<IRBody, CompilerError> {
    let LetValue::Const { name, args, .. } = &decl.value else {
        return Err(CompilerError::MalformedPseudoOp {
            op: decl.name.clone(),
            detail: "set pseudo-op lowering requires LetValue::Const",
        });
    };

    let s = name.to_string();
    if s == pseudo_op::SET {
        let obj_fvar = expect_fvar_arg(args, 0, name, "expected _set(obj, idx, val)")?;
        let idx = expect_index_arg(args, 1, name, "expected object field index")?;
        let val_fvar = expect_fvar_arg(args, 2, name, "expected _set value fvar")?;
        let var = require_runtime_var(state, obj_fvar, name, "_set target lowered to erased")?;
        let value = require_runtime_var(state, val_fvar, name, "_set value lowered to erased")?;
        let rest = lower_code(body, state)?;
        Ok(IRBody::Set {
            var,
            idx,
            value,
            rest: Box::new(rest),
        })
    } else if s == pseudo_op::USET {
        let obj_fvar = expect_fvar_arg(args, 0, name, "expected _uset(obj, idx, val)")?;
        let idx = expect_index_arg(args, 1, name, "expected usize field index")?;
        let val_fvar = expect_fvar_arg(args, 2, name, "expected _uset value fvar")?;
        let var = require_runtime_var(state, obj_fvar, name, "_uset target lowered to erased")?;
        let value = require_runtime_var(state, val_fvar, name, "_uset value lowered to erased")?;
        let rest = lower_code(body, state)?;
        Ok(IRBody::USet {
            var,
            idx,
            value,
            rest: Box::new(rest),
        })
    } else if s == pseudo_op::SSET {
        let obj_fvar = expect_fvar_arg(args, 0, name, "expected _sset(obj, n, offset, val)")?;
        let n = expect_index_arg(args, 1, name, "expected pointer-slot count")?;
        let offset = expect_index_arg(args, 2, name, "expected scalar byte offset")?;
        let val_fvar = expect_fvar_arg(args, 3, name, "expected _sset value fvar")?;
        let var = require_runtime_var(state, obj_fvar, name, "_sset target lowered to erased")?;
        let value = require_runtime_var(state, val_fvar, name, "_sset value lowered to erased")?;
        let rest = lower_code(body, state)?;
        let ty = state
            .get_var_type(value)
            .filter(|t| t.is_scalar())
            .cloned()
            .unwrap_or(IRType::UInt64);
        Ok(IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest: Box::new(rest),
        })
    } else {
        Err(CompilerError::MalformedPseudoOp {
            op: name.clone(),
            detail: "unsupported set pseudo-op",
        })
    }
}

/// Lower a reset/reuse pseudo-operation to real IR.
fn lower_reset_reuse_op(
    decl: &LetDecl,
    body: &Code,
    state: &mut ToIRState,
) -> Result<IRBody, CompilerError> {
    let LetValue::Const { name, args, .. } = &decl.value else {
        return Err(CompilerError::MalformedPseudoOp {
            op: decl.name.clone(),
            detail: "reset/reuse pseudo-op lowering requires LetValue::Const",
        });
    };

    let s = name.to_string();
    if s == pseudo_op::RESET {
        let fvar = expect_fvar_arg(args, 0, name, "expected _reset(x)")?;
        let var = require_runtime_var(state, fvar, name, "_reset target lowered to erased")?;
        let result_var = state.bind_var(decl.fvar_id);
        let rest = lower_code(body, state)?;
        Ok(IRBody::VDecl {
            var: result_var,
            ty: IRType::Object,
            value: IRExpr::Reset(var),
            rest: Box::new(rest),
        })
    } else if s == pseudo_op::REUSE {
        Err(CompilerError::MalformedPseudoOp {
            op: name.clone(),
            detail: "_reuse pseudo-op should be normalized into LetValue::Reuse before to_ir",
        })
    } else {
        Err(CompilerError::MalformedPseudoOp {
            op: name.clone(),
            detail: "unsupported reset/reuse pseudo-op",
        })
    }
}

fn expect_fvar_arg(
    args: &[Arg],
    index: usize,
    op: &Name,
    detail: &'static str,
) -> Result<FVarId, CompilerError> {
    match args.get(index) {
        Some(Arg::FVar(fvar)) => Ok(*fvar),
        _ => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}

fn expect_index_arg(
    args: &[Arg],
    index: usize,
    op: &Name,
    detail: &'static str,
) -> Result<u32, CompilerError> {
    match args.get(index) {
        Some(Arg::Index(idx)) => Ok(*idx),
        _ => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}

fn expect_ctor_name_arg(args: &[Arg], index: usize, op: &Name) -> Result<Name, CompilerError> {
    let Some(Arg::Type(expr)) = args.get(index) else {
        return Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail: "expected constructor type argument",
        });
    };
    ctor_name_from_expr(expr).ok_or_else(|| CompilerError::MalformedPseudoOp {
        op: op.clone(),
        detail: "constructor type argument must be a constant head",
    })
}

fn ctor_name_from_expr(expr: &Expr) -> Option<Name> {
    match expr.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

fn require_runtime_var(
    state: &ToIRState,
    fvar: FVarId,
    op: &Name,
    detail: &'static str,
) -> Result<VarId, CompilerError> {
    match state.get_var(fvar)? {
        IRArg::Var(var) => Ok(var),
        IRArg::Erased => Err(CompilerError::MalformedPseudoOp {
            op: op.clone(),
            detail,
        }),
    }
}

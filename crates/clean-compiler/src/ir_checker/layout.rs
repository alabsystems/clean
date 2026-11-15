// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rule C1 at the runtime header's widths.
//!
//! Pinned Lean's IR checker (`Checker.lean`@v4.30.0-rc2:137-141) refuses a
//! reference constructor whose tag exceeds `LeanMaxCtorTag` (243), more than
//! 256 object fields, and more than 1024 scalar bytes. Clean's object header
//! (`clean_runtime.h`, `clean_obj_header`) keeps the tag, `num_objs` and
//! `scalar_sz` in one byte each. A shape past a byte was silently truncated:
//! 256 object fields allocated 0 slots and then took 256 pointer writes, and
//! 32 `UInt64` fields allocated a 0-byte scalar area. Each such shape is
//! refused here by name, and the runtime's allocators panic on them as
//! defence in depth.
//!
//! A boxed (nullary) constructor keeps its tag in the pointer bits, not in a
//! header byte, and every lane reads it at 32 bits (the header's
//! `clean_obj_tag`, the trust-cg lane's `U32` import, the Rust runtime's
//! `obj_tag`), so it takes only the general `MAX_CTOR_TAG` bound: an enum of
//! 300 constructors is accepted, as pinned Lean accepts it.
//!
//! Every door that emits code from the boxed declarations runs this checker
//! first: the C lane (`emit_c_with_config`, `check_ir: true`, the path
//! `clean run` and `clean compile --emit c` take), the Rust lane
//! (`emit_rust_with_config`), and every trust-ir door (`clean compile --emit
//! trustir | trustir-bin | obj` and `clean run --backend trust-cg`), which
//! lowers through `compile_lcnf_to_trust_ir_with_report` or its carrier-export
//! twin. The Rust-ABI carrier lowering (`rust_abi::compile`) does not run it;
//! its emitter (`emit_trust_ir_carrier.rs`) refuses every constructor other
//! than `Bool`'s, so none of these shapes reaches it.

use super::{IRError, MAX_CTOR_OBJECT_FIELDS, MAX_CTOR_SCALAR_BYTES, MAX_REF_CTOR_TAG};
use crate::ir::CtorInfo;

/// Where a constructor's value lives at run time, which decides its tag bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CtorCell {
    /// Decided by the constructor's shape, as every emitter decides it
    /// (`emit_c`, `emit_rust`, `emit_trust_ir`): with no object field and no
    /// scalar byte it is a boxed scalar (`clean_box(tag)`), otherwise a heap
    /// cell (`clean_alloc_ctor`). Lean's `CtorInfo.isRef` answers the same
    /// question over a different layout: Clean keeps an object slot for type
    /// and proof fields, which Lean's IR drops (`to_ir/types.rs`), so a
    /// constructor Lean boxes can be a heap cell here and take the heap tag
    /// bound (`docs/DECISIONS.md` R39).
    ByShape,
    /// Always a heap cell: `reuse` writes the tag into a header
    /// (`clean_reuse` never boxes).
    Heap,
}

/// Check a constructor's tag, object-field count and scalar area against
/// the widths the runtime stores and reads them at.
pub(super) fn check_ctor_layout(info: &CtorInfo, cell: CtorCell) -> Result<(), IRError> {
    let scalar_bytes = info.scalar_size();
    let heap = cell == CtorCell::Heap || info.num_objects > 0 || scalar_bytes > 0;
    if heap && info.tag > MAX_REF_CTOR_TAG {
        return Err(IRError::RefCtorTagTooLarge {
            name: info.name.clone(),
            tag: info.tag,
            max: MAX_REF_CTOR_TAG,
        });
    }
    if info.num_objects > MAX_CTOR_OBJECT_FIELDS {
        return Err(IRError::CtorTooManyObjectFields {
            name: info.name.clone(),
            count: info.num_objects,
            max: MAX_CTOR_OBJECT_FIELDS,
        });
    }
    if scalar_bytes > MAX_CTOR_SCALAR_BYTES {
        return Err(IRError::CtorScalarSizeTooLarge {
            name: info.name.clone(),
            bytes: scalar_bytes,
            max: MAX_CTOR_SCALAR_BYTES,
        });
    }
    Ok(())
}

/// `setTag` rewrites a heap constructor's tag byte in place
/// (`clean_ctor_set_tag(o, uint8_t)`), so it takes the heap bound.
pub(super) fn check_set_tag(tag: u32) -> Result<(), IRError> {
    if tag > MAX_REF_CTOR_TAG {
        return Err(IRError::SetTagTooLarge {
            tag,
            max: MAX_REF_CTOR_TAG,
        });
    }
    Ok(())
}

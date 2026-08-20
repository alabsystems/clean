// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GPU dialect.
//!
//! Provides abstractions for GPU parallel execution, including thread/block
//! identifiers and synchronization primitives.
//!
//! # Payload-only contract (no built-in lowering)
//!
//! `gpu.*` is an **opaque payload-only** dialect, mirroring `vector.*`: the
//! stable contract is the serialized [`DialectInst`] payload (dialect name, op
//! name, operands, result types, attributes). The core crate validates and
//! round-trips `gpu.*` ops but does **not** ship a lowering pass for them.
//!
//! There is no portable, target-independent lowering of a GPU thread/block
//! identifier or barrier to core TrustIr: the correct expansion is a
//! target-specific intrinsic (`gpu.tid.x` -> NVPTX `%tid.x` / Metal
//! `thread_position_in_threadgroup`; `gpu.barrier` -> `bar.sync` /
//! `threadgroup_barrier`) that only the backend's symbol table can resolve.
//! The previous built-in pass lowered every op to a generic `Inst::Call` whose
//! callee was `FuncId::new(0x1000 + intrinsic_name.len())` — a synthesized id
//! that points at no real function and *collided distinct intrinsics with
//! equal-length names* (e.g. `gpu.tid.x` / `gpu.tid.y` / `gpu.tid.z`, and
//! `gpu.bid.*` vs `gpu.tid.*`). That is unsound, so the pass was removed.
//! Backends that consume `gpu.*` register their own resolve-by-symbol lowering;
//! this crate intentionally leaves [`Dialect::lowerings`] at its empty default
//! so the ops survive verbatim until such a pass runs.

use crate::dialect::{Dialect, DialectError, DialectInst};
use crate::ty::Ty;

pub const DIALECT: &str = "gpu";

pub const THREAD_ID_X_OP: &str = "thread_id_x";
pub const THREAD_ID_Y_OP: &str = "thread_id_y";
pub const THREAD_ID_Z_OP: &str = "thread_id_z";
pub const BLOCK_ID_X_OP: &str = "block_id_x";
pub const BLOCK_ID_Y_OP: &str = "block_id_y";
pub const BLOCK_ID_Z_OP: &str = "block_id_z";
pub const BLOCK_DIM_X_OP: &str = "block_dim_x";
pub const BLOCK_DIM_Y_OP: &str = "block_dim_y";
pub const BLOCK_DIM_Z_OP: &str = "block_dim_z";
pub const GRID_DIM_X_OP: &str = "grid_dim_x";
pub const GRID_DIM_Y_OP: &str = "grid_dim_y";
pub const GRID_DIM_Z_OP: &str = "grid_dim_z";
pub const BARRIER_OP: &str = "barrier";

const OPS: &[&str] = &[
    THREAD_ID_X_OP,
    THREAD_ID_Y_OP,
    THREAD_ID_Z_OP,
    BLOCK_ID_X_OP,
    BLOCK_ID_Y_OP,
    BLOCK_ID_Z_OP,
    BLOCK_DIM_X_OP,
    BLOCK_DIM_Y_OP,
    BLOCK_DIM_Z_OP,
    GRID_DIM_X_OP,
    GRID_DIM_Y_OP,
    GRID_DIM_Z_OP,
    BARRIER_OP,
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GpuSpec {
    ThreadIdX,
    ThreadIdY,
    ThreadIdZ,
    BlockIdX,
    BlockIdY,
    BlockIdZ,
    BlockDimX,
    BlockDimY,
    BlockDimZ,
    GridDimX,
    GridDimY,
    GridDimZ,
    Barrier,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct GpuDialect;

impl Dialect for GpuDialect {
    fn name(&self) -> &'static str {
        DIALECT
    }

    fn version(&self) -> u32 {
        1
    }

    fn ops(&self) -> &'static [&'static str] {
        OPS
    }

    // No `lowerings()` override: `gpu.*` is a payload-only contract. See the
    // module docs for why a generic synthesized-`FuncId` lowering is unsound.

    fn validate(&self, inst: &DialectInst) -> Result<(), DialectError> {
        inst.validate_names()?;
        if inst.dialect != self.name() {
            return Err(DialectError::NameMismatch {
                expected: self.name(),
                got: inst.dialect.clone(),
            });
        }
        if !self.has_op(&inst.op) {
            return Err(DialectError::UnknownOp {
                dialect: self.name(),
                op: inst.op.clone(),
            });
        }
        decode(inst).map(|_| ())
    }
}

pub fn decode(inst: &DialectInst) -> Result<GpuSpec, DialectError> {
    match inst.op.as_str() {
        THREAD_ID_X_OP => Ok(GpuSpec::ThreadIdX),
        THREAD_ID_Y_OP => Ok(GpuSpec::ThreadIdY),
        THREAD_ID_Z_OP => Ok(GpuSpec::ThreadIdZ),
        BLOCK_ID_X_OP => Ok(GpuSpec::BlockIdX),
        BLOCK_ID_Y_OP => Ok(GpuSpec::BlockIdY),
        BLOCK_ID_Z_OP => Ok(GpuSpec::BlockIdZ),
        BLOCK_DIM_X_OP => Ok(GpuSpec::BlockDimX),
        BLOCK_DIM_Y_OP => Ok(GpuSpec::BlockDimY),
        BLOCK_DIM_Z_OP => Ok(GpuSpec::BlockDimZ),
        GRID_DIM_X_OP => Ok(GpuSpec::GridDimX),
        GRID_DIM_Y_OP => Ok(GpuSpec::GridDimY),
        GRID_DIM_Z_OP => Ok(GpuSpec::GridDimZ),
        BARRIER_OP => Ok(GpuSpec::Barrier),
        _ => Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        }),
    }
}

fn dim_op(op: &'static str) -> DialectInst {
    DialectInst::new(DIALECT, op).with_result_ty(Ty::U32)
}

pub fn thread_id_x() -> DialectInst {
    dim_op(THREAD_ID_X_OP)
}
pub fn thread_id_y() -> DialectInst {
    dim_op(THREAD_ID_Y_OP)
}
pub fn thread_id_z() -> DialectInst {
    dim_op(THREAD_ID_Z_OP)
}
pub fn block_id_x() -> DialectInst {
    dim_op(BLOCK_ID_X_OP)
}
pub fn block_id_y() -> DialectInst {
    dim_op(BLOCK_ID_Y_OP)
}
pub fn block_id_z() -> DialectInst {
    dim_op(BLOCK_ID_Z_OP)
}
pub fn block_dim_x() -> DialectInst {
    dim_op(BLOCK_DIM_X_OP)
}
pub fn block_dim_y() -> DialectInst {
    dim_op(BLOCK_DIM_Y_OP)
}
pub fn block_dim_z() -> DialectInst {
    dim_op(BLOCK_DIM_Z_OP)
}
pub fn grid_dim_x() -> DialectInst {
    dim_op(GRID_DIM_X_OP)
}
pub fn grid_dim_y() -> DialectInst {
    dim_op(GRID_DIM_Y_OP)
}
pub fn grid_dim_z() -> DialectInst {
    dim_op(GRID_DIM_Z_OP)
}

pub fn barrier() -> DialectInst {
    DialectInst::new(DIALECT, BARRIER_OP)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::Dialect;

    /// `gpu.*` is a payload-only contract: the dialect ships NO lowering pass.
    /// (FIX: the removed `GpuLoweringPass` lowered distinct intrinsics to the
    /// same synthesized `FuncId`, colliding equal-length names.)
    #[test]
    fn gpu_dialect_is_payload_only_no_lowerings() {
        let dialect = GpuDialect;
        assert!(
            dialect.lowerings().is_empty(),
            "gpu.* must not ship a built-in lowering pass"
        );
    }

    /// Every builder produces a payload that decodes back to its spec, and the
    /// dialect validates it. This is the opaque round-trip the backend relies on.
    #[test]
    fn builders_round_trip_through_decode_and_validate() {
        let dialect = GpuDialect;
        let cases = [
            (thread_id_x(), GpuSpec::ThreadIdX),
            (thread_id_y(), GpuSpec::ThreadIdY),
            (thread_id_z(), GpuSpec::ThreadIdZ),
            (block_id_x(), GpuSpec::BlockIdX),
            (block_id_y(), GpuSpec::BlockIdY),
            (block_id_z(), GpuSpec::BlockIdZ),
            (block_dim_x(), GpuSpec::BlockDimX),
            (block_dim_y(), GpuSpec::BlockDimY),
            (block_dim_z(), GpuSpec::BlockDimZ),
            (grid_dim_x(), GpuSpec::GridDimX),
            (grid_dim_y(), GpuSpec::GridDimY),
            (grid_dim_z(), GpuSpec::GridDimZ),
            (barrier(), GpuSpec::Barrier),
        ];
        for (op, expected) in cases {
            assert_eq!(op.dialect, DIALECT);
            assert_eq!(decode(&op).expect("decode"), expected);
            dialect
                .validate(&op)
                .unwrap_or_else(|e| panic!("{} should validate: {e}", op.qualified_name()));
        }
    }

    /// Distinct ops that previously collided under the equal-length-name
    /// `FuncId::new(0x1000 + name.len())` lowering decode to DISTINCT specs.
    /// The collision is impossible now because there is no built-in lowering,
    /// but we still pin that the equal-length op names remain distinguishable.
    #[test]
    fn equal_length_names_do_not_collide() {
        // The X/Y/Z variants within a family are all the same length — exactly
        // the case the old length-keyed callee id conflated into one FuncId.
        // They must stay distinct values, not be conflated.
        assert_eq!(THREAD_ID_X_OP.len(), THREAD_ID_Y_OP.len());
        assert_eq!(THREAD_ID_Y_OP.len(), THREAD_ID_Z_OP.len());

        let tx = decode(&thread_id_x()).unwrap();
        let ty = decode(&thread_id_y()).unwrap();
        let tz = decode(&thread_id_z()).unwrap();
        assert_ne!(tx, ty);
        assert_ne!(ty, tz);
        assert_ne!(tx, tz);

        // `thread_id_x` and `block_dim_x` have equal-length op names (and the
        // old lowering's intrinsic targets `gpu.tid.x` / `gpu.bdim.x` would
        // also collide by length); they must decode to different specs.
        assert_eq!(THREAD_ID_X_OP.len(), BLOCK_DIM_X_OP.len());
        assert_ne!(
            decode(&thread_id_x()).unwrap(),
            decode(&block_dim_x()).unwrap()
        );

        // `block_id_x` and `grid_dim_x` likewise share an op-name length.
        assert_eq!(BLOCK_ID_X_OP.len(), GRID_DIM_X_OP.len());
        assert_ne!(
            decode(&block_id_x()).unwrap(),
            decode(&grid_dim_x()).unwrap()
        );
    }

    #[test]
    fn validate_rejects_unknown_op() {
        let dialect = GpuDialect;
        let bad = DialectInst::new(DIALECT, "warp_shuffle");
        assert!(matches!(
            dialect.validate(&bad),
            Err(DialectError::UnknownOp { .. })
        ));
    }
}

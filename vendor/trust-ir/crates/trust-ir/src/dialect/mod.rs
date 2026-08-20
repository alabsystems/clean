// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # Layered dialect framework
//!
//! MLIR-style dialects, adapted to TrustIr. A dialect is a named namespace of
//! operations that live *inside* the core TrustIr `Inst` enum via the
//! `Inst::DialectOp(Box<DialectInst>)` variant. Dialect ops round-trip through
//! every TrustIr serialization format without the core crate having to know their
//! semantics.
//!
//! Three layers:
//!
//! 1. **Representation.** [`inst::DialectInst`] carries a dialect name, op
//!    name, operands, result types, attributes, and a payload version.
//! 2. **Registry.** [`DialectRegistry`] holds registered dialects keyed by
//!    name, plus per-dialect lowering pipelines. Registries are created at
//!    the frontend/backend boundary and never persisted inside the IR.
//! 3. **Lowering.** [`lowering::LoweringPass`] rewrites dialect ops into
//!    lower-level TrustIr (or into another dialect). [`lowering::lower_module`]
//!    walks a whole module and applies all passes in a fixed point.
//!
//! This framework is the TrustIr half of the verification-dialect story in
//! TrustIr#390. A frontend like ty can introduce a `verif.*` dialect
//! (`verif.bfs_step`, `verif.frontier_drain`, `verif.fingerprint_batch`) that
//! is progressively lowered — first by TrustIr-side passes that rewrite verif
//! ops into generic TrustIr, then by TrustIr's own dialect layer that can still
//! pattern-match on any surviving verif ops.
//!
//! ## Example
//!
//! ```
//! use trust_ir::dialect::{Dialect, DialectRegistry, DialectInst};
//! use trust_ir::value::ValueId;
//! use trust_ir::ty::Ty;
//!
//! struct MyDialect;
//! impl Dialect for MyDialect {
//!     fn name(&self) -> &'static str { "mydialect" }
//!     fn version(&self) -> u32 { 1 }
//!     fn ops(&self) -> &'static [&'static str] { &["op_a", "op_b"] }
//! }
//!
//! let mut reg = DialectRegistry::new();
//! reg.register(Box::new(MyDialect));
//! assert!(reg.is_registered("mydialect"));
//!
//! let op = DialectInst::new("mydialect", "op_a")
//!     .with_operand(ValueId::new(0))
//!     .with_result_ty(Ty::I32);
//! assert_eq!(op.qualified_name(), "mydialect.op_a");
//! ```

pub mod ane;
pub mod avx512;
pub mod gpu;
pub mod inst;
pub mod lowering;
pub mod trust_rust;
pub mod vector;

#[cfg(any(test, feature = "dialect-verif-example"))]
pub mod examples;

pub use inst::{AttrEntry, AttrValue, DialectInst, NameError, NameRole};
pub use lowering::{LoweringPass, LoweringResult, RewriteOutcome, lower_module};

use crate::Module;

/// A TrustIr dialect: a namespace of operations above the core instruction set.
///
/// Implementors describe the dialect (its name, version, and op set) and
/// register lowering passes that rewrite its ops into lower-level TrustIr.
/// A dialect MUST be a zero-sized or cheaply-cloned value; registries store
/// them behind `Box<dyn Dialect>`.
pub trait Dialect: Send + Sync {
    /// Stable, unique namespace — e.g. `"verif"`. Must match the `dialect`
    /// field of every `DialectInst` this dialect owns.
    fn name(&self) -> &'static str;

    /// Dialect schema version. Bump when op semantics or attribute layout
    /// change in an incompatible way.
    fn version(&self) -> u32;

    /// List of op names this dialect defines. Used for validation and for
    /// diagnostics when an unknown op is encountered.
    fn ops(&self) -> &'static [&'static str];

    /// Returns true if the dialect claims the given op name.
    fn has_op(&self, op: &str) -> bool {
        self.ops().contains(&op)
    }

    /// Validates a `DialectInst` that claims to belong to this dialect.
    ///
    /// Default implementation checks that the dialect/op/attribute names are
    /// lexically well-formed (see [`DialectInst::validate_names`]), that the
    /// dialect name matches, and that the op name is registered. Dialects with
    /// richer invariants should override — but should call
    /// [`DialectInst::validate_names`] (or this default via the trait) so the
    /// lexical contract is never skipped.
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
        Ok(())
    }

    /// Returns lowering passes this dialect contributes to the pipeline.
    ///
    /// Passes are applied in order during a single sweep; `lower_module`
    /// iterates until no pass reports a change or until `max_iters` is
    /// exhausted.
    fn lowerings(&self) -> Vec<Box<dyn LoweringPass>> {
        Vec::new()
    }
}

/// Error returned by dialect validation and lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DialectError {
    /// A dialect, op, or attribute name is lexically malformed (empty or
    /// contains a delimiter / control char such as `.`). Such a name does not
    /// round-trip through the text format.
    InvalidName(NameError),
    /// `DialectInst::dialect` does not match the dialect the lookup targeted.
    NameMismatch { expected: &'static str, got: String },
    /// `DialectInst::op` is not part of the dialect's op set.
    UnknownOp { dialect: &'static str, op: String },
    /// No dialect with the given name is registered.
    UnknownDialect { name: String },
    /// A lowering pass failed with a descriptive message.
    LoweringFailed { pass: String, reason: String },
    /// The fixed-point iteration did not converge within `max_iters`.
    FixpointNotReached { max_iters: usize },
}

impl From<NameError> for DialectError {
    fn from(err: NameError) -> Self {
        DialectError::InvalidName(err)
    }
}

impl core::fmt::Display for DialectError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DialectError::InvalidName(err) => write!(f, "invalid dialect op name: {err}"),
            DialectError::NameMismatch { expected, got } => {
                write!(
                    f,
                    "dialect name mismatch: expected {expected:?}, got {got:?}"
                )
            }
            DialectError::UnknownOp { dialect, op } => {
                write!(f, "unknown op {op:?} in dialect {dialect:?}")
            }
            DialectError::UnknownDialect { name } => {
                write!(f, "no dialect registered with name {name:?}")
            }
            DialectError::LoweringFailed { pass, reason } => {
                write!(f, "lowering pass {pass:?} failed: {reason}")
            }
            DialectError::FixpointNotReached { max_iters } => {
                write!(
                    f,
                    "dialect lowering did not converge after {max_iters} iterations"
                )
            }
        }
    }
}

impl std::error::Error for DialectError {}

/// Holds registered dialects and their lowering passes.
///
/// A `DialectRegistry` is constructed per-pipeline (typically once per
/// frontend-to-backend compilation). It is not serialized as part of the IR —
/// only [`DialectInst`] payloads inside the module are. Two different
/// registries with different lowering pipelines can consume the same TrustIr.
#[derive(Default)]
pub struct DialectRegistry {
    dialects: Vec<Box<dyn Dialect>>,
    // Passes are owned by the registry. Cached here so `lower_module` does
    // not repeatedly traverse the dialect list to rebuild the pipeline.
    passes: Vec<Box<dyn LoweringPass>>,
}

impl DialectRegistry {
    /// Creates an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers a dialect. Its `lowerings()` are cached into the pipeline in
    /// registration order. Later dialects run after earlier ones in each
    /// lowering sweep.
    ///
    /// Registering two dialects with the same `name()` overwrites the first —
    /// the most recently registered dialect wins for `get()` lookups, but
    /// both dialects' passes remain in the pipeline. Prefer registering each
    /// dialect at most once.
    pub fn register(&mut self, dialect: Box<dyn Dialect>) {
        for pass in dialect.lowerings() {
            self.passes.push(pass);
        }
        self.dialects.push(dialect);
    }

    /// Returns true iff a dialect with the given name is registered.
    pub fn is_registered(&self, name: &str) -> bool {
        self.get(name).is_some()
    }

    /// Looks up a dialect by name. Returns the most recently registered one
    /// when multiple share the same name.
    pub fn get(&self, name: &str) -> Option<&dyn Dialect> {
        self.dialects
            .iter()
            .rev()
            .find(|d| d.name() == name)
            .map(|b| b.as_ref())
    }

    /// Returns the number of distinct dialect entries in the registry.
    pub fn len(&self) -> usize {
        self.dialects.len()
    }

    /// Returns true iff no dialects are registered.
    pub fn is_empty(&self) -> bool {
        self.dialects.is_empty()
    }

    /// Returns a slice of all registered dialects, in registration order.
    pub fn dialects(&self) -> &[Box<dyn Dialect>] {
        &self.dialects
    }

    /// Returns a slice of all lowering passes, in registration order.
    pub fn passes(&self) -> &[Box<dyn LoweringPass>] {
        &self.passes
    }

    /// Validates every `DialectInst` in `module` against the registry.
    ///
    /// Returns an error on the first op that references an unknown dialect
    /// or fails the dialect's own `validate()` check.
    pub fn validate_module(&self, module: &Module) -> Result<(), DialectError> {
        for func in &module.functions {
            for block in &func.blocks {
                for node in &block.body {
                    if let crate::inst::Inst::DialectOp(op) = &node.inst {
                        let Some(dialect) = self.get(&op.dialect) else {
                            return Err(DialectError::UnknownDialect {
                                name: op.dialect.clone(),
                            });
                        };
                        dialect.validate(op)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Lowers `module` by applying all registered passes until a fixed point
    /// is reached or `max_iters` is exceeded.
    ///
    /// This is a convenience wrapper over [`lowering::lower_module`] that
    /// uses the registry's own pass list.
    pub fn lower(
        &self,
        module: &mut Module,
        max_iters: usize,
    ) -> Result<LoweringResult, DialectError> {
        lowering::lower_module(module, &self.passes, max_iters)
    }
}

impl core::fmt::Debug for DialectRegistry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DialectRegistry")
            .field(
                "dialects",
                &self
                    .dialects
                    .iter()
                    .map(|d| (d.name(), d.version()))
                    .collect::<Vec<_>>(),
            )
            .field("pass_count", &self.passes.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct DummyDialect;
    impl Dialect for DummyDialect {
        fn name(&self) -> &'static str {
            "dummy"
        }
        fn version(&self) -> u32 {
            2
        }
        fn ops(&self) -> &'static [&'static str] {
            &["noop", "passthrough"]
        }
    }

    #[test]
    fn register_and_lookup() {
        let mut reg = DialectRegistry::new();
        assert!(reg.is_empty());
        reg.register(Box::new(DummyDialect));
        assert!(!reg.is_empty());
        assert_eq!(reg.len(), 1);
        assert!(reg.is_registered("dummy"));
        assert!(!reg.is_registered("missing"));
        let d = reg.get("dummy").unwrap();
        assert_eq!(d.name(), "dummy");
        assert_eq!(d.version(), 2);
        assert!(d.has_op("noop"));
        assert!(d.has_op("passthrough"));
        assert!(!d.has_op("unknown"));
    }

    #[test]
    fn validate_accepts_known_ops() {
        let d = DummyDialect;
        let ok = DialectInst::new("dummy", "noop");
        assert!(d.validate(&ok).is_ok());
    }

    #[test]
    fn validate_rejects_wrong_dialect() {
        let d = DummyDialect;
        let bad = DialectInst::new("other", "noop");
        let err = d.validate(&bad).unwrap_err();
        assert!(matches!(err, DialectError::NameMismatch { .. }));
    }

    #[test]
    fn validate_rejects_unknown_op() {
        let d = DummyDialect;
        let bad = DialectInst::new("dummy", "not_a_real_op");
        let err = d.validate(&bad).unwrap_err();
        assert!(matches!(err, DialectError::UnknownOp { .. }));
    }

    #[test]
    fn validate_rejects_lexically_malformed_names() {
        let d = DummyDialect;
        // A dotted op name does not round-trip through the text format, so the
        // default validator must reject it before the op-set membership check.
        let bad = DialectInst::new("dummy", "no.op");
        let err = d.validate(&bad).unwrap_err();
        assert!(matches!(
            err,
            DialectError::InvalidName(NameError {
                role: NameRole::Op,
                ..
            })
        ));

        // A dotted dialect name is rejected even though name-matching would
        // also fail — the lexical check runs first and is more specific.
        let dotted_dialect = DialectInst::new("a.b", "noop");
        assert!(matches!(
            d.validate(&dotted_dialect).unwrap_err(),
            DialectError::InvalidName(NameError {
                role: NameRole::Dialect,
                ..
            })
        ));
    }

    #[test]
    fn registry_validate_module_flags_unknown_dialect() {
        use crate::inst::Inst;
        use crate::node::InstrNode;
        use crate::value::{BlockId, FuncId, FuncTyId};
        use crate::{Block, Function, Module};

        let reg = DialectRegistry::new();
        let mut module = Module::new("m");
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(DialectInst::new(
                "ghost", "op",
            )))));
        func.blocks.push(block);
        module.add_function(func);

        let err = reg.validate_module(&module).unwrap_err();
        assert!(matches!(err, DialectError::UnknownDialect { .. }));
    }

    #[test]
    fn debug_format_lists_dialects() {
        let mut reg = DialectRegistry::new();
        reg.register(Box::new(DummyDialect));
        let s = format!("{reg:?}");
        assert!(s.contains("dummy"));
        assert!(s.contains("pass_count"));
    }

    #[test]
    fn display_error_has_useful_text() {
        let err = DialectError::UnknownDialect {
            name: "verif".to_string(),
        };
        let s = format!("{err}");
        assert!(s.contains("verif"));
    }
}

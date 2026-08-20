// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sealed Rust-source operations that cannot be represented faithfully by a
//! core TrustIr instruction.
//!
//! `trust_rust.*` is a payload-only dialect.  In particular,
//! [`thread_local_addr`] denotes evaluation of Rust MIR's
//! `Rvalue::ThreadLocalRef`: it produces the address of one named thread-local
//! static in the current thread.  It is deliberately distinct from
//! `Inst::Undef`, whose core TrustIr meaning is poison/undefined behavior.
//!
//! Consumers may conservatively model a TLS address as a fresh demonic pointer,
//! but version 1 grants no TLS identity, non-nullness, dereferenceability, or
//! aliasing assumptions.  The `symbol` attribute is provenance only.

use crate::dialect::{AttrValue, Dialect, DialectError, DialectInst};
use crate::ty::Ty;

pub const DIALECT: &str = "trust_rust";
pub const THREAD_LOCAL_ADDR_OP: &str = "thread_local_addr";
pub const THREAD_LOCAL_ADDR_ATTR_SCHEMA: &str = "schema";
pub const THREAD_LOCAL_ADDR_ATTR_SYMBOL: &str = "symbol";
pub const THREAD_LOCAL_ADDR_SCHEMA: &str = "trust-rust.thread-local-addr/v1";

const OPS: &[&str] = &[THREAD_LOCAL_ADDR_OP];

/// The decoded, exact version-1 thread-local-address payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ThreadLocalAddrSpec<'a> {
    /// Source-level TLS symbol identity.  This is provenance, not an equality
    /// or aliasing fact for the returned pointer.
    pub symbol: &'a str,
}

/// Payload-only Rust-source dialect.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrustRustDialect;

impl Dialect for TrustRustDialect {
    fn name(&self) -> &'static str {
        DIALECT
    }

    fn version(&self) -> u32 {
        1
    }

    fn ops(&self) -> &'static [&'static str] {
        OPS
    }

    fn validate(&self, inst: &DialectInst) -> Result<(), DialectError> {
        decode_thread_local_addr(inst).map(|_| ())
    }
}

/// Construct the one canonical version-1 Rust TLS-address payload.
///
/// An empty symbol can be constructed so frontends do not need to panic, but
/// [`decode_thread_local_addr`] rejects it.  Producers should pass the stable
/// source symbol supplied by their MIR extraction boundary.
pub fn thread_local_addr(symbol: impl Into<String>) -> DialectInst {
    DialectInst::new(DIALECT, THREAD_LOCAL_ADDR_OP)
        .with_result_ty(Ty::Ptr)
        .with_attr(
            THREAD_LOCAL_ADDR_ATTR_SCHEMA,
            AttrValue::Str(THREAD_LOCAL_ADDR_SCHEMA.to_owned()),
        )
        .with_attr(THREAD_LOCAL_ADDR_ATTR_SYMBOL, AttrValue::Str(symbol.into()))
}

/// Decode only the exact version-1 Rust TLS-address schema.
///
/// Unknown versions, operands, extra or duplicate attributes, result-shape
/// drift, and empty symbols are rejected.  The enclosing `InstrNode` must also
/// have exactly one result; consumers that accept unvalidated modules must
/// check that node-level invariant independently.
pub fn decode_thread_local_addr(
    inst: &DialectInst,
) -> Result<ThreadLocalAddrSpec<'_>, DialectError> {
    inst.validate_names()?;
    if inst.dialect != DIALECT {
        return Err(DialectError::NameMismatch {
            expected: DIALECT,
            got: inst.dialect.clone(),
        });
    }
    if inst.op != THREAD_LOCAL_ADDR_OP {
        return Err(DialectError::UnknownOp {
            dialect: DIALECT,
            op: inst.op.clone(),
        });
    }
    if inst.version != 1 {
        return Err(payload_error(format!(
            "expected payload version 1, got {}",
            inst.version
        )));
    }
    if !inst.operands.is_empty() {
        return Err(payload_error(format!(
            "expected zero operands, got {}",
            inst.operands.len()
        )));
    }
    if inst.result_tys.as_slice() != [Ty::Ptr] {
        return Err(payload_error(format!(
            "expected exactly one Ptr result type, got {:?}",
            inst.result_tys
        )));
    }
    if inst.attrs.len() != 2 {
        return Err(payload_error(format!(
            "expected exactly schema and symbol attributes, got {} attributes",
            inst.attrs.len()
        )));
    }

    let mut schema = None;
    let mut symbol = None;
    for attr in &inst.attrs {
        match (attr.name.as_str(), &attr.value) {
            (THREAD_LOCAL_ADDR_ATTR_SCHEMA, AttrValue::Str(value)) if schema.is_none() => {
                schema = Some(value.as_str());
            }
            (THREAD_LOCAL_ADDR_ATTR_SYMBOL, AttrValue::Str(value)) if symbol.is_none() => {
                symbol = Some(value.as_str());
            }
            (name, _) => {
                return Err(payload_error(format!(
                    "unexpected, duplicate, or ill-typed attribute {name:?}"
                )));
            }
        }
    }

    if schema != Some(THREAD_LOCAL_ADDR_SCHEMA) {
        return Err(payload_error("schema attribute does not match version 1"));
    }
    let Some(symbol) = symbol.filter(|symbol| !symbol.is_empty()) else {
        return Err(payload_error("symbol attribute must be a non-empty string"));
    };

    Ok(ThreadLocalAddrSpec { symbol })
}

/// True only for the exact version-1 Rust TLS-address schema.
pub fn is_thread_local_addr(inst: &DialectInst) -> bool {
    decode_thread_local_addr(inst).is_ok()
}

fn payload_error(reason: impl Into<String>) -> DialectError {
    DialectError::LoweringFailed {
        pass: "trust_rust.thread_local_addr.decode".to_owned(),
        reason: reason.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{AttrEntry, DialectRegistry};
    use crate::value::ValueId;

    #[test]
    fn canonical_builder_decodes_and_registry_validates() {
        let op = thread_local_addr("crate::TLS");
        assert_eq!(
            decode_thread_local_addr(&op),
            Ok(ThreadLocalAddrSpec {
                symbol: "crate::TLS"
            })
        );
        assert!(is_thread_local_addr(&op));

        let mut registry = DialectRegistry::new();
        registry.register(Box::new(TrustRustDialect));
        assert!(
            registry
                .get(DIALECT)
                .expect("registered dialect")
                .validate(&op)
                .is_ok()
        );
        assert!(
            registry.passes().is_empty(),
            "trust_rust must remain payload-only"
        );
    }

    #[test]
    fn decoder_rejects_every_schema_dimension_and_near_miss() {
        let canonical = thread_local_addr("crate::TLS");
        let mut cases = Vec::new();

        let mut op = canonical.clone();
        op.dialect = "other".to_owned();
        cases.push(op);
        let mut op = canonical.clone();
        op.op = "other".to_owned();
        cases.push(op);
        let mut op = canonical.clone();
        op.version = 2;
        cases.push(op);
        let mut op = canonical.clone();
        op.operands.push(ValueId::new(0));
        cases.push(op);
        let mut op = canonical.clone();
        op.result_tys.clear();
        cases.push(op);
        let mut op = canonical.clone();
        op.result_tys[0] = Ty::U64;
        cases.push(op);
        let mut op = canonical.clone();
        op.attrs.pop();
        cases.push(op);
        let mut op = canonical.clone();
        op.attrs.push(AttrEntry {
            name: "extra".to_owned(),
            value: AttrValue::Bool(true),
        });
        cases.push(op);
        let mut op = canonical.clone();
        op.attrs[0].value = AttrValue::Str("wrong-schema".to_owned());
        cases.push(op);
        let mut op = canonical.clone();
        op.attrs[1].value = AttrValue::Str(String::new());
        cases.push(op);
        let mut op = canonical;
        op.attrs[1].name = THREAD_LOCAL_ADDR_ATTR_SCHEMA.to_owned();
        cases.push(op);

        for case in cases {
            assert!(
                !is_thread_local_addr(&case),
                "near miss was accepted: {case:?}"
            );
            assert!(decode_thread_local_addr(&case).is_err());
        }
    }
}

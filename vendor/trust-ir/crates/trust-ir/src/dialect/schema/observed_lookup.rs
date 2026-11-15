// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual frozen data-only registry lookup; no opaque callbacks or new authority.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod storage;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
impl DialectSchemaRegistry {
    /// Check the original full lexical prefix and exact namespace/version/op
    /// selection under the supplied session. Borrowed declarations stay frozen;
    /// this is not complete schema validation, a module or semantic certificate.
    /// The caller must continue all count/result/actual SSA/function/attribute
    /// checks in their original order, under this same owner. No input disposal
    /// or physical std/allocation/time bound is established.
    pub fn lookup_operation_observed<O: ExecutionObserver>(
        &self,
        op: &DialectInst,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<&OperationSchema, String>> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<String>() + size_of::<Work<'_, '_, O>>(),
        })?;
        let mut output = String::new();
        let mut work = Work { session, site };
        let answer = self.lookup(op, &mut output, &mut work);
        match answer {
            Ok(Some(schema)) => {
                work.retire(output);
                work.publication()?;
                Ok(Ok(schema))
            }
            Ok(None) => match work.publication() {
                Ok(()) => Ok(Err(take(&mut output))),
                Err(e) => {
                    work.retire(output);
                    Err(work.terminal(e))
                }
            },
            Err(e) => {
                work.retire(output);
                Err(work.terminal(e))
            }
        }
    }

    fn lookup<'a, O: ExecutionObserver>(
        &'a self,
        op: &DialectInst,
        out: &mut String,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a OperationSchema>> {
        for (name, role) in [(&op.dialect, "Dialect"), (&op.op, "Op")] {
            if !valid(name, work)? {
                invalid(name, role, out, work)?;
                return Ok(None);
            }
        }
        let mut at = 0;
        while let Some(attr) = get(&op.attrs, at, work)? {
            if !valid(&attr.name, work)? {
                invalid(&attr.name, "Attr", out, work)?;
                return Ok(None);
            }
            at = next(at, work)?;
        }
        let mut at = 0;
        let dialect = loop {
            let Some(d) = get(&self.dialects, at, work)? else {
                work.text("dialect schema mismatch: UnknownDialect(", out)?;
                work.quoted(&op.dialect, out)?;
                work.text(")", out)?;
                return Ok(None);
            };
            if work.eq(&d.namespace, &op.dialect)? {
                break d;
            }
            at = next(at, work)?;
        };
        work.admit(1, size_of::<bool>())?;
        if op.version != dialect.version {
            work.text("dialect schema mismatch: VersionMismatch { expected: ", out)?;
            work.number(u128::from(dialect.version), out)?;
            work.text(", actual: ", out)?;
            work.number(u128::from(op.version), out)?;
            work.text(" }", out)?;
            return Ok(None);
        }
        let mut at = 0;
        loop {
            let Some(s) = get(&dialect.operations, at, work)? else {
                work.text("dialect schema mismatch: UnknownOperation(", out)?;
                work.quoted(&op.op, out)?;
                work.text(")", out)?;
                return Ok(None);
            };
            if work.eq(&s.name, &op.op)? {
                return Ok(Some(s));
            }
            at = next(at, work)?;
        }
    }
}
fn get<'a, T, O: ExecutionObserver>(
    rows: &'a [T],
    at: usize,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a T>> {
    work.admit(1, size_of::<Option<&T>>())?;
    Ok(rows.get(at))
}
fn next<O: ExecutionObserver>(n: usize, work: &mut Work<'_, '_, O>) -> R<usize> {
    work.admit(1, size_of::<usize>())?;
    n.checked_add(1).ok_or(ObservedValueError::CapacityOverflow)
}
fn valid<O: ExecutionObserver>(name: &str, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    if name.is_empty() {
        return Ok(false);
    }
    let mut at = 0;
    while let Some(b) = get(name.as_bytes(), at, work)? {
        work.admit(1, 0)?;
        if !(b.is_ascii_alphanumeric() || *b == b'_') {
            return Ok(false);
        }
        at = next(at, work)?;
    }
    Ok(true)
}
fn invalid<O: ExecutionObserver>(
    name: &str,
    role: &str,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.text(
        "dialect schema mismatch: InvalidName(NameError { role: ",
        out,
    )?;
    work.text(role, out)?;
    work.text(", name: ", out)?;
    work.quoted(name, out)?;
    work.text(" })", out)
}

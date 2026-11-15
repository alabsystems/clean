// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use core::cmp::Ordering;
use core::mem::size_of;

/// Stable bottom-up mergesort of borrowed rows: no payload clone, opaque
/// sorting callback, fresh owner or unobserved string comparison.
pub(super) fn sorted<'a, T, O: ExecutionObserver>(
    rows: &'a [T],
    out: &mut Writer<'_, '_, O>,
    mut compare: impl FnMut(&T, &T, &mut Writer<'_, '_, O>) -> Result<Ordering>,
) -> Result<Vec<&'a T>> {
    let mut source = Vec::new();
    let mut scratch = Vec::new();
    let result: Result = (|| {
        out.reserve(&mut source, rows.len())?;
        out.reserve(&mut scratch, rows.len())?;
        for row in rows {
            out.admit(2, 2 * size_of::<&T>())?;
            source.push(row);
            scratch.push(row);
        }
        let mut width = 1usize;
        while width < rows.len() {
            out.poll()?;
            let mut start = 0;
            while start < rows.len() {
                out.poll()?;
                let middle = start.saturating_add(width).min(rows.len());
                let end = middle.saturating_add(width).min(rows.len());
                let (mut left, mut right) = (start, middle);
                for destination in &mut scratch[start..end] {
                    out.admit(1, size_of::<&T>())?;
                    let from_left = right == end
                        || left < middle
                            && compare(source[left], source[right], out)? != Ordering::Greater;
                    if from_left {
                        *destination = source[left];
                        left += 1;
                    } else {
                        *destination = source[right];
                        right += 1;
                    }
                }
                start = end;
            }
            core::mem::swap(&mut source, &mut scratch);
            width = width.saturating_mul(2);
        }
        Ok::<(), ObservedValueError>(())
    })();
    out.retire_value(scratch);
    if let Err(error) = result {
        out.retire_value(source);
        return Err(error);
    }
    if let Err(error) = out.poll() {
        out.retire_value(source);
        return Err(error);
    }
    Ok(source)
}

pub(super) fn string_cmp<O: ExecutionObserver>(
    left: &str,
    right: &str,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    for (left, right) in left
        .as_bytes()
        .chunks(1024)
        .zip(right.as_bytes().chunks(1024))
    {
        out.admit(
            left.len()
                .checked_add(right.len())
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        let ordering = left.cmp(right);
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    out.poll()?;
    Ok(left.len().cmp(&right.len()))
}

pub(super) fn option_string_cmp<O: ExecutionObserver>(
    left: Option<&str>,
    right: Option<&str>,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    out.poll()?;
    match (left, right) {
        (None, None) => Ok(Ordering::Equal),
        (None, Some(_)) => Ok(Ordering::Less),
        (Some(_), None) => Ok(Ordering::Greater),
        (Some(left), Some(right)) => string_cmp(left, right, out),
    }
}

pub(super) fn tool_cmp<O: ExecutionObserver>(
    left: &NativeToolIdentity,
    right: &NativeToolIdentity,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    let name = string_cmp(&left.name, &right.name, out)?;
    if name != Ordering::Equal {
        return Ok(name);
    }
    let version = option_string_cmp(left.version.as_deref(), right.version.as_deref(), out)?;
    if version != Ordering::Equal {
        return Ok(version);
    }
    let revision = option_string_cmp(left.revision.as_deref(), right.revision.as_deref(), out)?;
    if revision != Ordering::Equal {
        return Ok(revision);
    }
    out.admit(66, 0)?;
    Ok(left.digest.cmp(&right.digest))
}

pub(super) fn certificate_cmp<O: ExecutionObserver>(
    left: &ProofCertificateRef,
    right: &ProofCertificateRef,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    out.poll()?;
    let id = left.obligation.cmp(&right.obligation);
    if id != Ordering::Equal {
        return Ok(id);
    }
    let prover = string_cmp(&left.prover, &right.prover, out)?;
    if prover != Ordering::Equal {
        return Ok(prover);
    }
    out.admit(66, 0)?;
    Ok(left.evidence_digest.cmp(&right.evidence_digest))
}

/// Retain and retire every borrowed sort buffer on success and every stop path.
pub(super) fn write_sorted<T, O: ExecutionObserver>(
    rows: &[T],
    out: &mut Writer<'_, '_, O>,
    compare: impl FnMut(&T, &T, &mut Writer<'_, '_, O>) -> Result<Ordering>,
    mut write: impl FnMut(&T, &mut Writer<'_, '_, O>) -> Result,
) -> Result {
    let rows = sorted(rows, out, compare)?;
    let result: Result = (|| {
        write_len(out, rows.len())?;
        for row in &rows {
            out.poll()?;
            write(row, out)?;
        }
        Ok(())
    })();
    out.retire_value(rows);
    result?;
    out.poll()
}

pub(super) fn artifact_cmp<O: ExecutionObserver>(
    left: &NativeEvidenceArtifact,
    right: &NativeEvidenceArtifact,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    let name = string_cmp(&left.name, &right.name, out)?;
    if name != Ordering::Equal {
        return Ok(name);
    }
    out.admit(66, 0)?;
    Ok((left.kind, left.digest).cmp(&(right.kind, right.digest)))
}

pub(super) fn unsupported_cmp<O: ExecutionObserver>(
    left: &NativeUnsupportedMode,
    right: &NativeUnsupportedMode,
    out: &mut Writer<'_, '_, O>,
) -> Result<Ordering> {
    out.poll()?;
    let reason = left.reason.cmp(&right.reason);
    if reason != Ordering::Equal {
        return Ok(reason);
    }
    string_cmp(&left.detail, &right.detail, out)
}

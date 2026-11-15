// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

pub(super) fn write_tool_identity<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    tool: &NativeToolIdentity,
) -> Result {
    write_name(out, &tool.name)?;
    write_option_str(out, tool.version.as_deref())?;
    write_option_str(out, tool.revision.as_deref())?;
    write_option_digest(out, tool.digest)
}

/// Byte-for-byte `canonical_tool_name`, with each input byte and scratch growth
/// admitted before processing. Ignoring non-ASCII prefix/suffix bytes already
/// has exactly the output effect of the legacy preliminary Unicode `trim`.
fn write_name<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, name: &str) -> Result {
    let mut normalized = Vec::new();
    let result: Result = (|| {
        let mut separator = false;
        for byte in name.bytes() {
            out.poll()?;
            if byte.is_ascii_alphanumeric() {
                if separator && !normalized.is_empty() {
                    out.push_value(&mut normalized, b'-')?;
                }
                out.push_value(&mut normalized, byte.to_ascii_lowercase())?;
                separator = false;
            } else if !normalized.is_empty() {
                separator = true;
            }
        }
        let (prefix, skip) = family_prefix(&normalized, out)?;
        let length = prefix
            .len()
            .checked_add(normalized.len() - skip)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        write_len(out, length)?;
        out.append(prefix)?;
        out.append(&normalized[skip..])
    })();
    out.retire_value(normalized);
    result?;
    out.poll()
}

fn family_prefix<'a, O: ExecutionObserver>(
    normalized: &[u8],
    out: &mut Writer<'_, '_, O>,
) -> Result<(&'a [u8], usize)> {
    for (compact, separated, family) in [
        (&b"trustvc"[..], &b"trust-vc"[..], &b"trust_vc"[..]),
        (&b"trustmc"[..], &b"trust-mc"[..], &b"trust_mc"[..]),
        (&b"trustwp"[..], &b"trust-wp"[..], &b"trust_wp"[..]),
        (&b"trustir"[..], &b"trust-ir"[..], &b"trust-ir"[..]),
    ] {
        for spelling in [compact, separated] {
            // At most eight prefix bytes; never an opaque full-string scan.
            out.admit(10, 0)?;
            if normalized.len() == spelling.len() && normalized == spelling {
                return Ok((family, spelling.len()));
            }
            if normalized.get(..spelling.len()) == Some(spelling)
                && normalized.get(spelling.len()) == Some(&b'-')
            {
                // Leave the existing separating hyphen in the borrowed suffix.
                return Ok((family, spelling.len()));
            }
        }
    }
    Ok((&[], 0))
}

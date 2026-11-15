// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
type Budget = R<Option<&'static str>>;
pub(super) fn identity<O: ExecutionObserver>(
    a: &SignatureAbi,
    out: &mut Writer<'_, '_, O>,
) -> Budget {
    out.admit(1, 9 * size_of::<&String>() + 2 * size_of::<usize>())?;
    let identities = [
        &a.target.triple,
        &a.target.data_layout,
        &a.target.abi,
        &a.target.cpu,
        &a.target.target_spec,
        &a.frontend.name,
        &a.frontend.revision,
        &a.convention,
        &a.source_abi,
    ];
    let mut bytes = 0;
    let mut at = 0;
    loop {
        out.admit(1, size_of::<Option<&&String>>())?;
        let Some(text) = identities.get(at) else {
            break;
        };
        if let Some(e) = identity_add(&mut bytes, text.len(), out)? {
            return Ok(Some(e));
        }
        out.admit(1, size_of::<usize>())?;
        at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
    let mut at = 0;
    loop {
        out.admit(1, size_of::<Option<&String>>())?;
        let Some(text) = a.target.features.get(at) else {
            break;
        };
        if let Some(e) = identity_add(&mut bytes, text.len(), out)? {
            return Ok(Some(e));
        }
        out.admit(1, size_of::<usize>())?;
        at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
    Ok(None)
}
pub(super) fn identity_add<O: ExecutionObserver>(
    bytes: &mut usize,
    count: usize,
    out: &mut Writer<'_, '_, O>,
) -> Budget {
    out.admit(2, 2 * size_of::<usize>())?;
    let Some(next) = bytes.checked_add(count) else {
        return Ok(Some("ABI identity byte count overflows"));
    };
    *bytes = next;
    Ok((next > MAX_ABI_TEXT_BYTES).then_some("ABI identity exceeds wire byte limit"))
}
pub(super) fn nodes<O: ExecutionObserver>(a: &SignatureAbi, out: &mut Writer<'_, '_, O>) -> Budget {
    out.admit(1, 2 * size_of::<usize>())?;
    let mut nodes = 20;
    if let Some(e) = add(&mut nodes, a.target.features.len(), out)? {
        return Ok(Some(e));
    }
    let mut at = 0;
    loop {
        out.admit(1, size_of::<Option<&AbiArgument>>())?;
        let Some(argument) = a.arguments.get(at) else {
            break;
        };
        if let Some(e) = argument_nodes(argument, &mut nodes, out)? {
            return Ok(Some(e));
        }
        out.admit(1, size_of::<usize>())?;
        at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
    argument_nodes(&a.result, &mut nodes, out)
}
fn argument_nodes<O: ExecutionObserver>(
    a: &AbiArgument,
    nodes: &mut usize,
    out: &mut Writer<'_, '_, O>,
) -> Budget {
    out.admit(5, 3 * size_of::<usize>() + size_of::<bool>())?;
    let mode_nodes = match &a.mode {
        AbiPassMode::Ignore => 2,
        AbiPassMode::Direct(_) => 21,
        AbiPassMode::Pair(_, _) => 40,
        AbiPassMode::Cast { prefix, .. } => {
            let Some(n) = prefix
                .len()
                .checked_mul(3)
                .and_then(|n| 23usize.checked_add(n))
            else {
                return Ok(Some("ABI node count overflows"));
            };
            n
        }
        AbiPassMode::Indirect {
            metadata_attributes,
            ..
        } => {
            if metadata_attributes.is_some() {
                28
            } else {
                17
            }
        }
    };
    let Some(mode_count) = 4usize.checked_add(mode_nodes) else {
        return Ok(Some("ABI node count overflows"));
    };
    if let Some(e) = add(nodes, mode_count, out)? {
        return Ok(Some(e));
    }
    out.admit(1, size_of::<usize>())?;
    let Some(count) = a.bindings.len().checked_mul(7) else {
        return Ok(Some("ABI node count overflows"));
    };
    add(nodes, count, out)
}
pub(super) fn add<O: ExecutionObserver>(
    nodes: &mut usize,
    count: usize,
    out: &mut Writer<'_, '_, O>,
) -> Budget {
    out.admit(2, 2 * size_of::<usize>())?;
    let Some(next) = nodes.checked_add(count) else {
        return Ok(Some("ABI node count overflows"));
    };
    *nodes = next;
    Ok((next > MAX_NODES).then_some("ABI record count exceeds wire node limit"))
}

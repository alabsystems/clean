// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The original typed reader's acceptance predicates, without constructing
//! another ABI value. Physical ABI validity and producer trust are separate.

use super::arena::{self, Arena, Node};
use super::*;

mod modes;

pub(super) fn validate_signature<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let f = fields(
        arena,
        root,
        &[
            "target",
            "frontend",
            "convention",
            "lowered_convention",
            "source_abi",
            "can_unwind",
            "variadic",
            "fixed_count",
            "arguments",
            "result",
        ],
        out,
    )?;
    target(arena, at(f, 0)?, out)?;
    frontend(arena, at(f, 1)?, out)?;
    text(arena, at(f, 2)?, out)?;
    calling_conv(arena, at(f, 3)?, out)?;
    text(arena, at(f, 4)?, out)?;
    boolean(arena, at(f, 5)?, out)?;
    boolean(arena, at(f, 6)?, out)?;
    unsigned(arena, at(f, 7)?, u64::from(u32::MAX), out)?;
    for argument in list(arena, at(f, 8)?, out)? {
        out.poll()?;
        argument_value(arena, *argument, out)?;
    }
    argument_value(arena, at(f, 9)?, out)
}

fn target<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(
        arena,
        root,
        &[
            "triple",
            "data_layout",
            "abi",
            "cpu",
            "features",
            "target_spec",
            "pointer_bytes",
            "little_endian",
        ],
        out,
    )?;
    for index in 0..4 {
        out.poll()?;
        text(arena, at(f, index)?, out)?;
    }
    for feature in list(arena, at(f, 4)?, out)? {
        out.poll()?;
        text(arena, *feature, out)?;
    }
    text(arena, at(f, 5)?, out)?;
    unsigned(arena, at(f, 6)?, u64::from(u8::MAX), out)?;
    boolean(arena, at(f, 7)?, out)
}

fn frontend<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(arena, root, &["name", "revision"], out)?;
    text(arena, at(f, 0)?, out)?;
    text(arena, at(f, 1)?, out)?;
    Ok(())
}

fn argument_value<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let f = fields(arena, root, &["size", "align", "mode", "bindings"], out)?;
    number(arena, at(f, 0)?, out)?;
    number(arena, at(f, 1)?, out)?;
    modes::mode(arena, at(f, 2)?, out)?;
    for binding in list(arena, at(f, 3)?, out)? {
        out.poll()?;
        binding_value(arena, *binding, out)?;
    }
    Ok(())
}

fn binding_value<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let f = fields(
        arena,
        root,
        &[
            "place",
            "index",
            "source_offset",
            "source_bytes",
            "carrier_offset",
            "carrier_bytes",
        ],
        out,
    )?;
    text(arena, at(f, 0)?, out)?;
    unsigned(arena, at(f, 1)?, u64::from(u32::MAX), out)?;
    choice(
        arena,
        at(f, 0)?,
        &["parameter", "result", "hidden_result"],
        out,
    )?;
    for index in 2..6 {
        out.poll()?;
        number(arena, at(f, index)?, out)?;
    }
    Ok(())
}

fn calling_conv<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let value = text(arena, root, out)?;
    for convention in crate::CallingConv::ALL {
        out.poll()?;
        let expected = match convention {
            crate::CallingConv::C => "ccc",
            crate::CallingConv::Fast => "fastcc",
            crate::CallingConv::Cold => "coldcc",
            crate::CallingConv::Rust => "rustcc",
            crate::CallingConv::Swift => "swiftcc",
            crate::CallingConv::CUnwind => "c_unwindcc",
            crate::CallingConv::SysV64 => "sysv64cc",
            crate::CallingConv::Win64 => "win64cc",
            crate::CallingConv::Aapcs => "aapcscc",
            crate::CallingConv::EfiApi => "efiapicc",
            crate::CallingConv::VectorCall => "vectorcallcc",
            crate::CallingConv::RustCold => "rust_coldcc",
        };
        if arena::literal(value, expected, out)? {
            return Ok(());
        }
    }
    Err(ObservedValueError::UnsupportedValue)
}

fn fields<'a, O: ExecutionObserver>(
    arena: &'a Arena,
    root: usize,
    names: &[&str],
    out: &mut Writer<'_, '_, O>,
) -> R<&'a [(String, usize)]> {
    let Node::Record(fields) = arena.node(root, out)? else {
        return Err(ObservedValueError::UnsupportedValue);
    };
    if fields.len() != names.len() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    for ((name, _), expected) in fields.iter().zip(names) {
        out.poll()?;
        if !arena::literal(name, expected, out)? {
            return Err(ObservedValueError::UnsupportedValue);
        }
    }
    Ok(fields)
}

fn at(fields: &[(String, usize)], index: usize) -> R<usize> {
    fields
        .get(index)
        .map(|(_, value)| *value)
        .ok_or(ObservedValueError::UnsupportedValue)
}

fn text<'a, O: ExecutionObserver>(
    arena: &'a Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R<&'a str> {
    match arena.node(root, out)? {
        Node::Text(value) => Ok(value),
        _ => Err(ObservedValueError::UnsupportedValue),
    }
}

fn list<'a, O: ExecutionObserver>(
    arena: &'a Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R<&'a [usize]> {
    match arena.node(root, out)? {
        Node::List(values) => Ok(values),
        _ => Err(ObservedValueError::UnsupportedValue),
    }
}

fn number<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R<u64> {
    match arena.node(root, out)? {
        Node::Atom(value) => arena::number(value, out),
        _ => Err(ObservedValueError::UnsupportedValue),
    }
}

fn unsigned<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    maximum: u64,
    out: &mut Writer<'_, '_, O>,
) -> R {
    if number(arena, root, out)? > maximum {
        return Err(ObservedValueError::UnsupportedValue);
    }
    Ok(())
}

fn boolean<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let Node::Atom(value) = arena.node(root, out)? else {
        return Err(ObservedValueError::UnsupportedValue);
    };
    if arena::literal(value, "true", out)? || arena::literal(value, "false", out)? {
        Ok(())
    } else {
        Err(ObservedValueError::UnsupportedValue)
    }
}

fn none<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R<bool> {
    match arena.node(root, out)? {
        Node::Atom(value) => arena::literal(value, "none", out),
        _ => Ok(false),
    }
}

fn choice<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    choices: &[&str],
    out: &mut Writer<'_, '_, O>,
) -> R<usize> {
    let value = text(arena, root, out)?;
    for (index, expected) in choices.iter().enumerate() {
        out.poll()?;
        if arena::literal(value, expected, out)? {
            return Ok(index);
        }
    }
    Err(ObservedValueError::UnsupportedValue)
}

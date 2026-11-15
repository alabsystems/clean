// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn attributes<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(
        arena,
        root,
        &[
            "extension",
            "in_reg",
            "no_alias",
            "nonnull",
            "readonly",
            "no_undef",
            "writable",
            "no_free",
            "capture",
            "pointee_size",
            "pointee_align",
        ],
        out,
    )?;
    choice(arena, at(f, 0)?, &["none", "sign", "zero"], out)?;
    for index in 1..8 {
        out.poll()?;
        boolean(arena, at(f, index)?, out)?;
    }
    choice(
        arena,
        at(f, 8)?,
        &["any", "readonly", "address", "none"],
        out,
    )?;
    number(arena, at(f, 9)?, out)?;
    let align = at(f, 10)?;
    if !none(arena, align, out)? {
        number(arena, align, out)?;
    }
    Ok(())
}

fn register<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(arena, root, &["class", "bytes"], out)?;
    choice(arena, at(f, 0)?, &["integer", "float", "vector"], out)?;
    number(arena, at(f, 1)?, out)?;
    Ok(())
}

fn scalar<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(
        arena,
        root,
        &[
            "register",
            "source_offset",
            "source_bytes",
            "value_bits",
            "attributes",
        ],
        out,
    )?;
    register(arena, at(f, 0)?, out)?;
    number(arena, at(f, 1)?, out)?;
    number(arena, at(f, 2)?, out)?;
    unsigned(arena, at(f, 3)?, u64::from(u16::MAX), out)?;
    attributes(arena, at(f, 4)?, out)
}

fn uniform<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(arena, root, &["unit", "total", "consecutive"], out)?;
    register(arena, at(f, 0)?, out)?;
    number(arena, at(f, 1)?, out)?;
    boolean(arena, at(f, 2)?, out)
}

pub(super) fn mode<O: ExecutionObserver>(
    arena: &Arena,
    root: usize,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let Node::Record(pairs) = arena.node(root, out)? else {
        return Err(ObservedValueError::UnsupportedValue);
    };
    let Some((name, kind)) = pairs.first() else {
        return Err(ObservedValueError::UnsupportedValue);
    };
    if !arena::literal(name, "kind", out)? {
        return Err(ObservedValueError::UnsupportedValue);
    }
    match choice(
        arena,
        *kind,
        &["ignore", "direct", "pair", "cast", "indirect"],
        out,
    )? {
        0 => {
            fields(arena, root, &["kind"], out)?;
            Ok(())
        }
        1 => {
            let f = fields(arena, root, &["kind", "scalar"], out)?;
            scalar(arena, at(f, 1)?, out)
        }
        2 => {
            let f = fields(arena, root, &["kind", "first", "second"], out)?;
            scalar(arena, at(f, 1)?, out)?;
            scalar(arena, at(f, 2)?, out)
        }
        3 => cast(arena, root, out),
        4 => indirect(arena, root, out),
        _ => Err(ObservedValueError::UnsupportedValue),
    }
}

fn cast<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(
        arena,
        root,
        &[
            "kind",
            "pad_i32",
            "prefix",
            "rest_offset",
            "rest",
            "attributes",
        ],
        out,
    )?;
    boolean(arena, at(f, 1)?, out)?;
    for element in list(arena, at(f, 2)?, out)? {
        out.poll()?;
        register(arena, *element, out)?;
    }
    let offset = at(f, 3)?;
    if !none(arena, offset, out)? {
        number(arena, offset, out)?;
    }
    uniform(arena, at(f, 4)?, out)?;
    attributes(arena, at(f, 5)?, out)
}

fn indirect<O: ExecutionObserver>(arena: &Arena, root: usize, out: &mut Writer<'_, '_, O>) -> R {
    let f = fields(
        arena,
        root,
        &[
            "kind",
            "attributes",
            "metadata_attributes",
            "on_stack",
            "caller_copy",
        ],
        out,
    )?;
    attributes(arena, at(f, 1)?, out)?;
    let metadata = at(f, 2)?;
    if !none(arena, metadata, out)? {
        attributes(arena, metadata, out)?;
    }
    boolean(arena, at(f, 3)?, out)?;
    boolean(arena, at(f, 4)?, out)
}

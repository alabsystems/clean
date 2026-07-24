// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OCaml Marshal object-graph decoder.
//!
//! Decodes the binary serialization format written by OCaml's
//! `Marshal.to_channel` (the encoding of every Coq `.vo` segment) into a
//! shared DAG: an arena of heap objects ([`MObject`]) plus immediate values
//! ([`MValue`]). Sharing is preserved exactly as in the OCaml heap.
//!
//! Semantics follow the OCaml runtime (`runtime/caml/intext.h`,
//! `runtime/intern.c`) and Coq's own re-implementation
//! (`checker/analyze.ml`, Coq 8.20):
//!
//! - The object table registers only *heap* objects, in the order their
//!   headers are read: blocks with at least one field, strings, doubles,
//!   double arrays, and custom blocks. Immediates (ints), atoms (zero-size
//!   blocks) and code pointers are **not** registered.
//! - `CODE_SHARED*` carries a back-reference `n`; the referenced object is
//!   `current_object_count - n` (relative, not absolute).
//! - Parsing is iterative (explicit field-fill stack), so arbitrarily deep
//!   structures (e.g. long OCaml lists) cannot overflow the Rust stack.

use thiserror::Error;

use super::marshal_reader::Reader;

// ---------------------------------------------------------------------------
// Marshal magic + opcodes (OCaml runtime/caml/intext.h; checker/analyze.ml)
// ---------------------------------------------------------------------------

/// Magic for the "small" marshal header (32-bit lengths).
pub const MARSHAL_MAGIC_SMALL: u32 = 0x8495_A6BE;
/// Magic for the "big" marshal header (64-bit lengths).
pub const MARSHAL_MAGIC_BIG: u32 = 0x8495_A6BF;

const PREFIX_SMALL_BLOCK: u8 = 0x80;
const PREFIX_SMALL_INT: u8 = 0x40;
const PREFIX_SMALL_STRING: u8 = 0x20;

const CODE_INT8: u8 = 0x00;
const CODE_INT16: u8 = 0x01;
const CODE_INT32: u8 = 0x02;
const CODE_INT64: u8 = 0x03;
const CODE_SHARED8: u8 = 0x04;
const CODE_SHARED16: u8 = 0x05;
const CODE_SHARED32: u8 = 0x06;
const CODE_DOUBLE_ARRAY32_LITTLE: u8 = 0x07;
const CODE_BLOCK32: u8 = 0x08;
const CODE_STRING8: u8 = 0x09;
const CODE_STRING32: u8 = 0x0A;
const CODE_DOUBLE_BIG: u8 = 0x0B;
const CODE_DOUBLE_LITTLE: u8 = 0x0C;
const CODE_DOUBLE_ARRAY8_BIG: u8 = 0x0D;
const CODE_DOUBLE_ARRAY8_LITTLE: u8 = 0x0E;
const CODE_DOUBLE_ARRAY32_BIG: u8 = 0x0F;
const CODE_CODEPOINTER: u8 = 0x10;
const CODE_INFIXPOINTER: u8 = 0x11;
const CODE_CUSTOM: u8 = 0x12;
const CODE_BLOCK64: u8 = 0x13;
const CODE_SHARED64: u8 = 0x14;
const CODE_STRING64: u8 = 0x15;
const CODE_DOUBLE_ARRAY64_BIG: u8 = 0x16;
const CODE_DOUBLE_ARRAY64_LITTLE: u8 = 0x17;
const CODE_CUSTOM_LEN: u8 = 0x18;
const CODE_CUSTOM_FIXED: u8 = 0x19;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from parsing OCaml marshal data.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MarshalError {
    #[error("invalid marshal magic: got 0x{got:08X}")]
    InvalidMagic { got: u32 },

    #[error("unexpected end of data at offset {offset} (need {need} bytes, have {have})")]
    UnexpectedEof {
        offset: usize,
        need: usize,
        have: usize,
    },

    #[error("unknown opcode 0x{opcode:02X} at offset {offset}")]
    UnknownOpcode { opcode: u8, offset: usize },

    #[error("shared back-reference {back} out of range (objects so far: {table_size}) at offset {offset}")]
    SharedOutOfRange {
        back: u64,
        table_size: usize,
        offset: usize,
    },

    #[error("unsupported feature: {feature} at offset {offset}")]
    Unsupported { feature: String, offset: usize },
}

pub type MarshalResult<T> = Result<T, MarshalError>;

// ---------------------------------------------------------------------------
// Value representation: immediates + object arena (shared DAG)
// ---------------------------------------------------------------------------

/// An immediate marshal value or a reference into the object arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MValue {
    /// OCaml unboxed integer (63-bit on 64-bit platforms).
    Int(i64),
    /// Zero-size block ("atom"): a constant constructor with a tag, or an
    /// empty array. Never registered in the sharing table.
    Atom(u8),
    /// Reference to a heap object in [`MarshalDag::objects`].
    Ref(usize),
    /// Code pointer (opaque; never appears in `.vo` kernel data).
    Code(u32),
}

/// A heap object in the shared DAG.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum MObject {
    /// Structured block with tag and at least one field.
    Block { tag: u8, fields: Vec<MValue> },
    /// OCaml string (bytes, not necessarily UTF-8).
    Str(Vec<u8>),
    /// Boxed IEEE 754 double.
    Double(f64),
    /// Unboxed float array.
    DoubleArray(Vec<f64>),
    /// Custom block (e.g. `_j` = boxed int64). `data` is the raw serialized
    /// payload as read from the stream.
    Custom { ident: Vec<u8>, data: Vec<u8> },
}

/// A fully decoded marshal value graph: `root` plus the object arena.
#[derive(Clone, Debug)]
pub struct MarshalDag {
    /// Heap objects in registration order (the marshal sharing table).
    pub objects: Vec<MObject>,
    /// The root value.
    pub root: MValue,
    /// Total bytes consumed from the input, including the header.
    pub bytes_consumed: usize,
}

impl MarshalDag {
    /// Resolve a value to its heap object, if it is a reference.
    #[must_use]
    pub fn get(&self, v: MValue) -> Option<&MObject> {
        match v {
            MValue::Ref(i) => self.objects.get(i),
            _ => None,
        }
    }

    /// View a value as a block `(tag, fields)`. Atoms are zero-field blocks.
    #[must_use]
    pub fn block(&self, v: MValue) -> Option<(u8, &[MValue])> {
        match v {
            MValue::Atom(tag) => Some((tag, &[])),
            MValue::Ref(i) => match self.objects.get(i) {
                Some(MObject::Block { tag, fields }) => Some((*tag, fields.as_slice())),
                _ => None,
            },
            _ => None,
        }
    }

    /// Field `i` of a block value.
    #[must_use]
    pub fn field(&self, v: MValue, i: usize) -> Option<MValue> {
        self.block(v).and_then(|(_, fields)| fields.get(i).copied())
    }

    /// View a value as an OCaml int.
    #[must_use]
    pub fn int(&self, v: MValue) -> Option<i64> {
        match v {
            MValue::Int(i) => Some(i),
            _ => None,
        }
    }

    /// View a value as string bytes.
    #[must_use]
    pub fn str_bytes(&self, v: MValue) -> Option<&[u8]> {
        match self.get(v) {
            Some(MObject::Str(b)) => Some(b.as_slice()),
            _ => None,
        }
    }

    /// View a value as a lossy UTF-8 string.
    #[must_use]
    pub fn string_lossy(&self, v: MValue) -> Option<String> {
        self.str_bytes(v)
            .map(|b| String::from_utf8_lossy(b).into_owned())
    }

    /// Iterate an OCaml list (`[] = Int 0`, `x :: t = Block(0, [x, t])`).
    /// Returns `None` if the value is not list-shaped.
    #[must_use]
    pub fn list(&self, v: MValue) -> Option<Vec<MValue>> {
        let mut out = Vec::new();
        let mut cur = v;
        loop {
            match cur {
                MValue::Int(0) => return Some(out),
                _ => {
                    let (tag, fields) = self.block(cur)?;
                    if tag != 0 || fields.len() != 2 {
                        return None;
                    }
                    out.push(fields[0]);
                    cur = fields[1];
                }
            }
        }
    }

    /// View an OCaml `option` (`None = Int 0`, `Some x = Block(0, [x])`).
    /// Outer `None` means the value is not option-shaped.
    #[must_use]
    pub fn opt(&self, v: MValue) -> Option<Option<MValue>> {
        match v {
            MValue::Int(0) => Some(None),
            _ => match self.block(v) {
                Some((0, [x])) => Some(Some(*x)),
                _ => None,
            },
        }
    }

    /// View a value as an OCaml array (block tag 0; empty array = Atom 0).
    #[must_use]
    pub fn array(&self, v: MValue) -> Option<&[MValue]> {
        match self.block(v) {
            Some((0, fields)) => Some(fields),
            _ => None,
        }
    }

    /// Decode a custom block as a boxed int64 (identifier `_j`).
    #[must_use]
    pub fn custom_int64(&self, v: MValue) -> Option<i64> {
        match self.get(v) {
            Some(MObject::Custom { ident, data }) if ident == b"_j" && data.len() == 8 => {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(data);
                Some(i64::from_be_bytes(buf))
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Cap on the pre-allocated object-table capacity (defensive; the real count
/// is taken from the header but must not trigger huge allocations up front).
const MAX_PREALLOC_OBJECTS: usize = 1 << 22;

/// Parse one complete marshaled value starting at `data[0]`.
///
/// The value must start with the marshal magic (small or big format).
/// Trailing bytes after the value (e.g. a `.vo` segment digest) are ignored;
/// [`MarshalDag::bytes_consumed`] reports where the value ended.
///
/// # Errors
///
/// Returns `MarshalError` on invalid magic, truncated data, unknown opcodes,
/// or out-of-range shared back-references.
pub fn parse_marshal(data: &[u8]) -> MarshalResult<MarshalDag> {
    let mut reader = Reader::new(data);
    let num_objects = parse_header(&mut reader)?;
    parse_body(&mut reader, num_objects)
}

/// Parse the header (magic + lengths). Returns the declared object count.
fn parse_header(reader: &mut Reader<'_>) -> MarshalResult<usize> {
    let magic = reader.read_u32_be()?;
    if magic == MARSHAL_MAGIC_SMALL {
        let _data_len = reader.read_u32_be()?;
        let num_objects = reader.read_u32_be()? as usize;
        let _size_32 = reader.read_u32_be()?;
        let _size_64 = reader.read_u32_be()?;
        Ok(num_objects)
    } else if magic == MARSHAL_MAGIC_BIG {
        let _reserved = reader.read_u32_be()?;
        let _data_len = reader.read_u64_be()?;
        let num_objects = reader.read_u64_be()? as usize;
        let _whsize = reader.read_u64_be()?;
        Ok(num_objects)
    } else {
        Err(MarshalError::InvalidMagic { got: magic })
    }
}

/// One item read from the stream: its value, plus the field count when the
/// item opened a new block whose fields follow.
struct Item {
    value: MValue,
    open_block: Option<(usize, usize)>, // (arena index, field count > 0)
}

/// A pending block whose fields are still being filled.
struct Frame {
    obj: usize,
    remaining: usize,
}

/// Iterative field-fill loop (mirrors `checker/analyze.ml:parse`).
fn parse_body(reader: &mut Reader<'_>, num_objects: usize) -> MarshalResult<MarshalDag> {
    let mut objects: Vec<MObject> = Vec::with_capacity(num_objects.min(MAX_PREALLOC_OBJECTS));
    let mut frames: Vec<Frame> = Vec::new();
    let mut root: Option<MValue> = None;

    loop {
        let item = parse_item(reader, &mut objects)?;

        // Deposit the value in its destination.
        match frames.last_mut() {
            None => root = Some(item.value),
            Some(frame) => {
                frame.remaining -= 1;
                let idx = frame.obj;
                if let MObject::Block { fields, .. } = &mut objects[idx] {
                    fields.push(item.value);
                }
            }
        }

        // A new non-empty block starts filling its own fields next.
        if let Some((obj, len)) = item.open_block {
            frames.push(Frame {
                obj,
                remaining: len,
            });
        } else {
            while frames.last().is_some_and(|f| f.remaining == 0) {
                frames.pop();
            }
        }

        if frames.is_empty() {
            if let Some(root) = root {
                return Ok(MarshalDag {
                    objects,
                    root,
                    bytes_consumed: reader.pos,
                });
            }
        }
    }
}

/// Read a single item header (and any inline payload).
fn parse_item(reader: &mut Reader<'_>, objects: &mut Vec<MObject>) -> MarshalResult<Item> {
    let offset = reader.pos;
    let code = reader.read_u8()?;

    if code >= PREFIX_SMALL_BLOCK {
        let tag = code & 0x0F;
        let len = ((code >> 4) & 0x07) as usize;
        return Ok(make_block(objects, tag, len));
    }
    if code >= PREFIX_SMALL_INT {
        return Ok(imm(MValue::Int(i64::from(code & 0x3F))));
    }
    if code >= PREFIX_SMALL_STRING {
        let len = (code & 0x1F) as usize;
        let bytes = reader.read_bytes(len)?.to_vec();
        return Ok(register(objects, MObject::Str(bytes)));
    }

    match code {
        CODE_INT8 => Ok(imm(MValue::Int(i64::from(reader.read_u8()? as i8)))),
        CODE_INT16 => Ok(imm(MValue::Int(i64::from(reader.read_u16_be()? as i16)))),
        CODE_INT32 => Ok(imm(MValue::Int(i64::from(reader.read_i32_be()?)))),
        CODE_INT64 => Ok(imm(MValue::Int(reader.read_i64_be()?))),
        CODE_SHARED8 => shared(objects, u64::from(reader.read_u8()?), offset),
        CODE_SHARED16 => shared(objects, u64::from(reader.read_u16_be()?), offset),
        CODE_SHARED32 => shared(objects, u64::from(reader.read_u32_be()?), offset),
        CODE_SHARED64 => shared(objects, reader.read_u64_be()?, offset),
        CODE_BLOCK32 => {
            let header = reader.read_u32_be()?;
            let tag = (header & 0xFF) as u8;
            let len = (header >> 10) as usize;
            Ok(make_block(objects, tag, len))
        }
        CODE_BLOCK64 => {
            let header = reader.read_u64_be()?;
            let tag = (header & 0xFF) as u8;
            let len = (header >> 10) as usize;
            Ok(make_block(objects, tag, len))
        }
        CODE_STRING8 => {
            let len = reader.read_u8()? as usize;
            let bytes = reader.read_bytes(len)?.to_vec();
            Ok(register(objects, MObject::Str(bytes)))
        }
        CODE_STRING32 => {
            let len = reader.read_u32_be()? as usize;
            let bytes = reader.read_bytes(len)?.to_vec();
            Ok(register(objects, MObject::Str(bytes)))
        }
        CODE_STRING64 => {
            let len = reader.read_u64_be()? as usize;
            let bytes = reader.read_bytes(len)?.to_vec();
            Ok(register(objects, MObject::Str(bytes)))
        }
        CODE_DOUBLE_BIG => {
            let f = reader.read_f64_big()?;
            Ok(register(objects, MObject::Double(f)))
        }
        CODE_DOUBLE_LITTLE => {
            let f = reader.read_f64_little()?;
            Ok(register(objects, MObject::Double(f)))
        }
        CODE_DOUBLE_ARRAY8_BIG | CODE_DOUBLE_ARRAY8_LITTLE => {
            let len = reader.read_u8()? as usize;
            double_array(reader, objects, len, code == CODE_DOUBLE_ARRAY8_BIG)
        }
        CODE_DOUBLE_ARRAY32_BIG | CODE_DOUBLE_ARRAY32_LITTLE => {
            let len = reader.read_u32_be()? as usize;
            double_array(reader, objects, len, code == CODE_DOUBLE_ARRAY32_BIG)
        }
        CODE_DOUBLE_ARRAY64_BIG | CODE_DOUBLE_ARRAY64_LITTLE => {
            let len = reader.read_u64_be()? as usize;
            double_array(reader, objects, len, code == CODE_DOUBLE_ARRAY64_BIG)
        }
        CODE_CODEPOINTER => {
            let addr = reader.read_u32_be()?;
            let _digest = reader.read_bytes(16)?;
            Ok(imm(MValue::Code(addr)))
        }
        CODE_INFIXPOINTER => Err(MarshalError::Unsupported {
            feature: "CODE_INFIXPOINTER (marshaled closure)".to_string(),
            offset,
        }),
        CODE_CUSTOM | CODE_CUSTOM_FIXED | CODE_CUSTOM_LEN => {
            parse_custom(reader, objects, code, offset)
        }
        _ => Err(MarshalError::UnknownOpcode {
            opcode: code,
            offset,
        }),
    }
}

fn imm(value: MValue) -> Item {
    Item {
        value,
        open_block: None,
    }
}

/// Register a completed heap object in the sharing table.
fn register(objects: &mut Vec<MObject>, obj: MObject) -> Item {
    let idx = objects.len();
    objects.push(obj);
    imm(MValue::Ref(idx))
}

/// Allocate a block. Zero-size blocks are atoms (never registered).
fn make_block(objects: &mut Vec<MObject>, tag: u8, len: usize) -> Item {
    if len == 0 {
        return imm(MValue::Atom(tag));
    }
    let idx = objects.len();
    objects.push(MObject::Block {
        tag,
        fields: Vec::with_capacity(len.min(1 << 16)),
    });
    Item {
        value: MValue::Ref(idx),
        open_block: Some((idx, len)),
    }
}

/// Resolve a shared back-reference: `objects.len() - back`.
fn shared(objects: &[MObject], back: u64, offset: usize) -> MarshalResult<Item> {
    let len = objects.len() as u64;
    if back == 0 || back > len {
        return Err(MarshalError::SharedOutOfRange {
            back,
            table_size: objects.len(),
            offset,
        });
    }
    Ok(imm(MValue::Ref((len - back) as usize)))
}

fn double_array(
    reader: &mut Reader<'_>,
    objects: &mut Vec<MObject>,
    len: usize,
    big: bool,
) -> MarshalResult<Item> {
    let mut arr = Vec::with_capacity(len.min(1 << 16));
    for _ in 0..len {
        arr.push(if big {
            reader.read_f64_big()?
        } else {
            reader.read_f64_little()?
        });
    }
    Ok(register(objects, MObject::DoubleArray(arr)))
}

/// Parse a custom block. Payload sizes for the fixed-size customs come from
/// the OCaml runtime's custom operations (`_j` = int64: 8 bytes, `_i` =
/// int32: 4 bytes, `_n` = nativeint: 1-byte tag + 4 or 8 bytes). Generic
/// `CODE_CUSTOM_LEN` payloads of unknown identifiers cannot be skipped
/// (their byte length is only known to the matching deserializer), so they
/// are reported as unsupported rather than guessed.
fn parse_custom(
    reader: &mut Reader<'_>,
    objects: &mut Vec<MObject>,
    code: u8,
    offset: usize,
) -> MarshalResult<Item> {
    let mut ident = Vec::new();
    loop {
        let b = reader.read_u8()?;
        if b == 0 {
            break;
        }
        ident.push(b);
    }
    if code == CODE_CUSTOM_LEN {
        // Skip the size_32 (u32) + size_64 (u64) allocation hints.
        let _ = reader.read_u32_be()?;
        let _ = reader.read_u64_be()?;
    }
    let data: Vec<u8> = match ident.as_slice() {
        b"_j" => reader.read_bytes(8)?.to_vec(),
        b"_i" => reader.read_bytes(4)?.to_vec(),
        b"_n" => {
            let tag = reader.read_u8()?;
            let n = match tag {
                1 => 4,
                2 => 8,
                _ => {
                    return Err(MarshalError::Unsupported {
                        feature: format!("nativeint custom tag {tag}"),
                        offset,
                    })
                }
            };
            let mut v = vec![tag];
            v.extend_from_slice(reader.read_bytes(n)?);
            v
        }
        other => {
            return Err(MarshalError::Unsupported {
                feature: format!("custom block '{}'", String::from_utf8_lossy(other)),
                offset,
            })
        }
    };
    Ok(register(objects, MObject::Custom { ident, data }))
}

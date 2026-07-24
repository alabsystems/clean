// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser scaffold for Coq `.vo` files.
//!
//! Coq artifacts are OCaml-marshaled binary blobs. This scaffold only validates
//! the outer marshal framing and preserves the raw payload for future decoding
//! into Gallina terms and declarations.

use super::{CoqImportError, CoqImportResult};
use std::fs;
use std::path::Path;

/// OCaml Marshal magic used by Coq artifact blobs.
pub const OCAML_MARSHAL_MAGIC: u32 = 0x8495_A6BE;
/// OCaml Marshal header size in bytes.
pub const OCAML_MARSHAL_HEADER_LEN: usize = 20;

/// Parsed `.vo` file scaffold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoFile {
    pub header: VoHeader,
    pub sections: Vec<VoSection>,
}

/// Outer marshal header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoHeader {
    pub magic: u32,
    pub data_len: u32,
    pub num_objects: u32,
    pub size32: u32,
    pub size64: u32,
}

/// One raw section captured by the scaffold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoSection {
    pub kind: VoSectionKind,
    pub offset: usize,
    pub bytes: Vec<u8>,
}

/// Outer `.vo` scaffold sections.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VoSectionKind {
    MarshalPayload,
    Trailer,
}

/// Parse a `.vo` byte buffer.
pub fn parse_vo(bytes: &[u8]) -> CoqImportResult<VoFile> {
    let mut cursor = Cursor::new(bytes);
    let header = VoHeader {
        magic: cursor.read_u32_be("marshal magic")?,
        data_len: cursor.read_u32_be("marshal data length")?,
        num_objects: cursor.read_u32_be("marshal object count")?,
        size32: cursor.read_u32_be("marshal size32")?,
        size64: cursor.read_u32_be("marshal size64")?,
    };
    if header.magic != OCAML_MARSHAL_MAGIC {
        return Err(CoqImportError::InvalidMarshalMagic {
            expected: OCAML_MARSHAL_MAGIC,
            actual: header.magic,
        });
    }

    let payload_len = usize::try_from(header.data_len).expect("u32 fits in usize");
    if cursor.remaining() < payload_len {
        return Err(CoqImportError::TruncatedMarshalPayload {
            declared: payload_len,
            available: cursor.remaining(),
        });
    }

    let payload = cursor.take(payload_len, "marshal payload")?.to_vec();
    let mut sections = vec![VoSection {
        kind: VoSectionKind::MarshalPayload,
        offset: OCAML_MARSHAL_HEADER_LEN,
        bytes: payload,
    }];
    if cursor.remaining() > 0 {
        let offset = cursor.offset;
        sections.push(VoSection {
            kind: VoSectionKind::Trailer,
            offset,
            bytes: cursor.take(cursor.remaining(), "trailer")?.to_vec(),
        });
    }
    Ok(VoFile { header, sections })
}

/// Parse a `.vo` file from disk.
pub fn parse_vo_file(path: impl AsRef<Path>) -> CoqImportResult<VoFile> {
    let bytes = fs::read(path)?;
    parse_vo(&bytes)
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.offset)
    }

    fn read_u32_be(&mut self, context: &'static str) -> CoqImportResult<u32> {
        let bytes = self.take(4, context)?;
        Ok(u32::from_be_bytes(
            bytes.try_into().expect("slice length is 4"),
        ))
    }

    fn take(&mut self, len: usize, context: &'static str) -> CoqImportResult<&'a [u8]> {
        if self.remaining() < len {
            return Err(CoqImportError::UnexpectedEof { context });
        }
        let start = self.offset;
        let end = start + len;
        self.offset = end;
        Ok(&self.bytes[start..end])
    }
}

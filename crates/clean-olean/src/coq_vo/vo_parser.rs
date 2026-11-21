// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq `.vo` container (`ObjFile`) parser.
//!
//! Layout (Coq 8.20 `lib/objFile.ml`; unchanged in Rocq 9.x apart from the
//! version number):
//!
//! ```text
//! int32   magic = 0x436F7121 ("Coq!")
//! int32   version (e.g. 82000 for Coq 8.20)
//! int64   absolute position of the segment summary
//! ...     segments: OCaml-marshaled data, each followed by a 16-byte MD5
//! summary: int32 count, then per segment:
//!          int32 name_len | name | int64 pos | int64 len | 16-byte MD5
//! ```
//!
//! Segment names in a stdlib `.vo`: `summary`, `library`, `opaques`,
//! `vmlibrary` (plus `tasks`/`universes` in `.vio`-style files).

use std::path::Path;

use super::library;
use super::marshal_parser::{parse_marshal, MarshalDag, MarshalError};
use thiserror::Error;

/// ObjFile magic: `"Coq!"` big-endian.
pub const VO_MAGIC: u32 = 0x436F_7121;

/// Maximum .vo file size we accept (2 GB). Beyond this, something is wrong.
const MAX_VO_SIZE: usize = 2 * 1024 * 1024 * 1024;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from parsing `.vo` files.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum VoParseError {
    #[error("invalid .vo magic: expected 0x{VO_MAGIC:08X} ('Coq!'), got 0x{got:08X}")]
    InvalidMagic { got: u32 },

    #[error("file too large: {size} bytes exceeds limit of {limit}")]
    FileTooLarge { size: usize, limit: usize },

    #[error("truncated .vo file reading {context} at offset {offset}")]
    Truncated { context: String, offset: usize },

    #[error("segment {name}: range {pos}+{len} exceeds file size {file_size}")]
    SegmentOutOfBounds {
        name: String,
        pos: u64,
        len: u64,
        file_size: usize,
    },

    #[error("segment {name} not present (have: {available:?})")]
    MissingSegment {
        name: String,
        available: Vec<String>,
    },

    #[error("marshal error in segment {segment}: {source}")]
    Marshal {
        segment: String,
        source: MarshalError,
    },

    #[error("unexpected structure in {context}: {message}")]
    Structure { context: String, message: String },

    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

pub type VoResult<T> = Result<T, VoParseError>;

// ---------------------------------------------------------------------------
// Segment table
// ---------------------------------------------------------------------------

/// One entry of the `.vo` segment summary.
#[derive(Clone, Debug)]
pub struct VoSegment {
    /// Segment identifier (`summary`, `library`, `opaques`, `vmlibrary`, ...).
    pub name: String,
    /// Absolute byte offset of the marshaled data.
    pub pos: u64,
    /// Byte length of the marshaled data (excluding the trailing MD5).
    pub len: u64,
    /// MD5 digest of the segment bytes.
    pub hash: [u8; 16],
}

/// A parsed `.vo` container: version + segment directory over borrowed bytes.
#[derive(Clone, Debug)]
pub struct VoObjFile<'a> {
    data: &'a [u8],
    /// `vo_version` from the header (82000 for Coq 8.20).
    pub version: i32,
    /// Segment directory in file order.
    pub segments: Vec<VoSegment>,
}

impl<'a> VoObjFile<'a> {
    /// Parse the container header and segment summary.
    ///
    /// # Errors
    ///
    /// Returns `VoParseError` on bad magic, truncation, or out-of-range
    /// segment table entries.
    pub fn parse(data: &'a [u8]) -> VoResult<Self> {
        if data.len() > MAX_VO_SIZE {
            return Err(VoParseError::FileTooLarge {
                size: data.len(),
                limit: MAX_VO_SIZE,
            });
        }
        let magic = read_u32(data, 0, "magic")?;
        if magic != VO_MAGIC {
            return Err(VoParseError::InvalidMagic { got: magic });
        }
        let version = read_u32(data, 4, "version")? as i32;
        let summary_pos = read_u64(data, 8, "summary position")? as usize;

        let count = read_u32(data, summary_pos, "segment count")? as usize;
        let mut pos = summary_pos + 4;
        let mut segments = Vec::with_capacity(count.min(64));
        for i in 0..count {
            let ctx = format!("segment summary #{i}");
            let name_len = read_u32(data, pos, &ctx)? as usize;
            pos += 4;
            let name_bytes =
                data.get(pos..pos + name_len)
                    .ok_or_else(|| VoParseError::Truncated {
                        context: ctx.clone(),
                        offset: pos,
                    })?;
            let name = String::from_utf8_lossy(name_bytes).into_owned();
            pos += name_len;
            let seg_pos = read_u64(data, pos, &ctx)?;
            let seg_len = read_u64(data, pos + 8, &ctx)?;
            let hash_bytes =
                data.get(pos + 16..pos + 32)
                    .ok_or_else(|| VoParseError::Truncated {
                        context: ctx.clone(),
                        offset: pos + 16,
                    })?;
            let mut hash = [0u8; 16];
            hash.copy_from_slice(hash_bytes);
            pos += 32;

            let in_bounds = seg_pos
                .checked_add(seg_len)
                .is_some_and(|end| end <= data.len() as u64);
            if !in_bounds {
                return Err(VoParseError::SegmentOutOfBounds {
                    name,
                    pos: seg_pos,
                    len: seg_len,
                    file_size: data.len(),
                });
            }
            segments.push(VoSegment {
                name,
                pos: seg_pos,
                len: seg_len,
                hash,
            });
        }
        segments.sort_by_key(|s| s.pos);
        Ok(Self {
            data,
            version,
            segments,
        })
    }

    /// Look up a segment by name.
    #[must_use]
    pub fn segment(&self, name: &str) -> Option<&VoSegment> {
        self.segments.iter().find(|s| s.name == name)
    }

    /// Decode a segment's marshaled object graph.
    ///
    /// # Errors
    ///
    /// Returns `MissingSegment` if the name is absent, or a wrapped
    /// `MarshalError` if decoding fails.
    pub fn read_segment(&self, name: &str) -> VoResult<MarshalDag> {
        let seg = self
            .segment(name)
            .ok_or_else(|| VoParseError::MissingSegment {
                name: name.to_string(),
                available: self.segments.iter().map(|s| s.name.clone()).collect(),
            })?;
        let start = seg.pos as usize;
        let end = start + seg.len as usize;
        // Range validated at parse time.
        let bytes = &self.data[start..end];
        parse_marshal(bytes).map_err(|e| VoParseError::Marshal {
            segment: name.to_string(),
            source: e,
        })
    }
}

fn read_u32(data: &[u8], offset: usize, context: &str) -> VoResult<u32> {
    data.get(offset..offset + 4)
        .map(|b| u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
        .ok_or_else(|| VoParseError::Truncated {
            context: context.to_string(),
            offset,
        })
}

fn read_u64(data: &[u8], offset: usize, context: &str) -> VoResult<u64> {
    data.get(offset..offset + 8)
        .map(|b| u64::from_be_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
        .ok_or_else(|| VoParseError::Truncated {
            context: context.to_string(),
            offset,
        })
}

// ---------------------------------------------------------------------------
// High-level file summary (declaration census) — used by the scale pipeline
// ---------------------------------------------------------------------------

/// A parsed `.vo` file overview.
#[derive(Clone, Debug)]
pub struct VoFile {
    /// Header description (e.g. "Coq! v82000").
    pub magic: String,
    /// Logical library name (e.g. "Coq.Init.Logic").
    pub library_name: Option<String>,
    /// Dependencies (logical names of required libraries).
    pub dependencies: Vec<String>,
    /// Segment directory (name, offset, length).
    pub segments: Vec<VoSegment>,
    /// Declarations extracted from the library segment.
    pub declarations: Vec<VoDeclaration>,
}

/// A declaration extracted from a .vo file.
#[derive(Clone, Debug)]
pub struct VoDeclaration {
    /// Fully-qualified name (e.g. "Coq.Init.Logic.eq_sym").
    pub name: String,
    /// Kind of declaration.
    pub kind: VoDeclKind,
    /// Whether this declaration has an opaque (Qed) proof body.
    pub is_opaque: bool,
    /// Source library logical name.
    pub library: String,
}

/// Kind of declaration in a .vo file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum VoDeclKind {
    /// A constant (theorem, lemma, definition, axiom).
    Constant,
    /// An inductive type block.
    Inductive,
    /// A module or module type.
    Module,
    /// A universe constraint.
    Universe,
    /// An unknown/opaque declaration kind.
    Other,
}

/// Parse a `.vo` file and extract its declaration census from the real
/// `library` segment structure (no heuristics).
///
/// # Errors
///
/// Returns `VoParseError` on invalid container framing, marshal failures, or
/// unexpected library structure.
pub fn parse_vo_file(data: &[u8]) -> VoResult<VoFile> {
    let obj = VoObjFile::parse(data)?;
    let magic = format!("Coq! v{}", obj.version);

    let summary_dag = obj.read_segment("summary")?;
    let summary = library::read_summary(&summary_dag)?;

    let library_dag = obj.read_segment("library")?;
    let lib = library::read_library(&library_dag, &summary.name)?;

    let mut declarations = Vec::new();
    for c in &lib.constants {
        declarations.push(VoDeclaration {
            name: c.qualified.clone(),
            kind: VoDeclKind::Constant,
            is_opaque: c.def == library::ConstantDefKind::OpaqueDef,
            library: summary.name.clone(),
        });
    }
    for ind in &lib.inductives {
        declarations.push(VoDeclaration {
            name: ind.qualified.clone(),
            kind: VoDeclKind::Inductive,
            is_opaque: false,
            library: summary.name.clone(),
        });
    }
    for m in &lib.modules {
        declarations.push(VoDeclaration {
            name: m.clone(),
            kind: VoDeclKind::Module,
            is_opaque: false,
            library: summary.name.clone(),
        });
    }

    Ok(VoFile {
        magic,
        library_name: Some(summary.name),
        dependencies: summary.deps,
        segments: obj.segments,
        declarations,
    })
}

/// Parse a `.vo` file from disk.
///
/// # Errors
///
/// Returns `VoParseError::Io` if the file cannot be read, else as
/// [`parse_vo_file`].
pub fn parse_vo_path(path: &Path) -> VoResult<VoFile> {
    let data = std::fs::read(path)?;
    parse_vo_file(&data)
}

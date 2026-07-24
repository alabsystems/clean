// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level (universe level) parsing from .olean files
//!
//! Lean 4 universe levels are represented as an inductive type:
//!
//! ```text
//! inductive Level where
//!   | zero                                -- tag 0
//!   | succ   (pred : Level)               -- tag 1, 1 field
//!   | max    (l r : Level)                -- tag 2, 2 fields
//!   | imax   (l r : Level)                -- tag 3, 2 fields
//!   | param  (name : Name)                -- tag 4, 1 field
//!   | mvar   (mvarId : LMVarId)           -- tag 5, 1 field
//! ```
//!
//! In the compacted region, these are constructor objects with the appropriate
//! number of pointer fields.

use crate::error::{OleanError, OleanResult};
use crate::region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};
use std::fmt;

/// Level tags (constructor indices) from the .olean format.
pub mod level_tags {
    /// Zero level (Prop).
    pub const ZERO: u8 = 0;
    /// Successor level.
    pub const SUCC: u8 = 1;
    /// Maximum of two levels.
    pub const MAX: u8 = 2;
    /// Impredicative maximum.
    pub const IMAX: u8 = 3;
    /// Universe parameter.
    pub const PARAM: u8 = 4;
    /// Universe metavariable.
    pub const MVAR: u8 = 5;
}

/// A parsed universe level.
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future Lean 4 universe level
/// constructors without breaking downstream code. Always include a wildcard arm
/// in match expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParsedLevel {
    /// Level 0 (Prop)
    Zero,
    /// Successor level
    Succ(Box<ParsedLevel>),
    /// Maximum of two levels
    Max(Box<ParsedLevel>, Box<ParsedLevel>),
    /// Impredicative maximum
    IMax(Box<ParsedLevel>, Box<ParsedLevel>),
    /// Universe parameter
    Param(String),
    /// Metavariable (shouldn't appear in .olean)
    MVar(String),
}

impl fmt::Display for ParsedLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParsedLevel::Zero => write!(f, "0"),
            ParsedLevel::Succ(l) => {
                // Try to collapse successive Succs into a number
                let mut level = l.as_ref();
                let mut count = 1u64;
                while let ParsedLevel::Succ(inner) = level {
                    count += 1;
                    level = inner;
                }
                if let ParsedLevel::Zero = level {
                    write!(f, "{count}")
                } else {
                    write!(f, "(succ {l})")
                }
            }
            ParsedLevel::Max(l, r) => write!(f, "(max {l} {r})"),
            ParsedLevel::IMax(l, r) => write!(f, "(imax {l} {r})"),
            ParsedLevel::Param(n) => write!(f, "{n}"),
            ParsedLevel::MVar(n) => write!(f, "?{n}"),
        }
    }
}

impl ParsedLevel {
    /// Count the depth of the level (for detecting infinite loops)
    pub fn depth(&self) -> usize {
        match self {
            ParsedLevel::Zero | ParsedLevel::Param(_) | ParsedLevel::MVar(_) => 0,
            ParsedLevel::Succ(l) => 1 + l.depth(),
            ParsedLevel::Max(l, r) | ParsedLevel::IMax(l, r) => 1 + l.depth().max(r.depth()),
        }
    }
}

impl<'a> CompactedRegion<'a> {
    /// Read a Level object at a file offset
    pub fn read_level_at(&self, offset: usize) -> OleanResult<ParsedLevel> {
        self.read_level_at_depth(offset, 0)
    }

    pub(crate) fn read_level_at_depth(
        &self,
        offset: usize,
        depth: usize,
    ) -> OleanResult<ParsedLevel> {
        if depth > 1000 {
            return Err(OleanError::Region("Level depth limit exceeded".into()));
        }

        let header = self.read_header_at(offset)?;

        let field_base = offset + 8;
        let _scalar_base = field_base + header.other as usize * 8;

        match header.tag {
            level_tags::ZERO => {
                // Level.zero: constructor 0, 0 fields
                // But may have a Data scalar field
                Ok(ParsedLevel::Zero)
            }

            level_tags::SUCC => {
                // Level.succ: constructor 1, 1 field (pred)
                // Layout: header(8) + data(8) + pred(8)
                // The Data field comes before the pred pointer
                Self::require_level_fields(&header, offset, 1)?;
                let pred_ptr = self.read_u64_at(field_base)?; // Skip header
                let pred = self.resolve_level_ptr(pred_ptr, depth + 1)?;
                Ok(ParsedLevel::Succ(Box::new(pred)))
            }

            level_tags::MAX => {
                // Level.max: constructor 2, 2 fields (l, r)
                // Layout: header(8) + data(8) + l(8) + r(8)
                Self::require_level_fields(&header, offset, 2)?;
                let l_ptr = self.read_u64_at(field_base)?;
                let r_ptr = self.read_u64_at(field_base + 8)?;
                let l = self.resolve_level_ptr(l_ptr, depth + 1)?;
                let r = self.resolve_level_ptr(r_ptr, depth + 1)?;
                Ok(ParsedLevel::Max(Box::new(l), Box::new(r)))
            }

            level_tags::IMAX => {
                // Level.imax: constructor 3, 2 fields (l, r)
                // Layout: header(8) + data(8) + l(8) + r(8)
                Self::require_level_fields(&header, offset, 2)?;
                let l_ptr = self.read_u64_at(field_base)?;
                let r_ptr = self.read_u64_at(field_base + 8)?;
                let l = self.resolve_level_ptr(l_ptr, depth + 1)?;
                let r = self.resolve_level_ptr(r_ptr, depth + 1)?;
                Ok(ParsedLevel::IMax(Box::new(l), Box::new(r)))
            }

            level_tags::PARAM => {
                // Level.param: constructor 4, 1 field (name)
                // Layout: header(8) + data(8) + name(8)
                Self::require_level_fields(&header, offset, 1)?;
                let name_ptr = self.read_u64_at(field_base)?;
                let name = if is_scalar(name_ptr) {
                    // Name.anonymous encoded as scalar 0
                    String::new()
                } else if is_ptr(name_ptr) {
                    let name_off = self.ptr_to_offset(name_ptr)?;
                    self.read_name_at(name_off)?
                } else {
                    String::new()
                };
                Ok(ParsedLevel::Param(name))
            }

            level_tags::MVAR => {
                // Level.mvar: constructor 5, 1 field (mvarId)
                // Layout: header(8) + data(8) + mvarId(8)
                Self::require_level_fields(&header, offset, 1)?;
                let id_ptr = self.read_u64_at(field_base)?;
                let name = if is_scalar(id_ptr) {
                    format!("mvar_{}", unbox_scalar(id_ptr))
                } else if is_ptr(id_ptr) {
                    let name_off = self.ptr_to_offset(id_ptr)?;
                    // LMVarId contains a Name
                    self.read_name_at(name_off)?
                } else {
                    "?".to_string()
                };
                Ok(ParsedLevel::MVar(name))
            }

            _ => Err(OleanError::InvalidObjectTag {
                tag: header.tag,
                offset,
            }),
        }
    }

    /// Validate that a `Level` constructor object declares enough pointer
    /// fields to satisfy its tag before any field is read.
    ///
    /// Lean's compacted region stores the number of pointer fields in the
    /// object header's `other` byte. Each level constructor has a fixed
    /// arity (`succ`/`param`/`mvar` = 1, `max`/`imax` = 2). A malformed or
    /// truncated `.olean` can present a level tag whose `other` is smaller
    /// than its arity; without this check the reader would interpret bytes
    /// belonging to an adjacent object (or scalar payload) as a child level
    /// pointer, silently fabricating a level. Fail closed with a typed
    /// [`OleanError::Region`] instead.
    ///
    /// # ENSURES
    /// - Returns `Ok(())` iff `header.other >= expected`.
    /// - Returns `OleanError::Region` describing the mismatch otherwise.
    fn require_level_fields(
        header: &crate::region::ObjectHeader,
        offset: usize,
        expected: u8,
    ) -> OleanResult<()> {
        if header.other < expected {
            return Err(OleanError::Region(format!(
                "malformed Level: tag {} at offset {} declares {} field(s), expected at least {}",
                header.tag, offset, header.other, expected
            )));
        }
        Ok(())
    }

    /// Resolve a level pointer (handling scalars for Level.zero)
    pub(crate) fn resolve_level_ptr(&self, ptr: u64, depth: usize) -> OleanResult<ParsedLevel> {
        if is_scalar(ptr) {
            // Level.zero is often encoded as scalar 0 (pointer value 1)
            // Similar to Name.anonymous
            let val = unbox_scalar(ptr);
            if val == 0 {
                return Ok(ParsedLevel::Zero);
            }
            // Could be a numeric level directly
            return Err(OleanError::Region(format!(
                "Unexpected scalar level value: {val}"
            )));
        }

        if !is_ptr(ptr) {
            return Ok(ParsedLevel::Zero);
        }

        let offset = self.ptr_to_offset(ptr)?;
        self.read_level_at_depth(offset, depth)
    }

    /// Find all Level objects in the file
    pub fn find_all_levels(&self) -> Vec<(usize, ParsedLevel)> {
        let mut levels = Vec::new();

        // Start at offset 64 (after header + root pointer)
        let mut offset = 64;
        while offset + 24 < self.data.len() {
            if let Ok(header) = self.read_header_at(offset) {
                // Check for Level constructors (tags 0-5 with appropriate field counts)
                let is_level = matches!(
                    (header.tag, header.other),
                    (level_tags::ZERO, 0)
                        | (level_tags::SUCC | level_tags::PARAM | level_tags::MVAR, 1)
                        | (level_tags::MAX | level_tags::IMAX, 2)
                );

                if is_level {
                    if let Ok(level) = self.read_level_at(offset) {
                        // Only include non-trivial levels
                        if !matches!(level, ParsedLevel::Zero) || header.tag == level_tags::ZERO {
                            levels.push((offset, level));
                        }
                    }
                }
            }
            offset += 8;
        }

        levels
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_lean_lib_path() -> Option<std::path::PathBuf> {
        let home = std::env::var("HOME").ok()?;
        let elan_path = std::path::PathBuf::from(home).join(".elan/toolchains");

        if elan_path.exists() {
            for entry in std::fs::read_dir(&elan_path).ok()? {
                let entry = entry.ok()?;
                let name = entry.file_name();
                if name.to_string_lossy().contains("lean4") {
                    return Some(entry.path().join("lib/lean"));
                }
            }
        }
        None
    }

    #[test]
    fn test_parsed_level_to_string() {
        assert_eq!(ParsedLevel::Zero.to_string(), "0");
        assert_eq!(
            ParsedLevel::Succ(Box::new(ParsedLevel::Zero)).to_string(),
            "1"
        );
        assert_eq!(
            ParsedLevel::Succ(Box::new(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))).to_string(),
            "2"
        );
        assert_eq!(ParsedLevel::Param("u".to_string()).to_string(), "u");
        assert_eq!(
            ParsedLevel::Max(
                Box::new(ParsedLevel::Param("u".to_string())),
                Box::new(ParsedLevel::Param("v".to_string()))
            )
            .to_string(),
            "(max u v)"
        );
    }

    /// Write a Level object header (rc=0, cs_sz=0) at the end of `data`,
    /// returning the offset the object starts at. Caller appends fields.
    fn push_level_header(data: &mut Vec<u8>, tag: u8, other: u8) -> usize {
        // Align to 8 bytes (object headers are 8-aligned in the region).
        while !data.len().is_multiple_of(8) {
            data.push(0);
        }
        let offset = data.len();
        data.extend_from_slice(&0i32.to_le_bytes()); // rc
        data.extend_from_slice(&0u16.to_le_bytes()); // cs_sz
        data.push(other); // other = pointer field count
        data.push(tag); // tag
        offset
    }

    /// A `Max` object that lies about its field count (`other = 1` instead of
    /// 2) must fail closed with a typed `Region` error rather than reading the
    /// adjacent object's bytes as its second child level.
    #[test]
    fn test_read_level_max_insufficient_fields_returns_region_error() {
        let base_addr = 0x1_0000u64;
        let mut data = vec![0u8; 64]; // header + root pointer placeholder

        // Max with other=1 but only room for (at most) one field before EOF.
        let max_off = push_level_header(&mut data, level_tags::MAX, 1);
        // Provide a single field word so the read would "succeed" silently
        // without the field-count guard, proving the guard is what rejects it.
        data.extend_from_slice(&Level0Scalar.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let err = region
            .read_level_at(max_off)
            .expect_err("Max with other<2 must be rejected");
        assert!(
            matches!(err, OleanError::Region(msg) if msg.contains("malformed Level")),
            "expected malformed-Level Region error"
        );
    }

    /// Scalar 0 (boxed `Level.zero`) used as a placeholder field value.
    #[allow(non_upper_case_globals)]
    const Level0Scalar: u64 = 1;

    /// An `IMax` object declaring zero fields must also fail closed.
    #[test]
    fn test_read_level_imax_zero_fields_returns_region_error() {
        let base_addr = 0x2_0000u64;
        let mut data = vec![0u8; 64];
        let imax_off = push_level_header(&mut data, level_tags::IMAX, 0);
        // Trailing bytes that would be misread as level pointers.
        data.extend_from_slice(&Level0Scalar.to_le_bytes());
        data.extend_from_slice(&Level0Scalar.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let err = region
            .read_level_at(imax_off)
            .expect_err("IMax with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)));
    }

    /// A `Succ` object declaring zero fields must fail closed rather than
    /// reading whatever follows as its predecessor.
    #[test]
    fn test_read_level_succ_zero_fields_returns_region_error() {
        let base_addr = 0x3_0000u64;
        let mut data = vec![0u8; 64];
        let succ_off = push_level_header(&mut data, level_tags::SUCC, 0);
        data.extend_from_slice(&Level0Scalar.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let err = region
            .read_level_at(succ_off)
            .expect_err("Succ with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)));
    }

    /// A `Param` object declaring zero fields must fail closed.
    #[test]
    fn test_read_level_param_zero_fields_returns_region_error() {
        let base_addr = 0x4_0000u64;
        let mut data = vec![0u8; 64];
        let param_off = push_level_header(&mut data, level_tags::PARAM, 0);
        data.extend_from_slice(&Level0Scalar.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let err = region
            .read_level_at(param_off)
            .expect_err("Param with other=0 must be rejected");
        assert!(matches!(err, OleanError::Region(_)));
    }

    /// A well-formed `Max(zero, zero)` (other=2) still parses successfully —
    /// the field-count guard rejects only genuinely malformed objects.
    #[test]
    fn test_read_level_max_correct_fields_still_parses() {
        let base_addr = 0x5_0000u64;
        let mut data = vec![0u8; 64];
        let max_off = push_level_header(&mut data, level_tags::MAX, 2);
        // Both children are scalar Level.zero (boxed 0 = pointer value 1).
        data.extend_from_slice(&Level0Scalar.to_le_bytes());
        data.extend_from_slice(&Level0Scalar.to_le_bytes());

        let region = CompactedRegion::new(&data, base_addr);
        let parsed = region
            .read_level_at(max_off)
            .expect("well-formed Max(zero, zero) should parse");
        assert!(
            matches!(&parsed, ParsedLevel::Max(l, r)
                if matches!(**l, ParsedLevel::Zero) && matches!(**r, ParsedLevel::Zero)),
            "expected Max(Zero, Zero), got {parsed:?}"
        );
    }

    /// Deeply-nested `Max`/`IMax`/`Succ` levels written by the exporter must
    /// round-trip back to the same structure, exercising the recursive
    /// pointer-following path well below the depth limit.
    #[test]
    fn test_deeply_nested_max_imax_roundtrips() {
        use crate::OleanExporter;
        use clean_kernel::level::Level;
        use clean_kernel::name::Name;

        // Build: max(imax(u, v), succ(succ(0))).
        //
        // `imax(u, v)` survives the kernel's smart constructor as a genuine
        // `IMax` node because `v` is a bare param (not provably nonzero) and
        // `u != v`. Wrapping it under a `Max` whose other arm is `succ(succ 0)`
        // keeps the IMax deeply nested, exercising recursive pointer-following
        // through both `Max` and `IMax` arms.
        let imax_node = Level::imax(
            Level::param(Name::from_string("u")),
            Level::param(Name::from_string("v")),
        );
        // Sanity: confirm the constructor did not collapse it to Max.
        assert!(
            matches!(imax_node, Level::IMax(_, _)),
            "test setup expected an IMax node, got {imax_node:?}"
        );
        let original = Level::max(imax_node, Level::succ(Level::succ(Level::zero())));

        let mut exp = OleanExporter::new();
        let ptr = exp.write_level(&original);
        let region = CompactedRegion::new(&exp.data, exp.base_addr);
        let offset = region
            .ptr_to_offset(ptr)
            .expect("exported level pointer should resolve");
        let parsed = region
            .read_level_at(offset)
            .expect("deeply nested level should parse");

        let expected = ParsedLevel::Max(
            Box::new(ParsedLevel::IMax(
                Box::new(ParsedLevel::Param("u".to_string())),
                Box::new(ParsedLevel::Param("v".to_string())),
            )),
            Box::new(ParsedLevel::Succ(Box::new(ParsedLevel::Succ(Box::new(
                ParsedLevel::Zero,
            ))))),
        );
        assert_eq!(parsed, expected, "deeply nested level mismatch");
    }

    /// A long chain of `Max` nodes (each declaring 2 fields) round-trips,
    /// confirming the recursive reader handles substantial nesting without
    /// tripping the field-count guard or the depth limit.
    #[test]
    fn test_long_max_chain_roundtrips() {
        use crate::OleanExporter;
        use clean_kernel::level::Level;
        use clean_kernel::name::Name;

        // Left-leaning chain: max(max(max(u0, u1), u2), u3) ... 32 deep.
        let mut original = Level::param(Name::from_string("u0"));
        for i in 1..32 {
            original = Level::max(original, Level::param(Name::from_string(&format!("u{i}"))));
        }

        let mut exp = OleanExporter::new();
        let ptr = exp.write_level(&original);
        let region = CompactedRegion::new(&exp.data, exp.base_addr);
        let offset = region.ptr_to_offset(ptr).expect("level pointer resolves");
        let parsed = region
            .read_level_at(offset)
            .expect("long Max chain should parse");

        // Depth of a left-leaning chain of 31 Max nodes is 31.
        assert_eq!(parsed.depth(), 31, "unexpected nesting depth");
        // The right spine of the outermost Max must be Param("u31").
        match &parsed {
            ParsedLevel::Max(_, r) => {
                assert_eq!(**r, ParsedLevel::Param("u31".to_string()));
            }
            other => panic!("expected outer Max, got {other:?}"),
        }
    }

    #[test]
    fn test_find_levels_in_prelude() {
        let Some(lib_path) = get_lean_lib_path() else {
            eprintln!("Skipping test: Lean 4 not found");
            return;
        };

        let prelude_path = lib_path.join("Init/Prelude.olean");
        if !prelude_path.exists() {
            eprintln!("Skipping test: Init/Prelude.olean not found at {prelude_path:?}");
            return;
        }

        let bytes = std::fs::read(&prelude_path).expect("Failed to read file");
        let header = crate::parse_header(&bytes).expect("Failed to parse header");
        let _region = CompactedRegion::new(&bytes, header.base_addr);

        // This is exploratory - we won't find levels easily with the simple scan
        // because tags 0-5 conflict with Name constructors and other types
        // We'll primarily read levels when traversing from known expression objects

        // Try to read a few levels from known structures
        println!("Searching for level-like objects in Init/Prelude.olean...");
    }
}

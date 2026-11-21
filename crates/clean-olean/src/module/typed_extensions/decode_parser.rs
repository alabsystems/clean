// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    invalid, Cell, CompactedRegion, OleanResult, Reader, TypedModuleLayout, MAX_TOTAL_ARRAY_ITEMS,
};
use crate::import::ParserToken;
use crate::region::is_ptr;

impl CompactedRegion<'_> {
    /// Stable Lean stores ScopedEnvExtension.Entry ParserExtension.OLeanEntry.
    pub(crate) fn stable_parser_tokens(&self, entries: u64) -> OleanResult<Vec<ParserToken>> {
        let reader = Reader {
            region: self,
            layout: TypedModuleLayout::LeanV2,
            legacy: false,
            remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
        };
        let mut tokens = Vec::new();
        for ptr in reader.array(entries)? {
            let (scope, inner) = match reader.parser_tag(ptr)? {
                0 => (None, reader.field(reader.object(ptr, 0, 1, 0)?, 0)?),
                1 => {
                    let at = reader.object(ptr, 1, 2, 0)?;
                    (
                        Some(reader.name(reader.field(at, 0)?)?),
                        reader.field(at, 1)?,
                    )
                }
                tag => {
                    return Err(invalid(format!(
                        "unknown scoped parser extension tag {tag}"
                    )))
                }
            };
            match reader.parser_tag(inner)? {
                0 => {
                    let at = reader.object(inner, 0, 1, 0)?;
                    let text = reader.string(reader.field(at, 0)?)?;
                    tokens.push(ParserToken { scope, text });
                }
                // kind, category, and parser declarations do not reserve tokens.
                1 => {
                    reader.object(inner, 1, 1, 0)?;
                }
                2 => {
                    reader.object(inner, 2, 2, 1)?;
                }
                3 => {
                    reader.object(inner, 3, 3, 0)?;
                }
                tag => return Err(invalid(format!("unknown parser extension entry tag {tag}"))),
            }
        }
        Ok(tokens)
    }
}

impl Reader<'_, '_> {
    fn parser_tag(&self, pointer: u64) -> OleanResult<u8> {
        if !is_ptr(pointer) {
            return Err(invalid("parser extension entry is not a constructor"));
        }
        let offset = self.region.ptr_to_offset(pointer)?;
        Ok(self.region.read_header_at(offset)?.tag)
    }
}

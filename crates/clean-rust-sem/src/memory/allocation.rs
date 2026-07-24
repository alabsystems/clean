// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::AllocId;
use crate::types::RustType;
use serde::{Deserialize, Serialize};

/// Memory allocation metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Allocation {
    /// Unique ID.
    pub id: AllocId,
    /// Size in bytes.
    pub size: usize,
    /// Alignment requirement.
    pub align: usize,
    /// Whether allocation is still valid.
    pub valid: bool,
    /// Whether the contents were conservatively invalidated by an opaque effect.
    pub tainted: bool,
    /// The data stored (as bytes).
    pub data: Vec<u8>,
    /// Optional type information.
    pub ty: Option<RustType>,
    /// Runtime slice length metadata for wide pointers into this allocation.
    pub slice_len: Option<usize>,
}

impl Allocation {
    /// Create a new allocation.
    pub fn new(id: AllocId, size: usize, align: usize) -> Self {
        Self {
            id,
            size,
            align,
            valid: true,
            tainted: false,
            data: vec![0; size],
            ty: None,
            slice_len: None,
        }
    }

    /// Check if an offset is in bounds.
    pub fn in_bounds(&self, offset: u64, size: usize) -> bool {
        usize::try_from(offset)
            .ok()
            .and_then(|o| o.checked_add(size))
            .is_some_and(|end| end <= self.size)
    }

    /// Check if offset is aligned for the given size.
    pub fn is_aligned(&self, offset: u64, align: usize) -> bool {
        offset.is_multiple_of(align as u64)
    }

    pub fn set_type(&mut self, ty: RustType) {
        self.slice_len = self.slice_len.or_else(|| slice_len_from_type(&ty));
        self.ty = Some(ty);
    }

    pub fn slice_len(&self) -> Option<usize> {
        self.slice_len
            .or_else(|| self.ty.as_ref().and_then(slice_len_from_type))
    }
}

fn slice_len_from_type(ty: &RustType) -> Option<usize> {
    match ty {
        RustType::Array { len, .. } => len.as_usize(&std::collections::HashMap::new()),
        _ => None,
    }
}

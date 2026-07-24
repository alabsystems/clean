// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Analysis and debugging utilities for module data.
//!
//! Provides `analyze_root` and `analyze_array` methods on CompactedRegion
//! for inspecting .olean file structure.

use crate::error::OleanResult;
use crate::region::{is_ptr, is_scalar, tags, unbox_scalar, CompactedRegion, ObjectHeader};

/// Analysis of the root object
#[derive(Debug)]
pub struct RootAnalysis {
    pub root_ptr: u64,
    pub root_offset: usize,
    pub tag: u8,
    pub num_fields: u8,
    pub cs_sz: u16,
    pub field_info: Vec<(usize, u64, String)>,
}

/// Analysis of an array in the module
#[derive(Debug)]
pub struct ArrayAnalysis {
    pub size: usize,
    pub sample_elements: Vec<ElementInfo>,
}

/// Information about an array element
#[derive(Debug)]
pub struct ElementInfo {
    pub index: usize,
    pub tag: u8,
    pub num_fields: u8,
    pub description: String,
}

impl<'a> CompactedRegion<'a> {
    /// Get basic statistics about the root object
    ///
    /// # REQUIRES
    /// - Root pointer must reference a valid ModuleData object.
    ///
    /// # ENSURES
    /// - Returns a `RootAnalysis` summary for debugging.
    pub fn analyze_root(&self) -> OleanResult<RootAnalysis> {
        let root_ptr = self.root_ptr()?;

        if is_scalar(root_ptr) {
            return Err(crate::error::OleanError::Region(format!(
                "Root is scalar: {}",
                unbox_scalar(root_ptr)
            )));
        }

        if !is_ptr(root_ptr) {
            return Err(crate::error::OleanError::Region("Root is null".into()));
        }

        let root_offset = self.ptr_to_offset(root_ptr)?;
        let header = self.read_header_at(root_offset)?;

        // Read the first several pointers after the root header
        let mut field_info = Vec::new();
        for i in 0..8 {
            let field_offset = root_offset + 8 + i * 8;
            if field_offset + 8 > self.data.len() {
                break;
            }
            let ptr = self.read_u64_at(field_offset)?;
            let kind = self.describe_ptr(ptr);
            field_info.push((i, ptr, kind));
        }

        Ok(RootAnalysis {
            root_ptr,
            root_offset,
            tag: header.tag,
            num_fields: header.other,
            cs_sz: header.cs_sz,
            field_info,
        })
    }

    /// Describe a pointer value for analysis output.
    fn describe_ptr(&self, ptr: u64) -> String {
        if is_scalar(ptr) {
            format!("scalar({})", unbox_scalar(ptr))
        } else if is_ptr(ptr) {
            if let Ok(off) = self.ptr_to_offset(ptr) {
                if let Ok(h) = self.read_header_at(off) {
                    format!("ptr->tag{}/{}fields", h.tag, h.other)
                } else {
                    "ptr->invalid".to_string()
                }
            } else {
                "ptr->out_of_bounds".to_string()
            }
        } else {
            "null".to_string()
        }
    }

    /// Analyze an array at a given pointer
    ///
    /// # REQUIRES
    /// - `ptr` is a pointer to an Array object in this region.
    /// - `max_samples` bounds the number of sampled elements.
    ///
    /// # ENSURES
    /// - Returns `ArrayAnalysis` with size and sampled elements.
    /// - Returns `OleanError` if `ptr` is invalid or not an array.
    pub fn analyze_array(&self, ptr: u64, max_samples: usize) -> OleanResult<ArrayAnalysis> {
        if !is_ptr(ptr) {
            return Err(crate::error::OleanError::Region("Not a pointer".into()));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Err(crate::error::OleanError::Region(format!(
                "Not an array (tag={})",
                header.tag
            )));
        }

        let size = self.read_usize_at(offset + 8, "Extension entry sample")?;
        self.validate_array_bounds(offset, size)?;
        let actual_sample_count = size.min(max_samples);
        let mut sample_elements = Vec::new();

        for i in 0..actual_sample_count {
            let elem_offset = self.array_elem_offset(offset, i, "Extension entry sample")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            sample_elements.push(self.analyze_element(i, elem_ptr));
        }

        Ok(ArrayAnalysis {
            size,
            sample_elements,
        })
    }

    /// Analyze a single array element for debugging.
    fn analyze_element(&self, index: usize, elem_ptr: u64) -> ElementInfo {
        let description = self.describe_element(elem_ptr);
        let (tag, num_fields) = self.element_header(elem_ptr);
        ElementInfo {
            index,
            tag,
            num_fields,
            description,
        }
    }

    /// Describe an array element value for analysis output.
    fn describe_element(&self, elem_ptr: u64) -> String {
        if is_scalar(elem_ptr) {
            return format!("scalar({})", unbox_scalar(elem_ptr));
        }
        if !is_ptr(elem_ptr) {
            return "null".to_string();
        }
        let Ok(elem_off) = self.ptr_to_offset(elem_ptr) else {
            return "out_of_bounds".to_string();
        };
        let Ok(elem_header) = self.read_header_at(elem_off) else {
            return "invalid".to_string();
        };
        Self::describe_object(self, elem_off, &elem_header)
    }

    /// Describe an object by its header for analysis output.
    fn describe_object(&self, offset: usize, header: &ObjectHeader) -> String {
        match header.tag {
            tags::STRING => {
                if let Ok(s) = self.read_lean_string_at(offset) {
                    format!("String(\"{}\")", s.chars().take(30).collect::<String>())
                } else {
                    "String(?)".to_string()
                }
            }
            0..=7 if header.other <= 2 => {
                if let Ok(name) = self.read_name_at(offset) {
                    format!("ctor{}/{}(name={})", header.tag, header.other, name)
                } else {
                    format!("ctor{}/{}", header.tag, header.other)
                }
            }
            0..=7 => format!("ctor{}/{}", header.tag, header.other),
            tags::ARRAY | tags::STRUCT_ARRAY => {
                let arr_size = self.read_u64_at(offset + 8).unwrap_or(0);
                format!("Array(size={arr_size})")
            }
            _ => format!("tag{}/{}", header.tag, header.other),
        }
    }

    /// Extract tag and num_fields from a pointer element.
    fn element_header(&self, elem_ptr: u64) -> (u8, u8) {
        if !is_ptr(elem_ptr) {
            return (255, 0);
        }
        let Ok(elem_off) = self.ptr_to_offset(elem_ptr) else {
            return (255, 0);
        };
        match self.read_header_at(elem_off) {
            Ok(h) => (h.tag, h.other),
            Err(_) => (255, 0),
        }
    }
}

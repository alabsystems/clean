// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! High-level export API, finalization, and payload support.

use super::OleanExporter;
use crate::error::OleanResult;
use crate::header::{OleanHeader, HEADER_SIZE};
use crate::module::ParsedExtension;
use crate::payload::{encode_clean_payload, CleanPayload};
use clean_kernel::env::{ConstantInfo, Environment};
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use clean_kernel::name::Name;

impl OleanExporter {
    /// Finalize and return the .olean file bytes
    ///
    /// # REQUIRES
    /// - `git_hash` is <= 40 bytes ASCII (will be padded/truncated by header).
    ///
    /// # ENSURES
    /// - Returns bytes with a serialized header and root pointer set.
    /// - Header base address matches `self.base_addr`.
    pub fn finalize(mut self, git_hash: &str) -> OleanResult<Vec<u8>> {
        // Create header
        let header = OleanHeader::new(git_hash, self.base_addr)?;
        let header_bytes = header.serialize();

        // Copy header to start of data
        self.data[0..HEADER_SIZE].copy_from_slice(&header_bytes);

        Ok(self.data)
    }

    /// Set the root pointer (module data offset)
    ///
    /// # REQUIRES
    /// - `offset` points to a valid object inside the compacted region.
    ///
    /// # ENSURES
    /// - Writes the root pointer into the header root slot.
    pub fn set_root(&mut self, offset: usize) {
        let ptr = self.offset_to_ptr(offset);
        self.data[HEADER_SIZE..HEADER_SIZE + 8].copy_from_slice(&ptr.to_le_bytes());
    }

    /// Export a minimal .olean file with just imports and constant names
    ///
    /// This is a simplified export that doesn't include full constant definitions,
    /// but is sufficient for dependency tracking.
    ///
    /// # REQUIRES
    /// - `git_hash` is <= 40 bytes ASCII (header pads/truncates).
    ///
    /// # ENSURES
    /// - Returns a valid .olean byte vector with imports/constNames populated.
    /// - Does not serialize constant definitions.
    pub fn export_minimal(
        imports: &[(&str, bool)],
        const_names: &[&str],
        entries: &[ParsedExtension],
        git_hash: &str,
    ) -> OleanResult<Vec<u8>> {
        let mut exporter = Self::new();

        // Write module data
        let module_offset = exporter.write_module_data(imports, const_names, entries);
        exporter.set_root(module_offset);

        exporter.finalize(git_hash)
    }

    /// Export an .olean file with a clean payload appended after the compacted region.
    ///
    /// The payload carries serialized kernel objects so dependent modules can
    /// load definitions without needing full Lean 4 ConstantInfo serialization.
    ///
    /// # REQUIRES
    /// - `git_hash` is <= 40 bytes ASCII (header pads/truncates).
    /// - `payload` is a valid `CleanPayload`.
    ///
    /// # ENSURES
    /// - Returns valid .olean bytes with a clean payload footer.
    /// - The payload footer is detectable by `decode_clean_payload`.
    pub fn export_with_payload(
        imports: &[(&str, bool)],
        const_names: &[&str],
        entries: &[ParsedExtension],
        git_hash: &str,
        payload: &CleanPayload,
    ) -> OleanResult<Vec<u8>> {
        let mut exporter = Self::new();

        let module_offset =
            exporter.write_module_data_with_payload(imports, const_names, entries, payload)?;
        exporter.set_root(module_offset);

        let mut bytes = exporter.finalize(git_hash)?;
        let payload_bytes = encode_clean_payload(payload)?;
        bytes.extend_from_slice(&payload_bytes);
        Ok(bytes)
    }

    /// Export an .olean file with full constants from an Environment
    ///
    /// This exports both the Lean 4 format constants array and the constNames,
    /// enabling full round-trip and Lean 4 compatibility.
    ///
    /// # REQUIRES
    /// - `env` contains the constants to export.
    /// - `git_hash` is <= 40 bytes ASCII (header pads/truncates).
    ///
    /// # ENSURES
    /// - Returns valid .olean bytes with populated constants array.
    /// - constNames matches the constants in the environment.
    pub fn export_with_env(
        env: &Environment,
        imports: &[(&str, bool)],
        entries: &[ParsedExtension],
        git_hash: &str,
    ) -> OleanResult<Vec<u8>> {
        let mut exporter = Self::new();

        let module_offset = exporter.write_module_data_with_env(env, imports, entries)?;
        exporter.set_root(module_offset);

        exporter.finalize(git_hash)
    }

    /// Export an .olean file with full constants and clean payload
    ///
    /// Combines the Lean 4 format constants with the clean payload for
    /// maximum compatibility.
    ///
    /// # REQUIRES
    /// - `env` contains the constants to export.
    /// - `git_hash` is <= 40 bytes ASCII (header pads/truncates).
    /// - `payload` is a valid `CleanPayload`.
    ///
    /// # ENSURES
    /// - Returns valid .olean bytes with both constants array and clean payload.
    pub fn export_with_env_and_payload(
        env: &Environment,
        imports: &[(&str, bool)],
        entries: &[ParsedExtension],
        git_hash: &str,
        payload: &CleanPayload,
    ) -> OleanResult<Vec<u8>> {
        let mut exporter = Self::new();

        let module_offset = exporter.write_module_data_with_env(env, imports, entries)?;
        exporter.set_root(module_offset);

        let mut bytes = exporter.finalize(git_hash)?;
        let payload_bytes = encode_clean_payload(payload)?;
        bytes.extend_from_slice(&payload_bytes);
        Ok(bytes)
    }
}

enum PayloadConstantRef<'a> {
    Constant(&'a ConstantInfo),
    Inductive(&'a InductiveVal),
    Constructor(&'a ConstructorVal),
    Recursor(&'a RecursorVal),
}

impl OleanExporter {
    /// Write a ModuleData structure with constants populated from a clean payload.
    ///
    /// ModuleData fields (from Lean 4 Environment.lean:122-141):
    /// 0: imports (Array Import)
    /// 1: constNames (Array Name) - from `const_names` parameter
    /// 2: constants (Array ConstantInfo) - from `payload`
    /// 3: extraConstNames (Array Name) - from `payload`
    /// 4: entries (Array (Name × Array EnvExtensionEntry))
    ///
    /// This uses `const_names` ordering to keep constNames and constants aligned.
    fn write_module_data_with_payload(
        &mut self,
        imports: &[(&str, bool)],
        const_names: &[&str],
        entries: &[ParsedExtension],
        payload: &CleanPayload,
    ) -> OleanResult<usize> {
        use std::collections::{HashMap, HashSet};

        // Write imports array
        let import_ptrs: Vec<u64> = imports
            .iter()
            .map(|(name, rt_only)| {
                let off = self.write_import(name, *rt_only);
                self.offset_to_ptr(off)
            })
            .collect();
        let imports_array_offset = self.write_array(&import_ptrs);
        let imports_ptr = self.offset_to_ptr(imports_array_offset);

        let mut payload_map: HashMap<String, PayloadConstantRef<'_>> =
            HashMap::with_capacity(payload.total_constants());
        for info in &payload.constants {
            payload_map.insert(info.name.to_string(), PayloadConstantRef::Constant(info));
        }
        for ind in &payload.inductives {
            payload_map.insert(ind.name.to_string(), PayloadConstantRef::Inductive(ind));
        }
        for ctor in &payload.constructors {
            payload_map.insert(ctor.name.to_string(), PayloadConstantRef::Constructor(ctor));
        }
        for rec in &payload.recursors {
            payload_map.insert(rec.name.to_string(), PayloadConstantRef::Recursor(rec));
        }

        let mut const_name_set = HashSet::with_capacity(const_names.len());
        let mut name_ptrs = Vec::with_capacity(const_names.len());
        let mut const_ptrs = Vec::with_capacity(const_names.len());
        for &name in const_names {
            const_name_set.insert(name.to_string());
            let name_offset = self.write_name(name);
            name_ptrs.push(self.offset_to_ptr(name_offset));

            let const_ptr = match payload_map.get(name) {
                Some(PayloadConstantRef::Constant(info)) => self.write_constant_info(info)?,
                Some(PayloadConstantRef::Inductive(ind)) => self.write_inductive_info(ind)?,
                Some(PayloadConstantRef::Constructor(ctor)) => self.write_constructor_info(ctor)?,
                Some(PayloadConstantRef::Recursor(rec)) => self.write_recursor_info(rec)?,
                None => {
                    return Err(crate::error::OleanError::Region(format!(
                        "payload missing constant info for {name}"
                    )))
                }
            };
            const_ptrs.push(const_ptr);
        }

        let names_array_offset = self.write_array(&name_ptrs);
        let names_ptr = self.offset_to_ptr(names_array_offset);

        let consts_array_offset = self.write_array(&const_ptrs);
        let consts_ptr = self.offset_to_ptr(consts_array_offset);

        let extra_names = collect_extra_const_names_from_payload(payload, &const_name_set);
        let extra_name_ptrs: Vec<u64> = extra_names
            .iter()
            .map(|name| {
                let off = self.write_kernel_name(name);
                self.offset_to_ptr(off)
            })
            .collect();
        let extra_names_array_offset = self.write_array(&extra_name_ptrs);
        let extra_names_ptr = self.offset_to_ptr(extra_names_array_offset);

        let entries_ptr = if entries.is_empty() {
            let empty_array_offset = self.write_array(&[]);
            self.offset_to_ptr(empty_array_offset)
        } else {
            self.write_parsed_extension_entries(entries)
        };

        // Write ModuleData constructor (5 pointer fields)
        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 5, 0);
        self.write_u64(imports_ptr); // imports
        self.write_u64(names_ptr); // constNames
        self.write_u64(consts_ptr); // constants
        self.write_u64(extra_names_ptr); // extraConstNames
        self.write_u64(entries_ptr); // entries

        Ok(offset)
    }
}

fn collect_extra_const_names_from_payload(
    payload: &CleanPayload,
    const_names: &std::collections::HashSet<String>,
) -> Vec<Name> {
    let mut extra = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let suffixes = ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType"];

    for ind in &payload.inductives {
        for suffix in &suffixes {
            let name = ind.name.clone().str(suffix);
            let name_str = name.to_string();
            if const_names.contains(&name_str) {
                continue;
            }
            if !seen.insert(name_str) {
                continue;
            }
            extra.push(name);
        }
    }

    extra
}

impl Default for OleanExporter {
    fn default() -> Self {
        Self::new()
    }
}

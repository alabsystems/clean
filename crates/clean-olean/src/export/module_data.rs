// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ModuleData assembly, import writing, and extension entry serialization.

use super::OleanExporter;
use crate::error::OleanResult;
use crate::module::{
    DefinitionSafety, ParsedExtension, ParsedExtensionEntry, ParsedExtensionEntryData,
};
use crate::region::tags;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

impl OleanExporter {
    /// Write an Array object (tag 246)
    ///
    /// Array layout:
    /// - header (8 bytes)
    /// - size (8 bytes)
    /// - capacity (8 bytes)
    /// - elements\[size\] (each 8 bytes)
    ///
    /// # REQUIRES
    /// - `elements` are valid pointer/scalar values for the target runtime.
    ///
    /// # ENSURES
    /// - Returns the offset of the new array object.
    /// - Array length equals `elements.len()`.
    pub(crate) fn write_array(&mut self, elements: &[u64]) -> usize {
        self.align8();
        let offset = self.current_offset();

        // Array header (tag 246, other = 0)
        self.write_header(tags::ARRAY, 0, 0);

        // Size
        self.write_u64(elements.len() as u64);

        // Capacity (same as size for compacted)
        self.write_u64(elements.len() as u64);

        // Elements
        for &elem in elements {
            self.write_u64(elem);
        }

        offset
    }

    /// Write raw object bytes into the compacted region.
    ///
    /// NOTE: Raw bytes may contain absolute pointers from another base address.
    /// Only pointer-free payloads (e.g., scalar arrays) are safe to re-emit.
    pub(super) fn write_raw_object(&mut self, bytes: &[u8]) -> usize {
        self.align8();
        let offset = self.current_offset();
        self.data.extend_from_slice(bytes);
        self.align8();
        offset
    }

    /// Write an Import object
    ///
    /// Import is a constructor with:
    /// - tag = 0
    /// - 1 pointer field (module_name: Name)
    /// - 1 scalar byte (runtime_only: Bool)
    ///
    /// The Bool is stored as a scalar byte after the pointer fields, not as a tagged pointer.
    pub(super) fn write_import(&mut self, module_name: &str, runtime_only: bool) -> usize {
        let name_offset = self.write_name(module_name);
        let name_ptr = self.offset_to_ptr(name_offset);

        self.align8();
        let offset = self.current_offset();

        // Import constructor (tag 0, 1 pointer field)
        self.write_header(0, 1, 0);
        self.write_u64(name_ptr);
        // Bool as scalar byte after the pointer field
        self.data.push(u8::from(runtime_only));
        // Pad to alignment
        self.align8();

        offset
    }

    /// Write a minimal ModuleData structure
    ///
    /// ModuleData fields (from Lean 4 Environment.lean:122-141):
    /// 0: imports (Array Import)
    /// 1: constNames (Array Name)
    /// 2: constants (Array ConstantInfo) - empty for now
    /// 3: extraConstNames (Array Name) - empty
    /// 4: entries (Array (Name × Array EnvExtensionEntry))
    ///
    /// Note: isModule (Bool) is a scalar field stored after pointer fields.
    /// We don't write it as it defaults to true for standard .olean files.
    ///
    /// # REQUIRES
    /// - `imports` and `const_names` use Lean-style module/name strings.
    ///
    /// # ENSURES
    /// - Returns the offset of the ModuleData object.
    /// - Populates imports and constNames arrays; other arrays are empty.
    pub(crate) fn write_module_data(
        &mut self,
        imports: &[(&str, bool)],
        const_names: &[&str],
        entries: &[ParsedExtension],
    ) -> usize {
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

        // Write constant names array
        let name_ptrs: Vec<u64> = const_names
            .iter()
            .map(|name| {
                let off = self.write_name(name);
                self.offset_to_ptr(off)
            })
            .collect();
        let names_array_offset = self.write_array(&name_ptrs);
        let names_ptr = self.offset_to_ptr(names_array_offset);

        // Empty arrays for constants, extraConstNames
        let empty_array_offset = self.write_array(&[]);
        let empty_ptr = self.offset_to_ptr(empty_array_offset);

        let entries_ptr = if entries.is_empty() {
            empty_ptr
        } else {
            self.write_parsed_extension_entries(entries)
        };

        // Write ModuleData constructor (5 pointer fields)
        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 5, 0);
        self.write_u64(imports_ptr); // imports
        self.write_u64(names_ptr); // constNames
        self.write_u64(empty_ptr); // constants (empty for now)
        self.write_u64(empty_ptr); // extraConstNames
        self.write_u64(entries_ptr); // entries

        offset
    }

    /// Write a ModuleData structure with constants populated from an Environment
    ///
    /// ModuleData fields (from Lean 4 Environment.lean:122-141):
    /// 0: imports (Array Import)
    /// 1: constNames (Array Name)
    /// 2: constants (Array ConstantInfo) - populated from environment
    /// 3: extraConstNames (Array Name) - populated with generated names
    /// 4: entries (Array (Name × Array EnvExtensionEntry))
    ///
    /// # REQUIRES
    /// - `env` contains the constants to export.
    /// - `imports` uses Lean-style module strings.
    ///
    /// # ENSURES
    /// - Returns Ok(offset) of the ModuleData object.
    /// - Returns Err(UnsupportedBigNat) if any constant contains BigNat > u64.
    /// - Populates all arrays including constants and extraConstNames.
    pub(crate) fn write_module_data_with_env(
        &mut self,
        env: &Environment,
        imports: &[(&str, bool)],
        entries: &[ParsedExtension],
    ) -> OleanResult<usize> {
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

        // Collect all constant names (basic constants + inductives + constructors + recursors + quotients)
        let mut all_names: Vec<Name> = Vec::new();
        let mut const_ptrs: Vec<u64> = Vec::new();

        // 1. Basic constants (axioms, definitions, theorems)
        // Skip inductives, constructors, recursors, and quotients - they are written in steps 2-5
        for c in env.constants() {
            if env.get_inductive(&c.name).is_some() {
                continue; // Inductives are handled in step 2
            }
            if env.get_constructor(&c.name).is_some() {
                continue; // Constructors are handled in step 3
            }
            if env.get_recursor(&c.name).is_some() {
                continue; // Recursors are handled in step 4
            }
            if env.get_quot(&c.name).is_some() {
                continue; // Quotients are handled in step 5
            }
            all_names.push(c.name.clone());
            // Partial is the tighter classification if a malformed caller has
            // placed a name in both registries: either way it must not regain
            // ordinary safe definitional authority on round-trip.
            let safety = if env.is_partial(&c.name) {
                DefinitionSafety::Partial
            } else if env.is_unsafe(&c.name) {
                DefinitionSafety::Unsafe
            } else {
                DefinitionSafety::Safe
            };
            const_ptrs.push(self.write_constant_info_with_definition_safety(c, safety)?);
        }

        // 2. Inductive types
        for ind in env.inductives() {
            all_names.push(ind.name.clone());
            const_ptrs.push(self.write_inductive_info_with_unsafe(ind, env.is_unsafe(&ind.name))?);
        }

        // 3. Constructors
        for ctor in env.constructors() {
            all_names.push(ctor.name.clone());
            const_ptrs
                .push(self.write_constructor_info_with_unsafe(ctor, env.is_unsafe(&ctor.name))?);
        }

        // 4. Recursors
        for rec in env.recursors() {
            all_names.push(rec.name.clone());
            const_ptrs.push(self.write_recursor_info_with_unsafe(rec, env.is_unsafe(&rec.name))?);
        }

        // 5. Quotients
        for quot in env.quotients() {
            all_names.push(quot.name.clone());
            const_ptrs.push(self.write_quotient_info(quot)?);
        }

        // Write constant names array
        let name_ptrs: Vec<u64> = all_names
            .iter()
            .map(|name| {
                let off = self.write_kernel_name(name);
                self.offset_to_ptr(off)
            })
            .collect();
        let names_array_offset = self.write_array(&name_ptrs);
        let names_ptr = self.offset_to_ptr(names_array_offset);

        // Write constants array
        let consts_array_offset = self.write_array(&const_ptrs);
        let consts_ptr = self.offset_to_ptr(consts_array_offset);

        // Collect extraConstNames (generated auxiliary names from inductives)
        let extra_names = collect_extra_const_names(env);
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

    /// Assemble a minimal ModuleData from pre-written constant pointers.
    ///
    /// Test-only sibling of [`OleanExporter::write_module_data_with_env`]
    /// that takes already-serialized `ConstantInfo` pointers (and their
    /// names) directly, bypassing the kernel `Environment`. This lets a
    /// test emit `ConstantInfo` payloads with field values the kernel
    /// model cannot express (e.g. a non-`safe` `DefinitionSafety`) and
    /// still produce a parseable `.olean` buffer.
    #[cfg(test)]
    pub(crate) fn write_module_data_with_const_ptrs(
        &mut self,
        const_names: &[&str],
        const_ptrs: &[u64],
    ) -> usize {
        let imports_array_offset = self.write_array(&[]);
        let imports_ptr = self.offset_to_ptr(imports_array_offset);

        let name_ptrs: Vec<u64> = const_names
            .iter()
            .map(|name| {
                let off = self.write_name(name);
                self.offset_to_ptr(off)
            })
            .collect();
        let names_array_offset = self.write_array(&name_ptrs);
        let names_ptr = self.offset_to_ptr(names_array_offset);

        let consts_array_offset = self.write_array(const_ptrs);
        let consts_ptr = self.offset_to_ptr(consts_array_offset);

        let empty_array_offset = self.write_array(&[]);
        let empty_ptr = self.offset_to_ptr(empty_array_offset);

        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 5, 0);
        self.write_u64(imports_ptr); // imports
        self.write_u64(names_ptr); // constNames
        self.write_u64(consts_ptr); // constants
        self.write_u64(empty_ptr); // extraConstNames
        self.write_u64(empty_ptr); // entries
        offset
    }

    /// Write parsed extension entries array.
    pub(super) fn write_parsed_extension_entries(&mut self, extensions: &[ParsedExtension]) -> u64 {
        let ext_ptrs: Vec<u64> = extensions
            .iter()
            .map(|ext| self.write_parsed_extension_block(ext))
            .collect();
        let entries_offset = self.write_array(&ext_ptrs);
        self.offset_to_ptr(entries_offset)
    }

    /// Write a single extension block.
    pub(super) fn write_parsed_extension_block(&mut self, extension: &ParsedExtension) -> u64 {
        let name_offset = self.write_name(&extension.extension_name);
        let name_ptr = self.offset_to_ptr(name_offset);
        let entries_ptr = self.write_parsed_entry_array(&extension.entries);

        self.align8();
        let offset = self.current_offset();
        self.write_header(0, 2, 0);
        self.write_u64(name_ptr);
        self.write_u64(entries_ptr);
        self.offset_to_ptr(offset)
    }

    /// Write an array of parsed entries.
    ///
    /// Each element is either a pointer to a (Name × DataValue) pair or a raw scalar.
    pub(super) fn write_parsed_entry_array(&mut self, entries: &[ParsedExtensionEntry]) -> u64 {
        let entry_ptrs: Vec<u64> = entries
            .iter()
            .map(|entry| self.write_parsed_entry(entry))
            .collect();
        let entries_offset = self.write_array(&entry_ptrs);
        self.offset_to_ptr(entries_offset)
    }

    /// Write a single parsed extension entry.
    ///
    /// Returns the pointer/scalar value to store in the array.
    pub(super) fn write_parsed_entry(&mut self, entry: &ParsedExtensionEntry) -> u64 {
        match entry {
            ParsedExtensionEntry::Named { name, data } => {
                let name_offset = self.write_name(name);
                let name_ptr = self.offset_to_ptr(name_offset);

                let data_ptr = match data {
                    ParsedExtensionEntryData::Scalar(value) => *value,
                    ParsedExtensionEntryData::Object(bytes) => {
                        if bytes.is_empty() {
                            0
                        } else {
                            let data_offset = self.write_raw_object(bytes);
                            self.offset_to_ptr(data_offset)
                        }
                    }
                };

                self.align8();
                let offset = self.current_offset();
                self.write_header(0, 2, 0);
                self.write_u64(name_ptr);
                self.write_u64(data_ptr);
                self.offset_to_ptr(offset)
            }
            ParsedExtensionEntry::RawScalar(value) => {
                // Raw scalars are stored directly in the array (not as pointers to objects)
                *value
            }
            ParsedExtensionEntry::Instance(inst) => {
                // A decoded real-Lean `@[instance]` entry. Clean's exporter
                // cannot reproduce Lean's own `InstanceEntry` layout (the
                // DiscrTree keys / `val : Expr` / `synthOrder` fields are not
                // retained at parse), so re-export it as a plain
                // `(Name × DataValue)` pair — instance name × tagged-scalar
                // priority — which re-imports as `Named { name,
                // Scalar(priority) }`. Before the typed decoder existed these
                // entries were dropped at parse and never reached export at
                // all, so this loses nothing relative to the prior
                // round-trip and keeps the region pointer-free and valid.
                let name_offset = self.write_name(&inst.instance_name);
                let name_ptr = self.offset_to_ptr(name_offset);

                // Tagged scalar encoding: (value << 1) | 1. Clamp to the
                // representable 63-bit range so a pathological priority can
                // never overflow the shift.
                let data_ptr = (inst.priority.min(u64::MAX >> 1) << 1) | 1;

                self.align8();
                let offset = self.current_offset();
                self.write_header(0, 2, 0);
                self.write_u64(name_ptr);
                self.write_u64(data_ptr);
                self.offset_to_ptr(offset)
            }
            ParsedExtensionEntry::Class(class) => {
                // A decoded real-Lean type-class declaration. Unlike
                // `InstanceEntry`, every field of `ClassEntry` is retained at
                // parse (name + two `Array Nat`s), so re-emit the exact Lean
                // layout — `ClassEntry` (tag 0, 3 object slots): `name`,
                // `outParams`, `outLevelParams`. Each `Nat` is written as a
                // tagged scalar `(v << 1) | 1`, exactly how the compacted
                // region stores small nats, so this round-trips back through
                // `read_class_entry` with `undecoded_entries == 0`.
                let name_offset = self.write_name(&class.name);
                let name_ptr = self.offset_to_ptr(name_offset);

                let out_params: Vec<u64> = class
                    .out_params
                    .iter()
                    .map(|&v| (v.min(u64::MAX >> 1) << 1) | 1)
                    .collect();
                let out_params_offset = self.write_array(&out_params);
                let out_params_ptr = self.offset_to_ptr(out_params_offset);

                let out_level_params: Vec<u64> = class
                    .out_level_params
                    .iter()
                    .map(|&v| (v.min(u64::MAX >> 1) << 1) | 1)
                    .collect();
                let out_level_params_offset = self.write_array(&out_level_params);
                let out_level_params_ptr = self.offset_to_ptr(out_level_params_offset);

                self.align8();
                let offset = self.current_offset();
                self.write_header(0, 3, 0);
                self.write_u64(name_ptr);
                self.write_u64(out_params_ptr);
                self.write_u64(out_level_params_ptr);
                self.offset_to_ptr(offset)
            }
        }
    }
}

/// Collect extra constant names from generated auxiliary definitions
///
/// These include recursor aliases, no-confusion lemmas, and cases elimination
/// functions that are generated for inductive types but may not be in the
/// primary constants list.
///
/// # ENSURES
/// - Returns names of generated auxiliary constants.
/// - Does not include names already in env.constants().
pub(super) fn collect_extra_const_names(env: &Environment) -> Vec<Name> {
    let mut extra = Vec::new();
    let const_names: std::collections::HashSet<_> =
        env.constants().map(|c| c.name.clone()).collect();

    // Collect names from inductives that generate auxiliary definitions
    for ind in env.inductives() {
        // Generated recursor names
        let rec_name = ind.name.clone().str("rec");
        if !const_names.contains(&rec_name) {
            extra.push(rec_name);
        }

        // recOn, casesOn
        let rec_on_name = ind.name.clone().str("recOn");
        if !const_names.contains(&rec_on_name) {
            extra.push(rec_on_name);
        }

        let cases_on_name = ind.name.clone().str("casesOn");
        if !const_names.contains(&cases_on_name) {
            extra.push(cases_on_name);
        }

        // noConfusion, noConfusionType
        let no_confusion_name = ind.name.clone().str("noConfusion");
        if !const_names.contains(&no_confusion_name) {
            extra.push(no_confusion_name);
        }

        let no_confusion_type_name = ind.name.clone().str("noConfusionType");
        if !const_names.contains(&no_confusion_type_name) {
            extra.push(no_confusion_type_name);
        }
    }

    extra
}

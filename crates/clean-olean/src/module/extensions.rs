// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extension entry parsing for CompactedRegion.
//!
//! Reads persistent environment extension entries from .olean files.
//! Each extension is a `(Name × Array (Name × DataValue))` pair.

use super::{
    ParsedAttrKind, ParsedClassEntry, ParsedExtension, ParsedExtensionEntry,
    ParsedExtensionEntryData, ParsedInstanceEntry, ParsedSimpEntry, ParsedSimpEntryKind,
};
use crate::error::{OleanError, OleanResult};
use crate::region::{is_ptr, tags, CompactedRegion};

/// The persisted name of Lean 4's typeclass-instance extension
/// (`Lean/Meta/Instances.lean`, registered via `decl_name%`).
pub(crate) const LEAN_INSTANCE_EXTENSION: &str = "Lean.Meta.instanceExtension";

/// The persisted name of Lean 4's type-class declaration extension
/// (`Lean/Class.lean`, registered via `builtin_initialize classExtension`).
pub(crate) const LEAN_CLASS_EXTENSION: &str = "Lean.classExtension";

/// The persisted name of Lean 4's default simp set extension
/// (`Lean/Meta/Tactic/Simp/Attr.lean`, registered via
/// `builtin_initialize simpExtension : SimpExtension ← registerSimpAttr \`simp …`,
/// whose extension name is the declaration name via `decl_name%`).
pub(crate) const LEAN_SIMP_EXTENSION: &str = "Lean.Meta.simpExtension";

/// The persisted name of Lean 4's alias extension (`Lean/ResolveName.lean`,
/// `builtin_initialize aliasExtension`). Holds one `Name × Name` pair per
/// `export`ed name — the mechanism behind root-level `isTrue` / `isFalse` /
/// `decide` (from `export Decidable …`) and `eq_of_beq` (`export LawfulBEq …`).
pub(crate) const LEAN_ALIAS_EXTENSION: &str = "Lean.aliasExtension";

/// Number of object (pointer) slots in a Lean 4 v4.x `ClassEntry`:
/// `name : Name`, `outParams : Array Nat`, `outLevelParams : Array Nat`
/// (`Lean/Class.lean:14-32`). All three slots are pointers; there is no
/// trailing scalar.
const CLASS_ENTRY_OBJ_FIELDS: u8 = 3;

/// Number of object (pointer) slots in a Lean 4 v4.x `InstanceEntry`:
/// `keys`, `val`, `priority`, `globalName?`, `synthOrder`
/// (`Lean/Meta/Instances.lean:46-60`). The trailing `attrKind : AttributeKind`
/// is a `uint8` scalar stored after the object slots.
const INSTANCE_ENTRY_OBJ_FIELDS: u8 = 5;

/// Byte offset of the `attrKind` scalar inside an `InstanceEntry` object:
/// 8-byte header + 5 object slots.
const INSTANCE_ENTRY_ATTR_KIND_OFFSET: usize = 8 + (INSTANCE_ENTRY_OBJ_FIELDS as usize) * 8;

/// Number of object (pointer) slots in a Lean 4 v4.x `SimpTheorem`:
/// `keys : Array SimpTheoremKey`, `levelParams : Array Name`, `proof : Expr`,
/// `priority : Nat`, `origin : Origin`
/// (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:143-165`). The trailing
/// `post`/`perm`/`rfl` fields are `Bool` (uint8) scalars stored after the
/// object slots, in declaration order. Layout verified byte-level against the
/// pinned v4.30.0-rc2 `Init/SimpLemmas.olean` (tag 0, 5 object fields,
/// `cs_sz` 56, scalars at offsets 48/49/50).
const SIMP_THEOREM_OBJ_FIELDS: u8 = 5;

/// Byte offset of the `post : Bool` scalar inside a `SimpTheorem` object:
/// 8-byte header + 5 object slots.
const SIMP_THEOREM_POST_OFFSET: usize = 8 + (SIMP_THEOREM_OBJ_FIELDS as usize) * 8;

/// Lean 4's default simp-lemma priority (`eval_prio default` = 1000,
/// `SimpTheorem.priority`'s default). Reported for `toUnfold`/`toUnfoldThms`
/// entries, which persist no priority of their own.
const LEAN_DEFAULT_SIMP_PRIORITY: u32 = 1000;

/// Byte offset of the `inv : Bool` scalar inside an `Origin.decl` object:
/// 8-byte header + 1 object slot (`declName : Name`) + 1 byte (`post : Bool`).
/// (`Origin.decl (declName : Name) (post := true) (inv := false)`,
/// `Lean/Meta/Tactic/Simp/SimpTheorems.lean:57-79`; verified: tag 0,
/// 1 object field, `cs_sz` 24.)
const ORIGIN_DECL_INV_OFFSET: usize = 8 + 8 + 1;

impl<'a> CompactedRegion<'a> {
    /// Read the entries array: Array (Name × Array (Name × DataValue))
    ///
    /// Each element is a product pair of (extension_name, entries_array).
    /// The inner array contains (entry_name, data_value) pairs.
    pub(crate) fn read_extension_entries_array(
        &self,
        ptr: u64,
    ) -> OleanResult<Vec<ParsedExtension>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }

        let size = self.read_usize_at(offset + 8, "Extension array")?;
        self.validate_array_bounds(offset, size)?;
        let mut extensions = Vec::with_capacity(size);

        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Extension array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if is_ptr(elem_ptr) {
                let ext = self.read_extension_pair(elem_ptr)?;
                extensions.push(ext);
            } else {
                return Err(OleanError::Region(format!(
                    "Invalid extension element at index {i}: expected pointer, got {elem_ptr:#x}"
                )));
            }
        }

        Ok(extensions)
    }

    /// Read a single (Name × Array (Name × DataValue)) product pair.
    ///
    /// Lean Prod structure has tag=0 and 2 fields: (fst, snd).
    fn read_extension_pair(&self, ptr: u64) -> OleanResult<ParsedExtension> {
        if !is_ptr(ptr) {
            return Err(OleanError::Region("Invalid extension pair pointer".into()));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if !header.is_constructor() || header.other < 2 {
            return Err(OleanError::Region(format!(
                "Expected Prod with 2 fields, got tag={} fields={}",
                header.tag, header.other
            )));
        }

        let name_ptr = self.read_u64_at(offset + 8)?;
        let extension_name = self.resolve_name_ptr(name_ptr)?;

        let entries_ptr = self.read_u64_at(offset + 16)?;
        let (entries, undecoded_entries) = if extension_name == LEAN_INSTANCE_EXTENSION {
            self.read_instance_entry_array(entries_ptr)?
        } else if extension_name == LEAN_CLASS_EXTENSION {
            self.read_class_entry_array(entries_ptr)?
        } else if extension_name == LEAN_SIMP_EXTENSION {
            self.read_simp_entry_array(entries_ptr)?
        } else if extension_name == LEAN_ALIAS_EXTENSION {
            (self.read_alias_entry_array(entries_ptr)?, 0)
        } else {
            (self.read_extension_entry_array(entries_ptr)?, 0)
        };

        Ok(ParsedExtension {
            extension_name,
            entries,
            undecoded_entries,
        })
    }

    /// Read a `Lean.Meta.instanceExtension` entry array with the real Lean 4
    /// layout: each element is a `ScopedEnvExtension.Entry InstanceEntry`.
    ///
    /// Returns the decoded entries plus a count of elements that did not
    /// match the expected layout. Failed elements are *inert* — they simply
    /// do not appear in the result, exactly as the generic `(Name × DataValue)`
    /// heuristic dropped them before this decoder existed — but the count
    /// keeps the loss observable (`ParsedExtension::undecoded_entries`).
    fn read_instance_entry_array(
        &self,
        ptr: u64,
    ) -> OleanResult<(Vec<ParsedExtensionEntry>, usize)> {
        if !is_ptr(ptr) {
            return Ok((Vec::new(), 0));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok((Vec::new(), 0));
        }

        let size = self.read_usize_at(offset + 8, "Instance entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);
        let mut undecoded = 0usize;

        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Instance entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            match self.read_scoped_instance_entry(elem_ptr) {
                Ok(Some(entry)) => entries.push(ParsedExtensionEntry::Instance(entry)),
                // Unexpected layout or unreadable object: degrade to the
                // pre-decoder behavior (entry absent) but count it — loud,
                // never silently wrong.
                Ok(None) | Err(_) => undecoded += 1,
            }
        }

        Ok((entries, undecoded))
    }

    /// Decode one `ScopedEnvExtension.Entry InstanceEntry` element.
    ///
    /// Layout (`Lean/ScopedEnvExtension.lean:17-19`):
    /// - tag 0 `global (v : InstanceEntry)` — 1 object field
    /// - tag 1 `scoped (ns : Name) (v : InstanceEntry)` — 2 object fields
    ///
    /// Returns `Ok(None)` for any shape mismatch so the caller can count the
    /// element as undecoded without failing the whole module parse.
    fn read_scoped_instance_entry(&self, ptr: u64) -> OleanResult<Option<ParsedInstanceEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if !header.is_constructor() {
            return Ok(None);
        }

        let (scope_ns, entry_ptr) = match header.tag {
            0 if header.other >= 1 => (None, self.read_u64_at(offset + 8)?),
            1 if header.other >= 2 => {
                let ns_ptr = self.read_u64_at(offset + 8)?;
                let ns = self.resolve_name_ptr(ns_ptr)?;
                (Some(ns), self.read_u64_at(offset + 16)?)
            }
            _ => return Ok(None),
        };

        self.read_instance_entry(entry_ptr, scope_ns)
    }

    /// Decode a Lean 4 `InstanceEntry` object (`Lean/Meta/Instances.lean:46-60`).
    ///
    /// Object slots in declaration order: `keys : Array DiscrTree.Key` (0,
    /// skipped), `val : Expr` (1, skipped), `priority : Nat` (2),
    /// `globalName? : Option Name` (3), `synthOrder : Array Nat` (4);
    /// then the `attrKind : AttributeKind` uint8 scalar.
    ///
    /// Returns `Ok(None)` when the object does not match this layout (e.g. a
    /// different toolchain's field set) or `globalName?` is `none` — the
    /// entry is then counted as undecoded rather than guessed at.
    fn read_instance_entry(
        &self,
        ptr: u64,
        scope_ns: Option<String>,
    ) -> OleanResult<Option<ParsedInstanceEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        // Layout gate: exactly the v4.x field set (5 object slots) AND an
        // object size that covers the trailing `attrKind` scalar byte — a
        // hypothetical scalar-less variant must not read the neighbouring
        // object's bytes as an attribute kind.
        if !header.is_constructor()
            || header.tag != 0
            || header.other != INSTANCE_ENTRY_OBJ_FIELDS
            || (header.cs_sz as usize) <= INSTANCE_ENTRY_ATTR_KIND_OFFSET
        {
            return Ok(None);
        }

        // Slot 2: priority : Nat (tagged scalar or mpz pointer).
        let priority_ptr = self.read_u64_at(offset + 8 + 16)?;
        let priority = self.read_nat_value(priority_ptr)?;

        // Slot 3: globalName? : Option Name. `box(0)` (= 0x1) is `none`.
        let global_name_ptr = self.read_u64_at(offset + 8 + 24)?;
        if !is_ptr(global_name_ptr) {
            return Ok(None); // `none`: a local instance; nothing to restore.
        }
        let some_offset = self.ptr_to_offset(global_name_ptr)?;
        let some_header = self.read_header_at(some_offset)?;
        if !some_header.is_constructor() || some_header.tag != 1 || some_header.other < 1 {
            return Ok(None);
        }
        let name_ptr = self.read_u64_at(some_offset + 8)?;
        let instance_name = self.resolve_name_ptr(name_ptr)?;

        // Slot 4: synthOrder : Array Nat.
        let synth_order_ptr = self.read_u64_at(offset + 8 + 32)?;
        let Some(synth_order) = self.read_nat_array(synth_order_ptr)? else {
            return Ok(None); // unexpected layout: count as undecoded, never guess
        };

        // Trailing scalar: attrKind : AttributeKind (uint8).
        let attr_byte = self.bytes_at(offset + INSTANCE_ENTRY_ATTR_KIND_OFFSET, 1)?[0];
        let Some(attr_kind) = ParsedAttrKind::from_tag(attr_byte) else {
            return Ok(None);
        };

        Ok(Some(ParsedInstanceEntry {
            instance_name,
            priority,
            attr_kind,
            scope_ns,
            synth_order,
        }))
    }

    /// Read a `Lean.Meta.simpExtension` entry array with the real Lean 4
    /// layout: each element is a `ScopedEnvExtension.Entry SimpEntry`.
    ///
    /// Returns the decoded entries plus a count of elements that did not
    /// match the expected layout. As with [`Self::read_instance_entry_array`],
    /// failed elements are *inert* — absent from the result, exactly as the
    /// generic `(Name × DataValue)` heuristic dropped every one of them before
    /// this decoder existed — but the count keeps the loss observable
    /// (`ParsedExtension::undecoded_entries`).
    fn read_simp_entry_array(&self, ptr: u64) -> OleanResult<(Vec<ParsedExtensionEntry>, usize)> {
        if !is_ptr(ptr) {
            return Ok((Vec::new(), 0));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok((Vec::new(), 0));
        }

        let size = self.read_usize_at(offset + 8, "Simp entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);
        let mut undecoded = 0usize;

        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Simp entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            match self.read_scoped_simp_entry(elem_ptr) {
                Ok(Some(entry)) => entries.push(ParsedExtensionEntry::Simp(entry)),
                // Unexpected layout or unreadable object: degrade to the
                // pre-decoder behavior (entry absent) but count it — loud,
                // never silently wrong.
                Ok(None) | Err(_) => undecoded += 1,
            }
        }

        Ok((entries, undecoded))
    }

    /// Decode one `ScopedEnvExtension.Entry SimpEntry` element.
    ///
    /// Layout (`Lean/ScopedEnvExtension.lean:17-19`):
    /// - tag 0 `global (v : SimpEntry)` — exactly 1 object field
    /// - tag 1 `scoped (ns : Name) (v : SimpEntry)` — exactly 2 object fields
    ///
    /// The arity gates are EXACT: a `(Name × DataValue)` Prod pair (tag 0,
    /// 2 fields — the shape Clean's own exporter re-emits decoded entries as)
    /// must NOT pass as `Entry.global`, or its first field (a `Name` object)
    /// would be mis-decoded as a `SimpEntry`.
    ///
    /// Returns `Ok(None)` for any shape mismatch so the caller can count the
    /// element as undecoded without failing the whole module parse.
    fn read_scoped_simp_entry(&self, ptr: u64) -> OleanResult<Option<ParsedSimpEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if !header.is_constructor() {
            return Ok(None);
        }

        let (scope_ns, entry_ptr) = match header.tag {
            0 if header.other == 1 => (None, self.read_u64_at(offset + 8)?),
            1 if header.other == 2 => {
                let ns_ptr = self.read_u64_at(offset + 8)?;
                let ns = self.resolve_name_ptr(ns_ptr)?;
                (Some(ns), self.read_u64_at(offset + 16)?)
            }
            _ => return Ok(None),
        };

        self.read_simp_entry(entry_ptr, scope_ns)
    }

    /// Decode a Lean 4 `SimpEntry` object
    /// (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:449-453`):
    /// - tag 0 `thm (SimpTheorem)` — exactly 1 object field
    /// - tag 1 `toUnfold (Name)` — exactly 1 object field
    /// - tag 2 `toUnfoldThms (Name) (Array Name)` — exactly 2 object fields
    ///   (only the declaration name is retained; Clean reconstructs equation
    ///   lemmas from the environment, never from serialized bytes)
    ///
    /// The arity gates are EXACT so no other constructor-shaped object (e.g.
    /// a `Name.str`, tag 1 with 2 object fields) can pass as a `SimpEntry`.
    ///
    /// Returns `Ok(None)` for an unknown constructor tag (a future Lean
    /// `SimpEntry` variant) so the entry is counted rather than guessed at.
    fn read_simp_entry(
        &self,
        ptr: u64,
        scope_ns: Option<String>,
    ) -> OleanResult<Option<ParsedSimpEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if !header.is_constructor() {
            return Ok(None);
        }

        match header.tag {
            0 if header.other == 1 => {
                let thm_ptr = self.read_u64_at(offset + 8)?;
                self.read_simp_theorem(thm_ptr, scope_ns)
            }
            1 if header.other == 1 => {
                let name_ptr = self.read_u64_at(offset + 8)?;
                let lemma_name = self.resolve_name_ptr(name_ptr)?;
                Ok(Some(ParsedSimpEntry {
                    lemma_name,
                    priority: u64::from(LEAN_DEFAULT_SIMP_PRIORITY),
                    post: true,
                    kind: ParsedSimpEntryKind::ToUnfold,
                    scope_ns,
                }))
            }
            2 if header.other == 2 => {
                let name_ptr = self.read_u64_at(offset + 8)?;
                let lemma_name = self.resolve_name_ptr(name_ptr)?;
                Ok(Some(ParsedSimpEntry {
                    lemma_name,
                    priority: u64::from(LEAN_DEFAULT_SIMP_PRIORITY),
                    post: true,
                    kind: ParsedSimpEntryKind::ToUnfoldThms,
                    scope_ns,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Decode a Lean 4 `SimpTheorem` object
    /// (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:143-165`).
    ///
    /// Object slots in declaration order: `keys : Array SimpTheoremKey` (0,
    /// skipped), `levelParams : Array Name` (1, skipped), `proof : Expr` (2,
    /// skipped — the statement is reconstructed from the kernel-checked
    /// environment constant, never from serialized bytes), `priority : Nat`
    /// (3), `origin : Origin` (4); then the `post`/`perm`/`rfl` `Bool` scalars.
    ///
    /// Only `Origin.decl` (tag 0) origins are decodable by name; `fvar`/`stx`/
    /// `other` origins carry no environment declaration to resolve (and Lean's
    /// own `exportEntry?` never persists them — `Lean/Meta/Tactic/Simp/
    /// SimpTheorems.lean:660-676` marks them `unreachable!`). An `inv := true`
    /// origin (`@[simp ←]`) rewrites right-to-left, a direction the by-name
    /// re-registration cannot represent — decoding it forward would flip the
    /// rewrite, so it is counted as undecoded instead of misregistered.
    ///
    /// Returns `Ok(None)` when the object does not match this layout (e.g. a
    /// different toolchain's field set) — the entry is then counted as
    /// undecoded rather than guessed at.
    fn read_simp_theorem(
        &self,
        ptr: u64,
        scope_ns: Option<String>,
    ) -> OleanResult<Option<ParsedSimpEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        // Layout gate: exactly the v4.x field set (5 object slots) AND an
        // object size that covers the trailing `post` scalar byte.
        if !header.is_constructor()
            || header.tag != 0
            || header.other != SIMP_THEOREM_OBJ_FIELDS
            || (header.cs_sz as usize) <= SIMP_THEOREM_POST_OFFSET
        {
            return Ok(None);
        }

        // Slot 3: priority : Nat (tagged scalar or mpz pointer).
        let priority_ptr = self.read_u64_at(offset + 8 + 24)?;
        let priority = self.read_nat_value(priority_ptr)?;

        // Slot 4: origin : Origin. Only `.decl` (tag 0, 1 object slot +
        // `post`/`inv` Bool scalars) names an environment declaration.
        let origin_ptr = self.read_u64_at(offset + 8 + 32)?;
        if !is_ptr(origin_ptr) {
            return Ok(None);
        }
        let origin_offset = self.ptr_to_offset(origin_ptr)?;
        let origin_header = self.read_header_at(origin_offset)?;
        if !origin_header.is_constructor()
            || origin_header.tag != 0
            || origin_header.other != 1
            || (origin_header.cs_sz as usize) <= ORIGIN_DECL_INV_OFFSET
        {
            return Ok(None);
        }
        // `inv := true` (`@[simp ←]`): the persisted direction is
        // right-to-left; registering the constant forward would flip it.
        // Count as undecoded, never misregister.
        if self.bytes_at(origin_offset + ORIGIN_DECL_INV_OFFSET, 1)?[0] != 0 {
            return Ok(None);
        }
        let name_ptr = self.read_u64_at(origin_offset + 8)?;
        let lemma_name = self.resolve_name_ptr(name_ptr)?;

        // Trailing scalar: post : Bool (uint8).
        let post = self.bytes_at(offset + SIMP_THEOREM_POST_OFFSET, 1)?[0] != 0;

        Ok(Some(ParsedSimpEntry {
            lemma_name,
            priority,
            post,
            kind: ParsedSimpEntryKind::Theorem,
            scope_ns,
        }))
    }

    /// Read a `Lean.classExtension` entry array with the real Lean 4 layout:
    /// each element is a `ClassEntry` (`Lean/Class.lean:14-32`).
    ///
    /// Returns the decoded entries plus a count of elements that did not match
    /// the expected layout. As with [`Self::read_instance_entry_array`], failed
    /// elements are *inert* — absent from the result, exactly as the generic
    /// `(Name × DataValue)` heuristic left them (it recovered only the class
    /// name, with the two `outParams`/`outLevelParams` arrays opaque) — but the
    /// count keeps the loss observable (`ParsedExtension::undecoded_entries`).
    fn read_class_entry_array(&self, ptr: u64) -> OleanResult<(Vec<ParsedExtensionEntry>, usize)> {
        if !is_ptr(ptr) {
            return Ok((Vec::new(), 0));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok((Vec::new(), 0));
        }

        let size = self.read_usize_at(offset + 8, "Class entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);
        let mut undecoded = 0usize;

        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Class entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            match self.read_class_entry(elem_ptr) {
                Ok(Some(entry)) => entries.push(ParsedExtensionEntry::Class(entry)),
                // Unexpected layout or unreadable object: degrade to the
                // pre-decoder behavior (entry absent) but count it — loud,
                // never silently wrong.
                Ok(None) | Err(_) => undecoded += 1,
            }
        }

        Ok((entries, undecoded))
    }

    /// Decode one Lean 4 `ClassEntry` object (`Lean/Class.lean:14-32`).
    ///
    /// Object slots in declaration order: `name : Name` (0),
    /// `outParams : Array Nat` (1), `outLevelParams : Array Nat` (2). All three
    /// are pointers; the constructor has tag 0 and no trailing scalar.
    ///
    /// Returns `Ok(None)` when the object does not match this layout (e.g. a
    /// different toolchain's field set), so the caller counts the element as
    /// undecoded rather than guessing.
    fn read_class_entry(&self, ptr: u64) -> OleanResult<Option<ParsedClassEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        // Layout gate: exactly the v4.x field set (3 object slots, tag 0).
        if !header.is_constructor() || header.tag != 0 || header.other != CLASS_ENTRY_OBJ_FIELDS {
            return Ok(None);
        }

        // Slot 0: name : Name.
        let name_ptr = self.read_u64_at(offset + 8)?;
        let name = self.resolve_name_ptr(name_ptr)?;

        // Slot 1: outParams : Array Nat.
        let out_params_ptr = self.read_u64_at(offset + 16)?;
        let Some(out_params) = self.read_nat_array(out_params_ptr)? else {
            return Ok(None); // unexpected layout: count as undecoded, never guess
        };

        // Slot 2: outLevelParams : Array Nat.
        let out_level_params_ptr = self.read_u64_at(offset + 24)?;
        let Some(out_level_params) = self.read_nat_array(out_level_params_ptr)? else {
            return Ok(None);
        };

        Ok(Some(ParsedClassEntry {
            name,
            out_params,
            out_level_params,
        }))
    }

    /// Decode an `Array Nat` object into its element values.
    ///
    /// Elements are boxed `Nat`s: tagged scalars for small values or `mpz`
    /// pointers for big ones — both handled by [`Self::read_nat_value`].
    /// Returns `Ok(None)` when the pointer does not reference an array-shaped
    /// object (the caller then counts the enclosing entry as undecoded rather
    /// than guessing).
    fn read_nat_array(&self, ptr: u64) -> OleanResult<Option<Vec<u64>>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(None);
        }
        let size = self.read_usize_at(offset + 8, "Nat array")?;
        self.validate_array_bounds(offset, size)?;
        let mut values = Vec::with_capacity(size);
        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Nat array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            values.push(self.read_nat_value(elem_ptr)?);
        }
        Ok(Some(values))
    }

    /// Read an array of extension entry elements.
    ///
    /// Each element is either a pointer to a (Name × DataValue) pair or a raw scalar
    /// (e.g., `0x1` for unit sentinel values). Scalar elements are preserved as
    /// `RawScalar` variants for roundtrip fidelity.
    fn read_extension_entry_array(&self, ptr: u64) -> OleanResult<Vec<ParsedExtensionEntry>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }

        let size = self.read_usize_at(offset + 8, "Extension entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);

        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Extension entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if is_ptr(elem_ptr) {
                if let Some(entry) = self.read_extension_entry_pair(elem_ptr)? {
                    entries.push(entry);
                }
            } else {
                entries.push(ParsedExtensionEntry::RawScalar(elem_ptr));
            }
        }

        Ok(entries)
    }

    /// Read `Lean.aliasExtension`'s entries: `Name × Name` pairs mapping an
    /// exported short name to its fully-qualified target. The generic reader
    /// treats the second slot as an opaque `DataValue`; here it is resolved
    /// as a `Name`, which is the whole difference between an alias that
    /// resolves after `import Init` and one that does not.
    fn read_alias_entry_array(&self, ptr: u64) -> OleanResult<Vec<ParsedExtensionEntry>> {
        if !is_ptr(ptr) {
            return Ok(Vec::new());
        }
        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY && header.tag != tags::STRUCT_ARRAY {
            return Ok(Vec::new());
        }
        let size = self.read_usize_at(offset + 8, "Alias entry array")?;
        self.validate_array_bounds(offset, size)?;
        let mut entries = Vec::with_capacity(size);
        for i in 0..size {
            let elem_offset = self.array_elem_offset(offset, i, "Alias entry array")?;
            let elem_ptr = self.read_u64_at(elem_offset)?;
            if !is_ptr(elem_ptr) {
                continue;
            }
            let pair_offset = self.ptr_to_offset(elem_ptr)?;
            let pair_header = self.read_header_at(pair_offset)?;
            if !pair_header.is_constructor() || pair_header.other < 2 {
                continue;
            }
            let alias_ptr = self.read_u64_at(pair_offset + 8)?;
            let target_ptr = self.read_u64_at(pair_offset + 16)?;
            // Faithfulness: a pair whose EITHER side fails to resolve as a
            // Name is dropped, never guessed.
            let (Ok(alias), Ok(target)) = (
                self.resolve_name_ptr(alias_ptr),
                self.resolve_name_ptr(target_ptr),
            ) else {
                continue;
            };
            entries.push(ParsedExtensionEntry::Alias { alias, target });
        }
        Ok(entries)
    }

    /// Read a single extension entry from the inner array.
    ///
    /// Lean 4 extension entries are opaque. We attempt to parse as
    /// `(Name × DataValue)` for backward compatibility, but fall back
    /// to opaque handling for unrecognized structures.
    fn read_extension_entry_pair(&self, ptr: u64) -> OleanResult<Option<ParsedExtensionEntry>> {
        if !is_ptr(ptr) {
            return Ok(None);
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        if !header.is_constructor() || header.other < 2 {
            return Ok(None);
        }

        let name_ptr = self.read_u64_at(offset + 8)?;
        let name = match self.resolve_name_ptr(name_ptr) {
            Ok(name) => name,
            Err(_) => return Ok(None),
        };

        let data_ptr = self.read_u64_at(offset + 16)?;
        let data = self.read_opaque_data(data_ptr)?;

        Ok(Some(ParsedExtensionEntry::Named { name, data }))
    }

    /// Read opaque data from a pointer.
    ///
    /// For DataValue payloads, we capture tagged scalars or raw object bytes
    /// for best-effort round-tripping.
    fn read_opaque_data(&self, ptr: u64) -> OleanResult<ParsedExtensionEntryData> {
        if !is_ptr(ptr) {
            return Ok(ParsedExtensionEntryData::Scalar(ptr));
        }

        let offset = self.ptr_to_offset(ptr)?;
        let header = self.read_header_at(offset)?;

        let mut obj_size = header.cs_sz as usize;

        if obj_size == 0 {
            obj_size = match header.tag {
                tags::ARRAY | tags::STRUCT_ARRAY => {
                    let size = self.read_usize_at(offset + 8, "Opaque array")?;
                    size.checked_mul(8)
                        .and_then(|s| s.checked_add(24))
                        .ok_or_else(|| OleanError::Region("Opaque array size overflow".into()))?
                }
                tags::SCALAR_ARRAY => {
                    let size = self.read_usize_at(offset + 8, "Opaque scalar array")?;
                    size.checked_mul(header.other as usize)
                        .and_then(|s| s.checked_add(24))
                        .ok_or_else(|| {
                            OleanError::Region("Opaque scalar array size overflow".into())
                        })?
                }
                tags::STRING => {
                    let size = self.read_usize_at(offset + 8, "Opaque string")?;
                    size.checked_add(32)
                        .ok_or_else(|| OleanError::Region("Opaque string size overflow".into()))?
                }
                _ => 0,
            };
        }

        if obj_size == 0 {
            return Ok(ParsedExtensionEntryData::Object(Vec::new()));
        }

        let end_offset = offset
            .checked_add(obj_size)
            .filter(|&end| end <= self.data.len())
            .ok_or_else(|| OleanError::Region("Opaque object extends past data".into()))?;

        Ok(ParsedExtensionEntryData::Object(
            self.data[offset..end_offset].to_vec(),
        ))
    }
}

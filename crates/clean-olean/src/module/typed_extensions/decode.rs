// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded extension metadata decoding for direct loading. Unknown rows are
//! retained as unmeasured; their bytes are not treated as Clean payloads.
use super::{
    TypedClassEntry, TypedExtension, TypedExtensionEntry, TypedInstanceEntry, TypedSimpEntry,
    TypedStructureEntry, TypedStructureParent,
};
use crate::error::{OleanError, OleanResult};
use crate::module::{ParsedAttrKind, ParsedExtensionEntryData};
use crate::region::{is_ptr, tags, CompactedRegion, TypedModuleLayout};
use clean_kernel::name::Name;
use std::cell::Cell;

pub(super) mod exported_term_syntax;

const MAX_ITEMS: usize = 100_000;
const MAX_TOTAL_ARRAY_ITEMS: usize = 1_000_000;

fn invalid(message: impl Into<String>) -> OleanError {
    OleanError::Region(message.into())
}

#[derive(Clone, Copy)]
enum Kind {
    Instance,
    Class,
    Matcher,
    Simp,
    Alias,
    Structure,
    ImplementedBy,
    CSimp,
    Noncomputable,
    Extern,
    Other,
}

/// Most `ExternEntry` rows one `ExternAttrData` may list (Lean writes one per
/// backend; every row of the pinned v4.30.0-rc2 `Init` and `Std` has one).
const MAX_EXTERN_ENTRIES: usize = 64;

fn kind(name: &Name) -> Kind {
    let lean = Name::anon().str("Lean");
    if name == &lean.clone().str("Meta").str("instanceExtension") {
        Kind::Instance
    } else if name == &lean.clone().str("classExtension") {
        Kind::Class
    } else if name
        == &lean
            .clone()
            .str("Meta")
            .str("Match")
            .str("Extension")
            .str("extension")
    {
        Kind::Matcher
    } else if name == &lean.clone().str("Meta").str("simpExtension") {
        Kind::Simp
    } else if name == &lean.clone().str("aliasExtension") {
        Kind::Alias
    } else if name == &lean.clone().str("Compiler").str("implementedByAttr") {
        Kind::ImplementedBy
    } else if name == &lean.clone().str("Compiler").str("CSimp").str("ext") {
        Kind::CSimp
    } else if name == &lean.clone().str("noncomputableExt") {
        Kind::Noncomputable
    } else if name == &lean.clone().str("externAttr") {
        Kind::Extern
    } else if is_structure_ext(name) {
        Kind::Structure
    } else {
        Kind::Other
    }
}

/// A table read for its names only (`TypedExtension::compiler_names`).
#[derive(Clone, Copy)]
enum NamesTable {
    /// `Lean.IR.declMapExt`: each row a `Lean.IR.Decl`.
    DeclMap,
    /// `Lean.Compiler.inlineAttrs`: each row a `Name × InlineAttributeKind`.
    InlineAttrs,
}

fn names_table(name: &Name) -> Option<NamesTable> {
    let lean = Name::anon().str("Lean");
    if name == &lean.clone().str("IR").str("declMapExt") {
        Some(NamesTable::DeclMap)
    } else if name == &lean.str("Compiler").str("inlineAttrs") {
        Some(NamesTable::InlineAttrs)
    } else {
        None
    }
}

/// `InlineAttributeKind`'s constructors (`inline | noinline | macroInline |
/// inlineIfReduce | alwaysInline`, the same order in v4.30.0-rc2 and
/// v4.8.0), boxed as Lean stores an enumeration in an object field.
const INLINE_ATTRIBUTE_KINDS: u64 = 5;

/// `Lean.structureExt`, bare or under its `_private.Lean.Structure.<n>.`
/// prefix (the initializer is `private`, so the persisted name carries Lean's
/// private-name prefix; measured on the pinned v4.30.0-rc2 `Init/Prelude`).
pub(crate) fn is_structure_ext(name: &Name) -> bool {
    crate::module::is_structure_extension_name(&name.to_string())
}

impl CompactedRegion<'_> {
    pub(crate) fn read_typed_extension_entries(
        &self,
        pointer: u64,
    ) -> OleanResult<Vec<TypedExtension>> {
        let layout = self.typed_module_layout()?;
        let reader = Reader {
            region: self,
            layout,
            legacy: layout == TypedModuleLayout::CleanLegacy,
            remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
        };
        let pointers = reader.array(pointer)?;
        let mut extensions = pointers
            .iter()
            .map(|&pointer| reader.extension(pointer))
            .collect::<OleanResult<Vec<_>>>()?;
        // Inline attributes affect source compilation even without any
        // implementedBy binding. A present unread table cannot mean no hints.
        let binds = extensions.iter().any(|extension| {
            extension
                .entries
                .iter()
                .any(|entry| matches!(entry, TypedExtensionEntry::ImplementedBy { .. }))
        });
        for (extension, &pointer) in extensions.iter_mut().zip(&pointers) {
            match names_table(&extension.extension_name) {
                Some(NamesTable::InlineAttrs) if !reader.legacy => {
                    extension.compiler_names =
                        Some(reader.compiler_names(pointer, NamesTable::InlineAttrs)?);
                }
                Some(NamesTable::DeclMap) if binds && !reader.legacy => {
                    extension.compiler_names =
                        reader.compiler_names(pointer, NamesTable::DeclMap).ok();
                }
                _ => {}
            }
        }
        Ok(extensions)
    }
}

struct Reader<'r, 'a> {
    region: &'r CompactedRegion<'a>,
    layout: TypedModuleLayout,
    legacy: bool,
    // Shared pointers may otherwise amplify a tiny file into MAX_ITEMS² work.
    remaining_items: Cell<usize>,
}

#[cfg(test)]
#[path = "decode_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "decode_extern_carrier_tests.rs"]
mod extern_carrier_tests;

#[cfg(test)]
#[path = "decode_csimp_tests.rs"]
mod csimp_tests;

#[path = "decode_parser.rs"]
mod parser;

#[path = "decode_matcher_modern.rs"]
mod matcher_modern;

#[cfg(test)]
#[path = "decode_matcher_modern_tests.rs"]
mod matcher_modern_tests;

impl Reader<'_, '_> {
    fn array(&self, pointer: u64) -> OleanResult<Vec<u64>> {
        if !is_ptr(pointer) {
            return Err(invalid("extension Array is not an object pointer"));
        }
        let r = self.region;
        let offset = r.ptr_to_offset(pointer)?;
        let h = r.read_header_at(offset)?;
        if !matches!(h.tag, tags::ARRAY | tags::STRUCT_ARRAY)
            || h.rc != 0
            || h.other != 0
            || h.cs_sz != if self.legacy { 0 } else { 1 }
        {
            return Err(invalid("unsupported extension Array header"));
        }
        let length = r.read_usize_at(offset + 8, "typed extension array")?;
        let capacity = r.read_usize_at(offset + 16, "typed extension capacity")?;
        if length > MAX_ITEMS || capacity < length {
            return Err(invalid("extension Array length/capacity bound"));
        }
        let remaining = self
            .remaining_items
            .get()
            .checked_sub(length)
            .ok_or_else(|| invalid("total extension Array item budget exhausted"))?;
        self.remaining_items.set(remaining);
        r.validate_array_bounds(offset, length)?;
        (0..length)
            .map(|index| {
                r.read_u64_at(r.array_elem_offset(offset, index, "typed extension array")?)
            })
            .collect()
    }

    fn object(&self, pointer: u64, tag: u8, fields: u8, scalars: usize) -> OleanResult<usize> {
        if !is_ptr(pointer) {
            return Err(invalid("extension constructor is not an object pointer"));
        }
        let r = self.region;
        let offset = r.ptr_to_offset(pointer)?;
        let h = r.read_header_at(offset)?;
        let minimum = 8 + usize::from(fields) * 8 + scalars;
        let size = (minimum + 7) & !7;
        if h.rc != 0
            || h.tag != tag
            || h.other != fields
            || (usize::from(h.cs_sz) != size && !(self.legacy && h.cs_sz == 0))
        {
            return Err(invalid(format!(
                "unsupported extension constructor {}/{}/{}, expected {tag}/{fields}/{size}",
                h.tag, h.other, h.cs_sz
            )));
        }
        r.bytes_at(offset, size)?;
        Ok(offset)
    }

    fn field(&self, offset: usize, index: usize) -> OleanResult<u64> {
        self.region.read_u64_at(offset + 8 + index * 8)
    }

    fn name(&self, pointer: u64) -> OleanResult<Name> {
        self.region.read_kernel_name_ptr(pointer)
    }
    fn nat(&self, pointer: u64) -> OleanResult<u64> {
        self.region.read_kernel_nat_u64(pointer)
    }
    fn nats(&self, pointer: u64) -> OleanResult<Vec<u64>> {
        self.array(pointer)?
            .into_iter()
            .map(|pointer| self.nat(pointer))
            .collect()
    }
    fn boolean(&self, offset: usize) -> OleanResult<bool> {
        match self.region.bytes_at(offset, 1)?[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(invalid("invalid extension Boolean")),
        }
    }

    fn extension(&self, pointer: u64) -> OleanResult<TypedExtension> {
        let offset = self.object(pointer, 0, 2, 0)?;
        let extension_name = self.name(self.field(offset, 0)?)?;
        let rows = self.array(self.field(offset, 1)?)?;
        let source_rows = Some(rows.len());
        let selected = kind(&extension_name);
        // A compiler-attribute row Clean cannot read is a binding it cannot
        // see, and the declaration's own body would compile where Lean runs
        // another, so a Lean row of either table (v1 or v2 layout) that does
        // not decode fails the read instead of becoming `Unmeasured`
        // (`docs/DECISIONS.md` R149). Measured on Lean v4.8.0 (v1): with the
        // rows `Unmeasured`, `implSlow 1` printed `3` at exit 0 where Lean
        // prints `2`.
        let compiler_attr = matches!(
            selected,
            Kind::ImplementedBy | Kind::Extern | Kind::Noncomputable | Kind::CSimp
        );
        let strict = compiler_attr && !self.legacy;
        let mut undecoded_entries = 0;
        let mut entries = Vec::with_capacity(rows.len());
        for (index, pointer) in rows.into_iter().enumerate() {
            // v1 Name/Array envelopes have separate measured support. That
            // does not establish its extension payload ABI; retain each row
            // rather than reinterpreting it as v2 or Clean's legacy encoding.
            // Class/instance rows, the compiler-attribute tables and
            // `Lean.aliasExtension` (`AliasEntry := Name × Name` in Lean 4.8.0
            // as in the pin; every row of v4.8.0's Init decodes to the pairs
            // its `getModuleEntries` prints) have measured v1 layouts. Other
            // extension families remain inert.
            let measured_v1 = compiler_attr
                || matches!(
                    selected,
                    Kind::Alias | Kind::Class | Kind::Instance | Kind::Matcher
                );
            let row = if self.layout == TypedModuleLayout::LeanV1 && !measured_v1 {
                Err(invalid("Lean v1 extension payload ABI is unmeasured"))
            } else {
                match selected {
                Kind::Alias => self.alias(pointer),
                Kind::Class => self.class(pointer).map(TypedExtensionEntry::Class),
                Kind::Matcher if !self.legacy => self.matcher(pointer),
                Kind::Instance if !self.legacy => self.instance(pointer).map(TypedExtensionEntry::Instance),
                Kind::Simp if !self.legacy => self.simp(pointer).map(TypedExtensionEntry::Simp),
                Kind::Structure if !self.legacy => self.structure(pointer).map(TypedExtensionEntry::Structure),
                Kind::CSimp if !self.legacy => self.csimp(pointer),
                Kind::ImplementedBy if !self.legacy => self.implemented_by(pointer),
                Kind::Extern if !self.legacy => self.extern_row(pointer),
                Kind::Noncomputable if !self.legacy => self.noncomputable(pointer),
                _ if self.legacy => self.legacy_named(pointer),
                _ => Err(invalid("modern opaque extension payload unmeasured; not a Clean Name/payload encoding")),
            }
            };
            match row {
                Ok(row) => entries.push(row),
                Err(error) if strict => {
                    return Err(invalid(format!(
                        "{extension_name} row {index} does not decode ({error}); a compiler \
                         attribute Clean cannot read would let a body compile that Lean never runs"
                    )));
                }
                Err(error) => {
                    undecoded_entries += 1;
                    entries.push(TypedExtensionEntry::Unmeasured {
                        index,
                        reason: error.to_string(),
                    });
                }
            }
        }
        Ok(TypedExtension {
            extension_name,
            source_rows,
            entries,
            undecoded_entries,
            compiler_names: None,
        })
    }

    /// The names of one [`NamesTable`]'s rows, with the row's constructor
    /// (`Decl.fdecl` 0 / `Decl.extern` 1) or `InlineAttributeKind` index.
    /// Every row must read; a row of another shape fails the whole table.
    fn compiler_names(&self, pointer: u64, table: NamesTable) -> OleanResult<Vec<(Name, u64)>> {
        let offset = self.object(pointer, 0, 2, 0)?;
        self.array(self.field(offset, 1)?)?
            .into_iter()
            .map(|row| match table {
                NamesTable::DeclMap => {
                    if !is_ptr(row) {
                        return Err(invalid("IR Decl row is not an object pointer"));
                    }
                    let tag = self
                        .region
                        .read_header_at(self.region.ptr_to_offset(row)?)?
                        .tag;
                    // `fdecl (f) (xs) (type) (body) (info)` / `extern (f) (xs)
                    // (type) (ext)`, in v4.30.0-rc2 and v4.8.0 alike.
                    let fields = match tag {
                        0 => 5,
                        1 => 4,
                        _ => return Err(invalid("unmeasured IR Decl constructor")),
                    };
                    let decl = self.object(row, tag, fields, 0)?;
                    Ok((self.name(self.field(decl, 0)?)?, u64::from(tag)))
                }
                NamesTable::InlineAttrs => {
                    let entry = self.object(row, 0, 2, 0)?;
                    let kind = self.field(entry, 1)?;
                    // A boxed scalar: `lean_box(i)` is `2 * i + 1`.
                    if kind & 1 != 1 || kind >> 1 >= INLINE_ATTRIBUTE_KINDS {
                        return Err(invalid("unmeasured InlineAttributeKind"));
                    }
                    Ok((self.name(self.field(entry, 0)?)?, kind >> 1))
                }
            })
            .collect()
    }

    /// `TagDeclarationExtension` exports its exact Name array in official
    /// Lean 4.8/4.30 (EnvExtension.lean); no wrapper or Boolean is inferred.
    fn noncomputable(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        let decl = self.name(pointer)?;
        if decl.is_anon() {
            return Err(invalid("anonymous noncomputable declaration"));
        }
        Ok(TypedExtensionEntry::Noncomputable { decl })
    }

    /// ScopedEnvExtension.Entry wrapping CSimp.Entry's three Name fields.
    fn csimp(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        let (pointer, namespace) = self.scoped(pointer)?;
        let offset = self.object(pointer, 0, 3, 0)?;
        let from = self.name(self.field(offset, 0)?)?;
        let to = self.name(self.field(offset, 1)?)?;
        let theorem = self.name(self.field(offset, 2)?)?;
        if from.is_anon()
            || to.is_anon()
            || theorem.is_anon()
            || namespace.as_ref().is_some_and(Name::is_anon)
        {
            return Err(invalid("anonymous CSimp identity or namespace"));
        }
        Ok(TypedExtensionEntry::CSimp {
            from,
            to,
            theorem,
            namespace,
        })
    }

    /// One `implementedByAttr` row: a `Name × Name` pair.
    fn implemented_by(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        let offset = self.object(pointer, 0, 2, 0)?;
        Ok(TypedExtensionEntry::ImplementedBy {
            decl: self.name(self.field(offset, 0)?)?,
            target: self.name(self.field(offset, 1)?)?,
        })
    }

    /// One `externAttr` row: `Name × ExternAttrData`. v4.30's
    /// `ExternAttrData` has the single field `entries : List ExternEntry` and
    /// is represented by its list (`List.nil` the scalar `lean_box(0)`,
    /// `List.cons` tag 1); v4.8.0's is `{ arity? : Option Nat, entries }`, a
    /// two-field constructor with tag 0, so the tag tells the two apart.
    /// `ExternEntry` is `adhoc (backend)` (tag 0), `inline (backend)
    /// (pattern)` (tag 1), `standard (backend) (fn)` (tag 2), v4.8.0's
    /// `foreign (backend) (fn)` (tag 3) or v4.30's scalar `opaque`
    /// (`lean_box(3)`), as `lean_ir`'s decoder reads them.
    fn extern_row(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        use clean_kernel::env::{
            CompilerExternArity, CompilerExternDescriptor, CompilerExternEntry,
            CompilerExternMetadata,
        };
        let offset = self.object(pointer, 0, 2, 0)?;
        let decl = self.name(self.field(offset, 0)?)?;
        let mut entries = Vec::new();
        let mut arity = CompilerExternArity::Unspecified;
        let mut current = self.field(offset, 1)?;
        if is_ptr(current)
            && self
                .region
                .read_header_at(self.region.ptr_to_offset(current)?)?
                .tag
                == 0
        {
            let data = self.object(current, 0, 2, 0)?;
            arity = CompilerExternArity::Legacy(self.option_nat(self.field(data, 0)?)?);
            current = self.field(data, 1)?;
        }
        loop {
            if current == 1 {
                break;
            }
            if entries.len() >= MAX_EXTERN_ENTRIES {
                return Err(invalid("ExternAttrData lists more entries than the bound"));
            }
            let cons = self.object(current, 1, 2, 0)?;
            let entry = self.field(cons, 0)?;
            current = self.field(cons, 1)?;
            if entry == 7 {
                entries.push(CompilerExternEntry::Opaque);
                continue;
            }
            if !is_ptr(entry) {
                return Err(invalid("unmeasured scalar ExternEntry"));
            }
            let at = self.region.ptr_to_offset(entry)?;
            entries.push(match self.region.read_header_at(at)?.tag {
                0 => {
                    let adhoc = self.object(entry, 0, 1, 0)?;
                    CompilerExternEntry::Adhoc {
                        backend: self.name(self.field(adhoc, 0)?)?,
                    }
                }
                tag @ (1..=3) => {
                    let row = self.object(entry, tag, 2, 0)?;
                    let backend = self.name(self.field(row, 0)?)?;
                    let text = self.string(self.field(row, 1)?)?;
                    match tag {
                        1 => CompilerExternEntry::Inline {
                            backend,
                            pattern: text,
                        },
                        2 => CompilerExternEntry::Standard {
                            backend,
                            symbol: text,
                        },
                        _ => CompilerExternEntry::Foreign {
                            backend,
                            symbol: text,
                        },
                    }
                }
                _ => return Err(invalid("unmeasured ExternEntry constructor")),
            });
        }
        if entries.is_empty() {
            return Err(invalid("ExternAttrData lists no entry"));
        }
        let descriptor = CompilerExternDescriptor { arity, entries };
        Ok(TypedExtensionEntry::Extern {
            decl,
            symbol: descriptor.diagnostic(),
            metadata: CompilerExternMetadata::Complete(descriptor),
        })
    }

    /// v4.8.0's `ExternAttrData.arity?`: `none` (`lean_box(0)`) or `some n`
    /// (tag 1, one field). Retained exactly in the typed compiler carrier.
    fn option_nat(&self, pointer: u64) -> OleanResult<Option<u64>> {
        if pointer == 1 {
            return Ok(None);
        }
        let some = self.object(pointer, 1, 1, 0)?;
        self.nat(self.field(some, 0)?).map(Some)
    }

    fn option_name(&self, pointer: u64) -> OleanResult<Option<Name>> {
        if pointer == 1 {
            return Ok(None);
        }
        let some = self.object(pointer, 1, 1, 0)?;
        self.name(self.field(some, 0)?).map(Some)
    }

    /// Select the measured five- or six-field matcher metadata representation.
    fn matcher(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        if self.layout == TypedModuleLayout::LeanV2 {
            return self.modern_matcher(pointer);
        }
        let entry = self.object(pointer, 0, 2, 0)?;
        let name = self.name(self.field(entry, 0)?)?;
        let info = self.object(self.field(entry, 1)?, 0, 5, 0)?;
        let bounded = |value: u64| -> OleanResult<u32> {
            if value > MAX_ITEMS as u64 {
                return Err(invalid(
                    "matcher field exceeds the bounded metadata surface",
                ));
            }
            u32::try_from(value).map_err(|_| invalid("matcher field does not fit u32"))
        };
        let num_params = bounded(self.nat(self.field(info, 0)?)?)?;
        let num_discrs = bounded(self.nat(self.field(info, 1)?)?)?;
        let alt_num_params = self
            .nats(self.field(info, 2)?)?
            .into_iter()
            .map(bounded)
            .collect::<OleanResult<Vec<_>>>()?;
        let u_elim_pos = self
            .option_nat(self.field(info, 3)?)?
            .map(bounded)
            .transpose()?;
        // Lean 4.8 unboxes the one-field DiscrInfo structure: each array
        // entry is its hName? Option directly (none = scalar 1, some = tag 1).
        // The genuine fixture covers both representations.
        let discr_names = self
            .array(self.field(info, 4)?)?
            .into_iter()
            .map(|pointer| self.option_name(pointer))
            .collect::<OleanResult<Vec<_>>>()?;
        if discr_names.len() != num_discrs as usize {
            return Err(invalid("matcher discriminant metadata length mismatch"));
        }
        Ok(TypedExtensionEntry::Matcher {
            name,
            info: clean_kernel::env::MatcherInfo {
                num_params,
                num_discrs,
                alt_num_params,
                u_elim_pos,
                discr_names,
                details: None,
            },
        })
    }

    fn string(&self, pointer: u64) -> OleanResult<String> {
        if !is_ptr(pointer) {
            return Err(invalid("extension String is not an object pointer"));
        }
        let offset = self.region.ptr_to_offset(pointer)?;
        if self.region.read_header_at(offset)?.rc != 0 {
            return Err(invalid("unsupported extension String header"));
        }
        Ok(self.region.read_lean_string_at(offset)?.to_owned())
    }

    fn alias(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        let offset = self.object(pointer, 0, 2, 0)?;
        Ok(TypedExtensionEntry::Alias {
            alias: self.name(self.field(offset, 0)?)?,
            target: self.name(self.field(offset, 1)?)?,
        })
    }

    fn class(&self, pointer: u64) -> OleanResult<TypedClassEntry> {
        // Lean 4.8 ClassEntry has name/outParams; the later representation
        // adds outLevelParams. Only the measured Lean v1 envelope admits the
        // two-field form. Exact tag, size and field decoding still apply.
        let old = self.layout == TypedModuleLayout::LeanV1;
        let offset = self.object(pointer, 0, if old { 2 } else { 3 }, 0)?;
        let name = self.name(self.field(offset, 0)?)?;
        let out_params = self.nats(self.field(offset, 1)?)?;
        // `outLevelParams` is measured for shape only: no registrar reads it.
        if !old {
            self.nats(self.field(offset, 2)?)?;
        }
        Ok(TypedClassEntry { name, out_params })
    }

    /// Unwrap a `ScopedEnvExtension.Entry`, returning the inner entry pointer
    /// and, for the `scoped ns e` constructor, the declaring namespace.
    fn scoped(&self, pointer: u64) -> OleanResult<(u64, Option<Name>)> {
        if !is_ptr(pointer) {
            return Err(invalid("scoped extension entry is not a pointer"));
        }
        let offset = self.region.ptr_to_offset(pointer)?;
        match self.region.read_header_at(offset)?.tag {
            0 => {
                self.object(pointer, 0, 1, 0)?;
                Ok((self.field(offset, 0)?, None))
            }
            1 => {
                self.object(pointer, 1, 2, 0)?;
                let namespace = self.name(self.field(offset, 0)?)?;
                Ok((self.field(offset, 1)?, Some(namespace)))
            }
            _ => Err(invalid("unmeasured scoped extension constructor")),
        }
    }

    fn instance(&self, pointer: u64) -> OleanResult<TypedInstanceEntry> {
        let (pointer, namespace) = self.scoped(pointer)?;
        let offset = self.object(pointer, 0, 5, 1)?;
        let some = self.object(self.field(offset, 3)?, 1, 1, 0)?;
        // An unknown AttributeKind tag is `Unmeasured`. A `scoped` entry keeps
        // its namespace: the registrar records it and the elaborator gates the
        // instance on `open` (`ScopedInstanceState`).
        let attr_kind = ParsedAttrKind::from_tag(self.region.bytes_at(offset + 48, 1)?[0])
            .ok_or_else(|| invalid("unmeasured instance AttributeKind"))?;
        let scope = (attr_kind == ParsedAttrKind::Scoped)
            .then_some(namespace)
            .flatten();
        // Keys/val are not reconstructed by this metadata-only increment.
        Ok(TypedInstanceEntry {
            instance_name: self.name(self.field(some, 0)?)?,
            priority: self.nat(self.field(offset, 2)?)?,
            synth_order: self.nats(self.field(offset, 4)?)?,
            scope,
        })
    }

    /// One `StructureInfo` (`Lean/Structure.lean:60-70`): `structName`,
    /// `fieldNames : Array Name`, `fieldInfo : Array StructureFieldInfo`,
    /// `parentInfo : Array StructureParentInfo`; no scoped wrapper, no scalar.
    /// `fieldInfo` rows are measured for shape (4 object slots + the
    /// `binderInfo` byte); the registrar reads the field NAMES, each field's
    /// `projFn` (to find a private field's projection) and the parents.
    fn structure(&self, pointer: u64) -> OleanResult<TypedStructureEntry> {
        let offset = self.object(pointer, 0, 4, 0)?;
        let struct_name = self.name(self.field(offset, 0)?)?;
        let field_names = self
            .array(self.field(offset, 1)?)?
            .into_iter()
            .map(|p| self.name(p))
            .collect::<OleanResult<Vec<_>>>()?;
        let mut field_proj_fns = Vec::new();
        for info in self.array(self.field(offset, 2)?)? {
            // `StructureFieldInfo`: `fieldName`, `projFn`, `subobject?`,
            // `autoParam?`, then the `binderInfo` byte.
            let info = self.object(info, 0, 4, 1)?;
            field_proj_fns.push((
                self.name(self.field(info, 0)?)?,
                self.name(self.field(info, 1)?)?,
            ));
        }
        let parents = self
            .array(self.field(offset, 3)?)?
            .into_iter()
            .map(|p| {
                // `StructureParentInfo`: `structName`, `projFn`, then the
                // `subobject : Bool` byte after the two object slots.
                let parent = self.object(p, 0, 2, 1)?;
                Ok(TypedStructureParent {
                    struct_name: self.name(self.field(parent, 0)?)?,
                    proj_fn: self.name(self.field(parent, 1)?)?,
                    subobject: self.boolean(parent + 8 + 2 * 8)?,
                })
            })
            .collect::<OleanResult<Vec<_>>>()?;
        Ok(TypedStructureEntry {
            struct_name,
            field_names,
            field_proj_fns,
            parents,
        })
    }

    fn simp(&self, pointer: u64) -> OleanResult<TypedSimpEntry> {
        let (pointer, _namespace) = self.scoped(pointer)?;
        if !is_ptr(pointer) {
            return Err(invalid("SimpEntry is not a pointer"));
        }
        let offset = self.region.ptr_to_offset(pointer)?;
        let tag = self.region.read_header_at(offset)?.tag;
        match tag {
            0 => {
                self.object(pointer, 0, 1, 0)?;
                let thm = self.object(self.field(offset, 0)?, 0, 5, 3)?;
                let origin = self.object(self.field(thm, 4)?, 0, 1, 2)?;
                if self.boolean(origin + 17)? {
                    return Err(invalid("inverse simp theorem direction remains unmeasured"));
                }
                // The post flag is measured but not carried: the existing
                // registry does not implement it. Proof/keys/levels and
                // perm/rfl remain unmeasured.
                self.boolean(origin + 16)?;
                self.boolean(thm + 49)?;
                self.boolean(thm + 50)?;
                let lemma_name = self.name(self.field(origin, 0)?)?;
                let priority = self.nat(self.field(thm, 3)?)?;
                self.boolean(thm + 48)?;
                Ok(TypedSimpEntry {
                    lemma_name,
                    priority,
                })
            }
            1 | 2 => {
                self.object(pointer, tag, tag, 0)?;
                // Equation-lemma identities are validated but not registered as
                // extra simp lemmas. Existing unfolding semantics are unchanged.
                if tag == 2 {
                    for name in self.array(self.field(offset, 1)?)? {
                        self.name(name)?;
                    }
                }
                Ok(TypedSimpEntry {
                    lemma_name: self.name(self.field(offset, 0)?)?,
                    priority: 1000,
                })
            }
            _ => Err(invalid("unmeasured SimpEntry constructor")),
        }
    }

    fn legacy_named(&self, pointer: u64) -> OleanResult<TypedExtensionEntry> {
        if !is_ptr(pointer) {
            return if pointer & 1 == 1 {
                Ok(TypedExtensionEntry::RawScalar)
            } else {
                Err(invalid("null legacy extension entry"))
            };
        }
        let offset = self.object(pointer, 0, 2, 0)?;
        let name = self.name(self.field(offset, 0)?)?;
        let data_pointer = self.field(offset, 1)?;
        let data = if !is_ptr(data_pointer) {
            ParsedExtensionEntryData::Scalar(data_pointer)
        } else {
            let data_offset = self.region.ptr_to_offset(data_pointer)?;
            let header = self.region.read_header_at(data_offset)?;
            let size = usize::from(header.cs_sz);
            if header.rc != 0 || header.other != 0 || size < 8 {
                return Err(invalid(
                    "legacy opaque payload lacks a bounded pointer-free object envelope",
                ));
            }
            ParsedExtensionEntryData::Object(self.region.bytes_at(data_offset, size)?.to_vec())
        };
        Ok(TypedExtensionEntry::Named { name, data })
    }
}

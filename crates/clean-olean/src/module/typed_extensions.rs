// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Load-only extension identities. These records do not certify a declaration,
//! reconstruct skipped proof/key payloads, or implement scoped registration.
//! The public `Parsed*` representation remains an explicitly lossy projection.
//!
//! A typed record carries exactly what a registrar reads. Identity bytes the
//! decoder measures but no registrar consumes — a simp entry's `post` flag,
//! kind and scope, a class's `outLevelParams` — are VALIDATED by `decode` (a
//! malformed row is still `Unmeasured`) and then dropped; the public `Parsed*`
//! entry is where they stay available to callers. An INSTANCE's scope
//! namespace IS carried (`TypedInstanceEntry::scope`): the loader records it in
//! `ScopedInstanceState` and the elaborator gates a `scoped instance` on
//! `open`, so the field and its reader exist together. `Lean.structureExt`
//! rows are carried as [`TypedStructureEntry`] for the structure registrar.
//! `Lean.Compiler.implementedByAttr` and `Lean.externAttr` rows are carried
//! for the compiler-attribute registrar (`TypedExtensionEntry::ImplementedBy`,
//! `TypedExtensionEntry::Extern`). `Lean.noncomputableExt` restores the
//! declaration's code-generation ineligibility as `Noncomputable`. Unlike
//! diagnostic-only tables, a row of these compiler tables
//! in a Lean layout (v2, or v1 as Lean 4.8.0 writes it) that does not decode
//! fails the module read instead of becoming `Unmeasured`: an unread binding
//! is a body compiled where Lean runs another (`docs/DECISIONS.md` R149).
//! The measured v1 class/instance tables also feed their existing registrars;
//! every other v1 table stays `Unmeasured`.
//!
//! In a part that carries `implementedByAttr` rows, two more tables are read
//! for their NAMES only (`TypedExtension::compiler_names`), beside their rows
//! (which stay `Unmeasured`, so the accounting is unchanged): which
//! declarations `Lean.IR.declMapExt` holds IR for, and the
//! `Lean.Compiler.inlineAttrs` kind of each declaration. `.olean` import reads
//! them to tell whether Lean compiled a bound declaration before its binding
//! (`import::late_binding`).

use super::{ParsedExtension, ParsedExtensionEntry, ParsedExtensionEntryData};
use clean_kernel::name::Name;

mod decode;

pub use decode::exported_term_syntax::{
    read_exported_term_syntax, ExportedTermSyntax, LeadingIdentBehavior, ParserRegistration,
    ScopedSyntaxEntry, TermElaboratorRegistration,
};

#[derive(Clone, Debug)]
pub(crate) struct TypedExtension {
    pub extension_name: Name,
    /// Exact raw Array population, absent for the lossy Parsed compatibility API.
    pub source_rows: Option<usize>,
    pub entries: Vec<TypedExtensionEntry>,
    pub undecoded_entries: usize,
    /// For `Lean.IR.declMapExt` (each IR declaration's name and `Decl`
    /// constructor: `0` fdecl, `1` extern) and `Lean.Compiler.inlineAttrs`
    /// (each declaration's name and `InlineAttributeKind` index: `0` inline,
    /// `1` noinline, `2` macroInline, `3` inlineIfReduce, `4` alwaysInline),
    /// read only in a part with `implementedByAttr` rows (module docs). `None`
    /// for every other table, in every other part, and when a row did not read.
    pub compiler_names: Option<Vec<(Name, u64)>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TypedExtensionEntry {
    Named {
        name: Name,
        data: ParsedExtensionEntryData,
    },
    /// An opaque legacy sentinel with no name. No registrar reads its value;
    /// `ParsedExtensionEntry::RawScalar` keeps it for round-trips.
    RawScalar,
    Instance(TypedInstanceEntry),
    Class(TypedClassEntry),
    /// Exact measured match-compiler metadata; never inferred from a name.
    Matcher {
        name: Name,
        info: clean_kernel::env::MatcherInfo,
    },
    Simp(TypedSimpEntry),
    /// One `Lean.structureExt` row: field table and `extends` parents.
    Structure(TypedStructureEntry),
    Alias {
        alias: Name,
        target: Name,
    },
    /// One `Lean.Compiler.implementedByAttr` row (a `ParametricAttribute
    /// Name`, so a `Name × Name` pair): compiled code runs `target` wherever
    /// it calls `decl`. Read by `register_real_compiler_attr_entries`.
    ImplementedBy {
        decl: Name,
        target: Name,
    },
    /// One direct Name in Lean's `TagDeclarationExtension` for source
    /// declarations explicitly excluded from code generation.
    Noncomputable {
        decl: Name,
    },
    /// A scoped compiler equality from Lean.Compiler.CSimp.ext.
    CSimp {
        from: Name,
        to: Name,
        theorem: Name,
        namespace: Option<Name>,
    },
    /// One `Lean.externAttr` row (`Name × ExternAttrData`): compiled code
    /// calls the external implementation, never `decl`'s value. `symbol`
    /// remains the existing refusal label; `metadata` retains every ordered
    /// entry, backend, kind and represented legacy arity. Neither admits a
    /// native implementation. Read by `register_real_compiler_attr_entries`.
    Extern {
        decl: Name,
        symbol: String,
        metadata: clean_kernel::env::CompilerExternMetadata,
    },
    /// The original position remains visible, even when no identity is
    /// readable; `ExtensionLoadAccounting::undecoded_reasons` reports both.
    Unmeasured {
        index: usize,
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypedInstanceEntry {
    pub instance_name: Name,
    pub priority: u64,
    pub synth_order: Vec<u64>,
    /// The declaring namespace of a `scoped instance`
    /// (`ScopedEnvExtension.Entry.scoped ns e`); `None` for a global one.
    /// Read by `register_real_instance_entries` into `ScopedInstanceState`.
    pub scope: Option<Name>,
}

/// A decoded `StructureInfo` (`Lean/Structure.lean`): the DIRECT field names
/// in constructor order, and the `extends` parents with Lean's own
/// `subobject` flag and projection function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypedStructureEntry {
    pub struct_name: Name,
    pub field_names: Vec<Name>,
    /// `(fieldName, projFn)` per `StructureFieldInfo`: the projection a
    /// private field is read through is `_private.<mod>.<n>.S.f`, not `S.f`.
    pub field_proj_fns: Vec<(Name, Name)>,
    pub parents: Vec<TypedStructureParent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypedStructureParent {
    pub struct_name: Name,
    pub proj_fn: Name,
    pub subobject: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypedClassEntry {
    pub name: Name,
    pub out_params: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypedSimpEntry {
    pub lemma_name: Name,
    pub priority: u64,
}

/// Compatibility ONLY: legacy public callers supplied display strings, so the
/// original typed identity is unavailable. This is never called by a raw/direct
/// loader and never serves as fallback after a typed decode failure.
pub(crate) fn legacy_display_extension_projection(
    input: &[ParsedExtension],
) -> Vec<TypedExtension> {
    input
        .iter()
        .map(|extension| TypedExtension {
            source_rows: None,
            extension_name: if extension.extension_name.is_empty() {
                Name::anon()
            } else {
                Name::interned(&extension.extension_name)
            },
            undecoded_entries: extension.undecoded_entries,
            compiler_names: None,
            entries: extension
                .entries
                .iter()
                .map(|entry| match entry {
                    ParsedExtensionEntry::Named { name, data } => TypedExtensionEntry::Named {
                        name: Name::interned(name),
                        data: data.clone(),
                    },
                    ParsedExtensionEntry::RawScalar(_) => TypedExtensionEntry::RawScalar,
                    ParsedExtensionEntry::Alias { alias, target } => TypedExtensionEntry::Alias {
                        alias: Name::interned(alias),
                        target: Name::interned(target),
                    },
                    ParsedExtensionEntry::Instance(entry) => {
                        TypedExtensionEntry::Instance(TypedInstanceEntry {
                            instance_name: Name::interned(&entry.instance_name),
                            priority: entry.priority,
                            synth_order: entry.synth_order.clone(),
                            scope: (entry.attr_kind == super::ParsedAttrKind::Scoped)
                                .then(|| entry.scope_ns.as_deref().map(Name::interned))
                                .flatten(),
                        })
                    }
                    ParsedExtensionEntry::Structure(entry) => {
                        TypedExtensionEntry::Structure(TypedStructureEntry {
                            struct_name: Name::interned(&entry.struct_name),
                            field_names: entry
                                .field_names
                                .iter()
                                .map(|f| Name::interned(f))
                                .collect(),
                            field_proj_fns: entry
                                .fields
                                .iter()
                                .map(|f| {
                                    (Name::interned(&f.field_name), Name::interned(&f.proj_fn))
                                })
                                .collect(),
                            parents: entry
                                .parents
                                .iter()
                                .map(|p| TypedStructureParent {
                                    struct_name: Name::interned(&p.struct_name),
                                    proj_fn: Name::interned(&p.proj_fn),
                                    subobject: p.subobject,
                                })
                                .collect(),
                        })
                    }
                    ParsedExtensionEntry::Class(entry) => {
                        TypedExtensionEntry::Class(TypedClassEntry {
                            name: Name::interned(&entry.name),
                            out_params: entry.out_params.clone(),
                        })
                    }
                    ParsedExtensionEntry::Simp(entry) => {
                        TypedExtensionEntry::Simp(TypedSimpEntry {
                            lemma_name: Name::interned(&entry.lemma_name),
                            priority: entry.priority,
                        })
                    }
                })
                .collect(),
        })
        .collect()
}

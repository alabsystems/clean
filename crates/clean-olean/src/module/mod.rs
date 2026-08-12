// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module data parsing from .olean files
//!
//! The .olean file structure at the high level:
//!
//! ```text
//! Offset 0-..:   Header (version-dependent)
//! Offset H:      Root pointer to ModuleData object (H = header size)
//! Offset H+8+:   Compacted region (serialized objects)
//! ```
//!
//! ModuleData (structure that stores a module's compiled data):
//!
//! ```text
//! structure ModuleData where
//!   isModule        : Bool               -- participating in module system? (scalar field)
//!   imports         : Array Import       -- import declarations (ptr field 0)
//!   constNames      : Array Name         -- exported constant names (ptr field 1)
//!   constants       : Array ConstantInfo -- constant definitions (ptr field 2)
//!   extraConstNames : Array Name         -- extra constants from codegen (ptr field 3)
//!   entries         : Array (Name × Array EnvExtensionEntry) -- extension entries (ptr field 4)
//! ```
//!
//! Note: In Lean's compacted region format, scalar fields like `isModule` are stored
//! AFTER the pointer fields. The header's `m_other` field contains the number of
//! pointer fields (5 for ModuleData). We currently ignore `isModule` as it's always
//! true for standard .olean files.

mod analysis;
mod constants;
mod extensions;
mod readers;

#[cfg(test)]
mod tests;

pub use analysis::{ArrayAnalysis, ElementInfo, RootAnalysis};
pub(crate) use extensions::{LEAN_CLASS_EXTENSION, LEAN_INSTANCE_EXTENSION};

use crate::expr::ParsedExpr;

/// Import declaration from an .olean file.
#[derive(Debug, Clone)]
pub struct ParsedImport {
    /// Name of the imported module.
    pub module_name: String,
    /// Whether this is a runtime-only import.
    pub runtime_only: bool,
}

/// A parsed constant from the module
#[derive(Debug, Clone)]
pub struct ParsedConstant {
    /// Full name of the constant
    pub name: String,
    /// Kind of constant
    pub kind: ConstantKind,
    /// Universe parameter names
    pub level_params: Vec<String>,
    /// Type of the constant
    pub type_: Option<ParsedExpr>,
    /// Value (for definitions, theorems)
    pub value: Option<ParsedExpr>,
    /// Extra data for inductive types
    pub inductive_val: Option<InductiveValData>,
    /// Extra data for constructors
    pub constructor_val: Option<ConstructorValData>,
    /// Extra data for recursors
    pub recursor_val: Option<RecursorValData>,
    /// Reducibility hints (for definitions only)
    pub hints: Option<ReducibilityHintsData>,
    /// Declaration safety metadata.
    ///
    /// The historical field name reflects its original `DefinitionVal`-only
    /// scope. It now also carries `AxiomVal.isUnsafe` and
    /// `OpaqueVal.isUnsafe`: `Some(Safe | Unsafe)` for axioms/opaques and
    /// `Some(Safe | Unsafe | Partial)` for definitions. Inductive-family
    /// declarations retain their corresponding `is_unsafe` field in the
    /// kind-specific value below. Dropping any of these flags silently grants
    /// safe logical authority to a declaration Lean excluded from its trusted
    /// kernel fragment, so recognized layouts fail closed instead of
    /// fabricating `Safe`. `None` is reserved for declaration kinds with no
    /// safety field.
    pub definition_safety: Option<DefinitionSafety>,
    /// Which quotient primitive this is (for `ConstantKind::Quot` only).
    ///
    /// `QuotVal` (`ConstantInfo.quotInfo`, tag 4) carries a `kind`
    /// discriminant distinguishing `Quot` / `Quot.mk` / `Quot.lift` /
    /// `Quot.ind` / `Quot.sound`. Earlier the discriminant tag was read
    /// only as the `Quot` constant kind and the per-primitive
    /// `QuotKind` was discarded; this field preserves it so a parsed
    /// quotient round-trips losslessly.
    pub quot_kind: Option<ParsedQuotKind>,
}

/// The kind of quotient primitive carried by `QuotVal`.
///
/// Mirrors `clean_kernel::quot::QuotKind`. The numeric discriminants
/// match the tags written by the olean exporter
/// (`OleanExporter::write_quotient_info`): `Type=0`, `Mk=1`, `Lift=2`,
/// `Ind=3`, `Sound=4`.
///
/// # Forward Compatibility
///
/// Marked `#[non_exhaustive]` to allow future Lean 4 quotient kinds
/// without breaking downstream code. Always include a wildcard arm in
/// match expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParsedQuotKind {
    /// `Quot` — the quotient type former (tag 0).
    Type,
    /// `Quot.mk` — the constructor (tag 1).
    Mk,
    /// `Quot.lift` — the eliminator (tag 2).
    Lift,
    /// `Quot.ind` — the induction principle (tag 3).
    Ind,
    /// `Quot.sound` — the quotient soundness axiom (tag 4).
    Sound,
}

impl ParsedQuotKind {
    /// Decode a `QuotVal.kind` discriminant tag into a `ParsedQuotKind`.
    ///
    /// Returns `None` for tags outside the known range so callers can
    /// distinguish "absent / malformed" from a recognized kind without
    /// fabricating one.
    pub fn from_tag(tag: u64) -> Option<Self> {
        match tag {
            0 => Some(ParsedQuotKind::Type),
            1 => Some(ParsedQuotKind::Mk),
            2 => Some(ParsedQuotKind::Lift),
            3 => Some(ParsedQuotKind::Ind),
            4 => Some(ParsedQuotKind::Sound),
            _ => None,
        }
    }

    /// Encode this kind back to its `QuotVal.kind` discriminant tag.
    ///
    /// Inverse of [`ParsedQuotKind::from_tag`]: `from_tag(k.to_tag()) ==
    /// Some(k)` for every variant.
    #[must_use]
    pub fn to_tag(self) -> u64 {
        match self {
            ParsedQuotKind::Type => 0,
            ParsedQuotKind::Mk => 1,
            ParsedQuotKind::Lift => 2,
            ParsedQuotKind::Ind => 3,
            ParsedQuotKind::Sound => 4,
        }
    }
}

/// Reducibility hints from `DefinitionVal`.
///
/// Lean represents the nullary `opaque`/`abbrev` constructors as tagged
/// scalars and `regular` as a heap object carrying an unboxed `UInt32`.
/// Reference: Lean 4 `src/kernel/declaration.h:15-18`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHintsData {
    /// opaque (tag 0) — never unfold
    Opaque,
    /// abbrev (tag 1) — always unfold (`@[reducible]`)
    Abbrev,
    /// regular (tag 2) — unfold based on height ordering
    Regular(u32),
}

/// Definition safety flag carried by `DefinitionVal`.
///
/// Mirrors Lean 4's `DefinitionSafety` enum
/// (`src/Lean/Declaration.lean`). The numeric discriminants match the
/// `safety` scalar written in `DefinitionVal`: `unsafe = 0`, `safe = 1`,
/// `partial = 2`.
///
/// # Forward Compatibility
///
/// Marked `#[non_exhaustive]` to allow future Lean 4 safety levels
/// without breaking downstream code. Always include a wildcard arm in
/// match expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DefinitionSafety {
    /// `safe` (tag 1) — fully checked by the kernel (the common case).
    Safe,
    /// `unsafe` (tag 0) — bypasses termination/positivity checking.
    Unsafe,
    /// `partial` (tag 2) — a `partial def`; not reduced by the kernel.
    Partial,
}

impl DefinitionSafety {
    /// Decode a `DefinitionVal.safety` discriminant tag.
    ///
    /// Returns `None` for tags outside the known range so callers can
    /// distinguish "absent / malformed" from a recognized level without
    /// fabricating one.
    pub fn from_tag(tag: u64) -> Option<Self> {
        match tag {
            0 => Some(DefinitionSafety::Unsafe),
            1 => Some(DefinitionSafety::Safe),
            2 => Some(DefinitionSafety::Partial),
            _ => None,
        }
    }

    /// Encode this safety level back to its `DefinitionVal.safety` tag.
    ///
    /// Inverse of [`DefinitionSafety::from_tag`]: `from_tag(s.to_tag()) ==
    /// Some(s)` for every variant.
    #[must_use]
    pub fn to_tag(self) -> u64 {
        match self {
            DefinitionSafety::Safe => 1,
            DefinitionSafety::Unsafe => 0,
            DefinitionSafety::Partial => 2,
        }
    }
}

/// Extra data from InductiveVal
#[derive(Debug, Clone)]
pub struct InductiveValData {
    pub num_params: u32,
    pub num_indices: u32,
    /// Names of all inductives in mutual group
    pub all: Vec<String>,
    /// Constructor names
    pub ctors: Vec<String>,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
    pub is_nested: bool,
}

/// Extra data from ConstructorVal
#[derive(Debug, Clone)]
pub struct ConstructorValData {
    /// Name of the inductive type
    pub induct: String,
    /// Constructor index
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}

/// Extra data from RecursorVal
#[derive(Debug, Clone)]
pub struct RecursorValData {
    /// Names of all inductives in mutual group
    pub all: Vec<String>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    /// Recursor rules for each constructor
    pub rules: Vec<RecursorRuleData>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// A recursor rule for a constructor
#[derive(Debug, Clone)]
pub struct RecursorRuleData {
    pub ctor: String,
    pub num_fields: u32,
    pub rhs: Option<ParsedExpr>,
}

/// The level at which .olean data is exported.
///
/// Lean 4 splits module data into multiple `.olean` parts:
/// - `.olean` (exported) - Public API for downstream modules
/// - `.olean.server` - LSP server metadata (e.g., hover info)
/// - `.olean.private` - Private implementation details
///
/// This matches Lean 4's `OLeanLevel` enum in `Lean/Environment.lean`.
/// Source: `./clean/lean4/src/Lean/Environment.lean:1531-1539`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum OLeanLevel {
    /// Public API data (`.olean`) - this is the default level
    #[default]
    Exported,
    /// LSP server metadata (`.olean.server`)
    Server,
    /// Private implementation details (`.olean.private`)
    Private,
}

impl OLeanLevel {
    /// Get the file extension suffix for this level.
    ///
    /// Returns "" for Exported, ".server" for Server, ".private" for Private.
    pub fn file_suffix(&self) -> &'static str {
        match self {
            OLeanLevel::Exported => "",
            OLeanLevel::Server => ".server",
            OLeanLevel::Private => ".private",
        }
    }

    /// Parse level from a file path.
    ///
    /// Returns `Some(level)` if the path ends with a recognized olean suffix.
    pub fn from_path(path: &std::path::Path) -> Option<(OLeanLevel, std::path::PathBuf)> {
        let file_name = path.file_name()?.to_str()?;

        if file_name.ends_with(".olean.private") {
            let base = path.with_file_name(file_name.strip_suffix(".private")?);
            Some((OLeanLevel::Private, base))
        } else if file_name.ends_with(".olean.server") {
            let base = path.with_file_name(file_name.strip_suffix(".server")?);
            Some((OLeanLevel::Server, base))
        } else if file_name.ends_with(".olean") {
            Some((OLeanLevel::Exported, path.to_path_buf()))
        } else {
            None
        }
    }

    /// Get all levels in the order they should be loaded.
    pub fn all() -> [OLeanLevel; 3] {
        [
            OLeanLevel::Exported,
            OLeanLevel::Server,
            OLeanLevel::Private,
        ]
    }
}

impl std::fmt::Display for OLeanLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OLeanLevel::Exported => write!(f, "exported"),
            OLeanLevel::Server => write!(f, "server"),
            OLeanLevel::Private => write!(f, "private"),
        }
    }
}

/// A parsed module with its associated olean level.
///
/// Wraps `ParsedModule` with the level it was loaded from, enabling
/// part-aware processing of extension entries.
#[derive(Debug, Clone)]
pub struct ParsedModulePart {
    /// The olean level this module was loaded from
    pub level: OLeanLevel,
    /// The parsed module data
    pub module: ParsedModule,
}

/// Kind of constant
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future Lean 4 constant kinds
/// without breaking downstream code. Always include a wildcard arm in match expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ConstantKind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Quot,
    Inductive,
    Constructor,
    Recursor,
}

/// Opaque data stored inside a persistent environment extension entry.
///
/// DataValue is opaque in Lean 4, so we preserve either a tagged scalar
/// or the raw object bytes. Raw bytes only round-trip safely when the
/// payload object contains no pointers (e.g., ByteArray/scalar arrays).
///
/// # Forward Compatibility
///
/// This enum is marked `#[non_exhaustive]` to allow future data representations
/// without breaking downstream code. Always include a wildcard arm in match expressions.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ParsedExtensionEntryData {
    /// Tagged scalar or null pointer value.
    Scalar(u64),
    /// Raw object bytes (includes header). Pointer relocation is not applied.
    Object(Vec<u8>),
}

/// The attribute kind recorded on a decoded `@[instance]` registration.
///
/// Mirrors Lean 4's `AttributeKind` (`Lean/Attributes.lean`): `global = 0`,
/// `local = 1`, `scoped = 2`. Local instances should never appear in
/// persisted extension entries (they are not exported), but the tag is
/// decoded faithfully rather than assumed.
///
/// # Forward Compatibility
///
/// Marked `#[non_exhaustive]` to allow future Lean 4 attribute kinds
/// without breaking downstream code. Always include a wildcard arm in
/// match expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParsedAttrKind {
    /// `global` (tag 0) — active everywhere once imported.
    Global,
    /// `local` (tag 1) — active only in the declaring section.
    Local,
    /// `scoped` (tag 2) — active when the declaring namespace is open.
    Scoped,
}

impl ParsedAttrKind {
    /// Decode an `AttributeKind` discriminant tag.
    ///
    /// Returns `None` for tags outside the known range so callers can
    /// distinguish "unknown / malformed" from a recognized kind without
    /// fabricating one.
    pub fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(ParsedAttrKind::Global),
            1 => Some(ParsedAttrKind::Local),
            2 => Some(ParsedAttrKind::Scoped),
            _ => None,
        }
    }
}

/// A decoded `Lean.Meta.instanceExtension` entry: one `@[instance]`
/// registration persisted by a real Lean 4 `.olean`.
///
/// Lean serializes `ScopedEnvExtension.Entry InstanceEntry` per entry
/// (`Lean/Meta/Instances.lean:46-60`); of `InstanceEntry`'s fields this
/// preserves the ones the import bridge needs to restore the instance table
/// faithfully: `globalName?` (the instance's declaration name), `priority`,
/// `attrKind`, and `synthOrder` (sub-goal synthesization order, consumed by
/// `resolve_instance`). The `keys` (DiscrTree) and `val : Expr` fields are
/// intentionally not retained: the elaborator reconstructs the instance term
/// from the imported constant itself (the same path used for natively
/// declared instances), and Clean's `resolve_instance` builds its own
/// candidate ordering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedInstanceEntry {
    /// Declaration name of the instance (`InstanceEntry.globalName?`).
    pub instance_name: String,
    /// Synthesis priority (`InstanceEntry.priority`; Lean default is 1000).
    pub priority: u64,
    /// How the attribute was applied (`InstanceEntry.attrKind`).
    pub attr_kind: ParsedAttrKind,
    /// Namespace of a `scoped instance` registration
    /// (`ScopedEnvExtension.Entry.scoped`'s namespace); `None` for global.
    pub scope_ns: Option<String>,
    /// The order in which the instance's Pi-telescope binders are to be
    /// synthesized (`InstanceEntry.synthOrder : Array Nat`), as binder
    /// indices. Lean computes it at declaration time (`computeSynthOrder`,
    /// `Lean/Meta/Instances.lean:145-229`) so that each sub-goal is attempted
    /// only after the metavariables in its non-out-params have been
    /// determined; `Lean/Meta/SynthInstance.lean:337` consumes it verbatim
    /// when scheduling sub-goals.
    pub synth_order: Vec<u64>,
}

/// A decoded `Lean.classExtension` entry: one type-class declaration persisted
/// by a real Lean 4 `.olean`.
///
/// Lean serializes a `ClassEntry` per entry (`Lean/Class.lean:14-32`): the
/// class name plus the binder positions of its `outParam`s and the universe
/// positions that only appear in output-parameter types. `outParams` is the
/// field the import bridge threads into the kernel's `KernelClassInfo`
/// (`resolve_instance` reads it for two-phase out-param unification);
/// `outLevelParams` is decoded for fidelity but parked until the resolver
/// consumes it (Lean uses it only to normalize TC cache keys).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedClassEntry {
    /// Class declaration name (`ClassEntry.name`).
    pub name: String,
    /// Binder positions of the class's `outParam`s (`ClassEntry.outParams`),
    /// as 0-based indices into the class's parameter telescope. e.g. `GetElem`
    /// ⟶ `[2, 3]`, `Membership` ⟶ `[0]`, a non-out-param class ⟶ `[]`.
    pub out_params: Vec<u64>,
    /// Positions of universe level parameters that only appear in output
    /// parameter types (`ClassEntry.outLevelParams`). Decoded for completeness;
    /// not yet consumed by Clean's resolver.
    pub out_level_params: Vec<u64>,
}

/// A single environment extension entry with opaque data.
///
/// Most entries are named (Name × DataValue) pairs, but extension entry arrays
/// can also contain raw scalar elements (e.g., sentinel values like `0x1` for unit).
/// The `RawScalar` variant preserves these for roundtrip fidelity.
/// Extensions with a known Lean 4 entry layout are decoded into typed
/// variants (`Instance` for `Lean.Meta.instanceExtension`, `Class` for
/// `Lean.classExtension`).
#[derive(Debug, Clone)]
pub enum ParsedExtensionEntry {
    /// Standard named entry: (Name × DataValue) pair.
    Named {
        /// Entry key name
        name: String,
        /// Opaque DataValue payload
        data: ParsedExtensionEntryData,
    },
    /// Raw scalar element in extension entry array (e.g., sentinel, unit value).
    /// Lean 4's compacted region uses tagged scalars (LSB=1) for small values.
    RawScalar(u64),
    /// Decoded `@[instance]` registration from `Lean.Meta.instanceExtension`.
    Instance(ParsedInstanceEntry),
    /// Decoded type-class declaration from `Lean.classExtension`.
    Class(ParsedClassEntry),
}

/// Extension entries for a single persistent environment extension.
///
/// Maps an extension name to its array of entries. This corresponds to
/// Lean 4's `(Name × Array (Name × DataValue))` structure.
#[derive(Debug, Clone)]
pub struct ParsedExtension {
    /// Extension name
    pub extension_name: String,
    /// Entries for this extension
    pub entries: Vec<ParsedExtensionEntry>,
    /// Number of entries a known typed decoder recognized as belonging to
    /// this extension but could NOT decode (unexpected layout, missing
    /// `globalName?`, unknown tag, …). Such entries degrade to today's
    /// behavior — absent from `entries` — but the count keeps the loss loud
    /// (surfaced through `LoadSummary::extension_undecoded_entries`) instead
    /// of silent. Always `0` for extensions without a typed decoder.
    pub undecoded_entries: usize,
}

/// Parsed module data from .olean file
#[derive(Debug, Clone)]
pub struct ParsedModule {
    /// Constant names exported by this module
    pub const_names: Vec<String>,
    /// Constant definitions
    pub constants: Vec<ParsedConstant>,
    /// Extra constant names (codegen)
    pub extra_const_names: Vec<String>,
    /// Import declarations
    pub imports: Vec<ParsedImport>,
    /// Persistent environment extension entries.
    ///
    /// Lean 4 stores persistent env extension state in this field for .olean
    /// round-tripping. Each extension contributes an array of entries keyed
    /// by name. See Lean.Environment docs for PersistentEnvExtensionState.
    pub entries: Vec<ParsedExtension>,
    /// Optional clean payload attached to the file
    pub clean_payload: Option<CleanPayload>,
}

use crate::payload::CleanPayload;

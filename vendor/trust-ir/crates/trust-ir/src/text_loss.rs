// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What the TrustIr text grammar cannot carry (roadmap WS4.2, finding F-065;
//! interim guard for F-064 / F-070 / F-072).
//!
//! [`text_losses`] names every field of a [`Module`] whose value the current
//! text grammar (`display.rs` printer, `parser.rs` reader) would NOT carry
//! through `print → parse`. Its consumers:
//!
//! * `Display for Module` (the human dump, and therefore
//!   `crate::format::canonical`) prints a `; #lossy: <summaries>` line right
//!   after the `; TrustIr text format v1` header whenever the list is
//!   non-empty, and the parser REFUSES that line — so a lossy text can no
//!   longer be parsed back into a module that silently lacks the field
//!   (before WS4.2, `global_asm` vanished through text and with it the
//!   `GlobalAsmNotConsumable` codegen refusal — the permissive laundering).
//! * `crate::format::canonical_checked` (`fmt` feature) returns
//!   [`TextLossError`] instead of a string. The `trust-ir-fmt` binary uses it
//!   and exits 1.
//! * `crate::format::text_checked` (`fmt` feature) is the same refusal over
//!   the module printed AS STORED, with no canonical rewrite first. The CLI's
//!   `convert --to text` uses it, because `convert` is a transport.
//!
//! # The contract
//!
//! For a module in canonical form (`m == crate::format::canonicalize(m)`):
//! `text_losses(m).is_empty()` ⇒ `parse_module(&m.to_string()) == Ok(m)`.
//! The conformance corpus asserts this EXACT structural equality for every
//! loss-free fixture and for every fuzzer seed, and for every lossy fixture
//! that erasing precisely the reported losses makes the two sides equal — so
//! a field the grammar drops without a [`TextLoss`] arm is a gate failure.
//!
//! The canonical-form precondition is real and was once load-bearing in the
//! wrong direction. `Display` prints the module's OWN SSA value ids;
//! `canonicalize` renumbers them densely (every block's parameters first, then
//! instruction results) and reorders blocks. That rewrite is DECLARED, so it
//! is deliberately not a [`TextLoss`] — but it means a transport that prints
//! `canonical_checked` of a non-canonical module hands back a DIFFERENT module
//! with an empty loss list: `bin -> text -> bin` stops being byte-identical
//! and nothing reports it (the false-clean direction — a consumer validates
//! what the producer never emitted). Hence the stronger contract that
//! `crate::format::text_checked` carries, for ANY module, canonical or not:
//! `text_losses(m).is_empty()` ⇒ `parse_module(&m.to_string()) == Ok(m)`.
//! `module_roundtrip_fuzz` asserts it per seed, with an anti-vacuity guard
//! that the corpus still contains non-canonical modules.
//!
//! # The marker is a tripwire, not integrity
//!
//! Text carries no authentication. A human who deletes the `; #lossy:` line
//! gets a parseable module that has lost the named fields. The closure of the
//! permissive direction for edited text is carrying the field (roadmap WS4.4
//! / WS4.5); the authority for any consumer remains `validate_module*` on what
//! it parsed. Do not describe `#lossy` as tamper-evident.
//!
//! # Compile-time completeness
//!
//! The walk destructures `Module`, `Function`, `Global`, `StructDef`,
//! `FieldDef`, `EnumDef`, `EnumVariant`, `RecordDef`, `ProofObligation`,
//! `ProofFormula`, `ProofCertificate`, `SpecModule`, `SpecVar` and
//! `SpecInvariant` EXHAUSTIVELY, with no `..` rest pattern: adding a field to
//! any of them fails to compile here until the field is classified as carried
//! or lost. Since WS4.5's enum half the same holds for `EnumLayoutDescriptor`
//! and `EnumTagEncoding`, in [`enum_layout_text_refusal`] here and in
//! `display::write_enum_layout`: a new layout field must be given a spelling
//! or a refusal, and cannot become a silent drop. Since WS4.4 it holds for
//! `ProofFormula`, `FunctionSummary`, `CleanCicKernelRecheck`,
//! `CertificateBinding` (its WS1.13 `IslandEnvironment` included) and
//! `CoverageAssurance` too, in `display.rs`'s
//! proof-surface writers.
//!
//! # The proof surface (WS4.4)
//!
//! Function summaries, clause bindings, certificate assurance, the
//! `clean_cic` kernel re-check directive (its WS1.12a binding included), the
//! v41 obligation kinds and the v46 typed spec carrier are CARRIED since WS4.4
//! (findings F-064, F-070, F-071). Their [`TextLoss`] variants stay in the
//! enum for consumers of earlier loss reports, but the only residue any of
//! them still reports is a [`crate::proof::ClauseSort`] nested deeper than
//! [`MAX_TEXT_CLAUSE_SORT_DEPTH`]: the parser's recursive-descent sort reader
//! refuses such a sort, so the printer must not write one without `#lossy`.

use core::fmt;

use crate::constant::ConstantG;
use crate::inst::InstG;
use crate::proof::{
    ClauseSort, ProofAnnotation, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation,
};
use crate::spec::{SpecInvariant, SpecModule, SpecVar};
use crate::ty::{
    EnumDefG, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariantG, FieldDef,
    RecordDef, StructDefG,
};
use crate::value::{BlockId, EnumId, FuncId, GlobalId, ProofId, RecordId, StructId};
use crate::{FunctionG, GlobalG, ModuleG};

/// Which name a [`TextLoss::UnspellableName`] is about.
///
/// Definition-site symbols accept nonempty bare or quoted names since WS4.3;
/// empty symbols remain unrepresentable. Names inside constants and dialect
/// operations retain their narrower identifier grammars, checked separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum NameKind {
    /// `Function.name`; `index` is the position in `Module.functions`.
    Function,
    /// `Global.name`; `index` is the position in `Module.globals`.
    Global,
    /// `StructDef.name`; `index` is the position in `Module.structs`.
    Struct,
    /// `EnumDef.name`; `index` is the position in `Module.enums`.
    Enum,
    /// An `EnumVariant.name`; `index` is the enum's position.
    EnumVariant,
    /// `RecordDef.name`; `index` is the position in `Module.records`.
    Record,
    /// A `RecordDef` field name; `index` is the record's position.
    RecordField,
    /// A `Constant::Record` field name or a `Constant::SymbolAddr` symbol in a
    /// global initializer; `index` is the global's position.
    GlobalConstant,
    /// A `Constant::Record` field name or `Constant::SymbolAddr` symbol in an
    /// `Inst::Const`, or a `DialectOp` dialect / op / attribute name;
    /// `index` is the function's position.
    FunctionBody,
}

impl NameKind {
    fn token(self) -> &'static str {
        match self {
            NameKind::Function => "fn",
            NameKind::Global => "global",
            NameKind::Struct => "struct",
            NameKind::Enum => "enum",
            NameKind::EnumVariant => "enum-variant",
            NameKind::Record => "record",
            NameKind::RecordField => "record-field",
            NameKind::GlobalConstant => "global-constant",
            NameKind::FunctionBody => "fn-body",
        }
    }
}

/// Where a [`TextLoss::UnspellableFloat`] sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum FloatSite {
    /// A `Constant::Float` in a global initializer; `index` is the global's
    /// position in `Module.globals`.
    GlobalConstant,
    /// A `Constant::Float` in an `Inst::Const`, or a `bounded_output(lo, hi)`
    /// proof annotation on the function or one of its instructions; `index`
    /// is the function's position in `Module.functions`.
    FunctionBody,
    /// A `gamma_crown <epsilon>` certificate; `index` is the certificate's
    /// position in `Module.proof_certificates`.
    Certificate,
}

impl FloatSite {
    fn token(self) -> &'static str {
        match self {
            FloatSite::GlobalConstant => "global",
            FloatSite::FunctionBody => "fn",
            FloatSite::Certificate => "certificate",
        }
    }
}

/// The deepest [`ClauseSort`] the text grammar reads back (WS4.4).
///
/// `array(..)` and `datatype(..)` nest, so the parser's sort reader is
/// recursive descent and caps its depth here rather than letting adversarial
/// text exhaust the stack. Depth counts sort constructors on the longest path:
/// a scalar (`bool`, `int`, `bv(..)`, `float(..)`, `rm`) and a
/// constructor-free `datatype(..)` are depth 1, and `array(int, bool)` is
/// depth 2. A sort deeper than this is REPORTED (as the loss of the formula
/// that carries it), never printed into a text its own reader refuses.
pub const MAX_TEXT_CLAUSE_SORT_DEPTH: usize = 64;

/// The nesting depth of `sort` as [`MAX_TEXT_CLAUSE_SORT_DEPTH`] counts it.
/// The walk stops descending once it passes the cap, so measuring a hostile
/// in-memory sort costs bounded recursion.
#[must_use]
pub fn clause_sort_depth(sort: &ClauseSort) -> usize {
    fn depth(sort: &ClauseSort, level: usize) -> usize {
        if level > MAX_TEXT_CLAUSE_SORT_DEPTH {
            return level;
        }
        match sort {
            ClauseSort::Bool
            | ClauseSort::Int
            | ClauseSort::BitVec(_)
            | ClauseSort::Float { .. }
            | ClauseSort::RoundingMode => level,
            ClauseSort::Array(index, element) => {
                depth(index, level + 1).max(depth(element, level + 1))
            }
            ClauseSort::Datatype { constructors, .. } => constructors
                .iter()
                .flat_map(|(_, fields)| fields)
                .map(|(_, field)| depth(field, level + 1))
                .max()
                .unwrap_or(level),
        }
    }
    depth(sort, 1)
}

/// True iff some binding of `formula` carries a sort text cannot read back.
fn formula_has_unspellable_sort(formula: &ProofFormula) -> bool {
    formula
        .bindings
        .iter()
        .any(|(_, binding)| clause_sort_depth(&binding.sort) > MAX_TEXT_CLAUSE_SORT_DEPTH)
}

/// One field the text grammar cannot carry, with its location.
///
/// `#[non_exhaustive]`: the list only SHRINKS as the grammar grows (WS4.4
/// carries the proof surface, WS4.5 the layout/linkage surface), but a
/// consumer must not assume the set is closed. The must-refuse corpus cannot
/// express that rule (`refuse/text_loss_set_not_closed`): it is about this
/// enum, not about any module. What the corpus does pin is that a lossy row is
/// never offered as text: every artifact row's exact loss set is a manifest
/// column (`refuse/import_backed_summary_unauthenticated` loses
/// `FunctionSummary`; `refuse/global_asm_block` lost `GlobalAsm` until WS4.5
/// carried the block, and now loses nothing — its refusal survives text).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TextLoss {
    /// A `Function.summary` clause the text cannot carry.
    ///
    /// NARROWED by WS4.4: the summary is carried (`; #summary:` and its
    /// `#requires` / `#ensures` / `#decreases` / `#backed-by` block), so this
    /// now fires only for a clause binding whose [`ClauseSort`] nests deeper
    /// than [`MAX_TEXT_CLAUSE_SORT_DEPTH`]. Before WS4.4 every `Some` summary
    /// was a loss (F-064). Since v59 (WS1.14) the `#effects` line carries the
    /// effect summary, and this also fires for an effect set that is not the
    /// ONE spelling of its set (an empty, unordered or duplicated `Places`
    /// list), which the parser refuses as every other decoder does — such a
    /// module is invalid, but its text must still never be offered as
    /// lossless.
    FunctionSummary { func: FuncId },
    /// An obligation's `ProofFormula.bindings` the text cannot carry.
    ///
    /// NARROWED by WS4.4: bindings are carried (`bind "<name>" <sort>
    /// <place>`), so this now fires only for a binding whose sort nests deeper
    /// than [`MAX_TEXT_CLAUSE_SORT_DEPTH`]. Before WS4.4 every non-empty list
    /// was a loss (F-064).
    ClauseBindings { obligation: ProofId },
    /// Historical: `ProofCertificate.assurance` had no spelling. Carried since
    /// WS4.4 (`assurance <bound> digest ..`); no longer reported.
    CertificateAssurance { obligation: ProofId },
    /// Historical: a `CleanCic` certificate's `kernel_recheck` had no
    /// spelling, so a kernel-Certified module turned invalid through text
    /// (F-070). Carried since WS4.4 (`recheck module .. anchor ..`, its
    /// WS1.12a binding included); no longer reported.
    KernelRecheck { obligation: ProofId },
    /// Historical: an obligation kind the parser could not read back
    /// (`termination`, `ownership`, `custom:<ns>/<name>`, F-071). Parsed since
    /// WS4.4 (`custom("<ns>", "<name>")` is the module-text spelling of the
    /// last); no longer reported.
    ObligationKind {
        id: ProofId,
        kind: crate::proof::ObligationKind,
    },
    /// `EnumDef.layout` is `Some` and the `layout(..)` clause cannot carry it
    /// EXACTLY — the descriptor is internally inconsistent against this enum
    /// (see [`enum_layout_text_refusal`] for the exhaustive list of reasons).
    ///
    /// NARROWED by WS4.5 (enum half): a WELL-FORMED descriptor is carried, so
    /// this no longer fires for every layout-bearing enum, only for one the
    /// grammar would have to launder. Before WS4.5 text was layout-agnostic
    /// for enums and every `Some` was a loss (F-072).
    EnumLayout { enum_id: EnumId },
    /// A variant's `field_names` is non-empty but NOT parallel to its
    /// `fields` (a length mismatch `validate_module` refuses), so the
    /// `Name(field: ty, ..)` spelling cannot carry it exactly.
    ///
    /// NARROWED by WS4.5: a parallel list is carried (`Name(a: u8, : u16)`),
    /// so this no longer fires for every named variant, only for one the
    /// grammar would have to launder. Before WS4.5 every non-empty list was a
    /// loss (F-072).
    EnumFieldNames { enum_id: EnumId },
    /// `EnumDef.discriminants` carries entries a `bin -> text -> bin` round
    /// trip cannot give back: a trailing implicit (`None`) entry, which the
    /// parser rebuilds trimmed, OR an entry past `variants.len()`, which the
    /// printer never reaches at all (it indexes by variant). Checked by
    /// comparing against `discriminants_text_reconstruction`, not by testing
    /// either symptom on its own.
    EnumDiscriminantsTail { enum_id: EnumId },
    /// A struct field has a non-empty name; `struct @S { ty, .. }` carries
    /// types only (F-072).
    StructFieldNames { struct_id: StructId },
    /// A struct field has `offset: Some` (F-072).
    StructFieldOffsets { struct_id: StructId },
    /// A record field has `offset: Some` (records have no layout in text).
    RecordFieldOffsets { record_id: RecordId },
    /// Historical loss for `Global.section` / `visibility` / `retained`
    /// (F-072). These fields now have text spellings; retained for consumers
    /// of earlier loss reports. `global` is the position in `Module.globals`.
    GlobalAttrs { global: GlobalId },
    /// Historical loss for a non-empty `Module.global_asm` (F-065): dropping
    /// it launders the `GlobalAsmNotConsumable` codegen refusal. CARRIED since
    /// WS4.5 (`global_asm "<escaped>"`, one line per block), so
    /// [`text_losses`] never reports it; retained for consumers of earlier
    /// loss reports.
    GlobalAsm { blocks: usize },
    /// Historical loss for a `Switch` with `exhaustive_enum_unreachable:
    /// true` (F-072). CARRIED since WS4.5 (a trailing ` exhaustive` on the
    /// `switch`), so [`text_losses`] never reports it; retained for consumers
    /// of earlier loss reports.
    SwitchExhaustive { func: FuncId, block: BlockId },
    /// A name the text grammar cannot carry: an empty definition-site symbol
    /// or an unsupported name inside a constant or operation (see [`NameKind`]).
    UnspellableName { kind: NameKind, index: u32 },
    /// `Function.id` differs from its position: the parser numbers functions
    /// densely in text order. `index` is the position.
    FunctionId { index: u32, id: FuncId },
    /// `Function.entry` is not the first printed block (or `bb0` for a
    /// bodyless function): the parser takes the first block as the entry.
    EntryBlock { func: FuncId },
    /// Historical: `FuncAttrs.params` ended in an empty `ParamAttrs` that the
    /// printer omitted. The final `#param_attrs N:` row now records its exact
    /// length, including a default slot; no longer reported. Retained for
    /// consumers of earlier loss reports. Canonicalization still trims the
    /// default tail explicitly, but raw text transport never does.
    ParamAttrsTail { func: FuncId },
    /// A float the grammar cannot spell back bit-exactly (WS4.2 review):
    ///
    /// * a `Constant::Float` NaN whose bits are not the canonical quiet NaN
    ///   (`f64::NAN`) — the printer writes every NaN as `NaN` and the parser
    ///   rebuilds `f64::NAN`, SILENTLY changing the sign bit or payload a
    ///   later `Bitcast` / `copysign` observes (a miscompile, not a debug
    ///   nicety);
    /// * a non-finite `bounded_output(lo, hi)` bound or `gamma_crown` epsilon —
    ///   printed as `inf` / `NaN`, which those arms' number reader refuses, so
    ///   the text would not parse back at all.
    UnspellableFloat { site: FloatSite, index: u32 },
    /// A `ProofAnnotation::Goal` (feature `clean-expr`) on the function or
    /// one of its instructions. The printer writes an opaque `goal(N hyps)`
    /// summary with no parser arm; the kernel `Expr` it stands for has no
    /// text syntax. (Only reported when `clean-expr` is enabled — without it
    /// the variant does not exist.)
    KernelGoal { func: FuncId },
    /// v46 typed spec-carrier content the text cannot carry.
    ///
    /// NARROWED by WS4.4: `SpecVar.sort` (`var .. sort <sort>`),
    /// `SpecInvariant.typed` (`invariant .. typed formula ..`) and
    /// `SpecModule.temporal` (`temporal "<name>" always|eventually|leads_to|
    /// weak_fair|strong_fair ..`) are carried in the shared sort / formula
    /// spelling, so this now fires only for a sort nested deeper than
    /// [`MAX_TEXT_CLAUSE_SORT_DEPTH`]. `machine` is the position in
    /// `Module.spec_modules`. (`ProofKind::CleanTheorem` and the obligation
    /// `spec` backref were carried already.)
    SpecCarrier { machine: u32 },
}

/// The fieldless discriminant of a [`TextLoss`] — the unit the conformance
/// ratchet (`TEXT_LOSS_RATCHET`) records per fixture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum TextLossKind {
    FunctionSummary,
    ClauseBindings,
    CertificateAssurance,
    KernelRecheck,
    ObligationKind,
    EnumLayout,
    EnumFieldNames,
    EnumDiscriminantsTail,
    StructFieldNames,
    StructFieldOffsets,
    RecordFieldOffsets,
    GlobalAttrs,
    GlobalAsm,
    SwitchExhaustive,
    UnspellableName,
    FunctionId,
    EntryBlock,
    ParamAttrsTail,
    UnspellableFloat,
    KernelGoal,
    SpecCarrier,
}

impl TextLoss {
    /// The fieldless kind of this loss.
    #[must_use]
    pub fn kind(&self) -> TextLossKind {
        match self {
            TextLoss::FunctionSummary { .. } => TextLossKind::FunctionSummary,
            TextLoss::ClauseBindings { .. } => TextLossKind::ClauseBindings,
            TextLoss::CertificateAssurance { .. } => TextLossKind::CertificateAssurance,
            TextLoss::KernelRecheck { .. } => TextLossKind::KernelRecheck,
            TextLoss::ObligationKind { .. } => TextLossKind::ObligationKind,
            TextLoss::EnumLayout { .. } => TextLossKind::EnumLayout,
            TextLoss::EnumFieldNames { .. } => TextLossKind::EnumFieldNames,
            TextLoss::EnumDiscriminantsTail { .. } => TextLossKind::EnumDiscriminantsTail,
            TextLoss::StructFieldNames { .. } => TextLossKind::StructFieldNames,
            TextLoss::StructFieldOffsets { .. } => TextLossKind::StructFieldOffsets,
            TextLoss::RecordFieldOffsets { .. } => TextLossKind::RecordFieldOffsets,
            TextLoss::GlobalAttrs { .. } => TextLossKind::GlobalAttrs,
            TextLoss::GlobalAsm { .. } => TextLossKind::GlobalAsm,
            TextLoss::SwitchExhaustive { .. } => TextLossKind::SwitchExhaustive,
            TextLoss::UnspellableName { .. } => TextLossKind::UnspellableName,
            TextLoss::FunctionId { .. } => TextLossKind::FunctionId,
            TextLoss::EntryBlock { .. } => TextLossKind::EntryBlock,
            TextLoss::ParamAttrsTail { .. } => TextLossKind::ParamAttrsTail,
            TextLoss::UnspellableFloat { .. } => TextLossKind::UnspellableFloat,
            TextLoss::KernelGoal { .. } => TextLossKind::KernelGoal,
            TextLoss::SpecCarrier { .. } => TextLossKind::SpecCarrier,
        }
    }
}

/// One-token-per-loss summary used on the `; #lossy:` line. It is always a
/// single line of ASCII with no `,` (the list separator): locations are
/// indices, never names, because a name is exactly what may be unspellable.
impl fmt::Display for TextLoss {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TextLoss::FunctionSummary { func } => {
                write!(f, "function-summary(fn {})", func.index())
            }
            TextLoss::ClauseBindings { obligation } => {
                write!(f, "clause-bindings(obligation {})", obligation.index())
            }
            TextLoss::CertificateAssurance { obligation } => {
                write!(
                    f,
                    "certificate-assurance(obligation {})",
                    obligation.index()
                )
            }
            TextLoss::KernelRecheck { obligation } => {
                write!(f, "kernel-recheck(obligation {})", obligation.index())
            }
            TextLoss::ObligationKind { id, kind } => {
                // `Custom`'s payload is free text; name only the family.
                let family = match kind {
                    crate::proof::ObligationKind::Custom { .. } => "custom".to_string(),
                    other => other.to_string(),
                };
                write!(f, "obligation-kind(obligation {} {family})", id.index())
            }
            TextLoss::EnumLayout { enum_id } => write!(f, "enum-layout(enum {})", enum_id.index()),
            TextLoss::EnumFieldNames { enum_id } => {
                write!(f, "enum-field-names(enum {})", enum_id.index())
            }
            TextLoss::EnumDiscriminantsTail { enum_id } => {
                write!(f, "enum-discriminants-tail(enum {})", enum_id.index())
            }
            TextLoss::StructFieldNames { struct_id } => {
                write!(f, "struct-field-names(struct {})", struct_id.index())
            }
            TextLoss::StructFieldOffsets { struct_id } => {
                write!(f, "struct-field-offsets(struct {})", struct_id.index())
            }
            TextLoss::RecordFieldOffsets { record_id } => {
                write!(f, "record-field-offsets(record {})", record_id.index())
            }
            TextLoss::GlobalAttrs { global } => {
                write!(f, "global-attrs(global {})", global.index())
            }
            TextLoss::GlobalAsm { blocks } => write!(f, "global-asm({blocks} blocks)"),
            TextLoss::SwitchExhaustive { func, block } => write!(
                f,
                "switch-exhaustive(fn {} bb{})",
                func.index(),
                block.index()
            ),
            TextLoss::UnspellableName { kind, index } => {
                write!(f, "unspellable-name({} {index})", kind.token())
            }
            TextLoss::FunctionId { index, id } => {
                write!(f, "function-id(position {index} id {})", id.index())
            }
            TextLoss::EntryBlock { func } => write!(f, "entry-block(fn {})", func.index()),
            TextLoss::ParamAttrsTail { func } => {
                write!(f, "param-attrs-tail(fn {})", func.index())
            }
            TextLoss::UnspellableFloat { site, index } => {
                write!(f, "unspellable-float({} {index})", site.token())
            }
            TextLoss::KernelGoal { func } => write!(f, "kernel-goal(fn {})", func.index()),
            TextLoss::SpecCarrier { machine } => {
                write!(f, "spec-carrier(spec_module {machine})")
            }
        }
    }
}

/// The comma-separated summary printed after `; #lossy:`.
#[must_use]
pub fn summarize(losses: &[TextLoss]) -> String {
    let mut out = String::new();
    for (i, loss) in losses.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&loss.to_string());
    }
    out
}

/// The refusal returned by `crate::format::canonical_checked`: the module has
/// fields the text grammar cannot carry, listed in full.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextLossError {
    /// Every loss, in [`text_losses`] order. Never empty.
    pub losses: Vec<TextLoss>,
}

impl fmt::Display for TextLossError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the TrustIr text format cannot carry {} field(s) of this module ({}); \
             emit binary, JSON or MessagePack instead",
            self.losses.len(),
            summarize(&self.losses)
        )
    }
}

impl std::error::Error for TextLossError {}

/// True iff `name` is read back by the parser's bare-identifier scanner
/// (`Parser::read_ident`): the non-empty ASCII run `[A-Za-z0-9_.$]`.
#[must_use]
pub fn is_bare_ident(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$')
}

/// A dialect name the parser splits back out of `<dialect>.<op>`: the
/// validated dialect alphabet (ASCII alphanumerics and `_`), so it cannot
/// contain the separating `.`.
fn is_dialect_ident(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(crate::dialect::inst::is_valid_dialect_name_char)
}

fn position(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}

/// The value mask of a niche lane of type `ty` — every bit pattern the lane
/// can hold.
fn niche_lane_mask(ty: EnumTagRepr) -> u128 {
    match ty.size_bytes().saturating_mul(8) {
        bits if bits >= 128 => u128::MAX,
        bits => (1u128 << bits) - 1,
    }
}

/// Why the text grammar cannot carry `ed.layout`, or `None` when it can (a
/// descriptor-less enum included).
///
/// WS4.5 (enum half). The `layout(..)` clause carries every field of an
/// [`EnumLayoutDescriptor`] verbatim, so the only thing text refuses is a
/// descriptor that is INTERNALLY INCONSISTENT against its own enum: a
/// field-offset list per variant it does not have, an offset outside the
/// declared size, a tag or niche lane that does not fit, an interval naming a
/// variant that does not exist, an `Untagged` image for an enum with more than
/// one variant. Every one of those already makes
/// `Module::enum_layout_shape` fail closed (`EnumLayoutUnavailable`), so
/// nothing that a consumer can actually use is refused here.
///
/// ONE AUTHORITY FOR TWO READERS, and they must not drift:
///
/// * [`text_losses`] reports [`TextLoss::EnumLayout`] exactly when this is
///   `Some`, and `Display for Module` then omits the clause (the module prints
///   `#lossy`, which the parser refuses);
/// * `Parser::parse_enum_def` REFUSES a parsed `layout(..)` clause with this
///   message rather than defaulting or dropping a field.
///
/// If the printer emitted a clause this rejects, `convert --to text` would
/// write a file its own reader refuses — the WS4.2 hazard the `#lossy` marker
/// exists to prevent. If it refused one this accepts, a carried field would
/// silently become a loss.
#[must_use]
pub fn enum_layout_text_refusal<X>(ed: &EnumDefG<X>) -> Option<&'static str> {
    let layout = ed.layout.as_ref()?;
    // Exhaustive: a new `EnumLayoutDescriptor` field fails to compile here
    // until it is classified as carried by the clause or refused.
    let EnumLayoutDescriptor {
        encoding,
        size,
        align,
        variant_field_offsets,
    } = layout;
    if *align == 0 || !align.is_power_of_two() {
        return Some("an enum layout align must be a non-zero power of two");
    }
    if !size.is_multiple_of(*align) {
        return Some("an enum layout size must be a multiple of its align");
    }
    if variant_field_offsets.len() != ed.variants.len() {
        return Some("an enum layout must carry exactly one field-offset list per variant");
    }
    for (index, (offsets, variant)) in variant_field_offsets.iter().zip(&ed.variants).enumerate() {
        if matches!(encoding, EnumTagEncoding::SingleInhabited { variant } if usize::try_from(*variant).ok() != Some(index))
        {
            if !offsets.is_empty() {
                return Some("an inactive single-inhabited variant has no physical offset row");
            }
            continue;
        }
        if offsets.len() != variant.fields.len() {
            return Some("an enum layout variant must carry exactly one offset per field");
        }
        // `<= size`, not `< size`: a zero-sized field sits at the end of the
        // image, and rustc really does place one there (`Result<(), ()>` is
        // one byte with both payloads at offset 1).
        if offsets.iter().any(|offset| offset > size) {
            return Some("an enum layout field offset lies outside the declared size");
        }
    }
    match encoding {
        EnumTagEncoding::Direct { tag_offset } => {
            // The tag's WIDTH is not a descriptor field: it comes from the
            // enum's canonical tag repr. When the enum has none the layout is
            // uncomputable for a different reason, and the lane bound is
            // simply the image bound.
            let tag_size = ed.canonical_tag_repr().map_or(0, EnumTagRepr::size_bytes);
            if tag_offset
                .checked_add(tag_size)
                .is_none_or(|end| end > *size)
            {
                return Some("an enum layout tag lane lies outside the declared size");
            }
        }
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => {
            let variants = u32::try_from(ed.variants.len()).unwrap_or(u32::MAX);
            if *untagged_variant >= variants || *niche_variants_end >= variants {
                return Some("an enum layout niche variant index names no variant");
            }
            if niche_variants_start > niche_variants_end {
                return Some("an enum layout niche interval is empty");
            }
            let mask = niche_lane_mask(*niche_ty);
            if *niche_start > mask || u128::from(niche_variants_end - niche_variants_start) > mask {
                return Some("an enum layout niche value does not fit its lane");
            }
            if niche_offset
                .checked_add(niche_ty.size_bytes())
                .is_none_or(|end| end > *size)
            {
                return Some("an enum layout niche lane lies outside the declared size");
            }
        }
        EnumTagEncoding::Untagged => {
            if ed.variants.len() != 1 {
                return Some("an untagged enum layout requires exactly one variant");
            }
        }
        EnumTagEncoding::SingleInhabited { variant } => {
            if usize::try_from(*variant)
                .ok()
                .is_none_or(|index| index >= ed.variants.len())
            {
                return Some("a single-inhabited enum selector must name a declared variant");
            }
        }
    }
    None
}

/// Every field of `module` the text grammar cannot carry, in a deterministic
/// order (module tables in print order). Empty means `print → parse` is
/// lossless for a canonical module — see the module docs for the contract.
#[must_use]
pub fn text_losses<X: crate::level::Extension>(module: &ModuleG<X>) -> Vec<TextLoss> {
    // Exhaustive: a new `Module` field fails to compile until classified.
    let ModuleG {
        name: _,                   // carried: `module "<quoted>"`
        functions,                 // walked below
        structs,                   // walked below
        enums,                     // walked below
        records,                   // walked below
        closure_types: _,          // carried: `closure_ty functy.N { .. }`
        globals,                   // walked below
        func_types: _,             // carried: `functy.N = (..) -> (..)`
        types: _,                  // carried: `type ty.N = ..`
        proof_obligations,         // walked below
        proof_certificates,        // walked below
        target_info: _,            // carried: `target ".." N endian [abi=..] [structpass=..]`
        files: _,                  // carried: `file N "<quoted>"`
        obligation_diagnostics: _, // carried: `diagnostic ..`
        spec_modules,              // walked below
        universes: _,              // carried: `univ univ.N = ..`
        predicates: _,             // carried: `pred pred.N = ..`
        global_asm: _,             // carried since WS4.5: `global_asm "<escaped>"` per block
        imports: _,                // carried: `import import.N = ..`
        tuple_layouts: _,          // carried: `tuple_layout ty.N ..`
        completeness: _,           // carried: `completeness ..` + `unlowered ..` rows
        drop_glue: _,              // carried: `drop_glue @func.N <ty>` rows
        closure_layouts: _,        // carried: `closure_layout closure.N ..` (v58)
        blobs: _,                  // carried: `blob <digest> bytes<..>` rows (v70)
    } = module;

    let mut losses = Vec::new();

    for (index, sd) in structs.iter().enumerate() {
        struct_losses(index, sd, &mut losses);
    }
    for (index, ed) in enums.iter().enumerate() {
        enum_losses(index, ed, &mut losses);
    }
    for (index, rd) in records.iter().enumerate() {
        record_losses(index, rd, &mut losses);
    }
    for (index, global) in globals.iter().enumerate() {
        global_losses(index, global, &mut losses);
    }
    for (index, func) in functions.iter().enumerate() {
        function_losses(index, func, &mut losses);
    }
    for obligation in proof_obligations {
        obligation_losses(obligation, &mut losses);
    }
    for (index, machine) in spec_modules.iter().enumerate() {
        spec_module_losses(index, machine, &mut losses);
    }
    for (index, certificate) in proof_certificates.iter().enumerate() {
        certificate_losses(index, certificate, &mut losses);
    }
    losses
}

fn struct_losses<X>(index: usize, sd: &StructDefG<X>, losses: &mut Vec<TextLoss>) {
    let StructDefG {
        id,
        name, // carried when nonempty: printed bare or as `@"escaped"`
        fields,
        size: _,   // carried: `size=N`
        align: _,  // carried: `align=N`
        repr: _,   // carried: `repr=..`
        origin: _, // carried: `origin=rust(..)` / `origin=clean(..)` (v58)
    } = sd;
    if name.is_empty() {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::Struct,
            index: position(index),
        });
    }
    // WS4.5 (struct half): a field's NAME and OFFSET are both CARRIED — the
    // printer emits `name: ty @off` and `parse_struct_field` reads it back. The
    // bare type list stays readable as the legacy spelling (name "", offset
    // None) but is never printed, so printer output keeps one spelling per
    // construct.
    let _ = (id, fields, losses);
}

fn enum_losses<X>(index: usize, ed: &EnumDefG<X>, losses: &mut Vec<TextLoss>) {
    let EnumDefG {
        id,
        name, // carried when nonempty: printed bare or as `@"escaped"`
        variants,
        discriminants, // carried in trimmed form (`Name = N`)
        repr: _,       // carried: `repr(u8)`
        layout: _,     // carried since WS4.5: `layout(..)` — checked below
        origin: _,     // carried: `origin=rust(..)` / `origin=clean(..)` (v58)
    } = ed;
    if name.is_empty() {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::Enum,
            index: position(index),
        });
    }
    let (mut empty_variant_name, mut field_names_unspellable) = (false, false);
    for variant in variants {
        let EnumVariantG {
            name,        // carried when nonempty: bare, or `"escaped"`
            fields,      // carried: `Name(ty, ..)` / `Name(field: ty, ..)`
            field_names, // carried since WS4.5 when parallel to `fields`
        } = variant;
        empty_variant_name |= name.is_empty();
        field_names_unspellable |= !field_names.is_empty() && field_names.len() != fields.len();
    }
    // Variant names are CARRIED since WS4.3 (bare, or `"escaped"`) when
    // nonempty; the parser's `read_symbol` refuses the empty quoted name.
    if empty_variant_name {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::EnumVariant,
            index: position(index),
        });
    }
    if *discriminants != discriminants_text_reconstruction(variants.len(), discriminants) {
        losses.push(TextLoss::EnumDiscriminantsTail { enum_id: *id });
    }
    // WS4.5 (enum half): the descriptor is CARRIED by the `layout(..)` clause
    // unless it is internally inconsistent against this enum, which is the
    // narrowed residual — see `enum_layout_text_refusal`, the one authority
    // the printer and the parser both read.
    if enum_layout_text_refusal(ed).is_some() {
        losses.push(TextLoss::EnumLayout { enum_id: *id });
    }
    if field_names_unspellable {
        losses.push(TextLoss::EnumFieldNames { enum_id: *id });
    }
}

/// Does the `Name(field: ty, ..)` spelling carry `variant.field_names`?
///
/// WS4.5. True exactly when the list is non-empty AND parallel to `fields`
/// (the only shape `validate_module` admits): the printer then spells every
/// field `name: ty` (an empty name as `: ty`) and the parser rebuilds the list
/// verbatim. An empty list is the positional spelling (`Name(ty, ..)`); a
/// non-parallel list is unspellable and reported as
/// [`TextLoss::EnumFieldNames`]. The printer and [`text_losses`] both read
/// this one predicate, so they cannot disagree about what is carried.
#[must_use]
pub fn enum_variant_field_names_spellable<X>(variant: &EnumVariantG<X>) -> bool {
    !variant.field_names.is_empty() && variant.field_names.len() == variant.fields.len()
}

/// The exact `EnumDef.discriminants` vector a `bin -> text -> bin` round trip
/// reconstructs, so the loss check can compare against it instead of testing
/// one symptom of disagreeing with it.
///
/// Two rules, one from each side, and the vector survives only when it is a
/// fixpoint of both:
///
/// * the PRINTER (`display.rs`) reads `discriminants[i]` for each VARIANT
///   index `i` and emits `= N` only for a `Some`, so every entry from
///   `variants.len()` onward is unreachable — it is never printed and nothing
///   reported it;
/// * the PARSER (`parser.rs`) rebuilds the vector only up to the LAST variant
///   carrying an explicit `= N` (`resize(variants.len(), None)` then push), so
///   trailing `None`s do not come back either, and an all-implicit enum parses
///   to an EMPTY vector rather than a run of `None`s.
///
/// The previous check tested `discriminants.last() == Some(None)`, which is
/// the second rule's symptom only. It was blind to the first: an over-long
/// vector ending in `Some` — `variants: [A, B]` with
/// `discriminants: [Some(0), Some(1), Some(99)]` — reported NO loss while the
/// round trip dropped `Some(99)`, the false-clean direction this module exists
/// to close (measured 2026-09-21: `losses_empty=true`,
/// `round_trip_equal=false`).
fn discriminants_text_reconstruction(
    variant_count: usize,
    discriminants: &[Option<i128>],
) -> Vec<Option<i128>> {
    let printed: Vec<Option<i128>> = (0..variant_count)
        .map(|i| discriminants.get(i).copied().flatten())
        .collect();
    match printed.iter().rposition(Option::is_some) {
        Some(last) => printed[..=last].to_vec(),
        None => Vec::new(),
    }
}

fn record_losses(index: usize, rd: &RecordDef, losses: &mut Vec<TextLoss>) {
    let RecordDef { id, name, fields } = rd; // name carried when nonempty: bare or `@"escaped"`
    // `name` is CARRIED since 2026-09-21: the printer emits `@"escaped"` for any
    // name outside the bare alphabet and `Parser::read_name` decodes it, so an
    // entity name is no longer a text loss — except the EMPTY name, which the
    // printer spells `""` and `read_symbol` refuses. Entity names print by
    // name; call and global-address SITES print by index (`call @func.N`,
    // `global_addr @global.N`), so there is no second spelling to keep in step.
    if name.is_empty() {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::Record,
            index: position(index),
        });
    }
    let (mut empty_field_name, mut offset) = (false, false);
    for field in fields {
        let FieldDef {
            name,  // carried when nonempty: `name: ty`, bare or `"escaped"`
            ty: _, // carried
            offset: field_offset,
        } = field;
        empty_field_name |= name.is_empty();
        offset |= field_offset.is_some();
    }
    if empty_field_name {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::RecordField,
            index: position(index),
        });
    }
    if offset {
        losses.push(TextLoss::RecordFieldOffsets { record_id: *id });
    }
}

fn global_losses<X: crate::level::Extension>(
    index: usize,
    global: &GlobalG<X>,
    losses: &mut Vec<TextLoss>,
) {
    let GlobalG {
        name,          // carried when nonempty: bare, or `@"escaped"`
        ty: _,         // carried
        mutable: _,    // carried: `mut`
        initializer,   // carried: `= <constant>` (names inside checked below)
        linkage: _,    // carried
        tls: _,        // carried: `tls(..)`
        align: _,      // carried: `align(N)`
        section: _,    // carried: `section("...")`
        visibility: _, // carried: `visibility(..)`
        retained: _,   // carried: `retained`
    } = global;
    if name.is_empty() {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::Global,
            index: position(index),
        });
    }
    if initializer
        .as_ref()
        .is_some_and(|c| !constant_is_spellable(c))
    {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::GlobalConstant,
            index: position(index),
        });
    }
    if initializer
        .as_ref()
        .is_some_and(constant_has_unspellable_float)
    {
        losses.push(TextLoss::UnspellableFloat {
            site: FloatSite::GlobalConstant,
            index: position(index),
        });
    }
}

/// True iff every name the printer writes bare inside `constant` is a bare
/// identifier (`record{ name = .. }` field names and `symaddr<name>`).
fn constant_is_spellable<X: crate::level::Extension>(constant: &ConstantG<X>) -> bool {
    match constant {
        ConstantG::Record(fields) => fields
            .iter()
            .all(|(name, value)| is_bare_ident(name) && constant_is_spellable(value)),
        ConstantG::SymbolAddr { symbol, .. } => is_bare_ident(symbol),
        ConstantG::Aggregate(elems)
        | ConstantG::Array(elems)
        | ConstantG::Vector(elems)
        | ConstantG::Sequence(elems)
        | ConstantG::Set(elems) => elems.iter().all(constant_is_spellable),
        ConstantG::Closure { captures, .. } => captures.iter().all(constant_is_spellable),
        ConstantG::Splat { elem, .. } => constant_is_spellable(elem),
        ConstantG::Int(_)
        | ConstantG::U128(_)
        | ConstantG::Bytes { .. }
        | ConstantG::Float(_)
        | ConstantG::Bool(_)
        | ConstantG::FnDef(_)
        | ConstantG::PhantomData
        // Crystal lane (E3b): `uninit` is a bare keyword the parser reads back.
        | ConstantG::Uninit
        // v70: `tensor_blob<hex>[dims]` spells no name.
        | ConstantG::TensorBlob { .. } => true,
        ConstantG::Ext(_) => true,
    }
}

/// True iff `v` is a NaN the parser's `NaN` token cannot rebuild: it reads
/// every `NaN` back as `f64::NAN`, so any other sign bit or payload is lost.
fn is_unspellable_nan(v: f64) -> bool {
    v.is_nan() && v.to_bits() != f64::NAN.to_bits()
}

/// True iff `constant` (recursively) holds a float [`is_unspellable_nan`].
fn constant_has_unspellable_float<X: crate::level::Extension>(constant: &ConstantG<X>) -> bool {
    match constant {
        ConstantG::Float(v) => is_unspellable_nan(*v),
        ConstantG::Record(fields) => fields
            .iter()
            .any(|(_, value)| constant_has_unspellable_float(value)),
        ConstantG::Aggregate(elems)
        | ConstantG::Array(elems)
        | ConstantG::Vector(elems)
        | ConstantG::Sequence(elems)
        | ConstantG::Set(elems) => elems.iter().any(constant_has_unspellable_float),
        ConstantG::Closure { captures, .. } => captures.iter().any(constant_has_unspellable_float),
        ConstantG::Splat { elem, .. } => constant_has_unspellable_float(elem),
        ConstantG::Int(_)
        | ConstantG::U128(_)
        | ConstantG::Bytes { .. }
        | ConstantG::Bool(_)
        | ConstantG::FnDef(_)
        | ConstantG::SymbolAddr { .. }
        | ConstantG::PhantomData
        | ConstantG::Uninit
        | ConstantG::TensorBlob { .. } => false,
        ConstantG::Ext(_) => false,
    }
}

/// `(unspellable float, kernel goal)` for one proof annotation. The
/// `bounded_output` arm reads its bounds with a finite-only number reader,
/// so `inf` / `NaN` there cannot be parsed back.
fn annotation_losses(annotation: &ProofAnnotation) -> (bool, bool) {
    match annotation {
        ProofAnnotation::BoundedOutput { lo, hi } => (!lo.is_finite() || !hi.is_finite(), false),
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(_) => (false, true),
        _ => (false, false),
    }
}

fn function_losses<X: crate::level::Extension>(
    index: usize,
    func: &FunctionG<X>,
    losses: &mut Vec<TextLoss>,
) {
    let FunctionG {
        id,
        name,  // carried when nonempty: printed bare or as `@"escaped"`
        ty: _, // carried: `(functy.N)`
        entry,
        blocks,
        proofs,               // carried: `; #proof:` (floats / goals checked below)
        calling_conv: _,      // carried: cc prefix
        linkage: _,           // carried: linkage prefix
        attrs: _,             // carried: `; #attrs:` / `#target_features` / `#param_attrs`
        summary,              // carried since WS4.4: `; #summary:` block (sorts checked below)
        producer: _,          // carried: `; #producer:`
        value_names: _,       // carried: `; #names:`
        scopes: _,            // carried: `; #scope:`
        source_provenance: _, // carried: `; #source-provenance:` / `-loop` / `-binding`
        body_gate: _,         // carried: `; #body-gate:`
        display_path: _,      // carried: `; #display-path:`
        section: _,           // carried: `; #section:` (v45, WS3.10)
        visibility: _,        // carried: `; #visibility:` (v45)
        retained: _,          // carried: `; #retained:` (v45)
    } = func;
    if *id != FuncId::new(position(index)) {
        losses.push(TextLoss::FunctionId {
            index: position(index),
            id: *id,
        });
    }
    if name.is_empty() {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::Function,
            index: position(index),
        });
    }
    let parsed_entry = blocks.first().map_or(BlockId::new(0), |b| b.id);
    if *entry != parsed_entry {
        losses.push(TextLoss::EntryBlock { func: *id });
    }
    // WS4.4: the summary is carried; only a clause sort the parser's depth
    // cap refuses is still a loss — and (v59) an effect set the parser
    // refuses as non-canonical.
    if summary.as_ref().is_some_and(|summary| {
        summary
            .requires
            .iter()
            .chain(&summary.ensures)
            .chain(&summary.decreases)
            .any(formula_has_unspellable_sort)
            || summary.effects.as_ref().is_some_and(|effects| {
                !effects.reads.is_canonical() || !effects.writes.is_canonical()
            })
    }) {
        losses.push(TextLoss::FunctionSummary { func: *id });
    }
    let mut unspellable_body = false;
    let (mut unspellable_float, mut kernel_goal) = (false, false);
    for annotation in proofs.iter().chain(
        blocks
            .iter()
            .flat_map(|b| b.body.iter().flat_map(|n| &n.proofs)),
    ) {
        let (float, goal) = annotation_losses(annotation);
        unspellable_float |= float;
        kernel_goal |= goal;
    }
    for block in blocks {
        for node in &block.body {
            match &node.inst {
                // `Switch.exhaustive_enum_unreachable` is CARRIED since
                // WS4.5: a trailing ` exhaustive` on the `switch` line.
                InstG::Const { value, .. } => {
                    unspellable_body |= !constant_is_spellable(value);
                    unspellable_float |= constant_has_unspellable_float(value);
                }
                InstG::DialectOp(op) => {
                    unspellable_body |= !is_dialect_ident(&op.dialect)
                        || !is_bare_ident(&op.op)
                        || op.attrs.iter().any(|entry| !is_bare_ident(&entry.name));
                }
                _ => {}
            }
        }
    }
    if unspellable_body {
        losses.push(TextLoss::UnspellableName {
            kind: NameKind::FunctionBody,
            index: position(index),
        });
    }
    if unspellable_float {
        losses.push(TextLoss::UnspellableFloat {
            site: FloatSite::FunctionBody,
            index: position(index),
        });
    }
    if kernel_goal {
        losses.push(TextLoss::KernelGoal { func: *id });
    }
}

fn obligation_losses(obligation: &ProofObligation, losses: &mut Vec<TextLoss>) {
    let ProofObligation {
        id,
        kind: _,        // carried since WS4.4: every kind; `custom("<ns>", "<name>")`
        status: _,      // carried
        description: _, // carried (quoted)
        formula,
        function: _, // carried: `function N`
        source: _,   // carried: `source .. assertion ..`
        site: _,     // carried: `site fF/bbB#I`
        spec: _,     // carried: `spec "<machine>" "<temporal>"` (v46)
    } = obligation;
    if let Some(formula) = formula {
        let ProofFormula {
            schema: _,   // carried (quoted)
            payload: _,  // carried (quoted)
            smtlib: _,   // carried: `smtlib ".."`
            sort: _,     // carried: `sort ".."`
            bindings: _, // carried since WS4.4: `bind "<name>" <sort> <place>` (depth checked)
        } = formula;
        if formula_has_unspellable_sort(formula) {
            losses.push(TextLoss::ClauseBindings { obligation: *id });
        }
    }
}

/// v46: the typed spec carrier. `SpecVar.sort`, `SpecInvariant.typed` and
/// `SpecModule.temporal` are carried since WS4.4 in the shared sort / formula
/// spelling; the one residue is a sort deeper than the parser's cap, reported
/// once per machine.
fn spec_module_losses(index: usize, machine: &SpecModule, losses: &mut Vec<TextLoss>) {
    use crate::spec::TemporalForm;
    let SpecModule {
        name: _,        // carried (quoted)
        vars,           // walked below: `var ".." : ".." [sort <sort>]`
        actions: _,     // carried: `action ".."`
        invariants,     // walked below: `invariant ".." : ".." [typed formula ..]`
        anchors: _,     // carried: `anchor machine .. action .. ..`
        waivers: _,     // carried: `waiver machine .. action .. reason ..`
        proofs: _,      // carried: `proof machine .. kind ".." [theorem ".."]`
        origin: _,      // carried: `origin embedded | external ".."`
        enforcement: _, // carried: `enforcement design-only | linked`
        temporal,       // carried since WS4.4: `temporal ".." <form>` (sorts checked below)
    } = machine;
    let mut lost = false;
    for variable in vars {
        let SpecVar {
            name: _, // carried (quoted)
            ty: _,   // carried (quoted)
            sort,    // carried since WS4.4: `sort <sort>`
        } = variable;
        lost |= sort
            .as_ref()
            .is_some_and(|sort| clause_sort_depth(sort) > MAX_TEXT_CLAUSE_SORT_DEPTH);
    }
    for invariant in invariants {
        let SpecInvariant {
            name: _,    // carried (quoted)
            formula: _, // carried (quoted)
            typed,      // carried since WS4.4: `typed formula ..`
        } = invariant;
        lost |= typed.as_ref().is_some_and(formula_has_unspellable_sort);
    }
    for property in temporal {
        let leaves: Vec<&ProofFormula> = match &property.form {
            TemporalForm::Always(leaf) | TemporalForm::Eventually(leaf) => vec![leaf],
            TemporalForm::LeadsTo(from, to) => vec![from, to],
            TemporalForm::WeakFair { relation, .. } | TemporalForm::StrongFair { relation, .. } => {
                relation.iter().collect()
            }
        };
        lost |= leaves.into_iter().any(formula_has_unspellable_sort);
    }
    if lost {
        losses.push(TextLoss::SpecCarrier {
            machine: position(index),
        });
    }
}

fn certificate_losses(index: usize, certificate: &ProofCertificate, losses: &mut Vec<TextLoss>) {
    let ProofCertificate {
        obligation: _, // carried
        prover: _,     // carried (quoted)
        evidence,      // carried; `clean_cic .. recheck ..` since WS4.4 (F-070)
        assurance: _,  // carried since WS4.4: `assurance <bound> digest ..` (F-064)
    } = certificate;
    // `gamma_crown <epsilon>` is read back with the finite-only number
    // reader: a non-finite epsilon would print an unparseable text.
    if let ProofEvidence::GammaCrownBound { epsilon, .. } = evidence
        && !epsilon.is_finite()
    {
        losses.push(TextLoss::UnspellableFloat {
            site: FloatSite::Certificate,
            index: position(index),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::FuncTy;
    use crate::{Function, Module};

    #[test]
    fn empty_module_is_lossless() {
        assert!(text_losses(&Module::new("m")).is_empty());
    }

    #[test]
    fn global_asm_is_carried_not_a_loss() {
        // WS4.5: `global_asm "<escaped>"` carries the block.
        let mut m = Module::new("m");
        m.global_asm.push(".globl _x\n_x: ret".into());
        assert!(text_losses(&m).is_empty());
    }

    #[test]
    fn historical_loss_summarizes_on_one_line() {
        let losses = vec![TextLoss::GlobalAsm { blocks: 1 }];
        assert_eq!(summarize(&losses), "global-asm(1 blocks)");
        assert_eq!(losses[0].kind(), TextLossKind::GlobalAsm);
    }

    #[test]
    fn bare_ident_alphabet_matches_the_parser() {
        for ok in ["a", "_ZN3foo3barE", "opendir$INODE64", "List.map", "0"] {
            assert!(is_bare_ident(ok), "{ok}");
        }
        for bad in ["", "Vec<u8>", "a::b", "café", "a b", "x,y"] {
            assert!(!is_bare_ident(bad), "{bad}");
        }
    }

    #[test]
    fn sparse_function_id_and_foreign_entry_are_losses() {
        let mut m = Module::new("m");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        m.functions
            .push(Function::new(FuncId::new(7), "f", ft, BlockId::new(3)));
        assert_eq!(
            text_losses(&m),
            vec![
                TextLoss::FunctionId {
                    index: 0,
                    id: FuncId::new(7)
                },
                TextLoss::EntryBlock {
                    func: FuncId::new(7)
                },
            ]
        );
    }
}

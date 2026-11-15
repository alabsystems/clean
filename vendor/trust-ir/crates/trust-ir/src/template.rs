// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Level S: generic templates (amendment S, `docs/SPEC_RATIFICATIONS.md` §22).
//!
//! A [`Template`] is one generic definition: a header (its parameters and its
//! HOLES — the facts only the host can answer, each with a host key, its
//! arguments and a contract) and a [`ModuleG<TemplateRef>`] whose first
//! function row is the one body and whose other rows are declarations.
//!
//! A template is never a module. Every level-R entry point (`validate_module`,
//! the interpreter, `serialize_module`, every backend) takes `&Module`, which
//! is `ModuleG<NoExt>`; a template's module is `ModuleG<TemplateRef>`, so
//! passing it is a type error:
//!
//! ```compile_fail
//! fn level_r_only(_: &trust_ir::Module) {}
//! fn give(template: &trust_ir::template::Template) {
//!     level_r_only(&template.module);
//! }
//! ```
//!
//! A consumer turns a template into a level-R module with
//! `trust_ir_build::template::instantiate`, which asks a host to answer the
//! holes, checks every answer, and returns only an output `validate_module`
//! accepts. This module holds the carrier, its identity and its STRUCTURAL
//! rules (T1–T5, T7–T9 of the amendment); T6, the level-R rules at level S, is
//! `trust_ir_build::template::validate_template`'s, because it runs the
//! level-R validator over the template's skolem instance.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::constant::ConstantG;
use crate::inst::InstG;
use crate::level::TemplateRef;
use crate::ty::{EnumTagRepr, Ty, TyG};
use crate::value::{FuncId, FuncTyId, GlobalId, HoleId, ParamId, TyId};
use crate::{FunctionG, ModuleG};

/// The reserved name of a template's body row (`functions[0]`): it is not a
/// link symbol; the host names the instance (§5 step 6).
pub const TEMPLATE_BODY_NAME: &str = "!template_body";

/// The reserved-name prefix of a hole's declaration or global row:
/// `!template_hole::<n>`, `n` the hole's id. Not a link symbol: the host's
/// answer names the row at instantiation.
pub const TEMPLATE_HOLE_ROW_PREFIX: &str = "!template_hole::";

/// The digest domain of a template's identity (amendment S, S12).
pub const TEMPLATE_DIGEST_DOMAIN: &str = "trust_ir.template.v1";

/// The digest domain of an instance's identity: (template digest, output
/// module `stable_digest`) (amendment S, S12, review R5).
pub const TEMPLATE_INSTANCE_DIGEST_DOMAIN: &str = "trust_ir.template.instance.v1";

/// The reserved name of hole `hole`'s row.
#[must_use]
pub fn hole_row_name(hole: HoleId) -> String {
    format!("{TEMPLATE_HOLE_ROW_PREFIX}{}", hole.index())
}

/// One generic definition at level S.
///
/// A template's module is a `ModuleG<TemplateRef>`, a different type from the
/// level-R `Module`, so no level-R entry point (validator, interpreter,
/// codec, digest) can be handed one: only `instantiate`'s output reaches
/// them. The consumer twin of amendment S, §8:
///
/// ```compile_fail
/// fn level_r_consumer(_: &trust_ir::Module) {}
/// fn handed_a_template(template: &trust_ir::template::Template) {
///     level_r_consumer(&template.module);
/// }
/// ```
///
/// while the level-S carrier it does have type-checks:
///
/// ```
/// fn level_s_consumer(_: &trust_ir::ModuleG<trust_ir::TemplateRef>) {}
/// fn handed_a_template(template: &trust_ir::template::Template) {
///     level_s_consumer(&template.module);
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Template {
    pub header: TemplateHeader,
    /// `functions[0]` is the body, named [`TEMPLATE_BODY_NAME`]; every other
    /// row is a declaration. Non-generic tables are ground (T5).
    pub module: ModuleG<TemplateRef>,
}

/// A template's parameters and holes.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TemplateHeader {
    /// The host's stable name for the generic definition (diagnostic, and
    /// part of the template digest). Nonempty, no line break (T9).
    pub identity: String,
    pub params: Vec<TemplateParam>,
    /// Unique by (kind, key, args) (T2).
    pub holes: Vec<HoleDef>,
}

/// A template parameter.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TemplateParam {
    /// A type with a level-R spelling; may appear in any type position.
    Type,
    /// A const parameter of a scalar type (an integer, a float, `Bool` or
    /// `Char`, T8).
    Const { ty: Ty },
    /// A parameter with no level-R value spelling (Rust `T: ?Sized`): its
    /// argument is the host's own key, and it appears only as a hole
    /// argument ([`TemplateArg::Host`]), never in a body position (T1).
    Host,
}

/// A hole: a fact the host answers at instantiation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HoleDef {
    pub kind: HoleKind,
    pub key: HostKey,
    /// The format's record of what the hole depends on: parameters and LOWER
    /// holes only (T2). A Rust host answers from the key in its own
    /// instantiation context; the arguments are passed for hosts that can use
    /// them (review R10).
    pub args: Vec<TemplateArg>,
}

/// The host's key for a hole. trust-ir compares it and nothing else.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct HostKey {
    /// Which host's key space, e.g. `rust`. Nonempty `[A-Za-z0-9_.]`.
    pub namespace: String,
    pub bytes: Vec<u8>,
}

impl HostKey {
    /// A key in `namespace` with `bytes`.
    pub fn new(namespace: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            namespace: namespace.into(),
            bytes: bytes.into(),
        }
    }

    /// Whether the namespace is lexically valid (T2).
    #[must_use]
    pub fn namespace_is_valid(&self) -> bool {
        !self.namespace.is_empty()
            && self
                .namespace
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
    }
}

/// One argument of a hole.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TemplateArg {
    Type(TyG<TemplateRef>),
    /// A const argument of the scalar type `ty`: a literal, or a const
    /// parameter or lower const hole of that type.
    Const {
        value: ConstantG<TemplateRef>,
        ty: Ty,
    },
    /// A [`TemplateParam::Host`] parameter.
    Host(ParamId),
}

/// What a hole is, and what its answer must satisfy.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum HoleKind {
    /// Answer: one level-R type, in the instance's ids, satisfying `contract`.
    Type { contract: TypeContract },
    /// Answer: one level-R constant of the scalar type `ty`.
    Const { ty: Ty },
    /// Answer: a link symbol, convention, attributes and linkage for the
    /// declaration row `decl` (named `!template_hole::<n>`), whose signature
    /// after substitution is the callee's.
    Callee { decl: FuncId },
    /// Answer: a symbol and linkage for the global row `decl` (named
    /// `!template_hole::<n>`), declared, or defined with a ground initializer.
    Global { decl: GlobalId },
}

impl HoleKind {
    /// The wire / text word of the kind.
    #[must_use]
    pub fn word(&self) -> &'static str {
        match self {
            HoleKind::Type { .. } => "type",
            HoleKind::Const { .. } => "const",
            HoleKind::Callee { .. } => "callee",
            HoleKind::Global { .. } => "global",
        }
    }
}

/// What a type hole's answer must be.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeContract {
    /// Nothing is known: only transport operations apply (T4).
    Opaque,
    /// The answer is `Ty::Struct(s)` whose fields' types, in order, equal
    /// `fields[σ]`.
    Struct { fields: Vec<TyG<TemplateRef>> },
    /// The answer is `Ty::Enum(e)` whose variants' field types equal
    /// `variants[σ]` in order, and whose declared `discriminants` and `repr`
    /// equal these (the body's switch reads them; review R3).
    Enum {
        variants: Vec<Vec<TyG<TemplateRef>>>,
        discriminants: Vec<Option<i128>>,
        repr: Option<EnumTagRepr>,
    },
}

/// A refusal of a template by its decoder or one of its structural rules.
/// Each variant is a rule of the amendment (§4) and has a must-refuse row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemplateError {
    /// The bytes are not a template blob (the magic is not `TRUST_IS`).
    NotATemplate,
    /// The template blob does not decode (`deserialize_template`).
    Binary(String),
    /// T9: the identity is empty or carries a line break.
    InvalidIdentity,
    /// T1: a reference to a parameter that does not exist.
    ParamOutOfScope { param: u32, at: String },
    /// T1: a parameter used where its kind is not admitted.
    ParamKindMismatch { param: u32, at: String },
    /// T1: a reference to a hole that does not exist.
    HoleOutOfScope { hole: u32, at: String },
    /// T1: a hole used where its kind is not admitted.
    HoleKindMismatch { hole: u32, at: String },
    /// T2: two holes with one (kind, key, args).
    DuplicateHole { hole: u32, first: u32 },
    /// T2: a hole that depends on no parameter (it has a ground spelling).
    GroundHole { hole: u32 },
    /// T2: a host key namespace outside `[A-Za-z0-9_.]+`.
    InvalidHostKey { hole: u32 },
    /// T2: a hole whose arguments name a hole that is not lower.
    HoleCycle { hole: u32, names: u32 },
    /// T2: a callee or global hole and its reserved-name row disagree.
    HoleRowMismatch { why: String },
    /// T2: a type or const hole nothing references.
    UnusedHole { hole: u32 },
    /// T2: a declaration or global whose type mentions a parameter or hole
    /// but which is not a hole row (one symbol has one signature).
    GenericRowNotAHole { row: String },
    /// T3: a layout literal that would depend on a parameter.
    ParamDependentLiteral { at: String },
    /// T4: an operation that inspects an opaque value.
    OpaqueOperation { at: String },
    /// T5: a parameter or hole in a ground table.
    ExtInGroundTable { table: &'static str, index: u32 },
    /// T7: the body is not one definition named `!template_body` beside
    /// declarations, or a row carries a fact the host answers.
    TemplateBodyShape { why: String },
    /// T7/T8: a construct level S does not carry (proof surface, coroutines,
    /// dialect ops, binding frames, sequence ops, a non-scalar const).
    TemplateUnsupported { what: String },
}

impl core::fmt::Display for TemplateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TemplateError::NotATemplate => {
                f.write_str("not a template blob (magic is not TRUST_IS)")
            }
            TemplateError::Binary(why) => write!(f, "template blob does not decode: {why}"),
            TemplateError::InvalidIdentity => {
                f.write_str("T9: the template identity is empty or carries a line break")
            }
            TemplateError::ParamOutOfScope { param, at } => {
                write!(f, "T1: parameter ${param} does not exist ({at})")
            }
            TemplateError::ParamKindMismatch { param, at } => {
                write!(f, "T1: parameter ${param} is not admitted here ({at})")
            }
            TemplateError::HoleOutOfScope { hole, at } => {
                write!(f, "T1: hole ?{hole} does not exist ({at})")
            }
            TemplateError::HoleKindMismatch { hole, at } => {
                write!(f, "T1: hole ?{hole} is not admitted here ({at})")
            }
            TemplateError::DuplicateHole { hole, first } => {
                write!(
                    f,
                    "T2: hole ?{hole} repeats ?{first} (one hole per kind, key and arguments)"
                )
            }
            TemplateError::GroundHole { hole } => write!(
                f,
                "T2: hole ?{hole} depends on no parameter; a ground construct has a level-R spelling"
            ),
            TemplateError::InvalidHostKey { hole } => {
                write!(f, "T2: hole ?{hole}'s key namespace is not [A-Za-z0-9_.]+")
            }
            TemplateError::HoleCycle { hole, names } => write!(
                f,
                "T2: hole ?{hole}'s arguments name ?{names}, which is not a lower hole"
            ),
            TemplateError::HoleRowMismatch { why } => write!(f, "T2: {why}"),
            TemplateError::UnusedHole { hole } => write!(f, "T2: hole ?{hole} is never used"),
            TemplateError::GenericRowNotAHole { row } => write!(
                f,
                "T2: {row} has a parameter-dependent type but is not a hole row"
            ),
            TemplateError::ParamDependentLiteral { at } => {
                write!(
                    f,
                    "T3: a layout literal at a parameter-dependent type ({at})"
                )
            }
            TemplateError::OpaqueOperation { at } => {
                write!(
                    f,
                    "T4: an opaque value is inspected, not transported ({at})"
                )
            }
            TemplateError::ExtInGroundTable { table, index } => write!(
                f,
                "T5: row {index} of the ground {table} table names a parameter-dependent type"
            ),
            TemplateError::TemplateBodyShape { why } => write!(f, "T7: {why}"),
            TemplateError::TemplateUnsupported { what } => {
                write!(f, "level S does not carry {what}")
            }
        }
    }
}

impl std::error::Error for TemplateError {}

/// Whether `ty` is a scalar a const parameter or const hole may have (T8).
#[must_use]
pub fn is_template_scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Char
    )
}

impl Template {
    /// The template body, `module.functions[0]`, if there is one.
    #[must_use]
    pub fn body(&self) -> Option<&FunctionG<TemplateRef>> {
        self.module.functions.first()
    }

    /// The hole `hole`, if it exists.
    #[must_use]
    pub fn hole(&self, hole: HoleId) -> Option<&HoleDef> {
        self.header.holes.get(hole.as_usize())
    }

    /// Every violation of the structural rules (T1–T5, T7–T9), in a fixed
    /// order. T6 is `trust_ir_build::template::validate_template`'s.
    #[must_use]
    pub fn structural_violations(&self) -> Vec<TemplateError> {
        let mut violations = Checker::new(self).run();
        let rows = GenericRows::of(&self.module);
        for (index, signature) in self.module.func_types.iter().enumerate() {
            if let Some(abi) = &signature.abi
                && let Err(detail) = abi.validate_encoding_limits()
            {
                violations.push(TemplateError::TemplateUnsupported {
                    what: format!("signature {index} ABI encoding: {detail}"),
                });
            }
            if rows.func_types[index] && signature.abi.is_some() {
                violations.push(TemplateError::TemplateUnsupported {
                    what: format!(
                        "typed ABI placement on polymorphic signature {index} requires an explicit instantiation binding"
                    ),
                });
            }
        }
        violations
    }

    /// The template's identity: SHA-256 under `trust_ir.template.v1` of its
    /// canonical `TRUST_IS` encoding (amendment S, S12). A template failing a
    /// structural rule has no wire identity and is refused with that rule.
    pub fn digest(&self) -> Result<crate::proof::ProofDigest, TemplateError> {
        crate::binary::template_digest(self)
    }

    /// The first structural violation, if any.
    pub fn check_structure(&self) -> Result<(), TemplateError> {
        match self.structural_violations().into_iter().next() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

// ---------------------------------------------------------------------------
// The structural rules
// ---------------------------------------------------------------------------

/// Which rows of a template's `types` / `func_types` tables mention a
/// parameter or hole, directly or through other rows (cycles terminate: a row
/// on the current path contributes nothing more).
pub struct GenericRows {
    pub types: Vec<bool>,
    pub func_types: Vec<bool>,
}

impl GenericRows {
    /// Compute which rows of `module` are generic.
    #[must_use]
    pub fn of(module: &ModuleG<TemplateRef>) -> Self {
        let mut rows = GenericRows {
            types: vec![false; module.types.len()],
            func_types: vec![false; module.func_types.len()],
        };
        let mut refs = RefCollector::new(module);
        for (index, generic) in rows.types.iter_mut().enumerate() {
            let mut out = BTreeSet::new();
            refs.ty_row(
                TyId::new(u32::try_from(index).unwrap_or(u32::MAX)),
                &mut out,
            );
            *generic = !out.is_empty();
        }
        for (index, generic) in rows.func_types.iter_mut().enumerate() {
            let mut out = BTreeSet::new();
            refs.func_ty_row(
                FuncTyId::new(u32::try_from(index).unwrap_or(u32::MAX)),
                &mut out,
            );
            *generic = !out.is_empty();
        }
        rows
    }

    /// Whether `ty` mentions a parameter or hole, directly or through a row.
    #[must_use]
    pub fn ty_is_generic(&self, ty: &TyG<TemplateRef>) -> bool {
        let mut generic = false;
        ty.for_each_ext(&mut |_| generic = true);
        if generic {
            return true;
        }
        let mut via_ty_row = false;
        let mut via_func_ty_row = false;
        ty.for_each_row(
            &mut |row| via_ty_row |= self.types.get(row.as_usize()).copied().unwrap_or(false),
            &mut |row| {
                via_func_ty_row |= self
                    .func_types
                    .get(row.as_usize())
                    .copied()
                    .unwrap_or(false);
            },
        );
        generic || via_ty_row || via_func_ty_row
    }

    /// Whether a level-R (ground-table) type names a generic row.
    #[must_use]
    pub fn ground_ty_names_generic_row(&self, ty: &Ty) -> bool {
        let generic = false;
        let mut via_ty_row = false;
        let mut via_func_ty_row = false;
        ty.for_each_row(
            &mut |row| via_ty_row |= self.types.get(row.as_usize()).copied().unwrap_or(false),
            &mut |row| {
                via_func_ty_row |= self
                    .func_types
                    .get(row.as_usize())
                    .copied()
                    .unwrap_or(false);
            },
        );
        generic || via_ty_row || via_func_ty_row
    }
}

/// Collects the [`TemplateRef`]s a type mentions, through `types` and
/// `func_types` rows, memoized per row.
pub struct RefCollector<'t> {
    module: &'t ModuleG<TemplateRef>,
    ty_memo: BTreeMap<u32, BTreeSet<TemplateRef>>,
    fty_memo: BTreeMap<u32, BTreeSet<TemplateRef>>,
    on_path_ty: BTreeSet<u32>,
    on_path_fty: BTreeSet<u32>,
}

impl<'t> RefCollector<'t> {
    #[must_use]
    pub fn new(module: &'t ModuleG<TemplateRef>) -> Self {
        Self {
            module,
            ty_memo: BTreeMap::new(),
            fty_memo: BTreeMap::new(),
            on_path_ty: BTreeSet::new(),
            on_path_fty: BTreeSet::new(),
        }
    }

    /// Add every reference `ty` makes to `out`.
    pub fn ty(&mut self, ty: &TyG<TemplateRef>, out: &mut BTreeSet<TemplateRef>) {
        ty.for_each_ext(&mut |r| {
            out.insert(*r);
        });
        let mut ty_rows = Vec::new();
        let mut fty_rows = Vec::new();
        ty.for_each_row(&mut |row| ty_rows.push(row), &mut |row| fty_rows.push(row));
        for row in ty_rows {
            self.ty_row(row, out);
        }
        for row in fty_rows {
            self.func_ty_row(row, out);
        }
    }

    /// Add every reference the `types` row `row` makes to `out`.
    pub fn ty_row(&mut self, row: TyId, out: &mut BTreeSet<TemplateRef>) {
        let key = row.index();
        if let Some(memo) = self.ty_memo.get(&key) {
            out.extend(memo.iter().copied());
            return;
        }
        if !self.on_path_ty.insert(key) {
            return;
        }
        let mut local = BTreeSet::new();
        if let Some(ty) = self.module.types.get(row.as_usize()) {
            self.ty(ty, &mut local);
        }
        self.on_path_ty.remove(&key);
        out.extend(local.iter().copied());
        self.ty_memo.insert(key, local);
    }

    /// Add every reference the `func_types` row `row` makes to `out`.
    pub fn func_ty_row(&mut self, row: FuncTyId, out: &mut BTreeSet<TemplateRef>) {
        let key = row.index();
        if let Some(memo) = self.fty_memo.get(&key) {
            out.extend(memo.iter().copied());
            return;
        }
        if !self.on_path_fty.insert(key) {
            return;
        }
        let mut local = BTreeSet::new();
        if let Some(signature) = self.module.func_types.get(row.as_usize()) {
            for ty in signature.params.iter().chain(&signature.returns) {
                self.ty(ty, &mut local);
            }
        }
        self.on_path_fty.remove(&key);
        out.extend(local.iter().copied());
        self.fty_memo.insert(key, local);
    }
}

struct Checker<'t> {
    t: &'t Template,
    rows: GenericRows,
    errors: Vec<TemplateError>,
}

impl<'t> Checker<'t> {
    fn new(t: &'t Template) -> Self {
        Self {
            t,
            rows: GenericRows::of(&t.module),
            errors: Vec::new(),
        }
    }

    fn run(mut self) -> Vec<TemplateError> {
        self.identity();
        self.body_shape();
        self.proof_surface();
        self.scope();
        self.holes();
        self.rows_are_holes();
        self.ground_tables();
        self.literals_and_operations();
        self.errors
    }

    fn push(&mut self, error: TemplateError) {
        self.errors.push(error);
    }

    // T9
    fn identity(&mut self) {
        let identity = &self.t.header.identity;
        if identity.is_empty() || identity.contains(['\n', '\r']) {
            self.push(TemplateError::InvalidIdentity);
        }
    }

    // T7: one definition named `!template_body`, then declarations; the body
    // row and every hole row carry the defaults of the facts the host answers.
    fn body_shape(&mut self) {
        let t = self.t;
        let functions = &t.module.functions;
        let Some(body) = functions.first() else {
            self.push(TemplateError::TemplateBodyShape {
                why: "a template has no body row".to_string(),
            });
            return;
        };
        if body.blocks.is_empty() {
            self.push(TemplateError::TemplateBodyShape {
                why: "functions[0] is a declaration; the body row is a definition".to_string(),
            });
        }
        if body.name != TEMPLATE_BODY_NAME {
            self.push(TemplateError::TemplateBodyShape {
                why: format!(
                    "the body row is named `{}`, not `{TEMPLATE_BODY_NAME}` (the host names the instance)",
                    body.name
                ),
            });
        }
        for function in &functions[1..] {
            if !function.blocks.is_empty() {
                self.push(TemplateError::TemplateBodyShape {
                    why: format!(
                        "`{}` is a second definition; a template has one body",
                        function.name
                    ),
                });
            }
        }
        let hole_rows: Vec<&FunctionG<TemplateRef>> = std::iter::once(body)
            .chain(
                functions[1..]
                    .iter()
                    .filter(|f| f.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX)),
            )
            .collect();
        for function in hole_rows {
            if let Some(fact) = host_answered_fact(function) {
                self.push(TemplateError::TemplateBodyShape {
                    why: format!(
                        "`{}` states its {fact}, which the host answers at instantiation",
                        function.name
                    ),
                });
            }
        }
        for global in &t.module.globals {
            if global.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX)
                && (global.initializer.is_some()
                    || global.linkage != crate::Linkage::default()
                    || global.visibility != crate::Visibility::default()
                    || global.align.is_some()
                    || global.section.is_some()
                    || global.retained
                    || global.tls.is_some())
            {
                self.push(TemplateError::TemplateBodyShape {
                    why: format!(
                        "global `{}` states a fact the host answers (initializer, linkage, \
                         visibility, alignment, section, retention or TLS)",
                        global.name
                    ),
                });
            }
        }
    }

    // T7: no proof surface.
    fn proof_surface(&mut self) {
        let t = self.t;
        let m = &t.module;
        let mut what = Vec::new();
        if !m.proof_obligations.is_empty() {
            what.push("proof obligations");
        }
        if !m.proof_certificates.is_empty() {
            what.push("proof certificates");
        }
        if !m.obligation_diagnostics.is_empty() {
            what.push("obligation diagnostics");
        }
        if !m.spec_modules.is_empty() {
            what.push("spec modules");
        }
        if !m.imports.is_empty() {
            what.push("imports");
        }
        if m.completeness.is_some() {
            what.push("a completeness claim");
        }
        if !m.global_asm.is_empty() {
            what.push("global asm");
        }
        if m.functions
            .iter()
            .any(|f| !f.proofs.is_empty() || f.summary.is_some())
        {
            what.push("function proofs or summaries");
        }
        if m.functions.iter().any(|f| {
            f.blocks.iter().any(|b| {
                b.body
                    .iter()
                    .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
            })
        }) {
            what.push("instruction proofs or proof contexts");
        }
        for what in what {
            self.push(TemplateError::TemplateUnsupported {
                what: format!("{what} (proof surface stays on level R)"),
            });
        }
    }

    // T1: every reference is in scope and of an admitted kind.
    fn scope(&mut self) {
        let t = self.t;
        let module = &t.module;
        let mut sites: Vec<(String, &TyG<TemplateRef>)> = Vec::new();
        for (index, ty) in module.types.iter().enumerate() {
            sites.push((format!("type row {index}"), ty));
        }
        for (index, signature) in module.func_types.iter().enumerate() {
            for ty in signature.params.iter().chain(&signature.returns) {
                sites.push((format!("functy row {index}"), ty));
            }
        }
        for global in &module.globals {
            sites.push((format!("global `{}`", global.name), &global.ty));
        }
        for function in &module.functions {
            for block in &function.blocks {
                for (_, ty) in &block.params {
                    sites.push((
                        format!("`{}` bb{} parameter", function.name, block.id.index()),
                        ty,
                    ));
                }
                for (index, node) in block.body.iter().enumerate() {
                    node.inst.for_each_ty(|ty| {
                        sites.push((
                            format!(
                                "`{}` bb{} instruction {index}",
                                function.name,
                                block.id.index()
                            ),
                            ty,
                        ));
                    });
                }
            }
        }
        for (h, hole) in t.header.holes.iter().enumerate() {
            for arg in &hole.args {
                if let TemplateArg::Type(ty) = arg {
                    sites.push((format!("hole ?{h} argument"), ty));
                }
            }
            if let HoleKind::Type { contract } = &hole.kind {
                for ty in contract_tys(contract) {
                    sites.push((format!("hole ?{h} contract"), ty));
                }
            }
        }
        let mut errors = Vec::new();
        for (at, ty) in sites {
            ty.for_each_ext(&mut |r| {
                if let Some(error) = self.type_ref_error(*r, &at) {
                    errors.push(error);
                }
            });
        }
        // Constant positions: the root of an `Inst::Const` value.
        for function in &module.functions {
            for block in &function.blocks {
                for (index, node) in block.body.iter().enumerate() {
                    if let InstG::Const {
                        ty,
                        value: ConstantG::Ext(r),
                    } = &node.inst
                    {
                        let at = format!(
                            "`{}` bb{} instruction {index}",
                            function.name,
                            block.id.index()
                        );
                        if let Some(error) = self.const_ref_error(*r, ty, &at) {
                            errors.push(error);
                        }
                    }
                }
            }
        }
        // Hole arguments: const and host forms.
        for (h, hole) in t.header.holes.iter().enumerate() {
            for arg in &hole.args {
                let at = format!("hole ?{h} argument");
                match arg {
                    TemplateArg::Type(_) => {}
                    TemplateArg::Const { value, ty } => {
                        if let ConstantG::Ext(r) = value
                            && let Some(error) = self.const_ref_error(*r, &ty.embed(), &at)
                        {
                            errors.push(error);
                        }
                    }
                    TemplateArg::Host(p) => match t.header.params.get(p.as_usize()) {
                        None => errors.push(TemplateError::ParamOutOfScope {
                            param: p.index(),
                            at,
                        }),
                        Some(TemplateParam::Host) => {}
                        Some(_) => errors.push(TemplateError::ParamKindMismatch {
                            param: p.index(),
                            at,
                        }),
                    },
                }
            }
        }
        self.errors.extend(errors);
    }

    fn type_ref_error(&self, r: TemplateRef, at: &str) -> Option<TemplateError> {
        match r {
            TemplateRef::Param(p) => match self.t.header.params.get(p.as_usize()) {
                None => Some(TemplateError::ParamOutOfScope {
                    param: p.index(),
                    at: at.to_string(),
                }),
                Some(TemplateParam::Type) => None,
                Some(_) => Some(TemplateError::ParamKindMismatch {
                    param: p.index(),
                    at: format!("{at}: a type position needs a type parameter"),
                }),
            },
            TemplateRef::Hole(h) => match self.t.header.holes.get(h.as_usize()) {
                None => Some(TemplateError::HoleOutOfScope {
                    hole: h.index(),
                    at: at.to_string(),
                }),
                Some(HoleDef {
                    kind: HoleKind::Type { .. },
                    ..
                }) => None,
                Some(_) => Some(TemplateError::HoleKindMismatch {
                    hole: h.index(),
                    at: format!("{at}: a type position needs a type hole"),
                }),
            },
        }
    }

    fn const_ref_error(
        &self,
        r: TemplateRef,
        at_ty: &TyG<TemplateRef>,
        at: &str,
    ) -> Option<TemplateError> {
        match r {
            TemplateRef::Param(p) => match self.t.header.params.get(p.as_usize()) {
                None => Some(TemplateError::ParamOutOfScope {
                    param: p.index(),
                    at: at.to_string(),
                }),
                Some(TemplateParam::Const { ty }) if ty.embed::<TemplateRef>() == *at_ty => None,
                Some(_) => Some(TemplateError::ParamKindMismatch {
                    param: p.index(),
                    at: format!("{at}: a constant position needs a const parameter of its type"),
                }),
            },
            TemplateRef::Hole(h) => match self.t.header.holes.get(h.as_usize()) {
                None => Some(TemplateError::HoleOutOfScope {
                    hole: h.index(),
                    at: at.to_string(),
                }),
                Some(HoleDef {
                    kind: HoleKind::Const { ty },
                    ..
                }) if ty.embed::<TemplateRef>() == *at_ty => None,
                Some(_) => Some(TemplateError::HoleKindMismatch {
                    hole: h.index(),
                    at: format!("{at}: a constant position needs a const hole of its type"),
                }),
            },
        }
    }

    // T2: the hole table is canonical.
    fn holes(&mut self) {
        let t = self.t;
        let holes = &t.header.holes;
        let mut refs = RefCollector::new(&t.module);
        let mut first_of: HashMap<&HoleDef, usize> = HashMap::new();
        let mut depends: Vec<bool> = Vec::with_capacity(holes.len());
        for (h, hole) in holes.iter().enumerate() {
            let h32 = u32::try_from(h).unwrap_or(u32::MAX);
            if let Some(first) = first_of.get(hole) {
                self.push(TemplateError::DuplicateHole {
                    hole: h32,
                    first: u32::try_from(*first).unwrap_or(u32::MAX),
                });
            } else {
                first_of.insert(hole, h);
            }
            if !hole.key.namespace_is_valid() {
                self.push(TemplateError::InvalidHostKey { hole: h32 });
            }
            // Arguments name parameters and LOWER holes only (through rows too).
            let mut named = BTreeSet::new();
            let mut on_param = false;
            for arg in &hole.args {
                match arg {
                    TemplateArg::Type(ty) => refs.ty(ty, &mut named),
                    TemplateArg::Const { value, .. } => {
                        if let ConstantG::Ext(r) = value {
                            named.insert(*r);
                        }
                    }
                    TemplateArg::Host(_) => on_param = true,
                }
            }
            for r in &named {
                match r {
                    TemplateRef::Param(_) => on_param = true,
                    TemplateRef::Hole(other) => {
                        if other.as_usize() >= h {
                            self.push(TemplateError::HoleCycle {
                                hole: h32,
                                names: other.index(),
                            });
                        } else if depends.get(other.as_usize()).copied().unwrap_or(false) {
                            on_param = true;
                        }
                    }
                }
            }
            depends.push(on_param);
            if !on_param {
                self.push(TemplateError::GroundHole { hole: h32 });
            }
        }
        self.hole_rows();
        self.unused_holes(&mut refs);
    }

    fn hole_rows(&mut self) {
        let t = self.t;
        let module = &t.module;
        let mut named_rows: BTreeSet<(bool, String)> = BTreeSet::new();
        for (h, hole) in t.header.holes.iter().enumerate() {
            let expected = hole_row_name(HoleId::new(u32::try_from(h).unwrap_or(u32::MAX)));
            match &hole.kind {
                HoleKind::Callee { decl } => {
                    let row = module
                        .functions
                        .iter()
                        .enumerate()
                        .find(|(_, f)| f.id == *decl);
                    match row {
                        Some((0, _)) => self.push(TemplateError::HoleRowMismatch {
                            why: format!("callee hole ?{h} names the body row"),
                        }),
                        Some((_, f)) if f.name == expected => {
                            if !named_rows.insert((true, expected.clone())) {
                                self.push(TemplateError::HoleRowMismatch {
                                    why: format!("row `{expected}` is named by two holes"),
                                });
                            }
                        }
                        Some((_, f)) => self.push(TemplateError::HoleRowMismatch {
                            why: format!(
                                "callee hole ?{h} names row `{}`, not `{expected}`",
                                f.name
                            ),
                        }),
                        None => self.push(TemplateError::HoleRowMismatch {
                            why: format!(
                                "callee hole ?{h} names @func.{}, which no row has",
                                decl.index()
                            ),
                        }),
                    }
                }
                HoleKind::Global { decl } => match module.globals.get(decl.as_usize()) {
                    Some(g) if g.name == expected => {
                        if !named_rows.insert((false, expected.clone())) {
                            self.push(TemplateError::HoleRowMismatch {
                                why: format!("global `{expected}` is named by two holes"),
                            });
                        }
                    }
                    Some(g) => self.push(TemplateError::HoleRowMismatch {
                        why: format!(
                            "global hole ?{h} names global `{}`, not `{expected}`",
                            g.name
                        ),
                    }),
                    None => self.push(TemplateError::HoleRowMismatch {
                        why: format!(
                            "global hole ?{h} names global {}, which does not exist",
                            decl.index()
                        ),
                    }),
                },
                HoleKind::Type { .. } | HoleKind::Const { .. } => {}
            }
        }
        for function in module.functions.iter().skip(1) {
            if function.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX)
                && !named_rows.contains(&(true, function.name.clone()))
            {
                self.push(TemplateError::HoleRowMismatch {
                    why: format!(
                        "row `{}` carries a reserved name no callee hole names",
                        function.name
                    ),
                });
            }
        }
        for global in &module.globals {
            if global.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX)
                && !named_rows.contains(&(false, global.name.clone()))
            {
                self.push(TemplateError::HoleRowMismatch {
                    why: format!(
                        "global `{}` carries a reserved name no global hole names",
                        global.name
                    ),
                });
            }
        }
    }

    fn unused_holes(&mut self, refs: &mut RefCollector<'_>) {
        let t = self.t;
        let module = &t.module;
        let mut used = BTreeSet::new();
        for ty in &module.types {
            refs.ty(ty, &mut used);
        }
        for signature in &module.func_types {
            for ty in signature.params.iter().chain(&signature.returns) {
                refs.ty(ty, &mut used);
            }
        }
        for global in &module.globals {
            refs.ty(&global.ty, &mut used);
        }
        for function in &module.functions {
            refs.func_ty_row(function.ty, &mut used);
            for block in &function.blocks {
                for (_, ty) in &block.params {
                    refs.ty(ty, &mut used);
                }
                for node in &block.body {
                    let mut tys = Vec::new();
                    node.inst.for_each_ty(|ty| tys.push(ty));
                    for ty in tys {
                        refs.ty(ty, &mut used);
                    }
                    if let InstG::Const {
                        value: ConstantG::Ext(r),
                        ..
                    } = &node.inst
                    {
                        used.insert(*r);
                    }
                }
            }
        }
        for hole in &t.header.holes {
            for arg in &hole.args {
                match arg {
                    TemplateArg::Type(ty) => refs.ty(ty, &mut used),
                    TemplateArg::Const {
                        value: ConstantG::Ext(r),
                        ..
                    } => {
                        used.insert(*r);
                    }
                    TemplateArg::Const { .. } | TemplateArg::Host(_) => {}
                }
            }
            if let HoleKind::Type { contract } = &hole.kind {
                for ty in contract_tys(contract) {
                    refs.ty(ty, &mut used);
                }
            }
        }
        for (h, hole) in t.header.holes.iter().enumerate() {
            let id = HoleId::new(u32::try_from(h).unwrap_or(u32::MAX));
            let row_hole = matches!(hole.kind, HoleKind::Callee { .. } | HoleKind::Global { .. });
            if !row_hole && !used.contains(&TemplateRef::Hole(id)) {
                self.push(TemplateError::UnusedHole { hole: id.index() });
            }
        }
    }

    // T2: a row whose type is generic is a hole row.
    fn rows_are_holes(&mut self) {
        let t = self.t;
        let module = &t.module;
        for function in module.functions.iter().skip(1) {
            let generic = self
                .rows
                .func_types
                .get(function.ty.as_usize())
                .copied()
                .unwrap_or(false);
            if generic && !function.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX) {
                self.push(TemplateError::GenericRowNotAHole {
                    row: format!("declaration `{}`", function.name),
                });
            }
        }
        for global in &module.globals {
            if self.rows.ty_is_generic(&global.ty)
                && !global.name.starts_with(TEMPLATE_HOLE_ROW_PREFIX)
            {
                self.push(TemplateError::GenericRowNotAHole {
                    row: format!("global `{}`", global.name),
                });
            }
        }
    }

    // T5: ground tables name only ground rows.
    fn ground_tables(&mut self) {
        let t = self.t;
        let module = &t.module;
        let rows = &self.rows;
        let mut errors = Vec::new();
        let check =
            |errors: &mut Vec<TemplateError>, table: &'static str, index: usize, ty: &Ty| {
                if rows.ground_ty_names_generic_row(ty) {
                    errors.push(TemplateError::ExtInGroundTable {
                        table,
                        index: u32::try_from(index).unwrap_or(u32::MAX),
                    });
                }
            };
        for (index, sd) in module.structs.iter().enumerate() {
            for field in &sd.fields {
                if rows.ty_is_generic(&field.ty) {
                    errors.push(TemplateError::ExtInGroundTable {
                        table: "struct",
                        index: u32::try_from(index).unwrap_or(u32::MAX),
                    });
                }
            }
        }
        for (index, ed) in module.enums.iter().enumerate() {
            for variant in &ed.variants {
                for ty in &variant.fields {
                    if rows.ty_is_generic(ty) {
                        errors.push(TemplateError::ExtInGroundTable {
                            table: "enum",
                            index: u32::try_from(index).unwrap_or(u32::MAX),
                        });
                    }
                }
            }
        }
        for (index, rd) in module.records.iter().enumerate() {
            for field in &rd.fields {
                check(&mut errors, "record", index, &field.ty);
            }
        }
        for (index, ct) in module.closure_types.iter().enumerate() {
            for ty in &ct.captures {
                check(&mut errors, "closure-type", index, ty);
            }
            if rows
                .func_types
                .get(ct.func.as_usize())
                .copied()
                .unwrap_or(false)
            {
                errors.push(TemplateError::ExtInGroundTable {
                    table: "closure-type",
                    index: u32::try_from(index).unwrap_or(u32::MAX),
                });
            }
        }
        for (index, layout) in module.tuple_layouts.iter().enumerate() {
            if rows
                .types
                .get(layout.tuple_type.as_usize())
                .copied()
                .unwrap_or(false)
            {
                errors.push(TemplateError::ExtInGroundTable {
                    table: "tuple-layout",
                    index: u32::try_from(index).unwrap_or(u32::MAX),
                });
            }
        }
        for (index, entry) in module.drop_glue.iter().enumerate() {
            check(&mut errors, "drop-glue", index, &entry.ty);
        }
        self.errors.extend(errors);
    }

    // T3, T4, T8 over the body and every type row.
    fn literals_and_operations(&mut self) {
        let t = self.t;
        let module = &t.module;
        let holes = &t.header.holes;
        let rows = &self.rows;
        let opaque = |ty: &TyG<TemplateRef>| match ty.head_ext() {
            Some(TemplateRef::Param(_)) => true,
            Some(TemplateRef::Hole(h)) => matches!(
                holes.get(h.as_usize()),
                Some(HoleDef {
                    kind: HoleKind::Type {
                        contract: TypeContract::Opaque
                    },
                    ..
                })
            ),
            None => false,
        };
        let mut errors = Vec::new();
        // T8 on types: no tensor at all (a type former of SemR's type
        // fragment, `lean/semr/TY_FRAGMENT.tsv`, has no level-S role and no
        // `TemplateTy` constructor yet: PKG-U13a), and no vector, sequence,
        // set or refinement over a parameter-dependent type.
        let tensor_ty = refuse_tensor::<TemplateRef>;
        let unsupported_ty = |ty: &TyG<TemplateRef>, at: &str, errors: &mut Vec<TemplateError>| {
            tensor_ty(ty, at, errors);
            let mut bad = None;
            walk_ty(ty, &mut |t| match t {
                TyG::Vector(inner, _) if rows.ty_is_generic(inner) => bad = Some("a vector"),
                TyG::Sequence(row) | TyG::Set(row, _) | TyG::Refine(row, _)
                    if rows.types.get(row.as_usize()).copied().unwrap_or(false) =>
                {
                    bad = Some("a sequence, set or refinement")
                }
                _ => {}
            });
            if let Some(what) = bad {
                errors.push(TemplateError::TemplateUnsupported {
                    what: format!("{what} over a parameter-dependent type ({at})"),
                });
            }
        };
        for (index, ty) in module.types.iter().enumerate() {
            unsupported_ty(ty, &format!("type row {index}"), &mut errors);
        }
        // Every other table that spells a type: globals (at the template's
        // level), and the ground record, closure-capture and drop-glue rows.
        for (index, global) in module.globals.iter().enumerate() {
            tensor_ty(&global.ty, &format!("global {index}"), &mut errors);
        }
        for (index, record) in module.records.iter().enumerate() {
            for (field, def) in record.fields.iter().enumerate() {
                refuse_tensor(
                    &def.ty,
                    &format!("record {index} field {field}"),
                    &mut errors,
                );
            }
        }
        for (index, closure) in module.closure_types.iter().enumerate() {
            for (capture, ty) in closure.captures.iter().enumerate() {
                refuse_tensor(
                    ty,
                    &format!("closure type {index} capture {capture}"),
                    &mut errors,
                );
            }
        }
        for (index, entry) in module.drop_glue.iter().enumerate() {
            refuse_tensor(&entry.ty, &format!("drop-glue row {index}"), &mut errors);
        }
        for def in &module.structs {
            for (index, field) in def.fields.iter().enumerate() {
                tensor_ty(
                    &field.ty,
                    &format!("struct {} field {index}", def.id.0),
                    &mut errors,
                );
            }
        }
        for def in &module.enums {
            for (v, variant) in def.variants.iter().enumerate() {
                for (index, ty) in variant.fields.iter().enumerate() {
                    tensor_ty(
                        ty,
                        &format!("enum {} variant {v} field {index}", def.id.0),
                        &mut errors,
                    );
                }
            }
        }
        for (index, signature) in module.func_types.iter().enumerate() {
            for ty in signature.params.iter().chain(&signature.returns) {
                unsupported_ty(ty, &format!("functy row {index}"), &mut errors);
            }
        }
        for (index, param) in t.header.params.iter().enumerate() {
            if let TemplateParam::Const { ty } = param
                && !is_template_scalar(ty)
            {
                errors.push(TemplateError::TemplateUnsupported {
                    what: format!("const parameter ${index} of the non-scalar type {ty}"),
                });
            }
        }
        for (h, hole) in holes.iter().enumerate() {
            if let HoleKind::Const { ty } = &hole.kind
                && !is_template_scalar(ty)
            {
                errors.push(TemplateError::TemplateUnsupported {
                    what: format!("const hole ?{h} of the non-scalar type {ty}"),
                });
            }
        }
        for function in &module.functions {
            for block in &function.blocks {
                for (_, ty) in &block.params {
                    unsupported_ty(
                        ty,
                        &format!("`{}` bb{} parameter", function.name, block.id.index()),
                        &mut errors,
                    );
                }
                for (index, node) in block.body.iter().enumerate() {
                    let at = format!(
                        "`{}` bb{} instruction {index}",
                        function.name,
                        block.id.index()
                    );
                    let mut tys = Vec::new();
                    node.inst.for_each_ty(|ty| tys.push(ty));
                    for ty in tys {
                        unsupported_ty(ty, &at, &mut errors);
                    }
                    if let Some(error) = inst_rule(&node.inst, &at, rows, &opaque) {
                        errors.push(error);
                    }
                }
            }
        }
        self.errors.extend(errors);
    }
}

/// The facts a body or hole row must leave to the host (T7), the first one it
/// states.
fn host_answered_fact(function: &FunctionG<TemplateRef>) -> Option<&'static str> {
    if function.linkage != crate::Linkage::default() {
        return Some("linkage");
    }
    if function.visibility != crate::Visibility::default() {
        return Some("visibility");
    }
    if function.calling_conv != crate::CallingConv::default() {
        return Some("calling convention");
    }
    if function.attrs != crate::FuncAttrs::default() {
        return Some("attributes");
    }
    if function.body_gate.is_some() {
        return Some("body gate");
    }
    if function.display_path.is_some() {
        return Some("display path");
    }
    if function.section.is_some() {
        return Some("section");
    }
    if function.retained {
        return Some("retention");
    }
    if function.source_provenance.is_some() {
        return Some("source provenance");
    }
    None
}

/// T8: a tensor anywhere in `ty` (inline, not through rows: each row is
/// checked where it is declared) is refused, whatever its element. A type
/// former of SemR's type fragment (`lean/semr/TY_FRAGMENT.tsv`) has no
/// level-S role and no `TemplateTy` constructor yet (PKG-U13a).
fn refuse_tensor<X>(ty: &TyG<X>, at: &str, errors: &mut Vec<TemplateError>) {
    let mut tensor = false;
    walk_ty(ty, &mut |t| tensor |= matches!(t, TyG::Tensor(..)));
    if tensor {
        errors.push(TemplateError::TemplateUnsupported {
            what: format!("a tensor ({at}): the tensor region has no template role yet"),
        });
    }
}

/// Visit `ty` and every type nested in it (not through rows), in preorder.
fn walk_ty<X>(ty: &TyG<X>, f: &mut dyn FnMut(&TyG<X>)) {
    f(ty);
    match ty {
        TyG::Vector(inner, _)
        | TyG::Tensor(inner, _)
        | TyG::Ref(inner)
        | TyG::RefMut(inner)
        | TyG::PtrConst(inner)
        | TyG::PtrMut(inner)
        | TyG::Rc(inner) => walk_ty(inner, f),
        TyG::Tuple(elems) => elems.iter().for_each(|elem| walk_ty(elem, f)),
        _ => {}
    }
}

/// The types a contract names.
pub fn contract_tys(contract: &TypeContract) -> Vec<&TyG<TemplateRef>> {
    match contract {
        TypeContract::Opaque => Vec::new(),
        TypeContract::Struct { fields } => fields.iter().collect(),
        TypeContract::Enum { variants, .. } => variants.iter().flatten().collect(),
    }
}

/// T3, T4 and the instruction half of T8, for one instruction.
fn inst_rule(
    inst: &InstG<TemplateRef>,
    at: &str,
    rows: &GenericRows,
    opaque: &dyn Fn(&TyG<TemplateRef>) -> bool,
) -> Option<TemplateError> {
    let opaque_op = |what: &str| {
        Some(TemplateError::OpaqueOperation {
            at: format!("{at}: {what} at an opaque type"),
        })
    };
    let unsupported = |what: &str| {
        Some(TemplateError::TemplateUnsupported {
            what: format!("{what} ({at})"),
        })
    };
    let literal = |what: &str| {
        Some(TemplateError::ParamDependentLiteral {
            at: format!("{at}: {what}"),
        })
    };
    // T3: an alignment literal at a parameter-dependent type, other than 1
    // (an under-aligned access is valid at every type).
    let align_literal = |ty: &TyG<TemplateRef>, align: &Option<u64>| {
        matches!(align, Some(a) if *a != 1) && rows.ty_is_generic(ty)
    };
    match inst {
        InstG::Load { ty, align, .. }
        | InstG::Store { ty, align, .. }
        | InstG::Alloca { ty, align, .. }
        | InstG::HeapAlloc { ty, align, .. }
            if align_literal(ty, align) =>
        {
            literal("an alignment literal other than 1")
        }
        InstG::BinOp { ty, .. }
        | InstG::UnOp { ty, .. }
        | InstG::Overflow { ty, .. }
        | InstG::ICmp { ty, .. }
        | InstG::FCmp { ty, .. }
            if opaque(ty) =>
        {
            opaque_op("arithmetic or comparison")
        }
        InstG::Cast { src_ty, dst_ty, .. } if opaque(src_ty) || opaque(dst_ty) => {
            opaque_op("a cast")
        }
        InstG::AtomicLoad { ty, .. }
        | InstG::AtomicStore { ty, .. }
        | InstG::AtomicRMW { ty, .. }
        | InstG::CmpXchg { ty, .. }
            if opaque(ty) =>
        {
            opaque_op("an atomic operation")
        }
        InstG::PtrData { ptr_ty, .. } if opaque(ptr_ty) => opaque_op("a pointer-part operation"),
        InstG::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | InstG::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } if opaque(ptr_ty) || opaque(metadata_ty) => opaque_op("a pointer-part operation"),
        InstG::MakeAggregate { ty, .. } if opaque(ty) => opaque_op("building a value"),
        InstG::InsertField { ty, .. } | InstG::InsertElement { ty, .. } if opaque(ty) => {
            opaque_op("writing a lane")
        }
        InstG::Const { ty, value } if opaque(ty) && !matches!(value, ConstantG::Ext(_)) => {
            opaque_op("a constant")
        }
        InstG::CoroSuspend { .. } => unsupported("a coroutine suspend"),
        InstG::DialectOp(_) => unsupported("a dialect op"),
        InstG::OpenFrame { .. }
        | InstG::BindSlot { .. }
        | InstG::LoadSlot { .. }
        | InstG::CloseFrame { .. } => unsupported("a binding frame"),
        InstG::SeqMapAddK { .. } | InstG::SeqMapNot { .. } | InstG::SeqMap { .. } => {
            unsupported("a sequence op")
        }
        // PKG-U13a: the tensor region has no template role yet (its
        // instantiation over a parameter-dependent element or rank is
        // undecided), so a template carrying one fails closed.
        InstG::TensorContract { .. } => unsupported("a tensor contraction"),
        // PKG-U13c: likewise the map, the reduction and the view.
        InstG::TensorMap { .. } => unsupported("a tensor map"),
        InstG::TensorReduce { .. } => unsupported("a tensor reduction"),
        InstG::TensorView { .. } => unsupported("a tensor view"),
        // PKG-U13d: likewise the gather and the scatter.
        InstG::TensorGather { .. } => unsupported("a tensor gather"),
        InstG::TensorScatter { .. } => unsupported("a tensor scatter"),
        // Everything else transports its values, has no type field, or was
        // admitted above at a non-opaque type. Listed, not wildcarded: a new
        // instruction is a compile error here until its T4 role is decided.
        InstG::Load { .. }
        | InstG::Store { .. }
        | InstG::Alloca { .. }
        | InstG::HeapAlloc { .. }
        | InstG::BinOp { .. }
        | InstG::UnOp { .. }
        | InstG::Overflow { .. }
        | InstG::ICmp { .. }
        | InstG::FCmp { .. }
        | InstG::Cast { .. }
        | InstG::AtomicLoad { .. }
        | InstG::AtomicStore { .. }
        | InstG::AtomicRMW { .. }
        | InstG::CmpXchg { .. }
        | InstG::PtrData { .. }
        | InstG::PtrMetadata { .. }
        | InstG::PtrFromParts { .. }
        | InstG::MakeAggregate { .. }
        | InstG::MakeClosure { .. }
        | InstG::InsertField { .. }
        | InstG::InsertElement { .. }
        | InstG::Const { .. }
        | InstG::Drop { .. }
        | InstG::DropInvoke { .. }
        | InstG::GEP { .. }
        | InstG::Fence { .. }
        | InstG::Br { .. }
        | InstG::CondBr { .. }
        | InstG::Switch { .. }
        | InstG::Call { .. }
        | InstG::CallIndirect { .. }
        | InstG::CallCannotUnwind { .. }
        | InstG::CallIndirectCannotUnwind { .. }
        | InstG::Invoke { .. }
        | InstG::InvokeIndirect { .. }
        | InstG::Return { .. }
        | InstG::ExtractField { .. }
        | InstG::ExtractElement { .. }
        | InstG::NullPtr
        | InstG::GlobalAddr { .. }
        | InstG::Undef { .. }
        | InstG::Assume { .. }
        | InstG::Assert { .. }
        | InstG::AssertInvoke { .. }
        | InstG::Unreachable
        | InstG::Copy { .. }
        | InstG::Select { .. }
        | InstG::Borrow { .. }
        | InstG::BorrowMut { .. }
        | InstG::EndBorrow { .. }
        | InstG::Retain { .. }
        | InstG::Release { .. }
        | InstG::IsUnique { .. }
        | InstG::Dealloc { .. }
        | InstG::MemCopy { .. }
        | InstG::MemSet { .. }
        | InstG::LandingPad { .. }
        | InstG::Resume { .. }
        | InstG::ArraySplat { .. } => None,
    }
}

// ---------------------------------------------------------------------------
// The answer vocabulary (amendment S, §5): what a host answers, as data.
// The algorithm that asks and checks is `trust_ir_build::template`'s.
// ---------------------------------------------------------------------------

/// One level-R argument of a template parameter (or of a hole, substituted).
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum InstArg {
    /// A [`TemplateParam::Type`] argument.
    Type(Ty),
    /// A [`TemplateParam::Const`] argument.
    Const(crate::Constant),
    /// A [`TemplateParam::Host`] argument: the host's own key.
    Host(HostKey),
}

/// The link facts of a declaration the host names: a callee hole's row, or a
/// destructor's glue.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LinkAnswer {
    pub symbol: String,
    pub calling_conv: crate::CallingConv,
    pub attrs: crate::FuncAttrs,
    pub linkage: crate::Linkage,
}

impl LinkAnswer {
    /// An external declaration of `symbol` at the Rust convention.
    pub fn rust(symbol: impl Into<String>) -> Self {
        Self {
            symbol: symbol.into(),
            calling_conv: crate::CallingConv::Rust,
            attrs: crate::FuncAttrs::default(),
            linkage: crate::Linkage::External,
        }
    }
}

/// A global hole's answer: a symbol and link facts; a definition carries its
/// ground initializer (a parameter-dependent promoted), a declaration none.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GlobalAnswer {
    pub symbol: String,
    pub linkage: crate::Linkage,
    pub visibility: crate::Visibility,
    pub initializer: Option<crate::Constant>,
    pub align: Option<u32>,
}

/// The instance's own header: the facts of the body row a template leaves to
/// the host (T7).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InstanceHeader {
    pub symbol: String,
    pub linkage: crate::Linkage,
    pub visibility: crate::Visibility,
    pub calling_conv: crate::CallingConv,
    pub attrs: crate::FuncAttrs,
    pub display_path: Option<String>,
    pub body_gate: crate::BodyGate,
}

/// Whether an instantiated type owns a destructor (review R1).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Destructor {
    /// The type has no drop glue (Rust: `needs_drop` is false): a drop of it
    /// does nothing, and is erased.
    NoDestructor,
    /// The type's glue, declared by this answer; a drop of it resolves.
    Glue(LinkAnswer),
}

/// A declared tuple layout the host answers for a tuple substitution created.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TupleLayout {
    pub size: u64,
    pub align: u64,
    pub field_offsets: Vec<u64>,
}

/// One hole's answer.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum HoleAnswer {
    Type(Ty),
    Const(crate::Constant),
    Callee(LinkAnswer),
    Global(GlobalAnswer),
}

/// A scripted answer to one hole: an answer, or a refusal with its reason.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ScriptedAnswer {
    Answer(HoleAnswer),
    Refuse(String),
}

/// A host whose every answer is DATA (amendment S, §8): the must-refuse
/// corpus ships one beside each instantiation row, so a refusal is
/// reproducible bytes and a script, never a closure. Its rows (`structs`,
/// `enums`, `types`) are appended to the instance when the arguments are
/// asked, at the ids they carry.
#[derive(Debug, Clone, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScriptedHost {
    pub structs: Vec<crate::StructDef>,
    pub enums: Vec<crate::EnumDef>,
    pub types: Vec<Ty>,
    pub arguments: Vec<InstArg>,
    /// By hole id; a missing entry is a refusal.
    pub holes: Vec<ScriptedAnswer>,
    /// `None`: the instance header is refused.
    pub header: Option<InstanceHeader>,
    /// A missing type is a refusal.
    pub destructors: Vec<(Ty, Destructor)>,
    /// A missing tuple type has no declared layout.
    pub tuple_layouts: Vec<(Ty, TupleLayout)>,
    /// A misbehaving host, for the corpus: renames the instance when the
    /// arguments are asked (an edit, not an append).
    pub tamper: bool,
}

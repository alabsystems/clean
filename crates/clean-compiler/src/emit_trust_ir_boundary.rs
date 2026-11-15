// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed boundary carriers for Clean structures and inductives (two-language
//! roadmap WS6.9, F-102; DG-70 option (a)).
//!
//! # The representation does not change
//!
//! Inside a module Clean keeps its boxed Perceus object model: a structure or
//! an inductive is a `Ptr` to a runtime cell, allocated by `clean_alloc_ctor`
//! and released by the native ARC instructions. That is the runtime truth and
//! trust-ir carries it faithfully. What was missing is a BOUNDARY spelling a
//! second producer can share: a Rust caller has no way to hand a `Ptr` to a
//! Clean cell it never allocated.
//!
//! So for each REQUESTED export (`exports` in `plan_carrier_exports`) whose
//! signature is carrier-faithful, the back end adds a by-value WRAPPER:
//!
//! * a parameter of a non-recursive structure whose fields are all carrier
//!   scalars is a `Ty::Struct` with explicit `#[repr(C)]` field offsets;
//! * a parameter of a non-recursive inductive whose constructor fields are all
//!   carrier scalars is a `Ty::Enum` with a NORMATIVE `EnumLayoutDescriptor`
//!   (a `u8` tag at offset 0, then the payload union: the `#[repr(C, u8)]`
//!   layout, which is also trust-ir's canonical tagged-union layout);
//! * a carrier scalar (`Bool`, `UInt8`..`UInt64`, `Float`) is itself.
//!
//! The carrier scalars are exactly the types the WS6.9 design names. Anything
//! else — a recursive inductive, `Nat`, `String`, `Array`, a function, a
//! parameterised or indexed family, a dependent signature — gets NO carrier:
//! the export is refused as [`TrustIrError::NoTotalCarrier`]
//! (`carrier/no-total-carrier`), fail closed. It is never spelled as `Ptr`
//! and called complete. A carrier-typed RESULT is refused the same way for
//! now (the unmarshalling half is not built); a scalar result is carried.
//!
//! # Symbol discipline
//!
//! The boxed body KEEPS its export symbol: that is the Clean↔Clean ABI a
//! Clean importer binds to (WS6.8), and renaming it in place would silently
//! re-point every existing importer at a different `FuncTy`. The wrapper takes
//! a distinct, deterministic symbol, `carrier_symbol`: the exact source
//! identity's wire name under the reserved `__clean_typed_v1_` escape
//! namespace, which no user name can render to (every user name inside that
//! namespace is itself escaped to `__clean_typed_v1_a…`). The Rust-side
//! carrier map (WS5.18) is not built yet; until it is, this symbol IS the
//! carrier map's Clean column.
//!
//! # Where the wrapper is built (the allocation stays in L5IR)
//!
//! The marshalling that ALLOCATES is not trust-ir-only code. For every
//! combination of constructors the carrier parameters can take, the planner
//! adds one kernel definition (a "marshal-in helper"),
//!
//! ```text
//! area.__clean_carrier_in_1 : UInt64 → UInt64 → UInt64
//!   := fun w h => area (Shape.rect w h)
//! ```
//!
//! which the KERNEL type-checks (`Environment::add_decl`) before anything is
//! lowered, and which then goes through the ordinary pipeline: RC insertion,
//! L5IR, boxing, the post-boxing RC repair and `verify_rc_linearity` (WS6.2)
//! all see its constructor allocation and its release, and the C back end
//! emits it too. The trust-ir wrapper itself allocates nothing: it reads the
//! tag lane, switches to the arm of the active variant, projects that
//! variant's scalar lanes (`ExtractField`, under the dominating switch arm,
//! per WS2.2's lane model), and calls the arm's helper. A helper whose lowered
//! signature is not exactly its scalar fields (boxing moved one) is refused at
//! emission, never patched up.
//!
//! # What is not claimed
//!
//! The wrapper is stamped `BodyGate::Ungated`, like every body this back end
//! emits before the translation-validation minter runs, and the minter does
//! not cover it (it has no kernel source of its own). Kernel TV of the
//! marshaller is the WS6.6 Fragment-4 follow-up. The layout rule is a
//! PRODUCER decision recorded in `docs/DECISIONS.md`: WS5.18 ratifies the
//! Rust side of the same carrier, and a Rust declaration whose layout differs
//! is refused at linked validation (`ty_structurally_eq_across` compares the
//! full `StructDef` / `EnumDef`, descriptor included).

use std::collections::{BTreeMap, HashMap};

use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};
use trust_ir::inst::SwitchCase;
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef,
    StructRepr, Ty,
};
use trust_ir::value::{BlockId, FuncId, SourceSpan, ValueId};
use trust_ir::{BodyGate, Constant};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

use super::names::{wire_name, PREFIX};
use super::{lower_ret_tys, lower_ty, TrustIrError};
use crate::ir::IRDecl;
use crate::lcnf::Decl;

/// The refusal code every no-carrier export carries, matching the Rust side's
/// `trust-clean-carrier` spelling for the same verdict.
pub const NO_TOTAL_CARRIER: &str = "carrier/no-total-carrier";

/// The most constructor combinations one export may expand to (the product of
/// its enum parameters' variant counts). Beyond it the export is refused
/// rather than emitting an unbounded number of helpers.
pub const MAX_VARIANT_COMBINATIONS: usize = 64;

/// The most constructors one enum carrier may have: its tag is a `u8`.
const MAX_ENUM_VARIANTS: usize = 256;

/// A carrier scalar: a value that is its own boundary spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CarrierScalar {
    /// `Bool` (one byte).
    Bool,
    /// `UInt8`.
    U8,
    /// `UInt16`.
    U16,
    /// `UInt32`.
    U32,
    /// `UInt64`.
    U64,
    /// `Float` (IEEE binary64).
    F64,
}

impl CarrierScalar {
    fn of_kernel_name(name: &Name) -> Option<Self> {
        Some(match name.to_string().as_str() {
            "Bool" => Self::Bool,
            "UInt8" => Self::U8,
            "UInt16" => Self::U16,
            "UInt32" => Self::U32,
            "UInt64" => Self::U64,
            "Float" => Self::F64,
            _ => return None,
        })
    }

    /// The trust-ir type of this scalar.
    #[must_use]
    pub(crate) fn ty(self) -> Ty {
        match self {
            Self::Bool => Ty::Bool,
            Self::U8 => Ty::U8,
            Self::U16 => Ty::U16,
            Self::U32 => Ty::U32,
            Self::U64 => Ty::U64,
            Self::F64 => Ty::F64,
        }
    }

    /// Size in bytes, which is also the natural alignment.
    #[must_use]
    pub(crate) fn size(self) -> u64 {
        match self {
            Self::Bool | Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 | Self::F64 => 8,
        }
    }
}

/// One constructor of a carrier type: its kernel name, its trust-ir variant
/// name, and its fields (source name, if the type registers one, and scalar).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CarrierCtor {
    /// The kernel constructor (`Shape.rect`).
    pub ctor: Name,
    /// The constructor's last name component (`rect`), the variant name.
    pub short: String,
    /// Each field's kernel type expression (a closed scalar constant).
    field_tys: Vec<Expr>,
    /// Each field's scalar.
    pub fields: Vec<CarrierScalar>,
}

/// The boundary spelling of one parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CarrierTy {
    /// A carrier scalar, passed as itself.
    Scalar(CarrierScalar),
    /// A single-constructor type: a `Ty::Struct` with `#[repr(C)]` offsets.
    Struct {
        /// The inductive (`Pt`).
        name: Name,
        /// Field names: the registered structure fields, else positional.
        field_names: Vec<String>,
        /// The one constructor.
        ctor: CarrierCtor,
    },
    /// A multi-constructor type: a `Ty::Enum` with a `u8` tag and a
    /// normative layout descriptor.
    Enum {
        /// The inductive (`Shape`).
        name: Name,
        /// The constructors, in declaration (= tag) order.
        ctors: Vec<CarrierCtor>,
    },
}

impl CarrierTy {
    /// The constructors this parameter can take: one for a scalar (no
    /// constructor at all, but one "arm") and a structure, `n` for an enum.
    fn arms(&self) -> usize {
        match self {
            Self::Scalar(_) | Self::Struct { .. } => 1,
            Self::Enum { ctors, .. } => ctors.len(),
        }
    }
}

/// One marshal-in helper: the kernel definition for one combination of
/// constructors, `choice[i]` being parameter `i`'s arm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CarrierHelper {
    /// The helper's kernel name (`area.__clean_carrier_in_1`).
    pub name: Name,
    /// The arm each parameter takes.
    pub choice: Vec<usize>,
}

/// One planned carrier export.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CarrierExport {
    /// The boxed body this wraps; its symbol is unchanged.
    pub source: Name,
    /// The wrapper's link-time symbol (`carrier_symbol`).
    pub symbol: String,
    /// Each parameter's boundary spelling.
    pub(crate) params: Vec<CarrierTy>,
    /// The (scalar) result.
    pub(crate) ret: CarrierScalar,
    /// One helper per constructor combination, in mixed-radix order of
    /// `choice` (the first parameter varies slowest).
    pub(crate) helpers: Vec<CarrierHelper>,
}

/// The result of [`plan_carrier_exports`]: the kernel environment extended by
/// the helpers, the L5CNF slice extended by their lowered declarations, and
/// the plan the trust-ir emitter realizes.
pub(crate) struct CarrierPlan {
    /// The input environment plus every helper definition, each admitted by
    /// the kernel's full `add_decl` check.
    pub env: Environment,
    /// The input declarations followed by the helpers' L5CNF declarations.
    pub decls: Vec<Decl>,
    /// The exports, in request order.
    pub exports: Vec<CarrierExport>,
}

/// The carrier symbol of `source`: `__clean_typed_v1_carrier_<wire name>`.
///
/// Deterministic, and disjoint from every symbol [`wire_name`] can produce:
/// a user name that starts with the reserved prefix is itself escaped, so it
/// renders to `__clean_typed_v1_a…`, never `__clean_typed_v1_carrier_…`.
#[must_use]
pub(crate) fn carrier_symbol(source: &Name) -> String {
    format!("{PREFIX}carrier_{}", wire_name(source))
}

/// The kernel name of `source`'s `k`-th marshal-in helper.
fn helper_name(source: &Name, k: usize) -> Name {
    source.clone().str(format!("__clean_carrier_in_{k}"))
}

fn refuse(decl: &Name, reason: impl Into<String>) -> TrustIrError {
    TrustIrError::NoTotalCarrier {
        decl: decl.to_string(),
        reason: reason.into(),
    }
}

/// A closed constant with no universe arguments, or `None`.
fn const_name(expr: &Expr) -> Option<&Name> {
    match expr.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => Some(name),
        ExprKind::MData(_, inner) => const_name(inner),
        _ => None,
    }
}

/// Split `Π (x₁ : T₁) … (xₙ : Tₙ), R` into its domains and codomain, refusing
/// a non-explicit binder or a dependent one (a `Tᵢ` or `R` that mentions a
/// bound variable).
fn split_signature(decl: &Name, ty: &Expr) -> Result<(Vec<Expr>, Expr), TrustIrError> {
    let mut domains = Vec::new();
    let mut cur = ty;
    loop {
        match cur.kind() {
            ExprKind::Pi(bd, domain, body) => {
                if bd.info != BinderInfo::Default {
                    return Err(refuse(
                        decl,
                        format!(
                            "parameter {} is not an explicit binder; a boundary carrier \
                             passes explicit runtime values only",
                            domains.len()
                        ),
                    ));
                }
                if domain.has_loose_bvars() {
                    return Err(refuse(
                        decl,
                        format!(
                            "parameter {} has a dependent type; a boundary carrier has a \
                             fixed layout",
                            domains.len()
                        ),
                    ));
                }
                domains.push(domain.as_ref().clone());
                cur = body;
            }
            ExprKind::MData(_, inner) => cur = inner,
            _ => break,
        }
    }
    if cur.has_loose_bvars() {
        return Err(refuse(
            decl,
            "the result type depends on a parameter; a boundary carrier has a fixed layout",
        ));
    }
    Ok((domains, cur.clone()))
}

/// Classify one kernel type as a carrier, or say why it has none.
fn classify(env: &Environment, decl: &Name, ty: &Expr) -> Result<CarrierTy, TrustIrError> {
    let Some(name) = const_name(ty) else {
        return Err(refuse(
            decl,
            format!(
                "`{ty}` is not a closed monomorphic type constant (a function, a type \
                 application or a universe-polymorphic type has no boundary carrier)"
            ),
        ));
    };
    if let Some(scalar) = CarrierScalar::of_kernel_name(name) {
        return Ok(CarrierTy::Scalar(scalar));
    }
    match name.to_string().as_str() {
        "Nat" | "Int" => {
            return Err(refuse(
                decl,
                format!(
                    "`{name}` has no boundary carrier: Clean's runtime Nat is not \
                     `trust_bignum::Nat`, and no converting shim is admitted (WS6.9 DECIDE 2, \
                     pending WS8 F-129)"
                ),
            ))
        }
        "String" | "Array" | "ByteArray" | "List" => {
            return Err(refuse(
                decl,
                format!("`{name}` has no boundary carrier (a runtime collection object)"),
            ))
        }
        _ => {}
    }
    let Some(ind) = env.get_inductive(name) else {
        return Err(refuse(
            decl,
            format!("`{name}` is neither a carrier scalar nor an inductive type"),
        ));
    };
    if ind.is_recursive || ind.is_reflexive || ind.is_nested || ind.all_names.len() != 1 {
        return Err(refuse(
            decl,
            format!(
                "`{name}` is recursive, nested or mutual; a recursive inductive has no total \
                 by-value carrier (DG-70 option (c), a pinned runtime handle, is staged later)"
            ),
        ));
    }
    if ind.num_params != 0 || ind.num_indices != 0 || !ind.level_params.is_empty() {
        return Err(refuse(
            decl,
            format!("`{name}` has parameters, indices or universe parameters"),
        ));
    }
    if ind.constructor_names.is_empty() {
        return Err(refuse(
            decl,
            format!("`{name}` is uninhabited; no value of it can cross the boundary"),
        ));
    }
    if ind.constructor_names.len() > MAX_ENUM_VARIANTS {
        return Err(refuse(
            decl,
            format!(
                "`{name}` has {} constructors; the carrier tag is one byte",
                ind.constructor_names.len()
            ),
        ));
    }
    let mut ctors = Vec::with_capacity(ind.constructor_names.len());
    for ctor_name in &ind.constructor_names {
        let Some(ctor) = env.get_constructor(ctor_name) else {
            return Err(refuse(
                decl,
                format!("constructor `{ctor_name}` is not in the environment"),
            ));
        };
        let (field_tys, result) = split_signature(decl, &ctor.type_).map_err(|_| {
            refuse(
                decl,
                format!("constructor `{ctor_name}` has a dependent or implicit field"),
            )
        })?;
        if const_name(&result) != Some(name) || field_tys.len() != ctor.num_fields as usize {
            return Err(refuse(
                decl,
                format!("constructor `{ctor_name}` does not build `{name}` from its fields"),
            ));
        }
        let mut fields = Vec::with_capacity(field_tys.len());
        for (j, fty) in field_tys.iter().enumerate() {
            let scalar = const_name(fty).and_then(CarrierScalar::of_kernel_name);
            let Some(scalar) = scalar else {
                return Err(refuse(
                    decl,
                    format!(
                        "field {j} of `{ctor_name}` is `{fty}`, which is not a carrier \
                         scalar (Bool, UInt8..UInt64, Float)"
                    ),
                ));
            };
            fields.push(scalar);
        }
        ctors.push(CarrierCtor {
            ctor: ctor_name.clone(),
            short: ctor_name
                .last_component()
                .unwrap_or_else(|| ctor_name.to_string()),
            field_tys,
            fields,
        });
    }
    let single = if ctors.len() == 1 { ctors.pop() } else { None };
    if let Some(ctor) = single {
        if ctor.fields.is_empty() {
            return Err(refuse(
                decl,
                format!("`{name}` is a field-less structure; it carries no runtime value"),
            ));
        }
        let field_names = match env.get_structure_field_names(name) {
            Some(names) if names.len() == ctor.fields.len() => names
                .iter()
                .map(|n| n.last_component().unwrap_or_else(|| n.to_string()))
                .collect(),
            _ => (0..ctor.fields.len()).map(|j| j.to_string()).collect(),
        };
        return Ok(CarrierTy::Struct {
            name: name.clone(),
            field_names,
            ctor,
        });
    }
    Ok(CarrierTy::Enum {
        name: name.clone(),
        ctors,
    })
}

/// Plan the requested carrier exports and extend `env` / `decls` with their
/// marshal-in helpers.
///
/// Every export must name a declaration of `decls` with no universe
/// parameters, whose kernel signature is `Π (explicit, non-dependent
/// carrier-typed params), carrier-scalar`. Anything else is refused as
/// [`TrustIrError::NoTotalCarrier`]; nothing is half-planned.
///
/// # Errors
/// [`TrustIrError::NoTotalCarrier`] for an export with no total carrier, or
/// whose helper the kernel refuses (a name collision included).
pub(crate) fn plan_carrier_exports(
    env: &Environment,
    decls: &[Decl],
    exports: &[Name],
) -> Result<CarrierPlan, TrustIrError> {
    let mut env = env.clone();
    let mut out_decls = decls.to_vec();
    let mut planned = Vec::with_capacity(exports.len());
    for source in exports {
        if planned.iter().any(|e: &CarrierExport| &e.source == source) {
            return Err(refuse(source, "requested twice"));
        }
        let Some(decl) = decls.iter().find(|d| &d.name == source) else {
            return Err(refuse(
                source,
                "is not among the compiled declarations, so there is no boxed body to wrap",
            ));
        };
        if !decl.level_params.is_empty() {
            return Err(refuse(source, "is universe-polymorphic"));
        }
        let Some(info) = env.get_const(source) else {
            return Err(refuse(source, "has no kernel constant"));
        };
        if !info.level_params.is_empty() {
            return Err(refuse(source, "is universe-polymorphic"));
        }
        let (domains, codomain) = split_signature(source, &info.type_.clone())?;
        let params = domains
            .iter()
            .map(|d| classify(&env, source, d))
            .collect::<Result<Vec<_>, _>>()?;
        let ret = match classify(&env, source, &codomain)? {
            CarrierTy::Scalar(s) => s,
            CarrierTy::Struct { name, .. } | CarrierTy::Enum { name, .. } => {
                return Err(refuse(
                    source,
                    format!(
                        "its result is `{name}`; a by-value structure or inductive RESULT is \
                         not carried yet (the unmarshalling half of the wrapper is not built)"
                    ),
                ))
            }
        };
        let combos = params.iter().try_fold(1usize, |acc, p| {
            acc.checked_mul(p.arms())
                .filter(|n| *n <= MAX_VARIANT_COMBINATIONS)
        });
        let Some(combos) = combos else {
            return Err(refuse(
                source,
                format!(
                    "its enum parameters expand to more than {MAX_VARIANT_COMBINATIONS} \
                     constructor combinations"
                ),
            ));
        };

        let mut helpers = Vec::with_capacity(combos);
        for k in 0..combos {
            let choice = mixed_radix(k, &params);
            let name = helper_name(source, k);
            let (type_, value) = helper_definition(source, &params, &choice, &codomain)?;
            env.add_decl(Declaration::Definition {
                name: name.clone(),
                level_params: vec![],
                type_,
                value,
                is_reducible: false,
            })
            .map_err(|e| {
                refuse(
                    source,
                    format!("the kernel refused marshal-in helper `{name}`: {e}"),
                )
            })?;
            let helper_info = env
                .get_const(&name)
                .ok_or_else(|| {
                    refuse(
                        source,
                        format!(
                            "marshal-in helper `{name}` is missing after the kernel admitted it"
                        ),
                    )
                })?
                .clone();
            let lowered = crate::to_lcnf::constant_to_decl(&env, &helper_info)
                .map_err(|e| refuse(source, format!("helper `{name}` did not lower: {e}")))?
                .ok_or_else(|| refuse(source, format!("helper `{name}` has no runtime body")))?;
            out_decls.push(lowered);
            helpers.push(CarrierHelper { name, choice });
        }
        planned.push(CarrierExport {
            source: source.clone(),
            symbol: carrier_symbol(source),
            params,
            ret,
            helpers,
        });
    }
    Ok(CarrierPlan {
        env,
        decls: out_decls,
        exports: planned,
    })
}

/// `k` in mixed radix over the parameters' arm counts, first parameter most
/// significant.
fn mixed_radix(mut k: usize, params: &[CarrierTy]) -> Vec<usize> {
    let mut choice = vec![0; params.len()];
    for (i, p) in params.iter().enumerate().rev() {
        let n = p.arms();
        choice[i] = k % n;
        k /= n;
    }
    choice
}

/// The helper's kernel type and value: binders for every scalar the chosen
/// arms carry, in parameter order, and the source applied to the scalars and
/// to the chosen constructors applied to theirs.
fn helper_definition(
    source: &Name,
    params: &[CarrierTy],
    choice: &[usize],
    codomain: &Expr,
) -> Result<(Expr, Expr), TrustIrError> {
    // Binder domains in order (outermost first), and per parameter the range
    // of binder indices it owns.
    let mut domains: Vec<Expr> = Vec::new();
    let mut owned: Vec<(Option<Name>, std::ops::Range<usize>)> = Vec::new();
    for (p, &arm) in params.iter().zip(choice) {
        let start = domains.len();
        match p {
            CarrierTy::Scalar(_) => {
                // The scalar's own type is the parameter's domain; recover it
                // from the scalar (a closed constant of the same name).
                domains.push(scalar_kernel_ty(p));
                owned.push((None, start..domains.len()));
            }
            CarrierTy::Struct { ctor, .. } => {
                domains.extend(ctor.field_tys.iter().cloned());
                owned.push((Some(ctor.ctor.clone()), start..domains.len()));
            }
            CarrierTy::Enum { ctors, .. } => {
                let ctor = &ctors[arm];
                domains.extend(ctor.field_tys.iter().cloned());
                owned.push((Some(ctor.ctor.clone()), start..domains.len()));
            }
        }
    }
    // `bvars[j]` is binder `j` seen from the body: de Bruijn index m - 1 - j.
    let Ok(m) = u32::try_from(domains.len()) else {
        return Err(refuse(
            source,
            format!(
                "its marshal-in helper needs {} binders, more than a de Bruijn index holds",
                domains.len()
            ),
        ));
    };
    let bvars: Vec<Expr> = (0..m).rev().map(Expr::bvar).collect();
    let var = |j: usize| bvars[j].clone();
    let args: Vec<Expr> = owned
        .iter()
        .map(|(ctor, range)| match ctor {
            None => var(range.start),
            Some(ctor) => Expr::apps(Expr::const_(ctor.clone(), vec![]), range.clone().map(var)),
        })
        .collect();
    let mut value = Expr::apps(Expr::const_(source.clone(), vec![]), args);
    let mut type_ = codomain.clone();
    for domain in domains.iter().rev() {
        value = Expr::lam(BinderInfo::Default, domain.clone(), value);
        type_ = Expr::pi(BinderInfo::Default, domain.clone(), type_);
    }
    Ok((type_, value))
}

/// The kernel type constant of a scalar parameter.
fn scalar_kernel_ty(p: &CarrierTy) -> Expr {
    let CarrierTy::Scalar(s) = p else {
        unreachable!("called on a scalar parameter only")
    };
    let name = match s {
        CarrierScalar::Bool => "Bool",
        CarrierScalar::U8 => "UInt8",
        CarrierScalar::U16 => "UInt16",
        CarrierScalar::U32 => "UInt32",
        CarrierScalar::U64 => "UInt64",
        CarrierScalar::F64 => "Float",
    };
    Expr::const_str(name)
}

// ---------------------------------------------------------------------------
// Layout
// ---------------------------------------------------------------------------

fn align_up(x: u64, a: u64) -> u64 {
    x.div_ceil(a) * a
}

/// `#[repr(C)]` layout of a field list: (offsets, size, align).
#[must_use]
pub(crate) fn c_layout(fields: &[CarrierScalar]) -> (Vec<u64>, u64, u64) {
    let mut offsets = Vec::with_capacity(fields.len());
    let mut at = 0u64;
    let mut align = 1u64;
    for f in fields {
        let a = f.size();
        at = align_up(at, a);
        offsets.push(at);
        at += f.size();
        align = align.max(a);
    }
    (offsets, align_up(at, align), align)
}

/// The enum carrier's descriptor: a `u8` tag at offset 0, the payload union at
/// `align_up(1, payload_align)`, each variant laid out `#[repr(C)]` inside it.
/// This is the `#[repr(C, u8)]` layout and trust-ir's canonical tagged union.
#[must_use]
pub(crate) fn enum_layout(ctors: &[Vec<CarrierScalar>]) -> EnumLayoutDescriptor {
    let variants: Vec<(Vec<u64>, u64, u64)> = ctors.iter().map(|f| c_layout(f)).collect();
    let payload_align = variants.iter().map(|v| v.2).max().unwrap_or(1).max(1);
    let payload_size = variants.iter().map(|v| v.1).max().unwrap_or(0);
    let payload_offset = align_up(1, payload_align);
    let align = payload_align.max(1);
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: align_up(payload_offset + payload_size, align),
        align,
        variant_field_offsets: variants
            .into_iter()
            .map(|(offs, _, _)| offs.into_iter().map(|o| payload_offset + o).collect())
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

/// The carrier definitions registered so far, by inductive wire name. The
/// general back end registers no other struct or enum, so ids are assigned
/// densely from 0 here (the validator refuses a collision regardless).
#[derive(Default)]
struct CarrierDefs {
    tys: BTreeMap<String, Ty>,
    structs: u32,
    enums: u32,
}

/// Register (once per inductive) the trust-ir definition of a carrier type.
fn carrier_trust_ir_ty(mb: &mut ModuleBuilder, defs: &mut CarrierDefs, p: &CarrierTy) -> Ty {
    match p {
        CarrierTy::Scalar(s) => s.ty(),
        CarrierTy::Struct {
            name,
            field_names,
            ctor,
        } => {
            let key = wire_name(name);
            if let Some(ty) = defs.tys.get(&key) {
                return ty.clone();
            }
            let (offsets, size, align) = c_layout(&ctor.fields);
            let id = trust_ir::StructId::new(defs.structs);
            defs.structs += 1;
            let sid = mb.add_struct(StructDef {
                id,
                name: key.clone(),
                fields: ctor
                    .fields
                    .iter()
                    .zip(field_names)
                    .zip(offsets)
                    .map(|((f, n), off)| FieldDef {
                        name: n.clone(),
                        ty: f.ty(),
                        offset: Some(off),
                    })
                    .collect(),
                size: Some(size),
                align: Some(align),
                repr: StructRepr::C,
                origin: None,
            });
            let ty = Ty::Struct(sid);
            defs.tys.insert(key, ty.clone());
            ty
        }
        CarrierTy::Enum { name, ctors } => {
            let key = wire_name(name);
            if let Some(ty) = defs.tys.get(&key) {
                return ty.clone();
            }
            let layout = enum_layout(&ctors.iter().map(|c| c.fields.clone()).collect::<Vec<_>>());
            let id = trust_ir::EnumId::new(defs.enums);
            defs.enums += 1;
            let eid = mb.add_enum(EnumDef {
                id,
                name: key.clone(),
                variants: ctors
                    .iter()
                    .map(|c| EnumVariant {
                        name: c.short.clone(),
                        fields: c.fields.iter().map(|f| f.ty()).collect(),
                        field_names: vec![],
                    })
                    .collect(),
                discriminants: vec![],
                repr: Some(EnumTagRepr::U8),
                layout: Some(layout),
                origin: None,
            });
            let ty = Ty::Enum(eid);
            defs.tys.insert(key, ty.clone());
            ty
        }
    }
}

/// Emit one typed wrapper per planned export into `mb`.
///
/// `fn_ids` maps every in-slice declaration to its function; `decls` is the
/// emitted L5IR slice, read to check each helper's lowered signature.
pub(crate) fn emit_carrier_wrappers(
    mb: &mut ModuleBuilder,
    exports: &[CarrierExport],
    decls: &[IRDecl],
    fn_ids: &HashMap<Name, FuncId>,
    span: Option<SourceSpan>,
) -> Result<(), TrustIrError> {
    let mut defs = CarrierDefs::default();
    for export in exports {
        // Resolve and check every helper BEFORE any function builder is live.
        let mut helper_ids = Vec::with_capacity(export.helpers.len());
        for helper in &export.helpers {
            let Some(id) = fn_ids.get(&helper.name) else {
                return Err(refuse(
                    &export.source,
                    format!("marshal-in helper `{}` was not emitted", helper.name),
                ));
            };
            let Some(decl) = decls.iter().find(|d| d.name == helper.name) else {
                return Err(refuse(
                    &export.source,
                    format!(
                        "marshal-in helper `{}` has no lowered declaration",
                        helper.name
                    ),
                ));
            };
            let got: Vec<Ty> = decl.params.iter().map(|(_, t)| lower_ty(t)).collect();
            let want: Vec<Ty> = export
                .params
                .iter()
                .zip(&helper.choice)
                .flat_map(|(p, &arm)| arm_scalars(p, arm))
                .map(CarrierScalar::ty)
                .collect();
            let got_ret = lower_ret_tys(&decl.return_type);
            if got != want || got_ret != vec![export.ret.ty()] {
                return Err(refuse(
                    &export.source,
                    format!(
                        "marshal-in helper `{}` lowered to ({}) -> ({}), not the carrier \
                         scalars ({}) -> ({}); the boundary is refused rather than re-boxed",
                        helper.name,
                        join(&got),
                        join(&got_ret),
                        join(&want),
                        export.ret.ty()
                    ),
                ));
            }
            helper_ids.push(*id);
        }
        let param_tys: Vec<Ty> = export
            .params
            .iter()
            .map(|p| carrier_trust_ir_ty(mb, &mut defs, p))
            .collect();
        let fty = mb.intern_func_type(trust_ir::ty::FuncTy {
            params: param_tys.clone(),
            returns: vec![export.ret.ty()],
            is_vararg: false,
            abi: None,
        });
        let mut fb = mb.function(export.symbol.clone(), fty);
        fb.set_body_gate(BodyGate::Ungated);
        fb.set_display_path(export.source.to_string());
        if let Some(span) = span {
            fb.set_span(span);
        }
        let entry = fb.create_block();
        let params: Vec<ValueId> = param_tys
            .iter()
            .map(|t| fb.add_block_param(entry, t.clone()))
            .collect();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let mut w = Wrapper {
            fb: &mut fb,
            export,
            params: &params,
            helper_ids: &helper_ids,
        };
        w.dispatch(0, 0, Vec::new())?;
        fb.build();
    }
    Ok(())
}

fn join(tys: &[Ty]) -> String {
    tys.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The scalars arm `arm` of parameter `p` passes to a helper.
fn arm_scalars(p: &CarrierTy, arm: usize) -> Vec<CarrierScalar> {
    match p {
        CarrierTy::Scalar(s) => vec![*s],
        CarrierTy::Struct { ctor, .. } => ctor.fields.clone(),
        CarrierTy::Enum { ctors, .. } => ctors[arm].fields.clone(),
    }
}

struct Wrapper<'a, 'b, 'c> {
    fb: &'a mut FunctionBuilder<'b>,
    export: &'c CarrierExport,
    params: &'c [ValueId],
    helper_ids: &'c [FuncId],
}

impl Wrapper<'_, '_, '_> {
    /// Unmarshal parameter `i` onward in the current block; `k` is the
    /// mixed-radix prefix of the arms chosen so far, `args` the scalars.
    fn dispatch(&mut self, i: usize, k: usize, mut args: Vec<ValueId>) -> Result<(), TrustIrError> {
        if i == self.params.len() {
            let result = self.fb.call(self.helper_ids[k], args);
            self.fb.ret(vec![result]);
            return Ok(());
        }
        let v = self.params[i];
        match &self.export.params[i] {
            CarrierTy::Scalar(_) => {
                args.push(v);
                self.dispatch(i + 1, k, args)?;
            }
            CarrierTy::Struct { ctor, .. } => {
                for (j, f) in ctor.fields.iter().enumerate() {
                    let lane = self.lane(j)?;
                    args.push(self.fb.extract_field(f.ty(), v, lane));
                }
                self.dispatch(i + 1, k, args)?;
            }
            CarrierTy::Enum { ctors, .. } => {
                // Lane 0 is the tag at the canonical repr (`u8`); lane j + 1 is
                // field j of the ACTIVE variant, read only under the switch arm
                // that selects it (WS2.2's lane model).
                let tag = self.fb.extract_field(Ty::U8, v, 0);
                let dead: BlockId = self.fb.create_block();
                let arms: Vec<BlockId> = ctors.iter().map(|_| self.fb.create_block()).collect();
                // The tag of variant t is t itself (counted as i128, the
                // constant's own width, so no conversion can fail).
                let cases = (0i128..)
                    .zip(&arms)
                    .map(|(t, &target)| SwitchCase {
                        value: Constant::Int(t),
                        target,
                        args: vec![],
                    })
                    .collect();
                self.fb.switch(tag, cases, dead, vec![]);
                self.fb.switch_to_block(dead);
                self.fb.unreachable();
                for (t, (ctor, &block)) in ctors.iter().zip(&arms).enumerate() {
                    self.fb.switch_to_block(block);
                    let mut arm_args = args.clone();
                    for (j, f) in ctor.fields.iter().enumerate() {
                        let lane = self.lane(j + 1)?;
                        arm_args.push(self.fb.extract_field(f.ty(), v, lane));
                    }
                    let n = ctors.len();
                    self.dispatch(i + 1, k * n + t, arm_args)?;
                }
            }
        }
        // Mixed radix: a scalar or struct parameter has one arm, so `k`
        // passes through unchanged (k * 1 + 0).
        Ok(())
    }

    /// Lane `j` as trust-ir's `u32` lane index; a lane past it is refused.
    fn lane(&self, j: usize) -> Result<u32, TrustIrError> {
        u32::try_from(j).map_err(|_| {
            refuse(
                &self.export.source,
                format!("field lane {j} does not fit a trust-ir lane index"),
            )
        })
    }
}

#[cfg(test)]
#[path = "emit_trust_ir_boundary_tests.rs"]
mod tests;

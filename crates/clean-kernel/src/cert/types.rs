// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type definitions for proof certificates.
//!
//! Contains the core certificate types (`ProofCert`, `DefEqStep`, `CertError`)
//! and their helper display functions.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal, MDataMap};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;

use serde::{Deserialize, Serialize};

/// A proof certificate witnessing a typing derivation.
///
/// The certificate structure mirrors the expression structure but includes
/// all intermediate types needed for verification.
///
/// Certificates are serializable for proof archives and can be verified
/// independently by a certificate verifier.
#[must_use = "proof certificates should be verified or stored"]
pub enum ProofCert {
    /// Certificate for Sort(l) : Sort(succ(l))
    Sort {
        /// Universe level of the Sort
        level: Level,
    },

    /// Certificate for `BVar` (de Bruijn index)
    /// Includes the expected type from context
    BVar {
        /// De Bruijn index
        idx: u32,
        /// Expected type from the typing context
        expected_type: Box<Expr>,
    },

    /// Certificate for `FVar` (free variable)
    /// Includes the type from local context
    FVar {
        /// Free variable identifier
        id: FVarId,
        /// Type of the free variable from local context
        type_: Box<Expr>,
    },

    /// Certificate for Const (constant reference)
    /// Includes instantiated type
    Const {
        /// Constant name
        name: Name,
        /// Universe level instantiation
        levels: Vec<Level>,
        /// Instantiated type of the constant
        type_: Box<Expr>,
    },

    /// Certificate for App: f a : B[a/x]
    /// Records: function cert, arg cert, and the instantiated result type
    App {
        /// Certificate for the function expression
        fn_cert: Box<ProofCert>,
        /// The Pi type of the function
        fn_type: Box<Expr>,
        /// Certificate for the argument expression
        arg_cert: Box<ProofCert>,
        /// Result type after substitution: B[a/x]
        result_type: Box<Expr>,
    },

    /// Certificate for Lam: λ (x : A). b : (x : A) → B
    /// Records: arg type cert, body cert (in extended context)
    Lam {
        /// Binder information (implicit, explicit, etc.)
        binder_info: BinderInfo,
        /// Certificate proving A : Sort(l)
        arg_type_cert: Box<ProofCert>,
        /// Certificate proving b : B in extended context
        body_cert: Box<ProofCert>,
        /// The resulting Pi type
        result_type: Box<Expr>,
    },

    /// Certificate for Pi: (x : A) → B : Sort(imax(l1, l2))
    Pi {
        /// Binder information (implicit, explicit, etc.)
        binder_info: BinderInfo,
        /// Certificate proving A : Sort(l1)
        arg_type_cert: Box<ProofCert>,
        /// Universe level l1 of the domain
        arg_level: Level,
        /// Certificate proving B : Sort(l2) in extended context
        body_type_cert: Box<ProofCert>,
        /// Universe level l2 of the codomain
        body_level: Level,
    },

    /// Certificate for Let: let x : A := v in b : B[v/x]
    Let {
        /// Certificate proving A : Sort(l)
        type_cert: Box<ProofCert>,
        /// Certificate proving v : A
        value_cert: Box<ProofCert>,
        /// Certificate proving b : B in extended context
        body_cert: Box<ProofCert>,
        /// Result type after substitution: B[v/x]
        result_type: Box<Expr>,
    },

    /// Certificate for Literal values
    Lit {
        /// The literal value
        lit: Literal,
        /// Type of the literal (Nat or String)
        type_: Box<Expr>,
    },

    /// Certificate for definitional equality check
    /// Used when checking e : T reduces to checking e : T' where T ≡ T'
    DefEq {
        /// Certificate for the inner expression
        inner: Box<ProofCert>,
        /// Expected type from context
        expected_type: Box<Expr>,
        /// Actual inferred type
        actual_type: Box<Expr>,
        /// Steps needed to show equivalence (for debugging/verification)
        eq_steps: Vec<DefEqStep>,
    },

    /// Certificate for `MData` (metadata wrapper)
    /// `MData` is transparent - the type is the type of the inner expression
    MData {
        /// Metadata map attached to the expression
        metadata: MDataMap,
        /// Certificate for the inner expression
        inner_cert: Box<ProofCert>,
        /// Result type (same as inner expression's type)
        result_type: Box<Expr>,
    },

    /// Certificate for Proj (projection from structure)
    /// Records the struct name, field index, and the type of the projected field
    Proj {
        /// Name of the structure type
        struct_name: Name,
        /// Field index in the structure
        idx: u32,
        /// Certificate for the expression being projected
        expr_cert: Box<ProofCert>,
        /// Type of the expression being projected
        expr_type: Box<Expr>,
        /// Type of the projected field
        field_type: Box<Expr>,
    },

    // ════════════════════════════════════════════════════════════════════════
    // Mode-specific certificates (Cubical, Classical, SetTheoretic)
    // ════════════════════════════════════════════════════════════════════════
    /// Certificate for CubicalInterval : Type (Sort 1)
    /// The interval type I has two elements (i0, i1) in Cubical type theory
    CubicalInterval,

    /// Certificate for CubicalI0 : I and CubicalI1 : I
    /// The endpoints of the interval
    CubicalEndpoint {
        /// true for I1, false for I0
        is_one: bool,
    },

    /// Certificate for CubicalPath { ty, left, right } : Sort(l)
    /// Path A a b is a type when A : Sort(l), a : A, b : A
    CubicalPath {
        /// Certificate for the type family A
        ty_cert: Box<ProofCert>,
        /// Universe level of the type family
        ty_level: Level,
        /// Certificate for the left endpoint a
        left_cert: Box<ProofCert>,
        /// Certificate for the right endpoint b
        right_cert: Box<ProofCert>,
    },

    /// Certificate for CubicalPathLam { body } : Path A (body[0/i]) (body[1/i])
    /// Path abstraction `<i> e` where i : I
    CubicalPathLam {
        /// Certificate for the path body expression
        body_cert: Box<ProofCert>,
        /// The type of the body (before abstracting interval var)
        body_type: Box<Expr>,
        /// The resulting Path type
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalPathApp { path, arg } : A
    /// Path application p @ i where p : Path A a b and i : I
    CubicalPathApp {
        /// Certificate for the path expression being applied
        path_cert: Box<ProofCert>,
        /// Certificate for the interval argument
        arg_cert: Box<ProofCert>,
        /// The Path type of the path expression
        path_type: Box<Expr>,
        /// The result type (the type parameter A from Path A a b)
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalHComp { ty, phi, u, base } : ty
    /// Homogeneous composition in Cubical type theory
    CubicalHComp {
        /// Certificate for the type parameter
        ty_cert: Box<ProofCert>,
        /// Certificate for the face formula φ : F
        phi_cert: Box<ProofCert>,
        /// Certificate for the partial element u : (i : I) → Partial φ A
        u_cert: Box<ProofCert>,
        /// Certificate for the base element a₀ : A
        base_cert: Box<ProofCert>,
        /// The result type A
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalTransp { ty, phi, base } : ty[1/i]
    /// Transport along a path in Cubical type theory
    CubicalTransp {
        /// Certificate for the type family A : I → Type
        ty_cert: Box<ProofCert>,
        /// Certificate for the face formula φ : F
        phi_cert: Box<ProofCert>,
        /// Certificate for the base element a₀ : A(0)
        base_cert: Box<ProofCert>,
        /// The result type A(1)
        result_type: Box<Expr>,
    },

    /// Certificate for CubicalCoe { ty, r, s, base } : ty s
    /// Generalized coercion `coe^{r→s}` in Cubical type theory
    CubicalCoe {
        /// Certificate for the type-family line A : I → Sort u
        ty_cert: Box<ProofCert>,
        /// Certificate for the source endpoint r : I
        r_cert: Box<ProofCert>,
        /// Certificate for the target endpoint s : I
        s_cert: Box<ProofCert>,
        /// Certificate for the base element base : A r
        base_cert: Box<ProofCert>,
        /// The result type A s
        result_type: Box<Expr>,
    },

    /// Certificate for ZFCSet expressions : Set
    /// Various set constructions in ZFC
    ZFCSet {
        /// The specific set construction
        kind: ZFCSetCertKind,
        /// Always Set (the type of sets)
        result_type: Box<Expr>,
    },

    /// Certificate for ZFCMem { elem, set } : Prop
    /// Set membership ∈
    ZFCMem {
        /// Certificate for the element expression
        elem_cert: Box<ProofCert>,
        /// Certificate for the set expression
        set_cert: Box<ProofCert>,
    },

    /// Certificate for ZFCComprehension { var_ty, pred } : Set
    /// Set comprehension { x : A | P(x) }
    ZFCComprehension {
        /// Certificate for the variable type A
        var_ty_cert: Box<ProofCert>,
        /// Certificate for the predicate P : A → Prop
        pred_cert: Box<ProofCert>,
        /// The result type Set
        result_type: Box<Expr>,
    },

    // ════════════════════════════════════════════════════════════════════════
    // Impredicative mode certificates
    // ════════════════════════════════════════════════════════════════════════
    /// Certificate for SProp : Type 1
    /// SProp is the sort of strict propositions (always proof-irrelevant)
    SProp,

    /// Certificate for Squash A : SProp (when A : Sort u)
    /// Squash (propositional truncation) - all proofs are definitionally equal
    Squash {
        /// Certificate for the inner type being squashed
        inner_cert: Box<ProofCert>,
    },
}

/// Bounded diagnostic representation.
///
/// Certificate rejection is an attacker-reachable path. Printing a complete
/// recursive certificate there would consume O(depth) native stack and
/// unbounded output, so Debug reports scalar metadata and one child-rule level.
impl std::fmt::Debug for ProofCert {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sort { level } => f.debug_struct("Sort").field("level", level).finish(),
            Self::BVar { idx, expected_type } => f
                .debug_struct("BVar")
                .field("idx", idx)
                .field("expected_type", &ExprRule(expected_type))
                .finish(),
            Self::FVar { id, type_ } => f
                .debug_struct("FVar")
                .field("id", id)
                .field("type_", &ExprRule(type_))
                .finish(),
            Self::Const {
                name,
                levels,
                type_,
            } => f
                .debug_struct("Const")
                .field("name", name)
                .field("levels", &LevelListSummary(levels))
                .field("type_", &ExprRule(type_))
                .finish(),
            Self::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => f
                .debug_struct("App")
                .field("fn_cert", &CertRule(fn_cert))
                .field("fn_type", &ExprRule(fn_type))
                .field("arg_cert", &CertRule(arg_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::Lam {
                binder_info,
                arg_type_cert,
                body_cert,
                result_type,
            } => f
                .debug_struct("Lam")
                .field("binder_info", binder_info)
                .field("arg_type_cert", &CertRule(arg_type_cert))
                .field("body_cert", &CertRule(body_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::Pi {
                binder_info,
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
            } => f
                .debug_struct("Pi")
                .field("binder_info", binder_info)
                .field("arg_type_cert", &CertRule(arg_type_cert))
                .field("arg_level", arg_level)
                .field("body_type_cert", &CertRule(body_type_cert))
                .field("body_level", body_level)
                .finish(),
            Self::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => f
                .debug_struct("Let")
                .field("type_cert", &CertRule(type_cert))
                .field("value_cert", &CertRule(value_cert))
                .field("body_cert", &CertRule(body_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::Lit { lit, type_ } => f
                .debug_struct("Lit")
                .field("lit", &LiteralSummary(lit))
                .field("type_", &ExprRule(type_))
                .finish(),
            Self::DefEq {
                inner,
                expected_type,
                actual_type,
                eq_steps,
            } => f
                .debug_struct("DefEq")
                .field("inner", &CertRule(inner))
                .field("expected_type", &ExprRule(expected_type))
                .field("actual_type", &ExprRule(actual_type))
                .field("eq_steps", &DefEqListSummary(eq_steps))
                .finish(),
            Self::MData {
                metadata,
                inner_cert,
                result_type,
            } => f
                .debug_struct("MData")
                .field("metadata", &MetadataSummary(metadata))
                .field("inner_cert", &CertRule(inner_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::Proj {
                struct_name,
                idx,
                expr_cert,
                expr_type,
                field_type,
            } => f
                .debug_struct("Proj")
                .field("struct_name", struct_name)
                .field("idx", idx)
                .field("expr_cert", &CertRule(expr_cert))
                .field("expr_type", &ExprRule(expr_type))
                .field("field_type", &ExprRule(field_type))
                .finish(),
            Self::CubicalInterval => f.write_str("CubicalInterval"),
            Self::CubicalEndpoint { is_one } => f
                .debug_struct("CubicalEndpoint")
                .field("is_one", is_one)
                .finish(),
            Self::CubicalPath {
                ty_cert,
                ty_level,
                left_cert,
                right_cert,
            } => f
                .debug_struct("CubicalPath")
                .field("ty_cert", &CertRule(ty_cert))
                .field("ty_level", ty_level)
                .field("left_cert", &CertRule(left_cert))
                .field("right_cert", &CertRule(right_cert))
                .finish(),
            Self::CubicalPathLam {
                body_cert,
                body_type,
                result_type,
            } => f
                .debug_struct("CubicalPathLam")
                .field("body_cert", &CertRule(body_cert))
                .field("body_type", &ExprRule(body_type))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::CubicalPathApp {
                path_cert,
                arg_cert,
                path_type,
                result_type,
            } => f
                .debug_struct("CubicalPathApp")
                .field("path_cert", &CertRule(path_cert))
                .field("arg_cert", &CertRule(arg_cert))
                .field("path_type", &ExprRule(path_type))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                result_type,
            } => f
                .debug_struct("CubicalHComp")
                .field("ty_cert", &CertRule(ty_cert))
                .field("phi_cert", &CertRule(phi_cert))
                .field("u_cert", &CertRule(u_cert))
                .field("base_cert", &CertRule(base_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::CubicalTransp {
                ty_cert,
                phi_cert,
                base_cert,
                result_type,
            } => f
                .debug_struct("CubicalTransp")
                .field("ty_cert", &CertRule(ty_cert))
                .field("phi_cert", &CertRule(phi_cert))
                .field("base_cert", &CertRule(base_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::CubicalCoe {
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                result_type,
            } => f
                .debug_struct("CubicalCoe")
                .field("ty_cert", &CertRule(ty_cert))
                .field("r_cert", &CertRule(r_cert))
                .field("s_cert", &CertRule(s_cert))
                .field("base_cert", &CertRule(base_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::ZFCSet { kind, result_type } => f
                .debug_struct("ZFCSet")
                .field("kind", &ZfcRule(kind))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::ZFCMem {
                elem_cert,
                set_cert,
            } => f
                .debug_struct("ZFCMem")
                .field("elem_cert", &CertRule(elem_cert))
                .field("set_cert", &CertRule(set_cert))
                .finish(),
            Self::ZFCComprehension {
                var_ty_cert,
                pred_cert,
                result_type,
            } => f
                .debug_struct("ZFCComprehension")
                .field("var_ty_cert", &CertRule(var_ty_cert))
                .field("pred_cert", &CertRule(pred_cert))
                .field("result_type", &ExprRule(result_type))
                .finish(),
            Self::SProp => f.write_str("SProp"),
            Self::Squash { inner_cert } => f
                .debug_struct("Squash")
                .field("inner_cert", &CertRule(inner_cert))
                .finish(),
        }
    }
}

struct CertRule<'a>(&'a ProofCert);

impl std::fmt::Debug for CertRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(cert_rule(self.0))
    }
}

fn cert_rule(cert: &ProofCert) -> &'static str {
    match cert {
        ProofCert::Sort { .. } => "Sort",
        ProofCert::BVar { .. } => "BVar",
        ProofCert::FVar { .. } => "FVar",
        ProofCert::Const { .. } => "Const",
        ProofCert::App { .. } => "App",
        ProofCert::Lam { .. } => "Lam",
        ProofCert::Pi { .. } => "Pi",
        ProofCert::Let { .. } => "Let",
        ProofCert::Lit { .. } => "Lit",
        ProofCert::DefEq { .. } => "DefEq",
        ProofCert::MData { .. } => "MData",
        ProofCert::Proj { .. } => "Proj",
        ProofCert::CubicalInterval => "CubicalInterval",
        ProofCert::CubicalEndpoint { .. } => "CubicalEndpoint",
        ProofCert::CubicalPath { .. } => "CubicalPath",
        ProofCert::CubicalPathLam { .. } => "CubicalPathLam",
        ProofCert::CubicalPathApp { .. } => "CubicalPathApp",
        ProofCert::CubicalHComp { .. } => "CubicalHComp",
        ProofCert::CubicalTransp { .. } => "CubicalTransp",
        ProofCert::CubicalCoe { .. } => "CubicalCoe",
        ProofCert::ZFCSet { .. } => "ZFCSet",
        ProofCert::ZFCMem { .. } => "ZFCMem",
        ProofCert::ZFCComprehension { .. } => "ZFCComprehension",
        ProofCert::SProp => "SProp",
        ProofCert::Squash { .. } => "Squash",
    }
}

struct ExprRule<'a>(&'a Expr);

impl std::fmt::Debug for ExprRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match &self.0.kind {
            ExprKind::BVar(_) => "BVar",
            ExprKind::FVar(_) => "FVar",
            ExprKind::Sort(_) => "Sort",
            ExprKind::Const(_, _) => "Const",
            ExprKind::App(_, _) => "App",
            ExprKind::Lam(_, _, _) => "Lam",
            ExprKind::Pi(_, _, _) => "Pi",
            ExprKind::Let(_, _, _, _, _) => "Let",
            ExprKind::Lit(_) => "Lit",
            ExprKind::Proj(_, _, _) => "Proj",
            ExprKind::MData(_, _) => "MData",
            ExprKind::CubicalInterval => "CubicalInterval",
            ExprKind::CubicalI0 => "CubicalI0",
            ExprKind::CubicalI1 => "CubicalI1",
            ExprKind::CubicalPath { .. } => "CubicalPath",
            ExprKind::CubicalPathLam { .. } => "CubicalPathLam",
            ExprKind::CubicalPathApp { .. } => "CubicalPathApp",
            ExprKind::CubicalHComp { .. } => "CubicalHComp",
            ExprKind::CubicalTransp { .. } => "CubicalTransp",
            ExprKind::CubicalCoe { .. } => "CubicalCoe",
            ExprKind::ZFCSet(_) => "ZFCSet",
            ExprKind::ZFCMem { .. } => "ZFCMem",
            ExprKind::ZFCComprehension { .. } => "ZFCComprehension",
            ExprKind::SProp => "SProp",
            ExprKind::Squash(_) => "Squash",
        })
    }
}

struct LevelListSummary<'a>(&'a [Level]);

impl std::fmt::Debug for LevelListSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut summary = f.debug_struct("LevelList");
        summary.field("len", &self.0.len());
        if let Some(first) = self.0.first() {
            summary.field("first", first);
        }
        summary.finish()
    }
}

struct LiteralSummary<'a>(&'a Literal);

impl std::fmt::Debug for LiteralSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Literal::Nat(value) => match value.to_u64() {
                Some(value) => f.debug_tuple("Nat").field(&value).finish(),
                None => f.write_str("Nat(<big>)"),
            },
            Literal::String(value) => f
                .debug_struct("String")
                .field("len", &value.len())
                .field("prefix", &BoundedStr(value))
                .finish(),
        }
    }
}

struct BoundedStr<'a>(&'a str);

impl std::fmt::Debug for BoundedStr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const MAX_CHARS: usize = 32;
        let end = self
            .0
            .char_indices()
            .nth(MAX_CHARS)
            .map_or(self.0.len(), |(index, _)| index);
        std::fmt::Debug::fmt(&&self.0[..end], f)?;
        if end != self.0.len() {
            f.write_str("…")?;
        }
        Ok(())
    }
}

struct DefEqListSummary<'a>(&'a [DefEqStep]);

impl std::fmt::Debug for DefEqListSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut summary = f.debug_struct("DefEqSteps");
        summary.field("len", &self.0.len());
        if let Some(first) = self.0.first() {
            summary.field("first", &DefEqRule(first));
        }
        summary.finish()
    }
}

struct DefEqRule<'a>(&'a DefEqStep);

impl std::fmt::Debug for DefEqRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(def_eq_rule(self.0))
    }
}

fn def_eq_rule(step: &DefEqStep) -> &'static str {
    match step {
        DefEqStep::Refl => "Refl",
        DefEqStep::Symm(_) => "Symm",
        DefEqStep::Trans(_, _) => "Trans",
        DefEqStep::Beta => "Beta",
        DefEqStep::Delta(_) => "Delta",
        DefEqStep::Zeta => "Zeta",
        DefEqStep::Iota => "Iota",
        DefEqStep::Struct(_, _) => "Struct",
    }
}

struct MetadataSummary<'a>(&'a MDataMap);

impl std::fmt::Debug for MetadataSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut summary = f.debug_struct("Metadata");
        summary.field("len", &self.0.len());
        if let Some((name, value)) = self.0.first() {
            summary.field("first_name", name);
            summary.field("first_value_kind", &metadata_value_rule(value));
            summary.field("first_value", &MetadataValueSummary(value));
        }
        summary.finish()
    }
}

struct MetadataValueSummary<'a>(&'a crate::expr::MDataValue);

impl std::fmt::Debug for MetadataValueSummary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            crate::expr::MDataValue::Bool(value) => std::fmt::Debug::fmt(value, f),
            crate::expr::MDataValue::Nat(value) => std::fmt::Debug::fmt(value, f),
            crate::expr::MDataValue::String(value) => f
                .debug_struct("String")
                .field("len", &value.len())
                .field("prefix", &BoundedStr(value))
                .finish(),
            crate::expr::MDataValue::Name(value) => std::fmt::Debug::fmt(value, f),
        }
    }
}

fn metadata_value_rule(value: &crate::expr::MDataValue) -> &'static str {
    match value {
        crate::expr::MDataValue::Bool(_) => "Bool",
        crate::expr::MDataValue::Nat(_) => "Nat",
        crate::expr::MDataValue::String(_) => "String",
        crate::expr::MDataValue::Name(_) => "Name",
    }
}

struct ZfcRule<'a>(&'a ZFCSetCertKind);

impl std::fmt::Debug for ZfcRule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.0 {
            ZFCSetCertKind::Empty => "Empty",
            ZFCSetCertKind::Singleton(_) => "Singleton",
            ZFCSetCertKind::Pair(_, _) => "Pair",
            ZFCSetCertKind::Union(_) => "Union",
            ZFCSetCertKind::PowerSet(_) => "PowerSet",
            ZFCSetCertKind::Separation { .. } => "Separation",
            ZFCSetCertKind::Replacement { .. } => "Replacement",
            ZFCSetCertKind::Infinity => "Infinity",
            ZFCSetCertKind::Choice(_) => "Choice",
        })
    }
}

// Generic wire mirrors preserve the exact derived serde representation while
// allowing recursive certificate edges to call the manual, stack-guarded
// implementations below. Box and references are both serde-transparent.
#[derive(Serialize, Deserialize)]
#[serde(rename = "ProofCert")]
enum ProofCertWire<C, E, L, LS, N, Li, M, D, Z> {
    Sort {
        level: L,
    },
    BVar {
        idx: u32,
        expected_type: E,
    },
    FVar {
        id: FVarId,
        type_: E,
    },
    Const {
        name: N,
        levels: LS,
        type_: E,
    },
    App {
        fn_cert: C,
        fn_type: E,
        arg_cert: C,
        result_type: E,
    },
    Lam {
        binder_info: BinderInfo,
        arg_type_cert: C,
        body_cert: C,
        result_type: E,
    },
    Pi {
        binder_info: BinderInfo,
        arg_type_cert: C,
        arg_level: L,
        body_type_cert: C,
        body_level: L,
    },
    Let {
        type_cert: C,
        value_cert: C,
        body_cert: C,
        result_type: E,
    },
    Lit {
        lit: Li,
        type_: E,
    },
    DefEq {
        inner: C,
        expected_type: E,
        actual_type: E,
        eq_steps: D,
    },
    MData {
        metadata: M,
        inner_cert: C,
        result_type: E,
    },
    Proj {
        struct_name: N,
        idx: u32,
        expr_cert: C,
        expr_type: E,
        field_type: E,
    },
    CubicalInterval,
    CubicalEndpoint {
        is_one: bool,
    },
    CubicalPath {
        ty_cert: C,
        ty_level: L,
        left_cert: C,
        right_cert: C,
    },
    CubicalPathLam {
        body_cert: C,
        body_type: E,
        result_type: E,
    },
    CubicalPathApp {
        path_cert: C,
        arg_cert: C,
        path_type: E,
        result_type: E,
    },
    CubicalHComp {
        ty_cert: C,
        phi_cert: C,
        u_cert: C,
        base_cert: C,
        result_type: E,
    },
    CubicalTransp {
        ty_cert: C,
        phi_cert: C,
        base_cert: C,
        result_type: E,
    },
    CubicalCoe {
        ty_cert: C,
        r_cert: C,
        s_cert: C,
        base_cert: C,
        result_type: E,
    },
    ZFCSet {
        kind: Z,
        result_type: E,
    },
    ZFCMem {
        elem_cert: C,
        set_cert: C,
    },
    ZFCComprehension {
        var_ty_cert: C,
        pred_cert: C,
        result_type: E,
    },
    SProp,
    Squash {
        inner_cert: C,
    },
}

type BorrowedProofCertWire<'a> = ProofCertWire<
    &'a ProofCert,
    &'a Expr,
    &'a Level,
    &'a Vec<Level>,
    &'a Name,
    &'a Literal,
    &'a MDataMap,
    &'a Vec<DefEqStep>,
    &'a ZFCSetCertKind,
>;

type OwnedProofCertWire = ProofCertWire<
    Box<ProofCert>,
    Box<Expr>,
    Level,
    Vec<Level>,
    Name,
    Literal,
    MDataMap,
    Vec<DefEqStep>,
    ZFCSetCertKind,
>;

fn proof_cert_wire(cert: &ProofCert) -> BorrowedProofCertWire<'_> {
    match cert {
        ProofCert::Sort { level } => ProofCertWire::Sort { level },
        ProofCert::BVar { idx, expected_type } => ProofCertWire::BVar {
            idx: *idx,
            expected_type,
        },
        ProofCert::FVar { id, type_ } => ProofCertWire::FVar { id: *id, type_ },
        ProofCert::Const {
            name,
            levels,
            type_,
        } => ProofCertWire::Const {
            name,
            levels,
            type_,
        },
        ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => ProofCertWire::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        },
        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => ProofCertWire::Lam {
            binder_info: *binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        },
        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => ProofCertWire::Pi {
            binder_info: *binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        },
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => ProofCertWire::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        },
        ProofCert::Lit { lit, type_ } => ProofCertWire::Lit { lit, type_ },
        ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => ProofCertWire::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        },
        ProofCert::MData {
            metadata,
            inner_cert,
            result_type,
        } => ProofCertWire::MData {
            metadata,
            inner_cert,
            result_type,
        },
        ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => ProofCertWire::Proj {
            struct_name,
            idx: *idx,
            expr_cert,
            expr_type,
            field_type,
        },
        ProofCert::CubicalInterval => ProofCertWire::CubicalInterval,
        ProofCert::CubicalEndpoint { is_one } => ProofCertWire::CubicalEndpoint { is_one: *is_one },
        ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => ProofCertWire::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        },
        ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => ProofCertWire::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        },
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => ProofCertWire::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        },
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => ProofCertWire::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        },
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => ProofCertWire::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        },
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => ProofCertWire::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        },
        ProofCert::ZFCSet { kind, result_type } => ProofCertWire::ZFCSet { kind, result_type },
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => ProofCertWire::ZFCMem {
            elem_cert,
            set_cert,
        },
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => ProofCertWire::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        },
        ProofCert::SProp => ProofCertWire::SProp,
        ProofCert::Squash { inner_cert } => ProofCertWire::Squash { inner_cert },
    }
}

fn proof_cert_from_wire(wire: OwnedProofCertWire) -> ProofCert {
    match wire {
        ProofCertWire::Sort { level } => ProofCert::Sort { level },
        ProofCertWire::BVar { idx, expected_type } => ProofCert::BVar { idx, expected_type },
        ProofCertWire::FVar { id, type_ } => ProofCert::FVar { id, type_ },
        ProofCertWire::Const {
            name,
            levels,
            type_,
        } => ProofCert::Const {
            name,
            levels,
            type_,
        },
        ProofCertWire::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        },
        ProofCertWire::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        },
        ProofCertWire::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        },
        ProofCertWire::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        },
        ProofCertWire::Lit { lit, type_ } => ProofCert::Lit { lit, type_ },
        ProofCertWire::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        },
        ProofCertWire::MData {
            metadata,
            inner_cert,
            result_type,
        } => ProofCert::MData {
            metadata,
            inner_cert,
            result_type,
        },
        ProofCertWire::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        },
        ProofCertWire::CubicalInterval => ProofCert::CubicalInterval,
        ProofCertWire::CubicalEndpoint { is_one } => ProofCert::CubicalEndpoint { is_one },
        ProofCertWire::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        },
        ProofCertWire::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        },
        ProofCertWire::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        },
        ProofCertWire::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        },
        ProofCertWire::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        },
        ProofCertWire::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        },
        ProofCertWire::ZFCSet { kind, result_type } => ProofCert::ZFCSet { kind, result_type },
        ProofCertWire::ZFCMem {
            elem_cert,
            set_cert,
        } => ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        },
        ProofCertWire::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        },
        ProofCertWire::SProp => ProofCert::SProp,
        ProofCertWire::Squash { inner_cert } => ProofCert::Squash { inner_cert },
    }
}

impl Serialize for ProofCert {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        crate::expr::stack_safe(|| proof_cert_wire(self).serialize(serializer))
    }
}

impl<'de> Deserialize<'de> for ProofCert {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let _decode_node = crate::serde_budget::enter_decode_node::<D::Error>("proof certificate")?;
        crate::expr::stack_safe(|| {
            OwnedProofCertWire::deserialize(deserializer).map(proof_cert_from_wire)
        })
    }
}

// Do not derive `Clone` for this recursive certificate tree. A certificate can
// be cloned while type inference is already deep in a protected stack segment
// (notably by the Arc-identity memo), and the derived implementation performs
// its whole recursive descent without another `stack_safe` boundary. On the
// default Rust test-thread stack that can cross the guard page and abort the
// entire process. Every recursive child clone re-enters this implementation, so
// guarding here keeps both direct clones and all existing call sites stack-safe.
impl Clone for ProofCert {
    fn clone(&self) -> Self {
        crate::expr::stack_safe(|| match self {
            Self::Sort { level } => Self::Sort {
                level: level.clone(),
            },
            Self::BVar { idx, expected_type } => Self::BVar {
                idx: *idx,
                expected_type: expected_type.clone(),
            },
            Self::FVar { id, type_ } => Self::FVar {
                id: *id,
                type_: type_.clone(),
            },
            Self::Const {
                name,
                levels,
                type_,
            } => Self::Const {
                name: name.clone(),
                levels: levels.clone(),
                type_: type_.clone(),
            },
            Self::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => Self::App {
                fn_cert: fn_cert.clone(),
                fn_type: fn_type.clone(),
                arg_cert: arg_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::Lam {
                binder_info,
                arg_type_cert,
                body_cert,
                result_type,
            } => Self::Lam {
                binder_info: *binder_info,
                arg_type_cert: arg_type_cert.clone(),
                body_cert: body_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::Pi {
                binder_info,
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
            } => Self::Pi {
                binder_info: *binder_info,
                arg_type_cert: arg_type_cert.clone(),
                arg_level: arg_level.clone(),
                body_type_cert: body_type_cert.clone(),
                body_level: body_level.clone(),
            },
            Self::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => Self::Let {
                type_cert: type_cert.clone(),
                value_cert: value_cert.clone(),
                body_cert: body_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::Lit { lit, type_ } => Self::Lit {
                lit: lit.clone(),
                type_: type_.clone(),
            },
            Self::DefEq {
                inner,
                expected_type,
                actual_type,
                eq_steps,
            } => Self::DefEq {
                inner: inner.clone(),
                expected_type: expected_type.clone(),
                actual_type: actual_type.clone(),
                eq_steps: eq_steps.clone(),
            },
            Self::MData {
                metadata,
                inner_cert,
                result_type,
            } => Self::MData {
                metadata: metadata.clone(),
                inner_cert: inner_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::Proj {
                struct_name,
                idx,
                expr_cert,
                expr_type,
                field_type,
            } => Self::Proj {
                struct_name: struct_name.clone(),
                idx: *idx,
                expr_cert: expr_cert.clone(),
                expr_type: expr_type.clone(),
                field_type: field_type.clone(),
            },
            Self::CubicalInterval => Self::CubicalInterval,
            Self::CubicalEndpoint { is_one } => Self::CubicalEndpoint { is_one: *is_one },
            Self::CubicalPath {
                ty_cert,
                ty_level,
                left_cert,
                right_cert,
            } => Self::CubicalPath {
                ty_cert: ty_cert.clone(),
                ty_level: ty_level.clone(),
                left_cert: left_cert.clone(),
                right_cert: right_cert.clone(),
            },
            Self::CubicalPathLam {
                body_cert,
                body_type,
                result_type,
            } => Self::CubicalPathLam {
                body_cert: body_cert.clone(),
                body_type: body_type.clone(),
                result_type: result_type.clone(),
            },
            Self::CubicalPathApp {
                path_cert,
                arg_cert,
                path_type,
                result_type,
            } => Self::CubicalPathApp {
                path_cert: path_cert.clone(),
                arg_cert: arg_cert.clone(),
                path_type: path_type.clone(),
                result_type: result_type.clone(),
            },
            Self::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                result_type,
            } => Self::CubicalHComp {
                ty_cert: ty_cert.clone(),
                phi_cert: phi_cert.clone(),
                u_cert: u_cert.clone(),
                base_cert: base_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::CubicalTransp {
                ty_cert,
                phi_cert,
                base_cert,
                result_type,
            } => Self::CubicalTransp {
                ty_cert: ty_cert.clone(),
                phi_cert: phi_cert.clone(),
                base_cert: base_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::CubicalCoe {
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                result_type,
            } => Self::CubicalCoe {
                ty_cert: ty_cert.clone(),
                r_cert: r_cert.clone(),
                s_cert: s_cert.clone(),
                base_cert: base_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::ZFCSet { kind, result_type } => Self::ZFCSet {
                kind: kind.clone(),
                result_type: result_type.clone(),
            },
            Self::ZFCMem {
                elem_cert,
                set_cert,
            } => Self::ZFCMem {
                elem_cert: elem_cert.clone(),
                set_cert: set_cert.clone(),
            },
            Self::ZFCComprehension {
                var_ty_cert,
                pred_cert,
                result_type,
            } => Self::ZFCComprehension {
                var_ty_cert: var_ty_cert.clone(),
                pred_cert: pred_cert.clone(),
                result_type: result_type.clone(),
            },
            Self::SProp => Self::SProp,
            Self::Squash { inner_cert } => Self::Squash {
                inner_cert: inner_cert.clone(),
            },
        })
    }
}

impl PartialEq for ProofCert {
    fn eq(&self, other: &Self) -> bool {
        crate::expr::stack_safe(|| match (self, other) {
            (Self::Sort { level: left }, Self::Sort { level: right }) => left == right,
            (
                Self::BVar {
                    idx: li,
                    expected_type: lt,
                },
                Self::BVar {
                    idx: ri,
                    expected_type: rt,
                },
            ) => li == ri && lt == rt,
            (Self::FVar { id: li, type_: lt }, Self::FVar { id: ri, type_: rt }) => {
                li == ri && lt == rt
            }
            (
                Self::Const {
                    name: ln,
                    levels: ll,
                    type_: lt,
                },
                Self::Const {
                    name: rn,
                    levels: rl,
                    type_: rt,
                },
            ) => ln == rn && ll == rl && lt == rt,
            (
                Self::App {
                    fn_cert: lf,
                    fn_type: lft,
                    arg_cert: la,
                    result_type: lr,
                },
                Self::App {
                    fn_cert: rf,
                    fn_type: rft,
                    arg_cert: ra,
                    result_type: rr,
                },
            ) => lf == rf && lft == rft && la == ra && lr == rr,
            (
                Self::Lam {
                    binder_info: lbi,
                    arg_type_cert: la,
                    body_cert: lb,
                    result_type: lr,
                },
                Self::Lam {
                    binder_info: rbi,
                    arg_type_cert: ra,
                    body_cert: rb,
                    result_type: rr,
                },
            ) => lbi == rbi && la == ra && lb == rb && lr == rr,
            (
                Self::Pi {
                    binder_info: lbi,
                    arg_type_cert: la,
                    arg_level: lal,
                    body_type_cert: lb,
                    body_level: lbl,
                },
                Self::Pi {
                    binder_info: rbi,
                    arg_type_cert: ra,
                    arg_level: ral,
                    body_type_cert: rb,
                    body_level: rbl,
                },
            ) => lbi == rbi && la == ra && lal == ral && lb == rb && lbl == rbl,
            (
                Self::Let {
                    type_cert: lt,
                    value_cert: lv,
                    body_cert: lb,
                    result_type: lr,
                },
                Self::Let {
                    type_cert: rt,
                    value_cert: rv,
                    body_cert: rb,
                    result_type: rr,
                },
            ) => lt == rt && lv == rv && lb == rb && lr == rr,
            (Self::Lit { lit: ll, type_: lt }, Self::Lit { lit: rl, type_: rt }) => {
                ll == rl && lt == rt
            }
            (
                Self::DefEq {
                    inner: li,
                    expected_type: le,
                    actual_type: la,
                    eq_steps: ls,
                },
                Self::DefEq {
                    inner: ri,
                    expected_type: re,
                    actual_type: ra,
                    eq_steps: rs,
                },
            ) => li == ri && le == re && la == ra && ls == rs,
            (
                Self::MData {
                    metadata: lm,
                    inner_cert: li,
                    result_type: lr,
                },
                Self::MData {
                    metadata: rm,
                    inner_cert: ri,
                    result_type: rr,
                },
            ) => lm == rm && li == ri && lr == rr,
            (
                Self::Proj {
                    struct_name: ln,
                    idx: li,
                    expr_cert: lc,
                    expr_type: let_,
                    field_type: lft,
                },
                Self::Proj {
                    struct_name: rn,
                    idx: ri,
                    expr_cert: rc,
                    expr_type: ret,
                    field_type: rft,
                },
            ) => ln == rn && li == ri && lc == rc && let_ == ret && lft == rft,
            (Self::CubicalInterval, Self::CubicalInterval) => true,
            (Self::CubicalEndpoint { is_one: left }, Self::CubicalEndpoint { is_one: right }) => {
                left == right
            }
            (
                Self::CubicalPath {
                    ty_cert: lt,
                    ty_level: ll,
                    left_cert: lle,
                    right_cert: lr,
                },
                Self::CubicalPath {
                    ty_cert: rt,
                    ty_level: rl,
                    left_cert: rle,
                    right_cert: rr,
                },
            ) => lt == rt && ll == rl && lle == rle && lr == rr,
            (
                Self::CubicalPathLam {
                    body_cert: lb,
                    body_type: lbt,
                    result_type: lr,
                },
                Self::CubicalPathLam {
                    body_cert: rb,
                    body_type: rbt,
                    result_type: rr,
                },
            ) => lb == rb && lbt == rbt && lr == rr,
            (
                Self::CubicalPathApp {
                    path_cert: lp,
                    arg_cert: la,
                    path_type: lpt,
                    result_type: lr,
                },
                Self::CubicalPathApp {
                    path_cert: rp,
                    arg_cert: ra,
                    path_type: rpt,
                    result_type: rr,
                },
            ) => lp == rp && la == ra && lpt == rpt && lr == rr,
            (
                Self::CubicalHComp {
                    ty_cert: lt,
                    phi_cert: lp,
                    u_cert: lu,
                    base_cert: lb,
                    result_type: lr,
                },
                Self::CubicalHComp {
                    ty_cert: rt,
                    phi_cert: rp,
                    u_cert: ru,
                    base_cert: rb,
                    result_type: rr,
                },
            ) => lt == rt && lp == rp && lu == ru && lb == rb && lr == rr,
            (
                Self::CubicalTransp {
                    ty_cert: lt,
                    phi_cert: lp,
                    base_cert: lb,
                    result_type: lr,
                },
                Self::CubicalTransp {
                    ty_cert: rt,
                    phi_cert: rp,
                    base_cert: rb,
                    result_type: rr,
                },
            ) => lt == rt && lp == rp && lb == rb && lr == rr,
            (
                Self::CubicalCoe {
                    ty_cert: lt,
                    r_cert: lrc,
                    s_cert: ls,
                    base_cert: lb,
                    result_type: lr,
                },
                Self::CubicalCoe {
                    ty_cert: rt,
                    r_cert: rrc,
                    s_cert: rs,
                    base_cert: rb,
                    result_type: rr,
                },
            ) => lt == rt && lrc == rrc && ls == rs && lb == rb && lr == rr,
            (
                Self::ZFCSet {
                    kind: lk,
                    result_type: lr,
                },
                Self::ZFCSet {
                    kind: rk,
                    result_type: rr,
                },
            ) => lk == rk && lr == rr,
            (
                Self::ZFCMem {
                    elem_cert: le,
                    set_cert: ls,
                },
                Self::ZFCMem {
                    elem_cert: re,
                    set_cert: rs,
                },
            ) => le == re && ls == rs,
            (
                Self::ZFCComprehension {
                    var_ty_cert: lv,
                    pred_cert: lp,
                    result_type: lr,
                },
                Self::ZFCComprehension {
                    var_ty_cert: rv,
                    pred_cert: rp,
                    result_type: rr,
                },
            ) => lv == rv && lp == rp && lr == rr,
            (Self::SProp, Self::SProp) => true,
            (Self::Squash { inner_cert: left }, Self::Squash { inner_cert: right }) => {
                left == right
            }
            _ => false,
        })
    }
}

impl Drop for ProofCert {
    fn drop(&mut self) {
        if !proof_cert_has_recursive_children(self) || !recursive_drop_needs_segment() {
            return;
        }

        // Ordinary nodes use compiler-generated field teardown. At the stack
        // red zone, detach only the next recursive children and destroy them
        // on a grown stack segment. Replacement allocations therefore occur
        // at segment transitions rather than at every node in a deep tree.
        let leaf = || Box::new(ProofCert::SProp);
        let mut cert_children = Vec::with_capacity(4);
        let mut def_eq_steps = None;
        let mut zfc_kind = None;

        match self {
            Self::App {
                fn_cert, arg_cert, ..
            } => {
                cert_children.push(std::mem::replace(fn_cert, leaf()));
                cert_children.push(std::mem::replace(arg_cert, leaf()));
            }
            Self::Lam {
                arg_type_cert,
                body_cert,
                ..
            }
            | Self::Pi {
                arg_type_cert,
                body_type_cert: body_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(arg_type_cert, leaf()));
                cert_children.push(std::mem::replace(body_cert, leaf()));
            }
            Self::Let {
                type_cert,
                value_cert,
                body_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(type_cert, leaf()));
                cert_children.push(std::mem::replace(value_cert, leaf()));
                cert_children.push(std::mem::replace(body_cert, leaf()));
            }
            Self::DefEq {
                inner, eq_steps, ..
            } => {
                cert_children.push(std::mem::replace(inner, leaf()));
                def_eq_steps = Some(std::mem::take(eq_steps));
            }
            Self::MData { inner_cert, .. }
            | Self::Proj {
                expr_cert: inner_cert,
                ..
            }
            | Self::CubicalPathLam {
                body_cert: inner_cert,
                ..
            }
            | Self::Squash { inner_cert } => {
                cert_children.push(std::mem::replace(inner_cert, leaf()));
            }
            Self::CubicalPath {
                ty_cert,
                left_cert,
                right_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(ty_cert, leaf()));
                cert_children.push(std::mem::replace(left_cert, leaf()));
                cert_children.push(std::mem::replace(right_cert, leaf()));
            }
            Self::CubicalPathApp {
                path_cert,
                arg_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(path_cert, leaf()));
                cert_children.push(std::mem::replace(arg_cert, leaf()));
            }
            Self::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(ty_cert, leaf()));
                cert_children.push(std::mem::replace(phi_cert, leaf()));
                cert_children.push(std::mem::replace(u_cert, leaf()));
                cert_children.push(std::mem::replace(base_cert, leaf()));
            }
            Self::CubicalTransp {
                ty_cert,
                phi_cert,
                base_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(ty_cert, leaf()));
                cert_children.push(std::mem::replace(phi_cert, leaf()));
                cert_children.push(std::mem::replace(base_cert, leaf()));
            }
            Self::CubicalCoe {
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(ty_cert, leaf()));
                cert_children.push(std::mem::replace(r_cert, leaf()));
                cert_children.push(std::mem::replace(s_cert, leaf()));
                cert_children.push(std::mem::replace(base_cert, leaf()));
            }
            Self::ZFCSet { kind, .. } => {
                zfc_kind = Some(std::mem::replace(kind, ZFCSetCertKind::Empty));
            }
            Self::ZFCMem {
                elem_cert,
                set_cert,
            } => {
                cert_children.push(std::mem::replace(elem_cert, leaf()));
                cert_children.push(std::mem::replace(set_cert, leaf()));
            }
            Self::ZFCComprehension {
                var_ty_cert,
                pred_cert,
                ..
            } => {
                cert_children.push(std::mem::replace(var_ty_cert, leaf()));
                cert_children.push(std::mem::replace(pred_cert, leaf()));
            }
            Self::Sort { .. }
            | Self::BVar { .. }
            | Self::FVar { .. }
            | Self::Const { .. }
            | Self::Lit { .. }
            | Self::CubicalInterval
            | Self::CubicalEndpoint { .. }
            | Self::SProp => {}
        }

        crate::expr::stack_safe(move || {
            drop(cert_children);
            drop(def_eq_steps);
            drop(zfc_kind);
        });
    }
}

fn proof_cert_has_recursive_children(cert: &ProofCert) -> bool {
    !matches!(
        cert,
        ProofCert::Sort { .. }
            | ProofCert::BVar { .. }
            | ProofCert::FVar { .. }
            | ProofCert::Const { .. }
            | ProofCert::Lit { .. }
            | ProofCert::CubicalInterval
            | ProofCert::CubicalEndpoint { .. }
            | ProofCert::SProp
    )
}

fn recursive_drop_needs_segment() -> bool {
    #[cfg(kani)]
    {
        false
    }
    #[cfg(not(kani))]
    {
        const DROP_RED_ZONE: usize = 256 * 1024;
        stacker::remaining_stack().is_none_or(|remaining| remaining < DROP_RED_ZONE)
    }
}

/// Certificate variants for ZFC set expressions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ZFCSetCertKind {
    /// Empty set ∅
    Empty,
    /// Singleton {a}
    Singleton(Box<ProofCert>),
    /// Unordered pair {a, b}
    Pair(Box<ProofCert>, Box<ProofCert>),
    /// Union ⋃A
    Union(Box<ProofCert>),
    /// Power set P(A)
    PowerSet(Box<ProofCert>),
    /// Separation {x ∈ A | φ(x)}
    Separation {
        /// Certificate for the base set A
        set_cert: Box<ProofCert>,
        /// Certificate for the predicate φ
        pred_cert: Box<ProofCert>,
    },
    /// Replacement {F(x) | x ∈ A}
    Replacement {
        /// Certificate for the base set A
        set_cert: Box<ProofCert>,
        /// Certificate for the function F
        func_cert: Box<ProofCert>,
    },
    /// Infinity ω
    Infinity,
    /// Choice (AC)
    Choice(Box<ProofCert>),
}

/// A step in a definitional equality proof.
///
/// These steps record how the verifier establishes definitional equality
/// between types, useful for debugging and proof reconstruction.
pub enum DefEqStep {
    /// Reflexivity: e ≡ e
    Refl,
    /// Symmetry: e1 ≡ e2 implies e2 ≡ e1
    Symm(Box<DefEqStep>),
    /// Transitivity: e1 ≡ e2 and e2 ≡ e3 implies e1 ≡ e3
    Trans(Box<DefEqStep>, Box<DefEqStep>),
    /// Beta reduction: (λx.b) a ≡ b[a/x]
    Beta,
    /// Delta reduction: unfold constant definition
    Delta(Name),
    /// Zeta reduction: unfold let binding
    Zeta,
    /// Iota reduction: recursor computation rule
    Iota,
    /// Structural: congruence through constructors
    Struct(String, Vec<DefEqStep>),
}

impl std::fmt::Debug for DefEqStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Refl => f.write_str("Refl"),
            Self::Symm(inner) => f.debug_tuple("Symm").field(&DefEqRule(inner)).finish(),
            Self::Trans(left, right) => f
                .debug_tuple("Trans")
                .field(&DefEqRule(left))
                .field(&DefEqRule(right))
                .finish(),
            Self::Beta => f.write_str("Beta"),
            Self::Delta(name) => f.debug_tuple("Delta").field(name).finish(),
            Self::Zeta => f.write_str("Zeta"),
            Self::Iota => f.write_str("Iota"),
            Self::Struct(name, children) => {
                let mut value = f.debug_struct("Struct");
                value.field("name", &BoundedStr(name));
                value.field("children", &DefEqListSummary(children));
                value.finish()
            }
        }
    }
}

impl PartialEq for DefEqStep {
    fn eq(&self, other: &Self) -> bool {
        crate::expr::stack_safe(|| match (self, other) {
            (Self::Refl, Self::Refl)
            | (Self::Beta, Self::Beta)
            | (Self::Zeta, Self::Zeta)
            | (Self::Iota, Self::Iota) => true,
            (Self::Symm(left), Self::Symm(right)) => left == right,
            (Self::Trans(ll, lr), Self::Trans(rl, rr)) => ll == rl && lr == rr,
            (Self::Delta(left), Self::Delta(right)) => left == right,
            (Self::Struct(ln, ls), Self::Struct(rn, rs)) => ln == rn && ls == rs,
            _ => false,
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename = "DefEqStep")]
enum DefEqStepWire<D, N, S, V> {
    Refl,
    Symm(D),
    Trans(D, D),
    Beta,
    Delta(N),
    Zeta,
    Iota,
    Struct(S, V),
}

fn def_eq_step_wire(
    step: &DefEqStep,
) -> DefEqStepWire<&DefEqStep, &Name, &String, &Vec<DefEqStep>> {
    match step {
        DefEqStep::Refl => DefEqStepWire::Refl,
        DefEqStep::Symm(inner) => DefEqStepWire::Symm(inner),
        DefEqStep::Trans(left, right) => DefEqStepWire::Trans(left, right),
        DefEqStep::Beta => DefEqStepWire::Beta,
        DefEqStep::Delta(name) => DefEqStepWire::Delta(name),
        DefEqStep::Zeta => DefEqStepWire::Zeta,
        DefEqStep::Iota => DefEqStepWire::Iota,
        DefEqStep::Struct(name, children) => DefEqStepWire::Struct(name, children),
    }
}

fn def_eq_step_from_wire(
    wire: DefEqStepWire<Box<DefEqStep>, Name, String, Vec<DefEqStep>>,
) -> DefEqStep {
    match wire {
        DefEqStepWire::Refl => DefEqStep::Refl,
        DefEqStepWire::Symm(inner) => DefEqStep::Symm(inner),
        DefEqStepWire::Trans(left, right) => DefEqStep::Trans(left, right),
        DefEqStepWire::Beta => DefEqStep::Beta,
        DefEqStepWire::Delta(name) => DefEqStep::Delta(name),
        DefEqStepWire::Zeta => DefEqStep::Zeta,
        DefEqStepWire::Iota => DefEqStep::Iota,
        DefEqStepWire::Struct(name, children) => DefEqStep::Struct(name, children),
    }
}

impl Serialize for DefEqStep {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        crate::expr::stack_safe(|| def_eq_step_wire(self).serialize(serializer))
    }
}

impl<'de> Deserialize<'de> for DefEqStep {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let _decode_node =
            crate::serde_budget::enter_decode_node::<D::Error>("definitional-equality step")?;
        crate::expr::stack_safe(|| {
            DefEqStepWire::<Box<DefEqStep>, Name, String, Vec<DefEqStep>>::deserialize(deserializer)
                .map(def_eq_step_from_wire)
        })
    }
}

// Definitional-equality traces are recursive independently of `ProofCert`.
// Give each child clone its own growth boundary for the same reason as the
// certificate tree above.
impl Clone for DefEqStep {
    fn clone(&self) -> Self {
        crate::expr::stack_safe(|| match self {
            Self::Refl => Self::Refl,
            Self::Symm(step) => Self::Symm(step.clone()),
            Self::Trans(left, right) => Self::Trans(left.clone(), right.clone()),
            Self::Beta => Self::Beta,
            Self::Delta(name) => Self::Delta(name.clone()),
            Self::Zeta => Self::Zeta,
            Self::Iota => Self::Iota,
            Self::Struct(name, steps) => Self::Struct(name.clone(), steps.clone()),
        })
    }
}

impl Drop for DefEqStep {
    fn drop(&mut self) {
        if matches!(
            self,
            Self::Refl | Self::Beta | Self::Delta(_) | Self::Zeta | Self::Iota
        ) || !recursive_drop_needs_segment()
        {
            return;
        }

        let leaf = || Box::new(DefEqStep::Refl);
        let mut boxed_children = Vec::with_capacity(2);
        let mut vector_children = None;
        match self {
            Self::Symm(step) => boxed_children.push(std::mem::replace(step, leaf())),
            Self::Trans(left, right) => {
                boxed_children.push(std::mem::replace(left, leaf()));
                boxed_children.push(std::mem::replace(right, leaf()));
            }
            Self::Struct(_, steps) => vector_children = Some(std::mem::take(steps)),
            Self::Refl | Self::Beta | Self::Delta(_) | Self::Zeta | Self::Iota => {}
        }
        crate::expr::stack_safe(move || {
            drop(boxed_children);
            drop(vector_children);
        });
    }
}

/// Error during certificate verification
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum CertError {
    /// Type mismatch during verification
    #[error("Type mismatch at {location}: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        /// The expected type in this context.
        expected: Box<Expr>,
        /// The actual type found.
        actual: Box<Expr>,
        /// Description of where the mismatch occurred.
        location: String,
    },
    /// Unknown constant reference
    #[error("Unknown constant: {0:?}")]
    UnknownConst(Name),
    /// Unknown free variable
    #[error("Unknown free variable: {0:?}")]
    UnknownFVar(FVarId),
    /// Invalid de Bruijn index
    #[error("Invalid bound variable index: {0}")]
    InvalidBVar(u32),
    /// Certificate structure doesn't match expression
    #[error("Structure mismatch: expected {expected}, got {actual}")]
    StructureMismatch {
        /// The expected certificate structure.
        expected: String,
        /// The actual certificate structure.
        actual: String,
    },
    /// Definitional equality check failed
    #[error("Definitional equality failed: {left:?} ≢ {right:?}")]
    DefEqFailed {
        /// The left-hand side of the equality.
        left: Box<Expr>,
        /// The right-hand side of the equality.
        right: Box<Expr>,
    },
    /// Sort level mismatch
    #[error("Level mismatch: expected {expected:?}, got {actual:?}")]
    LevelMismatch {
        /// The expected universe level.
        expected: Level,
        /// The actual universe level.
        actual: Level,
    },
    /// Invalid certificate structure
    #[error("Invalid certificate: {0}")]
    InvalidCert(String),
    /// Mode-specific feature requires a different mode
    #[error(
        "Feature '{feature}' requires {required_mode} mode, but current mode is {current_mode}"
    )]
    ModeRequired {
        /// The feature that was attempted.
        feature: String,
        /// The mode required to use this feature.
        required_mode: CleanMode,
        /// The current mode that doesn't support the feature.
        current_mode: CleanMode,
    },
}

/// Get a descriptive name for certificate variant
pub fn cert_name(cert: &ProofCert) -> String {
    match cert {
        ProofCert::Sort { .. } => "Sort".to_string(),
        ProofCert::BVar { .. } => "BVar".to_string(),
        ProofCert::FVar { .. } => "FVar".to_string(),
        ProofCert::Const { .. } => "Const".to_string(),
        ProofCert::App { .. } => "App".to_string(),
        ProofCert::Lam { .. } => "Lam".to_string(),
        ProofCert::Pi { .. } => "Pi".to_string(),
        ProofCert::Let { .. } => "Let".to_string(),
        ProofCert::Lit { .. } => "Lit".to_string(),
        ProofCert::DefEq { .. } => "DefEq".to_string(),
        ProofCert::MData { .. } => "MData".to_string(),
        ProofCert::Proj { .. } => "Proj".to_string(),
        ProofCert::CubicalInterval => "CubicalInterval".to_string(),
        ProofCert::CubicalEndpoint { .. } => "CubicalEndpoint".to_string(),
        ProofCert::CubicalPath { .. } => "CubicalPath".to_string(),
        ProofCert::CubicalPathLam { .. } => "CubicalPathLam".to_string(),
        ProofCert::CubicalPathApp { .. } => "CubicalPathApp".to_string(),
        ProofCert::CubicalHComp { .. } => "CubicalHComp".to_string(),
        ProofCert::CubicalTransp { .. } => "CubicalTransp".to_string(),
        ProofCert::CubicalCoe { .. } => "CubicalCoe".to_string(),
        ProofCert::ZFCSet { .. } => "ZFCSet".to_string(),
        ProofCert::ZFCMem { .. } => "ZFCMem".to_string(),
        ProofCert::ZFCComprehension { .. } => "ZFCComprehension".to_string(),
        ProofCert::SProp => "SProp".to_string(),
        ProofCert::Squash { .. } => "Squash".to_string(),
    }
}

/// Get a descriptive name for expression variant
pub fn expr_name(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::BVar(_) => "BVar".to_string(),
        ExprKind::FVar(_) => "FVar".to_string(),
        ExprKind::Sort(_) => "Sort".to_string(),
        ExprKind::Const(_, _) => "Const".to_string(),
        ExprKind::App(_, _) => "App".to_string(),
        ExprKind::Lam(_, _, _) => "Lam".to_string(),
        ExprKind::Pi(_, _, _) => "Pi".to_string(),
        ExprKind::Let(_, _, _, _, _) => "Let".to_string(),
        ExprKind::Lit(_) => "Lit".to_string(),
        ExprKind::Proj(_, _, _) => "Proj".to_string(),
        ExprKind::MData(_, _) => "MData".to_string(),
        ExprKind::CubicalInterval => "CubicalInterval".to_string(),
        ExprKind::CubicalI0 => "CubicalI0".to_string(),
        ExprKind::CubicalI1 => "CubicalI1".to_string(),
        ExprKind::CubicalPath { .. } => "CubicalPath".to_string(),
        ExprKind::CubicalPathLam { .. } => "CubicalPathLam".to_string(),
        ExprKind::CubicalPathApp { .. } => "CubicalPathApp".to_string(),
        ExprKind::CubicalHComp { .. } => "CubicalHComp".to_string(),
        ExprKind::CubicalTransp { .. } => "CubicalTransp".to_string(),
        ExprKind::CubicalCoe { .. } => "CubicalCoe".to_string(),
        ExprKind::ZFCSet(_) => "ZFCSet".to_string(),
        ExprKind::ZFCMem { .. } => "ZFCMem".to_string(),
        ExprKind::ZFCComprehension { .. } => "ZFCComprehension".to_string(),
        ExprKind::SProp => "SProp".to_string(),
        ExprKind::Squash(_) => "Squash".to_string(),
    }
}

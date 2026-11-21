// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust mirror of the Coq 8.20 kernel `Constr.t` (and the name/universe
//! types it embeds), as laid out in `kernel/constr.ml` and validated by
//! `checker/values.ml`.
//!
//! Constructor tags follow `kind_of_term` declaration order (all
//! constructors are non-constant): Rel=0, Var=1, Meta=2, Evar=3, Sort=4,
//! Cast=5, Prod=6, Lambda=7, LetIn=8, App=9, Const=10, Ind=11, Construct=12,
//! Case=13, Fix=14, CoFix=15, Proj=16, Int=17, Float=18, String=19,
//! Array=20. `Constr.t` is `[@@unboxed]`, so the marshaled value *is* the
//! `kind_of_term` block.

// ---------------------------------------------------------------------------
// Names (kernel/names.ml)
// ---------------------------------------------------------------------------

/// A directory path, stored as in the kernel: most-local component first
/// (`Coq.Init.Logic` is `["Logic", "Init", "Coq"]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirPath(pub Vec<String>);

impl DirPath {
    /// Dotted form, outermost first: `Coq.Init.Logic`.
    #[must_use]
    pub fn dotted(&self) -> String {
        self.0.iter().rev().cloned().collect::<Vec<_>>().join(".")
    }
}

/// A module path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModPath {
    /// Toplevel library file (`MPfile`).
    File(DirPath),
    /// Functor parameter (`MPbound`): unique id `(uid, id, dirpath)`.
    Bound { uid: i64, id: String, dp: DirPath },
    /// Submodule access (`MPdot`).
    Dot(Box<ModPath>, String),
}

/// A kernel name: module path + label. The kernel's cached `refhash` is
/// dropped (it is derivable and irrelevant to identity).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KerName {
    pub modpath: ModPath,
    pub label: String,
}

/// A constant / mutual-inductive name (`KerPair`): user name plus the
/// canonical name when they differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KerPair {
    pub user: KerName,
    pub canonical: Option<KerName>,
}

/// An inductive type reference: block name + index within the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndRef {
    pub mind: KerPair,
    pub index: i64,
}

/// A constructor reference. `index` is 1-based, as in the kernel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorRef {
    pub ind: IndRef,
    pub index: i64,
}

// ---------------------------------------------------------------------------
// Universes and sorts (kernel/univ.ml, kernel/sorts.ml)
// ---------------------------------------------------------------------------

/// A sort-quality variable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QVar {
    /// `Var of int`.
    Idx(i64),
    /// `Unif of string * int`.
    Named(String, i64),
}

/// A sort quality (element of a universe instance).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Quality {
    Var(QVar),
    /// `QConstant`: 0 = QSProp, 1 = QProp, 2 = QType.
    Constant(i64),
}

/// A global universe level (`Univ.UGlobal.t`): `{library; process; uid}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UGlobal {
    pub library: DirPath,
    pub process: String,
    pub uid: i64,
}

/// `Univ.Level.raw_level`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawLevel {
    Set,
    Level(UGlobal),
    Var(i64),
}

/// `Univ.Level.t = { hash : int; data : raw_level }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Level {
    pub hash: i64,
    pub data: RawLevel,
}

/// `Univ.Universe.t`: a non-empty list of `(level, increment)` pairs.
pub type Universe = Vec<(Level, i64)>;

/// `Sorts.t`.
#[derive(Clone, Debug, PartialEq)]
pub enum Sort {
    SProp,
    Prop,
    Set,
    Type(Universe),
    QSort(QVar, Universe),
}

/// `Sorts.relevance`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Relevance {
    Relevant,
    Irrelevant,
    Var(QVar),
}

/// A binder annotation: optional name + relevance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    /// `None` = Anonymous.
    pub name: Option<String>,
    pub relevance: Relevance,
}

/// A universe instance: quality and level arrays.
#[derive(Clone, Debug, PartialEq)]
pub struct Instance {
    pub qualities: Vec<Quality>,
    pub levels: Vec<Level>,
}

// ---------------------------------------------------------------------------
// Case / fixpoint / projection payloads
// ---------------------------------------------------------------------------

/// `Constr.cast_kind`: VMcast = 0, NATIVEcast = 1, DEFAULTcast = 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    Vm,
    Native,
    Default,
}

/// `Constr.case_info`.
#[derive(Clone, Debug, PartialEq)]
pub struct CaseInfo {
    pub ind: IndRef,
    pub npar: i64,
    pub cstr_ndecls: Vec<i64>,
    pub cstr_nargs: Vec<i64>,
    /// `case_style`: LetStyle=0, IfStyle=1, LetPatternStyle=2, MatchStyle=3,
    /// RegularStyle=4.
    pub style: i64,
}

/// The return predicate of a `Case`.
#[derive(Clone, Debug, PartialEq)]
pub struct CaseReturn {
    pub binders: Vec<Binder>,
    pub body: Constr,
    pub relevance: Relevance,
}

/// One branch of a `Case`.
#[derive(Clone, Debug, PartialEq)]
pub struct CaseBranch {
    pub binders: Vec<Binder>,
    pub body: Constr,
}

/// Full `Case` payload.
#[derive(Clone, Debug, PartialEq)]
pub struct CaseData {
    pub info: CaseInfo,
    pub instance: Instance,
    pub params: Vec<Constr>,
    pub ret: CaseReturn,
    /// `NoInvert` = `None`; `CaseInvert {indices}` = `Some(indices)`.
    pub invert: Option<Vec<Constr>>,
    pub scrutinee: Constr,
    pub branches: Vec<CaseBranch>,
}

/// Mutual (co)fixpoint declaration block.
#[derive(Clone, Debug, PartialEq)]
pub struct RecDecl {
    pub binders: Vec<Binder>,
    pub types: Vec<Constr>,
    pub bodies: Vec<Constr>,
}

/// Projection payload (`Names.Projection.Repr.t` + unfolded flag).
#[derive(Clone, Debug, PartialEq)]
pub struct ProjData {
    pub ind: IndRef,
    pub npars: i64,
    pub arg: i64,
    pub name: KerPair,
    pub unfolded: bool,
}

// ---------------------------------------------------------------------------
// Constr
// ---------------------------------------------------------------------------

/// Rust mirror of the Coq kernel term representation.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum Constr {
    /// De Bruijn index (1-based).
    Rel(i64),
    /// Named section/context variable.
    Var(String),
    Sort(Box<Sort>),
    Cast(Box<Constr>, CastKind, Box<Constr>),
    Prod(Binder, Box<Constr>, Box<Constr>),
    Lambda(Binder, Box<Constr>, Box<Constr>),
    /// `LetIn (binder, value, type, body)`.
    LetIn(Binder, Box<Constr>, Box<Constr>, Box<Constr>),
    App(Box<Constr>, Vec<Constr>),
    Const(Box<(KerPair, Instance)>),
    Ind(Box<(IndRef, Instance)>),
    Construct(Box<(CtorRef, Instance)>),
    Case(Box<CaseData>),
    Fix {
        /// Structurally-recursive argument index per component.
        struct_args: Vec<i64>,
        /// Which component this `Fix` denotes.
        which: i64,
        decl: Box<RecDecl>,
    },
    CoFix {
        which: i64,
        decl: Box<RecDecl>,
    },
    Proj(Box<ProjData>, Relevance, Box<Constr>),
    /// Primitive 63-bit unsigned integer (stored in an OCaml int).
    Uint63(i64),
    /// Primitive float.
    Float64(f64),
    /// Primitive string.
    PStr(Vec<u8>),
    /// Primitive persistent array: `(instance, elems, default, type)`.
    Array(Box<(Instance, Vec<Constr>, Constr, Constr)>),
}

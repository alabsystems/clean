// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq ecosystem library detection and type mappings.
//!
//! Handles major Coq ecosystem libraries beyond the standard library:
//! CompCert (verified C compiler), Flocq (IEEE 754 floating-point),
//! MathComp (ssreflect-based mathematics), Iris, UniMath, HoTT, and others.
//!
//! Each ecosystem gets a type mapping table and default axiom profile.
//! The [`EcosystemMap`] merges all mappings for fast cross-ecosystem lookup.

use crate::coq::stdlib::{coq_clean_mappings, MappingCategory, TypeMapping};
use crate::types::AxiomProfile;

/// Coq ecosystem library classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CoqEcosystem {
    Stdlib,
    MathComp,
    CompCert,
    Flocq,
    /// Concurrent separation logic (Iris).
    Iris,
    /// Univalent mathematics (UniMath).
    UniMath,
    /// Homotopy type theory (HoTT).
    HoTT,
    /// std++ library.
    Stdpp,
    /// CoqEAL (algebra).
    Coqeal,
    Unknown,
}

/// Detect which Coq ecosystem library a module belongs to.
pub fn detect_ecosystem(module_path: &str) -> CoqEcosystem {
    if module_path.starts_with("Coq.") || module_path.starts_with("Init.") {
        CoqEcosystem::Stdlib
    } else if module_path.starts_with("mathcomp.") || module_path.starts_with("ssreflect.") {
        CoqEcosystem::MathComp
    } else if module_path.contains("compcert")
        || module_path.starts_with("Clight.")
        || module_path.starts_with("Asm.")
    {
        CoqEcosystem::CompCert
    } else if module_path.starts_with("Flocq.") {
        CoqEcosystem::Flocq
    } else if module_path.starts_with("iris.") {
        CoqEcosystem::Iris
    } else if module_path.starts_with("UniMath.") {
        CoqEcosystem::UniMath
    } else if module_path.starts_with("HoTT.") {
        CoqEcosystem::HoTT
    } else if module_path.starts_with("stdpp.") {
        CoqEcosystem::Stdpp
    } else if module_path.starts_with("CoqEAL") {
        CoqEcosystem::Coqeal
    } else {
        CoqEcosystem::Unknown
    }
}

// ---------------------------------------------------------------------------
// CompCert type mappings
// ---------------------------------------------------------------------------

/// CompCert verified C compiler type mappings.
pub fn compcert_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // Memory model
        TypeMapping {
            coq_name: "Memdata.memval",
            clean_name_mapping: "Mathverse.CompCert.Memval",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Memory.Mem.mem",
            clean_name_mapping: "Mathverse.CompCert.Mem",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Memory.Mem.load",
            clean_name_mapping: "Mathverse.CompCert.Mem.load",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Memory.Mem.store",
            clean_name_mapping: "Mathverse.CompCert.Mem.store",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Memory.Mem.alloc",
            clean_name_mapping: "Mathverse.CompCert.Mem.alloc",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Memory.Mem.free",
            clean_name_mapping: "Mathverse.CompCert.Mem.free",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Memory.Mem.valid_pointer",
            clean_name_mapping: "Mathverse.CompCert.Mem.validPtr",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Memory.Mem.perm",
            clean_name_mapping: "Mathverse.CompCert.Mem.perm",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "Values.val",
            clean_name_mapping: "Mathverse.CompCert.Val",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Values.Vundef",
            clean_name_mapping: "Mathverse.CompCert.Val.undef",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Values.Vint",
            clean_name_mapping: "Mathverse.CompCert.Val.int",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Values.Vlong",
            clean_name_mapping: "Mathverse.CompCert.Val.long",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Values.Vfloat",
            clean_name_mapping: "Mathverse.CompCert.Val.float",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Values.Vptr",
            clean_name_mapping: "Mathverse.CompCert.Val.ptr",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Integers.int",
            clean_name_mapping: "Mathverse.CompCert.Int32",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Integers.int64",
            clean_name_mapping: "Mathverse.CompCert.Int64",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Integers.ptrofs",
            clean_name_mapping: "Mathverse.CompCert.PtrOfs",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Integers.byte",
            clean_name_mapping: "Mathverse.CompCert.Byte",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Floats.float",
            clean_name_mapping: "Mathverse.CompCert.Float64",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Floats.float32",
            clean_name_mapping: "Mathverse.CompCert.Float32",
            category: BaseType,
        },
        // AST types
        TypeMapping {
            coq_name: "AST.program",
            clean_name_mapping: "Mathverse.CompCert.Program",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "AST.fundef",
            clean_name_mapping: "Mathverse.CompCert.Fundef",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "AST.ident",
            clean_name_mapping: "Mathverse.CompCert.Ident",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "AST.globdef",
            clean_name_mapping: "Mathverse.CompCert.Globdef",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "AST.globvar",
            clean_name_mapping: "Mathverse.CompCert.Globvar",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "AST.typ",
            clean_name_mapping: "Mathverse.CompCert.Typ",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "AST.memory_chunk",
            clean_name_mapping: "Mathverse.CompCert.MemChunk",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "AST.external_function",
            clean_name_mapping: "Mathverse.CompCert.ExtFun",
            category: BaseType,
        },
        // Clight (C subset) — semantics types
        TypeMapping {
            coq_name: "Clight.expr",
            clean_name_mapping: "Mathverse.CompCert.CExpr",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Clight.statement",
            clean_name_mapping: "Mathverse.CompCert.CStmt",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Clight.function",
            clean_name_mapping: "Mathverse.CompCert.CFunction",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Clight.type",
            clean_name_mapping: "Mathverse.CompCert.CType",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Clight.program",
            clean_name_mapping: "Mathverse.CompCert.CProgram",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Clight.env",
            clean_name_mapping: "Mathverse.CompCert.CEnv",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Clight.temp_env",
            clean_name_mapping: "Mathverse.CompCert.CTempEnv",
            category: BaseType,
        },
        // Key theorems
        TypeMapping {
            coq_name: "Compiler.transf_c_program_correct",
            clean_name_mapping: "Mathverse.CompCert.compiler_correctness",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Smallstep.forward_simulation",
            clean_name_mapping: "Mathverse.CompCert.ForwardSim",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Smallstep.backward_simulation",
            clean_name_mapping: "Mathverse.CompCert.BackwardSim",
            category: BaseType,
        },
    ]
}

// ---------------------------------------------------------------------------
// Flocq type mappings
// ---------------------------------------------------------------------------

/// Flocq IEEE 754 floating-point formalization type mappings.
pub fn flocq_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // Core definitions
        TypeMapping {
            coq_name: "Flocq.Defs.float_class",
            clean_name_mapping: "Mathverse.Flocq.FloatClass",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Defs.radix",
            clean_name_mapping: "Mathverse.Flocq.Radix",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Defs.generic_format",
            clean_name_mapping: "Mathverse.Flocq.GenericFormat",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Defs.round",
            clean_name_mapping: "Mathverse.Flocq.Round",
            category: Arithmetic,
        },
        // IEEE 754 binary floats
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.binary_float",
            clean_name_mapping: "Mathverse.Flocq.BinaryFloat",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.B754_zero",
            clean_name_mapping: "Mathverse.Flocq.BinaryFloat.zero",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.B754_infinity",
            clean_name_mapping: "Mathverse.Flocq.BinaryFloat.inf",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.B754_nan",
            clean_name_mapping: "Mathverse.Flocq.BinaryFloat.nan",
            category: Constructor,
        },
        // Core formats
        TypeMapping {
            coq_name: "Flocq.Core.FLX.FLX_format",
            clean_name_mapping: "Mathverse.Flocq.FLXFormat",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Core.FLT.FLT_format",
            clean_name_mapping: "Mathverse.Flocq.FLTFormat",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Core.FIX.FIX_format",
            clean_name_mapping: "Mathverse.Flocq.FIXFormat",
            category: BaseType,
        },
        // Rounding modes
        TypeMapping {
            coq_name: "Flocq.Core.Zaux.Znearest",
            clean_name_mapping: "Mathverse.Flocq.RoundNearest",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Core.Zaux.Zfloor",
            clean_name_mapping: "Mathverse.Flocq.RoundFloor",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "Flocq.Core.Zaux.Zceil",
            clean_name_mapping: "Mathverse.Flocq.RoundCeil",
            category: BaseType,
        },
        // Key theorems
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.Bplus_correct",
            clean_name_mapping: "Mathverse.Flocq.add_correct",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.Bmult_correct",
            clean_name_mapping: "Mathverse.Flocq.mul_correct",
            category: Theorem,
        },
        TypeMapping {
            coq_name: "Flocq.IEEE754.Binary.Bdiv_correct",
            clean_name_mapping: "Mathverse.Flocq.div_correct",
            category: Theorem,
        },
    ]
}

// ---------------------------------------------------------------------------
// MathComp type mappings
// ---------------------------------------------------------------------------

/// MathComp (ssreflect-based mathematics) type mappings.
pub fn mathcomp_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // ssreflect basics
        TypeMapping {
            coq_name: "ssrbool.is_true",
            clean_name_mapping: "Mathverse.MathComp.IsTrue",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "ssrbool.reflect",
            clean_name_mapping: "Mathverse.MathComp.Reflect",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "ssrbool.negb",
            clean_name_mapping: "Mathverse.MathComp.Negb",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "ssrbool.andb",
            clean_name_mapping: "Mathverse.MathComp.Andb",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "ssrbool.orb",
            clean_name_mapping: "Mathverse.MathComp.Orb",
            category: Arithmetic,
        },
        // ssrnat
        TypeMapping {
            coq_name: "ssrnat.nat_eqType",
            clean_name_mapping: "Mathverse.MathComp.NatEqType",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "ssrnat.addn",
            clean_name_mapping: "Mathverse.MathComp.Addn",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "ssrnat.muln",
            clean_name_mapping: "Mathverse.MathComp.Muln",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "ssrnat.subn",
            clean_name_mapping: "Mathverse.MathComp.Subn",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "ssrnat.leq",
            clean_name_mapping: "Mathverse.MathComp.Leq",
            category: Comparison,
        },
        // seq (list operations)
        TypeMapping {
            coq_name: "seq.seq",
            clean_name_mapping: "List",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "seq.size",
            clean_name_mapping: "Mathverse.MathComp.SeqSize",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "seq.cat",
            clean_name_mapping: "Mathverse.MathComp.SeqCat",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "seq.map",
            clean_name_mapping: "Mathverse.MathComp.SeqMap",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "seq.filter",
            clean_name_mapping: "Mathverse.MathComp.SeqFilter",
            category: Arithmetic,
        },
        // Finite types
        TypeMapping {
            coq_name: "fintype.Finite.type",
            clean_name_mapping: "Mathverse.MathComp.FinType",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "fintype.enum",
            clean_name_mapping: "Mathverse.MathComp.Enum",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "fintype.card",
            clean_name_mapping: "Mathverse.MathComp.Card",
            category: Arithmetic,
        },
        // Big operators
        TypeMapping {
            coq_name: "bigop.bigop",
            clean_name_mapping: "Mathverse.MathComp.BigOp",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "bigop.big_sum",
            clean_name_mapping: "Mathverse.MathComp.BigSum",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "bigop.big_prod",
            clean_name_mapping: "Mathverse.MathComp.BigProd",
            category: Arithmetic,
        },
        // Algebra
        TypeMapping {
            coq_name: "ssralg.GRing.Ring.type",
            clean_name_mapping: "Mathverse.MathComp.Ring",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "ssralg.GRing.Field.type",
            clean_name_mapping: "Mathverse.MathComp.Field",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "ssralg.GRing.Zmodule.type",
            clean_name_mapping: "Mathverse.MathComp.Zmodule",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "ssralg.GRing.Lmodule.type",
            clean_name_mapping: "Mathverse.MathComp.Lmodule",
            category: BaseType,
        },
        // Polynomial and matrix
        TypeMapping {
            coq_name: "poly.polynomial",
            clean_name_mapping: "Mathverse.MathComp.Polynomial",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "poly.polyC",
            clean_name_mapping: "Mathverse.MathComp.PolyConst",
            category: Arithmetic,
        },
        TypeMapping {
            coq_name: "matrix.matrix",
            clean_name_mapping: "Mathverse.MathComp.Matrix",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "matrix.mxvec",
            clean_name_mapping: "Mathverse.MathComp.MatrixVec",
            category: Arithmetic,
        },
        // Order
        TypeMapping {
            coq_name: "order.Order.le",
            clean_name_mapping: "Mathverse.MathComp.OrderLe",
            category: Comparison,
        },
        TypeMapping {
            coq_name: "order.Order.lt",
            clean_name_mapping: "Mathverse.MathComp.OrderLt",
            category: Comparison,
        },
        // Path
        TypeMapping {
            coq_name: "path.path",
            clean_name_mapping: "Mathverse.MathComp.Path",
            category: TypeConstructor,
        },
    ]
}

// ---------------------------------------------------------------------------
// Iris type mappings
// ---------------------------------------------------------------------------

/// Iris concurrent separation logic type mappings.
pub fn iris_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // Core logic
        TypeMapping {
            coq_name: "iris.bi.bi.bi",
            clean_name_mapping: "Mathverse.Iris.BI",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "iris.bi.bi.bi_wand",
            clean_name_mapping: "Mathverse.Iris.Wand",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.bi.bi.bi_sep",
            clean_name_mapping: "Mathverse.Iris.Sep",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.bi.bi.bi_pure",
            clean_name_mapping: "Mathverse.Iris.Pure",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.bi.bi.persistently",
            clean_name_mapping: "Mathverse.Iris.Persistently",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.bi.bi.later",
            clean_name_mapping: "Mathverse.Iris.Later",
            category: LogicalConnective,
        },
        // Base logic
        TypeMapping {
            coq_name: "iris.base_logic.lib.iprop.iProp",
            clean_name_mapping: "Mathverse.Iris.iProp",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "iris.base_logic.upred.uPred",
            clean_name_mapping: "Mathverse.Iris.uPred",
            category: BaseType,
        },
        // Algebra
        TypeMapping {
            coq_name: "iris.algebra.cmra.cmra",
            clean_name_mapping: "Mathverse.Iris.CMRA",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "iris.algebra.ofe.ofe",
            clean_name_mapping: "Mathverse.Iris.OFE",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "iris.algebra.auth.auth",
            clean_name_mapping: "Mathverse.Iris.Auth",
            category: TypeConstructor,
        },
        // Proofmode / resource
        TypeMapping {
            coq_name: "iris.base_logic.lib.own.own",
            clean_name_mapping: "Mathverse.Iris.Own",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.base_logic.lib.invariants.inv",
            clean_name_mapping: "Mathverse.Iris.Inv",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.base_logic.lib.fancy_updates.fupd",
            clean_name_mapping: "Mathverse.Iris.FUpd",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "iris.program_logic.weakestpre.wp",
            clean_name_mapping: "Mathverse.Iris.WP",
            category: LogicalConnective,
        },
    ]
}

// ---------------------------------------------------------------------------
// UniMath type mappings
// ---------------------------------------------------------------------------

/// UniMath (univalent mathematics) type mappings.
pub fn unimath_mappings() -> &'static [TypeMapping] {
    use MappingCategory::*;
    &[
        // Foundations
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.UU",
            clean_name_mapping: "Mathverse.UniMath.UU",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.paths",
            clean_name_mapping: "Mathverse.UniMath.Paths",
            category: LogicalConnective,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.idpath",
            clean_name_mapping: "Mathverse.UniMath.Idpath",
            category: Constructor,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.dirprod",
            clean_name_mapping: "Mathverse.UniMath.DirProd",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.coprod",
            clean_name_mapping: "Mathverse.UniMath.Coprod",
            category: TypeConstructor,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.isofhlevel",
            clean_name_mapping: "Mathverse.UniMath.IsOfHLevel",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.isaprop",
            clean_name_mapping: "Mathverse.UniMath.IsAProp",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartA.isaset",
            clean_name_mapping: "Mathverse.UniMath.IsASet",
            category: BaseType,
        },
        // Propositions
        TypeMapping {
            coq_name: "UniMath.Foundations.PartB.hProp",
            clean_name_mapping: "Mathverse.UniMath.HProp",
            category: BaseType,
        },
        TypeMapping {
            coq_name: "UniMath.Foundations.PartB.hSet",
            clean_name_mapping: "Mathverse.UniMath.HSet",
            category: BaseType,
        },
        // Equivalences
        TypeMapping {
            coq_name: "UniMath.Foundations.PartD.weq",
            clean_name_mapping: "Mathverse.UniMath.Weq",
            category: TypeConstructor,
        },
    ]
}

// ---------------------------------------------------------------------------
// Ecosystem axiom profiles
// ---------------------------------------------------------------------------

/// Default axiom profile for an ecosystem library.
///
/// Stdlib depends on the specific module (see [`super::coq::classify_coq_module`]).
/// Most ecosystem libraries get at minimum `BRIDGE_AXIOM` since they are imported
/// rather than kernel-verified. Flocq additionally needs `REAL_AXIOMS` for its
/// Reals dependency. UniMath and HoTT require `UNIVALENCE`.
pub fn ecosystem_base_profile(eco: CoqEcosystem) -> AxiomProfile {
    match eco {
        CoqEcosystem::Stdlib => AxiomProfile::NONE,
        CoqEcosystem::MathComp => AxiomProfile::BRIDGE_AXIOM,
        CoqEcosystem::CompCert => AxiomProfile::BRIDGE_AXIOM,
        CoqEcosystem::Flocq => AxiomProfile::BRIDGE_AXIOM | AxiomProfile::REAL_AXIOMS,
        CoqEcosystem::Iris => AxiomProfile::BRIDGE_AXIOM,
        CoqEcosystem::UniMath => AxiomProfile::BRIDGE_AXIOM | AxiomProfile::UNIVALENCE,
        CoqEcosystem::HoTT => AxiomProfile::BRIDGE_AXIOM | AxiomProfile::UNIVALENCE,
        CoqEcosystem::Stdpp => AxiomProfile::BRIDGE_AXIOM,
        CoqEcosystem::Coqeal => AxiomProfile::BRIDGE_AXIOM,
        CoqEcosystem::Unknown => AxiomProfile::BRIDGE_AXIOM,
    }
}

/// Get the type mappings for an ecosystem.
pub fn ecosystem_mappings(eco: CoqEcosystem) -> &'static [TypeMapping] {
    match eco {
        CoqEcosystem::CompCert => compcert_mappings(),
        CoqEcosystem::Flocq => flocq_mappings(),
        CoqEcosystem::MathComp => mathcomp_mappings(),
        CoqEcosystem::Iris => iris_mappings(),
        CoqEcosystem::UniMath => unimath_mappings(),
        _ => &[],
    }
}

// ---------------------------------------------------------------------------
// Combined ecosystem map
// ---------------------------------------------------------------------------

/// Combined lookup map across stdlib and all ecosystem mappings.
///
/// Merges [`coq_clean_mappings`], [`compcert_mappings`], [`flocq_mappings`],
/// [`mathcomp_mappings`], [`iris_mappings`], and [`unimath_mappings`] into
/// a single hash map for fast translation.
pub struct EcosystemMap {
    mappings: hashbrown::HashMap<&'static str, &'static TypeMapping>,
}

impl EcosystemMap {
    /// Build the combined map from all ecosystem mapping tables.
    pub fn new() -> Self {
        let sources: &[&[TypeMapping]] = &[
            coq_clean_mappings(),
            compcert_mappings(),
            flocq_mappings(),
            mathcomp_mappings(),
            iris_mappings(),
            unimath_mappings(),
        ];
        let total: usize = sources.iter().map(|s| s.len()).sum();
        let mut mappings = hashbrown::HashMap::with_capacity(total);
        for source in sources {
            for m in *source {
                mappings.insert(m.coq_name, m);
            }
        }
        Self { mappings }
    }

    /// Translate a Coq qualified name to its Lean 5 equivalent.
    pub fn translate(&self, coq_name: &str) -> Option<&'static str> {
        self.mappings.get(coq_name).map(|m| m.clean_name_mapping)
    }

    /// Total number of mappings across all ecosystems.
    pub fn total_mappings(&self) -> usize {
        self.mappings.len()
    }
}

impl Default for EcosystemMap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Ecosystem detection ---

    #[test]
    fn test_detect_stdlib() {
        assert_eq!(detect_ecosystem("Coq.Init.Datatypes"), CoqEcosystem::Stdlib);
        assert_eq!(detect_ecosystem("Coq.Arith.PeanoNat"), CoqEcosystem::Stdlib);
        assert_eq!(detect_ecosystem("Init.Prelude"), CoqEcosystem::Stdlib);
    }

    #[test]
    fn test_detect_mathcomp() {
        assert_eq!(
            detect_ecosystem("mathcomp.ssreflect.ssrbool"),
            CoqEcosystem::MathComp
        );
        assert_eq!(detect_ecosystem("ssreflect.ssrnat"), CoqEcosystem::MathComp);
    }

    #[test]
    fn test_detect_compcert() {
        assert_eq!(
            detect_ecosystem("compcert.common.Values"),
            CoqEcosystem::CompCert
        );
        assert_eq!(detect_ecosystem("Clight.expr"), CoqEcosystem::CompCert);
        assert_eq!(detect_ecosystem("Asm.program"), CoqEcosystem::CompCert);
    }

    #[test]
    fn test_detect_flocq() {
        assert_eq!(
            detect_ecosystem("Flocq.IEEE754.Binary"),
            CoqEcosystem::Flocq
        );
        assert_eq!(detect_ecosystem("Flocq.Core.FLX"), CoqEcosystem::Flocq);
    }

    #[test]
    fn test_detect_iris_unimath_hott_stdpp_coqeal() {
        assert_eq!(detect_ecosystem("iris.algebra.ofe"), CoqEcosystem::Iris);
        assert_eq!(
            detect_ecosystem("UniMath.Foundations.PartA"),
            CoqEcosystem::UniMath
        );
        assert_eq!(detect_ecosystem("HoTT.Basics.Overture"), CoqEcosystem::HoTT);
        assert_eq!(detect_ecosystem("stdpp.base"), CoqEcosystem::Stdpp);
        assert_eq!(detect_ecosystem("CoqEAL.refinements"), CoqEcosystem::Coqeal);
    }

    #[test]
    fn test_detect_unknown() {
        assert_eq!(detect_ecosystem("SomeRandom.Module"), CoqEcosystem::Unknown);
        assert_eq!(detect_ecosystem(""), CoqEcosystem::Unknown);
    }

    // --- CompCert mappings ---

    #[test]
    fn test_compcert_mappings_nonempty() {
        let m = compcert_mappings();
        assert!(
            m.len() >= 35,
            "expected >= 35 CompCert mappings, got {}",
            m.len()
        );
    }

    #[test]
    fn test_compcert_memory_model() {
        let m = compcert_mappings();
        let mem = m
            .iter()
            .find(|t| t.coq_name == "Memory.Mem.mem")
            .expect("Mem.mem mapping");
        assert_eq!(mem.clean_name_mapping, "Mathverse.CompCert.Mem");
        assert_eq!(mem.category, MappingCategory::BaseType);
    }

    #[test]
    fn test_compcert_compiler_correctness() {
        let m = compcert_mappings();
        let thm = m
            .iter()
            .find(|t| t.coq_name == "Compiler.transf_c_program_correct")
            .expect("compiler correctness theorem");
        assert_eq!(
            thm.clean_name_mapping,
            "Mathverse.CompCert.compiler_correctness"
        );
        assert_eq!(thm.category, MappingCategory::Theorem);
    }

    #[test]
    fn test_compcert_no_duplicate_coq_names() {
        let m = compcert_mappings();
        let mut seen = hashbrown::HashSet::new();
        for t in m {
            assert!(
                seen.insert(t.coq_name),
                "duplicate CompCert coq_name: {}",
                t.coq_name
            );
        }
    }

    // --- Flocq mappings ---

    #[test]
    fn test_flocq_mappings_nonempty() {
        let m = flocq_mappings();
        assert!(
            m.len() >= 15,
            "expected >= 15 Flocq mappings, got {}",
            m.len()
        );
    }

    #[test]
    fn test_flocq_binary_float() {
        let m = flocq_mappings();
        let bf = m
            .iter()
            .find(|t| t.coq_name == "Flocq.IEEE754.Binary.binary_float")
            .expect("binary_float mapping");
        assert_eq!(bf.clean_name_mapping, "Mathverse.Flocq.BinaryFloat");
        assert_eq!(bf.category, MappingCategory::TypeConstructor);
    }

    #[test]
    fn test_flocq_theorems() {
        let m = flocq_mappings();
        let add = m
            .iter()
            .find(|t| t.coq_name == "Flocq.IEEE754.Binary.Bplus_correct")
            .expect("Bplus_correct");
        assert_eq!(add.category, MappingCategory::Theorem);
        let mul = m
            .iter()
            .find(|t| t.coq_name == "Flocq.IEEE754.Binary.Bmult_correct")
            .expect("Bmult_correct");
        assert_eq!(mul.category, MappingCategory::Theorem);
    }

    // --- MathComp mappings ---

    #[test]
    fn test_mathcomp_mappings_nonempty() {
        let m = mathcomp_mappings();
        assert!(
            m.len() >= 25,
            "expected >= 25 MathComp mappings, got {}",
            m.len()
        );
    }

    #[test]
    fn test_mathcomp_ssreflect_basics() {
        let m = mathcomp_mappings();
        let is_true = m
            .iter()
            .find(|t| t.coq_name == "ssrbool.is_true")
            .expect("is_true");
        assert_eq!(is_true.clean_name_mapping, "Mathverse.MathComp.IsTrue");
        assert_eq!(is_true.category, MappingCategory::LogicalConnective);
    }

    #[test]
    fn test_mathcomp_seq_maps_to_list() {
        let m = mathcomp_mappings();
        let seq = m.iter().find(|t| t.coq_name == "seq.seq").expect("seq.seq");
        assert_eq!(seq.clean_name_mapping, "List");
    }

    #[test]
    fn test_mathcomp_algebra() {
        let m = mathcomp_mappings();
        let ring = m
            .iter()
            .find(|t| t.coq_name == "ssralg.GRing.Ring.type")
            .expect("Ring");
        assert_eq!(ring.clean_name_mapping, "Mathverse.MathComp.Ring");
        let matrix = m
            .iter()
            .find(|t| t.coq_name == "matrix.matrix")
            .expect("matrix");
        assert_eq!(matrix.category, MappingCategory::TypeConstructor);
    }

    // --- Axiom profiles ---

    #[test]
    fn test_stdlib_profile_is_none() {
        assert!(ecosystem_base_profile(CoqEcosystem::Stdlib).is_pure());
    }

    #[test]
    fn test_compcert_profile_has_bridge() {
        let p = ecosystem_base_profile(CoqEcosystem::CompCert);
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(!p.has(AxiomProfile::REAL_AXIOMS));
    }

    #[test]
    fn test_flocq_profile_has_reals() {
        let p = ecosystem_base_profile(CoqEcosystem::Flocq);
        assert!(p.has(AxiomProfile::BRIDGE_AXIOM));
        assert!(p.has(AxiomProfile::REAL_AXIOMS));
    }

    #[test]
    fn test_unimath_and_hott_have_univalence() {
        let u = ecosystem_base_profile(CoqEcosystem::UniMath);
        assert!(u.has(AxiomProfile::UNIVALENCE));
        assert!(u.has(AxiomProfile::BRIDGE_AXIOM));
        let h = ecosystem_base_profile(CoqEcosystem::HoTT);
        assert!(h.has(AxiomProfile::UNIVALENCE));
        assert!(h.has(AxiomProfile::BRIDGE_AXIOM));
    }

    #[test]
    fn test_bridge_axiom_ecosystems() {
        for eco in [
            CoqEcosystem::MathComp,
            CoqEcosystem::Iris,
            CoqEcosystem::Stdpp,
            CoqEcosystem::Coqeal,
            CoqEcosystem::Unknown,
        ] {
            let p = ecosystem_base_profile(eco);
            assert!(
                p.has(AxiomProfile::BRIDGE_AXIOM),
                "{eco:?} should have BRIDGE_AXIOM"
            );
        }
    }

    // --- ecosystem_mappings ---

    #[test]
    fn test_ecosystem_mappings_returns_correct_tables() {
        assert_eq!(
            ecosystem_mappings(CoqEcosystem::CompCert).len(),
            compcert_mappings().len()
        );
        assert_eq!(
            ecosystem_mappings(CoqEcosystem::Flocq).len(),
            flocq_mappings().len()
        );
        assert_eq!(
            ecosystem_mappings(CoqEcosystem::MathComp).len(),
            mathcomp_mappings().len()
        );
        assert_eq!(
            ecosystem_mappings(CoqEcosystem::Iris).len(),
            iris_mappings().len()
        );
        assert_eq!(
            ecosystem_mappings(CoqEcosystem::UniMath).len(),
            unimath_mappings().len()
        );
        assert!(ecosystem_mappings(CoqEcosystem::Stdlib).is_empty());
    }

    // --- Combined map ---

    #[test]
    fn test_combined_map_size() {
        let map = EcosystemMap::new();
        let expected = coq_clean_mappings().len()
            + compcert_mappings().len()
            + flocq_mappings().len()
            + mathcomp_mappings().len()
            + iris_mappings().len()
            + unimath_mappings().len();
        // seq.seq maps to "List" which also exists in stdlib — but the coq_name
        // keys are different, so all should be present.
        assert_eq!(map.total_mappings(), expected);
    }

    #[test]
    fn test_translate_stdlib_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(map.translate("Coq.Init.Datatypes.nat"), Some("Nat"));
        assert_eq!(map.translate("Coq.Init.Logic.eq"), Some("Eq"));
    }

    #[test]
    fn test_translate_compcert_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(map.translate("Values.val"), Some("Mathverse.CompCert.Val"));
        assert_eq!(
            map.translate("Integers.int"),
            Some("Mathverse.CompCert.Int32")
        );
        assert_eq!(
            map.translate("Compiler.transf_c_program_correct"),
            Some("Mathverse.CompCert.compiler_correctness"),
        );
    }

    #[test]
    fn test_translate_flocq_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(
            map.translate("Flocq.IEEE754.Binary.binary_float"),
            Some("Mathverse.Flocq.BinaryFloat")
        );
        assert_eq!(
            map.translate("Flocq.IEEE754.Binary.Bplus_correct"),
            Some("Mathverse.Flocq.add_correct")
        );
    }

    #[test]
    fn test_translate_mathcomp_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(
            map.translate("ssrbool.is_true"),
            Some("Mathverse.MathComp.IsTrue")
        );
        assert_eq!(
            map.translate("matrix.matrix"),
            Some("Mathverse.MathComp.Matrix")
        );
    }

    #[test]
    fn test_translate_unknown_returns_none() {
        let map = EcosystemMap::new();
        assert!(map.translate("Nonexistent.thing").is_none());
        assert!(map.translate("").is_none());
    }

    // --- Iris mappings ---

    #[test]
    fn test_iris_mappings_nonempty() {
        let m = iris_mappings();
        assert!(
            m.len() >= 15,
            "expected >= 15 Iris mappings, got {}",
            m.len()
        );
    }

    #[test]
    fn test_iris_core_logic() {
        let m = iris_mappings();
        let iprop = m
            .iter()
            .find(|t| t.coq_name == "iris.base_logic.lib.iprop.iProp")
            .expect("iProp mapping");
        assert_eq!(iprop.clean_name_mapping, "Mathverse.Iris.iProp");
        assert_eq!(iprop.category, MappingCategory::BaseType);

        let wand = m
            .iter()
            .find(|t| t.coq_name == "iris.bi.bi.bi_wand")
            .expect("bi_wand");
        assert_eq!(wand.clean_name_mapping, "Mathverse.Iris.Wand");
        assert_eq!(wand.category, MappingCategory::LogicalConnective);
    }

    #[test]
    fn test_iris_separation_logic() {
        let m = iris_mappings();
        let sep = m
            .iter()
            .find(|t| t.coq_name == "iris.bi.bi.bi_sep")
            .expect("bi_sep");
        assert_eq!(sep.clean_name_mapping, "Mathverse.Iris.Sep");
        let own = m
            .iter()
            .find(|t| t.coq_name == "iris.base_logic.lib.own.own")
            .expect("own");
        assert_eq!(own.clean_name_mapping, "Mathverse.Iris.Own");
        let inv = m
            .iter()
            .find(|t| t.coq_name == "iris.base_logic.lib.invariants.inv")
            .expect("inv");
        assert_eq!(inv.clean_name_mapping, "Mathverse.Iris.Inv");
    }

    #[test]
    fn test_iris_no_duplicate_coq_names() {
        let m = iris_mappings();
        let mut seen = hashbrown::HashSet::new();
        for t in m {
            assert!(
                seen.insert(t.coq_name),
                "duplicate Iris coq_name: {}",
                t.coq_name
            );
        }
    }

    #[test]
    fn test_translate_iris_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(
            map.translate("iris.base_logic.lib.iprop.iProp"),
            Some("Mathverse.Iris.iProp")
        );
        assert_eq!(
            map.translate("iris.algebra.cmra.cmra"),
            Some("Mathverse.Iris.CMRA")
        );
        assert_eq!(
            map.translate("iris.program_logic.weakestpre.wp"),
            Some("Mathverse.Iris.WP")
        );
    }

    // --- UniMath mappings ---

    #[test]
    fn test_unimath_mappings_nonempty() {
        let m = unimath_mappings();
        assert!(
            m.len() >= 10,
            "expected >= 10 UniMath mappings, got {}",
            m.len()
        );
    }

    #[test]
    fn test_unimath_foundations() {
        let m = unimath_mappings();
        let uu = m
            .iter()
            .find(|t| t.coq_name == "UniMath.Foundations.PartA.UU")
            .expect("UU");
        assert_eq!(uu.clean_name_mapping, "Mathverse.UniMath.UU");
        assert_eq!(uu.category, MappingCategory::BaseType);

        let paths = m
            .iter()
            .find(|t| t.coq_name == "UniMath.Foundations.PartA.paths")
            .expect("paths");
        assert_eq!(paths.clean_name_mapping, "Mathverse.UniMath.Paths");
        assert_eq!(paths.category, MappingCategory::LogicalConnective);
    }

    #[test]
    fn test_unimath_hlevels() {
        let m = unimath_mappings();
        let hlevel = m
            .iter()
            .find(|t| t.coq_name == "UniMath.Foundations.PartA.isofhlevel")
            .expect("isofhlevel");
        assert_eq!(hlevel.clean_name_mapping, "Mathverse.UniMath.IsOfHLevel");
        let hprop = m
            .iter()
            .find(|t| t.coq_name == "UniMath.Foundations.PartB.hProp")
            .expect("hProp");
        assert_eq!(hprop.clean_name_mapping, "Mathverse.UniMath.HProp");
    }

    #[test]
    fn test_unimath_no_duplicate_coq_names() {
        let m = unimath_mappings();
        let mut seen = hashbrown::HashSet::new();
        for t in m {
            assert!(
                seen.insert(t.coq_name),
                "duplicate UniMath coq_name: {}",
                t.coq_name
            );
        }
    }

    #[test]
    fn test_translate_unimath_via_combined() {
        let map = EcosystemMap::new();
        assert_eq!(
            map.translate("UniMath.Foundations.PartA.UU"),
            Some("Mathverse.UniMath.UU")
        );
        assert_eq!(
            map.translate("UniMath.Foundations.PartD.weq"),
            Some("Mathverse.UniMath.Weq")
        );
    }

    // --- Expanded CompCert tests ---

    #[test]
    fn test_compcert_memory_operations() {
        let m = compcert_mappings();
        let load = m
            .iter()
            .find(|t| t.coq_name == "Memory.Mem.load")
            .expect("Mem.load");
        assert_eq!(load.clean_name_mapping, "Mathverse.CompCert.Mem.load");
        assert_eq!(load.category, MappingCategory::Arithmetic);
        let store = m
            .iter()
            .find(|t| t.coq_name == "Memory.Mem.store")
            .expect("Mem.store");
        assert_eq!(store.clean_name_mapping, "Mathverse.CompCert.Mem.store");
    }

    #[test]
    fn test_compcert_value_constructors() {
        let m = compcert_mappings();
        let vint = m
            .iter()
            .find(|t| t.coq_name == "Values.Vint")
            .expect("Vint");
        assert_eq!(vint.clean_name_mapping, "Mathverse.CompCert.Val.int");
        assert_eq!(vint.category, MappingCategory::Constructor);
        let vptr = m
            .iter()
            .find(|t| t.coq_name == "Values.Vptr")
            .expect("Vptr");
        assert_eq!(vptr.clean_name_mapping, "Mathverse.CompCert.Val.ptr");
    }

    #[test]
    fn test_compcert_clight_semantics() {
        let m = compcert_mappings();
        let ctype = m
            .iter()
            .find(|t| t.coq_name == "Clight.type")
            .expect("Clight.type");
        assert_eq!(ctype.clean_name_mapping, "Mathverse.CompCert.CType");
        let cprog = m
            .iter()
            .find(|t| t.coq_name == "Clight.program")
            .expect("Clight.program");
        assert_eq!(cprog.category, MappingCategory::TypeConstructor);
    }

    // --- Expanded Flocq tests ---

    #[test]
    fn test_flocq_ieee754_constructors() {
        let m = flocq_mappings();
        let zero = m
            .iter()
            .find(|t| t.coq_name == "Flocq.IEEE754.Binary.B754_zero")
            .expect("B754_zero");
        assert_eq!(zero.clean_name_mapping, "Mathverse.Flocq.BinaryFloat.zero");
        assert_eq!(zero.category, MappingCategory::Constructor);
        let nan = m
            .iter()
            .find(|t| t.coq_name == "Flocq.IEEE754.Binary.B754_nan")
            .expect("B754_nan");
        assert_eq!(nan.clean_name_mapping, "Mathverse.Flocq.BinaryFloat.nan");
    }

    #[test]
    fn test_flocq_rounding_modes() {
        let m = flocq_mappings();
        let floor = m
            .iter()
            .find(|t| t.coq_name == "Flocq.Core.Zaux.Zfloor")
            .expect("Zfloor");
        assert_eq!(floor.clean_name_mapping, "Mathverse.Flocq.RoundFloor");
        let ceil = m
            .iter()
            .find(|t| t.coq_name == "Flocq.Core.Zaux.Zceil")
            .expect("Zceil");
        assert_eq!(ceil.clean_name_mapping, "Mathverse.Flocq.RoundCeil");
    }

    // --- Expanded MathComp tests ---

    #[test]
    fn test_mathcomp_ssrnat() {
        let m = mathcomp_mappings();
        let addn = m
            .iter()
            .find(|t| t.coq_name == "ssrnat.addn")
            .expect("addn");
        assert_eq!(addn.clean_name_mapping, "Mathverse.MathComp.Addn");
        assert_eq!(addn.category, MappingCategory::Arithmetic);
        let leq = m.iter().find(|t| t.coq_name == "ssrnat.leq").expect("leq");
        assert_eq!(leq.category, MappingCategory::Comparison);
    }

    #[test]
    fn test_mathcomp_bigop() {
        let m = mathcomp_mappings();
        let bigop = m
            .iter()
            .find(|t| t.coq_name == "bigop.bigop")
            .expect("bigop");
        assert_eq!(bigop.clean_name_mapping, "Mathverse.MathComp.BigOp");
    }

    #[test]
    fn test_mathcomp_no_duplicate_coq_names() {
        let m = mathcomp_mappings();
        let mut seen = hashbrown::HashSet::new();
        for t in m {
            assert!(
                seen.insert(t.coq_name),
                "duplicate MathComp coq_name: {}",
                t.coq_name
            );
        }
    }

    #[test]
    fn test_flocq_no_duplicate_coq_names() {
        let m = flocq_mappings();
        let mut seen = hashbrown::HashSet::new();
        for t in m {
            assert!(
                seen.insert(t.coq_name),
                "duplicate Flocq coq_name: {}",
                t.coq_name
            );
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ALL TRUST VALUE & PROOF-LAYER TYPES ARE CLEAN TYPES — trust-ir's constant and
//! proof enums (first-party/trust-ir/crates/trust-ir/src/{constant.rs,proof.rs})
//! modeled faithfully in Clean and proven down to the 3 foundational axioms.
//!
//! The value/proof companion to `tyfull_e2e.rs`/`tyall_e2e.rs` (the `Ty` type enum)
//! and `inst_types_e2e.rs` (the `Inst` instruction enums). Three namespaces:
//!
//!   * `ValConstant`   — the 13-variant `Constant` enum, with scalar/aggregate/
//!       callable/addr/phantom kind classifiers + disjointness + coverage.
//!   * `ValProofAnn`   — `ProofAnnotation`, with the documented 10-category
//!       taxonomy (memory/arith/functional/concurrency/mem-role/parallel/nn/
//!       aliasing/safety/extensible) + the GPU-safety predicate family
//!       (Pure+NoPanic+Deterministic = `Function::is_safe_for_gpu`).
//!   * `ValProofInfra` — `ProofStatus` as the ASSURANCE LADDER (Certified is the
//!       top, the kernel-checked tier; Trusted the weakest resolved) + `ProofEvidence`
//!       (machine-checked vs Trusted; `CleanCic` = the unique kernel-certified
//!       evidence, the `trust_certify` path) + `ObligationKind` categories.
//!
//! Classifiers tied to a literal Rust method match the body; category/taxonomy
//! classifiers match the trust-ir doc-comments + CLAUDE.md tables. Every theorem
//! passes the `axiom_deps(name).is_empty()` bedrock gate. All three slices
//! elaborate together in one environment.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const VALUEPROOF_SOURCE: &str = r#"

-- ###########################################################################
-- Constant enum (constant.rs:7, 13 variants) — scalar/aggregate/callable/addr/phantom kind taxonomy
-- ###########################################################################
namespace ValConstant

-- A faithful Clean image of trust-ir `Constant` (constant.rs:7), 13 variants in
-- DECLARATION ORDER, each modeled as a NULLARY tag. The i128 / f64 / Vec<...> /
-- FuncId / String / addend payloads do NOT affect the kind classifiers (which
-- match only on the outer constructor), so they are dropped — exactly as the
-- payload-free instruction tags are dropped in inst_types_e2e.rs::InstK.
--   cint        = Int(i128)
--   cfloat      = Float(f64)
--   cbool       = Bool(bool)
--   caggregate  = Aggregate(Vec<Constant>)
--   carray      = Array(Vec<Constant>)
--   cvector     = Vector(Vec<Constant>)
--   csequence   = Sequence(Vec<Constant>)
--   cset        = Set(Vec<Constant>)
--   crecord     = Record(Vec<(String, Constant)>)
--   cclosure    = Closure { func, captures }
--   cfndef      = FnDef(FuncId)
--   csymboladdr = SymbolAddr { symbol, addend }
--   cphantom    = PhantomData
inductive ConstK where
  | cint : ConstK
  | cfloat : ConstK
  | cbool : ConstK
  | caggregate : ConstK
  | carray : ConstK
  | cvector : ConstK
  | csequence : ConstK
  | cset : ConstK
  | crecord : ConstK
  | cclosure : ConstK
  | cfndef : ConstK
  | csymboladdr : ConstK
  | cphantom : ConstK

-- ===========================================================================
-- KIND CLASSIFIERS. `Constant` exposes NO `is_*` method in constant.rs, so these
-- four (plus isPhantomConst) are the DOCUMENTED STRUCTURE TAXONOMY: scalar (the
-- three primitive payloads), aggregate (the six "mirrors Ty::Array/Vector/
-- Sequence/Set/Record + the legacy Aggregate" composite literals), callable (the
-- two function-valued constants Closure/FnDef), addr (the one link-time-relocated
-- SymbolAddr), with PhantomData the zero-size unit. Each is a 13-minor
-- @ConstK.casesOn over bare Bool literals (all ctors nullary), DECLARATION ORDER:
--   cint cfloat cbool caggregate carray cvector csequence cset crecord
--   cclosure cfndef csymboladdr cphantom
-- ===========================================================================

-- isScalarConst: the primitive scalar payloads — Int, Float, Bool.
def isScalarConst : ConstK -> Bool := fun c =>
  @ConstK.casesOn (fun _ => Bool) c
    true true true                       -- cint cfloat cbool
    false false false false false false  -- caggregate carray cvector csequence cset crecord
    false false                          -- cclosure cfndef
    false                                -- csymboladdr
    false                                -- cphantom

-- isAggregateConst: the composite literals — Aggregate, Array, Vector, Sequence,
-- Set, Record (each "mirrors Ty::..." per constant.rs).
def isAggregateConst : ConstK -> Bool := fun c =>
  @ConstK.casesOn (fun _ => Bool) c
    false false false                    -- cint cfloat cbool
    true true true true true true        -- caggregate carray cvector csequence cset crecord
    false false                          -- cclosure cfndef
    false                                -- csymboladdr
    false                                -- cphantom

-- isCallableConst: the function-valued constants — Closure (captured env) and
-- FnDef (bare function item).
def isCallableConst : ConstK -> Bool := fun c =>
  @ConstK.casesOn (fun _ => Bool) c
    false false false                    -- cint cfloat cbool
    false false false false false false  -- caggregate carray cvector csequence cset crecord
    true true                            -- cclosure cfndef
    false                                -- csymboladdr
    false                                -- cphantom

-- isAddrConst: the one link-time-relocated address constant — SymbolAddr.
def isAddrConst : ConstK -> Bool := fun c =>
  @ConstK.casesOn (fun _ => Bool) c
    false false false                    -- cint cfloat cbool
    false false false false false false  -- caggregate carray cvector csequence cset crecord
    false false                          -- cclosure cfndef
    true                                 -- csymboladdr
    false                                -- cphantom

-- isPhantomConst: the zero-size PhantomData unit constant.
def isPhantomConst : ConstK -> Bool := fun c =>
  @ConstK.casesOn (fun _ => Bool) c
    false false false                    -- cint cfloat cbool
    false false false false false false  -- caggregate carray cvector csequence cset crecord
    false false                          -- cclosure cfndef
    false                                -- csymboladdr
    true                                 -- cphantom

-- ===========================================================================
-- FAITHFULNESS: isScalarConst — exactly cint/cfloat/cbool, all 13 by casesOn iota.
-- ===========================================================================
theorem cst_isScalarConst_cint : isScalarConst ConstK.cint = true := rfl
theorem cst_isScalarConst_cfloat : isScalarConst ConstK.cfloat = true := rfl
theorem cst_isScalarConst_cbool : isScalarConst ConstK.cbool = true := rfl
theorem cst_isScalarConst_caggregate : isScalarConst ConstK.caggregate = false := rfl
theorem cst_isScalarConst_carray : isScalarConst ConstK.carray = false := rfl
theorem cst_isScalarConst_cvector : isScalarConst ConstK.cvector = false := rfl
theorem cst_isScalarConst_csequence : isScalarConst ConstK.csequence = false := rfl
theorem cst_isScalarConst_cset : isScalarConst ConstK.cset = false := rfl
theorem cst_isScalarConst_crecord : isScalarConst ConstK.crecord = false := rfl
theorem cst_isScalarConst_cclosure : isScalarConst ConstK.cclosure = false := rfl
theorem cst_isScalarConst_cfndef : isScalarConst ConstK.cfndef = false := rfl
theorem cst_isScalarConst_csymboladdr : isScalarConst ConstK.csymboladdr = false := rfl
theorem cst_isScalarConst_cphantom : isScalarConst ConstK.cphantom = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isAggregateConst — exactly the six composite literals.
-- ===========================================================================
theorem cst_isAggregateConst_cint : isAggregateConst ConstK.cint = false := rfl
theorem cst_isAggregateConst_cfloat : isAggregateConst ConstK.cfloat = false := rfl
theorem cst_isAggregateConst_cbool : isAggregateConst ConstK.cbool = false := rfl
theorem cst_isAggregateConst_caggregate : isAggregateConst ConstK.caggregate = true := rfl
theorem cst_isAggregateConst_carray : isAggregateConst ConstK.carray = true := rfl
theorem cst_isAggregateConst_cvector : isAggregateConst ConstK.cvector = true := rfl
theorem cst_isAggregateConst_csequence : isAggregateConst ConstK.csequence = true := rfl
theorem cst_isAggregateConst_cset : isAggregateConst ConstK.cset = true := rfl
theorem cst_isAggregateConst_crecord : isAggregateConst ConstK.crecord = true := rfl
theorem cst_isAggregateConst_cclosure : isAggregateConst ConstK.cclosure = false := rfl
theorem cst_isAggregateConst_cfndef : isAggregateConst ConstK.cfndef = false := rfl
theorem cst_isAggregateConst_csymboladdr : isAggregateConst ConstK.csymboladdr = false := rfl
theorem cst_isAggregateConst_cphantom : isAggregateConst ConstK.cphantom = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isCallableConst — exactly cclosure/cfndef.
-- ===========================================================================
theorem cst_isCallableConst_cint : isCallableConst ConstK.cint = false := rfl
theorem cst_isCallableConst_cfloat : isCallableConst ConstK.cfloat = false := rfl
theorem cst_isCallableConst_cbool : isCallableConst ConstK.cbool = false := rfl
theorem cst_isCallableConst_caggregate : isCallableConst ConstK.caggregate = false := rfl
theorem cst_isCallableConst_carray : isCallableConst ConstK.carray = false := rfl
theorem cst_isCallableConst_cvector : isCallableConst ConstK.cvector = false := rfl
theorem cst_isCallableConst_csequence : isCallableConst ConstK.csequence = false := rfl
theorem cst_isCallableConst_cset : isCallableConst ConstK.cset = false := rfl
theorem cst_isCallableConst_crecord : isCallableConst ConstK.crecord = false := rfl
theorem cst_isCallableConst_cclosure : isCallableConst ConstK.cclosure = true := rfl
theorem cst_isCallableConst_cfndef : isCallableConst ConstK.cfndef = true := rfl
theorem cst_isCallableConst_csymboladdr : isCallableConst ConstK.csymboladdr = false := rfl
theorem cst_isCallableConst_cphantom : isCallableConst ConstK.cphantom = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isAddrConst — exactly csymboladdr.
-- ===========================================================================
theorem cst_isAddrConst_cint : isAddrConst ConstK.cint = false := rfl
theorem cst_isAddrConst_cfloat : isAddrConst ConstK.cfloat = false := rfl
theorem cst_isAddrConst_cbool : isAddrConst ConstK.cbool = false := rfl
theorem cst_isAddrConst_caggregate : isAddrConst ConstK.caggregate = false := rfl
theorem cst_isAddrConst_carray : isAddrConst ConstK.carray = false := rfl
theorem cst_isAddrConst_cvector : isAddrConst ConstK.cvector = false := rfl
theorem cst_isAddrConst_csequence : isAddrConst ConstK.csequence = false := rfl
theorem cst_isAddrConst_cset : isAddrConst ConstK.cset = false := rfl
theorem cst_isAddrConst_crecord : isAddrConst ConstK.crecord = false := rfl
theorem cst_isAddrConst_cclosure : isAddrConst ConstK.cclosure = false := rfl
theorem cst_isAddrConst_cfndef : isAddrConst ConstK.cfndef = false := rfl
theorem cst_isAddrConst_csymboladdr : isAddrConst ConstK.csymboladdr = true := rfl
theorem cst_isAddrConst_cphantom : isAddrConst ConstK.cphantom = false := rfl

-- ===========================================================================
-- FAITHFULNESS: isPhantomConst — exactly cphantom.
-- ===========================================================================
theorem cst_isPhantomConst_cint : isPhantomConst ConstK.cint = false := rfl
theorem cst_isPhantomConst_cfloat : isPhantomConst ConstK.cfloat = false := rfl
theorem cst_isPhantomConst_cbool : isPhantomConst ConstK.cbool = false := rfl
theorem cst_isPhantomConst_caggregate : isPhantomConst ConstK.caggregate = false := rfl
theorem cst_isPhantomConst_carray : isPhantomConst ConstK.carray = false := rfl
theorem cst_isPhantomConst_cvector : isPhantomConst ConstK.cvector = false := rfl
theorem cst_isPhantomConst_csequence : isPhantomConst ConstK.csequence = false := rfl
theorem cst_isPhantomConst_cset : isPhantomConst ConstK.cset = false := rfl
theorem cst_isPhantomConst_crecord : isPhantomConst ConstK.crecord = false := rfl
theorem cst_isPhantomConst_cclosure : isPhantomConst ConstK.cclosure = false := rfl
theorem cst_isPhantomConst_cfndef : isPhantomConst ConstK.cfndef = false := rfl
theorem cst_isPhantomConst_csymboladdr : isPhantomConst ConstK.csymboladdr = false := rfl
theorem cst_isPhantomConst_cphantom : isPhantomConst ConstK.cphantom = true := rfl

-- ===========================================================================
-- DISJOINTNESS METATHEOREMS — proven over ALL 13 ctors by one all-ctor
-- @ConstK.casesOn (each of the 13 minors is `rfl`, since every ctor is nullary).
-- These say the kind families are pairwise-coherent for EVERY Constant, not just
-- the witnessed ones — structural content the per-variant rfls cannot express.
-- ===========================================================================

-- Scalar and aggregate constants are disjoint over all of Constant.
theorem cst_disjoint_scalar_aggregate (c : ConstK) :
    Bool.and (isScalarConst c) (isAggregateConst c) = false :=
  @ConstK.casesOn (fun k => Bool.and (isScalarConst k) (isAggregateConst k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Aggregate and callable constants are disjoint over all of Constant.
theorem cst_disjoint_aggregate_callable (c : ConstK) :
    Bool.and (isAggregateConst c) (isCallableConst c) = false :=
  @ConstK.casesOn (fun k => Bool.and (isAggregateConst k) (isCallableConst k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Scalar and callable constants are disjoint over all of Constant.
theorem cst_disjoint_scalar_callable (c : ConstK) :
    Bool.and (isScalarConst c) (isCallableConst c) = false :=
  @ConstK.casesOn (fun k => Bool.and (isScalarConst k) (isCallableConst k) = false) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- COVERAGE METATHEOREM — the five kinds (scalar, aggregate, callable, addr,
-- phantom) COVER every Constant: their Bool-or is `true` for all 13 ctors. This
-- is the totality statement that the taxonomy partitions the whole enum.
-- ===========================================================================
theorem cst_cover_all (c : ConstK) :
    Bool.or (Bool.or (isScalarConst c) (isAggregateConst c))
      (Bool.or (isCallableConst c) (Bool.or (isAddrConst c) (isPhantomConst c))) = true :=
  @ConstK.casesOn
    (fun k => Bool.or (Bool.or (isScalarConst k) (isAggregateConst k))
      (Bool.or (isCallableConst k) (Bool.or (isAddrConst k) (isPhantomConst k))) = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- Additional partition edges (more disjointness over all 13 ctors), pushing the
-- metatheorem count past the >=5 target and confirming addr/phantom are isolated
-- singletons in the taxonomy.
-- ===========================================================================

-- The addr constant is neither scalar nor aggregate nor callable: addr is a
-- singleton kind. Stated as `not isAddrConst || not(scalar||aggregate||callable)`.
theorem cst_addr_singleton (c : ConstK) :
    Bool.or (Bool.not (isAddrConst c))
      (Bool.not (Bool.or (Bool.or (isScalarConst c) (isAggregateConst c)) (isCallableConst c)))
      = true :=
  @ConstK.casesOn
    (fun k => Bool.or (Bool.not (isAddrConst k))
      (Bool.not (Bool.or (Bool.or (isScalarConst k) (isAggregateConst k)) (isCallableConst k)))
      = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- The phantom unit constant is isolated from every other kind: phantom singleton.
theorem cst_phantom_singleton (c : ConstK) :
    Bool.or (Bool.not (isPhantomConst c))
      (Bool.not (Bool.or (Bool.or (isScalarConst c) (isAggregateConst c))
        (Bool.or (isCallableConst c) (isAddrConst c))))
      = true :=
  @ConstK.casesOn
    (fun k => Bool.or (Bool.not (isPhantomConst k))
      (Bool.not (Bool.or (Bool.or (isScalarConst k) (isAggregateConst k))
        (Bool.or (isCallableConst k) (isAddrConst k))))
      = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end ValConstant

-- ###########################################################################
-- ProofAnnotation (proof.rs:42) — 10-category taxonomy + GPU-safety/hint predicates (Function::is_safe_for_gpu)
-- ###########################################################################
namespace ValProofAnn

-- ###########################################################################
-- ProofAnnotation (proof.rs:42) — 34 variants modeled as NULLARY tags.
-- The payload-carrying variants (pAtomicOrdering(Ordering), pBoundedOutput{lo,hi},
-- pAligned(u64), pBoundedLoop(u64), pDivergenceClass(Divergence), pCustom(ProofTag),
-- pProofRef(ProofId), pValueRange{lo,hi}, pKnownBits{zeros,ones}) are reduced to
-- nullary tags: the classifier methods (is_memory_safety / is_arithmetic_safety /
-- is_functional / is_concurrency / is_memory_role / is_parallel / is_neural_network
-- / is_aliasing, proof.rs:184-343) match only on the OUTER constructor, so payloads
-- do not affect the category. Ctors are in DECLARATION ORDER (proof.rs:44-176).
-- ###########################################################################
inductive ProofAnn where
  | pInBounds : ProofAnn
  | pNotNull : ProofAnn
  | pValidBorrow : ProofAnn
  | pUniqueBorrow : ProofAnn
  | pSharedBorrow : ProofAnn
  | pValidDealloc : ProofAnn
  | pNoOverflow : ProofAnn
  | pNoWrap : ProofAnn
  | pDivNonZero : ProofAnn
  | pShiftInRange : ProofAnn
  | pWrapping : ProofAnn
  | pPure : ProofAnn
  | pTerminates : ProofAnn
  | pDeterministic : ProofAnn
  | pAssociative : ProofAnn
  | pCommutative : ProofAnn
  | pDataRaceFree : ProofAnn
  | pAtomicOrdering : ProofAnn
  | pBoundedOutput : ProofAnn
  | pMonotonic : ProofAnn
  | pNoAlias : ProofAnn
  | pAligned : ProofAnn
  | pNoPanic : ProofAnn
  | pNoUndef : ProofAnn
  | pReadonlyTable : ProofAnn
  | pAppendOnlyBuffer : ProofAnn
  | pAtomicSetInsert : ProofAnn
  | pParallelMap : ProofAnn
  | pBoundedLoop : ProofAnn
  | pDivergenceClass : ProofAnn
  | pCustom : ProofAnn
  | pProofRef : ProofAnn
  | pValueRange : ProofAnn
  | pKnownBits : ProofAnn

-- The category lattice. 10 constructors (>=2, so this is a genuine inductive,
-- not a structure). Grounded in the CLAUDE.md proof.rs "Category" table + the
-- classifier doc-comments at proof.rs:180-343.
inductive Cat where
  | catMemory : Cat
  | catArith : Cat
  | catFunctional : Cat
  | catConcurrency : Cat
  | catMemRole : Cat
  | catParallel : Cat
  | catNN : Cat
  | catAliasing : Cat
  | catSafety : Cat
  | catExtensible : Cat

-- The classifier. category : ProofAnn -> Cat, faithful to the proof.rs table:
--   catMemory     : pInBounds pNotNull pValidBorrow pUniqueBorrow pSharedBorrow pValidDealloc
--   catArith      : pNoOverflow pNoWrap pDivNonZero pShiftInRange pWrapping
--   catFunctional : pPure pTerminates pDeterministic pAssociative pCommutative pMonotonic
--   catConcurrency: pDataRaceFree pAtomicOrdering pAtomicSetInsert
--   catNN         : pBoundedOutput
--   catAliasing   : pNoAlias pAligned
--   catSafety     : pNoPanic pNoUndef
--   catMemRole    : pReadonlyTable pAppendOnlyBuffer
--   catParallel   : pParallelMap pBoundedLoop pDivergenceClass
--   catExtensible : pCustom pProofRef pValueRange pKnownBits
-- GROUNDING NOTE: this is a documented TAXONOMY (the proof.rs classifier family),
-- not a single Rust method — pMonotonic is grouped with catFunctional per the
-- CLAUDE.md table even though is_neural_network also names BoundedOutput+Monotonic;
-- we choose the functional placement (one-category-per-variant total function) and
-- say so. The 34 minors below are in DECLARATION ORDER.
def category : ProofAnn -> Cat := fun a =>
  @ProofAnn.casesOn (fun _ => Cat) a
    Cat.catMemory       -- pInBounds
    Cat.catMemory       -- pNotNull
    Cat.catMemory       -- pValidBorrow
    Cat.catMemory       -- pUniqueBorrow
    Cat.catMemory       -- pSharedBorrow
    Cat.catMemory       -- pValidDealloc
    Cat.catArith        -- pNoOverflow
    Cat.catArith        -- pNoWrap
    Cat.catArith        -- pDivNonZero
    Cat.catArith        -- pShiftInRange
    Cat.catArith        -- pWrapping
    Cat.catFunctional   -- pPure
    Cat.catFunctional   -- pTerminates
    Cat.catFunctional   -- pDeterministic
    Cat.catFunctional   -- pAssociative
    Cat.catFunctional   -- pCommutative
    Cat.catConcurrency  -- pDataRaceFree
    Cat.catConcurrency  -- pAtomicOrdering
    Cat.catNN           -- pBoundedOutput
    Cat.catFunctional   -- pMonotonic
    Cat.catAliasing     -- pNoAlias
    Cat.catAliasing     -- pAligned
    Cat.catSafety       -- pNoPanic
    Cat.catSafety       -- pNoUndef
    Cat.catMemRole      -- pReadonlyTable
    Cat.catMemRole      -- pAppendOnlyBuffer
    Cat.catConcurrency  -- pAtomicSetInsert
    Cat.catParallel     -- pParallelMap
    Cat.catParallel     -- pBoundedLoop
    Cat.catParallel     -- pDivergenceClass
    Cat.catExtensible   -- pCustom
    Cat.catExtensible   -- pProofRef
    Cat.catExtensible   -- pValueRange
    Cat.catExtensible   -- pKnownBits

-- Decidable equality on Cat (a 10x10 casesOn-of-casesOn). Used to build Bool
-- category predicates (isMemoryAnn / isArithAnn / isFunctionalAnn).
def eqCat : Cat -> Cat -> Bool := fun x y =>
  @Cat.casesOn (fun _ => Bool) x
    (@Cat.casesOn (fun _ => Bool) y true false false false false false false false false false)
    (@Cat.casesOn (fun _ => Bool) y false true false false false false false false false false)
    (@Cat.casesOn (fun _ => Bool) y false false true false false false false false false false)
    (@Cat.casesOn (fun _ => Bool) y false false false true false false false false false false)
    (@Cat.casesOn (fun _ => Bool) y false false false false true false false false false false)
    (@Cat.casesOn (fun _ => Bool) y false false false false false true false false false false)
    (@Cat.casesOn (fun _ => Bool) y false false false false false false true false false false)
    (@Cat.casesOn (fun _ => Bool) y false false false false false false false true false false)
    (@Cat.casesOn (fun _ => Bool) y false false false false false false false false true false)
    (@Cat.casesOn (fun _ => Bool) y false false false false false false false false false true)

-- Bool category predicates via eqCat (the "catBool" helpers the metatheorems use).
def isMemoryAnn : ProofAnn -> Bool := fun a => eqCat (category a) Cat.catMemory
def isArithAnn : ProofAnn -> Bool := fun a => eqCat (category a) Cat.catArith
def isFunctionalAnn : ProofAnn -> Bool := fun a => eqCat (category a) Cat.catFunctional
def isSafetyAnn : ProofAnn -> Bool := fun a => eqCat (category a) Cat.catSafety

-- The documented `Function::is_safe_for_gpu` predicate (CLAUDE.md gpu_proofs +
-- designs/2026-04-18 §3.2): a function is GPU-safe iff it carries Pure + NoPanic
-- + Deterministic. Per-ANNOTATION witness: isGpuSafetyAnn is true exactly for the
-- three member annotations pPure / pNoPanic / pDeterministic.
def isGpuSafetyAnn : ProofAnn -> Bool := fun a =>
  @ProofAnn.casesOn (fun _ => Bool) a
    false   -- pInBounds
    false   -- pNotNull
    false   -- pValidBorrow
    false   -- pUniqueBorrow
    false   -- pSharedBorrow
    false   -- pValidDealloc
    false   -- pNoOverflow
    false   -- pNoWrap
    false   -- pDivNonZero
    false   -- pShiftInRange
    false   -- pWrapping
    true    -- pPure           (GPU-safe)
    false   -- pTerminates
    true    -- pDeterministic  (GPU-safe)
    false   -- pAssociative
    false   -- pCommutative
    false   -- pDataRaceFree
    false   -- pAtomicOrdering
    false   -- pBoundedOutput
    false   -- pMonotonic
    false   -- pNoAlias
    false   -- pAligned
    true    -- pNoPanic        (GPU-safe)
    false   -- pNoUndef
    false   -- pReadonlyTable
    false   -- pAppendOnlyBuffer
    false   -- pAtomicSetInsert
    false   -- pParallelMap
    false   -- pBoundedLoop
    false   -- pDivergenceClass
    false   -- pCustom
    false   -- pProofRef
    false   -- pValueRange
    false   -- pKnownBits

-- The `gpu_proofs` hint family (CLAUDE.md: memory-role hints + ParallelMap +
-- BoundedLoop + DivergenceClass). isGpuHint is true exactly for the six hint
-- annotations pReadonlyTable / pAppendOnlyBuffer / pAtomicSetInsert / pParallelMap
-- / pBoundedLoop / pDivergenceClass.
def isGpuHint : ProofAnn -> Bool := fun a =>
  @ProofAnn.casesOn (fun _ => Bool) a
    false   -- pInBounds
    false   -- pNotNull
    false   -- pValidBorrow
    false   -- pUniqueBorrow
    false   -- pSharedBorrow
    false   -- pValidDealloc
    false   -- pNoOverflow
    false   -- pNoWrap
    false   -- pDivNonZero
    false   -- pShiftInRange
    false   -- pWrapping
    false   -- pPure
    false   -- pTerminates
    false   -- pDeterministic
    false   -- pAssociative
    false   -- pCommutative
    false   -- pDataRaceFree
    false   -- pAtomicOrdering
    false   -- pBoundedOutput
    false   -- pMonotonic
    false   -- pNoAlias
    false   -- pAligned
    false   -- pNoPanic
    false   -- pNoUndef
    true    -- pReadonlyTable     (memory-role hint)
    true    -- pAppendOnlyBuffer  (memory-role hint)
    true    -- pAtomicSetInsert   (memory-role hint)
    true    -- pParallelMap       (parallel hint)
    true    -- pBoundedLoop       (parallel hint)
    true    -- pDivergenceClass   (parallel hint)
    false   -- pCustom
    false   -- pProofRef
    false   -- pValueRange
    false   -- pKnownBits

-- ===========================================================================
-- FAITHFULNESS: category on a REPRESENTATIVE of every category (one per cat min).
-- Each is a casesOn iota = rfl, after eqCat-reducing to a Bool to compare Cats.
-- We compare via eqCat so the equation reduces by iota on literal ctors.
-- ===========================================================================
theorem pann_cat_memory_rep : eqCat (category ProofAnn.pInBounds) Cat.catMemory = true := rfl
theorem pann_cat_arith_rep : eqCat (category ProofAnn.pNoOverflow) Cat.catArith = true := rfl
theorem pann_cat_functional_rep : eqCat (category ProofAnn.pPure) Cat.catFunctional = true := rfl
theorem pann_cat_concurrency_rep : eqCat (category ProofAnn.pDataRaceFree) Cat.catConcurrency = true := rfl
theorem pann_cat_memrole_rep : eqCat (category ProofAnn.pReadonlyTable) Cat.catMemRole = true := rfl
theorem pann_cat_parallel_rep : eqCat (category ProofAnn.pParallelMap) Cat.catParallel = true := rfl
theorem pann_cat_nn_rep : eqCat (category ProofAnn.pBoundedOutput) Cat.catNN = true := rfl
theorem pann_cat_aliasing_rep : eqCat (category ProofAnn.pNoAlias) Cat.catAliasing = true := rfl
theorem pann_cat_safety_rep : eqCat (category ProofAnn.pNoPanic) Cat.catSafety = true := rfl
theorem pann_cat_extensible_rep : eqCat (category ProofAnn.pCustom) Cat.catExtensible = true := rfl

-- Extra category witnesses (the concurrency-grouped memory-role variant
-- pAtomicSetInsert is catConcurrency, NOT catMemRole — faithful to proof.rs:264).
theorem pann_cat_atomicsetinsert_concurrency :
    eqCat (category ProofAnn.pAtomicSetInsert) Cat.catConcurrency = true := rfl
-- pMonotonic groups with catFunctional (our chosen placement, see GROUNDING NOTE).
theorem pann_cat_monotonic_functional :
    eqCat (category ProofAnn.pMonotonic) Cat.catFunctional = true := rfl

-- ===========================================================================
-- FAITHFULNESS: isGpuSafetyAnn — true on the three members, false on a non-member.
-- ===========================================================================
theorem pann_gpusafety_pure : isGpuSafetyAnn ProofAnn.pPure = true := rfl
theorem pann_gpusafety_nopanic : isGpuSafetyAnn ProofAnn.pNoPanic = true := rfl
theorem pann_gpusafety_deterministic : isGpuSafetyAnn ProofAnn.pDeterministic = true := rfl
theorem pann_gpusafety_inbounds_false : isGpuSafetyAnn ProofAnn.pInBounds = false := rfl
theorem pann_gpusafety_terminates_false : isGpuSafetyAnn ProofAnn.pTerminates = false := rfl
theorem pann_gpusafety_nooverflow_false : isGpuSafetyAnn ProofAnn.pNoOverflow = false := rfl

-- FAITHFULNESS: isGpuHint — true on the six hint members, false on a non-member.
theorem pann_gpuhint_readonlytable : isGpuHint ProofAnn.pReadonlyTable = true := rfl
theorem pann_gpuhint_appendonly : isGpuHint ProofAnn.pAppendOnlyBuffer = true := rfl
theorem pann_gpuhint_atomicsetinsert : isGpuHint ProofAnn.pAtomicSetInsert = true := rfl
theorem pann_gpuhint_parallelmap : isGpuHint ProofAnn.pParallelMap = true := rfl
theorem pann_gpuhint_boundedloop : isGpuHint ProofAnn.pBoundedLoop = true := rfl
theorem pann_gpuhint_divergenceclass : isGpuHint ProofAnn.pDivergenceClass = true := rfl
theorem pann_gpuhint_pure_false : isGpuHint ProofAnn.pPure = false := rfl
theorem pann_gpuhint_inbounds_false : isGpuHint ProofAnn.pInBounds = false := rfl

-- ===========================================================================
-- METATHEOREM 1 — every GPU-safety annotation is FUNCTIONAL-or-SAFETY: for all a,
-- isGpuSafetyAnn a = true -> (isFunctionalAnn a || isSafetyAnn a) = true. Encoded
-- over Bool as `or (not isGpuSafetyAnn) (isFunctionalAnn || isSafetyAnn) = true`.
-- FAITHFULNESS NOTE: the `is_safe_for_gpu` members are Pure + Deterministic (both
-- catFunctional) AND NoPanic (catSafety, proof.rs:511) — so the honest invariant
-- is functional OR safety, not functional alone (pNoPanic lives under the Safety
-- category in the proof.rs table). Proven by a 34-ctor casesOn (each minor rfl).
-- ===========================================================================
theorem pann_gpusafety_implies_functional_or_safety (a : ProofAnn) :
    Bool.or (Bool.not (isGpuSafetyAnn a)) (Bool.or (isFunctionalAnn a) (isSafetyAnn a)) = true :=
  @ProofAnn.casesOn
    (fun k => Bool.or (Bool.not (isGpuSafetyAnn k)) (Bool.or (isFunctionalAnn k) (isSafetyAnn k)) = true) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- METATHEOREM 1b — every FUNCTIONAL annotation is NOT a GPU hint (the
-- `is_safe_for_gpu` predicate and the `gpu_proofs` hint family are about different
-- categories): isFunctionalAnn a = true -> isGpuHint a = false, encoded
-- `or (not isFunctionalAnn) (not isGpuHint) = true`. 34-ctor casesOn.
theorem pann_functional_not_gpuhint (a : ProofAnn) :
    Bool.or (Bool.not (isFunctionalAnn a)) (Bool.not (isGpuHint a)) = true :=
  @ProofAnn.casesOn
    (fun k => Bool.or (Bool.not (isFunctionalAnn k)) (Bool.not (isGpuHint k)) = true) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 2 — the memory and arithmetic category samples are DISJOINT:
-- for all a, and (isMemoryAnn a) (isArithAnn a) = false. No annotation is both a
-- memory-safety and an arithmetic-safety annotation. 34-ctor casesOn.
-- ===========================================================================
theorem pann_memory_arith_disjoint (a : ProofAnn) :
    Bool.and (isMemoryAnn a) (isArithAnn a) = false :=
  @ProofAnn.casesOn (fun k => Bool.and (isMemoryAnn k) (isArithAnn k) = false) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 3 — memory and functional category samples are DISJOINT.
-- ===========================================================================
theorem pann_memory_functional_disjoint (a : ProofAnn) :
    Bool.and (isMemoryAnn a) (isFunctionalAnn a) = false :=
  @ProofAnn.casesOn (fun k => Bool.and (isMemoryAnn k) (isFunctionalAnn k) = false) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 4 — arithmetic and functional category samples are DISJOINT.
-- ===========================================================================
theorem pann_arith_functional_disjoint (a : ProofAnn) :
    Bool.and (isArithAnn a) (isFunctionalAnn a) = false :=
  @ProofAnn.casesOn (fun k => Bool.and (isArithAnn k) (isFunctionalAnn k) = false) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 5 — eqCat is REFLEXIVE on every category: for all c, eqCat c c =
-- true. This is what makes the category predicates well-behaved (an annotation is
-- always in its own category). 10-ctor casesOn over Cat.
-- ===========================================================================
theorem pann_eqCat_refl (c : Cat) : eqCat c c = true :=
  @Cat.casesOn (fun k => eqCat k k = true) c
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 6 — every GPU-safety annotation is DISJOINT from the arithmetic
-- category (sharper structural fact): no `is_safe_for_gpu` member is an arithmetic
-- annotation. isGpuSafetyAnn a = true -> isArithAnn a = false, encoded
-- `or (not isGpuSafetyAnn) (not isArithAnn) = true`. 34-ctor casesOn.
-- ===========================================================================
theorem pann_gpusafety_not_arith (a : ProofAnn) :
    Bool.or (Bool.not (isGpuSafetyAnn a)) (Bool.not (isArithAnn a)) = true :=
  @ProofAnn.casesOn
    (fun k => Bool.or (Bool.not (isGpuSafetyAnn k)) (Bool.not (isArithAnn k)) = true) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

-- ===========================================================================
-- METATHEOREM 7 — GPU-safety and GPU-hint families are DISJOINT: no annotation is
-- both a `is_safe_for_gpu` member AND a `gpu_proofs` hint (the safety predicate is
-- functional/safety annotations; the hints are memory-role + parallel). For all a,
-- and (isGpuSafetyAnn a) (isGpuHint a) = false. 34-ctor casesOn.
-- ===========================================================================
theorem pann_gpusafety_gpuhint_disjoint (a : ProofAnn) :
    Bool.and (isGpuSafetyAnn a) (isGpuHint a) = false :=
  @ProofAnn.casesOn (fun k => Bool.and (isGpuSafetyAnn k) (isGpuHint k) = false) a
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl

end ValProofAnn

-- ###########################################################################
-- proof-infra: ProofStatus (assurance ladder, Certified top) + ProofEvidence (machine-checked vs Trusted; CleanCic=kernel-certified) + ObligationKind categories
-- ###########################################################################
namespace ValProofInfra

-- ###########################################################################
-- ProofStatus (proof.rs:412) — 5 ctors, the assurance ladder.
-- ###########################################################################

-- A faithful Clean image of trust-ir `ProofStatus` (proof.rs:412). 5 nullary
-- ctors in DECLARATION ORDER (Pending, Discharged, Failed, Trusted, Certified;
-- prefixed `s` to stay distinct from the evidence/kind tags). The casesOn minors
-- below follow this exact order. The proof.rs doc-comment fixes the semantics:
-- `Certified` is "strictly stronger than `Trusted`" — kernel-checkable CIC vs.
-- a manual audit taken on faith.
inductive ProofStatus where
  | sPending : ProofStatus
  | sDischarged : ProofStatus
  | sFailed : ProofStatus
  | sTrusted : ProofStatus
  | sCertified : ProofStatus

-- isResolved: a status that closes its obligation. Discharged (proved),
-- Trusted (audited), Certified (kernel-checked) are RESOLVED; Pending (open)
-- and Failed (refuted/unprovable) are NOT. (Grounded in the proof.rs status
-- semantics: Pending/Failed are the two non-closing states.)
def isResolved : ProofStatus -> Bool := fun s =>
  @ProofStatus.casesOn (fun _ => Bool) s
    false   -- sPending      (open)
    true    -- sDischarged   (proved)
    false   -- sFailed       (refuted / unprovable)
    true    -- sTrusted      (manual audit)
    true    -- sCertified    (kernel-checked CIC)

-- assuranceRank: the STRENGTH of a resolved status (NOT a literal Rust method —
-- this encodes the documented assurance ladder). The two NON-resolved states
-- carry no assurance (rank 0): sFailed = 0, sPending = 0. Among the resolved
-- states, sTrusted is the WEAKEST (manual audit taken on faith) = 1, sDischarged
-- (a discharged proof obligation) = 2, and sCertified is the STRONGEST
-- (kernel-re-checkable CIC term, "strictly stronger than Trusted") = 3.
def assuranceRank : ProofStatus -> Nat := fun s =>
  @ProofStatus.casesOn (fun _ => Nat) s
    (0)    -- sPending
    (2)    -- sDischarged
    (0)    -- sFailed
    (1)    -- sTrusted
    (3)    -- sCertified

-- s is no stronger than t iff assuranceRank s <= assuranceRank t (Nat.ble).
def assuranceLE : ProofStatus -> ProofStatus -> Bool := fun s t =>
  Nat.ble (assuranceRank s) (assuranceRank t)

-- ===========================================================================
-- FAITHFULNESS: isResolved, per variant (casesOn iota = rfl).
-- ===========================================================================
theorem pinf_isResolved_sPending : isResolved ProofStatus.sPending = false := rfl
theorem pinf_isResolved_sDischarged : isResolved ProofStatus.sDischarged = true := rfl
theorem pinf_isResolved_sFailed : isResolved ProofStatus.sFailed = false := rfl
theorem pinf_isResolved_sTrusted : isResolved ProofStatus.sTrusted = true := rfl
theorem pinf_isResolved_sCertified : isResolved ProofStatus.sCertified = true := rfl

-- ===========================================================================
-- FAITHFULNESS: assuranceRank, per variant.
-- ===========================================================================
theorem pinf_assuranceRank_sPending : assuranceRank ProofStatus.sPending = 0 := rfl
theorem pinf_assuranceRank_sDischarged : assuranceRank ProofStatus.sDischarged = 2 := rfl
theorem pinf_assuranceRank_sFailed : assuranceRank ProofStatus.sFailed = 0 := rfl
theorem pinf_assuranceRank_sTrusted : assuranceRank ProofStatus.sTrusted = 1 := rfl
theorem pinf_assuranceRank_sCertified : assuranceRank ProofStatus.sCertified = 3 := rfl

-- Certified outranks Trusted (the proof.rs "strictly stronger" doc-comment).
theorem pinf_certified_above_trusted :
    assuranceLE ProofStatus.sTrusted ProofStatus.sCertified = true := rfl
-- ...and Trusted is NOT as strong as Certified (the order is genuine, not trivial).
theorem pinf_trusted_not_above_certified :
    assuranceLE ProofStatus.sCertified ProofStatus.sTrusted = false := rfl
-- Discharged outranks Trusted.
theorem pinf_discharged_above_trusted :
    assuranceLE ProofStatus.sTrusted ProofStatus.sDischarged = true := rfl

-- ===========================================================================
-- METATHEOREMS over ProofStatus (all-ctor @casesOn; 5 nullary minors -> rfl).
-- ===========================================================================

-- assuranceLE is REFLEXIVE: every status is no stronger than itself.
theorem pinf_assuranceLE_refl (s : ProofStatus) : assuranceLE s s = true :=
  @ProofStatus.casesOn (fun k => assuranceLE k k = true) s
    rfl rfl rfl rfl rfl

-- sCertified is the TOP element: every status is no stronger than Certified.
theorem pinf_certified_is_top (s : ProofStatus) :
    assuranceLE s ProofStatus.sCertified = true :=
  @ProofStatus.casesOn (fun k => assuranceLE k ProofStatus.sCertified = true) s
    rfl rfl rfl rfl rfl

-- Certified is resolved (it closes the obligation, at the strongest tier).
theorem pinf_certified_is_resolved : isResolved ProofStatus.sCertified = true := rfl

-- ===========================================================================
-- ProofEvidence (proof.rs:630) — 8 ctors, how an obligation was discharged.
-- ###########################################################################
-- A faithful Clean image of trust-ir `ProofEvidence` (proof.rs:630). The 8
-- variants carry payloads (proof bytes, layer counts, digests, ...) that the
-- classifiers below do NOT inspect — each matches only the outer ctor TAG — so
-- they are modeled as nullary tags in DECLARATION ORDER:
--   SmtProof LeanProof KaniHarness GammaCrownBound TranslationValidation
--   Trusted InheritedFromCallee CleanCic
-- (prefixed `e` to stay distinct from the status/kind tags).
inductive ProofEvidence where
  | eSmtProof : ProofEvidence
  | eLeanProof : ProofEvidence
  | eKaniHarness : ProofEvidence
  | eGammaCrownBound : ProofEvidence
  | eTranslationValidation : ProofEvidence
  | eTrusted : ProofEvidence
  | eInheritedFromCallee : ProofEvidence
  | eCleanCic : ProofEvidence

-- isMachineChecked: evidence backed by a MACHINE artifact that a tool produced /
-- can re-check — SmtProof (ay), LeanProof (Lean term), KaniHarness (Kani),
-- GammaCrownBound (NN verifier), TranslationValidation (pass validator), CleanCic
-- (kernel CIC term). NOT machine-checked: eTrusted (manual audit "taken on faith"
-- per proof.rs) and eInheritedFromCallee (a composition reference, "*not*
-- self-justifying evidence" per the proof.rs doc-comment). (Grounded in the
-- proof.rs evidence doc-comments + the CLAUDE.md ProofEvidence table.)
def isMachineChecked : ProofEvidence -> Bool := fun e =>
  @ProofEvidence.casesOn (fun _ => Bool) e
    true    -- eSmtProof              (ay SMT proof)
    true    -- eLeanProof             (Lean 4 proof term)
    true    -- eKaniHarness           (Kani harness)
    true    -- eGammaCrownBound       (NN verifier bound)
    true    -- eTranslationValidation (pass validator)
    false   -- eTrusted               (manual audit, taken on faith)
    false   -- eInheritedFromCallee   (composition ref, not self-justifying)
    true    -- eCleanCic              (kernel-checkable CIC term)

-- isKernelCertified: evidence that is the kernel-checked Clean CIC term — the
-- STRONGEST evidence, the trust_certify path (proof.rs: "*re-checked* by a CIC
-- kernel, not trusted"). Only eCleanCic qualifies; every other evidence form
-- (even a Lean term) is not, here, a re-checkable Clean kernel object.
def isKernelCertified : ProofEvidence -> Bool := fun e =>
  @ProofEvidence.casesOn (fun _ => Bool) e
    false   -- eSmtProof
    false   -- eLeanProof
    false   -- eKaniHarness
    false   -- eGammaCrownBound
    false   -- eTranslationValidation
    false   -- eTrusted
    false   -- eInheritedFromCallee
    true    -- eCleanCic              (the unique kernel-certified evidence)

-- ===========================================================================
-- FAITHFULNESS: isMachineChecked, per variant.
-- ===========================================================================
theorem pinf_isMachineChecked_eSmtProof : isMachineChecked ProofEvidence.eSmtProof = true := rfl
theorem pinf_isMachineChecked_eLeanProof : isMachineChecked ProofEvidence.eLeanProof = true := rfl
theorem pinf_isMachineChecked_eKaniHarness : isMachineChecked ProofEvidence.eKaniHarness = true := rfl
theorem pinf_isMachineChecked_eGammaCrownBound : isMachineChecked ProofEvidence.eGammaCrownBound = true := rfl
theorem pinf_isMachineChecked_eTranslationValidation : isMachineChecked ProofEvidence.eTranslationValidation = true := rfl
theorem pinf_isMachineChecked_eTrusted : isMachineChecked ProofEvidence.eTrusted = false := rfl
theorem pinf_isMachineChecked_eInheritedFromCallee : isMachineChecked ProofEvidence.eInheritedFromCallee = false := rfl
theorem pinf_isMachineChecked_eCleanCic : isMachineChecked ProofEvidence.eCleanCic = true := rfl

-- ===========================================================================
-- FAITHFULNESS: isKernelCertified — eCleanCic is the UNIQUE kernel-certified
-- evidence (= true), and = false for the other 7.
-- ===========================================================================
theorem pinf_isKernelCertified_eSmtProof : isKernelCertified ProofEvidence.eSmtProof = false := rfl
theorem pinf_isKernelCertified_eLeanProof : isKernelCertified ProofEvidence.eLeanProof = false := rfl
theorem pinf_isKernelCertified_eKaniHarness : isKernelCertified ProofEvidence.eKaniHarness = false := rfl
theorem pinf_isKernelCertified_eGammaCrownBound : isKernelCertified ProofEvidence.eGammaCrownBound = false := rfl
theorem pinf_isKernelCertified_eTranslationValidation : isKernelCertified ProofEvidence.eTranslationValidation = false := rfl
theorem pinf_isKernelCertified_eTrusted : isKernelCertified ProofEvidence.eTrusted = false := rfl
theorem pinf_isKernelCertified_eInheritedFromCallee : isKernelCertified ProofEvidence.eInheritedFromCallee = false := rfl
theorem pinf_isKernelCertified_eCleanCic : isKernelCertified ProofEvidence.eCleanCic = true := rfl

-- ===========================================================================
-- METATHEOREM: kernel-certified => machine-checked. The strongest evidence is
-- a fortiori machine-checked. Encoded over Bool as the implication
--   (not isKernelCertified) || isMachineChecked = true
-- proven by an 8-ctor casesOn (each minor rfl, all ctors nullary).
-- ===========================================================================
theorem pinf_kernelcertified_implies_machinechecked (e : ProofEvidence) :
    Bool.or (Bool.not (isKernelCertified e)) (isMachineChecked e) = true :=
  @ProofEvidence.casesOn
    (fun k => Bool.or (Bool.not (isKernelCertified k)) (isMachineChecked k) = true) e
    rfl rfl rfl rfl rfl rfl rfl rfl

-- METATHEOREM: NO evidence is both kernel-certified and non-machine-checked
-- (the contrapositive partition edge): and (isKernelCertified e) (not
-- (isMachineChecked e)) = false over all 8 ctors.
theorem pinf_no_kernelcertified_unchecked (e : ProofEvidence) :
    Bool.and (isKernelCertified e) (Bool.not (isMachineChecked e)) = false :=
  @ProofEvidence.casesOn
    (fun k => Bool.and (isKernelCertified k) (Bool.not (isMachineChecked k)) = false) e
    rfl rfl rfl rfl rfl rfl rfl rfl

-- ###########################################################################
-- ObligationKind (proof.rs:385) — 12 ctors, the obligation taxonomy.
-- ###########################################################################

-- The category enum the 12 obligation kinds fold into. This is a DOCUMENTED
-- TAXONOMY (not a single Rust method): contracts, invariants, panic-class safety,
-- temporal properties, and translation validation. (Grounded in CLAUDE.md proof.rs
-- "ProofObligation kinds" + the proof.rs ArithmeticSafety/BoundsCheck doc-comments
-- noting they are panic-freedom-class obligations.) 5 nullary ctors.
inductive OKCat where
  | okContract : OKCat
  | okInvariant : OKCat
  | okSafety : OKCat
  | okTemporal : OKCat
  | okTranslation : OKCat

-- A faithful Clean image of trust-ir `ObligationKind` (proof.rs:385). 12 nullary
-- ctors in DECLARATION ORDER (prefixed `o`):
--   Precondition Postcondition LoopInvariant TypeInvariant RefinementType
--   TranslationValidation MemorySafety PanicFreedom TemporalSafety Liveness
--   ArithmeticSafety BoundsCheck
inductive ObligationKind where
  | oPrecondition : ObligationKind
  | oPostcondition : ObligationKind
  | oLoopInvariant : ObligationKind
  | oTypeInvariant : ObligationKind
  | oRefinementType : ObligationKind
  | oTranslationValidation : ObligationKind
  | oMemorySafety : ObligationKind
  | oPanicFreedom : ObligationKind
  | oTemporalSafety : ObligationKind
  | oLiveness : ObligationKind
  | oArithmeticSafety : ObligationKind
  | oBoundsCheck : ObligationKind

-- okCategory: fold each of the 12 kinds into its category. Mapping (per the
-- taxonomy above):
--   okContract:    Precondition, Postcondition
--   okInvariant:   LoopInvariant, TypeInvariant, RefinementType
--   okSafety:      MemorySafety, PanicFreedom, ArithmeticSafety, BoundsCheck
--   okTemporal:    TemporalSafety, Liveness
--   okTranslation: TranslationValidation
def okCategory : ObligationKind -> OKCat := fun k =>
  @ObligationKind.casesOn (fun _ => OKCat) k
    OKCat.okContract      -- oPrecondition
    OKCat.okContract      -- oPostcondition
    OKCat.okInvariant     -- oLoopInvariant
    OKCat.okInvariant     -- oTypeInvariant
    OKCat.okInvariant     -- oRefinementType
    OKCat.okTranslation   -- oTranslationValidation
    OKCat.okSafety        -- oMemorySafety
    OKCat.okSafety        -- oPanicFreedom
    OKCat.okTemporal      -- oTemporalSafety
    OKCat.okTemporal      -- oLiveness
    OKCat.okSafety        -- oArithmeticSafety
    OKCat.okSafety        -- oBoundsCheck

-- isSafetyKind: a Bool view of the okSafety category (the panic-class / memory
-- obligations). Used for the partition metatheorem below.
def isSafetyKind : ObligationKind -> Bool := fun k =>
  @ObligationKind.casesOn (fun _ => Bool) k
    false   -- oPrecondition
    false   -- oPostcondition
    false   -- oLoopInvariant
    false   -- oTypeInvariant
    false   -- oRefinementType
    false   -- oTranslationValidation
    true    -- oMemorySafety
    true    -- oPanicFreedom
    false   -- oTemporalSafety
    false   -- oLiveness
    true    -- oArithmeticSafety
    true    -- oBoundsCheck

-- isContractKind: a Bool view of the okContract category (pre/postconditions).
def isContractKind : ObligationKind -> Bool := fun k =>
  @ObligationKind.casesOn (fun _ => Bool) k
    true    -- oPrecondition
    true    -- oPostcondition
    false   -- oLoopInvariant
    false   -- oTypeInvariant
    false   -- oRefinementType
    false   -- oTranslationValidation
    false   -- oMemorySafety
    false   -- oPanicFreedom
    false   -- oTemporalSafety
    false   -- oLiveness
    false   -- oArithmeticSafety
    false   -- oBoundsCheck

-- ===========================================================================
-- FAITHFULNESS: okCategory, per variant (casesOn iota = rfl). The result type is
-- OKCat, so each fact is an equality of OKCat values.
-- ===========================================================================
theorem pinf_okCategory_oPrecondition : okCategory ObligationKind.oPrecondition = OKCat.okContract := rfl
theorem pinf_okCategory_oPostcondition : okCategory ObligationKind.oPostcondition = OKCat.okContract := rfl
theorem pinf_okCategory_oLoopInvariant : okCategory ObligationKind.oLoopInvariant = OKCat.okInvariant := rfl
theorem pinf_okCategory_oTypeInvariant : okCategory ObligationKind.oTypeInvariant = OKCat.okInvariant := rfl
theorem pinf_okCategory_oRefinementType : okCategory ObligationKind.oRefinementType = OKCat.okInvariant := rfl
theorem pinf_okCategory_oTranslationValidation : okCategory ObligationKind.oTranslationValidation = OKCat.okTranslation := rfl
theorem pinf_okCategory_oMemorySafety : okCategory ObligationKind.oMemorySafety = OKCat.okSafety := rfl
theorem pinf_okCategory_oPanicFreedom : okCategory ObligationKind.oPanicFreedom = OKCat.okSafety := rfl
theorem pinf_okCategory_oTemporalSafety : okCategory ObligationKind.oTemporalSafety = OKCat.okTemporal := rfl
theorem pinf_okCategory_oLiveness : okCategory ObligationKind.oLiveness = OKCat.okTemporal := rfl
theorem pinf_okCategory_oArithmeticSafety : okCategory ObligationKind.oArithmeticSafety = OKCat.okSafety := rfl
theorem pinf_okCategory_oBoundsCheck : okCategory ObligationKind.oBoundsCheck = OKCat.okSafety := rfl

-- ===========================================================================
-- METATHEOREMS over ObligationKind (all-ctor @casesOn; 12 nullary minors -> rfl).
-- ===========================================================================

-- The safety and contract Bool views are DISJOINT over all 12 kinds (no
-- obligation is both a contract and a panic-class safety obligation).
theorem pinf_safety_contract_disjoint (k : ObligationKind) :
    Bool.and (isSafetyKind k) (isContractKind k) = false :=
  @ObligationKind.casesOn (fun j => Bool.and (isSafetyKind j) (isContractKind j) = false) k
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- Every safety kind has category okSafety (the Bool view agrees with okCategory):
-- (not isSafetyKind k) || (okCategory k == okSafety) — phrased as the implication
-- that a safety kind is NOT a contract kind, proven uniformly over all 12 ctors.
theorem pinf_safety_implies_not_contract (k : ObligationKind) :
    Bool.or (Bool.not (isSafetyKind k)) (Bool.not (isContractKind k)) = true :=
  @ObligationKind.casesOn
    (fun j => Bool.or (Bool.not (isSafetyKind j)) (Bool.not (isContractKind j)) = true) k
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end ValProofInfra
"#;

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn resolve_name(env: &Environment, short: &str) -> Name {
    env.constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| panic!("no registered constant with short name `{short}`"))
}

fn assert_proven_to_foundations(env: &Environment, short: &str) {
    let name = resolve_name(env, short);
    let deps = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name}: not registered (axiom_deps returned None)"));
    assert!(
        deps.is_empty(),
        "{name} must be proven down to the foundational axioms, but rests on: {deps:?}"
    );
}

/// Every theorem across the three value/proof-layer slices, in order.
const VALUEPROOF_THEOREMS: &[&str] = &[
    // --- ValConstant (71) ---
    "cst_isScalarConst_cint",
    "cst_isScalarConst_cfloat",
    "cst_isScalarConst_cbool",
    "cst_isScalarConst_caggregate",
    "cst_isScalarConst_carray",
    "cst_isScalarConst_cvector",
    "cst_isScalarConst_csequence",
    "cst_isScalarConst_cset",
    "cst_isScalarConst_crecord",
    "cst_isScalarConst_cclosure",
    "cst_isScalarConst_cfndef",
    "cst_isScalarConst_csymboladdr",
    "cst_isScalarConst_cphantom",
    "cst_isAggregateConst_cint",
    "cst_isAggregateConst_cfloat",
    "cst_isAggregateConst_cbool",
    "cst_isAggregateConst_caggregate",
    "cst_isAggregateConst_carray",
    "cst_isAggregateConst_cvector",
    "cst_isAggregateConst_csequence",
    "cst_isAggregateConst_cset",
    "cst_isAggregateConst_crecord",
    "cst_isAggregateConst_cclosure",
    "cst_isAggregateConst_cfndef",
    "cst_isAggregateConst_csymboladdr",
    "cst_isAggregateConst_cphantom",
    "cst_isCallableConst_cint",
    "cst_isCallableConst_cfloat",
    "cst_isCallableConst_cbool",
    "cst_isCallableConst_caggregate",
    "cst_isCallableConst_carray",
    "cst_isCallableConst_cvector",
    "cst_isCallableConst_csequence",
    "cst_isCallableConst_cset",
    "cst_isCallableConst_crecord",
    "cst_isCallableConst_cclosure",
    "cst_isCallableConst_cfndef",
    "cst_isCallableConst_csymboladdr",
    "cst_isCallableConst_cphantom",
    "cst_isAddrConst_cint",
    "cst_isAddrConst_cfloat",
    "cst_isAddrConst_cbool",
    "cst_isAddrConst_caggregate",
    "cst_isAddrConst_carray",
    "cst_isAddrConst_cvector",
    "cst_isAddrConst_csequence",
    "cst_isAddrConst_cset",
    "cst_isAddrConst_crecord",
    "cst_isAddrConst_cclosure",
    "cst_isAddrConst_cfndef",
    "cst_isAddrConst_csymboladdr",
    "cst_isAddrConst_cphantom",
    "cst_isPhantomConst_cint",
    "cst_isPhantomConst_cfloat",
    "cst_isPhantomConst_cbool",
    "cst_isPhantomConst_caggregate",
    "cst_isPhantomConst_carray",
    "cst_isPhantomConst_cvector",
    "cst_isPhantomConst_csequence",
    "cst_isPhantomConst_cset",
    "cst_isPhantomConst_crecord",
    "cst_isPhantomConst_cclosure",
    "cst_isPhantomConst_cfndef",
    "cst_isPhantomConst_csymboladdr",
    "cst_isPhantomConst_cphantom",
    "cst_disjoint_scalar_aggregate",
    "cst_disjoint_aggregate_callable",
    "cst_disjoint_scalar_callable",
    "cst_cover_all",
    "cst_addr_singleton",
    "cst_phantom_singleton",
    // --- ValProofAnn (34) ---
    "pann_cat_memory_rep",
    "pann_cat_arith_rep",
    "pann_cat_functional_rep",
    "pann_cat_concurrency_rep",
    "pann_cat_memrole_rep",
    "pann_cat_parallel_rep",
    "pann_cat_nn_rep",
    "pann_cat_aliasing_rep",
    "pann_cat_safety_rep",
    "pann_cat_extensible_rep",
    "pann_cat_atomicsetinsert_concurrency",
    "pann_cat_monotonic_functional",
    "pann_gpusafety_pure",
    "pann_gpusafety_nopanic",
    "pann_gpusafety_deterministic",
    "pann_gpusafety_inbounds_false",
    "pann_gpusafety_terminates_false",
    "pann_gpusafety_nooverflow_false",
    "pann_gpuhint_readonlytable",
    "pann_gpuhint_appendonly",
    "pann_gpuhint_atomicsetinsert",
    "pann_gpuhint_parallelmap",
    "pann_gpuhint_boundedloop",
    "pann_gpuhint_divergenceclass",
    "pann_gpuhint_pure_false",
    "pann_gpuhint_inbounds_false",
    "pann_gpusafety_implies_functional_or_safety",
    "pann_functional_not_gpuhint",
    "pann_memory_arith_disjoint",
    "pann_memory_functional_disjoint",
    "pann_arith_functional_disjoint",
    "pann_eqCat_refl",
    "pann_gpusafety_not_arith",
    "pann_gpusafety_gpuhint_disjoint",
    // --- ValProofInfra (48) ---
    "pinf_isResolved_sPending",
    "pinf_isResolved_sDischarged",
    "pinf_isResolved_sFailed",
    "pinf_isResolved_sTrusted",
    "pinf_isResolved_sCertified",
    "pinf_assuranceRank_sPending",
    "pinf_assuranceRank_sDischarged",
    "pinf_assuranceRank_sFailed",
    "pinf_assuranceRank_sTrusted",
    "pinf_assuranceRank_sCertified",
    "pinf_certified_above_trusted",
    "pinf_trusted_not_above_certified",
    "pinf_discharged_above_trusted",
    "pinf_assuranceLE_refl",
    "pinf_certified_is_top",
    "pinf_certified_is_resolved",
    "pinf_isMachineChecked_eSmtProof",
    "pinf_isMachineChecked_eLeanProof",
    "pinf_isMachineChecked_eKaniHarness",
    "pinf_isMachineChecked_eGammaCrownBound",
    "pinf_isMachineChecked_eTranslationValidation",
    "pinf_isMachineChecked_eTrusted",
    "pinf_isMachineChecked_eInheritedFromCallee",
    "pinf_isMachineChecked_eCleanCic",
    "pinf_isKernelCertified_eSmtProof",
    "pinf_isKernelCertified_eLeanProof",
    "pinf_isKernelCertified_eKaniHarness",
    "pinf_isKernelCertified_eGammaCrownBound",
    "pinf_isKernelCertified_eTranslationValidation",
    "pinf_isKernelCertified_eTrusted",
    "pinf_isKernelCertified_eInheritedFromCallee",
    "pinf_isKernelCertified_eCleanCic",
    "pinf_kernelcertified_implies_machinechecked",
    "pinf_no_kernelcertified_unchecked",
    "pinf_okCategory_oPrecondition",
    "pinf_okCategory_oPostcondition",
    "pinf_okCategory_oLoopInvariant",
    "pinf_okCategory_oTypeInvariant",
    "pinf_okCategory_oRefinementType",
    "pinf_okCategory_oTranslationValidation",
    "pinf_okCategory_oMemorySafety",
    "pinf_okCategory_oPanicFreedom",
    "pinf_okCategory_oTemporalSafety",
    "pinf_okCategory_oLiveness",
    "pinf_okCategory_oArithmeticSafety",
    "pinf_okCategory_oBoundsCheck",
    "pinf_safety_contract_disjoint",
    "pinf_safety_implies_not_contract",
];

#[test]
fn value_proof_types_elaborate_and_kernel_check() {
    elaborate_module(VALUEPROOF_SOURCE).expect(
        "the trust-ir value/proof types (Constant + ProofAnnotation + ProofStatus/ProofEvidence/\
         ObligationKind), faithful to constant.rs/proof.rs, must elaborate and kernel-check together",
    );
}

#[test]
fn value_proof_types_faithfulness_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(VALUEPROOF_SOURCE)
        .expect("the value/proof-types module must elaborate before auditing its theorems");
    for thm in VALUEPROOF_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "ALL TRUST VALUE & PROOF-LAYER TYPES ARE CLEAN TYPES: {} faithfulness + structural theorems \
         over trust-ir's Constant + proof enums, every one proven to the 3 foundational axioms.",
        VALUEPROOF_THEOREMS.len()
    );
}

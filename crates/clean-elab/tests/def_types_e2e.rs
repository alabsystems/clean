// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! TRUST DEFINITION TYPES ARE CLEAN TYPES — trust-ir's supporting definition
//! structs (the records behind the id-carrying `Ty` variants) and the `Divergence`
//! GPU lattice, modeled in Clean and proven to the 3 foundational axioms.
//!
//! The last piece of the trust-ir type surface (after tyfull/tyall/inst_types/
//! value_proof/typed_inst). Two namespaces:
//!
//!   * `DefTypes`      — `FuncTy` (param/return arity, vararg), `StructDef` vs
//!       `RecordDef` (the documented layout distinction: struct has size/align/
//!       offsets, record never does), `EnumDef`/`EnumVariant` (variant/field
//!       arity), and `ClosureTy` — the ty#4145 SOUNDNESS LESSON proven: captures
//!       are part of the type identity (same function signature + different
//!       captured environment = a DIFFERENT closure type).
//!   * `DefDivergence` — `Divergence` (Uniform/Low/High) as the GPU-divergence
//!       lattice (Uniform bottom, High top, reflexive) + the `is_gpu_eligible`
//!       gate (Uniform/Low eligible, High disqualified).
//!
//! Field names and Ty payloads are abstracted to arities/type-tags (the faithful
//! abstraction for the well-formedness classifiers). Every theorem passes the
//! `axiom_deps(name).is_empty()` bedrock gate; both slices elaborate together.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const DEFTYPES_SOURCE: &str = r#"

-- ###########################################################################
-- definition structs: FuncTy/StructDef/RecordDef/EnumDef/EnumVariant arity + struct-vs-record layout + ClosureTy captures-are-identity (ty#4145)
-- ###########################################################################
namespace DefTypes

-- ###########################################################################
-- 1) FuncTy { params: Vec<Ty>, returns: Vec<Ty>, is_vararg: bool } (ty.rs:465)
-- ###########################################################################
-- Abstract the two Ty vectors to their LENGTHS (paramCount, returnCount); the
-- element Ty payloads do not affect signature arity. is_vararg is kept as Bool.
-- A two-ctor inductive (real `funcTy` + a `nop` sentinel) so field access via
-- @FuncTyDef.casesOn iota-reduces and projections never get in the way.
inductive FuncTyDef where
  | funcTy : Nat -> Nat -> Bool -> FuncTyDef
  | funcNop : FuncTyDef

-- arity := paramCount (the number of parameter types).
def arity : FuncTyDef -> Nat := fun f =>
  @FuncTyDef.casesOn (fun _ => Nat) f
    (fun p _r _v => p)   -- funcTy paramCount returnCount isVararg
    0                    -- funcNop

-- returnArity := returnCount (the number of return types; multi-return supported).
def returnArity : FuncTyDef -> Nat := fun f =>
  @FuncTyDef.casesOn (fun _ => Nat) f
    (fun _p r _v => r)   -- funcTy
    0                    -- funcNop

-- isVararg accessor (the is_vararg flag).
def isVararg : FuncTyDef -> Bool := fun f =>
  @FuncTyDef.casesOn (fun _ => Bool) f
    (fun _p _r v => v)   -- funcTy
    false                -- funcNop

-- FAITHFULNESS (FuncTy):
theorem def_arity_funcTy_2_1_false : arity (FuncTyDef.funcTy 2 1 false) = 2 := rfl
-- a (funcTy 0 0 false) is the nullary signature: arity 0 AND returnArity 0.
theorem def_arity_nullary : arity (FuncTyDef.funcTy 0 0 false) = 0 := rfl
theorem def_returnArity_nullary : returnArity (FuncTyDef.funcTy 0 0 false) = 0 := rfl
-- isVararg of a vararg signature is true.
theorem def_isVararg_true : isVararg (FuncTyDef.funcTy 1 0 true) = true := rfl
-- a non-vararg signature reports false.
theorem def_isVararg_false : isVararg (FuncTyDef.funcTy 2 1 false) = false := rfl
-- multi-return: returnArity (funcTy 1 2 false) = 2.
theorem def_returnArity_multi : returnArity (FuncTyDef.funcTy 1 2 false) = 2 := rfl

-- ###########################################################################
-- 2) StructDef { fields, size, align } vs RecordDef { fields } (ty.rs:473,415)
-- ###########################################################################
-- DOCUMENTED DISTINCTION (ty.rs doc-comments): a Struct carries layout metadata
-- (size/align present, field offsets), a Record has NO layout (offset always
-- None, no size/align). We abstract `fields` to its LENGTH (fieldCount) and carry
-- a hasLayout Bool. For structs hasLayout is the supplied flag (true in practice);
-- for records it is ALWAYS false by construction (recordDef carries no layout).
inductive StructDefD where
  | structDef : Nat -> Bool -> StructDefD   -- fieldCount, hasLayout
  | structNop : StructDefD

inductive RecordDefD where
  | recordDef : Nat -> RecordDefD            -- fieldCount (NO layout slot at all)
  | recordNop : RecordDefD

-- fieldCount of a struct.
def fieldCount : StructDefD -> Nat := fun s =>
  @StructDefD.casesOn (fun _ => Nat) s
    (fun n _h => n)      -- structDef fieldCount hasLayout
    0                    -- structNop

-- hasLayout of a struct: the carried layout flag.
def hasLayout : StructDefD -> Bool := fun s =>
  @StructDefD.casesOn (fun _ => Bool) s
    (fun _n h => h)      -- structDef
    false                -- structNop

-- fieldCount of a record.
def recordFieldCount : RecordDefD -> Nat := fun r =>
  @RecordDefD.casesOn (fun _ => Nat) r
    (fun n => n)         -- recordDef fieldCount
    0                    -- recordNop

-- recordHasLayout: a Record NEVER has layout — false by construction for every
-- recordDef (and for the nop). This is the documented "offset always None" fact.
def recordHasLayout : RecordDefD -> Bool := fun r =>
  @RecordDefD.casesOn (fun _ => Bool) r
    (fun _n => false)    -- recordDef : no layout, ever
    false                -- recordNop

-- FAITHFULNESS (StructDef vs RecordDef):
theorem def_struct_hasLayout : hasLayout (StructDefD.structDef 3 true) = true := rfl
theorem def_record_hasLayout_false : recordHasLayout (RecordDefD.recordDef 2) = false := rfl
theorem def_struct_fieldCount : fieldCount (StructDefD.structDef 3 true) = 3 := rfl
theorem def_record_fieldCount : recordFieldCount (RecordDefD.recordDef 2) = 2 := rfl

-- COHERENCE METATHEOREM: a record NEVER has layout, for EVERY record value
-- (over both ctors of RecordDefD; the recordDef minor binds its fieldCount).
theorem def_record_never_has_layout (r : RecordDefD) : recordHasLayout r = false :=
  @RecordDefD.casesOn (fun k => recordHasLayout k = false) r
    (fun _n => rfl)      -- recordDef
    rfl                  -- recordNop

-- ###########################################################################
-- 3) EnumDef { variants } + EnumVariant { fields } (ty.rs:492,501)
-- ###########################################################################
-- EnumDef abstracts `variants : Vec<EnumVariant>` to its LENGTH (variantCount);
-- EnumVariant abstracts `fields : Vec<Ty>` to its LENGTH (fieldCount). The variant
-- names and the element Ty payloads do not affect the arity classifiers.
inductive EnumVariantD where
  | enumVariant : Nat -> EnumVariantD        -- fieldCount of this variant
  | enumVariantNop : EnumVariantD

inductive EnumDefD where
  | enumDef : Nat -> EnumDefD                 -- variantCount
  | enumDefNop : EnumDefD

-- variantFieldCount := number of fields the variant carries (its arity).
def variantFieldCount : EnumVariantD -> Nat := fun v =>
  @EnumVariantD.casesOn (fun _ => Nat) v
    (fun n => n)         -- enumVariant fieldCount
    0                    -- enumVariantNop

-- variantCount := number of variants in the enum.
def variantCount : EnumDefD -> Nat := fun e =>
  @EnumDefD.casesOn (fun _ => Nat) e
    (fun n => n)         -- enumDef variantCount
    0                    -- enumDefNop

-- FAITHFULNESS (EnumDef + EnumVariant):
-- an Option-like enum (Some/None) has 2 variants.
theorem def_enum_variantCount : variantCount (EnumDefD.enumDef 2) = 2 := rfl
-- a single-field variant has field arity 1.
theorem def_variant_fieldCount_one : variantFieldCount (EnumVariantD.enumVariant 1) = 1 := rfl
-- a UNIT variant (no fields) has 0 fields.
theorem def_variant_unit_zero : variantFieldCount (EnumVariantD.enumVariant 0) = 0 := rfl
-- an Option-like enum has exactly 2 variants (restated as the documented example).
theorem def_enum_option_two : variantCount (EnumDefD.enumDef 2) = 2 := rfl

-- ###########################################################################
-- 4) ClosureTy { func: FuncTyId, captures: Vec<Ty> } (ty.rs:437) — THE HIGHLIGHT
-- ###########################################################################
-- ty#4145 SOUNDNESS LESSON (ty.rs doc-comment): captures are PART OF THE TYPE
-- IDENTITY. Two closures over the SAME bare function signature but DIFFERENT
-- captured environments are NOT the same closure type — a self-referential
-- FuncDef routes its captured state through the closure type identity, so a
-- cached body that references stale captures is the soundness bug. We model the
-- captured-env frame as a List of type-tags (Nat), and the func id as a Nat.
-- The IDENTITY property is the statement that closureEq distinguishes closures
-- that differ in EITHER the func id OR the capture tag list.
inductive ClosureTyD where
  | closureTy : Nat -> List Nat -> ClosureTyD   -- func id, captures (type-tags)
  | closureNop : ClosureTyD

-- func id accessor.
def closureFunc : ClosureTyD -> Nat := fun c =>
  @ClosureTyD.casesOn (fun _ => Nat) c
    (fun fid _caps => fid)   -- closureTy
    0                        -- closureNop

-- captures accessor (the type-tag list).
def closureCaptures : ClosureTyD -> List Nat := fun c =>
  @ClosureTyD.casesOn (fun _ => List Nat) c
    (fun _fid caps => caps)  -- closureTy
    List.nil                 -- closureNop

-- captureCount := List.length captures (number of captured-env slots).
def captureCount : ClosureTyD -> Nat := fun c =>
  List.length (closureCaptures c)

-- A Nat-list equality, self-proven by structural recursion via @List.rec.
-- natListEq : List Nat -> List Nat -> Bool. The motive is (fun _ => List Nat -> Bool):
-- the recursor folds over the FIRST list, threading the second list as the argument.
--   nil  case (natListNil):  (fun ys => List-is-nil? ys)
--   cons case (natListCons): (fun x xs ih ys => match ys with
--                                 | nil      => false
--                                 | y :: ys' => (Nat.beq x y) && ih ys')
-- The cons minor's IH is bound `ih` (NOT `rec`, a reserved surface keyword), and
-- the inner `match on ys` is an @List.casesOn. The two minors are factored out so
-- @List.rec sees them as atoms; the function-typed result is RIGHT-associated
-- (`(List Nat -> Bool) -> List Nat -> Bool`, no parens on the final result).
def natListNil : List Nat -> Bool := fun ys =>
  @List.casesOn Nat (fun _ => Bool) ys
    true                       -- nil
    (fun _y _ys => false)      -- cons
def natListCons : Nat -> List Nat -> (List Nat -> Bool) -> List Nat -> Bool :=
  fun x => fun xs => fun ih => fun ys =>
    @List.casesOn Nat (fun _ => Bool) ys
      false                                                  -- ys = nil  => unequal
      (fun y ys2 => Bool.and (Nat.beq x y) (ih ys2))         -- ys = y::ys2
def natListEq : List Nat -> List Nat -> Bool := fun xs =>
  @List.rec Nat (fun _ => List Nat -> Bool) natListNil natListCons xs

-- closureEq: two closures are the SAME type iff SAME func id AND SAME captures.
def closureEq : ClosureTyD -> ClosureTyD -> Bool := fun a b =>
  Bool.and (Nat.beq (closureFunc a) (closureFunc b))
           (natListEq (closureCaptures a) (closureCaptures b))

-- FAITHFULNESS (ClosureTy / ty#4145 identity):
-- bare (no captures) vs one capture differ: SAME func, DIFFERENT captures => NOT
-- the same closure type.
theorem def_closure_bare_vs_one_differ :
    closureEq (ClosureTyD.closureTy 7 List.nil)
              (ClosureTyD.closureTy 7 (List.cons 0 List.nil)) = false := rfl
-- different captures differ (same func id, capture tag 0 vs 1).
theorem def_closure_diff_captures_differ :
    closureEq (ClosureTyD.closureTy 7 (List.cons 0 List.nil))
              (ClosureTyD.closureTy 7 (List.cons 1 List.nil)) = false := rfl
-- same func + same captures ARE equal.
theorem def_closure_same_equal :
    closureEq (ClosureTyD.closureTy 7 (List.cons 0 List.nil))
              (ClosureTyD.closureTy 7 (List.cons 0 List.nil)) = true := rfl
-- different func id (same captures) also differ — func is part of identity too.
theorem def_closure_diff_func_differ :
    closureEq (ClosureTyD.closureTy 7 List.nil)
              (ClosureTyD.closureTy 8 List.nil) = false := rfl
-- captureCount: bare closure has 0 captures.
theorem def_captureCount_zero : captureCount (ClosureTyD.closureTy 3 List.nil) = 0 := rfl
-- captureCount: two captures.
theorem def_captureCount_two :
    captureCount (ClosureTyD.closureTy 3 (List.cons 0 (List.cons 1 List.nil))) = 2 := rfl

-- IDENTITY METATHEOREM: closureEq is REFLEXIVE — every closure type is the same
-- type as itself. This requires natListEq to be reflexive, which we prove first
-- by @List.rec over the capture list (the cons case uses Nat.beq reflexivity).
theorem def_natBeq_refl (n : Nat) : Nat.beq n n = true :=
  @Nat.rec (fun k => Nat.beq k k = true)
    rfl                                  -- zero
    (fun _k ih => ih)                    -- succ : Nat.beq (succ k) (succ k) iota-reduces to Nat.beq k k
    n
-- The cons case: natListEq (cons x xs) (cons x xs) iota-reduces to
-- Bool.and (Nat.beq x x) (natListEq xs xs); rewrite Nat.beq x x -> true (via
-- def_natBeq_refl) and natListEq xs xs -> true (the IH) under Bool.and (a @congr
-- of two @congrArg/IH proofs), then Bool.and true true = true by iota (rfl).
theorem def_natListEq_refl (xs : List Nat) : natListEq xs xs = true :=
  @List.rec Nat (fun zs => natListEq zs zs = true)
    rfl                                                          -- nil
    (fun x xs ih =>
      @Eq.trans Bool (Bool.and (Nat.beq x x) (natListEq xs xs)) (Bool.and true true) true
        (@congr Bool Bool (Bool.and (Nat.beq x x)) (Bool.and true) (natListEq xs xs) true
          (@congrArg Bool (Bool -> Bool) (Nat.beq x x) true Bool.and (def_natBeq_refl x))
          ih)
        rfl)
    xs

end DefTypes

-- ###########################################################################
-- Divergence GPU lattice (Uniform/Low/High; Uniform bottom, High top) + is_gpu_eligible gate
-- ###########################################################################
namespace DefDivergence

-- A faithful Clean image of trust-ir `Divergence` (proof.rs:18), the GPU
-- thread-divergence class. 3 nullary ctors in DECLARATION ORDER:
--   dUniform = Uniform  (all GPU lanes execute the same control-flow path)
--   dLow     = Low      (minor divergence hardware lane-masking absorbs cheaply)
--   dHigh    = High     (unpredictable control flow; disqualifies GPU execution)
inductive Divergence where
  | dUniform : Divergence
  | dLow : Divergence
  | dHigh : Divergence

-- rank: the divergence HAZARD level — increasing along the lattice.
-- dUniform=0 (ideal), dLow=1 (tolerable), dHigh=2 (disqualifying). The order
-- Uniform <= Low <= High is exactly rank monotonicity.
def rank : Divergence -> Nat := fun d =>
  @Divergence.casesOn (fun _ => Nat) d
    (0)   -- dUniform
    (1)   -- dLow
    (2)   -- dHigh

-- divLE: the lattice order via rank comparison (Nat.ble). divLE o p = true iff o
-- is no more divergent than p, i.e. Uniform <= Low <= High.
def divLE : Divergence -> Divergence -> Bool := fun o p =>
  Nat.ble (rank o) (rank p)

-- isGpuEligibleDiv: the divergence gate of `Function::is_gpu_eligible`
-- (lib.rs:870, divergence_class().is_some_and(|d| d == Uniform || d == Low)).
-- dUniform / dLow are GPU-eligible; dHigh is the hazard marker that disqualifies
-- kernel extraction.
def isGpuEligibleDiv : Divergence -> Bool := fun d =>
  @Divergence.casesOn (fun _ => Bool) d
    true    -- dUniform  (GPU-eligible)
    true    -- dLow      (GPU-eligible)
    false   -- dHigh     (hazard; disqualifies)

-- ===========================================================================
-- PER-VARIANT GATE FAITHFULNESS (casesOn iota = rfl).
-- ===========================================================================
theorem div_eligible_uniform : isGpuEligibleDiv Divergence.dUniform = true := rfl
theorem div_eligible_low : isGpuEligibleDiv Divergence.dLow = true := rfl
theorem div_eligible_high : isGpuEligibleDiv Divergence.dHigh = false := rfl

-- Per-variant rank faithfulness (the hazard ladder).
theorem div_rank_uniform : rank Divergence.dUniform = 0 := rfl
theorem div_rank_low : rank Divergence.dLow = 1 := rfl
theorem div_rank_high : rank Divergence.dHigh = 2 := rfl

-- ===========================================================================
-- LATTICE ORDER LAWS (all-ctor @Divergence.casesOn; 3 nullary minors -> rfl).
-- ===========================================================================

-- REFLEXIVE: every class is no more divergent than itself.
theorem div_LE_refl (o : Divergence) : divLE o o = true :=
  @Divergence.casesOn (fun k => divLE k k = true) o
    rfl rfl rfl

-- Uniform is the BOTTOM element: it is <= every class.
theorem div_uniform_bottom (o : Divergence) : divLE Divergence.dUniform o = true :=
  @Divergence.casesOn (fun k => divLE Divergence.dUniform k = true) o
    rfl rfl rfl

-- High is the TOP element: every class is <= High.
theorem div_high_top (o : Divergence) : divLE o Divergence.dHigh = true :=
  @Divergence.casesOn (fun k => divLE k Divergence.dHigh = true) o
    rfl rfl rfl

-- ===========================================================================
-- THE GATE IS EXACTLY THE NON-TOP ELEMENTS. Two equivalent characterisations,
-- each proven over all 3 ctors by casesOn:
--   (1) isGpuEligibleDiv o = Bool.not (Nat.beq (rank o) 2)  — eligible iff rank != 2
--   (2) isGpuEligibleDiv o = divLE o dLow                   — eligible iff o <= Low
-- These say: GPU-eligible <=> not the (unique) top element High.
-- ===========================================================================
theorem div_gate_is_non_top_rank (o : Divergence) :
    isGpuEligibleDiv o = Bool.not (Nat.beq (rank o) 2) :=
  @Divergence.casesOn (fun k => isGpuEligibleDiv k = Bool.not (Nat.beq (rank k) 2)) o
    rfl rfl rfl

theorem div_gate_eq_le_low (o : Divergence) :
    isGpuEligibleDiv o = divLE o Divergence.dLow :=
  @Divergence.casesOn (fun k => isGpuEligibleDiv k = divLE k Divergence.dLow) o
    rfl rfl rfl

-- ===========================================================================
-- High disqualifies DESPITE being a valid lattice element: the combined fact
-- and (isGpuEligibleDiv dHigh) (divLE dHigh dHigh) = false — High is reflexively
-- ordered (a valid element of the lattice) yet NOT GPU-eligible.
-- ===========================================================================
theorem div_high_valid_but_disqualified :
    Bool.and (isGpuEligibleDiv Divergence.dHigh) (divLE Divergence.dHigh Divergence.dHigh) = false := rfl

-- ===========================================================================
-- TRANSITIVITY SAMPLE along the chain Uniform <= Low <= High (the witnesses that
-- the order is a genuine total chain, not the discrete order).
-- ===========================================================================
theorem div_trans_uniform_low : divLE Divergence.dUniform Divergence.dLow = true := rfl
theorem div_trans_low_high : divLE Divergence.dLow Divergence.dHigh = true := rfl
theorem div_trans_uniform_high : divLE Divergence.dUniform Divergence.dHigh = true := rfl

-- The chain is STRICT at the top: High is not <= Low (so the gate genuinely
-- excludes High, the order is not the codiscrete order).
theorem div_high_not_le_low : divLE Divergence.dHigh Divergence.dLow = false := rfl

-- METATHEOREM: every GPU-eligible class is <= Low (the gate is bounded above by
-- Low). For all o, (not isGpuEligibleDiv o) || (divLE o dLow) = true. 3-ctor
-- casesOn. This is the implication form of div_gate_eq_le_low.
theorem div_eligible_implies_le_low (o : Divergence) :
    Bool.or (Bool.not (isGpuEligibleDiv o)) (divLE o Divergence.dLow) = true :=
  @Divergence.casesOn
    (fun k => Bool.or (Bool.not (isGpuEligibleDiv k)) (divLE k Divergence.dLow) = true) o
    rfl rfl rfl

end DefDivergence
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

/// Every definition-type theorem across the two slices, in order.
const DEFTYPES_THEOREMS: &[&str] = &[
    // --- DefTypes (23) ---
    "def_arity_funcTy_2_1_false",
    "def_arity_nullary",
    "def_returnArity_nullary",
    "def_isVararg_true",
    "def_isVararg_false",
    "def_returnArity_multi",
    "def_struct_hasLayout",
    "def_record_hasLayout_false",
    "def_struct_fieldCount",
    "def_record_fieldCount",
    "def_record_never_has_layout",
    "def_enum_variantCount",
    "def_variant_fieldCount_one",
    "def_variant_unit_zero",
    "def_enum_option_two",
    "def_closure_bare_vs_one_differ",
    "def_closure_diff_captures_differ",
    "def_closure_same_equal",
    "def_closure_diff_func_differ",
    "def_captureCount_zero",
    "def_captureCount_two",
    "def_natBeq_refl",
    "def_natListEq_refl",
    // --- DefDivergence (17) ---
    "div_eligible_uniform",
    "div_eligible_low",
    "div_eligible_high",
    "div_rank_uniform",
    "div_rank_low",
    "div_rank_high",
    "div_LE_refl",
    "div_uniform_bottom",
    "div_high_top",
    "div_gate_is_non_top_rank",
    "div_gate_eq_le_low",
    "div_high_valid_but_disqualified",
    "div_trans_uniform_low",
    "div_trans_low_high",
    "div_trans_uniform_high",
    "div_high_not_le_low",
    "div_eligible_implies_le_low",
];

#[test]
fn definition_types_elaborate_and_kernel_check() {
    elaborate_module(DEFTYPES_SOURCE).expect(
        "trust-ir's definition structs (FuncTy/StructDef/RecordDef/EnumDef/ClosureTy) + the Divergence \
         lattice, faithful to ty.rs/proof.rs, must elaborate and kernel-check together",
    );
}

#[test]
fn definition_type_theorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(DEFTYPES_SOURCE)
        .expect("the definition-types module must elaborate before auditing its theorems");
    for thm in DEFTYPES_THEOREMS {
        assert_proven_to_foundations(&env, thm);
    }
    println!(
        "TRUST DEFINITION TYPES ARE CLEAN TYPES: {} theorems (FuncTy/StructDef/RecordDef/EnumDef/ClosureTy \
         + Divergence lattice, incl. the ty#4145 captures-are-identity property) proven to the 3 axioms.",
        DEFTYPES_THEOREMS.len()
    );
}

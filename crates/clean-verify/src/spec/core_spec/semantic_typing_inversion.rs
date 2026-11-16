// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generation for the existing ten-constructor semantic typing judgment.
//!
//! One actual typing induction derives application, constant and Pi packages.
//! Trailing conversion is retained as DefEqIn, never silently upgraded to Eq.
//! This adds no projection rule, typing oracle, environment-validity premise,
//! term-substitution theorem or Rust refinement claim. Typed-spine extraction
//! remains a later consumer needing conversion under term instantiation.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (
        r"inductive SemanticTypingAppReturn (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr) : Type
| intro : forall (A : KExpr) (B : KExpr),
 TypingCtxConvIn R tenv G f (KExpr.pi A B) -> TypingCtxConvIn R tenv G a A ->
 DefEqIn R (instantiate B a) T -> SemanticTypingAppReturn R tenv G f a T",
        "Application generation data retains both actual typing premises and conversion from the instantiated codomain to the observed result.",
    ),
    (
        r"inductive SemanticTypingConstantReturn (R : RedEnv) (tenv : KDeclEnv)
 (n : Name) (us : ListType Level) (T : KExpr) : Type
| intro : forall (A : KExpr),
 @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) ->
 DefEqIn R A T -> SemanticTypingConstantReturn R tenv n us T",
        "Constant generation retains the computed guarded lookup and general semantic conversion, not equality of raw and returned types.",
    ),
    (
        r"inductive SemanticTypingPiReturn (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr) : Type
| intro : forall (u : Level) (v : Level),
 TypingCtxConvIn R tenv G A (KExpr.sort u) ->
 TypingCtxConvIn R tenv (@ListType.cons KExpr A G) B (KExpr.sort v) ->
 DefEqIn R (KExpr.sort (Level.imax u v)) T -> SemanticTypingPiReturn R tenv G A B T",
        "Pi generation retains actual domain/body formation derivations and conversion from the raw imax sort to the observed result.",
    ),
    (
        r"def semantic_typing_generation (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) : Type := match e with
| KExpr.sort u => Nat
| KExpr.bvar i => Nat
| KExpr.app f a => SemanticTypingAppReturn R tenv G f a T
| KExpr.lam A b => Nat
| KExpr.pi A B => SemanticTypingPiReturn R tenv G A B T
| KExpr.const n us => SemanticTypingConstantReturn R tenv n us T
| KExpr.let_ A v b => Nat
| KExpr.proj S i e => Nat
| KExpr.lit n => Nat",
        "A shape-indexed generation assertion; other expression shapes impose no application/constant/Pi obligation. This does not assert they are typable.",
    ),
    (
        r"def semantic_typing_generation_convert (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) : forall (T : KExpr) (U : KExpr),
 semantic_typing_generation R tenv G e T -> DefEqIn R T U ->
 semantic_typing_generation R tenv G e U := match e with
| KExpr.sort u => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero
| KExpr.bvar i => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero
| KExpr.app f a => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingAppReturn R tenv G f a T) (h : DefEqIn R T U) =>
 @SemanticTypingAppReturn.rec R tenv G f a T
  (fun (_p : SemanticTypingAppReturn R tenv G f a T) => SemanticTypingAppReturn R tenv G f a U)
  (fun (A : KExpr) (B : KExpr) (hf : TypingCtxConvIn R tenv G f (KExpr.pi A B))
   (ha : TypingCtxConvIn R tenv G a A) (result : DefEqIn R (instantiate B a) T) =>
   @SemanticTypingAppReturn.intro R tenv G f a U A B hf ha
    (@DefEqIn.trans R (instantiate B a) T U result h)) p
| KExpr.lam A b => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero
| KExpr.pi A B => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingPiReturn R tenv G A B T) (h : DefEqIn R T U) =>
 @SemanticTypingPiReturn.rec R tenv G A B T
  (fun (_p : SemanticTypingPiReturn R tenv G A B T) => SemanticTypingPiReturn R tenv G A B U)
  (fun (u : Level) (v : Level) (ha : TypingCtxConvIn R tenv G A (KExpr.sort u))
   (hb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G) B (KExpr.sort v))
   (result : DefEqIn R (KExpr.sort (Level.imax u v)) T) =>
   @SemanticTypingPiReturn.intro R tenv G A B U u v ha hb
    (@DefEqIn.trans R (KExpr.sort (Level.imax u v)) T U result h)) p
| KExpr.const n us => fun (T : KExpr) (U : KExpr)
 (p : SemanticTypingConstantReturn R tenv n us T) (h : DefEqIn R T U) =>
 @SemanticTypingConstantReturn.rec R tenv n us T
  (fun (_p : SemanticTypingConstantReturn R tenv n us T) => SemanticTypingConstantReturn R tenv n us U)
  (fun (A : KExpr)
   (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
   (result : DefEqIn R A T) => @SemanticTypingConstantReturn.intro R tenv n us U A get
    (@DefEqIn.trans R A T U result h)) p
| KExpr.let_ A v b => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero
| KExpr.proj S i e => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero
| KExpr.lit n => fun (T : KExpr) (U : KExpr) (_p : Nat) (_h : DefEqIn R T U) => Nat.zero",
        "Transport all three generation packages through actual trailing semantic conversion, composing the preserved result conversion by transitivity.",
    ),
    (
        r"def typingctxconv_in_generation (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtxConvIn R tenv G e T) :
 semantic_typing_generation R tenv G e T :=
 @TypingCtxConvIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
   (_h : TypingCtxConvIn R tenv G0 e0 T0) => semantic_typing_generation R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
   (_get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_u : Level) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
   (ha : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (hb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) B (KExpr.sort v))
   (_iha : semantic_typing_generation R tenv G0 A (KExpr.sort u))
   (_ihb : semantic_typing_generation R tenv (@ListType.cons KExpr A G0) B (KExpr.sort v)) =>
   @SemanticTypingPiReturn.intro R tenv G0 A B (KExpr.sort (Level.imax u v)) u v ha hb
    (@DefEqIn.refl R (KExpr.sort (Level.imax u v))))
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_ha : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (_hb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) b B)
   (_iha : semantic_typing_generation R tenv G0 A (KExpr.sort u))
   (_ihb : semantic_typing_generation R tenv (@ListType.cons KExpr A G0) b B) => Nat.zero)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
   (hf : TypingCtxConvIn R tenv G0 f (KExpr.pi A B)) (ha : TypingCtxConvIn R tenv G0 a A)
   (_ihf : semantic_typing_generation R tenv G0 f (KExpr.pi A B))
   (_iha : semantic_typing_generation R tenv G0 a A) =>
   @SemanticTypingAppReturn.intro R tenv G0 f a (instantiate B a) A B hf ha
    (@DefEqIn.refl R (instantiate B a)))
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
   (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
   @SemanticTypingConstantReturn.intro R tenv n us A A get (@DefEqIn.refl R A))
  (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
   (_typed : TypingCtxConvIn R tenv G0 e0 A) (convert : DefEqIn R A B)
   (ih : semantic_typing_generation R tenv G0 e0 A) =>
   semantic_typing_generation_convert R tenv G0 e0 A B ih convert)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_ht : TypingCtxConvIn R tenv G0 A (KExpr.sort u)) (_hv : TypingCtxConvIn R tenv G0 v A)
   (_hb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) b B)
   (_iht : semantic_typing_generation R tenv G0 A (KExpr.sort u))
   (_ihv : semantic_typing_generation R tenv G0 v A)
   (_ihb : semantic_typing_generation R tenv (@ListType.cons KExpr A G0) b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero) G e T h",
        "Simultaneously derive app/constant/Pi generation by all ten actual semantic typing recursor cases, including both literal minors and the trailing-conversion minor. No regularity or environment faithfulness assumption.",
    ),
    (
        r"def typingctxconv_in_app_gen (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr)
 (h : TypingCtxConvIn R tenv G (KExpr.app f a) T) (C : Type)
 (consume : forall (A : KExpr) (B : KExpr), TypingCtxConvIn R tenv G f (KExpr.pi A B) ->
 TypingCtxConvIn R tenv G a A -> DefEqIn R (instantiate B a) T -> C) : C :=
 @SemanticTypingAppReturn.rec R tenv G f a T
  (fun (_p : SemanticTypingAppReturn R tenv G f a T) => C) consume
  (typingctxconv_in_generation R tenv G (KExpr.app f a) T h)",
        "CPS application generation for arbitrary semantic typing, retaining both typing derivations and the exact trailing conversion.",
    ),
    (
        r"def typingctxconv_in_constant_gen (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (h : TypingCtxConvIn R tenv G (KExpr.const n us) T) (C : Type)
 (consume : forall (A : KExpr),
 @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) -> DefEqIn R A T -> C) : C :=
 @SemanticTypingConstantReturn.rec R tenv n us T
  (fun (_p : SemanticTypingConstantReturn R tenv n us T) => C) consume
  (typingctxconv_in_generation R tenv G (KExpr.const n us) T h)",
        "CPS constant generation for arbitrary declarative typing, not just KernelInfersIn. Raw type lookup and general DefEqIn remain separate.",
    ),
    (
        r"def typingctxconv_in_pi_gen (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr)
 (h : TypingCtxConvIn R tenv G (KExpr.pi A B) T) (C : Type)
 (consume : forall (u : Level) (v : Level), TypingCtxConvIn R tenv G A (KExpr.sort u) ->
 TypingCtxConvIn R tenv (@ListType.cons KExpr A G) B (KExpr.sort v) ->
 DefEqIn R (KExpr.sort (Level.imax u v)) T -> C) : C :=
 @SemanticTypingPiReturn.rec R tenv G A B T
  (fun (_p : SemanticTypingPiReturn R tenv G A B T) => C) consume
  (typingctxconv_in_generation R tenv G (KExpr.pi A B) T h)",
        "CPS Pi generation recovers domain and dependent body formation plus conversion from the rule's raw imax sort.",
    ),
    (
        r"def typingctxconv_in_constant_lookup_failure (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (n : Name) (us : ListType Level) (T : KExpr)
 (missing : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.none KExpr))
 (h : TypingCtxConvIn R tenv G (KExpr.const n us) T) : Empty :=
 typingctxconv_in_constant_gen R tenv G n us T h Empty
  (fun (A : KExpr)
   (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
   (_convert : DefEqIn R A T) => option_none_ne_some_type KExpr A Empty
    (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (kdecl_type_at tenv n us)
     (@OptionType.some KExpr A)
     (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.none KExpr) missing) get))",
        "No trailing conversion can rescue any declarative constant result after actual guarded lookup fails.",
    ),
];

const WITNESSES: &[(&str, &str)] = &[
    (
        r"def semantic_typing_constant_conv_caller (R : RedEnv) (G : ListType KExpr) (u : Level) :
 TypingCtxConvIn R acceptance_constant_imax_tenv G
 (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level))) (KExpr.sort Level.zero) :=
 @TypingCtxConvIn.conv R acceptance_constant_imax_tenv G
  (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
  (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
  (@TypingCtxConvIn.const R acceptance_constant_imax_tenv G Name.anonymous
   (@ListType.cons Level u (@ListType.nil Level)) (KExpr.sort (Level.imax u Level.zero))
   (acceptance_constant_imax_lookup u))
  (@DefEqIn.levels R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
   (kexprUniverseEq_imax_zero u))",
        "Actual guarded singleton lookup followed by non-syntactic imax-zero semantic conversion; no assumed result typing.",
    ),
    (
        r"def semantic_typing_constant_gen_caller (R : RedEnv) (G : ListType KExpr) (u : Level) :
 SemanticTypingConstantReturn R acceptance_constant_imax_tenv Name.anonymous
 (@ListType.cons Level u (@ListType.nil Level)) (KExpr.sort Level.zero) :=
 typingctxconv_in_constant_gen R acceptance_constant_imax_tenv G Name.anonymous
  (@ListType.cons Level u (@ListType.nil Level)) (KExpr.sort Level.zero)
  (semantic_typing_constant_conv_caller R G u)
  (SemanticTypingConstantReturn R acceptance_constant_imax_tenv Name.anonymous
   (@ListType.cons Level u (@ListType.nil Level)) (KExpr.sort Level.zero))
  (@SemanticTypingConstantReturn.intro R acceptance_constant_imax_tenv Name.anonymous
   (@ListType.cons Level u (@ListType.nil Level)) (KExpr.sort Level.zero))",
        "The assembled constant generator is called on real trailing semantic conversion and returns the exact raw-lookup/conversion package.",
    ),
    (
        r"def semantic_typing_constant_missing_caller (R : RedEnv) (G : ListType KExpr) (T : KExpr) :
 TypingCtxConvIn R acceptance_constant_imax_tenv G
 (KExpr.const Name.anonymous (@ListType.nil Level)) T -> Empty :=
 typingctxconv_in_constant_lookup_failure R acceptance_constant_imax_tenv G Name.anonymous
  (@ListType.nil Level) T acceptance_constant_imax_missing_lookup",
        "The same stored environment rejects every declarative result when its universe argument is omitted.",
    ),
    (
        r"def semantic_typing_app_sig : KConstSig :=
 KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero))
   (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)))",
        "One schematic function signature; the result retains raw imax syntax. This is a model fixture, not admitted production metadata.",
    ),
    (
        r"def semantic_typing_app_tenv : KDeclEnv := fun (n : Name) =>
 opt_pick KConstSig (name_eqb n Name.anonymous) semantic_typing_app_sig (@OptionType.none KConstSig)",
        "Actual singleton guarded declaration environment for the application caller.",
    ),
    (
        r"def semantic_typing_app_lookup (u : Level) : @Eq (OptionType KExpr)
 (kdecl_type_at semantic_typing_app_tenv Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
 (@OptionType.some KExpr (KExpr.pi (KExpr.sort (Level.succ Level.zero))
  (KExpr.sort (Level.imax u Level.zero)))) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.imax u Level.zero))))",
        "Compute the actual universe-guarded function type from its one stored schematic signature.",
    ),
    (
        r"def semantic_typing_app_function (R : RedEnv) (G : ListType KExpr) (u : Level) :
 TypingCtxConvIn R semantic_typing_app_tenv G
 (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
 (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.imax u Level.zero))) :=
 @TypingCtxConvIn.const R semantic_typing_app_tenv G Name.anonymous
  (@ListType.cons Level u (@ListType.nil Level))
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.imax u Level.zero)))
  (semantic_typing_app_lookup u)",
        "Function typing is obtained from computed guarded lookup, not a caller-supplied function typing oracle.",
    ),
    (
        r"def semantic_typing_app_conv_caller (R : RedEnv) (G : ListType KExpr) (u : Level) :
 TypingCtxConvIn R semantic_typing_app_tenv G
 (KExpr.app (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
  (KExpr.sort Level.zero)) (KExpr.sort Level.zero) :=
 @TypingCtxConvIn.conv R semantic_typing_app_tenv G
  (KExpr.app (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
   (KExpr.sort Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
  (@TypingCtxConvIn.app R semantic_typing_app_tenv G
   (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level))) (KExpr.sort Level.zero)
   (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.imax u Level.zero))
   (semantic_typing_app_function R G u) (@TypingCtxConvIn.sort R semantic_typing_app_tenv G Level.zero))
  (@DefEqIn.levels R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
   (kexprUniverseEq_imax_zero u))",
        "A real application typing rule consumes a guarded constant and a proved Sort argument, then traverses nontrivial semantic result conversion.",
    ),
    (
        r"def semantic_typing_app_gen_caller (R : RedEnv) (G : ListType KExpr) (u : Level) :
 SemanticTypingAppReturn R semantic_typing_app_tenv G
 (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
 (KExpr.sort Level.zero) (KExpr.sort Level.zero) :=
 typingctxconv_in_app_gen R semantic_typing_app_tenv G
  (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
  (KExpr.sort Level.zero) (KExpr.sort Level.zero) (semantic_typing_app_conv_caller R G u)
  (SemanticTypingAppReturn R semantic_typing_app_tenv G
   (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
   (KExpr.sort Level.zero) (KExpr.sort Level.zero))
  (@SemanticTypingAppReturn.intro R semantic_typing_app_tenv G
   (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
   (KExpr.sort Level.zero) (KExpr.sort Level.zero))",
        "The assembled application generator returns its actual premises and retained conversion after the concrete application's trailing semantic conversion.",
    ),
    (
        r"def semantic_typing_pi_conv_caller (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) :
 TypingCtxConvIn R tenv G (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))
 (KExpr.sort (Level.succ Level.zero)) :=
 @TypingCtxConvIn.conv R tenv G (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))
  (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
  (KExpr.sort (Level.succ Level.zero))
  (@TypingCtxConvIn.pi R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
   (Level.succ Level.zero) (Level.succ Level.zero)
   (@TypingCtxConvIn.sort R tenv G Level.zero)
   (@TypingCtxConvIn.sort R tenv (@ListType.cons KExpr (KExpr.sort Level.zero) G) Level.zero))
  (@DefEqIn.levels R
   (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)))
   (KExpr.sort (Level.succ Level.zero))
   (KExprUniverseEq.sort (Level.imax (Level.succ Level.zero) (Level.succ Level.zero))
    (Level.succ Level.zero) (fun (_v : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero))))",
        "A Pi with proved domain/body formation returns a semantically simplified sort by an explicit trailing conversion.",
    ),
    (
        r"def semantic_typing_pi_gen_caller (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) :
 SemanticTypingPiReturn R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
 (KExpr.sort (Level.succ Level.zero)) :=
 typingctxconv_in_pi_gen R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (semantic_typing_pi_conv_caller R tenv G)
  (SemanticTypingPiReturn R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
   (KExpr.sort (Level.succ Level.zero)))
  (@SemanticTypingPiReturn.intro R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
   (KExpr.sort (Level.succ Level.zero)))",
        "The actual Pi generator recovers formation and sort conversion from its inhabited converted caller.",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "semantic_typing_generation_convert",
    "typingctxconv_in_generation",
    "typingctxconv_in_app_gen",
    "typingctxconv_in_constant_gen",
    "typingctxconv_in_pi_gen",
    "typingctxconv_in_constant_lookup_failure",
    "semantic_typing_constant_conv_caller",
    "semantic_typing_constant_gen_caller",
    "semantic_typing_constant_missing_caller",
    "semantic_typing_app_lookup",
    "semantic_typing_app_function",
    "semantic_typing_app_conv_caller",
    "semantic_typing_app_gen_caller",
    "semantic_typing_pi_conv_caller",
    "semantic_typing_pi_gen_caller",
];

impl Specification {
    /// Requires acceptance_in, acceptance_constants and its semantic adapters.
    /// Registered in the full bundle; typed-spine consumers remain separate.
    pub(super) fn add_semantic_typing_inversion(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLARATIONS.iter().chain(WITNESSES) {
            if source.starts_with("inductive ") {
                self.add_inductive(source, description)?;
            } else {
                self.add_recursive_def(source, description)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def semantic_typing_forged_raw_lookup : @Eq (OptionType KExpr)
 (kdecl_type_at acceptance_constant_imax_tenv Name.anonymous
  (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
 (@OptionType.some KExpr (KExpr.sort Level.zero)) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
        r"def semantic_typing_forged_app_conversion (R : RedEnv) (G : ListType KExpr) (u : Level) :
 SemanticTypingAppReturn R semantic_typing_app_tenv G
 (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
 (KExpr.sort Level.zero) (KExpr.sort Level.zero) :=
 @SemanticTypingAppReturn.intro R semantic_typing_app_tenv G
 (KExpr.const Name.anonymous (@ListType.cons Level u (@ListType.nil Level)))
 (KExpr.sort Level.zero) (KExpr.sort Level.zero)
 (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.imax u Level.zero))
 (semantic_typing_app_function R G u) (@TypingCtxConvIn.sort R semantic_typing_app_tenv G Level.zero)
 (@DefEqIn.refl R (KExpr.sort Level.zero))",
        r"def semantic_typing_forged_pi_conversion (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) :
 SemanticTypingPiReturn R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
 (KExpr.sort (Level.succ Level.zero)) :=
 @SemanticTypingPiReturn.intro R tenv G (KExpr.sort Level.zero) (KExpr.sort Level.zero)
 (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero) (Level.succ Level.zero)
 (@TypingCtxConvIn.sort R tenv G Level.zero)
 (@TypingCtxConvIn.sort R tenv (@ListType.cons KExpr (KExpr.sort Level.zero) G) Level.zero)
 (@DefEqIn.refl R (KExpr.sort (Level.succ Level.zero)))",
    ];

    #[test]
    fn semantic_typing_generation_sources_parse() {
        for (source, _) in super::DECLARATIONS.iter().chain(super::WITNESSES) {
            crate::test_utils::parse_check(source).expect("generation source parses");
        }
        for source in NEGATIVE_CONTROLS {
            crate::test_utils::parse_check(source).expect("negative control parses");
        }
    }

    #[test]
    fn semantic_typing_generation_and_converted_callers_are_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        if !spec
            .definitions()
            .contains_key("typingctxconv_in_generation")
        {
            spec.add_semantic_typing_inversion()
                .expect("generation proof stage checks");
        }
        for name in super::PROOF_ROOTS {
            let definition = spec
                .definitions()
                .get(*name)
                .expect("generation proof present");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        for source in NEGATIVE_CONTROLS {
            assert!(spec
                .add_recursive_def(source, "Refuse loss of actual generation conversion.")
                .is_err());
        }
    }
}

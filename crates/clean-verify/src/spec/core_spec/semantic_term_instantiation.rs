// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term-instantiation conversion via beta, and one derived constant-spine step.
//!
//! Conversion is proved for arbitrary R by a beta/congruence/beta path, without
//! assuming operational substitution closure. The typed constant-application
//! inverter uses RedEnvFaithful only for the existing semantic Pi injectivity.
//! No general typing-substitution, declaration validity or projection theorem
//! is asserted. Registered in the full bundle; general typed-spine and
//! projection-preservation consumers remain separate work.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (
        r"def def_eq_in_beta (R : RedEnv) (A : KExpr) (b : KExpr) (v : KExpr) :
 DefEqIn R (KExpr.app (KExpr.lam A b) v) (instantiate b v) :=
 @DefEqIn.raw R (KExpr.app (KExpr.lam A b) v) (instantiate b v)
  (@par_reduces_cd.beta R A A b b v v
   (@par_reduces_cd.refl R A) (@par_reduces_cd.refl R b) (@par_reduces_cd.refl R v))",
        "The actual raw parallel beta constructor supplies semantic conversion under arbitrary R, with all three reflexive premises constructed.",
    ),
    (
        r"def def_eq_in_instantiate_congr (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (v2 : KExpr) (hb : DefEqIn R b b2) (hv : DefEqIn R v v2) :
 DefEqIn R (instantiate b v) (instantiate b2 v2) :=
 @DefEqIn.trans R (instantiate b v) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v)
  (instantiate b2 v2)
  (@DefEqIn.symm R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v) (instantiate b v)
   (def_eq_in_beta R (KExpr.sort Level.zero) b v))
  (@DefEqIn.trans R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b) v)
   (KExpr.app (KExpr.lam (KExpr.sort Level.zero) b2) v2) (instantiate b2 v2)
   (@DefEqIn.app R (KExpr.lam (KExpr.sort Level.zero) b)
    (KExpr.lam (KExpr.sort Level.zero) b2) v v2
    (@DefEqIn.lam R (KExpr.sort Level.zero) (KExpr.sort Level.zero) b b2
     (@DefEqIn.refl R (KExpr.sort Level.zero)) hb) hv)
   (def_eq_in_beta R (KExpr.sort Level.zero) b2 v2))",
        "A beta sandwich proves simultaneous body/value instantiation congruence. Arbitrary R; no environment closure, typing, raw-step substitution premise or confluence is needed for this conversion theorem.",
    ),
    (
        r"def def_eq_in_instantiate_same (R : RedEnv) (b : KExpr) (b2 : KExpr)
 (v : KExpr) (hb : DefEqIn R b b2) : DefEqIn R (instantiate b v) (instantiate b2 v) :=
 def_eq_in_instantiate_congr R b b2 v v hb (@DefEqIn.refl R v)",
        "Advance convertible codomains through the same actual argument without a general typing-substitution theorem.",
    ),
    (
        r"def def_eq_in_instantiate_value (R : RedEnv) (b : KExpr)
 (v : KExpr) (v2 : KExpr) (hv : DefEqIn R v v2) :
 DefEqIn R (instantiate b v) (instantiate b v2) :=
 def_eq_in_instantiate_congr R b b v v2 (@DefEqIn.refl R b) hv",
        "A fixed dependent codomain respects conversion of the substituted value; the proof is derived from actual beta and congruence.",
    ),
    (
        r"def semantic_typing_const_pi_conversion (R : RedEnv) (tenv : KDeclEnv)
 (n : Name) (us : ListType Level) (A0 : KExpr) (B0 : KExpr) (F : KExpr) (A : KExpr) (B : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
 (convert : DefEqIn R F (KExpr.pi A B)) : DefEqIn R (KExpr.pi A0 B0) (KExpr.pi A B) :=
 Eq.substType KExpr (fun (T : KExpr) => DefEqIn R T (KExpr.pi A B)) F (KExpr.pi A0 B0)
  (option_some_inj KExpr F (KExpr.pi A0 B0)
   (Eq.trans (OptionType KExpr) (@OptionType.some KExpr F) (kdecl_type_at tenv n us)
    (@OptionType.some KExpr (KExpr.pi A0 B0))
    (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F) found)
    canonical)) convert",
        "Unique results of the same actual guarded lookup identify the stored Pi type; conversion to the inferred Pi is transported, not strengthened to syntactic equality.",
    ),
    (
        r"def typingctxconv_in_const_app_gen (R : RedEnv) (faithful : RedEnvFaithful R)
 (tenv : KDeclEnv) (G : ListType KExpr) (n : Name) (us : ListType Level)
 (a : KExpr) (T : KExpr) (A0 : KExpr) (B0 : KExpr)
 (canonical : @Eq (OptionType KExpr) (kdecl_type_at tenv n us)
  (@OptionType.some KExpr (KExpr.pi A0 B0)))
 (typed : TypingCtxConvIn R tenv G (KExpr.app (KExpr.const n us) a) T)
 (C : Type) (consume : TypingCtxConvIn R tenv G a A0 ->
  DefEqIn R (instantiate B0 a) T -> C) : C :=
 typingctxconv_in_app_gen R tenv G (KExpr.const n us) a T typed C
  (fun (A : KExpr) (B : KExpr)
   (hf : TypingCtxConvIn R tenv G (KExpr.const n us) (KExpr.pi A B))
   (ha : TypingCtxConvIn R tenv G a A) (result : DefEqIn R (instantiate B a) T) =>
   typingctxconv_in_constant_gen R tenv G n us (KExpr.pi A B) hf C
    (fun (F : KExpr)
     (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr F))
     (convert : DefEqIn R F (KExpr.pi A B)) =>
     def_eq_in_pi_components R faithful A0 B0 A B
      (semantic_typing_const_pi_conversion R tenv n us A0 B0 F A B canonical found convert) C
      (fun (domains : DefEqIn R A0 A) (bodies : DefEqIn R B0 B) =>
       consume
        (@TypingCtxConvIn.conv R tenv G a A A0 ha (@DefEqIn.symm R A0 A domains))
        (@DefEqIn.trans R (instantiate B0 a) (instantiate B a) T
         (def_eq_in_instantiate_same R B0 B a bodies) result))))",
        "One genuine typed constant-spine step: derive actual argument typing and canonical instantiated-codomain conversion from whole-application typing plus its raw signature lookup. Faithfulness is used exactly by semantic Pi injectivity; no output-typing oracle is assumed.",
    ),
    (
        r"def semantic_dependent_app_sig : KConstSig :=
 KConstSig.mk (@ListType.nil Name)
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero))",
        "A deliberately schematic model environment fixture with a genuinely dependent codomain. No claim that this arbitrary signature is an admitted definition or logically inhabited production declaration.",
    ),
    (
        r"def semantic_dependent_app_tenv : KDeclEnv := fun (n : Name) =>
 opt_pick KConstSig (name_eqb n Name.anonymous) semantic_dependent_app_sig (@OptionType.none KConstSig)",
        "Actual singleton declaration lookup for the dependent application example; environment validity is not asserted.",
    ),
    (
        r"def semantic_dependent_app_argument : KExpr :=
 KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)",
        "The actual argument has nontrivial raw universe syntax; instantiating bvar zero returns this expression, not a fixed independent codomain.",
    ),
    (
        r"def semantic_dependent_app_lookup : @Eq (OptionType KExpr)
 (kdecl_type_at semantic_dependent_app_tenv Name.anonymous (@ListType.nil Level))
 (@OptionType.some KExpr (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero))) :=
 @Eq.refl (OptionType KExpr)
  (@OptionType.some KExpr (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero)))",
        "The exact zero-universe-arity guarded lookup computes the stored dependent Pi.",
    ),
    (
        r"def semantic_dependent_app_argument_typed (R : RedEnv) (G : ListType KExpr) :
 TypingCtxConvIn R semantic_dependent_app_tenv G semantic_dependent_app_argument
 (KExpr.sort (Level.succ Level.zero)) :=
 @TypingCtxConvIn.conv R semantic_dependent_app_tenv G semantic_dependent_app_argument
  (KExpr.sort (Level.succ (Level.imax (Level.succ Level.zero) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))
  (@TypingCtxConvIn.sort R semantic_dependent_app_tenv G (Level.imax (Level.succ Level.zero) Level.zero))
  (@DefEqIn.levels R
   (KExpr.sort (Level.succ (Level.imax (Level.succ Level.zero) Level.zero)))
   (KExpr.sort (Level.succ Level.zero))
   (KExprUniverseEq.sort (Level.succ (Level.imax (Level.succ Level.zero) Level.zero))
    (Level.succ Level.zero) (fun (_v : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero))))",
        "Derive the actual argument's domain typing from the sort rule and semantic universe conversion, not a supplied typing premise.",
    ),
    (
        r"def semantic_dependent_app_typed (R : RedEnv) (G : ListType KExpr) :
 TypingCtxConvIn R semantic_dependent_app_tenv G
 (KExpr.app (KExpr.const Name.anonymous (@ListType.nil Level)) semantic_dependent_app_argument)
 (KExpr.sort Level.zero) :=
 @TypingCtxConvIn.conv R semantic_dependent_app_tenv G
  (KExpr.app (KExpr.const Name.anonymous (@ListType.nil Level)) semantic_dependent_app_argument)
  semantic_dependent_app_argument (KExpr.sort Level.zero)
  (@TypingCtxConvIn.app R semantic_dependent_app_tenv G
   (KExpr.const Name.anonymous (@ListType.nil Level)) semantic_dependent_app_argument
   (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero)
   (@TypingCtxConvIn.const R semantic_dependent_app_tenv G Name.anonymous (@ListType.nil Level)
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero)) semantic_dependent_app_lookup)
   (semantic_dependent_app_argument_typed R G))
  (@DefEqIn.levels R semantic_dependent_app_argument (KExpr.sort Level.zero)
   (kexprUniverseEq_imax_zero (Level.succ Level.zero)))",
        "A real dependent application derives its result by substituting the actual argument into bvar zero, then traverses an explicit trailing semantic conversion.",
    ),
    (
        r"def semantic_dependent_codomain_caller (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) : DefEqIn R semantic_dependent_app_argument (KExpr.sort Level.zero) :=
 typingctxconv_in_const_app_gen R faithful semantic_dependent_app_tenv G Name.anonymous
  (@ListType.nil Level) semantic_dependent_app_argument (KExpr.sort Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero) semantic_dependent_app_lookup
  (semantic_dependent_app_typed R G) (DefEqIn R semantic_dependent_app_argument (KExpr.sort Level.zero))
  (fun (_argument : TypingCtxConvIn R semantic_dependent_app_tenv G semantic_dependent_app_argument
    (KExpr.sort (Level.succ Level.zero)))
   (result : DefEqIn R (instantiate (KExpr.bvar Nat.zero) semantic_dependent_app_argument)
    (KExpr.sort Level.zero)) => result)",
        "The new generation/spine bridge consumes an actual dependent application derivation and returns its canonical instantiated-codomain conversion. This conditional model caller is not declaration admission or general typing substitution.",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "def_eq_in_beta",
    "def_eq_in_instantiate_congr",
    "def_eq_in_instantiate_same",
    "def_eq_in_instantiate_value",
    "semantic_typing_const_pi_conversion",
    "typingctxconv_in_const_app_gen",
    "semantic_dependent_app_lookup",
    "semantic_dependent_app_argument_typed",
    "semantic_dependent_app_typed",
    "semantic_dependent_codomain_caller",
];

impl Specification {
    pub(super) fn add_semantic_term_instantiation(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLARATIONS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def semantic_term_forged_beta_endpoint (R : RedEnv) :
 DefEqIn R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))
  (KExpr.sort Level.zero)) (KExpr.bvar Nat.zero) :=
 def_eq_in_beta R (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)",
        r"def semantic_term_forged_dependent_endpoint (R : RedEnv) (faithful : RedEnvFaithful R)
 (G : ListType KExpr) : DefEqIn R
 (instantiate (KExpr.bvar (Nat.succ Nat.zero)) semantic_dependent_app_argument)
 (KExpr.sort Level.zero) := semantic_dependent_codomain_caller R faithful G",
    ];

    #[test]
    fn semantic_term_instantiation_sources_parse() {
        for (source, _) in super::DECLARATIONS {
            crate::test_utils::parse_check(source).expect("term instantiation source parses");
        }
        for source in NEGATIVE_CONTROLS {
            crate::test_utils::parse_check(source).expect("forged endpoint parses");
        }
    }

    #[test]
    fn semantic_term_instantiation_and_dependent_spine_are_checked() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        if !spec
            .definitions()
            .contains_key("typingctxconv_in_generation")
        {
            spec.add_semantic_typing_inversion()
                .expect("generation prerequisites check");
        }
        if !spec
            .definitions()
            .contains_key("def_eq_in_instantiate_congr")
        {
            spec.add_semantic_term_instantiation()
                .expect("term instantiation proof stage checks");
        }
        for name in super::PROOF_ROOTS {
            let definition = spec
                .definitions()
                .get(*name)
                .expect("checked proof present");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        for source in NEGATIVE_CONTROLS {
            assert!(spec
                .add_recursive_def(source, "Reject wrong beta/dependent endpoint.")
                .is_err());
        }
    }
}

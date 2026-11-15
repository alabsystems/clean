// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Applying the same universe substitution preserves semantic universe equality.
//!
//! The existing levelEq_subst_stable theorem is reused, not restated: its proof
//! uses evalL_substL to reindex valuations. These list and expression lifts are
//! different from comparing one fixed body under two pointwise-related
//! substitutions. No reduction, environment or admission invariant is assumed.
//!
//! In particular this is NOT fixed-environment delta/iota commutation. That
//! separate claim needs stored-body support for schematic delta and, in the
//! current universe-blind iota model, parameter-free stored recursor RHSs.
//! Legacy DefEq is unchanged; no DefEqIn substitution theorem is asserted here.
//!
//! Independent check: 27 exact dependency blocks from actual checkpoint
//! 9f368f80a/hvs0z0, export SHA256
//! b5ff6fa3fc255b6dd1bcce19223911ee2babde3374e91508243ccad7773f861f.
//! Pinned Lean 4.30.0-rc2 checked all 8 new declarations axiom-free on
//! 2026-09-08 (0.40 seconds, 407,814,144-byte max RSS, 1 GB reserved).
//! Exact scratch SHA256:
//! 4845b3b2a072e27a56a974def04484500cccf66cbd7ee7645bace94bfd2bea12.
//! A forged caller leaving only the right side unsubstituted was independently
//! rejected at the intended type mismatch (0.24 seconds, 406,355,968-byte RSS).
//! Reproduce with scratch/clean_model_slice.rb, the exact export and this file.
//! Registered Clean and whole-corpus replay are still separate gates.
//!
//! Next reduction frontier (read-only source audit, not an assumed interface):
//! - delta_universe_instantiation.rs:273 already proves
//!   delta_step_instL_supported env supported s e e' step. Its support premise
//!   concerns each actually looked-up KDefSig BODY under its signature params.
//! - No generic current-iota instL theorem exists. A sufficient structural
//!   premise is: every successful recrule_for env rn cn = some rule has
//!   KExprParamSupport (ListType.nil Name) (recrule_rhs rule). First derive
//!   instL s RHS = RHS from that support, then reconstruct the actual five-bind
//!   iota graph. Arbitrary stored RHSs do not satisfy this premise.
//! - Existing kapp_fn_instL, kapp_args_instL, kexpr_const_name_instL and
//!   instL_apply_spine are in delta_universe_instantiation.rs:126-242;
//!   mapLT_length and list_head_mapLT are in schema.rs:1228/1333.
//!   Actual mapLT/list_take and list_drop commutation are remaining substrate.
//! - typingctxconv_universe_instantiation.rs:54 defeq_instL instead carries
//!   fixed-environment delta/iota output-step closure hypotheses. It is not
//!   proof authority for this new generic DefEqIn target. Once actual generic
//!   iota commutation is derived, raw parallel instL preservation needs its
//!   11-constructor induction (beta/zeta use instL_instantiate); DefEqIn then
//!   needs its own 10-constructor induction, using this module at levels.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def levelListEqSem_substL (s : Name -> Level)
 (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) :
 LevelListEqSem (mapLL (substL s) us) (mapLL (substL s) vs) :=
 LevelListEqSem.rec
  (fun (xs : ListType Level) (ys : ListType Level) (_h : LevelListEqSem xs ys) =>
    LevelListEqSem (mapLL (substL s) xs) (mapLL (substL s) ys))
  LevelListEqSem.nil
  (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
    (huv : levelEqSem u v) (_hxy : LevelListEqSem xs ys)
    (ih : LevelListEqSem (mapLL (substL s) xs) (mapLL (substL s) ys)) =>
    LevelListEqSem.cons (substL s u) (substL s v)
      (mapLL (substL s) xs) (mapLL (substL s) ys)
      (levelEq_subst_stable s u v huv) ih) us vs h",
        "Same universe substitution preserves pointwise semantic level-list equivalence, using the existing levelEq_subst_stable proof through valuation reindexing; no new level axiom or duplicate composition theorem.",
    ),
    (
        r"def kexprUniverseEq_instL (s : Name -> Level)
 (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 KExprUniverseEq (instL s e) (instL s e2) :=
 KExprUniverseEq.rec
  (fun (a : KExpr) (b : KExpr) (_h : KExprUniverseEq a b) =>
    KExprUniverseEq (instL s a) (instL s b))
  (fun (u : Level) (v : Level) (huv : levelEqSem u v) =>
    KExprUniverseEq.sort (substL s u) (substL s v) (levelEq_subst_stable s u v huv))
  (fun (i : Nat) => KExprUniverseEq.bvar i)
  (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr)
    (_hf : KExprUniverseEq f f2) (_ha : KExprUniverseEq a a2)
    (ihf : KExprUniverseEq (instL s f) (instL s f2)) (iha : KExprUniverseEq (instL s a) (instL s a2)) =>
    KExprUniverseEq.app (instL s f) (instL s f2) (instL s a) (instL s a2) ihf iha)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_hA : KExprUniverseEq A A2) (_hb : KExprUniverseEq b b2)
    (ihA : KExprUniverseEq (instL s A) (instL s A2)) (ihb : KExprUniverseEq (instL s b) (instL s b2)) =>
    KExprUniverseEq.lam (instL s A) (instL s A2) (instL s b) (instL s b2) ihA ihb)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_hA : KExprUniverseEq A A2) (_hb : KExprUniverseEq b b2)
    (ihA : KExprUniverseEq (instL s A) (instL s A2)) (ihb : KExprUniverseEq (instL s b) (instL s b2)) =>
    KExprUniverseEq.pi (instL s A) (instL s A2) (instL s b) (instL s b2) ihA ihb)
  (fun (n : Name) (us : ListType Level) (vs : ListType Level) (hus : LevelListEqSem us vs) =>
    KExprUniverseEq.const n (mapLL (substL s) us) (mapLL (substL s) vs)
      (levelListEqSem_substL s us vs hus))
  (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
    (_hA : KExprUniverseEq A A2) (_hv : KExprUniverseEq v v2) (_hb : KExprUniverseEq b b2)
    (ihA : KExprUniverseEq (instL s A) (instL s A2)) (ihv : KExprUniverseEq (instL s v) (instL s v2))
    (ihb : KExprUniverseEq (instL s b) (instL s b2)) =>
    KExprUniverseEq.let_ (instL s A) (instL s A2) (instL s v) (instL s v2) (instL s b) (instL s b2) ihA ihv ihb)
  (fun (n : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (_hsub : KExprUniverseEq sub sub2)
    (ih : KExprUniverseEq (instL s sub) (instL s sub2)) =>
    KExprUniverseEq.proj n i (instL s sub) (instL s sub2) ih)
  (fun (n : Nat) => KExprUniverseEq.lit n) e e2 h",
        "Semantic universe equivalence itself is stable under the same actual instL substitution, by all nine relation constructors. Distinct from fixed-body comparison under two pointwise-related substitutions. No reduction environment, typing, support, NoDup or admission premise.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def semantic_universe_subst_nonidentity (n : Name) : Level :=
 Level.succ (Level.param n)",
        "Nonidentity substitution: every universe parameter is replaced by its successor, rather than erased or left unchanged.",
    ),
    (
        r"def semantic_universe_subst_changes_param :
 levelEqSem (Level.param Name.anonymous)
   (substL semantic_universe_subst_nonidentity (Level.param Name.anonymous)) -> Empty :=
 fun (h : levelEqSem (Level.param Name.anonymous)
   (substL semantic_universe_subst_nonidentity (Level.param Name.anonymous))) =>
 nat_zero_ne_succ Nat.zero Empty (h (fun (_n : Name) => Nat.zero))",
        "Actual nonidentity control: at the zero valuation the original parameter evaluates to zero and its substituted successor to one; semantic equality would contradict proved Nat no-confusion.",
    ),
    (
        r"def semantic_universe_subst_input : KExpr :=
 KExpr.lam (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))
   (KExpr.const Name.anonymous
     (ListType.cons Level (Level.imax (Level.param Name.anonymous) Level.zero) (ListType.nil Level)))",
        "Universe-parametric binder and constant-level-list input for an actual caller of same-substitution semantic stability.",
    ),
    (
        r"def semantic_universe_subst_target : KExpr :=
 KExpr.lam (KExpr.sort Level.zero)
   (KExpr.const Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level)))",
        "Semantically simplified binder and constant universe arguments; this target is unchanged by the chosen substitution.",
    ),
    (
        r"def semantic_universe_subst_input_related :
 KExprUniverseEq semantic_universe_subst_input semantic_universe_subst_target :=
 KExprUniverseEq.lam
  (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.sort Level.zero)
  (KExpr.const Name.anonymous (ListType.cons Level (Level.imax (Level.param Name.anonymous) Level.zero) (ListType.nil Level)))
  (KExpr.const Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level)))
  (kexprUniverseEq_imax_zero (Level.param Name.anonymous))
  (KExprUniverseEq.const Name.anonymous
    (ListType.cons Level (Level.imax (Level.param Name.anonymous) Level.zero) (ListType.nil Level))
    (ListType.cons Level Level.zero (ListType.nil Level))
    (LevelListEqSem.cons (Level.imax (Level.param Name.anonymous) Level.zero) Level.zero
      (ListType.nil Level) (ListType.nil Level)
      (fun (_rho : Name -> Nat) => Eq.refl Nat Nat.zero) LevelListEqSem.nil))",
        "An inhabited source relation simultaneously simplifies an open universe parameter under imax in a binder annotation and a constant's actual level list.",
    ),
    (
        r"def semantic_universe_subst_nonidentity_caller :
 KExprUniverseEq (instL semantic_universe_subst_nonidentity semantic_universe_subst_input)
   semantic_universe_subst_target :=
 kexprUniverseEq_instL semantic_universe_subst_nonidentity
   semantic_universe_subst_input semantic_universe_subst_target semantic_universe_subst_input_related",
        "The actual same-substitution theorem preserves the parametric imax simplification under a separately proved nonidentity substitution, including both binder and constant level-list paths.",
    ),
];

impl Specification {
    /// Requires semantic universe relations, actual instL/mapLL operators and
    /// the existing levelEq_subst_stable theorem. Controls also use Nat no-confusion.
    pub(super) fn add_semantic_universe_substitution(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    #[test]
    fn semantic_same_substitution_and_nonidentity_caller_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "evalL_substL",
            "levelEq_subst_stable",
            "levelListEqSem_substL",
            "kexprUniverseEq_instL",
            "semantic_universe_subst_changes_param",
            "semantic_universe_subst_input_related",
            "semantic_universe_subst_nonidentity_caller",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked same-substitution declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn semantic_substitution_cannot_silently_leave_one_side_unchanged() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = crate::test_utils::build_spec_with_stack();
            assert!(spec.add_recursive_def(
                "def semantic_universe_subst_forged_unchanged : KExprUniverseEq (instL semantic_universe_subst_nonidentity (KExpr.sort (Level.param Name.anonymous))) (KExpr.sort (Level.param Name.anonymous)) := kexprUniverseEq_instL semantic_universe_subst_nonidentity (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort (Level.param Name.anonymous)) (KExprUniverseEq.sort (Level.param Name.anonymous) (Level.param Name.anonymous) (fun (rho : Name -> Nat) => Eq.refl Nat (evalL rho (Level.param Name.anonymous))))",
                "Rejected control: preservation applies the same substitution to both sides; successor of a parameter is not semantically the original parameter."
            ).is_err());
        });
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe substitution for the actual shared-signature delta operation.
//!
//! Stored-body parameter support is the only semantic environment premise.
//! Successful guarded lookup supplies the actual shared record, exact arity,
//! and result; preserved arity and supported raw fusion derive the new lookup.
//! All nine expression constructors, actual head universe arguments and the
//! complete term spine are preserved. No per-instantiated equality or typing
//! result is assumed. This does not establish production admission/support,
//! reflected-universe fidelity, smart-level semantics or Rust refinement.
//!
//! Independently checked exact-export prototype:
//! scratch/self-verification-delta-universe-2026-09-08.lean.
//! This file is initially unregistered; the bundle owner must place the general
//! stage after delta_signature_lookup, universe_support_fusion and mapLT's
//! early schema objects, plus the existing reduction-family constructor/view
//! pair, before subject reduction if it consumes the theorem.
//! Controls additionally need the later support controls and kexpr_sort_inj.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn delta_universe_theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Pure head/name views of raw universe instantiation. These unchanged
    /// structural proofs also serve the subset-bundle faithful checkers; they
    /// do not depend on supported lookup fusion or the later schema objects.
    pub(super) fn add_universe_instantiation_head_views(&mut self) -> Result<(), SpecError> {
        delta_universe_theorem(
            self,
            "kapp_fn_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq KExpr (kapp_fn (instL s (e))) (instL s (kapp_fn (e)))",
            r"fun (s : Name -> Level) (e : KExpr) =>
KExpr.rec (fun (e : KExpr) => Eq KExpr (kapp_fn (instL s (e))) (instL s (kapp_fn (e))))
  (fun (u : Level)  => Eq.refl KExpr (instL s (KExpr.sort u)))
  (fun (i : Nat)  => Eq.refl KExpr (instL s (KExpr.bvar i)))
  (fun (f : KExpr) (a : KExpr) (ihf : Eq KExpr (kapp_fn (instL s (f))) (instL s (kapp_fn (f)))) (iha : Eq KExpr (kapp_fn (instL s (a))) (instL s (kapp_fn (a)))) => ihf)
  (fun (A : KExpr) (b : KExpr) (ihA : Eq KExpr (kapp_fn (instL s (A))) (instL s (kapp_fn (A)))) (ihb : Eq KExpr (kapp_fn (instL s (b))) (instL s (kapp_fn (b)))) => Eq.refl KExpr (instL s (KExpr.lam A b)))
  (fun (A : KExpr) (B : KExpr) (ihA : Eq KExpr (kapp_fn (instL s (A))) (instL s (kapp_fn (A)))) (ihB : Eq KExpr (kapp_fn (instL s (B))) (instL s (kapp_fn (B)))) => Eq.refl KExpr (instL s (KExpr.pi A B)))
  (fun (n : Name) (us : ListType Level)  => Eq.refl KExpr (instL s (KExpr.const n us)))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : Eq KExpr (kapp_fn (instL s (A))) (instL s (kapp_fn (A)))) (ihv : Eq KExpr (kapp_fn (instL s (v))) (instL s (kapp_fn (v)))) (ihb : Eq KExpr (kapp_fn (instL s (b))) (instL s (kapp_fn (b)))) => Eq.refl KExpr (instL s (KExpr.let_ A v b)))
  (fun (n : Name) (i : Nat) (e : KExpr) (ihe : Eq KExpr (kapp_fn (instL s (e))) (instL s (kapp_fn (e)))) => Eq.refl KExpr (instL s (KExpr.proj n i e)))
  (fun (n : Nat)  => Eq.refl KExpr (instL s (KExpr.lit n))) e",
            "Universe substitution commutes with application-head extraction, over all nine expression constructors.",
        )?;

        delta_universe_theorem(
            self,
            "kexpr_const_name_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq (OptionType Name) (kexpr_const_name (instL s (e))) (kexpr_const_name (e))",
            r"fun (s : Name -> Level) (e : KExpr) =>
KExpr.rec (fun (e : KExpr) => Eq (OptionType Name) (kexpr_const_name (instL s (e))) (kexpr_const_name (e)))
  (fun (u : Level)  => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (i : Nat)  => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (f : KExpr) (a : KExpr) (ihf : Eq (OptionType Name) (kexpr_const_name (instL s (f))) (kexpr_const_name (f))) (iha : Eq (OptionType Name) (kexpr_const_name (instL s (a))) (kexpr_const_name (a))) => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (A : KExpr) (b : KExpr) (ihA : Eq (OptionType Name) (kexpr_const_name (instL s (A))) (kexpr_const_name (A))) (ihb : Eq (OptionType Name) (kexpr_const_name (instL s (b))) (kexpr_const_name (b))) => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (A : KExpr) (B : KExpr) (ihA : Eq (OptionType Name) (kexpr_const_name (instL s (A))) (kexpr_const_name (A))) (ihB : Eq (OptionType Name) (kexpr_const_name (instL s (B))) (kexpr_const_name (B))) => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (n : Name) (us : ListType Level)  => Eq.refl (OptionType Name) (OptionType.some Name n))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : Eq (OptionType Name) (kexpr_const_name (instL s (A))) (kexpr_const_name (A))) (ihv : Eq (OptionType Name) (kexpr_const_name (instL s (v))) (kexpr_const_name (v))) (ihb : Eq (OptionType Name) (kexpr_const_name (instL s (b))) (kexpr_const_name (b))) => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (n : Name) (i : Nat) (e : KExpr) (ihe : Eq (OptionType Name) (kexpr_const_name (instL s (e))) (kexpr_const_name (e))) => Eq.refl (OptionType Name) (OptionType.none Name))
  (fun (n : Nat)  => Eq.refl (OptionType Name) (OptionType.none Name)) e",
            "Universe substitution preserves the constant-name view; no claim that universe arguments are unchanged.",
        )?;

        delta_universe_theorem(
            self,
            "delta_head_name_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn (instL s e))) (kexpr_const_name (kapp_fn e))",
            r"fun (s : Name -> Level) (e : KExpr) =>
 Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (instL s e))) (kexpr_const_name (instL s (kapp_fn e))) (kexpr_const_name (kapp_fn e))
   (Eq.cong KExpr (OptionType Name) (fun (h : KExpr) => kexpr_const_name h)
     (kapp_fn (instL s e)) (instL s (kapp_fn e)) (kapp_fn_instL s e))
   (kexpr_const_name_instL s (kapp_fn e))",
            "Compose the actual application-head and constant-view transport lemmas.",
        )?;

        Ok(())
    }

    /// Pure general closure proofs; no dependency on later model-to-model
    /// bridges, schema lemmas, support controls or subject reduction.
    pub(super) fn add_delta_universe_instantiation(&mut self) -> Result<(), SpecError> {
        delta_universe_theorem(
            self,
            "kdef_value_at_instL_supported_at",
            r"forall (env : DefEnv) (n : Name) (us : ListType Level) (A : KExpr),
 Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr A) ->
 (forall (sig : KDefSig), Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig sig) ->
   KExprParamSupport (kconst_params (kdef_signature sig)) (kdef_value sig)) ->
 forall (s : Name -> Level),
 Eq (OptionType KExpr) (kdef_value_at env n (mapLL (substL s) us))
   (OptionType.some KExpr (instL s A))",
            r"fun (env : DefEnv) (n : Name) (us : ListType Level) (A : KExpr)
 (accepted : Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr A))
 (supported : forall (sig : KDefSig),
   Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig sig) ->
   KExprParamSupport (kconst_params (kdef_signature sig)) (kdef_value sig))
 (s : Name -> Level) =>
 kdef_value_at_some_inv_prop env n us A accepted
   (Eq (OptionType KExpr) (kdef_value_at env n (mapLL (substL s) us))
     (OptionType.some KExpr (instL s A)))
   (fun (sig : KDefSig)
     (found : Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig sig))
     (arity : kconst_arity (kdef_signature sig) us)
     (result : Eq KExpr A (kdef_inst_value sig us)) =>
     Eq.trans (OptionType KExpr)
       (kdef_value_at env n (mapLL (substL s) us))
       (OptionType.some KExpr (kdef_inst_value sig (mapLL (substL s) us)))
       (OptionType.some KExpr (instL s A))
       (kdef_value_at_intro env n sig (mapLL (substL s) us) found
         (arity_mapLL (kconst_params (kdef_signature sig)) us arity (substL s)))
       (Eq.cong KExpr (OptionType KExpr)
         (fun (T : KExpr) => OptionType.some KExpr T)
         (kdef_inst_value sig (mapLL (substL s) us)) (instL s A)
         (Eq.trans KExpr
           (kdef_inst_value sig (mapLL (substL s) us))
           (instL s (kdef_inst_value sig us)) (instL s A)
           (Eq.symm KExpr (instL s (kdef_inst_value sig us))
             (kdef_inst_value sig (mapLL (substL s) us))
             (instL_instLevels_supported (kconst_params (kdef_signature sig)) (kdef_value sig) us
               (supported sig found) s))
           (Eq.cong KExpr KExpr (fun (T : KExpr) => instL s T)
             (kdef_inst_value sig us) A
             (Eq.symm KExpr A (kdef_inst_value sig us) result)))))",
            "Computed successful definition lookup commutes with universe substitution from support of the actual body at the queried name. Inversion supplies real lookup, exact arity and the original result equation; mapped arity and supported fusion derive the new result. No per-instantiated-output law is assumed.",
        )?;

        delta_universe_theorem(
            self,
            "kdef_value_at_instL_supported",
            r"forall (env : DefEnv),
 (forall (n : Name) (sig : KDefSig),
   Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig sig) ->
   KExprParamSupport (kconst_params (kdef_signature sig)) (kdef_value sig)) ->
 forall (n : Name) (us : ListType Level) (A : KExpr),
 Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr A) ->
 forall (s : Name -> Level),
 Eq (OptionType KExpr) (kdef_value_at env n (mapLL (substL s) us))
   (OptionType.some KExpr (instL s A))",
            r"fun (env : DefEnv)
 (supported : forall (n : Name) (sig : KDefSig),
   Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig sig) ->
   KExprParamSupport (kconst_params (kdef_signature sig)) (kdef_value sig))
 (n : Name) (us : ListType Level) (A : KExpr)
 (accepted : Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr A))
 (s : Name -> Level) =>
 kdef_value_at_instL_supported_at env n us A accepted (supported n) s",
            "Environment-wide corollary: support is required only of each stored schematic body under its own declared parameters. This discharges the computed constant-lookup case, not the other typing/conversion cases or production admission.",
        )?;

        delta_universe_theorem(
            self,
            "kexpr_const_levels_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq (ListType Level) (kexpr_const_levels (instL s (e))) (mapLL (substL s) (kexpr_const_levels (e)))",
            r"fun (s : Name -> Level) (e : KExpr) =>
KExpr.rec (fun (e : KExpr) => Eq (ListType Level) (kexpr_const_levels (instL s (e))) (mapLL (substL s) (kexpr_const_levels (e))))
  (fun (u : Level)  => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (i : Nat)  => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (f : KExpr) (a : KExpr) (ihf : Eq (ListType Level) (kexpr_const_levels (instL s (f))) (mapLL (substL s) (kexpr_const_levels (f)))) (iha : Eq (ListType Level) (kexpr_const_levels (instL s (a))) (mapLL (substL s) (kexpr_const_levels (a)))) => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (A : KExpr) (b : KExpr) (ihA : Eq (ListType Level) (kexpr_const_levels (instL s (A))) (mapLL (substL s) (kexpr_const_levels (A)))) (ihb : Eq (ListType Level) (kexpr_const_levels (instL s (b))) (mapLL (substL s) (kexpr_const_levels (b)))) => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (A : KExpr) (B : KExpr) (ihA : Eq (ListType Level) (kexpr_const_levels (instL s (A))) (mapLL (substL s) (kexpr_const_levels (A)))) (ihB : Eq (ListType Level) (kexpr_const_levels (instL s (B))) (mapLL (substL s) (kexpr_const_levels (B)))) => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (n : Name) (us : ListType Level)  => Eq.refl (ListType Level) (mapLL (substL s) us))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : Eq (ListType Level) (kexpr_const_levels (instL s (A))) (mapLL (substL s) (kexpr_const_levels (A)))) (ihv : Eq (ListType Level) (kexpr_const_levels (instL s (v))) (mapLL (substL s) (kexpr_const_levels (v)))) (ihb : Eq (ListType Level) (kexpr_const_levels (instL s (b))) (mapLL (substL s) (kexpr_const_levels (b)))) => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (n : Name) (i : Nat) (e : KExpr) (ihe : Eq (ListType Level) (kexpr_const_levels (instL s (e))) (mapLL (substL s) (kexpr_const_levels (e)))) => Eq.refl (ListType Level) (ListType.nil Level))
  (fun (n : Nat)  => Eq.refl (ListType Level) (ListType.nil Level)) e",
            "The actual constant universe-argument view maps substitution, including every nonconstant default.",
        )?;

        delta_universe_theorem(
            self,
            "delta_instL_map_append",
            r"forall (s : Name -> Level) (xs : ListType KExpr) (ys : ListType KExpr),
 Eq (ListType KExpr) (mapLT (instL s) (list_append xs ys))
   (list_append (mapLT (instL s) xs) (mapLT (instL s) ys))",
            r"fun (s : Name -> Level) (xs : ListType KExpr) (ys : ListType KExpr) =>
 ListType.rec KExpr
   (fun (zs : ListType KExpr) => Eq (ListType KExpr)
     (mapLT (instL s) (list_append zs ys))
     (list_append (mapLT (instL s) zs) (mapLT (instL s) ys)))
   (Eq.refl (ListType KExpr) (mapLT (instL s) ys))
   (fun (x : KExpr) (rest : ListType KExpr)
     (ih : Eq (ListType KExpr) (mapLT (instL s) (list_append rest ys))
       (list_append (mapLT (instL s) rest) (mapLT (instL s) ys))) =>
     Eq.cong (ListType KExpr) (ListType KExpr)
       (fun (zs : ListType KExpr) => ListType.cons KExpr (instL s x) zs)
       (mapLT (instL s) (list_append rest ys))
       (list_append (mapLT (instL s) rest) (mapLT (instL s) ys)) ih) xs",
            "Early list mapping/append prerequisite for delta's actual spine; does not depend on the later schema proof stage.",
        )?;

        delta_universe_theorem(
            self,
            "kapp_args_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq (ListType KExpr) (kapp_args (instL s (e))) (mapLT (instL s) (kapp_args (e)))",
            r"fun (s : Name -> Level) (e : KExpr) =>
KExpr.rec (fun (e : KExpr) => Eq (ListType KExpr) (kapp_args (instL s (e))) (mapLT (instL s) (kapp_args (e))))
  (fun (u : Level)  => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (i : Nat)  => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (f : KExpr) (a : KExpr) (ihf : Eq (ListType KExpr) (kapp_args (instL s (f))) (mapLT (instL s) (kapp_args (f)))) (iha : Eq (ListType KExpr) (kapp_args (instL s (a))) (mapLT (instL s) (kapp_args (a)))) => Eq.trans (ListType KExpr)
 (list_append (kapp_args (instL s f)) (ListType.cons KExpr (instL s a) (ListType.nil KExpr)))
 (list_append (mapLT (instL s) (kapp_args f)) (ListType.cons KExpr (instL s a) (ListType.nil KExpr)))
 (mapLT (instL s) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))))
 (Eq.cong (ListType KExpr) (ListType KExpr)
   (fun (zs : ListType KExpr) => list_append zs (ListType.cons KExpr (instL s a) (ListType.nil KExpr)))
   (kapp_args (instL s f)) (mapLT (instL s) (kapp_args f)) ihf)
 (Eq.symm (ListType KExpr)
   (mapLT (instL s) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))))
   (list_append (mapLT (instL s) (kapp_args f)) (mapLT (instL s) (ListType.cons KExpr a (ListType.nil KExpr))))
   (delta_instL_map_append s (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))))
  (fun (A : KExpr) (b : KExpr) (ihA : Eq (ListType KExpr) (kapp_args (instL s (A))) (mapLT (instL s) (kapp_args (A)))) (ihb : Eq (ListType KExpr) (kapp_args (instL s (b))) (mapLT (instL s) (kapp_args (b)))) => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (A : KExpr) (B : KExpr) (ihA : Eq (ListType KExpr) (kapp_args (instL s (A))) (mapLT (instL s) (kapp_args (A)))) (ihB : Eq (ListType KExpr) (kapp_args (instL s (B))) (mapLT (instL s) (kapp_args (B)))) => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (n : Name) (us : ListType Level)  => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : Eq (ListType KExpr) (kapp_args (instL s (A))) (mapLT (instL s) (kapp_args (A)))) (ihv : Eq (ListType KExpr) (kapp_args (instL s (v))) (mapLT (instL s) (kapp_args (v)))) (ihb : Eq (ListType KExpr) (kapp_args (instL s (b))) (mapLT (instL s) (kapp_args (b)))) => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (n : Name) (i : Nat) (e : KExpr) (ihe : Eq (ListType KExpr) (kapp_args (instL s (e))) (mapLT (instL s) (kapp_args (e)))) => Eq.refl (ListType KExpr) (ListType.nil KExpr))
  (fun (n : Nat)  => Eq.refl (ListType KExpr) (ListType.nil KExpr)) e",
            "Universe substitution maps every actual argument in the application spine.",
        )?;

        delta_universe_theorem(
            self,
            "instL_apply_spine",
            r"forall (s : Name -> Level) (args : ListType KExpr) (head : KExpr),
 Eq KExpr (instL s (apply_spine args head))
   (apply_spine (mapLT (instL s) args) (instL s head))",
            r"fun (s : Name -> Level) (args : ListType KExpr) =>
 ListType.rec KExpr
   (fun (xs : ListType KExpr) => forall (head : KExpr),
     Eq KExpr (instL s (apply_spine xs head))
       (apply_spine (mapLT (instL s) xs) (instL s head)))
   (fun (head : KExpr) => Eq.refl KExpr (instL s head))
   (fun (x : KExpr) (rest : ListType KExpr)
     (ih : forall (head : KExpr), Eq KExpr (instL s (apply_spine rest head))
       (apply_spine (mapLT (instL s) rest) (instL s head))) =>
     fun (head : KExpr) => ih (KExpr.app head x)) args",
            "Universe substitution commutes with the actual left-fold application-spine function.",
        )?;

        delta_universe_theorem(
            self,
            "delta_head_levels_instL",
            r"forall (s : Name -> Level) (e : KExpr), Eq (ListType Level) (kexpr_const_levels (kapp_fn (instL s e))) (mapLL (substL s) (kexpr_const_levels (kapp_fn e)))",
            r"fun (s : Name -> Level) (e : KExpr) =>
 Eq.trans (ListType Level) (kexpr_const_levels (kapp_fn (instL s e))) (kexpr_const_levels (instL s (kapp_fn e))) (mapLL (substL s) (kexpr_const_levels (kapp_fn e)))
   (Eq.cong KExpr (ListType Level) (fun (h : KExpr) => kexpr_const_levels h)
     (kapp_fn (instL s e)) (instL s (kapp_fn e)) (kapp_fn_instL s e))
   (kexpr_const_levels_instL s (kapp_fn e))",
            "Compose the actual application-head and constant-view transport lemmas.",
        )?;

        delta_universe_theorem(
            self,
            "delta_step_instL_supported",
            r"forall (env : DefEnv), (forall (n : Name) (defn : KDefSig),
 Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig defn) ->
 KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn)) ->
 forall (s : Name -> Level) (e : KExpr) (e' : KExpr),
 delta_step env e e' -> delta_step env (instL s e) (instL s e')",
            r"fun (env : DefEnv) (supported : (forall (n : Name) (defn : KDefSig),
 Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig defn) ->
 KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn)))
 (s : Name -> Level) (e : KExpr) (e' : KExpr) (step : delta_step env e e') =>
 opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn e)) (fun (n : Name) => opt_bind KExpr KExpr
 (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val))) e'
   (delta_step env (instL s e) (instL s e')) step
   (fun (n : Name)
     (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
     (inner : Eq (OptionType KExpr)
       (opt_bind KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)))
       (OptionType.some KExpr e')) =>
     opt_bind_some_inv KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn e)))
       (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) val)) e' (delta_step env (instL s e) (instL s e')) inner
       (fun (v : KExpr)
         (found : Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr v))
         (result : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) v)) (OptionType.some KExpr e')) =>
         Eq.trans (OptionType KExpr) (delta_reduct env (instL s e)) (opt_bind KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn (instL s e)))) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (instL s e)) val)))
           (OptionType.some KExpr (instL s e'))
           (Eq.cong (OptionType Name) (OptionType KExpr)
             (fun (hn : OptionType Name) => opt_bind Name KExpr hn
               (fun (n : Name) => opt_bind KExpr KExpr
                 (kdef_value_at env n (kexpr_const_levels (kapp_fn (instL s e)))) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (instL s e)) val))))
             (kexpr_const_name (kapp_fn (instL s e))) (OptionType.some Name n)
             (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (instL s e)))
               (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)
               (delta_head_name_instL s e) head))
           (Eq.trans (OptionType KExpr) (opt_bind KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn (instL s e)))) (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (instL s e)) val)))
             (OptionType.some KExpr (apply_spine (kapp_args (instL s e)) (instL s v))) (OptionType.some KExpr (instL s e'))
             (Eq.cong (OptionType KExpr) (OptionType KExpr)
               (fun (value : OptionType KExpr) => opt_bind KExpr KExpr value (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args (instL s e)) val)))
               (kdef_value_at env n (kexpr_const_levels (kapp_fn (instL s e))))
               (OptionType.some KExpr (instL s v))
               (Eq.trans (OptionType KExpr)
                 (kdef_value_at env n (kexpr_const_levels (kapp_fn (instL s e))))
                 (kdef_value_at env n (mapLL (substL s) (kexpr_const_levels (kapp_fn e))))
                 (OptionType.some KExpr (instL s v))
                 (Eq.cong (ListType Level) (OptionType KExpr)
                   (fun (us : ListType Level) => kdef_value_at env n us)
                   (kexpr_const_levels (kapp_fn (instL s e)))
                   (mapLL (substL s) (kexpr_const_levels (kapp_fn e)))
                   (delta_head_levels_instL s e))
                 (kdef_value_at_instL_supported env supported n
                   (kexpr_const_levels (kapp_fn e)) v found s)))
             (Eq.cong KExpr (OptionType KExpr)
               (fun (r : KExpr) => OptionType.some KExpr r)
               (apply_spine (kapp_args (instL s e)) (instL s v)) (instL s e')
               (Eq.trans KExpr (apply_spine (kapp_args (instL s e)) (instL s v))
                 (instL s (apply_spine (kapp_args e) v)) (instL s e')
                 (Eq.trans KExpr (apply_spine (kapp_args (instL s e)) (instL s v))
                   (apply_spine (mapLT (instL s) (kapp_args e)) (instL s v))
                   (instL s (apply_spine (kapp_args e) v))
                   (Eq.cong (ListType KExpr) KExpr
                     (fun (args : ListType KExpr) => apply_spine args (instL s v))
                     (kapp_args (instL s e)) (mapLT (instL s) (kapp_args e))
                     (kapp_args_instL s e))
                   (Eq.symm KExpr (instL s (apply_spine (kapp_args e) v))
                     (apply_spine (mapLT (instL s) (kapp_args e)) (instL s v))
                     (instL_apply_spine s (kapp_args e) v)))
                 (Eq.cong KExpr KExpr (fun (r : KExpr) => instL s r)
                   (apply_spine (kapp_args e) v) e'
                   (option_some_inj KExpr (apply_spine (kapp_args e) v) e' result)))))))",
            "Actual guarded delta-step universe-substitution closure, derived from support of stored schematic bodies. Inverts real lookup, preserves actual arity and maps both retained head universes and the complete term spine. No instantiated-result equality, body typing, is assumed. No production admission or source-fidelity claim is made.",
        )?;
        delta_universe_theorem(
            self,
            "delta_reduces_instL_supported",
            r"forall
 (supported : forall (n : Name) (defn : KDefSig),
   Eq (OptionType KDefSig) (kdef_for (red_def the_red_env) n) (OptionType.some KDefSig defn) ->
   KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn))
 (s : Name -> Level) (e : KExpr) (e' : KExpr),
 delta_reduces e e' -> delta_reduces (instL s e) (instL s e')",
            r"fun
 (supported : forall (n : Name) (defn : KDefSig),
   Eq (OptionType KDefSig) (kdef_for (red_def the_red_env) n) (OptionType.some KDefSig defn) ->
   KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn))
 (s : Name -> Level) (e : KExpr) (e' : KExpr) (step : delta_reduces e e') =>
 delta_reduces.mk (instL s e) (instL s e')
   (delta_step_instL_supported (red_def the_red_env) supported s e e'
     (delta_reduces_to_step e e' step))",
            "Fixed-environment delta-reduces closure derived from the generic actual guarded graph theorem and the existing constructor/view pair. The only environment premise is support of stored schematic bodies; no per-instantiated equality or typing is assumed.",
        )?;

        Ok(())
    }

    /// Positive and constructive refusal controls live at the late control
    /// frontier, separately from the proof needed by subject reduction.
    pub(super) fn add_delta_universe_instantiation_controls(&mut self) -> Result<(), SpecError> {
        delta_universe_theorem(
            self,
            "delta_universe_nonzero_spine_witness",
            r"forall (s : Name -> Level),
 delta_step (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (instL s (KExpr.app (KExpr.const Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))) (KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))))) (instL s (KExpr.app (KExpr.sort (Level.param Name.anonymous)) (KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero)))))",
            r"fun (s : Name -> Level) => Eq.refl (OptionType KExpr) (OptionType.some KExpr (instL s (KExpr.app (KExpr.sort (Level.param Name.anonymous)) (KExpr.proj Name.anonymous Nat.zero (KExpr.lit (Nat.succ Nat.zero))))))",
            "Computational positive control: a parameterized definition unfolds at arbitrary nonzero substituted universes and preserves an actual projection/literal application argument.",
        )?;

        delta_universe_theorem(
            self,
            "delta_universe_wrong_arity_none",
            r"forall (s : Name -> Level),
 Eq (OptionType KExpr) (delta_reduct (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (instL s (KExpr.const Name.anonymous (ListType.nil Level)))) (OptionType.none KExpr)",
            r"fun (s : Name -> Level) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "Computational refusal control: mapping universe arguments cannot repair a short universe list; the actual delta graph stays at none rather than exposing raw default instantiation.",
        )?;

        delta_universe_theorem(
            self,
            "delta_universe_unsupported_initial_step",
            r"delta_step (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous)))) (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort (Level.param Name.anonymous))",
            r"Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
            "An exact-arity initial delta step can exist even when the stored body contains an undeclared universe parameter. Successful lookup is not body-support evidence.",
        )?;

        delta_universe_theorem(
            self,
            "delta_universe_unsupported_closure_fails",
            r"delta_step (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous))))
 (instL (fun (_ : Name) => Level.zero) (KExpr.const Name.anonymous (ListType.nil Level)))
 (instL (fun (_ : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous))) -> Empty",
            r"fun (h : delta_step (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous))))
 (instL (fun (_ : Name) => Level.zero) (KExpr.const Name.anonymous (ListType.nil Level)))
 (instL (fun (_ : Name) => Level.zero) (KExpr.sort (Level.param Name.anonymous)))) =>
 unsupported_fusion_fails
   (Eq.symm Level (Level.param Name.anonymous) Level.zero
     (kexpr_sort_inj (Level.param Name.anonymous) Level.zero
       (option_some_inj KExpr (KExpr.sort (Level.param Name.anonymous)) (KExpr.sort Level.zero) h)))",
            "Constructive negative control: dropping stored-body support makes delta universe-substitution closure false, despite successful exact-arity initial unfolding and a supported signature type.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::delta_universe_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn delta_universe_instantiation_has_checked_values_and_no_axiom_residuals() {
        let spec = build_spec_with_stack();
        for name in [
            "kdef_value_at_instL_supported_at",
            "kdef_value_at_instL_supported",
            "kapp_fn_instL",
            "kexpr_const_name_instL",
            "kexpr_const_levels_instL",
            "delta_instL_map_append",
            "kapp_args_instL",
            "instL_apply_spine",
            "delta_head_name_instL",
            "delta_head_levels_instL",
            "delta_step_instL_supported",
            "delta_reduces_instL_supported",
            "delta_universe_nonzero_spine_witness",
            "delta_universe_wrong_arity_none",
            "delta_universe_unsupported_initial_step",
            "delta_universe_unsupported_closure_fails",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered delta universe term");
            assert!(!definition.is_axiom, "{name} must have a proof");
            assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
            assert!(
                definition.elaborated_value.is_some(),
                "{name} must be elaborated"
            );
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have empty actual transitive axiom closure"
            );
        }
    }

    #[test]
    fn delta_universe_closure_cannot_omit_body_support() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            let env = "(DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous))))";
            // The registered initial-step witness checks this lookup succeeds,
            // despite the undeclared parameter in its stored BODY.
            assert!(delta_universe_theorem(
                &mut spec,
                "delta_universe_unsupported_substitution_must_be_rejected",
                &format!("delta_step {env} (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero)"),
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))",
                "Negative control: exact-arity initial success does not imply closure for an unsupported stored body.",
            ).is_err());
        });
    }

    #[test]
    fn delta_universe_wrong_arity_cannot_expose_raw_default() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            let env = "(DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk (KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort Level.zero)) (KExpr.sort (Level.param Name.anonymous))))";
            assert!(delta_universe_theorem(
                &mut spec,
                "delta_universe_short_argument_list_must_be_rejected",
                &format!("delta_step {env} (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero)"),
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))",
                "Negative control: total raw missing-argument defaults cannot bypass delta's actual arity guard.",
            ).is_err());
        });
    }
}

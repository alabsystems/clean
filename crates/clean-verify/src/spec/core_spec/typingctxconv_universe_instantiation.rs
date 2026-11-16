// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conditional universe-substitution preservation for DefEq and TypingCtxConv.
//!
//! The operational delta/iota closure premises are explicit, for the chosen
//! substitution. They are not proved by this module and cannot be replaced by
//! assuming the typing of every instantiated output. DefEq preservation is
//! derived by its actual twelve-constructor induction; typing uses all ten
//! TypingCtxConv rules, including conversion and both tagged literal kinds.
//!
//! The KDefSig corollary derives instantiated-body typing from one schematic
//! derivation. Source-correct delta/iota closure, environment coherence and
//! production smart-level correspondence remain separate obligations.
//! Exact-export check: scratch/self-verification-typingctxconv-instantiation-2026-09-08.lean.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn instantiation_theorem(
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
    /// Requires the signature-aware live TypingCtxConv, actual DefEq/reduction
    /// families, typingctx_universe_instantiation lookup transport, and the
    /// declaration lookup/support and raw lift/instantiate commutation proofs.
    pub(super) fn add_typingctxconv_universe_instantiation(&mut self) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "defeq_instL",
            r"forall (s : Name -> Level),
 (forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL s e) (instL s e')) ->
 (forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL s e) (instL s e')) ->
 forall (a : KExpr) (b : KExpr), DefEq a b -> DefEq (instL s a) (instL s b)",
            r"fun (s : Name -> Level)
 (delta_closed : forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL s e) (instL s e'))
 (iota_closed : forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL s e) (instL s e'))
 (a : KExpr) (b : KExpr) (equivalent : DefEq a b) =>
 @DefEq.rec
   (fun (a0 : KExpr) (b0 : KExpr) (_h : DefEq a0 b0) => DefEq (instL s a0) (instL s b0))
   (fun (a0 : KExpr) => DefEq.refl (instL s a0))
   (fun (a0 : KExpr) (b0 : KExpr) (_h : DefEq a0 b0)
     (ih : DefEq (instL s a0) (instL s b0)) =>
     DefEq.symm (instL s a0) (instL s b0) ih)
   (fun (a0 : KExpr) (b0 : KExpr) (c0 : KExpr) (_hab : DefEq a0 b0) (_hbc : DefEq b0 c0)
     (ihab : DefEq (instL s a0) (instL s b0)) (ihbc : DefEq (instL s b0) (instL s c0)) =>
     DefEq.trans (instL s a0) (instL s b0) (instL s c0) ihab ihbc)
   (fun (A : KExpr) (body : KExpr) (arg : KExpr) =>
     @Eq.substType KExpr
       (fun (T : KExpr) => DefEq (KExpr.app (KExpr.lam (instL s A) (instL s body)) (instL s arg)) T)
       (instantiate (instL s body) (instL s arg)) (instL s (instantiate body arg))
       (@Eq.symm KExpr (instL s (instantiate body arg))
         (instantiate (instL s body) (instL s arg)) (instL_instantiate s body arg))
       (DefEq.beta (instL s A) (instL s body) (instL s arg)))
   (fun (f : KExpr) (f' : KExpr) (arg : KExpr) (arg' : KExpr)
     (_hf : DefEq f f') (_ha : DefEq arg arg')
     (ihf : DefEq (instL s f) (instL s f')) (iha : DefEq (instL s arg) (instL s arg')) =>
     DefEq.app_cong (instL s f) (instL s f') (instL s arg) (instL s arg') ihf iha)
   (fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr)
     (_hA : DefEq A A') (_hb : DefEq body body')
     (ihA : DefEq (instL s A) (instL s A')) (ihb : DefEq (instL s body) (instL s body')) =>
     DefEq.lam_cong (instL s A) (instL s A') (instL s body) (instL s body') ihA ihb)
   (fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr)
     (_hA : DefEq A A') (_hB : DefEq B B')
     (ihA : DefEq (instL s A) (instL s A')) (ihB : DefEq (instL s B) (instL s B')) =>
     DefEq.pi_cong (instL s A) (instL s A') (instL s B) (instL s B') ihA ihB)
   (fun (e : KExpr) (e' : KExpr) (step : delta_reduces e e') =>
     DefEq.delta (instL s e) (instL s e') (delta_closed e e' step))
   (fun (e : KExpr) (e' : KExpr) (step : iota_reduces e e') =>
     DefEq.iota (instL s e) (instL s e') (iota_closed e e' step))
   (fun (ty : KExpr) (value : KExpr) (body : KExpr) =>
     @Eq.substType KExpr
       (fun (T : KExpr) => DefEq (KExpr.let_ (instL s ty) (instL s value) (instL s body)) T)
       (instantiate (instL s body) (instL s value)) (instL s (instantiate body value))
       (@Eq.symm KExpr (instL s (instantiate body value))
         (instantiate (instL s body) (instL s value)) (instL_instantiate s body value))
       (DefEq.zeta (instL s ty) (instL s value) (instL s body)))
   (fun (ty : KExpr) (ty' : KExpr) (value : KExpr) (value' : KExpr) (body : KExpr) (body' : KExpr)
     (_hty : DefEq ty ty') (_hv : DefEq value value') (_hb : DefEq body body')
     (ihty : DefEq (instL s ty) (instL s ty'))
     (ihv : DefEq (instL s value) (instL s value'))
     (ihb : DefEq (instL s body) (instL s body')) =>
     DefEq.let_cong (instL s ty) (instL s ty') (instL s value) (instL s value')
       (instL s body) (instL s body') ihty ihv ihb)
   (fun (sn : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) (_h : DefEq sub sub')
     (ih : DefEq (instL s sub) (instL s sub')) =>
     DefEq.proj_cong sn i (instL s sub) (instL s sub') ih)
   a b equivalent",
            "All twelve actual DefEq constructors preserve raw universe substitution, conditional only on explicit directed delta/iota step closure for that substitution. Beta/zeta use proved term-instantiation commutation; no conversion or typing-preservation law is assumed.",
        )?;

        instantiation_theorem(
            self,
            "instL_literal_nat",
            r"forall (s : Name -> Level) (n : Nat), @Eq KExpr (instL s (literal_nat n)) (literal_nat n)",
            r"fun (s : Name -> Level) (n : Nat) => @Eq.refl KExpr (literal_nat n)",
            "Raw universe substitution preserves every tagged natural-literal payload.",
        )?;

        instantiation_theorem(
            self,
            "instL_literal_nat_type",
            r"forall (s : Name -> Level), @Eq KExpr (instL s literal_nat_type) literal_nat_type",
            r"fun (s : Name -> Level) => @Eq.refl KExpr literal_nat_type",
            "Raw universe substitution preserves the canonical natural-literal type, whose constant carries an empty universe argument list.",
        )?;

        instantiation_theorem(
            self,
            "instL_literal_string",
            r"forall (s : Name -> Level) (n : Nat), @Eq KExpr (instL s (literal_string n)) (literal_string n)",
            r"fun (s : Name -> Level) (n : Nat) => @Eq.refl KExpr (literal_string n)",
            "Raw universe substitution preserves every tagged string-identity payload.",
        )?;

        instantiation_theorem(
            self,
            "instL_literal_string_type",
            r"forall (s : Name -> Level), @Eq KExpr (instL s literal_string_type) literal_string_type",
            r"fun (s : Name -> Level) => @Eq.refl KExpr literal_string_type",
            "Raw universe substitution preserves the canonical string-literal type, whose constant carries an empty universe argument list.",
        )?;

        instantiation_theorem(
            self,
            "typingctxconv_instL",
            r"forall (tenv : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (s : Name -> Level),
 (forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL s e) (instL s e')) ->
 (forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL s e) (instL s e')) ->
 forall (G : ListType KExpr) (e : KExpr) (T : KExpr),
 TypingCtxConv tenv G e T ->
 TypingCtxConv tenv (mapLT (instL s) G) (instL s e) (instL s T)",
            r"fun (tenv : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (s : Name -> Level)
 (delta_closed : forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL s e) (instL s e'))
 (iota_closed : forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL s e) (instL s e'))
 (G : ListType KExpr) (e : KExpr) (T : KExpr)
 (typed : TypingCtxConv tenv G e T) =>
 @TypingCtxConv.rec tenv
   (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
     (_h : TypingCtxConv tenv G0 e0 T0) =>
     TypingCtxConv tenv (mapLT (instL s) G0) (instL s e0) (instL s T0))
   (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
     (found : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConv tenv (mapLT (instL s) G0) (KExpr.bvar i) T0)
       (lift_at (instL s A) Nat.zero (Nat.succ i))
       (instL s (lift_at A Nat.zero (Nat.succ i)))
       (@Eq.symm KExpr (instL s (lift_at A Nat.zero (Nat.succ i)))
         (lift_at (instL s A) Nat.zero (Nat.succ i))
         (instL_lift_at s A Nat.zero (Nat.succ i)))
       (@TypingCtxConv.var tenv (mapLT (instL s) G0) i (instL s A)
         (ctx_lookup_mapLT_some (instL s) G0 i A found)))
   (fun (G0 : ListType KExpr) (u : Level) =>
     @TypingCtxConv.sort tenv (mapLT (instL s) G0) (substL s u))
   (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
     (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
     (_hB : TypingCtxConv tenv (@ListType.cons KExpr A G0) B (KExpr.sort v))
     (ihA : TypingCtxConv tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihB : TypingCtxConv tenv (mapLT (instL s) (@ListType.cons KExpr A G0)) (instL s B) (instL s (KExpr.sort v))) =>
     @TypingCtxConv.pi tenv (mapLT (instL s) G0) (instL s A) (instL s B)
       (substL s u) (substL s v) ihA ihB)
   (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
     (_hb : TypingCtxConv tenv (@ListType.cons KExpr A G0) b B)
     (ihA : TypingCtxConv tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihb : TypingCtxConv tenv (mapLT (instL s) (@ListType.cons KExpr A G0)) (instL s b) (instL s B)) =>
     @TypingCtxConv.lam tenv (mapLT (instL s) G0) (instL s A) (instL s b) (instL s B)
       (substL s u) ihA ihb)
   (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
     (_hf : TypingCtxConv tenv G0 f (KExpr.pi A B))
     (_ha : TypingCtxConv tenv G0 a A)
     (ihf : TypingCtxConv tenv (mapLT (instL s) G0) (instL s f) (instL s (KExpr.pi A B)))
     (iha : TypingCtxConv tenv (mapLT (instL s) G0) (instL s a) (instL s A)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConv tenv (mapLT (instL s) G0)
         (KExpr.app (instL s f) (instL s a)) T0)
       (instantiate (instL s B) (instL s a)) (instL s (instantiate B a))
       (@Eq.symm KExpr (instL s (instantiate B a))
         (instantiate (instL s B) (instL s a)) (instL_instantiate s B a))
       (@TypingCtxConv.app tenv (mapLT (instL s) G0)
         (instL s f) (instL s a) (instL s A) (instL s B) ihf iha))
   (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
     (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
     @TypingCtxConv.const tenv (mapLT (instL s) G0) n (mapLL (substL s) us) (instL s A)
       (kdecl_type_at_instL_supported tenv supported n us A found s))
   (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
     (_typed : TypingCtxConv tenv G0 e0 A) (equivalent : DefEq A B)
     (ih : TypingCtxConv tenv (mapLT (instL s) G0) (instL s e0) (instL s A)) =>
     @TypingCtxConv.conv tenv (mapLT (instL s) G0) (instL s e0) (instL s A) (instL s B)
       ih (defeq_instL s delta_closed iota_closed A B equivalent))
   (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hty : TypingCtxConv tenv G0 ty (KExpr.sort u))
     (_hv : TypingCtxConv tenv G0 v ty)
     (_hb : TypingCtxConv tenv (@ListType.cons KExpr ty G0) b B)
     (ihty : TypingCtxConv tenv (mapLT (instL s) G0) (instL s ty) (instL s (KExpr.sort u)))
     (ihv : TypingCtxConv tenv (mapLT (instL s) G0) (instL s v) (instL s ty))
     (ihb : TypingCtxConv tenv (mapLT (instL s) (@ListType.cons KExpr ty G0)) (instL s b) (instL s B)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConv tenv (mapLT (instL s) G0)
         (KExpr.let_ (instL s ty) (instL s v) (instL s b)) T0)
       (instantiate (instL s B) (instL s v)) (instL s (instantiate B v))
       (@Eq.symm KExpr (instL s (instantiate B v))
         (instantiate (instL s B) (instL s v)) (instL_instantiate s B v))
       (@TypingCtxConv.let_ tenv (mapLT (instL s) G0)
         (instL s ty) (instL s v) (instL s b) (instL s B) (substL s u)
         ihty ihv ihb))
   (fun (G0 : ListType KExpr) (n : Nat) =>
     @TypingCtxConv.lit_nat tenv (mapLT (instL s) G0) n)
   (fun (G0 : ListType KExpr) (n : Nat) =>
     @TypingCtxConv.lit_string tenv (mapLT (instL s) G0) n)
   G e T typed",
            "Universe-substitution preservation for all ten signature-aware TypingCtxConv constructors. Premises are stored schematic-type support and explicit operational delta/iota closure at the chosen substitution; neither conversion preservation nor instantiated-output typing is assumed.",
        )?;

        instantiation_theorem(
            self,
            "typingctxconv_instLevels",
            r"forall (tenv : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (ps : ListType Name) (us : ListType Level),
 (forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL (paramSubstN ps us) e) (instL (paramSubstN ps us) e')) ->
 (forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL (paramSubstN ps us) e) (instL (paramSubstN ps us) e')) ->
 forall (G : ListType KExpr) (e : KExpr) (T : KExpr),
 TypingCtxConv tenv G e T ->
 TypingCtxConv tenv (mapLT (instL (paramSubstN ps us)) G)
   (instLevels ps e us) (instLevels ps T us)",
            r"fun (tenv : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (ps : ListType Name) (us : ListType Level)
 (delta_closed : forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces (instL (paramSubstN ps us) e) (instL (paramSubstN ps us) e'))
 (iota_closed : forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces (instL (paramSubstN ps us) e) (instL (paramSubstN ps us) e'))
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (typed : TypingCtxConv tenv G e T) =>
 typingctxconv_instL tenv supported (paramSubstN ps us) delta_closed iota_closed G e T typed",
            "Specialize the checked conversion-aware typing preservation theorem to the concrete paramSubstN/instLevels substitution. Operational closure remains an explicit premise, not a discharged source/model fact.",
        )?;

        instantiation_theorem(
            self,
            "typingctxconv_kdef_instantiated",
            r"forall (tenv : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (defn : KDefSig) (us : ListType Level),
 (forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e)
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e')) ->
 (forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e)
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e')) ->
 TypingCtxConv tenv (@ListType.nil KExpr) (kdef_value defn) (kconst_type (kdef_signature defn)) ->
 TypingCtxConv tenv (@ListType.nil KExpr) (kdef_inst_value defn us)
   (kconst_inst_type (kdef_signature defn) us)",
            r"fun (tenv : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (defn : KDefSig) (us : ListType Level)
 (delta_closed : forall (e : KExpr) (e' : KExpr), delta_reduces e e' ->
   delta_reduces
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e)
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e'))
 (iota_closed : forall (e : KExpr) (e' : KExpr), iota_reduces e e' ->
   iota_reduces
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e)
     (instL (paramSubstN (kconst_params (kdef_signature defn)) us) e'))
 (schematic : TypingCtxConv tenv (@ListType.nil KExpr)
   (kdef_value defn) (kconst_type (kdef_signature defn))) =>
 typingctxconv_instLevels tenv supported (kconst_params (kdef_signature defn)) us
   delta_closed iota_closed (@ListType.nil KExpr)
   (kdef_value defn) (kconst_type (kdef_signature defn)) schematic",
            "Derive an instantiated definition value's type from ONE schematic empty-context body-typing derivation, shared KDefSig parameters, stored-type support and the explicit operational closure premises. This is a derived conclusion, not a strengthened defval_typed field.",
        )?;

        // ── DECLARATION-ENVIRONMENT MONOTONICITY ────────────────────────────
        //
        // The property every incremental checker relies on and that this spec
        // did not state: a derivation obtained in `tenv` survives into any
        // environment that PRESERVES `tenv`'s entries. Nine of the ten rules
        // re-assemble their induction hypotheses unchanged; the whole content
        // is the `const` arm, because `const` carries the only premise in the
        // judgment that reads `tenv` at all.
        //
        // WHY THE HYPOTHESIS IS SHAPED THAT WAY, and why it cannot be weakened
        // to "defined wherever `tenv` is": `kdecl_type_at` reads `env` at the
        // single point `n` and then GUARDS on the stored signature's parameter
        // count against `us`. An extension free to rebind `n` to a different
        // signature changes the returned type, and one free to change the
        // parameter list's LENGTH sends the lookup to `none` outright. So the
        // premise has to preserve the signature itself, not merely its
        // definedness. `typingctxconv_tenv_mono_no_hyp_probe` is the control:
        // the same term with the hypothesis dropped has nothing to build
        // `ext n sig hlk` from and the kernel refuses it.
        //
        // MEASURED, and recorded because it is the obvious next move and it
        // does not work: this does NOT compose with
        // `kernel_add_decl_extends_env`
        // (`implementation_soundness_env_preservation.rs`). That lemma is over
        // `KEnv` — the structural `empty | addConst | addInductive` environment
        // of the Phase-4 definitional-extension lane (`env_extensions.rs`) —
        // and `TypingCtxConv`'s environment is `KDeclEnv`, which is the
        // FUNCTION `Name -> OptionType KConstSig` (`declaration_signatures.rs`).
        // Two different types with no bridge in this tree, so "add_decl
        // preserves every earlier derivation" is NOT available from these two
        // and would need that bridge first. Naming the gap is the point.
        //
        // NO CONSUMER TODAY, stated rather than implied: `TypingCtx`'s
        // consumers (`fundamental_general`, the Hurkens block, `typingctx_instL`)
        // all hold `tenv` FIXED. This is registered over the ten-constructor
        // `TypingCtxConv` rather than the conv-free `TypingCtx` because
        // `TypingCtxConv` is what the Layer-1 / ImplInfer soundness lane targets
        // (`impl_infer_sound.rs`), so that is where a consumer would arrive. The
        // conv-free twin is this proof minus three arms and is deliberately not
        // written: an unconsumed lemma is worth one, not two.
        instantiation_theorem(
            self,
            "typingctxconv_tenv_mono",
            r"forall (tenv : KDeclEnv) (tenv2 : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   @Eq (OptionType KConstSig) (tenv2 n) (@OptionType.some KConstSig sig)) ->
 forall (G : ListType KExpr) (e : KExpr) (T : KExpr),
 TypingCtxConv tenv G e T ->
 TypingCtxConv tenv2 G e T",
            r"fun (tenv : KDeclEnv) (tenv2 : KDeclEnv)
 (ext : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   @Eq (OptionType KConstSig) (tenv2 n) (@OptionType.some KConstSig sig))
 (G : ListType KExpr) (e : KExpr) (T : KExpr)
 (typed : TypingCtxConv tenv G e T) =>
 @TypingCtxConv.rec tenv
   (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
     (_h : TypingCtxConv tenv G0 e0 T0) =>
     TypingCtxConv tenv2 G0 e0 T0)
   (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
     (found : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
     @TypingCtxConv.var tenv2 G0 i A found)
   (fun (G0 : ListType KExpr) (u : Level) =>
     @TypingCtxConv.sort tenv2 G0 u)
   (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
     (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
     (_hB : TypingCtxConv tenv (@ListType.cons KExpr A G0) B (KExpr.sort v))
     (ihA : TypingCtxConv tenv2 G0 A (KExpr.sort u))
     (ihB : TypingCtxConv tenv2 (@ListType.cons KExpr A G0) B (KExpr.sort v)) =>
     @TypingCtxConv.pi tenv2 G0 A B u v ihA ihB)
   (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
     (_hb : TypingCtxConv tenv (@ListType.cons KExpr A G0) b B)
     (ihA : TypingCtxConv tenv2 G0 A (KExpr.sort u))
     (ihb : TypingCtxConv tenv2 (@ListType.cons KExpr A G0) b B) =>
     @TypingCtxConv.lam tenv2 G0 A b B u ihA ihb)
   (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
     (_hf : TypingCtxConv tenv G0 f (KExpr.pi A B))
     (_ha : TypingCtxConv tenv G0 a A)
     (ihf : TypingCtxConv tenv2 G0 f (KExpr.pi A B))
     (iha : TypingCtxConv tenv2 G0 a A) =>
     @TypingCtxConv.app tenv2 G0 f a A B ihf iha)
   (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
     (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
     kdecl_type_at_some_inv tenv n us A found
       (TypingCtxConv tenv2 G0 (KExpr.const n us) A)
       (fun (sig : KConstSig)
         (hlk : @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig))
         (harity : kconst_arity sig us)
         (hres : @Eq KExpr A (kconst_inst_type sig us)) =>
         @TypingCtxConv.const tenv2 G0 n us A
           (@Eq.trans (OptionType KExpr)
             (kdecl_type_at tenv2 n us)
             (@OptionType.some KExpr (kconst_inst_type sig us))
             (@OptionType.some KExpr A)
             (kdecl_type_at_intro tenv2 n sig us (ext n sig hlk) harity)
             (@Eq.cong KExpr (OptionType KExpr)
               (fun (T0 : KExpr) => @OptionType.some KExpr T0)
               (kconst_inst_type sig us) A
               (@Eq.symm KExpr A (kconst_inst_type sig us) hres)))))
   (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
     (_typed : TypingCtxConv tenv G0 e0 A) (equivalent : DefEq A B)
     (ih : TypingCtxConv tenv2 G0 e0 A) =>
     @TypingCtxConv.conv tenv2 G0 e0 A B ih equivalent)
   (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hty : TypingCtxConv tenv G0 ty (KExpr.sort u))
     (_hv : TypingCtxConv tenv G0 v ty)
     (_hb : TypingCtxConv tenv (@ListType.cons KExpr ty G0) b B)
     (ihty : TypingCtxConv tenv2 G0 ty (KExpr.sort u))
     (ihv : TypingCtxConv tenv2 G0 v ty)
     (ihb : TypingCtxConv tenv2 (@ListType.cons KExpr ty G0) b B) =>
     @TypingCtxConv.let_ tenv2 G0 ty v b B u ihty ihv ihb)
   (fun (G0 : ListType KExpr) (n : Nat) =>
     @TypingCtxConv.lit_nat tenv2 G0 n)
   (fun (G0 : ListType KExpr) (n : Nat) =>
     @TypingCtxConv.lit_string tenv2 G0 n)
   G e T typed",
            "typingctxconv_tenv_mono: DECLARATION-ENVIRONMENT MONOTONICITY of the ten-constructor              TypingCtxConv judgment. A derivation in tenv survives into any tenv2 that preserves              tenv's ENTRIES — signature and all, not merely their definedness. Nine rules              re-assemble their induction hypotheses unchanged and DefEq carries no environment, so              conv transports untouched; the entire content is the const arm, const's lookup              equation being the only premise in the judgment that reads tenv. It is discharged by              kdecl_type_at_some_inv (exposing the stored signature, its lookup equation, the              checked arity and the returned type), re-derived at tenv2 by kdecl_type_at_intro, and              re-aligned with the original A. No Eq.substType transport anywhere: G, e and T are              untouched, which makes this strictly simpler than typingctx_instL.                           WHY THE PREMISE IS SIGNATURE-PRESERVING AND NOT MERELY DEFINEDNESS-PRESERVING:              kdecl_type_at reads env at the single point n and then GUARDS on the stored              signature's parameter count against us, so an extension free to rebind n changes the              returned type and one free to change the parameter list's LENGTH sends the lookup to              none. The hypothesis is forced, not conservative.                           WHAT IT DOES NOT GIVE, measured: it does NOT compose with              kernel_add_decl_extends_env to yield 'add_decl preserves every earlier derivation'.              That lemma is over KEnv, the structural empty/addConst/addInductive environment of              the Phase-4 definitional-extension lane; TypingCtxConv's environment is KDeclEnv, the              FUNCTION Name -> OptionType KConstSig. Two unrelated types with no bridge in this              tree.                           NO CONSUMER TODAY: TypingCtx's consumers all hold tenv fixed. Registered over              TypingCtxConv rather than the conv-free TypingCtx because TypingCtxConv is what the              Layer-1 / ImplInfer soundness lane targets, which is where a consumer would arrive.              DerivedProved, zero axiom_deps, census-neutral.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::instantiation_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn conditional_conversion_instantiation_has_checked_values_and_empty_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "defeq_instL",
            "instL_literal_nat",
            "instL_literal_nat_type",
            "instL_literal_string",
            "instL_literal_string_type",
            "typingctxconv_instL",
            "typingctxconv_instLevels",
            "typingctxconv_kdef_instantiated",
            "typingctxconv_tenv_mono",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered conditional instantiation theorem");
            assert!(!definition.is_axiom);
            assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
            assert!(definition.elaborated_value.is_some());
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have empty actual axiom closure"
            );
        }
    }

    #[test]
    fn operational_closure_cannot_be_fabricated_by_returning_the_old_step() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for (name, relation) in [
                ("fake_delta_instL_closure_must_fail", "delta_reduces"),
                ("fake_iota_instL_closure_must_fail", "iota_reduces"),
            ] {
                assert!(instantiation_theorem(
                    &mut spec,
                    name,
                    &format!("forall (s : Name -> Level) (e : KExpr) (e2 : KExpr), {relation} e e2 -> {relation} (instL s e) (instL s e2)"),
                    &format!("fun (s : Name -> Level) (e : KExpr) (e2 : KExpr) (h : {relation} e e2) => h"),
                    "Negative control: an unsubstituted operational step is not a proof of the substituted step. The closure premise must be genuinely derived.",
                ).is_err(), "{relation} closure cannot be fabricated");
            }
            assert!(instantiation_theorem(
                &mut spec,
                "fake_defeq_instL_preservation_must_fail",
                "forall (s : Name -> Level) (e : KExpr) (e2 : KExpr), DefEq e e2 -> DefEq (instL s e) (instL s e2)",
                "fun (s : Name -> Level) (e : KExpr) (e2 : KExpr) (h : DefEq e e2) => h",
                "Negative control: conversion preservation is not established by simply reusing an unchanged derivation.",
            ).is_err());

            // THE HYPOTHESIS OF `typingctxconv_tenv_mono` IS LOAD-BEARING.
            //
            // Nine of that theorem's ten arms really do re-assemble their
            // induction hypotheses unchanged, which makes it tempting to read
            // the whole thing as a retyping that any environment would admit.
            // It is not: the `const` arm needs the extension premise, and
            // without it there is nothing to build `ext n sig hlk` from. This
            // probe claims the conclusion with the premise DELETED and proves
            // it by handing back the derivation untouched; the kernel must
            // refuse, because the hypothesis sits at `tenv` and the goal at
            // `tenv2`. If it ever passed, the theorem would be measuring
            // nothing about declaration environments at all.
            assert!(
                instantiation_theorem(
                    &mut spec,
                    "typingctxconv_tenv_mono_no_hyp_probe",
                    "forall (tenv : KDeclEnv) (tenv2 : KDeclEnv) (G : ListType KExpr) \
                     (e : KExpr) (T : KExpr), TypingCtxConv tenv G e T -> TypingCtxConv tenv2 G e T",
                    "fun (tenv : KDeclEnv) (tenv2 : KDeclEnv) (G : ListType KExpr) \
                     (e : KExpr) (T : KExpr) (h : TypingCtxConv tenv G e T) => h",
                    "Negative control: a derivation is not transported to another declaration \
                     environment by handing it back unchanged. The entry-preserving premise is \
                     what the const arm consumes.",
                )
                .is_err(),
                "environment monotonicity went through with NO hypothesis on tenv2 — the \
                 theorem's premise is not load-bearing and the const arm is not reading tenv"
            );
        });
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Supplied-payload admission and chronological request traces for KEnv.
//!
//! Fresh constants/families carry the existing extension evidence. Reuse must
//! select the exact historical payload by computed position; EnvSound recovers
//! both its admission and the validity of its original insertion environment.
//! A reuse consumes one request even though it erases to an empty old chain.
//! This is the existing numeric, single-family model fragment, not Rust named
//! tables, parameter promotion, nested restoration, or an execution refinement.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

enum DeclarationInput {
    Inductive(&'static str),
    Data(&'static str, &'static str, &'static str),
    Proof(&'static str, &'static str, &'static str),
}

const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive KernelDeclInput : Type
| const_ : ConstExtensionKind -> Nat -> KExpr -> KExpr -> KernelDeclInput
| inductive_ : Nat -> Nat -> KExpr -> CtorDecls -> KernelDeclInput",
    ),
    DeclarationInput::Data(
        "dia_admission_at",
        r"forall (prior : KEnv) (input : KernelDeclInput), Type",
        r"fun (prior : KEnv) (input : KernelDeclInput) =>
 KernelDeclInput.rec (fun (_ : KernelDeclInput) => Type)
  (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr) =>
   ConstantExtension prior (KEnv.addConst prior kind id ty value))
  (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls) =>
   InductiveExtension prior (KEnv.addInductive prior id np ty ctors)) input",
    ),
    DeclarationInput::Inductive(
        r"inductive KernelDeclInputAdmission (input : KernelDeclInput) : Type
| mk : forall (prior : KEnv), EnvSound prior -> dia_admission_at prior input -> KernelDeclInputAdmission input",
    ),
    DeclarationInput::Inductive(
        r"inductive KernelDeclInputAccepts (env : KEnv) : KernelDeclInput -> KEnv -> Type
| const_fresh : forall (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr),
 ConstantExtension env (KEnv.addConst env kind id ty value) ->
 KernelDeclInputAccepts env (KernelDeclInput.const_ kind id ty value) (KEnv.addConst env kind id ty value)
| inductive_fresh : forall (id np : Nat) (ty : KExpr) (ctors : CtorDecls),
 InductiveExtension env (KEnv.addInductive env id np ty ctors) ->
 KernelDeclInputAccepts env (KernelDeclInput.inductive_ id np ty ctors) (KEnv.addInductive env id np ty ctors)
| const_reuse : forall (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr),
 Eq (OptionType KEnv) (sfa_entry_at env depth) (OptionType.some KEnv (KEnv.addConst prior kind id ty value)) ->
 KernelDeclInputAccepts env (KernelDeclInput.const_ kind id ty value) env
| inductive_reuse : forall (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls),
 Eq (OptionType KEnv) (sfa_entry_at env depth) (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors)) ->
 KernelDeclInputAccepts env (KernelDeclInput.inductive_ id np ty ctors) env",
    ),
    DeclarationInput::Inductive(
        r"inductive KernelDeclInputChain : KEnv -> ListType KernelDeclInput -> KEnv -> Type
| nil : forall (env : KEnv), KernelDeclInputChain env (ListType.nil KernelDeclInput) env
| cons : forall (env mid out : KEnv) (input : KernelDeclInput) (rest : ListType KernelDeclInput),
 KernelDeclInputAccepts env input mid -> KernelDeclInputChain mid rest out ->
 KernelDeclInputChain env (ListType.cons KernelDeclInput input rest) out",
    ),
    DeclarationInput::Data(
        "dia_requests_admitted",
        r"forall (inputs : ListType KernelDeclInput), Type",
        r"fun (inputs : ListType KernelDeclInput) =>
 ListType.rec KernelDeclInput (fun (_ : ListType KernelDeclInput) => Type) Nat
  (fun (input : KernelDeclInput) (_rest : ListType KernelDeclInput) (tail : Type) =>
   ProdType (KernelDeclInputAdmission input) tail) inputs",
    ),
    DeclarationInput::Proof(
        "dia_entries_sound",
        r"forall (env : KEnv), sfa_entries env -> EnvSound env",
        r"fun (env : KEnv) => KEnv.rec
 (fun (e : KEnv) => sfa_entries e -> EnvSound e)
 (fun (_entries : Nat) => DefinitionalExtension.refl KEnv.empty)
 (fun (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
  (ih : sfa_entries prior -> EnvSound prior)
  (entries : sfa_entries (KEnv.addConst prior kind id ty value)) =>
  constant_extension_preserves_soundness prior (KEnv.addConst prior kind id ty value)
   (ProdType.snd (sfa_entries prior) (ConstantExtension prior (KEnv.addConst prior kind id ty value)) entries)
   (ih (ProdType.fst (sfa_entries prior) (ConstantExtension prior (KEnv.addConst prior kind id ty value)) entries)))
 (fun (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
  (ih : sfa_entries prior -> EnvSound prior)
  (entries : sfa_entries (KEnv.addInductive prior id np ty ctors)) =>
  inductive_extension_preserves_soundness prior (KEnv.addInductive prior id np ty ctors)
   (ProdType.snd (sfa_entries prior) (InductiveExtension prior (KEnv.addInductive prior id np ty ctors)) entries)
   (ih (ProdType.fst (sfa_entries prior) (InductiveExtension prior (KEnv.addInductive prior id np ty ctors)) entries))) env",
    ),
    DeclarationInput::Proof(
        "dia_stored_constant_admission",
        r"forall (env : KEnv) (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind)
 (id : Nat) (ty value : KExpr), EnvSound env ->
 Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addConst prior kind id ty value)) ->
 ConstantExtension prior (KEnv.addConst prior kind id ty value)",
        r"fun (env : KEnv) (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind)
 (id : Nat) (ty value : KExpr) (sound : EnvSound env)
 (found : Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addConst prior kind id ty value))) =>
 ProdType.snd (sfa_entries prior) (ConstantExtension prior (KEnv.addConst prior kind id ty value))
  (sfa_entries_at env depth (KEnv.addConst prior kind id ty value) (sfa_sound_entries env sound) found)",
    ),
    DeclarationInput::Proof(
        "dia_stored_constant_prior_sound",
        r"forall (env : KEnv) (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind)
 (id : Nat) (ty value : KExpr), EnvSound env ->
 Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addConst prior kind id ty value)) -> EnvSound prior",
        r"fun (env : KEnv) (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind)
 (id : Nat) (ty value : KExpr) (sound : EnvSound env)
 (found : Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addConst prior kind id ty value))) =>
 dia_entries_sound prior
  (ProdType.fst (sfa_entries prior) (ConstantExtension prior (KEnv.addConst prior kind id ty value))
   (sfa_entries_at env depth (KEnv.addConst prior kind id ty value) (sfa_sound_entries env sound) found))",
    ),
    DeclarationInput::Proof(
        "dia_stored_family_prior_sound",
        r"forall (env : KEnv) (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls),
 EnvSound env -> Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors)) -> EnvSound prior",
        r"fun (env : KEnv) (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (sound : EnvSound env) (found : Eq (OptionType KEnv) (sfa_entry_at env depth)
  (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors))) =>
 dia_entries_sound prior
  (ProdType.fst (sfa_entries prior) (InductiveExtension prior (KEnv.addInductive prior id np ty ctors))
   (sfa_entries_at env depth (KEnv.addInductive prior id np ty ctors) (sfa_sound_entries env sound) found))",
    ),
    DeclarationInput::Proof(
        "dia_input_admitted",
        r"forall (env : KEnv) (input : KernelDeclInput) (out : KEnv),
 KernelDeclInputAccepts env input out -> EnvSound env -> KernelDeclInputAdmission input",
        r"fun (env : KEnv) (input : KernelDeclInput) (out : KEnv)
 (accepted : KernelDeclInputAccepts env input out) =>
 KernelDeclInputAccepts.rec env
  (fun (d : KernelDeclInput) (dst : KEnv) (_h : KernelDeclInputAccepts env d dst) =>
   EnvSound env -> KernelDeclInputAdmission d)
  (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (ext : ConstantExtension env (KEnv.addConst env kind id ty value)) (sound : EnvSound env) =>
   KernelDeclInputAdmission.mk (KernelDeclInput.const_ kind id ty value) env sound ext)
  (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (ext : InductiveExtension env (KEnv.addInductive env id np ty ctors)) (sound : EnvSound env) =>
   KernelDeclInputAdmission.mk (KernelDeclInput.inductive_ id np ty ctors) env sound ext)
  (fun (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addConst prior kind id ty value))) (sound : EnvSound env) =>
   KernelDeclInputAdmission.mk (KernelDeclInput.const_ kind id ty value) prior
    (dia_stored_constant_prior_sound env depth prior kind id ty value sound found)
    (dia_stored_constant_admission env depth prior kind id ty value sound found))
  (fun (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors))) (sound : EnvSound env) =>
   KernelDeclInputAdmission.mk (KernelDeclInput.inductive_ id np ty ctors) prior
    (dia_stored_family_prior_sound env depth prior id np ty ctors sound found)
    (sfa_stored_family_admission env depth prior id np ty ctors sound found)) input out accepted",
    ),
    DeclarationInput::Proof(
        "dia_input_to_old_chain",
        r"forall (env : KEnv) (input : KernelDeclInput) (out : KEnv),
 KernelDeclInputAccepts env input out -> KernelAddDeclChain env out",
        r"fun (env : KEnv) (input : KernelDeclInput) (out : KEnv)
 (accepted : KernelDeclInputAccepts env input out) =>
 KernelDeclInputAccepts.rec env
  (fun (d : KernelDeclInput) (dst : KEnv) (_h : KernelDeclInputAccepts env d dst) => KernelAddDeclChain env dst)
  (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (ext : ConstantExtension env (KEnv.addConst env kind id ty value)) =>
   KernelAddDeclChain.step env env (KEnv.addConst env kind id ty value) (KernelAddDeclChain.refl env)
    (KernelAddDeclAccepts.const_case env (KEnv.addConst env kind id ty value) ext))
  (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (ext : InductiveExtension env (KEnv.addInductive env id np ty ctors)) =>
   KernelAddDeclChain.step env env (KEnv.addInductive env id np ty ctors) (KernelAddDeclChain.refl env)
    (KernelAddDeclAccepts.inductive_case env (KEnv.addInductive env id np ty ctors) ext))
  (fun (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (_found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addConst prior kind id ty value))) => KernelAddDeclChain.refl env)
  (fun (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (_found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors))) => KernelAddDeclChain.refl env)
  input out accepted",
    ),
    DeclarationInput::Proof(
        "dia_old_chain_trans",
        r"forall (env mid out : KEnv), KernelAddDeclChain env mid -> KernelAddDeclChain mid out -> KernelAddDeclChain env out",
        r"fun (env mid out : KEnv) (left : KernelAddDeclChain env mid) (right : KernelAddDeclChain mid out) =>
 KernelAddDeclChain.rec mid
  (fun (dst : KEnv) (_h : KernelAddDeclChain mid dst) => KernelAddDeclChain env dst)
  left
  (fun (prior dst : KEnv) (_prefix : KernelAddDeclChain mid prior) (step : KernelAddDeclAccepts prior dst)
   (ih : KernelAddDeclChain env prior) => KernelAddDeclChain.step env prior dst ih step) out right",
    ),
    DeclarationInput::Proof(
        "dia_chain_to_old_chain",
        r"forall (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv),
 KernelDeclInputChain env inputs out -> KernelAddDeclChain env out",
        r"fun (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv)
 (chain : KernelDeclInputChain env inputs out) => KernelDeclInputChain.rec
  (fun (src : KEnv) (ds : ListType KernelDeclInput) (dst : KEnv) (_h : KernelDeclInputChain src ds dst) =>
   KernelAddDeclChain src dst)
  (fun (src : KEnv) => KernelAddDeclChain.refl src)
  (fun (src mid dst : KEnv) (d : KernelDeclInput) (ds : ListType KernelDeclInput)
   (step : KernelDeclInputAccepts src d mid) (_tail : KernelDeclInputChain mid ds dst)
   (ih : KernelAddDeclChain mid dst) => dia_old_chain_trans src mid dst (dia_input_to_old_chain src d mid step) ih)
  env inputs out chain",
    ),
    DeclarationInput::Proof(
        "dia_input_preserves_sound",
        r"forall (env : KEnv) (input : KernelDeclInput) (out : KEnv),
 KernelDeclInputAccepts env input out -> EnvSound env -> EnvSound out",
        r"fun (env : KEnv) (input : KernelDeclInput) (out : KEnv)
 (accepted : KernelDeclInputAccepts env input out) => KernelDeclInputAccepts.rec env
  (fun (d : KernelDeclInput) (dst : KEnv) (_h : KernelDeclInputAccepts env d dst) => EnvSound env -> EnvSound dst)
  (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (ext : ConstantExtension env (KEnv.addConst env kind id ty value)) =>
   constant_extension_preserves_soundness env (KEnv.addConst env kind id ty value) ext)
  (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (ext : InductiveExtension env (KEnv.addInductive env id np ty ctors)) =>
   inductive_extension_preserves_soundness env (KEnv.addInductive env id np ty ctors) ext)
  (fun (depth : Nat) (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
   (_found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addConst prior kind id ty value))) (sound : EnvSound env) => sound)
  (fun (depth : Nat) (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (_found : Eq (OptionType KEnv) (sfa_entry_at env depth)
    (OptionType.some KEnv (KEnv.addInductive prior id np ty ctors))) (sound : EnvSound env) => sound)
  input out accepted",
    ),
    DeclarationInput::Proof(
        "dia_chain_admitted",
        r"forall (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv),
 KernelDeclInputChain env inputs out -> EnvSound env -> ProdType (EnvSound out) (dia_requests_admitted inputs)",
        r"fun (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv)
 (chain : KernelDeclInputChain env inputs out) => KernelDeclInputChain.rec
  (fun (src : KEnv) (ds : ListType KernelDeclInput) (dst : KEnv) (_h : KernelDeclInputChain src ds dst) =>
   EnvSound src -> ProdType (EnvSound dst) (dia_requests_admitted ds))
  (fun (src : KEnv) (sound : EnvSound src) => ProdType.mk (EnvSound src) Nat sound Nat.zero)
  (fun (src mid dst : KEnv) (d : KernelDeclInput) (ds : ListType KernelDeclInput)
   (step : KernelDeclInputAccepts src d mid) (_tail : KernelDeclInputChain mid ds dst)
   (ih : EnvSound mid -> ProdType (EnvSound dst) (dia_requests_admitted ds)) (sound : EnvSound src) =>
   (fun (tail_result : ProdType (EnvSound dst) (dia_requests_admitted ds)) =>
    ProdType.mk (EnvSound dst) (dia_requests_admitted (ListType.cons KernelDeclInput d ds))
     (ProdType.fst (EnvSound dst) (dia_requests_admitted ds) tail_result)
     (ProdType.mk (KernelDeclInputAdmission d) (dia_requests_admitted ds)
      (dia_input_admitted src d mid step sound)
      (ProdType.snd (EnvSound dst) (dia_requests_admitted ds) tail_result)))
    (ih (dia_input_preserves_sound src d mid step sound))) env inputs out chain",
    ),
    DeclarationInput::Proof(
        "dia_chain_sound",
        r"forall (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv) (ctx : KernelLocalCtx),
 KernelDeclInputChain env inputs out -> KernelStateMatchesSpec (KernelState.mk env ctx) -> EnvSound env ->
 ProdType (KernelStateMatchesSpec (KernelState.mk out ctx))
  (ProdType (EnvSound out) (dia_requests_admitted inputs))",
        r"fun (env : KEnv) (inputs : ListType KernelDeclInput) (out : KEnv) (ctx : KernelLocalCtx)
 (chain : KernelDeclInputChain env inputs out) (state_matches : KernelStateMatchesSpec (KernelState.mk env ctx))
 (sound : EnvSound env) =>
 ProdType.mk (KernelStateMatchesSpec (KernelState.mk out ctx))
  (ProdType (EnvSound out) (dia_requests_admitted inputs))
  (KernelAddDeclChainPreservesState env out ctx (dia_chain_to_old_chain env inputs out chain) state_matches sound)
  (dia_chain_admitted env inputs out chain sound)",
    ),
    DeclarationInput::Data(
        "dia_family_request",
        "KernelDeclInput",
        r"KernelDeclInput.inductive_ Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)",
    ),
    DeclarationInput::Data(
        "dia_constant_request",
        "KernelDeclInput",
        r"KernelDeclInput.const_ ConstExtensionKind.reducible_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)",
    ),
    DeclarationInput::Data(
        "dia_mixed_requests",
        "ListType KernelDeclInput",
        r"ListType.cons KernelDeclInput dia_family_request
 (ListType.cons KernelDeclInput dia_constant_request
  (ListType.cons KernelDeclInput dia_family_request
   (ListType.cons KernelDeclInput dia_constant_request (ListType.nil KernelDeclInput))))",
    ),
    DeclarationInput::Proof(
        "dia_fresh_family",
        r"KernelDeclInputAccepts KEnv.empty dia_family_request env_freshness_first",
        r"KernelDeclInputAccepts.inductive_fresh KEnv.empty Nat.zero Nat.zero env_freshness_type
 (env_freshness_ctors env_freshness_one) env_freshness_first_extension",
    ),
    DeclarationInput::Proof(
        "dia_fresh_constant",
        r"KernelDeclInputAccepts env_freshness_first dia_constant_request env_freshness_const_result",
        r"KernelDeclInputAccepts.const_fresh env_freshness_first ConstExtensionKind.reducible_
 env_freshness_two env_freshness_type (KExpr.sort Level.zero) env_freshness_const_extension",
    ),
    DeclarationInput::Proof(
        "dia_reuse_family",
        r"KernelDeclInputAccepts env_freshness_const_result dia_family_request env_freshness_const_result",
        r"KernelDeclInputAccepts.inductive_reuse env_freshness_const_result env_freshness_one KEnv.empty
 Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)
 (Eq.refl (OptionType KEnv) (OptionType.some KEnv env_freshness_first))",
    ),
    DeclarationInput::Proof(
        "dia_reuse_constant",
        r"KernelDeclInputAccepts env_freshness_const_result dia_constant_request env_freshness_const_result",
        r"KernelDeclInputAccepts.const_reuse env_freshness_const_result Nat.zero env_freshness_first
 ConstExtensionKind.reducible_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)
 (Eq.refl (OptionType KEnv) (OptionType.some KEnv env_freshness_const_result))",
    ),
    DeclarationInput::Proof(
        "dia_mixed_chain",
        r"KernelDeclInputChain KEnv.empty dia_mixed_requests env_freshness_const_result",
        r"KernelDeclInputChain.cons KEnv.empty env_freshness_first env_freshness_const_result dia_family_request
 (ListType.cons KernelDeclInput dia_constant_request
  (ListType.cons KernelDeclInput dia_family_request
   (ListType.cons KernelDeclInput dia_constant_request (ListType.nil KernelDeclInput)))) dia_fresh_family
 (KernelDeclInputChain.cons env_freshness_first env_freshness_const_result env_freshness_const_result dia_constant_request
  (ListType.cons KernelDeclInput dia_family_request
   (ListType.cons KernelDeclInput dia_constant_request (ListType.nil KernelDeclInput))) dia_fresh_constant
  (KernelDeclInputChain.cons env_freshness_const_result env_freshness_const_result env_freshness_const_result dia_family_request
   (ListType.cons KernelDeclInput dia_constant_request (ListType.nil KernelDeclInput)) dia_reuse_family
   (KernelDeclInputChain.cons env_freshness_const_result env_freshness_const_result env_freshness_const_result dia_constant_request
    (ListType.nil KernelDeclInput) dia_reuse_constant (KernelDeclInputChain.nil env_freshness_const_result))))",
    ),
    DeclarationInput::Proof(
        "dia_mixed_admissions",
        r"dia_requests_admitted dia_mixed_requests",
        r"ProdType.snd (EnvSound env_freshness_const_result) (dia_requests_admitted dia_mixed_requests)
 (dia_chain_admitted KEnv.empty dia_mixed_requests env_freshness_const_result dia_mixed_chain
  (DefinitionalExtension.refl KEnv.empty))",
    ),
    DeclarationInput::Proof(
        "dia_mixed_preservation",
        r"ProdType (KernelStateMatchesSpec (KernelState.mk env_freshness_const_result KernelLocalCtx.nil))
 (ProdType (EnvSound env_freshness_const_result) (dia_requests_admitted dia_mixed_requests))",
        r"dia_chain_sound KEnv.empty dia_mixed_requests env_freshness_const_result KernelLocalCtx.nil
 dia_mixed_chain KernelInitialStateValid (DefinitionalExtension.refl KEnv.empty)",
    ),
    DeclarationInput::Proof(
        "dia_reused_family_admitted",
        r"KernelDeclInputAdmission dia_family_request",
        r"dia_input_admitted env_freshness_const_result dia_family_request env_freshness_const_result
 dia_reuse_family env_freshness_const_preserves_sound",
    ),
    DeclarationInput::Proof(
        "dia_reused_constant_admitted",
        r"KernelDeclInputAdmission dia_constant_request",
        r"dia_input_admitted env_freshness_const_result dia_constant_request env_freshness_const_result
 dia_reuse_constant env_freshness_const_preserves_sound",
    ),
];

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    DECLARATIONS.iter()
}

impl Specification {
    /// Full only, after stored-family history recovery and extension preservation.
    pub(super) fn add_declaration_input_admission(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Exact supplied numeric declaration payload, admission witness or ordered request relation; not a Rust execution judgment.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent exact-payload admission family, request fold or concrete model-history request.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Supplied-payload model admission and preservation; reuse recovers a valid historical extension rather than assuming the requested result.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod controls;
#[cfg(test)]
use controls::{
    DATA_NAMES, INDUCTIVE_NAMES, NEGATIVE_CONTROLS, PROOF_ROOTS, PROP_PROOF_ROOTS, TYPE_PROOF_ROOTS,
};

#[cfg(test)]
mod tests;

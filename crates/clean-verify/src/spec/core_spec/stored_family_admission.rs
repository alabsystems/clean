// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission-witness recovery from computed model-history membership.
//! These statements use the existing fresh-extension KEnv fragment. They do not
//! validate Rust re-registration, identify named metadata with model history, or
//! establish parameter-promotion, nested-restoration, or execution refinement.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

enum DeclarationInput {
    Data(&'static str, &'static str, &'static str),
    Proof(&'static str, &'static str, &'static str),
}

const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "sfa_entry_at",
        r"forall (env : KEnv) (depth : Nat), OptionType KEnv",
        r"fun (env : KEnv) (depth : Nat) =>
 @KEnv.rec (fun (_ : KEnv) => Nat -> OptionType KEnv)
  (fun (_depth : Nat) => @OptionType.none KEnv)
  (fun (prior : KEnv) (kind : ConstExtensionKind) (id : Nat)
   (ty value : KExpr) (ih : Nat -> OptionType KEnv) (d : Nat) =>
   @Nat.rec (fun (_ : Nat) => OptionType KEnv)
    (@OptionType.some KEnv (KEnv.addConst prior kind id ty value))
    (fun (n : Nat) (_prev : OptionType KEnv) => ih n) d)
  (fun (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (ih : Nat -> OptionType KEnv) (d : Nat) =>
   @Nat.rec (fun (_ : Nat) => OptionType KEnv)
    (@OptionType.some KEnv (KEnv.addInductive prior id np ty ctors))
    (fun (n : Nat) (_prev : OptionType KEnv) => ih n) d)
  env depth",
    ),
    DeclarationInput::Data(
        "sfa_entries",
        r"forall (env : KEnv), Type",
        r"fun (env : KEnv) =>
 @KEnv.rec (fun (_ : KEnv) => Type) Nat
  (fun (prior : KEnv) (kind : ConstExtensionKind) (id : Nat)
   (ty value : KExpr) (prior_entries : Type) =>
   ProdType prior_entries
    (ConstantExtension prior (KEnv.addConst prior kind id ty value)))
  (fun (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
   (prior_entries : Type) =>
   ProdType prior_entries
    (InductiveExtension prior (KEnv.addInductive prior id np ty ctors))) env",
    ),
    DeclarationInput::Proof(
        "sfa_const_entries",
        r"forall (env out : KEnv), ConstantExtension env out -> sfa_entries env -> sfa_entries out",
        r"fun (env out : KEnv) (ext : ConstantExtension env out) =>
 @ConstantExtension.rec env
  (fun (dst : KEnv) (_h : ConstantExtension env dst) => sfa_entries env -> sfa_entries dst)
  (fun (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr) (u : Level)
   (fresh : FreshDeclName env id) (ht : Typing ty (KExpr.sort u)) (hv : Typing value ty)
   (entries : sfa_entries env) =>
   @ProdType.mk (sfa_entries env) (ConstantExtension env (KEnv.addConst env kind id ty value))
    entries (@ConstantExtension.mk env kind id ty value u fresh ht hv)) out ext",
    ),
    DeclarationInput::Proof(
        "sfa_inductive_entries",
        r"forall (env out : KEnv), InductiveExtension env out -> sfa_entries env -> sfa_entries out",
        r"fun (env out : KEnv) (ext : InductiveExtension env out) =>
 @InductiveExtension.rec env
  (fun (dst : KEnv) (_h : InductiveExtension env dst) => sfa_entries env -> sfa_entries dst)
  (fun (id np : Nat) (ty : KExpr) (ctors : CtorDecls) (u : Level)
   (fresh : FreshDeclName env id) (ht : Typing ty (KExpr.sort u))
   (positive : StrictlyPositiveCtorDecls ty ctors) (wf : WellFormedCtorDecls env id np ty ctors)
   (entries : sfa_entries env) =>
   @ProdType.mk (sfa_entries env) (InductiveExtension env (KEnv.addInductive env id np ty ctors))
    entries (@InductiveExtension.mk env id np ty ctors u fresh ht positive wf)) out ext",
    ),
    DeclarationInput::Proof(
        "sfa_extension_entries",
        r"forall (env out : KEnv), DefinitionalExtension env out -> sfa_entries env -> sfa_entries out",
        r"fun (env out : KEnv) (ext : DefinitionalExtension env out) =>
 @DefinitionalExtension.rec
  (fun (src dst : KEnv) (_h : DefinitionalExtension src dst) => sfa_entries src -> sfa_entries dst)
  (fun (src : KEnv) (entries : sfa_entries src) => entries)
  (fun (src dst : KEnv) (h : ConstantExtension src dst) => sfa_const_entries src dst h)
  (fun (src dst : KEnv) (h : InductiveExtension src dst) => sfa_inductive_entries src dst h)
  (fun (src mid dst : KEnv) (_a : DefinitionalExtension src mid) (_b : DefinitionalExtension mid dst)
   (iha : sfa_entries src -> sfa_entries mid) (ihb : sfa_entries mid -> sfa_entries dst)
   (entries : sfa_entries src) => ihb (iha entries)) env out ext",
    ),
    DeclarationInput::Proof(
        "sfa_sound_entries",
        r"forall (env : KEnv), EnvSound env -> sfa_entries env",
        r"fun (env : KEnv) (sound : EnvSound env) => sfa_extension_entries KEnv.empty env sound Nat.zero",
    ),
    DeclarationInput::Proof(
        "sfa_entries_at",
        r"forall (env : KEnv) (depth : Nat) (out : KEnv), sfa_entries env ->
 @Eq (OptionType KEnv) (sfa_entry_at env depth) (@OptionType.some KEnv out) -> sfa_entries out",
        r"fun (env : KEnv) => @KEnv.rec
 (fun (e : KEnv) => forall (depth : Nat) (out : KEnv), sfa_entries e ->
  @Eq (OptionType KEnv) (sfa_entry_at e depth) (@OptionType.some KEnv out) -> sfa_entries out)
 (fun (depth : Nat) (out : KEnv) (_entries : sfa_entries KEnv.empty)
  (found : @Eq (OptionType KEnv) (sfa_entry_at KEnv.empty depth) (@OptionType.some KEnv out)) =>
  opt_none_ne_some_t KEnv out (sfa_entries out) found)
 (fun (prior : KEnv) (kind : ConstExtensionKind) (id : Nat) (ty value : KExpr)
  (ih : forall (depth : Nat) (out : KEnv), sfa_entries prior ->
   @Eq (OptionType KEnv) (sfa_entry_at prior depth) (@OptionType.some KEnv out) -> sfa_entries out)
  (depth : Nat) => @Nat.rec
   (fun (d : Nat) => forall (out : KEnv), sfa_entries (KEnv.addConst prior kind id ty value) ->
    @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addConst prior kind id ty value) d) (@OptionType.some KEnv out) -> sfa_entries out)
   (fun (out : KEnv) (entries : sfa_entries (KEnv.addConst prior kind id ty value))
    (found : @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addConst prior kind id ty value) Nat.zero) (@OptionType.some KEnv out)) =>
    Eq.substType KEnv (fun (e : KEnv) => sfa_entries e) (KEnv.addConst prior kind id ty value) out
     (option_some_inj KEnv (KEnv.addConst prior kind id ty value) out found) entries)
   (fun (d : Nat) (_prev : forall (out : KEnv), sfa_entries (KEnv.addConst prior kind id ty value) ->
     @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addConst prior kind id ty value) d) (@OptionType.some KEnv out) -> sfa_entries out)
    (out : KEnv) (entries : sfa_entries (KEnv.addConst prior kind id ty value))
    (found : @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addConst prior kind id ty value) (Nat.succ d)) (@OptionType.some KEnv out)) =>
    ih d out (ProdType.fst (sfa_entries prior) (ConstantExtension prior (KEnv.addConst prior kind id ty value)) entries) found) depth)
 (fun (prior : KEnv) (id np : Nat) (ty : KExpr) (ctors : CtorDecls)
  (ih : forall (depth : Nat) (out : KEnv), sfa_entries prior ->
   @Eq (OptionType KEnv) (sfa_entry_at prior depth) (@OptionType.some KEnv out) -> sfa_entries out)
  (depth : Nat) => @Nat.rec
   (fun (d : Nat) => forall (out : KEnv), sfa_entries (KEnv.addInductive prior id np ty ctors) ->
    @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addInductive prior id np ty ctors) d) (@OptionType.some KEnv out) -> sfa_entries out)
   (fun (out : KEnv) (entries : sfa_entries (KEnv.addInductive prior id np ty ctors))
    (found : @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addInductive prior id np ty ctors) Nat.zero) (@OptionType.some KEnv out)) =>
    Eq.substType KEnv (fun (e : KEnv) => sfa_entries e) (KEnv.addInductive prior id np ty ctors) out
     (option_some_inj KEnv (KEnv.addInductive prior id np ty ctors) out found) entries)
   (fun (d : Nat) (_prev : forall (out : KEnv), sfa_entries (KEnv.addInductive prior id np ty ctors) ->
     @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addInductive prior id np ty ctors) d) (@OptionType.some KEnv out) -> sfa_entries out)
    (out : KEnv) (entries : sfa_entries (KEnv.addInductive prior id np ty ctors))
    (found : @Eq (OptionType KEnv) (sfa_entry_at (KEnv.addInductive prior id np ty ctors) (Nat.succ d)) (@OptionType.some KEnv out)) =>
    ih d out (ProdType.fst (sfa_entries prior) (InductiveExtension prior (KEnv.addInductive prior id np ty ctors)) entries) found) depth) env",
    ),
    DeclarationInput::Proof(
        "sfa_stored_family_admission",
        r"forall (env : KEnv) (depth : Nat) (prior : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls),
 EnvSound env -> @Eq (OptionType KEnv) (sfa_entry_at env depth)
  (@OptionType.some KEnv (KEnv.addInductive prior family np ty ctors)) ->
 InductiveExtension prior (KEnv.addInductive prior family np ty ctors)",
        r"fun (env : KEnv) (depth : Nat) (prior : KEnv) (family np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (sound : EnvSound env) (found : @Eq (OptionType KEnv) (sfa_entry_at env depth)
  (@OptionType.some KEnv (KEnv.addInductive prior family np ty ctors))) =>
 ProdType.snd (sfa_entries prior) (InductiveExtension prior (KEnv.addInductive prior family np ty ctors))
  (sfa_entries_at env depth (KEnv.addInductive prior family np ty ctors) (sfa_sound_entries env sound) found)",
    ),
    DeclarationInput::Proof(
        "sfa_prior_family_caller",
        r"InductiveExtension KEnv.empty env_freshness_first",
        r"sfa_stored_family_admission env_freshness_second env_freshness_one KEnv.empty Nat.zero Nat.zero
 env_freshness_type (env_freshness_ctors env_freshness_one) env_freshness_acceptance_preserves_sound
 (@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first))",
    ),
    DeclarationInput::Proof(
        "sfa_constant_tail_caller",
        r"InductiveExtension KEnv.empty env_freshness_first",
        r"sfa_stored_family_admission env_freshness_const_result env_freshness_one KEnv.empty Nat.zero Nat.zero
 env_freshness_type (env_freshness_ctors env_freshness_one) env_freshness_const_preserves_sound
 (@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first))",
    ),
];

fn declarations() -> impl Iterator<Item = &'static DeclarationInput> {
    DECLARATIONS.iter()
}

impl Specification {
    /// Full only: recover witnessed historical extensions in the existing model.
    pub(super) fn add_stored_family_admission(&mut self) -> Result<(), SpecError> {
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Witnessed fresh-extension model history and exact computed membership recovery; no Rust reuse or execution-refinement judgment.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent positional model-history lookup or Type-valued history-evidence fold.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
const PROOF_ROOTS: &[&str] = &[
    "sfa_const_entries",
    "sfa_inductive_entries",
    "sfa_extension_entries",
    "sfa_sound_entries",
    "sfa_entries_at",
    "sfa_stored_family_admission",
    "sfa_prior_family_caller",
    "sfa_constant_tail_caller",
];

#[cfg(test)]
const TYPE_PROOF_ROOTS: &[&str] = &[
    "sfa_const_entries",
    "sfa_inductive_entries",
    "sfa_extension_entries",
    "sfa_sound_entries",
    "sfa_entries_at",
    "sfa_stored_family_admission",
    "sfa_prior_family_caller",
    "sfa_constant_tail_caller",
];

#[cfg(test)]
const DATA_NAMES: &[&str] = &["sfa_entry_at", "sfa_entries"];

#[cfg(test)]
const PROP_PROOF_ROOTS: &[&str] = &[];

#[cfg(test)]
const INDUCTIVE_NAMES: &[&str] = &[];

// False exact-history lookups are tested as Prop-valued proof bodies, never
// traversed by the production registrar.
#[cfg(test)]
const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "sfa_false_changed_former",
        r"@Eq (OptionType KEnv) (sfa_entry_at env_freshness_second env_freshness_one)
 (@OptionType.some KEnv (KEnv.addInductive KEnv.empty Nat.zero Nat.zero (KExpr.sort Level.zero)
  (env_freshness_ctors env_freshness_one)))",
        r"@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first)",
    ),
    (
        "sfa_false_changed_parameters",
        r"@Eq (OptionType KEnv) (sfa_entry_at env_freshness_second env_freshness_one)
 (@OptionType.some KEnv (KEnv.addInductive KEnv.empty Nat.zero env_freshness_one env_freshness_type
  (env_freshness_ctors env_freshness_one)))",
        r"@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first)",
    ),
    (
        "sfa_false_shortened_constructors",
        r"@Eq (OptionType KEnv) (sfa_entry_at env_freshness_second env_freshness_one)
 (@OptionType.some KEnv (KEnv.addInductive KEnv.empty Nat.zero Nat.zero env_freshness_type CtorDecls.nil))",
        r"@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first)",
    ),
    (
        "sfa_false_wrong_position",
        r"@Eq (OptionType KEnv) (sfa_entry_at env_freshness_second Nat.zero) (@OptionType.some KEnv env_freshness_first)",
        r"@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_second)",
    ),
];

#[cfg(test)]
mod tests;

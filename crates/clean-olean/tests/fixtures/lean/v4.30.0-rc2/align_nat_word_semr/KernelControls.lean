/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Lean
import AlignNatWordSemRQualification

set_option debug.skipKernelTC false
set_option Elab.async false

open Lean Elab Command

-- This diagnostic uses the normal checked kernel API at its default limits.
-- Returned temporary environments are discarded; no control is registered.
run_cmd do
  let env ← getEnv
  let opts ← getOptions
  if Lean.debug.skipKernelTC.get opts then
    throwError "A1 SDK controls require kernel checking"
  let check (subject : Name) (target : Expr) (tag : String) (accepted : Bool) :
      CommandElabM Unit := do
    let some (.thmInfo proof) := env.find? subject
      | throwError "missing original theorem {subject}"
    let declaration := Declaration.thmDecl
      { name := .str `SemRWordSDKControls tag, levelParams := proof.levelParams,
        type := target, value := proof.value }
    match env.toKernelEnv.addDecl opts declaration with
    | .ok _ =>
      if accepted then logInfo m!"{tag}"
      else throwError "SDK accepted forged proposition: {tag}"
    | .error (.declTypeMismatch ..) =>
      if accepted then throwError "SDK refused original proposition: {tag}"
      else logInfo m!"{tag}"
    | .error _ => throwError "SDK control had a non-type-mismatch failure: {tag}"
  let modules := #[`AlignNatWordSemR, `AlignNatWordSemRContracts]
  let mut theoremCount := 0
  for (subject, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? subject then
      if let some source := env.allImportedModuleNames[idx.toNat]? then
        if modules.contains source then
          if let .thmInfo proof := info then
            check subject proof.type s!"SEMR_WORD_SDK_ORIGINAL {subject}" true
            check subject (mkConst ``False) s!"SEMR_WORD_SDK_FALSE {subject}" false
            theoremCount := theoremCount + 1
  if theoremCount == 0 then throwError "empty SDK theorem population"
  let literal (subject : Name) : CommandElabM Expr := do
    let some (.defnInfo value) := env.find? subject
      | throwError "missing independent proposition {subject}"
    pure value.value
  check ``AlignNatWordSemR.udiv_word (← literal ``AlignNatWordSemRContracts.divGuarded)
    "SEMR_WORD_SDK_LITERAL divGuarded" true
  check ``AlignNatWordSemR.urem_word (← literal ``AlignNatWordSemRContracts.modGuarded)
    "SEMR_WORD_SDK_LITERAL modGuarded" true
  check ``AlignNatWordSemR.udiv_success_iff (← literal ``AlignNatWordSemRContracts.divSuccess)
    "SEMR_WORD_SDK_LITERAL divSuccess" true
  check ``AlignNatWordSemR.urem_success_iff (← literal ``AlignNatWordSemRContracts.modSuccess)
    "SEMR_WORD_SDK_LITERAL modSuccess" true
  check ``AlignNatWordSemR.udiv_zero (← literal ``AlignNatWordSemRContracts.divZero)
    "SEMR_WORD_SDK_LITERAL divZero" true
  check ``AlignNatWordSemR.urem_zero (← literal ``AlignNatWordSemRContracts.modZero)
    "SEMR_WORD_SDK_LITERAL modZero" true
  check ``AlignNatWordSemR.udiv_word (← literal ``AlignNatWordSemRContracts.swappedDiv)
    "SEMR_WORD_SDK_SWAP div" false
  check ``AlignNatWordSemR.urem_word (← literal ``AlignNatWordSemRContracts.swappedMod)
    "SEMR_WORD_SDK_SWAP mod" false
  check ``AlignNatWordSemR.udiv_word (← literal ``AlignNatWordSemRContracts.unguardedDiv)
    "SEMR_WORD_SDK_OMIT div" false
  check ``AlignNatWordSemR.urem_word (← literal ``AlignNatWordSemRContracts.unguardedMod)
    "SEMR_WORD_SDK_OMIT mod" false
  logInfo m!"SEMR_WORD_SDK_OWNED_THEOREMS {theoremCount}"

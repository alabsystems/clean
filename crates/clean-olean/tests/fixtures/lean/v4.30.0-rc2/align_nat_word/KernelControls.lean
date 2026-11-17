/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Lean
import AlignNatWordQualification

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
      { name := .str `A1SDKControls tag, levelParams := proof.levelParams,
        type := target, value := proof.value }
    match env.toKernelEnv.addDecl opts declaration with
    | .ok _ =>
      if accepted then logInfo m!"{tag}"
      else throwError "SDK accepted forged proposition: {tag}"
    | .error (.declTypeMismatch ..) =>
      if accepted then throwError "SDK refused original proposition: {tag}"
      else logInfo m!"{tag}"
    | .error _ => throwError "SDK control had a non-type-mismatch failure: {tag}"
  let modules := #[`AlignNatWord.Arithmetic, `AlignNatWordContracts]
  let mut theoremCount := 0
  for (subject, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? subject then
      if let some source := env.allImportedModuleNames[idx.toNat]? then
        if modules.contains source then
          if let .thmInfo proof := info then
            check subject proof.type s!"A1_SDK_ORIGINAL {subject}" true
            check subject (mkConst ``False) s!"A1_SDK_FALSE {subject}" false
            theoremCount := theoremCount + 1
  if theoremCount == 0 then throwError "empty SDK theorem population"
  let literal (subject : Name) : CommandElabM Expr := do
    let some (.defnInfo value) := env.find? subject
      | throwError "missing independent proposition {subject}"
    pure value.value
  check ``AlignNatWord.div64_toNat (← literal ``AlignNatWordContracts.divBridge)
    "A1_SDK_LITERAL div" true
  check ``AlignNatWord.mod64_toNat (← literal ``AlignNatWordContracts.modBridge)
    "A1_SDK_LITERAL mod" true
  check ``AlignNatWord.div64_toNat (← literal ``AlignNatWordContracts.swappedDivBridge)
    "A1_SDK_SWAP div" false
  check ``AlignNatWord.mod64_toNat (← literal ``AlignNatWordContracts.swappedModBridge)
    "A1_SDK_SWAP mod" false
  logInfo m!"A1_SDK_OWNED_THEOREMS {theoremCount}"

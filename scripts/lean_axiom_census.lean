/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
-- The driver prepends imports of every source module and Lean. This is an
-- untrusted evidence producer, not the self-proof plan's trusted checker.
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      -- Selection is by module of origin, including _private declarations.
      if e7Modules.contains origin.toString then
        declarations := declarations + 1
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quotient"
        -- collectAxioms is precisely the implementation of #print axioms.
        -- Also execute the command itself, with the fully resolved name; this
        -- exercises private-name resolution and leaves a printable transcript.
        elabCommand (← `(#print axioms $(mkIdent name)))
        let axioms ← collectAxioms name
        logInfo ("E7_ROW " ++ (Json.mkObj [
          ("module", toJson origin.toString),
          ("declaration", toJson name.toString),
          ("kind", toJson kind),
          ("axiom_closure", toJson (axioms.map Name.toString))]).compress)
  logInfo ("E7_COUNT " ++ toString declarations)

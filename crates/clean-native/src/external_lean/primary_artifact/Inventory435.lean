/- Test-only raw SDK census. The maintained 4.30 DumpOlean oracle's
environment-mode initializer has an incompatible 4.35 type; this probe uses
only upstream readModuleDataParts and actual ModuleData fields. It grants no
source, replay or native authority and implements no artifact parser. -/
import Lean
open Lean

-- Same structural Name projection as the maintained DumpOlean oracle.
def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str parent text =>
    (nameComponents parent).push (.mkObj [("kind", .str "str"), ("value", .str text)])
  | .num parent number =>
    (nameComponents parent).push (.mkObj [("kind", .str "num"), ("value", toJson number)])

def nameJson (name : Name) : Json := .arr (nameComponents name)

def main (args : List String) : IO Unit := do
  let parts ← readModuleDataParts (args.toArray.map System.FilePath.mk)
  let result := parts.map fun part => Json.mkObj [
    ("const_names", .arr (part.1.constNames.map nameJson)),
    ("constants", .arr (part.1.constants.map fun c => .mkObj [
      ("name", nameJson c.name), ("is_unsafe", toJson c.isUnsafe),
      ("is_partial", toJson c.isPartial)]))]
  let encoded := (Json.mkObj [("parts", .arr result)]).compress
  IO.println encoded
  unless parts.size == args.length do
    throw (IO.userError "actual SDK returned an incomplete part array")

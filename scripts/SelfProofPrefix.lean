/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import KCheckRun.Recognise
import Lean.Data.Json

/-!
Ordered diagnostic on the actual interim reader and adopted checker. Each parsed
record is removed from the loader's output queue after its one checker call.
The loader's tables and the checker's returned environment persist across calls.
-/
open Lean (Json toJson)

private def emit (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj fields).compress

private def components (name : Lean.Name) : List Json :=
  name.components.map (fun component => match component with
    | .str _ s => toJson s
    | .num _ n => toJson n
    | .anonymous => Json.null)

private def recordFields (record : KCheckRun.Record) : List (String × Json) :=
  let names := match record.rows with
    | some rows => rows.types.map KCheckRun.TypeRow.name ++ rows.ctors.map KCheckRun.CtorRow.name ++ rows.recs.map KCheckRun.RecRow.name
    | none => [record.name]
  [("kind", toJson record.kind), ("name", toJson (toString record.name)),
   ("names", toJson (names.map toString)), ("name_components", toJson (names.map components))]

private def stop (why : String) (line : Nat) (fields : List (String × Json) := []) : IO Unit :=
  emit ([("stop", toJson why), ("line", toJson line)] ++ fields)

def main (args : List String) : IO UInt32 := do
  let [file, bound] := args | throw (IO.userError "expected EXPORT and an optional numeric bound or all")
  let limit ← if bound == "all" then pure none else
    match bound.toNat? with
    | some n => pure (some n)
    | none => throw (IO.userError "invalid bound")
  let bytes ← IO.FS.readBinFile file
  if bytes.isEmpty then
    stop "loader_refused" 0 [("reason", toJson "the export is empty"), ("stage", toJson "bytes")]
    return 0
  let mut st := KCheckRun.LoadState.start (bytes.size / 16)
  let mut env := KCheck.base
  let mut line := 0
  let mut pos := 0
  let mut accepted := 0
  while pos < bytes.size do
    if limit == some accepted then
      stop "limit_reached" line
      return 0
    line := line + 1
    let (json, endPos) ← match KCheckRun.value bytes (bytes.size + 2) pos with
      | .ok parsed => pure parsed
      | .error reason =>
        stop "loader_refused" line [("reason", toJson reason), ("stage", toJson "bytes")]
        return 0
    unless KCheckRun.byteIs bytes endPos 0x0A do
      stop "loader_refused" line [("reason", toJson "the record is not followed by a line feed (cut short, or trailing bytes)"),
                                ("stage", toJson "bytes")]
      return 0
    pos := endPos + 1
    let updated := if line == 1 then (KCheckRun.checkMeta json).map (fun _ => st) else st.line line json
    match updated with
    | .error reason =>
      stop "loader_refused" line [("reason", toJson reason), ("stage", toJson "load")]
      return 0
    | .ok next => st := next
    if let some record := st.records[0]? then
      st := { st with records := #[] }
      let mut fields := recordFields record
      if let .inductiveBlock block := record.input then
        let known := (KCheck.recogniseBlock env block).isSome
        let recognised := (KCheckRun.recognised record).isSome
        fields := fields ++ [("known_family", toJson known), ("recognised_rows", toJson recognised),
          ("unit_template", toJson (KCheck.UnitFamilyPacket.extract block).isSome)]
        if known && !recognised then
          stop "loader_refused" line (fields ++ [("stage", toJson "family_rows"),
            ("reason", toJson "the loader's recursor comparison failed for the known family")])
          return 0
      match KCheck.kcheckBytes env record.input ByteArray.empty with
      | .error err =>
        stop "checker_refused" line (fields ++ [("reason", toJson ((repr err).pretty 1000000))])
        return 0
      | .ok (next, receipt) =>
        emit (fields ++ [("line", toJson line), ("receipt", toJson (toString receipt.name)),
                        ("receipt_components", toJson (components receipt.name))])
        env := next
        accepted := accepted + 1
  stop "exhausted" line
  return 0

/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Compare an export with pinned Lean's own environment, constant by constant.

    lean --run Compare.lean <export.ndjson> <module>...

Run by `scripts/lean_export_replay.sh --reader upstream --against <module>`,
which compiles lean4export's own parser (`Export/Parse.lean`) at the commit
the mint script pins and puts it, and the modules' `.olean` directories, on
LEAN_PATH; do not run it with a bare `lean` (under aterm that is Clean).

WHY. Self-proof unit Q1 has Clean write Lean's export format from Clean's
kernel terms (`clean_export_write`). Comparing that file with lean4export's
cannot settle binder information: lean4export's expression table is a
`HashMap Expr Nat` and Lean's `BEq Expr` (`Expr.eqv`) ignores binder
annotations, so lean4export writes a term that differs from an earlier one
only in its annotations as that earlier term. This file compares with what
Lean itself holds instead: the export is parsed by lean4export's parser
(not Clean's), the modules are imported by Lean, and every constant the
export declares must be in that environment and equal to it.

WHAT "EQUAL" IS. Every field of the `ConstantInfo` is compared exactly
(level parameters, every count and flag, hints, safety, `all`, constructor
and recursor lists, recursor rules, quotient kind), and every expression with
`Expr.equal` (binder annotations included) after both sides are normalized
by `norm`: every `lam`/`forallE` binder name made anonymous and every `mdata`
payload emptied. Those two are what the export of Clean's kernel terms does
not carry (Clean's terms keep no binder names; the writer writes an `mdata`
node with an empty payload); a `letE`'s name is compared.

Exit 0: every constant present and equal; the last line of stdout is one
JSON object. Exit 1: a constant absent or different, listed in that object.
Exit 2: usage, or an export this file does not judge (format or Lean
version).
-/
import Export.Parse
import Lean
open Lean

namespace ExportCompare

/-- The header: format 3.1, and the Lean that is running. -/
def checkMeta (j : Json) : Except String (String × String) := do
  let m ← j.getObjVal? "meta"
  let format ← (← (← m.getObjVal? "format").getObjVal? "version").getStr?
  let lean ← m.getObjVal? "lean"
  let version ← (← lean.getObjVal? "version").getStr?
  let githash ← (← lean.getObjVal? "githash").getStr?
  if !format.startsWith "3.1." then throw s!"format version {format} is not 3.1"
  if version != Lean.versionString then
    throw s!"the export states Lean {version}; this comparison runs Lean {Lean.versionString}"
  if githash != Lean.githash then
    throw s!"the export states githash {githash}; this comparison runs {Lean.githash}"
  pure (version, githash)

abbrev Cache := Std.HashMap ExprStructEq Expr

/-- `e` with binder names anonymous and `mdata` payloads empty, memoized by
structural identity (`ExprStructEq` is `Expr.equal`: names and annotations
included), so a shared subterm is normalized once. -/
partial def norm (e : Expr) : StateM Cache Expr := do
  if let some r := (← get)[(e : ExprStructEq)]? then return r
  let r ← match e with
    | .lam _ t b bi => pure (.lam .anonymous (← norm t) (← norm b) bi)
    | .forallE _ t b bi => pure (.forallE .anonymous (← norm t) (← norm b) bi)
    | .letE n t v b nondep => pure (.letE n (← norm t) (← norm v) (← norm b) nondep)
    | .app f a => pure (.app (← norm f) (← norm a))
    | .mdata _ x => pure (.mdata {} (← norm x))
    | .proj s i x => pure (.proj s i (← norm x))
    | other => pure other
  modify (·.insert e r)
  return r

def sameExpr (a b : Expr) : StateM Cache Bool := do
  return (← norm a).equal (← norm b)

def hintsStr : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def quotStr : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def kindStr : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- The fields in which `ours` (the export) differs from `lean` (Lean's
environment); `[]` when equal. -/
def differences (lean ours : ConstantInfo) : StateM Cache (List String) := do
  let mut out : List String := []
  let flag (b : Bool) (field : String) (acc : List String) : List String :=
    if b then acc else field :: acc
  if kindStr lean != kindStr ours then
    return [s!"kind {kindStr lean} vs {kindStr ours}"]
  out := flag (lean.levelParams == ours.levelParams) "levelParams" out
  out := flag (← sameExpr lean.type ours.type) "type" out
  match lean, ours with
  | .axiomInfo a, .axiomInfo b =>
    out := flag (a.isUnsafe == b.isUnsafe) "isUnsafe" out
  | .defnInfo a, .defnInfo b =>
    out := flag (← sameExpr a.value b.value) "value" out
    out := flag (hintsStr a.hints == hintsStr b.hints)
      s!"hints {hintsStr a.hints} vs {hintsStr b.hints}" out
    out := flag (a.safety == b.safety) "safety" out
    out := flag (a.all == b.all) "all" out
  | .thmInfo a, .thmInfo b =>
    out := flag (← sameExpr a.value b.value) "value" out
    out := flag (a.all == b.all) "all" out
  | .opaqueInfo a, .opaqueInfo b =>
    out := flag (← sameExpr a.value b.value) "value" out
    out := flag (a.isUnsafe == b.isUnsafe) "isUnsafe" out
    out := flag (a.all == b.all) "all" out
  | .quotInfo a, .quotInfo b =>
    out := flag (quotStr a.kind == quotStr b.kind) "kind" out
  | .inductInfo a, .inductInfo b =>
    out := flag (a.numParams == b.numParams) "numParams" out
    out := flag (a.numIndices == b.numIndices) "numIndices" out
    out := flag (a.all == b.all) "all" out
    out := flag (a.ctors == b.ctors) "ctors" out
    out := flag (a.numNested == b.numNested) "numNested" out
    out := flag (a.isRec == b.isRec) "isRec" out
    out := flag (a.isUnsafe == b.isUnsafe) "isUnsafe" out
    out := flag (a.isReflexive == b.isReflexive) "isReflexive" out
  | .ctorInfo a, .ctorInfo b =>
    out := flag (a.induct == b.induct) "induct" out
    out := flag (a.cidx == b.cidx) "cidx" out
    out := flag (a.numParams == b.numParams) "numParams" out
    out := flag (a.numFields == b.numFields) "numFields" out
    out := flag (a.isUnsafe == b.isUnsafe) "isUnsafe" out
  | .recInfo a, .recInfo b =>
    out := flag (a.all == b.all) "all" out
    out := flag (a.numParams == b.numParams) "numParams" out
    out := flag (a.numIndices == b.numIndices) "numIndices" out
    out := flag (a.numMotives == b.numMotives) "numMotives" out
    out := flag (a.numMinors == b.numMinors) "numMinors" out
    out := flag (a.k == b.k) "k" out
    out := flag (a.isUnsafe == b.isUnsafe) "isUnsafe" out
    if a.rules.length != b.rules.length then
      out := "rules" :: out
    else
      let mut same := true
      for (x, y) in a.rules.zip b.rules do
        if x.ctor != y.ctor || x.nfields != y.nfields || !(← sameExpr x.rhs y.rhs) then
          same := false
      out := flag same "rules" out
  | _, _ => pure ()
  return out.reverse

end ExportCompare

open ExportCompare in
def main (args : List String) : IO UInt32 := do
  let (path, modules) ← match args with
    | path :: modules@(_ :: _) => pure (path, modules)
    | _ => do
      IO.eprintln "usage: lean --run Compare.lean <export.ndjson> <module>..."
      return (2 : UInt32)
  let first ← (← IO.FS.Handle.mk path .read).getLine
  let (version, githash) ← match Json.parse first >>= checkMeta with
    | .ok v => pure v
    | .error e => do
      IO.eprintln s!"lean_export_compare: not judged: {e}"
      return (2 : UInt32)
  let exported ← try
      Export.parseStream (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk path .read))
    catch e => do
      IO.eprintln s!"lean_export_compare: REJECTED (upstream reader): {e}"
      return (1 : UInt32)
  initSearchPath (← findSysroot)
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
  let mut cache : Cache := {}
  let mut absent : Array String := #[]
  let mut differing : Array Json := #[]
  let mut byField : Std.HashMap String Nat := {}
  let mut equal := 0
  for n in exported.constOrder do
    let some ours := exported.constMap[n]? | continue
    match env.find? n with
    | none => absent := absent.push n.toString
    | some lean =>
      let (fields, cache') := (differences lean ours).run cache
      cache := cache'
      if fields.isEmpty then
        equal := equal + 1
      else
        for f in fields do
          let key := (f.splitOn " ").head!
          byField := byField.insert key (byField.getD key 0 + 1)
        differing := differing.push (Json.mkObj [
          ("name", toJson n.toString), ("fields", toJson fields)])
  let fieldCounts := byField.toList.toArray.qsort (fun a b => a.1 < b.1)
  IO.println (Json.mkObj [
    ("verdict", if absent.isEmpty && differing.isEmpty then "equal" else "different"),
    ("against", "Lean's environment (importModules)"),
    ("reader", "lean4export Export.parseStream"),
    ("modules", toJson modules), ("lean_version", version), ("lean_githash", githash),
    ("compared", exported.constOrder.size), ("equal", equal),
    ("absent", toJson absent), ("differing_count", differing.size),
    ("differing_by_field", Json.mkObj (fieldCounts.toList.map fun (k, v) => (k, toJson v))),
    ("differing", Json.arr (differing.extract 0 200))]).compress
  return (if absent.isEmpty && differing.isEmpty then 0 else 1 : UInt32)

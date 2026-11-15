/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

Replay a lean4export NDJSON 3.1 export through Lean's own kernel.

    lean --run Replay.lean <export.ndjson> [--permit <axiom>]...

Run by `scripts/lean_export_replay.sh`, which picks the toolchain and the
environment; do not run it with a bare `lean` (under aterm that is Clean).

WHY. Unit Q1 of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md is done
when Lean's kernel accepts an export that Clean wrote. The toolchains before
v4.35 ship no reader of the format (`leanchecker` reads `.olean`s), so this
file is a reader: it parses the records into `ConstantInfo`s and hands them
to `Lean.Environment.replay` (Lean/Replay.lean, the engine of `leanchecker`),
starting from `mkEmptyEnvironment`. Every definition, theorem, opaque constant
and axiom goes to the kernel's `addDecl`; an inductive block is added from its
types and constructors, and its stored constructors and recursors must then
equal the ones the kernel generated; a `quot` record adds `quotDecl`.

WHAT IT IS NOT. It is not lean4export's own reader and it is not upstream's
`lake check`: the parsing below is Clean's reading of format_ndjson.md, in
Lean. The kernel that decides is Lean's. `Upstream.lean` beside this file
reads the same bytes with lean4export's own parser instead
(`scripts/lean_export_replay.sh --reader upstream`).

The reading is strict where a loose one could hide a difference: an index may
be bound once, a reference must be to a bound index, a declaration name may
be declared once, and a record must be one this file knows. An `unsafe` or
`partial` declaration is refused (Lean's replay would skip it, and a skipped
declaration is no evidence).

Exit 0: every declaration replayed and every axiom permitted; the last line
of stdout is one JSON object. Exit 1: refused, with the reason on stderr.
Exit 2: usage, or an export this file does not judge (another format version,
or a Lean version other than the one running).
-/
import Lean
open Lean

namespace CleanExportReplay

structure Tables where
  names : Std.HashMap Nat Name := (∅ : Std.HashMap Nat Name).insert 0 .anonymous
  levels : Std.HashMap Nat Level := (∅ : Std.HashMap Nat Level).insert 0 .zero
  exprs : Std.HashMap Nat Expr := ∅
  consts : Std.HashMap Name ConstantInfo := ∅
  axioms : Array Name := #[]
  line : Nat := 0

abbrev M := StateRefT Tables IO

def fail {α : Type} (msg : String) : M α := do
  throw <| IO.userError s!"line {(← get).line}: {msg}"

def ok {α : Type} (what : String) : Except String α → M α
  | .ok v => pure v
  | .error e => fail s!"{what}: {e}"

def field (j : Json) (k : String) : M Json := ok k (j.getObjVal? k)
def natOf (what : String) (j : Json) : M Nat := ok what j.getNat?
def nat (j : Json) (k : String) : M Nat := do natOf k (← field j k)
def str (j : Json) (k : String) : M String := do ok k (← field j k).getStr?
def bool (j : Json) (k : String) : M Bool := do ok k (← field j k).getBool?
def arr (j : Json) (k : String) : M (Array Json) := do ok k (← field j k).getArr?

def nameAt (i : Nat) : M Name := do
  match (← get).names[i]? with
  | some n => pure n
  | none => fail s!"name index {i} is not bound"

def levelAt (i : Nat) : M Level := do
  match (← get).levels[i]? with
  | some l => pure l
  | none => fail s!"level index {i} is not bound"

def exprAt (i : Nat) : M Expr := do
  match (← get).exprs[i]? with
  | some e => pure e
  | none => fail s!"expression index {i} is not bound"

def nameField (j : Json) (k : String) : M Name := do nameAt (← nat j k)
def exprField (j : Json) (k : String) : M Expr := do exprAt (← nat j k)
def namesField (j : Json) (k : String) : M (List Name) := do
  (← arr j k).toList.mapM fun x => do nameAt (← natOf k x)

def has (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

def bindName (j : Json) (i : Nat) : M Unit := do
  if (← get).names.contains i then fail s!"name index {i} is bound twice"
  let n ←
    if has j "str" then do
      let d ← field j "str"
      pure (Name.str (← nameField d "pre") (← str d "str"))
    else if has j "num" then do
      let d ← field j "num"
      pure (Name.num (← nameField d "pre") (← nat d "i"))
    else fail "a name record that is neither str nor num"
  modify fun s => { s with names := s.names.insert i n }

def bindLevel (j : Json) (i : Nat) : M Unit := do
  if (← get).levels.contains i then fail s!"level index {i} is bound twice"
  let pair (k : String) : M (Level × Level) := do
    let xs ← arr j k
    if xs.size != 2 then fail s!"{k} needs two levels"
    pure (← levelAt (← natOf k xs[0]!), ← levelAt (← natOf k xs[1]!))
  let l ←
    if has j "succ" then do pure (Level.succ (← levelAt (← nat j "succ")))
    else if has j "max" then do let (a, b) ← pair "max"; pure (Level.max a b)
    else if has j "imax" then do let (a, b) ← pair "imax"; pure (Level.imax a b)
    else if has j "param" then do pure (Level.param (← nameField j "param"))
    else fail "a level record of no known kind"
  modify fun s => { s with levels := s.levels.insert i l }

def binderInfo (j : Json) : M BinderInfo := do
  match ← str j "binderInfo" with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | other => fail s!"unknown binderInfo {other}"

def bindExpr (j : Json) (i : Nat) : M Unit := do
  if (← get).exprs.contains i then fail s!"expression index {i} is bound twice"
  let e ←
    if has j "bvar" then do pure (Expr.bvar (← nat j "bvar"))
    else if has j "sort" then do pure (Expr.sort (← levelAt (← nat j "sort")))
    else if has j "const" then do
      let d ← field j "const"
      let us ← (← arr d "us").toList.mapM fun x => do levelAt (← natOf "us" x)
      pure (Expr.const (← nameField d "name") us)
    else if has j "app" then do
      let d ← field j "app"
      pure (Expr.app (← exprField d "fn") (← exprField d "arg"))
    else if has j "lam" then do
      let d ← field j "lam"
      pure (Expr.lam (← nameField d "name") (← exprField d "type") (← exprField d "body")
        (← binderInfo d))
    else if has j "forallE" then do
      let d ← field j "forallE"
      pure (Expr.forallE (← nameField d "name") (← exprField d "type") (← exprField d "body")
        (← binderInfo d))
    else if has j "letE" then do
      let d ← field j "letE"
      pure (Expr.letE (← nameField d "name") (← exprField d "type") (← exprField d "value")
        (← exprField d "body") (← bool d "nondep"))
    else if has j "proj" then do
      let d ← field j "proj"
      pure (Expr.proj (← nameField d "typeName") (← nat d "idx") (← exprField d "struct"))
    else if has j "natVal" then do
      let text ← str j "natVal"
      match text.toNat? with
      | some n => pure (Expr.lit (.natVal n))
      | none => fail "natVal is not a decimal natural"
    else if has j "strVal" then do pure (Expr.lit (.strVal (← str j "strVal")))
    else if has j "mdata" then do
      let d ← field j "mdata"
      pure (Expr.mdata {} (← exprField d "expr"))
    else fail "an expression record of no known kind"
  modify fun s => { s with exprs := s.exprs.insert i e }

def declare (ci : ConstantInfo) : M Unit := do
  if (← get).consts.contains ci.name then fail s!"duplicate declaration {ci.name}"
  if ci.isUnsafe || ci.isPartial then
    fail s!"{ci.name} is unsafe or partial: Lean's replay would skip it"
  modify fun s => { s with consts := s.consts.insert ci.name ci }

def constantVal (d : Json) : M ConstantVal := do
  pure { name := ← nameField d "name", levelParams := ← namesField d "levelParams",
         type := ← exprField d "type" }

def declaration (j : Json) : M Unit := do
  if has j "axiom" then
    let d ← field j "axiom"
    let cv ← constantVal d
    declare (.axiomInfo { cv with isUnsafe := ← bool d "isUnsafe" })
    modify fun s => { s with axioms := s.axioms.push cv.name }
  else if has j "def" then
    let d ← field j "def"
    let cv ← constantVal d
    let h ← field d "hints"
    let hints ← match h with
      | .str "opaque" => pure ReducibilityHints.opaque
      | .str "abbrev" => pure ReducibilityHints.abbrev
      | _ => do pure (ReducibilityHints.regular (← nat h "regular").toUInt32)
    let safety ← match ← str d "safety" with
      | "safe" => pure DefinitionSafety.safe
      | "unsafe" => pure DefinitionSafety.unsafe
      | "partial" => pure DefinitionSafety.partial
      | other => fail s!"unknown safety {other}"
    declare (.defnInfo { cv with value := ← exprField d "value", hints, safety,
                                 all := ← namesField d "all" })
  else if has j "thm" then
    let d ← field j "thm"
    let cv ← constantVal d
    declare (.thmInfo { cv with value := ← exprField d "value", all := ← namesField d "all" })
  else if has j "opaque" then
    let d ← field j "opaque"
    let cv ← constantVal d
    declare (.opaqueInfo { cv with value := ← exprField d "value",
                                   isUnsafe := ← bool d "isUnsafe", all := ← namesField d "all" })
  else if has j "quot" then
    let d ← field j "quot"
    let cv ← constantVal d
    let kind ← match ← str d "kind" with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind" => pure QuotKind.ind
      | other => fail s!"unknown quot kind {other}"
    declare (.quotInfo { cv with kind })
  else if has j "inductive" then
    let d ← field j "inductive"
    for t in ← arr d "types" do
      let cv ← constantVal t
      declare (.inductInfo { cv with
        numParams := ← nat t "numParams", numIndices := ← nat t "numIndices",
        all := ← namesField t "all", ctors := ← namesField t "ctors",
        numNested := ← nat t "numNested", isRec := ← bool t "isRec",
        isUnsafe := ← bool t "isUnsafe", isReflexive := ← bool t "isReflexive" })
    for c in ← arr d "ctors" do
      let cv ← constantVal c
      declare (.ctorInfo { cv with
        induct := ← nameField c "induct", cidx := ← nat c "cidx",
        numParams := ← nat c "numParams", numFields := ← nat c "numFields",
        isUnsafe := ← bool c "isUnsafe" })
    for r in ← arr d "recs" do
      let cv ← constantVal r
      let rules ← (← arr r "rules").toList.mapM fun rule => do
        pure ({ ctor := ← nameField rule "ctor", nfields := ← nat rule "nfields",
                rhs := ← exprField rule "rhs" } : RecursorRule)
      declare (.recInfo { cv with
        all := ← namesField r "all", numParams := ← nat r "numParams",
        numIndices := ← nat r "numIndices", numMotives := ← nat r "numMotives",
        numMinors := ← nat r "numMinors", rules, k := ← bool r "k",
        isUnsafe := ← bool r "isUnsafe" })
  else fail "a record of no known kind"

def record (j : Json) : M Unit := do
  if has j "in" then bindName j (← nat j "in")
  else if has j "il" then bindLevel j (← nat j "il")
  else if has j "ie" then bindExpr j (← nat j "ie")
  else declaration j

/-- The header: format 3.1, and the Lean that is running. -/
def checkMeta (j : Json) : Except String (String × String) := do
  let m ← j.getObjVal? "meta"
  let format ← (← (← m.getObjVal? "format").getObjVal? "version").getStr?
  let lean ← m.getObjVal? "lean"
  let version ← (← lean.getObjVal? "version").getStr?
  let githash ← (← lean.getObjVal? "githash").getStr?
  if !format.startsWith "3.1." then throw s!"format version {format} is not 3.1"
  if version != Lean.versionString then
    throw s!"the export states Lean {version}; this replay runs Lean {Lean.versionString}"
  if githash != Lean.githash then
    throw s!"the export states githash {githash}; this replay runs {Lean.githash}"
  pure (version, githash)

partial def readAll (h : IO.FS.Handle) : M Unit := do
  let text ← h.getLine
  if text.isEmpty then return
  modify fun s => { s with line := s.line + 1 }
  let j ← ok "JSON" (Json.parse text)
  record j
  readAll h

end CleanExportReplay

open CleanExportReplay in
def main (args : List String) : IO UInt32 := do
  let rec permits : List String → Except String (List String)
    | [] => pure []
    | "--permit" :: a :: rest => do pure (a :: (← permits rest))
    | other :: _ => throw s!"unexpected argument {other}"
  let (path, permitted) ← match args with
    | path :: rest => match permits rest with
      | .ok ps => pure (path, ps)
      | .error e => do
        IO.eprintln s!"lean_export_replay: {e}"
        return (2 : UInt32)
    | [] => do
      IO.eprintln "usage: lean --run Replay.lean <export.ndjson> [--permit <axiom>]..."
      return (2 : UInt32)
  let h ← IO.FS.Handle.mk path .read
  let first ← h.getLine
  let (version, githash) ← match Json.parse first >>= checkMeta with
    | .ok v => pure v
    | .error e => do
      IO.eprintln s!"lean_export_replay: not judged: {e}"
      return (2 : UInt32)
  let tables ← try
      let (_, tables) ← (readAll h).run { line := 1 }
      pure tables
    catch e => do
      IO.eprintln s!"lean_export_replay: REJECTED (reader): {e}"
      return (1 : UInt32)
  let env ← mkEmptyEnvironment
  let replayed ← try
      env.replay tables.consts
    catch e => do
      IO.eprintln s!"lean_export_replay: REJECTED (kernel): {e}"
      return (1 : UInt32)
  let mut missing := #[]
  for (n, _) in tables.consts.toList do
    if (replayed.toKernelEnv.find? n).isNone then missing := missing.push n
  if !missing.isEmpty then
    IO.eprintln s!"lean_export_replay: REJECTED: declared and not in the replayed environment: {missing}"
    return (1 : UInt32)
  let axioms := (tables.axioms.map toString).qsort (· < ·)
  let unpermitted := axioms.filter fun a => !permitted.contains a
  if !unpermitted.isEmpty then
    IO.eprintln s!"lean_export_replay: REJECTED: axioms outside the permitted set: {unpermitted}"
    return (1 : UInt32)
  IO.println (Json.mkObj [
    ("verdict", "accepted"), ("kernel", "Lean.Environment.replay"),
    ("lean_version", version), ("lean_githash", githash),
    ("declarations", tables.consts.size), ("lines", tables.line),
    ("axioms", toJson axioms), ("permitted", toJson permitted)]).compress
  return (0 : UInt32)

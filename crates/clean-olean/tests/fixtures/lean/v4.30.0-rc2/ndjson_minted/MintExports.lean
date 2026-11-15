/-
Mints the honest lean4export-format exports under this directory from the
pinned toolchain's own declarations (tests/ndjson_front_door_fidelity.rs):

    cd crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/ndjson_minted
    ~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean MintExports.lean
    gzip -9 -n init_dotted_names.ndjson

`MiniExport.run` writes the dependency closure of the given constants, the
values Lean's environment stores, in lean4export NDJSON 3.1.0's record shapes
(keys sorted as `Lean.Json` sorts them, an inductive block as one record with
its auxiliary recursors). It is not lean4export: `meta.exporter.name` says
`clean-mini-export`, and an `mdata` payload is written empty (a reader drops
it, as Lean's own reader does).
-/
import Lean
open Lean

namespace MiniExport

structure St where
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := {}
  exprs : Std.HashMap Expr Nat := {}
  done : NameSet := {}
  out : Array String := #[]

abbrev M := StateRefT St CoreM

def emit (j : Json) : M Unit := modify fun s => { s with out := s.out.push j.compress }

partial def nameIdx (n : Name) : M Nat := do
  if n.isAnonymous then return 0
  if let some i := (← get).names[n]? then return i
  let body ← match n with
    | .str p s => do
      let pi ← nameIdx p
      pure (Json.mkObj [("str", Json.mkObj [("pre", pi), ("str", s)])])
    | .num p k => do
      let pi ← nameIdx p
      pure (Json.mkObj [("num", Json.mkObj [("pre", pi), ("i", k)])])
    | .anonymous => unreachable!
  let i := (← get).names.size + 1
  modify fun s => { s with names := s.names.insert n i }
  emit (body.mergeObj (Json.mkObj [("in", i)]))
  return i

partial def levelIdx (l : Level) : M Nat := do
  if l == .zero then return 0
  if let some i := (← get).levels[l]? then return i
  let body ← match l with
    | .succ a => do pure (Json.mkObj [("succ", ← levelIdx a)])
    | .max a b => do
      let ia ← levelIdx a
      let ib ← levelIdx b
      pure (Json.mkObj [("max", Json.arr #[ia, ib])])
    | .imax a b => do
      let ia ← levelIdx a
      let ib ← levelIdx b
      pure (Json.mkObj [("imax", Json.arr #[ia, ib])])
    | .param n => do pure (Json.mkObj [("param", ← nameIdx n)])
    | _ => throwError "unexportable level {l}"
  let i := (← get).levels.size + 1
  modify fun s => { s with levels := s.levels.insert l i }
  emit (body.mergeObj (Json.mkObj [("il", i)]))
  return i

def binfo : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def exprIdx (e : Expr) : M Nat := do
  if let some i := (← get).exprs[e]? then return i
  let body ← match e with
    | .bvar k => pure (Json.mkObj [("bvar", k)])
    | .sort l => do pure (Json.mkObj [("sort", ← levelIdx l)])
    | .const n us => do
      let ni ← nameIdx n
      let ls ← us.mapM levelIdx
      pure (Json.mkObj [("const", Json.mkObj [("name", ni), ("us", toJson ls)])])
    | .app f a => do
      let fi ← exprIdx f
      let ai ← exprIdx a
      pure (Json.mkObj [("app", Json.mkObj [("fn", fi), ("arg", ai)])])
    | .lam n t b bi => do
      let ni ← nameIdx n
      let ti ← exprIdx t
      let bdi ← exprIdx b
      pure (Json.mkObj [("lam", Json.mkObj [("name", ni), ("type", ti), ("body", bdi), ("binderInfo", binfo bi)])])
    | .forallE n t b bi => do
      let ni ← nameIdx n
      let ti ← exprIdx t
      let bdi ← exprIdx b
      pure (Json.mkObj [("forallE", Json.mkObj [("name", ni), ("type", ti), ("body", bdi), ("binderInfo", binfo bi)])])
    | .letE n t v b nd => do
      let ni ← nameIdx n
      let ti ← exprIdx t
      let vi ← exprIdx v
      let bdi ← exprIdx b
      pure (Json.mkObj [("letE", Json.mkObj [("name", ni), ("type", ti), ("value", vi), ("body", bdi), ("nondep", nd)])])
    | .lit (.natVal k) => pure (Json.mkObj [("natVal", toString k)])
    | .lit (.strVal s) => pure (Json.mkObj [("strVal", s)])
    | .mdata _ x => do
      let xi ← exprIdx x
      pure (Json.mkObj [("mdata", Json.mkObj [("expr", xi), ("data", Json.mkObj [])])])
    | .proj t k x => do
      let ti ← nameIdx t
      let xi ← exprIdx x
      pure (Json.mkObj [("proj", Json.mkObj [("typeName", ti), ("idx", k), ("struct", xi)])])
    | _ => throwError "unexportable expression {e}"
  let i := (← get).exprs.size
  modify fun s => { s with exprs := s.exprs.insert e i }
  emit (body.mergeObj (Json.mkObj [("ie", i)]))
  return i

def names (ns : List Name) : M Json := do return toJson (← ns.mapM nameIdx)

def hints : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => Json.mkObj [("regular", h.toNat)]

def safety : DefinitionSafety → String
  | .safe => "safe"
  | .unsafe => "unsafe"
  | .partial => "partial"

/-- The constants a declaration's stored data names. -/
def deps (ci : ConstantInfo) : M (Array Name) := do
  let env ← getEnv
  let mut out : NameSet := ci.type.getUsedConstantsAsSet
  if let some v := ci.value? (allowOpaque := true) then
    out := out.union v.getUsedConstantsAsSet
  match ci with
  | .inductInfo v =>
    for c in v.ctors do out := out.insert c
    for t in v.all do out := out.insert t
  | .ctorInfo v => out := out.insert v.induct
  | .recInfo v =>
    for t in v.all do out := out.insert t
    for r in v.rules do out := out.union r.rhs.getUsedConstantsAsSet
  | .quotInfo _ => if let some _ := env.find? `Eq then out := out.insert `Eq
  | _ => pure ()
  return out.toArray

def blockRecs (v : InductiveVal) : M (List Name) := do
  let env ← getEnv
  let mut recs := v.all.map (· ++ `rec)
  let first := v.all.head!
  for i in [1:v.numNested + 1] do
    let n := first.str s!"rec_{i}"
    if env.contains n then recs := recs ++ [n]
  return recs

partial def dump (n : Name) : M Unit := do
  if (← get).done.contains n then return
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown constant {n}"
  -- an inductive block is one record: start from its first type
  let rep : Name := match ci with
    | .ctorInfo v => v.induct
    | .recInfo v => v.all.head!
    | _ => n
  if rep != n then
    dump rep
    if !(← get).done.contains n then throwError "{n} not emitted with its block"
    return
  match ci with
  | .inductInfo v =>
    let recs ← blockRecs v
    let members := v.all ++ (v.all.flatMap fun t =>
      match env.find? t with | some (.inductInfo tv) => tv.ctors | _ => []) ++ recs
    modify fun s => { s with done := members.foldl (·.insert ·) s.done }
    for m in members do
      let some mi := env.find? m | throwError "unknown block member {m}"
      for d in ← deps mi do dump d
    let mut types := #[]
    let mut ctors := #[]
    for t in v.all do
      let some (.inductInfo tv) := env.find? t | throwError "not an inductive {t}"
      types := types.push (Json.mkObj [
        ("name", ← nameIdx tv.name), ("levelParams", ← names tv.levelParams),
        ("type", ← exprIdx tv.type), ("numParams", tv.numParams),
        ("numIndices", tv.numIndices), ("all", ← names tv.all),
        ("ctors", ← names tv.ctors), ("numNested", tv.numNested),
        ("isRec", tv.isRec), ("isUnsafe", tv.isUnsafe),
        ("isReflexive", tv.isReflexive)])
      for c in tv.ctors do
        let some (.ctorInfo cv) := env.find? c | throwError "not a constructor {c}"
        ctors := ctors.push (Json.mkObj [
          ("name", ← nameIdx cv.name), ("levelParams", ← names cv.levelParams),
          ("type", ← exprIdx cv.type), ("induct", ← nameIdx cv.induct),
          ("cidx", cv.cidx), ("numParams", cv.numParams),
          ("numFields", cv.numFields), ("isUnsafe", cv.isUnsafe)])
    let mut rs := #[]
    for r in recs do
      let some (.recInfo rv) := env.find? r | throwError "not a recursor {r}"
      let mut rules := #[]
      for rule in rv.rules do
        rules := rules.push (Json.mkObj [("ctor", ← nameIdx rule.ctor),
          ("nfields", rule.nfields), ("rhs", ← exprIdx rule.rhs)])
      rs := rs.push (Json.mkObj [
        ("name", ← nameIdx rv.name), ("levelParams", ← names rv.levelParams),
        ("type", ← exprIdx rv.type), ("all", ← names rv.all),
        ("numParams", rv.numParams), ("numIndices", rv.numIndices),
        ("numMotives", rv.numMotives), ("numMinors", rv.numMinors),
        ("rules", Json.arr rules), ("k", rv.k), ("isUnsafe", rv.isUnsafe)])
    emit (Json.mkObj [("inductive", Json.mkObj [("types", Json.arr types),
      ("ctors", Json.arr ctors), ("recs", Json.arr rs)])])
  | _ =>
    modify fun s => { s with done := s.done.insert n }
    for d in ← deps ci do dump d
    let common := fun (rest : List (String × Json)) => do
      let head : List (String × Json) := [("name", toJson (← nameIdx ci.name)),
        ("levelParams", ← names ci.levelParams), ("type", toJson (← exprIdx ci.type))]
      return Json.mkObj (head ++ rest)
    match ci with
    | .axiomInfo v => emit (Json.mkObj [("axiom", ← common [("isUnsafe", v.isUnsafe)])])
    | .defnInfo v =>
      let val ← exprIdx v.value
      emit (Json.mkObj [("def", ← common [("value", val), ("hints", hints v.hints),
        ("safety", safety v.safety), ("all", ← names v.all)])])
    | .thmInfo v =>
      let val ← exprIdx v.value
      emit (Json.mkObj [("thm", ← common [("value", val), ("all", ← names v.all)])])
    | .opaqueInfo v =>
      let val ← exprIdx v.value
      emit (Json.mkObj [("opaque", ← common [("value", val), ("isUnsafe", v.isUnsafe),
        ("all", ← names v.all)])])
    | .quotInfo v =>
      let kind := match v.kind with
        | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
      emit (Json.mkObj [("quot", ← common [("kind", kind)])])
    | _ => throwError "unexpected constant kind {n}"

def run (roots : List Name) (path : System.FilePath) : CoreM Unit := do
  let hdr := Json.mkObj [("meta", Json.mkObj [
    ("exporter", Json.mkObj [("name", "clean-mini-export"), ("version", "3.1.0")]),
    ("format", Json.mkObj [("version", "3.1.0")]),
    ("lean", Json.mkObj [("githash", Lean.githash), ("version", Lean.versionString)])])]
  let (_, s) ← (roots.forM dump).run {}
  IO.FS.writeFile path (String.intercalate "\n" (hdr.compress :: s.out.toList) ++ "\n")

end MiniExport


/-! Nested inductives whose reflexivity Lean reads off the auxiliary block
(`inductive.cpp` computes the flags on the nested-eliminated declaration):
`NRT` and `HNR` store `isReflexive := true`, `NW` (nested, no function-typed
field) stores `false`. -/
inductive NRT where
  | mk : List (Nat → NRT) → NRT

structure HBox (α : Type) where
  f : Nat → α

inductive HNR where
  | mk : HBox HNR → HNR

inductive NW where
  | mk : List NW → NW

#eval MiniExport.run [``NRT, ``HNR, ``NW] "nested_reflexive.ndjson"

/-! `Nat.add` folded on literals: the kernel checks `2 + 3 = 5` by `rfl`. -/
theorem natAddLit : 2 + 3 = 5 := rfl

#eval MiniExport.run [``natAddLit] "nat_add_literal.ndjson"

/-! The fourteen non-internal `Init` constants whose names have a component
with a `.` inside it, and two definitions whose names differ only there. -/
def Std.«a.b» : Nat := 1
def Std.a.b : Nat := 2
theorem Std.ab_one : Std.«a.b» = 1 := rfl
theorem Std.ab_two : Std.a.b = 2 := rfl

#eval MiniExport.run [``Std.ab_one, ``Std.ab_two,
  `Std.«term_<...<_», `Std.«term_...*», `Std.«term_...<_», `Lean.«termMacro.trace[_]_»,
  `Std.«term_<...=_», `Std.«term_...=_», `Std.«term*...=_», `Std.«term_<..._»,
  `Std.«term*...*», `Std.«term_<...*», `Std.«term*...<_», `Std.«term_..._»,
  `Std.«term*..._», `Rat.«term_/._»] "init_dotted_names.ndjson"

/-! A nested occurrence through a dependent container whose family argument is
a lambda with a function-typed body. Lean builds the auxiliary constructor with
`instantiate_rev`, which does not beta-reduce, so the field stays the redex
`(fun _ => Nat → SGS) fst`, not a function type, and Lean stores
`isReflexive := false`. -/
inductive SGS where
  | mk : (Σ _ : Nat, Nat → SGS) → SGS

#eval MiniExport.run [``SGS] "sigma_const_nested.ndjson"

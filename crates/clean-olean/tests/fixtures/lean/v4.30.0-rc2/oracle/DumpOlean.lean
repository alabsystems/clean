/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

DumpOlean — the independent upstream oracle for `clean-olean`'s real-fixture
tests. It is run by the pinned Lean binary itself, so every byte it prints is
Lean's own reading of an artifact, never Clean's:

    lean --run DumpOlean.lean <part.olean> [<part.olean.server> <part.olean.private>] ...
    lean --run DumpOlean.lean --env <Module> [--search-path <dir>]... [--name <Name>]...

Raw mode reads every listed part with `Lean.readModuleDataParts` (consecutive
arguments `X.olean`, `X.olean.server`, `X.olean.private` form one call, in that
order, which is the only order the parts of one module may be read in) and
never frees a `CompactedRegion`, so every object stays valid until exit.

Env mode `importModules` the named module with `loadExts := true` and reports,
for each probed name, whether Lean's own `Meta.isInstanceCore` / `isClass`
consider it registered and whether the constant is present at all. Without
`--name` the probed names are the module's own `constNames`.

The JSON schema is documented in README.md beside this file and is fixed by the
Rust consumers (`tests/runtime_declarations.rs`, `src/expr/bvar_tests.rs`,
`src/region/parsed_name_tests.rs`, `src/import/load_parse/companion_extension_tests.rs`,
`src/import/load_register/instance_metadata_tests.rs`). Nat values are printed
as bare integer literals of arbitrary size (`Lean.JsonNumber` is exact), so a
`Name.num` component above `u64::MAX` reaches serde_json as a float and fails
`as_u64()` — the refusal predicate `parsed_name_tests.rs:327` relies on.
-/
import Lean
open Lean

namespace DumpOlean

/-! ## JSON helpers -/

def obj (fields : List (String × Json)) : Json := Json.mkObj fields
def jstr (s : String) : Json := Json.str s
def jbool (b : Bool) : Json := Json.bool b
def jnat (n : Nat) : Json := Json.num (JsonNumber.fromNat n)
def tag (t : String) : String × Json := ("tag", jstr t)

/-! ## Names, levels, expressions -/

/-- A `Name` is its component list, root first: `[{"kind":"str","value":s} | {"kind":"num","value":n}]`. -/
def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameComponents p).push (obj [("kind", jstr "str"), ("value", jstr s)])
  | .num p n => (nameComponents p).push (obj [("kind", jstr "num"), ("value", jnat n)])

def nameJson (n : Name) : Json := Json.arr (nameComponents n)
def namesJson (ns : List Name) : Json := Json.arr (ns.toArray.map nameJson)

def levelJson : Level → Json
  | .zero => obj [tag "zero"]
  | .succ l => obj [tag "succ", ("inner", levelJson l)]
  | .max a b => obj [tag "max", ("left", levelJson a), ("right", levelJson b)]
  | .imax a b => obj [tag "imax", ("left", levelJson a), ("right", levelJson b)]
  | .param n => obj [tag "param", ("name", nameJson n)]
  | .mvar id => obj [tag "mvar-unmeasured", ("name", nameJson id.name)]

def binderInfoNum : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- Kernel expression as a tagged tree. `binder_name` is informational; the
consumers compare `binder`, `type` and `body` only. -/
partial def exprJson : Expr → Json
  | .bvar i => obj [tag "bvar", ("index", jnat i)]
  | .fvar id => obj [tag "fvar-unmeasured", ("name", nameJson id.name)]
  | .mvar id => obj [tag "mvar-unmeasured", ("name", nameJson id.name)]
  | .sort l => obj [tag "sort", ("level", levelJson l)]
  | .const n us =>
    obj [tag "const", ("name", nameJson n), ("levels", Json.arr (us.toArray.map levelJson))]
  | .app f a => obj [tag "app", ("fun", exprJson f), ("arg", exprJson a)]
  | .lam n t b bi =>
    obj [tag "lam", ("binder", jnat (binderInfoNum bi)), ("binder_name", nameJson n),
         ("type", exprJson t), ("body", exprJson b)]
  | .forallE n t b bi =>
    obj [tag "pi", ("binder", jnat (binderInfoNum bi)), ("binder_name", nameJson n),
         ("type", exprJson t), ("body", exprJson b)]
  | .letE n t v b nondep =>
    obj [tag "let", ("name", nameJson n), ("type", exprJson t), ("value", exprJson v),
         ("body", exprJson b), ("nondep", jbool nondep)]
  | .lit (.natVal v) => obj [tag "nat", ("value", jnat v)]
  | .lit (.strVal s) => obj [tag "str", ("value", jstr s)]
  | .mdata _ e => obj [tag "mdata-unmeasured", ("value", exprJson e)]
  | .proj n i e => obj [tag "proj", ("name", nameJson n), ("index", jnat i), ("value", exprJson e)]

/-- Every constant a term names through `const` or `proj`, deduplicated, in
first-occurrence order. -/
partial def collectRefs (e : Expr) (acc : Array Name) : Array Name :=
  let add (acc : Array Name) (n : Name) : Array Name :=
    if acc.contains n then acc else acc.push n
  match e with
  | .const n _ => add acc n
  | .proj n _ s => collectRefs s (add acc n)
  | .app f a => collectRefs a (collectRefs f acc)
  | .lam _ t b _ => collectRefs b (collectRefs t acc)
  | .forallE _ t b _ => collectRefs b (collectRefs t acc)
  | .letE _ t v b _ => collectRefs b (collectRefs v (collectRefs t acc))
  | .mdata _ e => collectRefs e acc
  | _ => acc

def refsJson (e : Expr) : Json := Json.arr ((collectRefs e #[]).map nameJson)

/-! ## Constants -/

def kindString : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The value the artifact physically stores. Unlike `ConstantInfo.value?`
this includes theorems and opaques: the question is storage, not reducibility. -/
def storedValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def safetyString : DefinitionSafety → String
  | .safe => "safe"
  | .unsafe => "unsafe"
  | .partial => "partial"

def hintsJson : ReducibilityHints → Json
  | .opaque => obj [("kind", jstr "opaque")]
  | .abbrev => obj [("kind", jstr "abbrev")]
  | .regular h => obj [("kind", jstr "regular"), ("height", jnat h.toNat)]

def quotKindString : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def ruleJson (r : RecursorRule) : Json :=
  obj [("constructor", nameJson r.ctor), ("num_fields", jnat r.nfields), ("rhs", exprJson r.rhs)]

/-- Kind-specific metadata. Every kind that carries Lean's `all` list emits it
as `all`, because Clean's `mutual_declarations` is compared against it for
definitions, theorems and opaques as well as for inductive families. -/
def familyJson : ConstantInfo → Json
  | .axiomInfo v => obj [("is_unsafe", jbool v.isUnsafe)]
  | .defnInfo v =>
    obj [("all", namesJson v.all), ("safety", jstr (safetyString v.safety)), ("hints", hintsJson v.hints)]
  | .thmInfo v => obj [("all", namesJson v.all)]
  | .opaqueInfo v => obj [("all", namesJson v.all), ("is_unsafe", jbool v.isUnsafe)]
  | .quotInfo v => obj [("quot_kind", jstr (quotKindString v.kind))]
  | .inductInfo v =>
    obj [("all", namesJson v.all), ("constructors", namesJson v.ctors),
         ("num_params", jnat v.numParams), ("num_indices", jnat v.numIndices),
         ("num_nested", jnat v.numNested), ("is_recursive", jbool v.isRec),
         ("is_unsafe", jbool v.isUnsafe), ("is_reflexive", jbool v.isReflexive)]
  | .ctorInfo v =>
    obj [("inductive", nameJson v.induct), ("index", jnat v.cidx), ("num_params", jnat v.numParams),
         ("num_fields", jnat v.numFields), ("is_unsafe", jbool v.isUnsafe)]
  | .recInfo v =>
    obj [("all", namesJson v.all), ("num_params", jnat v.numParams), ("num_indices", jnat v.numIndices),
         ("num_motives", jnat v.numMotives), ("num_minors", jnat v.numMinors), ("k", jbool v.k),
         ("is_unsafe", jbool v.isUnsafe), ("rules", Json.arr (v.rules.toArray.map ruleJson))]

def constantJson (c : ConstantInfo) : Json :=
  let value? := storedValue? c
  obj [("name", nameJson c.name),
       ("kind", jstr (kindString c)),
       ("levels", namesJson c.levelParams),
       ("type_core", exprJson c.type),
       ("value_core", (value?.map exprJson).getD Json.null),
       -- Non-null exactly when a value is stored; carries Lean's structural hash
       -- of that value rather than a second copy of the term.
       ("value", (value?.map fun v => obj [("hash", jnat v.hash.toNat)]).getD Json.null),
       ("family", familyJson c),
       ("type_refs", refsJson c.type),
       ("value_refs", (value?.map refsJson).getD Json.null)]

/-! ## Environment-extension entries -/

def attrKindString : AttributeKind → String
  | .global => "global"
  | .local => "local"
  | .scoped => "scoped"

def scopeJson (scope? : Option Name) : Json := (scope?.map nameJson).getD Json.null

def instanceJson (v : Meta.InstanceEntry) (scope? : Option Name) : Json :=
  obj [("kind", jstr "instance"),
       ("name", nameJson (v.globalName?.getD .anonymous)),
       ("global_name_present", jbool v.globalName?.isSome),
       ("priority", jnat v.priority),
       ("attr_kind", jstr (attrKindString v.attrKind)),
       ("synth_order", Json.arr (v.synthOrder.map jnat)),
       ("scope", scopeJson scope?)]

def classJson (v : ClassEntry) : Json :=
  obj [("kind", jstr "class"), ("name", nameJson v.name), ("out_params", Json.arr (v.outParams.map jnat))]

def originJson : Meta.Origin → Json
  | .decl n post inv => obj [("kind", jstr "decl"), ("name", nameJson n), ("post", jbool post), ("inv", jbool inv)]
  | .fvar id => obj [("kind", jstr "fvar"), ("name", nameJson id.name)]
  | .stx id _ => obj [("kind", jstr "stx"), ("name", nameJson id)]
  | .other n => obj [("kind", jstr "other"), ("name", nameJson n)]

def simpJson (e : Meta.SimpEntry) (scope? : Option Name) : Json :=
  match e with
  | .thm t =>
    obj [("kind", jstr "theorem"), ("name", nameJson t.origin.key), ("priority", jnat t.priority),
         ("post", jbool t.post), ("perm", jbool t.perm), ("rfl", jbool t.rfl),
         ("origin", originJson t.origin), ("scope", scopeJson scope?)]
  | .toUnfold n => obj [("kind", jstr "to_unfold"), ("name", nameJson n), ("scope", scopeJson scope?)]
  | .toUnfoldThms n thms =>
    obj [("kind", jstr "to_unfold_theorems"), ("name", nameJson n),
         ("theorems", namesJson thms.toList), ("scope", scopeJson scope?)]

def aliasJson (e : AliasEntry) : Json :=
  obj [("kind", jstr "alias"), ("alias", nameJson e.1), ("target", nameJson e.2)]

/-- Decode the four extensions Clean types; every other extension's row is
`null` (present and counted, not decoded). The extension is identified by the
name Lean registered at runtime, never by a string literal. -/
unsafe def entryJsonImpl (extName : Name) (e : EnvExtensionEntry) : Json :=
  if extName == PersistentEnvExtension.name (ScopedEnvExtension.ext Meta.instanceExtension) then
    match (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry) with
    | .global v => instanceJson v none
    | .scoped ns v => instanceJson v (some ns)
  else if extName == PersistentEnvExtension.name classExtension then
    classJson (unsafeCast e)
  else if extName == PersistentEnvExtension.name (ScopedEnvExtension.ext Meta.simpExtension) then
    match (unsafeCast e : ScopedEnvExtension.Entry Meta.SimpEntry) with
    | .global v => simpJson v none
    | .scoped ns v => simpJson v (some ns)
  else if extName == PersistentEnvExtension.name aliasExtension then
    aliasJson (unsafeCast e)
  else
    Json.null

@[implemented_by entryJsonImpl]
opaque entryJson (extName : Name) (e : EnvExtensionEntry) : Json

def entriesJson (entries : Array (Name × Array EnvExtensionEntry)) : Json :=
  Json.arr <| entries.map fun p =>
    let extName := p.1
    let rows := p.2
    obj [("name", nameJson extName), ("count", jnat rows.size),
         ("rows", Json.arr (rows.map fun r => obj [("value", entryJson extName r)]))]

/-! ## Parts -/

def importJson (i : Import) : Json :=
  obj [("module", nameJson i.module), ("import_all", jbool i.importAll),
       ("is_exported", jbool i.isExported), ("is_meta", jbool i.isMeta)]

def partJson (path : String) (md : ModuleData) : Json :=
  obj [("path", jstr path),
       ("is_module", jbool md.isModule),
       ("imports", Json.arr (md.imports.map importJson)),
       ("constants", Json.arr (md.constants.map constantJson)),
       ("entries", entriesJson md.entries),
       ("const_names", Json.arr (md.constNames.map nameJson)),
       ("extra_const_names", Json.arr (md.extraConstNames.map nameJson))]

/-- Consecutive `X.olean`, `X.olean.server`, `X.olean.private` arguments are
the parts of one module and must be read by one `readModuleDataParts` call. -/
def groupParts (paths : List String) : List (List String) :=
  let step (groups : List (List String)) (p : String) : List (List String) :=
    match groups with
    | (base :: rest) :: older =>
      if p == base ++ ".server" || p == base ++ ".private" then
        (base :: rest ++ [p]) :: older
      else
        [p] :: (base :: rest) :: older
    | _ => [p] :: groups
  (paths.foldl step []).reverse

def dumpRaw (paths : List String) : IO Json := do
  let mut parts : Array Json := #[]
  -- Regions are deliberately retained for the life of the process; nothing
  -- here calls `CompactedRegion.free`, so every ModuleData stays readable.
  let mut regions : Array CompactedRegion := #[]
  for group in groupParts paths do
    let loaded ← readModuleDataParts (group.toArray.map System.FilePath.mk)
    unless loaded.size == group.length do
      throw <| IO.userError s!"readModuleDataParts returned {loaded.size} parts for {group}"
    for (path, part) in group.zip loaded.toList do
      regions := regions.push part.2
      parts := parts.push (partJson path part.1)
  return obj [("parts", Json.arr parts), ("regions_kept", jnat regions.size)]

/-! ## Environment mode -/

@[implemented_by Lean.enableInitializersExecution]
opaque enableInit : IO Unit

/-- `A.B.«c.d».7` → `A.B.«c.d».7` with `«»` protecting dots and an unquoted
all-digit component read as `Name.num`. -/
def parseName (s : String) : Name :=
  let flush (acc : Name) (cur : String) (quoted : Bool) : Name :=
    if cur.isEmpty && !quoted then acc
    else if !quoted && cur.all Char.isDigit then acc.num cur.toNat!
    else acc.str cur
  let step (st : Name × String × Bool × Bool) (c : Char) : Name × String × Bool × Bool :=
    let (acc, cur, inQuote, quoted) := st
    if inQuote then
      if c == '»' then (acc, cur, false, true) else (acc, cur.push c, true, quoted)
    else if c == '«' then (acc, cur, true, true)
    else if c == '.' then (flush acc cur quoted, "", false, false)
    else (acc, cur.push c, false, quoted)
  let (acc, cur, _, quoted) := s.toList.foldl step (Name.anonymous, "", false, false)
  flush acc cur quoted

structure EnvArgs where
  module? : Option String := none
  searchPaths : List System.FilePath := []
  names : List Name := []

def parseEnvArgs : List String → EnvArgs → Except String EnvArgs
  | [], acc => .ok acc
  | "--env" :: m :: rest, acc => parseEnvArgs rest { acc with module? := some m }
  | "--search-path" :: d :: rest, acc => parseEnvArgs rest { acc with searchPaths := acc.searchPaths ++ [⟨d⟩] }
  | "--name" :: n :: rest, acc => parseEnvArgs rest { acc with names := acc.names ++ [parseName n] }
  | other :: _, _ => .error s!"unexpected env-mode argument '{other}'"

def dumpEnv (args : EnvArgs) : IO Json := do
  let some moduleText := args.module? | throw <| IO.userError "--env requires a module name"
  let modName := parseName moduleText
  let app ← IO.appPath
  let some binDir := app.parent | throw <| IO.userError s!"lean binary has no parent: {app}"
  let some sysroot := binDir.parent | throw <| IO.userError s!"lean bin dir has no parent: {binDir}"
  initSearchPath sysroot args.searchPaths
  enableInit
  let env ← importModules #[{ module := modName }] {} (loadExts := true)
  let names ← if args.names.isEmpty then do
      let path ← findOLean modName
      let (md, _region) ← readModuleData path
      pure md.constNames.toList
    else
      pure args.names
  let rows := names.toArray.map fun n =>
    obj [("name", nameJson n), ("is_instance", jbool (Meta.isInstanceCore env n)),
         ("constant_present", jbool (env.contains n))]
  let classes := names.toArray.map fun n =>
    obj [("name", nameJson n), ("is_class", jbool (isClass env n)),
         ("constant_present", jbool (env.contains n))]
  return obj [("module", nameJson modName), ("rows", Json.arr rows), ("classes", Json.arr classes)]

def usage : String :=
  "usage:\n  lean --run DumpOlean.lean <part.olean> [<part.olean.server> <part.olean.private>] ...\n" ++
  "  lean --run DumpOlean.lean --env <Module> [--search-path <dir>]... [--name <Name>]..."

end DumpOlean

open DumpOlean in
def main (args : List String) : IO UInt32 := do
  try
    let json ← match args with
      | [] => throw <| IO.userError usage
      | "--env" :: _ =>
        match parseEnvArgs args {} with
        | .ok parsed => dumpEnv parsed
        | .error e => throw <| IO.userError s!"{e}\n{usage}"
      | paths => dumpRaw paths
    IO.println json.pretty
    return 0
  catch e =>
    IO.eprintln s!"DumpOlean: {e}"
    return 1

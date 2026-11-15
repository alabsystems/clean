import Lean
/-!
# InspectCompanionProbe — the measuring instrument for fixture [F7]

NOT a fixture module (it is not listed in `../ORDER` and is never compiled to an
`.olean`). Run it with the pinned toolchain against the compiled triple, cwd =
the family directory:

```
$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --run \
  tools/InspectCompanionProbe.lean \
  CompanionProbe.olean CompanionProbe.olean.server CompanionProbe.olean.private
```

It prints ONE JSON document to stdout. The parts are read with
`Lean.readModuleDataParts` over the whole prefix at once, because a later part
shares objects with the earlier ones and cannot be read on its own
(`Lean/Environment.lean:1740-1745`).

Per part it reports:

* `constants`: every `ConstantInfo` in `ModuleData.constants` with its kind and
  whether a value is stored (the module system erases private bodies from the
  exported/server parts, so the same name can be a value-less stub in one part
  and a body-carrying declaration in another);
* `entries`: every persistent extension Lean wrote, in `ModuleData.entries`
  order, with its row count. For the four extensions Clean decodes
  (`crates/clean-olean/src/module/typed_extensions/decode.rs:33-41` —
  `Lean.Meta.instanceExtension`, `Lean.classExtension`,
  `Lean.Meta.simpExtension`, `Lean.aliasExtension`) every row is decoded by
  `unsafeCast` to Lean's OWN entry type and printed under the oracle [O] value
  shape (`{"kind": "instance"|"class"|"theorem"|"alias", "name"|"alias", "priority"}`
  plus extra measured fields); rows of every other extension are `null`;
* `recognized`: the number of decoded rows across the four extensions — the
  figure `companion_extension_tests.rs:122` pins per part as `[5, 5, 7]`.

Names are printed twice: as `Name.toString` (escaped, human-readable) and as the
oracle's component list `[{"kind": "str"|"num", "value": ...}]`.
-/
open Lean

partial def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameComponents p).push (Json.mkObj [("kind", "str"), ("value", s)])
  | .num p n => (nameComponents p).push (Json.mkObj [("kind", "num"), ("value", toJson n)])

def nameJson (n : Name) : Json :=
  Json.mkObj [("string", toString n), ("components", Json.arr (nameComponents n))]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- `hasValue (allowOpaque := true)`: `ConstantInfo.value?` alone answers `none`
for every theorem and opaque (`Lean/Declaration.lean:482-487`), which would
misreport a proof-carrying theorem as value-less. -/
def constantJson (ci : ConstantInfo) : Json :=
  Json.mkObj [
    ("name", nameJson ci.name),
    ("kind", kindOf ci),
    ("has_value", toJson (ci.hasValue (allowOpaque := true)))
  ]

/-- One `ModuleData.imports` row with its three module-system flags
(`Lean/Setup.lean`, `structure Import`). -/
def importJson (i : Import) : Json :=
  Json.mkObj [
    ("module", nameJson i.module),
    ("import_all", toJson i.importAll),
    ("is_exported", toJson i.isExported),
    ("is_meta", toJson i.isMeta)
  ]

def attrKindString : AttributeKind → String
  | .global => "global"
  | .local => "local"
  | .scoped => "scoped"

def scopeOf : ScopedEnvExtension.Entry α → Option Name × α
  | .global a => (none, a)
  | .scoped ns a => (some ns, a)

def optNameJson : Option Name → Json
  | none => Json.null
  | some n => nameJson n

unsafe def instanceRow (e : EnvExtensionEntry) : Json :=
  let (scope, ie) := scopeOf (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry)
  Json.mkObj [
    ("kind", "instance"),
    ("name", optNameJson ie.globalName?),
    ("priority", toJson ie.priority),
    ("attr_kind", attrKindString ie.attrKind),
    ("scope", optNameJson scope),
    ("synth_order", toJson ie.synthOrder),
    ("key_count", toJson ie.keys.size)
  ]

unsafe def classRow (e : EnvExtensionEntry) : Json :=
  let ce : ClassEntry := unsafeCast e
  Json.mkObj [
    ("kind", "class"),
    ("name", nameJson ce.name),
    ("out_params", toJson ce.outParams),
    ("out_level_params", toJson ce.outLevelParams)
  ]

unsafe def simpRow (e : EnvExtensionEntry) : Json :=
  let (scope, se) := scopeOf (unsafeCast e : ScopedEnvExtension.Entry Meta.SimpEntry)
  match se with
  | .thm t =>
    let (origin, post, inv) : Json × Bool × Bool := match t.origin with
      | .decl n post inv => (nameJson n, post, inv)
      | .fvar _ => ("fvar", true, false)
      | .stx _ _ => ("stx", true, false)
      | .other _ => ("other", true, false)
    Json.mkObj [
      ("kind", "theorem"),
      ("constructor", "thm"),
      ("name", origin),
      ("priority", toJson t.priority),
      ("post", toJson t.post),
      ("origin_post", toJson post),
      ("origin_inv", toJson inv),
      ("perm", toJson t.perm),
      ("rfl", toJson t.rfl),
      ("scope", optNameJson scope)
    ]
  | .toUnfold n =>
    Json.mkObj [("kind", "theorem"), ("constructor", "toUnfold"), ("name", nameJson n),
      ("priority", toJson (1000 : Nat)), ("scope", optNameJson scope)]
  | .toUnfoldThms n thms =>
    Json.mkObj [("kind", "theorem"), ("constructor", "toUnfoldThms"), ("name", nameJson n),
      ("priority", toJson (1000 : Nat)), ("equation_lemmas", Json.arr (thms.map nameJson)),
      ("scope", optNameJson scope)]

unsafe def aliasRow (e : EnvExtensionEntry) : Json :=
  let (a, target) : AliasEntry := unsafeCast e
  Json.mkObj [("kind", "alias"), ("alias", nameJson a), ("target", nameJson target)]

unsafe def decodeRow (ext : Name) (e : EnvExtensionEntry) : Option Json :=
  if ext == ``Lean.Meta.instanceExtension then some (instanceRow e)
  else if ext == ``Lean.classExtension then some (classRow e)
  else if ext == ``Lean.Meta.simpExtension then some (simpRow e)
  else if ext == ``Lean.aliasExtension then some (aliasRow e)
  else none

unsafe def partJson (file : System.FilePath) (md : ModuleData) : Json := Id.run do
  let mut recognized := 0
  let mut entries := #[]
  for (ext, rows) in md.entries do
    let decoded := rows.map (decodeRow ext)
    recognized := recognized + (decoded.filter Option.isSome).size
    entries := entries.push <| Json.mkObj [
      ("name", nameJson ext),
      ("count", toJson rows.size),
      ("rows", Json.arr (decoded.map fun r => match r with
        | some j => Json.mkObj [("value", j)]
        | none => Json.null))
    ]
  return Json.mkObj [
    ("file", toString file),
    ("is_module", toJson md.isModule),
    ("imports", Json.arr (md.imports.map importJson)),
    ("constant_count", toJson md.constants.size),
    ("const_names_count", toJson md.constNames.size),
    ("extra_const_names", Json.arr (md.extraConstNames.map nameJson)),
    ("constants", Json.arr (md.constants.map constantJson)),
    ("entry_count", toJson md.entries.size),
    ("row_total", toJson (md.entries.foldl (fun acc (_, rows) => acc + rows.size) 0)),
    ("recognized", toJson recognized),
    ("entries", Json.arr entries)
  ]

unsafe def inspect (paths : Array System.FilePath) : IO Unit := do
  -- Keep every CompactedRegion alive for the duration: the returned ModuleData
  -- points into them.
  let parts ← readModuleDataParts paths
  let mut out := #[]
  for h : i in [0:parts.size] do
    let (md, _region) := parts[i]
    out := out.push (partJson paths[i]! md)
  IO.println (Json.mkObj [
    ("lean_version", Lean.versionString),
    ("parts", Json.arr out)
  ]).pretty

unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then
    throw <| IO.userError
      "usage: lean --run tools/InspectCompanionProbe.lean <base.olean> [<.olean.server> [<.olean.private>]]"
  inspect (args.toArray.map System.FilePath.mk)

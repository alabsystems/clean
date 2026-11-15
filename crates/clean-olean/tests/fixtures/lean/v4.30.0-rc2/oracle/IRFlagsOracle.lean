import Lean
open Lean IR

/-!
# IR flag oracle (pinned Lean side)

Counts, over the transitive import closure of `IR_FLAGS_ROOTS`, the IR data
Lean's `IR.Decl` formatter never prints — so the census's byte-exact
declaration diff cannot see them — in the keys of `clean olean ir-census
--profile`:

* `instr_inc` / `instr_dec` and, over both, `rc_known_object` (`c = false`),
  `rc_persistent` (`persistent = true`) and `rc_count_not_one` (`n ≠ 1`);
* `param_borrowed` — borrowed parameters of `fdecl`s;
* `expr_ctor_args_differ_from_size` — `ctor` expressions whose argument count
  differs from `CtorInfo.size`;
* `distinct_case_types` — distinct `case` type ids (`tid`).

Declarations are read as the census reads them: `getModuleEntries`, plus
`getModuleIREntries` for a `module` file (for a non-`module` file both are
the same array). Consumers insert the roots as `import` lines directly after
`import Lean`. Output: one `FLAGS k=v …` line on stdout.
-/

namespace IRFlagsOracle

structure Counts where
  inc : Nat := 0
  dec : Nat := 0
  known : Nat := 0
  persistent : Nat := 0
  notOne : Nat := 0
  borrowed : Nat := 0
  ctorSize : Nat := 0
  tids : Std.HashSet Name := {}

def rc (a : Counts) (isInc : Bool) (n : Nat) (c p : Bool) : Counts :=
  { a with
    inc := a.inc + (if isInc then 1 else 0)
    dec := a.dec + (if isInc then 0 else 1)
    known := a.known + (if c then 0 else 1)
    persistent := a.persistent + (if p then 1 else 0)
    notOne := a.notOne + (if n != 1 then 1 else 0) }

partial def walk (b : FnBody) (a : Counts) : Counts :=
  match b with
  | .inc _ n c p k => walk k (rc a true n c p)
  | .dec _ n c p k => walk k (rc a false n c p)
  | .jdecl _ _ v k => walk k (walk v a)
  | .vdecl _ _ (.ctor i ys) k =>
    walk k { a with ctorSize := a.ctorSize + (if ys.size != i.size then 1 else 0) }
  | .case tid _ _ alts =>
    alts.foldl (fun a alt => walk alt.body a) { a with tids := a.tids.insert tid }
  | other => if other.isTerminal then a else walk other.body a

def closure (env : Environment) (roots : List Name) : IO (Array Nat) := do
  let names := env.header.moduleNames
  let mut idxOf : Std.HashMap Name Nat := {}
  for i in [0:names.size] do
    idxOf := idxOf.insert names[i]! i
  let mut seen : Std.HashSet Nat := {}
  let mut work : Array Nat := #[]
  for r in roots do
    match idxOf[r]? with
    | some i => work := work.push i
    | none => throw <| IO.userError s!"root module {r} is not in the environment"
  while !work.isEmpty do
    let i := work.back!
    work := work.pop
    if seen.contains i then continue
    seen := seen.insert i
    for imp in env.header.moduleData[i]!.imports do
      if let some j := idxOf[imp.module]? then work := work.push j
  return seen.toArray

def main : CoreM Unit := do
  let env ← getEnv
  let roots := ((← IO.getEnv "IR_FLAGS_ROOTS").getD "").splitOn "," |>.filter (!·.isEmpty)
    |>.map String.toName
  let idxs ← closure env roots
  let mut a : Counts := {}
  for i in idxs do
    let levels := if env.header.moduleData[i]!.isModule then
        [declMapExt.getModuleEntries env i, declMapExt.getModuleIREntries env i]
      else [declMapExt.getModuleEntries env i]
    for ds in levels do
      for d in ds do
        if let .fdecl _ xs _ b _ := d then
          a := walk b { a with borrowed := a.borrowed + (xs.filter (·.borrow)).size }
  IO.println s!"FLAGS modules={idxs.size} instr_inc={a.inc} instr_dec={a.dec} \
    rc_known_object={a.known} rc_persistent={a.persistent} rc_count_not_one={a.notOne} \
    param_borrowed={a.borrowed} expr_ctor_args_differ_from_size={a.ctorSize} \
    distinct_case_types={a.tids.size}"

end IRFlagsOracle

#eval IRFlagsOracle.main

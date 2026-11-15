import Lean
open Lean

/-! Pinned Lean's KERNEL verdict on `Sort a ≡ Sort b` for each `a<TAB>b` line of the input:
`def t.{u,v,w} : Sort a → Sort b := fun x => x` is admitted iff the kernel's `is_def_eq` on the
two sorts holds, i.e. `is_equivalent(a, b)` (type_checker.cpp:719-725). Levels are built with
the RAW constructors (`Level.max`/`Level.imax`), so the kernel sees exactly the encoded tree. -/

partial def parse : List Char → Except String (Level × List Char)
  | 'Z' :: r => return (.zero, r)
  | 'P' :: '(' :: r =>
    let n := r.takeWhile (· != ')')
    return (.param (String.ofList n).toName, r.drop (n.length + 1))
  | 'S' :: '(' :: r => do
    let (a, r) ← parse r
    return (.succ a, r.drop 1)
  | c :: '(' :: r => do
    let mk : Level → Level → Level ← if c == 'M' then pure Level.max
      else if c == 'I' then pure Level.imax else throw s!"bad level head {c}"
    let (a, r) ← parse r
    let (b, r) ← parse (r.drop 1)
    return (mk a b, r.drop 1)
  | r => throw s!"bad level {String.ofList r}"

def idDecl (i : Nat) (a b : Level) : Declaration :=
  .defnDecl { name := .num `t i, levelParams := [`u, `v, `w],
              type := mkForall `x .default (.sort a) (.sort b),
              value := mkLambda `x .default (.sort a) (.bvar 0),
              hints := .opaque, safety := .safe }

def main (args : List String) : IO UInt32 := do
  let [inp] := args | IO.eprintln "usage: KernelLevelVerdicts <pairs.tsv>"; return 2
  let some sysroot := (← IO.appDir).parent | return 2
  initSearchPath sysroot
  let env ← importModules #[{ module := `Init.Prelude }] {} (trustLevel := 0)
  IO.println s!"# lean {Lean.versionString}"
  let mut i := 0
  for line in (← IO.FS.lines inp) do
    match line.splitOn "\t" with
    | [ea, eb] =>
      match parse ea.toList, parse eb.toList with
      | .ok (a, _), .ok (b, _) =>
        let ok := (env.addDeclCore 0 (idDecl i a b) none (doCheck := true)) matches .ok _
        IO.println s!"{ea}\t{eb}\t{if ok then "ACCEPT" else "REJECT"}"
      | _, _ => IO.eprintln s!"unparsable: {line}"; return 1
    | _ => pure ()
    i := i + 1
  return 0

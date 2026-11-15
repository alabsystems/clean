import Lean
open Lean

/-! Pinned Lean's KERNEL verdict on each declaration that
`crates/clean-ck0/tests/level_as_written.rs` pins (`docs/DECISIONS.md` R174, R177). Each is handed
to `Environment.addDeclCore` with `doCheck := true`, so the kernel alone decides, on levels built
with the raw constructors (`Level.succ`, `Level.max`, `Level.imax`): the elaborator never sees
them. -/

def u : Level := .param `u
def v : Level := .param `v

def ind (n : Name) (lps : List Name) (np : Nat) (ty : Expr) (ctorTy : Expr) : Declaration :=
  .inductDecl lps np [{ name := n, type := ty, ctors := [{ name := n ++ `mk, type := ctorTy }] }] false

/-- `p : Sort l`, an axiom, then `∀ h1 h2 : p, h1 = h2 := fun h1 h2 => rfl`, which holds by
proof irrelevance only. -/
def irrel (p : Name) (l : Level) : List Declaration :=
  let pc := Expr.const p []
  let eqTy := mkApp3 (.const ``Eq [l]) pc (.bvar 1) (.bvar 0)
  [.axiomDecl { name := p, levelParams := [], type := .sort l, isUnsafe := false },
   .thmDecl { name := p ++ `irr, levelParams := [], type := .forallE `h1 pc (.forallE `h2 pc eqTy .default) .default,
              value := .lam `h1 pc (.lam `h2 pc (mkApp2 (.const ``Eq.refl [l]) pc (.bvar 1)) .default) .default }]

def w : Level := .param `w

/-- `succ (imax w r)`, over `u, v, w`. -/
def succImax (r : Level) : Level := .succ (.imax w r)

/-- `b.{u,v,w} : Sort (succImax r + 1) := Sort (succImax r)`, then
`t : Sort (succ (max u v)) → b.{u, v, max u v} := fun x => x`: the kernel
unfolds `b` at `w := max u v` and compares the two sorts. -/
def instDefEq (b : Name) (r : Level) : List Declaration :=
  let lhs := Expr.sort (.succ (.max u v))
  [.defnDecl { name := b, levelParams := [`u, `v, `w], type := .sort (.succ (succImax r)),
               value := .sort (succImax r), hints := .regular 0, safety := .safe },
   .defnDecl { name := b ++ `t, levelParams := [`u, `v], type := .forallE `x lhs (.const b [u, v, .max u v]) .default,
               value := .lam `x lhs (.bvar 0) .default, hints := .opaque, safety := .safe }]

/-- `g.{u,v,w} : Sort (succImax r)`, an axiom, then
`inductive g.I.{u,v} : Sort (succ (max u v))` with `mk : g.{u, v, max u v} → g.I`:
the kernel checks the result level against the field's, `succImax r` at
`w := max u v`. -/
def instGeq (g : Name) (r : Level) : List Declaration :=
  [.axiomDecl { name := g, levelParams := [`u, `v, `w], type := .sort (succImax r), isUnsafe := false },
   ind (g ++ `I) [`u, `v] 0 (.sort (.succ (.max u v)))
     (.forallE `x (.const g [u, v, .max u v]) (.const (g ++ `I) [u, v]) .default)]

/-- `n.{u,v} (α : Sort u) : Sort r` with `mk : α → n α`: the kernel checks `r`
against `u`. -/
def fieldU (n : Name) (r : Level) : Declaration :=
  ind n [`u, `v] 1 (.forallE `α (.sort u) (.sort r) .default)
    (.forallE `α (.sort u) (.forallE `a (.bvar 0) (mkApp (.const n [u, v]) (.bvar 1)) .default) .default)

/-- `n.{u,v} : Sort ty := Sort (max (u+1) (v+1))`: the kernel compares `ty`
with the value's type, `Sort (max (u+1) (v+1) + 1)`. -/
def defMaxSucc (n : Name) (ty : Level) : Declaration :=
  .defnDecl { name := n, levelParams := [`u, `v], type := .sort ty,
              value := .sort (.max (.succ u) (.succ v)), hints := .opaque, safety := .safe }

/-- `imax a (max u v)`. -/
def imaxMax (a : Level) : Level := .imax a (.max u v)

/-- `succ (imax a (max u v))`. -/
def succImaxMax (a : Level) : Level := .succ (imaxMax a)

/-- `n.{u,v} : Sort (succ (max u v))` with `mk : Sort l → n`: the field's level
is the `succ l` the kernel builds typing `Sort l`. -/
def fieldSort (n : Name) (l : Level) : Declaration :=
  ind n [`u, `v] 0 (.sort (.succ (.max u v))) (.forallE `x (.sort l) (.const n [u, v]) .default)

/-- `n.{u,v} : Sort (succ (max u v)) := Sort l`: the kernel compares
`succ (max u v)` with the `succ l` it builds typing `Sort l`. -/
def defSort (n : Name) (l : Level) : Declaration :=
  .defnDecl { name := n, levelParams := [`u, `v], type := .sort (.succ (.max u v)),
              value := .sort l, hints := .opaque, safety := .safe }

/-- `(α : Sort u) (β : Sort v)` around `body`. -/
def overUV (body : Expr) : Expr := .forallE `α (.sort u) (.forallE `β (.sort v) body .default) .default

def cases : List (String × List Declaration) := [
  -- R174's `S`, field `α → β` at `imax u v`, under `Sort (imax u v + 1)`; and over `max u v`.
  ("S imax u v + 1, field alpha -> beta",
    [ind `Sa [`u, `v] 2 (overUV (.sort (.succ (.imax u v))))
      (overUV (.forallE `f (.forallE `x (.bvar 1) (.bvar 1) .default) (mkApp2 (.const `Sa [u, v]) (.bvar 2) (.bvar 1)) .default))]),
  ("S max u v + 1, field alpha -> beta",
    [ind `Sm [`u, `v] 2 (overUV (.sort (.succ (.max u v))))
      (overUV (.forallE `f (.forallE `x (.bvar 1) (.bvar 1) .default) (mkApp2 (.const `Sm [u, v]) (.bvar 2) (.bvar 1)) .default))]),
  ("T imax u (v+1) + 1, field Sort (v+1)",
    [ind `T1 [`u, `v] 0 (.sort (.succ (.imax u (.succ v))))
      (.forallE `x (.sort (.succ v)) (.const `T1 [u, v]) .default)]),
  ("T imax u (v+1) + 1, field Sort (imax u v)",
    [ind `T2 [`u, `v] 0 (.sort (.succ (.imax u (.succ v))))
      (.forallE `x (.sort (.imax u v)) (.const `T2 [u, v]) .default)]),
  ("def : Sort (imax u (v+1) + 2) := Sort (max u (v+1) + 1)",
    [.defnDecl { name := `d1, levelParams := [`u, `v], type := .sort (.succ (.succ (.imax u (.succ v)))),
                 value := .sort (.succ (.max u (.succ v))), hints := .opaque, safety := .safe }]),
  ("def : Sort (max u (v+1) + 2) := Sort (max u (v+1) + 1)",
    [.defnDecl { name := `d2, levelParams := [`u, `v], type := .sort (.succ (.succ (.max u (.succ v)))),
                 value := .sort (.succ (.max u (.succ v))), hints := .opaque, safety := .safe }]),
  ("P Sort (imax u 0), field Type",
    [ind `P1 [`u] 0 (.sort (.imax u .zero)) (.forallE `x (.sort (.succ .zero)) (.const `P1 [u]) .default)]),
  ("P Prop, field Type",
    [ind `P2 [] 0 (.sort .zero) (.forallE `x (.sort (.succ .zero)) (.const `P2 []) .default)]),
  ("proof irrelevance at Sort 0", irrel `p0 .zero),
  ("proof irrelevance at Sort (max 0 0)", irrel `pmax (.max .zero .zero)),
  ("proof irrelevance at Sort (imax 0 0)", irrel `pimax (.imax .zero .zero)),
  -- R177's instantiation residue: `succ (imax w r)` at `w := max u v`, `r` written
  -- `max v u` (the residue) or `max u v` (its control), against `succ (max u v)`.
  ("def-eq at w := max u v, rhs max v u", instDefEq `B1 (.max v u)),
  ("def-eq at w := max u v, rhs max u v", instDefEq `B2 (.max u v)),
  ("universe check at w := max u v, rhs max v u", instGeq `G1 (.max v u)),
  ("universe check at w := max u v, rhs max u v", instGeq `G2 (.max u v)),
  -- R177's third form as written: `succ (imax a (max u v))`, whose `imax` Lean's
  -- `mk_imax` reduces to `max u v` for each `a` here, against `succ (max u v)`.
  ("C universe check, a = 0", [fieldU `Cg1 (succImaxMax .zero)]),
  ("C universe check, a = 1", [fieldU `Cg2 (succImaxMax (.succ .zero))]),
  ("C universe check, a = max u v", [fieldU `Cg3 (succImaxMax (.max u v))]),
  ("C universe check, a = max v u", [fieldU `Cg4 (succImaxMax (.max v u))]),
  ("C universe check, control succ (max u v)", [fieldU `Cg5 (.succ (.max u v))]),
  ("C def-eq, a = 0", [defMaxSucc `Cd1 (.succ (succImaxMax .zero))]),
  ("C def-eq, a = 1", [defMaxSucc `Cd2 (.succ (succImaxMax (.succ .zero)))]),
  ("C def-eq, a = max u v", [defMaxSucc `Cd3 (.succ (succImaxMax (.max u v)))]),
  ("C def-eq, a = max v u", [defMaxSucc `Cd4 (.succ (succImaxMax (.max v u)))]),
  ("C def-eq, control succ (succ (max u v))", [defMaxSucc `Cd5 (.succ (.succ (.max u v)))]),
  -- The same `imax`, with no `succ` written: the kernel's own, typing `Sort l`.
  ("C typed sort, universe check, a = 0", [fieldSort `Kg1 (imaxMax .zero)]),
  ("C typed sort, universe check, a = 1", [fieldSort `Kg2 (imaxMax (.succ .zero))]),
  ("C typed sort, universe check, a = max u v", [fieldSort `Kg3 (imaxMax (.max u v))]),
  ("C typed sort, universe check, a = max v u", [fieldSort `Kg4 (imaxMax (.max v u))]),
  ("C typed sort, universe check, control max u v", [fieldSort `Kg5 (.max u v)]),
  ("C typed sort, def-eq, a = 0", [defSort `Kd1 (imaxMax .zero)]),
  ("C typed sort, def-eq, a = 1", [defSort `Kd2 (imaxMax (.succ .zero))]),
  ("C typed sort, def-eq, a = max u v", [defSort `Kd3 (imaxMax (.max u v))]),
  ("C typed sort, def-eq, a = max v u", [defSort `Kd4 (imaxMax (.max v u))]),
  ("C typed sort, def-eq, control max u v", [defSort `Kd5 (.max u v)])
]

def main : IO UInt32 := do
  let some sysroot := (← IO.appDir).parent | return 2
  initSearchPath sysroot
  let env ← importModules #[{ module := `Init.Prelude }] {} (trustLevel := 0)
  IO.println s!"# lean {Lean.versionString}"
  for (tag, decls) in cases do
    let mut e := env
    let mut verdict := "ACCEPT"
    for d in decls do
      match e.addDeclCore 0 d none (doCheck := true) with
      | .ok e' => e := e'
      | .error err =>
        verdict := s!"REJECT {(← (err.toMessageData {}).toString).replace "\n" " "}"
        break
    IO.println s!"{tag}\t{verdict}"
  return 0

-- p24 — CLASS I, FRONTIER STAGE I-2: the GOAL side, with the built-in
-- `decEq` bridge removed from the picture.
--
-- PROVES: a Pi-shaped instance goal is now solved by BUILDING the function.
-- `MyDEq` is a `def`-based class alias that the elaborator δ-unfolds before
-- instance search ever sees it, so what arrives is
-- `(x y : Nat) → MyD (Eq Nat x y)` — a Pi, with no class application to
-- extract and NO local of that type in scope. Stage I-1's candidate-side
-- match cannot answer it (there is nothing to match against), and the answer
-- is not a binder: it is `fun x y => natMyD x y`.
--
-- Nothing built in is involved. `infer/instance.rs` carries a hand-written
-- bridge for exactly one shape — `Decidable (@Eq α a b)` delegating to
-- `DecidableEq α` — and p18 runs through it. The class, the alias and the
-- instance here are all user-declared, so the only route to `useNat` is
-- `resolve_pi_goal_by_abstraction`.
--
-- `depUse` is the dependent half. `DepAlias`'s SECOND binder type mentions
-- its FIRST binder (`(x : α) → (y : x = x) → …`), so the lambda can only be
-- built if abstraction reaches into binder types as well as into the body.
-- An implementation that abstracted the conclusion alone would emit
-- `fun (x : α) (y : Eq α x x) => …` with `x` still loose inside the second
-- binder's type, and the kernel would reject the declaration with
-- "contains free variables".
--
-- IN-FILE CONTROL (`bodyIsSolvable`): the Pi's BODY — `MyD (a = b)` at `Nat`
-- — resolves from the global table on its own, before this stage and after.
-- So what p24 measures is the ABSTRACTION, not the body and not `natMyD`.
--
-- CONTROL: p25 — the refusal half. The same shape whose body is solvable at
-- only ONE argument is still refused, so this pass is evidence for an
-- ARBITRARY argument rather than a grab. p26 — the arity half.
--
-- MEASURED at HEAD 69f4f4a70 (stage I-1, before this stage): `useNat` fails
-- `FailedToSynthesizeInstance { goal: "(n : Nat) -> (n1 : Nat) -> MyD (Eq {1}
-- Nat n n1)" }` and `depUse` fails `ResidualFreeVariables … unsolved
-- metavariables ?[0]`; the other three declarations pass.
class MyD (p : Prop) where
  ev : Nat

def MyDEq (α : Type) : Type := (x : α) → (y : α) → MyD (x = y)

instance natMyD (a b : Nat) : MyD (a = b) := ⟨0⟩

instance reflMyD (α : Type) (a : α) : MyD (a = a) := ⟨1⟩

def callee {α : Type} [MyDEq α] (a : α) : Nat := 0

def bodyIsSolvable (a b : Nat) : Nat := (inferInstance : MyD (a = b)).ev

def useNat (a : Nat) : Nat := callee a

def DepAlias (α : Type) : Type := (x : α) → (y : x = x) → MyD (x = x)

def depCallee (α : Type) [DepAlias α] (z : α) : Nat := 0

def depUse (z : Nat) : Nat := depCallee Nat z

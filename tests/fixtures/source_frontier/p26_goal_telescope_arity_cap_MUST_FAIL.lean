-- p26 — CLASS I, FRONTIER STAGE I-2: the arity cap is a REFUSAL, never a
-- truncation.
--
-- PROVES: `MAX_GOAL_TELESCOPE` (8, `infer/instance.rs`) bounds how deep a
-- Pi-shaped goal may be opened, and a goal deeper than that is refused whole.
-- The alternative failure mode is the dangerous one: an implementation that
-- opened the first eight binders and then matched the ninth Pi as if it were
-- the conclusion would build a lambda of the WRONG ARITY — a term of type
-- `α → … → (α → MyD (a = a))` handed to a caller expecting nine arguments'
-- worth of function. The cap exists so a pathological alias cannot turn a
-- failure path into an unbounded walk; it must not buy that bound by
-- emitting a term.
--
-- IN-FILE CONTROL (`useNarrow`): the SAME alias shape, the same class, the
-- same global instance, at two binders instead of nine — passes. So what is
-- refused below is the arity and nothing else: not `MyD`, not `reflMyD`, not
-- the `def`-based alias, not the goal-side telescope itself.
--
-- CONTROL: p24 — the capability this cap bounds.
class MyD (p : Prop) where
  ev : Nat

instance reflMyD (α : Type) (a : α) : MyD (a = a) := ⟨1⟩

def Narrow (α : Type) : Type := (a : α) → (b : α) → MyD (a = a)

def Wide (α : Type) : Type :=
  (a : α) → (b : α) → (c : α) → (d : α) → (e : α) → (f : α) → (g : α) → (h : α) → (i : α) →
    MyD (a = a)

def narrowCallee (α : Type) [Narrow α] (z : α) : Nat := 0

def wideCallee (α : Type) [Wide α] (z : α) : Nat := 0

def useNarrow (z : Nat) : Nat := narrowCallee Nat z

def useWide (z : Nat) : Nat := wideCallee Nat z

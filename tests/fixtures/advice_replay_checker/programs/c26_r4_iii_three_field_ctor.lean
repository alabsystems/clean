/-!
R4 item (iii): a tree type with a three-field constructor, as the checker's
labelled application `app f a label` (design 2.3), with recursion over it,
structural equality and rendering.
-/

inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm → Tm
  | lam : Tm → Tm

namespace Tm

def beq : Tm → Tm → Bool
  | .var i, .var j => i == j
  | .app f a l, .app g b m => beq f g && beq a b && beq l m
  | .lam b, .lam c => beq b c
  | _, _ => false

def size : Tm → Nat
  | .var _ => 1
  | .app f a l => size f + size a + size l + 1
  | .lam b => size b + 1

/-- Drop every label, keeping function and argument. -/
def erase : Tm → Tm
  | .var i => .var i
  | .app f a _ => .app (erase f) (erase a) (.var 0)
  | .lam b => .lam (erase b)

def render : Tm → String
  | .var i => s!"#{i}"
  | .app f a l => s!"({render f} {render a} : {render l})"
  | .lam b => s!"(fun {render b})"

end Tm

def main : IO Unit := do
  let t := Tm.app (.lam (.var 0)) (.var 3) (.lam (.var 1))
  IO.println t.render
  IO.println (toString t.size)
  IO.println t.erase.render
  IO.println (toString (Tm.beq t t))
  IO.println (toString (Tm.beq t t.erase))

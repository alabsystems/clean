-- The instance was compiled before the command with `slowBind`'s body
-- inlined into it (`@[inline]`), so `main`, compiled AFTER the command,
-- still runs the old body through it: Lean prints `2`. Clean's native path
-- inlined the instance's kernel value and printed `fastBind`'s `1` at exit 0.
structure Box (α : Type) where
  val : α
  tag : Nat
@[inline] def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
instance : Bind Box := ⟨fun x f => slowBind x f⟩
attribute [implemented_by fastBind] slowBind
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

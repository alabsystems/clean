-- The command before the instance: nothing was compiled before the binding,
-- and Lean runs `fastBind` through the instance, `1`.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
attribute [implemented_by fastBind] slowBind
instance : Bind Box := ⟨slowBind⟩
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

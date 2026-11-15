-- `@[implemented_by]` on an instance: compiled code runs the bound
-- instance's field, `1`; the kernel instance adds 2.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
@[reducible] def instFast : Bind Box := ⟨fastBind⟩
@[implemented_by instFast]
instance instSlow : Bind Box := ⟨slowBind⟩
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

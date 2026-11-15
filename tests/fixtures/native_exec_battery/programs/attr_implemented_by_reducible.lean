-- `@[implemented_by]` on a reducible instance field: compiled code runs
-- `fastBind`, `1`, even though `slowBind` unfolds at reducible transparency.
structure Box (α : Type) where
  val : α
  tag : Nat
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
@[reducible, implemented_by fastBind]
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
instance : Bind Box := ⟨slowBind⟩
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

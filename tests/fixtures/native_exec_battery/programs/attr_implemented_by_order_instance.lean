-- `main` reaches `slowBind` only through the `Bind Box` instance, and both
-- were compiled before `attribute [implemented_by fastBind] slowBind`: Lean
-- runs `slowBind`'s own body, `2`. Clean's native path inlines the instance
-- before its walk, so a record of direct references never saw `main`, and it
-- printed `fastBind`'s `1` at exit 0.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
instance : Bind Box := ⟨slowBind⟩
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))
attribute [implemented_by fastBind] slowBind

-- The same instance without `@[inline]`: Lean's instance inlining meets the
-- `slowBind` reference while compiling `main` after the command and runs
-- `fastBind`, `1`. Which body runs is Lean's inliner's choice (compare
-- `attr_implemented_by_order_instance_inline`); Clean does not model it and
-- refuses the program, although its output matched here.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
instance : Bind Box := ⟨slowBind⟩
attribute [implemented_by fastBind] slowBind
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

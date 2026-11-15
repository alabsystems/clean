-- `@[implemented_by pairF]` on an ordinary constant that the instance takes
-- apart with a `match`: compiled Lean runs `pairF`'s `fastBind`, `1`. Clean's
-- monad inlining reduced the `match` with full delta on `pairS`, unfolding
-- the declaration's own value, and printed `slowBind`'s `2` at exit 0.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
def pairF : Prod (Bind Box) Nat := (⟨fastBind⟩, 0)
@[implemented_by pairF] def pairS : Prod (Bind Box) Nat := (⟨slowBind⟩, 0)
instance instBindBox : Bind Box := match pairS with | (b, _) => b
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

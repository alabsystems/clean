-- The rebound `slowBind` is reached through `wrapper`, compiled before the
-- command, and `wrapper` only through `pairW`, an ordinary (non-reducible)
-- constant that the instance takes apart with a `match`. Lean runs
-- `wrapper`'s code as compiled before the binding: `2`. Clean's monad
-- inlining reduces the `match` with full delta on `pairW`, so `pairW` does
-- not survive into the value the walk reads; `wrapper` was compiled with
-- the binding, and the program printed `fastBind`'s `1` at exit 0.
structure Box (α : Type) where
  val : α
  tag : Nat
def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩
def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩
@[reducible, noinline] def wrapper {α β : Type} (x : Box α) (f : α → Box β) : Box β := slowBind x f
attribute [implemented_by fastBind] slowBind
def pairW : Prod (Bind Box) Nat := (⟨wrapper⟩, 0)
instance instBindBox : Bind Box := match pairW with | (b, _) => b
def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))

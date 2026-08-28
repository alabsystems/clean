-- Brick 0a reachability pin (designs/2026-08-25-rank1-full-gfp-lowering.md):
-- the v1 `coinductive` surface must be reachable through the REAL CLI path
-- (`clean check`), not only through elaborator unit tests. The declarations
-- mirror crates/clean-elab/src/infer/tests/inductive.rs (coind_stream_env +
-- the gfp discriminator): bisim_refl is provable ONLY in the greatest
-- fixpoint (the least fixpoint of this functor is empty on equal streams),
-- and bisim_head pins anti-vacuity (Bisim is not constantly true).

def Str : Type := Nat → Nat
def shd (s : Str) : Nat := s 0
def stl (s : Str) : Str := fun n => s (Nat.succ n)

coinductive Bisim : Str → Str → Prop
| step : shd s = shd t → Bisim (stl s) (stl t) → Bisim s t

theorem bisim_refl : ∀ s : Str, Bisim s s :=
  fun s => Bisim.coind (fun a b => a = b)
    (fun a b h => And.intro (congrArg shd h) (congrArg stl h)) s s rfl

theorem bisim_head : ∀ s : Str, ∀ t : Str, Bisim s t → shd s = shd t :=
  fun s t h => And.left (Bisim.unfold s t h)

theorem bisim_step_use : ∀ s : Str, ∀ t : Str,
    shd s = shd t → Bisim (stl s) (stl t) → Bisim s t :=
  fun s t h0 h1 => Bisim.step h0 h1

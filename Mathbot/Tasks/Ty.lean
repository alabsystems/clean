/-!
Ty reachability invariant replay toy.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Ty

inductive Reachable
    (Init : Nat → Prop)
    (Step : Nat → Nat → Prop) : Nat → Prop where
  | init (s : Nat) : Init s → Reachable Init Step s
  | step (s t : Nat) : Reachable Init Step s → Step s t → Reachable Init Step t

theorem ty_reachable_invariant_replay
    (Init Inv : Nat → Prop)
    (Step : Nat → Nat → Prop)
    (hinit : ∀ s, Init s → Inv s)
    (hstep : ∀ s t, Inv s → Step s t → Inv t) :
    ∀ s, Reachable Init Step s → Inv s := by
  intro s hreach
  induction hreach with
  | init s hs => exact hinit s hs
  | step s t _ hst ih => exact hstep s t ih hst

end Mathbot.Tasks.Ty

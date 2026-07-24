/-!
Branch-cover soundness for a branch-and-bound style verifier.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.BranchCover

structure SplitCover where
  domain : Nat → Prop
  left : Nat → Prop
  right : Nat → Prop

def covers (cover : SplitCover) : Prop :=
  ∀ x, cover.domain x → cover.left x ∨ cover.right x

theorem branch_cover_sound
    (cover : SplitCover)
    (safe : Nat → Prop)
    (hcover : covers cover)
    (hleft : ∀ x, cover.left x → safe x)
    (hright : ∀ x, cover.right x → safe x) :
    ∀ x, cover.domain x → safe x := by
  intro x hx
  cases hcover x hx with
  | inl h => exact hleft x h
  | inr h => exact hright x h

end Mathbot.Tasks.BranchCover

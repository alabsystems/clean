/-
  Bridge from a guarded Boolean VC to the existing SemR WP calculus.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanWPBranches

namespace SemRNativeWP
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches

/-- The native WP engine's two guarded successor obligations. -/
def guardedVC (condition yes no : Bool) : Bool :=
  (!condition || yes) && (!(!condition) || no)

def postHolds (post : Bool → Bool → Bool → Bool → Bool)
    (c a b : Bool) (vs : List Val) : Prop :=
  ∃ result, vs = [.bool result] ∧ post c a b result = true

/-- This is quantified over an arbitrary Boolean postcondition. The VC is
    the only postcondition premise; its selected clause supplies the leaf
    of the computed instruction WP. No execution or WP soundness is assumed. -/
theorem guarded_vc_implies_wp (post : Bool → Bool → Bool → Bool → Bool)
    (c a b : Bool) (depth : Nat)
    (hvc : guardedVC c (post c a b a) (post c a b b) = true) :
    diamondWP chooseModule 0 1 [2, 1] [] 2 [2, 1] [] 3 [4] [5] [] 7
      (postHolds post c a b) (chooseInitial c a b depth) := by
  cases c <;> simpa [guardedVC, diamondWP, conditionalWP, jumpWP, argsWP, armWP,
    prefixWP, returnPathWP, straightLineWP, returnWP, codeAt, postHolds,
    chooseInitial, chooseFunction, chooseSignature,
    chooseEntry, chooseLeft, chooseRight, chooseJoin, findBlock, nth?,
    conditionalNode, branchNode, returnNode, lookupEnv, bindParams,
    expectTy, Val.ty, Ty.beq, ok_bind] using hvc

theorem guarded_vc_implies_run (post : Bool → Bool → Bool → Bool → Bool)
    (c a b : Bool) (depth : Nat)
    (hvc : guardedVC c (post c a b a) (post c a b b) = true) :
    ∃ vs, runFunction chooseModule 0 [.bool c, .bool a, .bool b] 3 depth = .ret vs ∧
      postHolds post c a b vs := by
  obtain ⟨_, vs, _, hr, hpost⟩ := diamond_wp_run chooseModule
    0 1 [2, 1] [] 2 [2, 1] [] 3 [4] [5] [] 7
    (postHolds post c a b) (chooseInitial c a b depth)
    (guarded_vc_implies_wp post c a b depth hvc)
  have hstart : start chooseModule 0 [.bool c, .bool a, .bool b] depth =
      .ok (chooseInitial c a b depth) := by cases c <;> cases a <;> cases b <;> rfl
  exact ⟨vs, by simpa [runFunction, hstart] using hr, hpost⟩

end SemRNativeWP

/-
  DEEP-LAYER (machine-checked) joint 2-ReLU cut validity for ONE REAL pair.

  Net: ACAS-Xu net_1_1 (ACASXU_run2a_1_1_batch_2000.onnx), prop_1 input box.
  DEEP layer index = 2 (0-based hidden index; layer 0 is the FIRST hidden
  layer, so index 2 is hidden layer #3 -- PAST layer 1).  Pair = (36,46).

  z1,z2 are the TRUE pre-activations of neurons 36,46 at this deep layer.
  At a deep layer the reachable (z1,z2) is NOT an exact zonotope (it is gated by
  the earlier ReLUs).  We use the SOUND CROWN linear UPPER bounds
     z1 <= zU1(x) = ci.x + di,   z2 <= zU2(x) = cj.x + dj
  (the ci,di,cj,dj here are the f64 CROWN upper bounds SNAPPED OUTWARD to
  rationals, so zU stays a valid upper bound -- the snap inflates the intercept by
  the per-coordinate slope-rounding error over the box plus an f64 margin).  By
  relu monotonicity relu(z_i) <= relu(zU_i(x)); twoReluCut_pattern_dominance then
  bounds cc1*relu(zU1)+cc2*relu(zU2) <= B, where B = 33.906669 is the max of the
  four per-activation-pattern box-maxima (exact rationals).

  This is the DEEP analogue of acas_0_5_margin_closed (which was LAYER 1, exact
  zonotope).  Here the construction is SOUND-at-depth: it rests only on the sound
  CROWN upper bound + relu monotonicity (no claim that the deep reachable set is a
  zonotope).  cc1=cc2=1.

  #print axioms must be [propext, Classical.choice, Quot.sound], no sorryAx.
-/
import Crownproof.Basic
import Crownproof.TwoReluCutGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

namespace Crownproof

/-- ReLU is monotone: a ≤ b → relu a ≤ relu b.  (relu z = max 0 z.) -/
theorem relu_mono {a b : ℚ} (h : a ≤ b) : relu a ≤ relu b := by
  unfold relu
  exact max_le_max (le_refl 0) h

/-- DEEP real-pair joint-cut validity (sound at depth via CROWN upper bound +
relu monotonicity).  `z1,z2` are the true pre-activations; `huz1,huz2` are the
SOUND CROWN linear UPPER bound facts `z_i ≤ zU_i(x)`.  Conclusion: the joint
cut bound `B` dominates `relu z1 + relu z2` for every box point. -/
theorem acas_deep_36_46_cut
    (x0 x1 x2 x3 x4 z1 z2 : ℚ)
    (hl0 : (3 / 5 : ℚ) ≤ x0) (hu0 : x0 ≤ (679857769 / 1000000000 : ℚ))
    (hl1 : (-1 / 2 : ℚ) ≤ x1) (hu1 : x1 ≤ (1 / 2 : ℚ))
    (hl2 : (-1 / 2 : ℚ) ≤ x2) (hu2 : x2 ≤ (1 / 2 : ℚ))
    (hl3 : (9 / 20 : ℚ) ≤ x3) (hu3 : x3 ≤ (1 / 2 : ℚ))
    (hl4 : (-1 / 2 : ℚ) ≤ x4) (hu4 : x4 ≤ (-9 / 20 : ℚ))
    -- SOUND CROWN linear upper bounds (z_i ≤ zU_i(x)); from the backward pass
    (huz1 : z1 ≤ (-240971903 / 268435456 : ℚ)*x0 + (-2713645465 / 268435456 : ℚ)*x1 + (437923771 / 67108864 : ℚ)*x2 + (-66487649 / 268435456 : ℚ)*x3 + (388608867 / 268435456 : ℚ)*x4 + (14935895226958996904007 / 1099511627776000000000 : ℚ))
    (huz2 : z2 ≤ (-39759567 / 67108864 : ℚ)*x0 + (1548428853 / 134217728 : ℚ)*x1 + (1406632461 / 268435456 : ℚ)*x2 + (24449625 / 134217728 : ℚ)*x3 + (-65248495 / 67108864 : ℚ)*x4 + (8171255742075346182111 / 549755813888000000000 : ℚ)) :
    relu z1 + relu z2 ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) := by
  -- abbreviate the two affine upper bounds
  set zU1 : ℚ := (-240971903 / 268435456 : ℚ)*x0 + (-2713645465 / 268435456 : ℚ)*x1 + (437923771 / 67108864 : ℚ)*x2 + (-66487649 / 268435456 : ℚ)*x3 + (388608867 / 268435456 : ℚ)*x4 + (14935895226958996904007 / 1099511627776000000000 : ℚ) with hzU1
  set zU2 : ℚ := (-39759567 / 67108864 : ℚ)*x0 + (1548428853 / 134217728 : ℚ)*x1 + (1406632461 / 268435456 : ℚ)*x2 + (24449625 / 134217728 : ℚ)*x3 + (-65248495 / 67108864 : ℚ)*x4 + (8171255742075346182111 / 549755813888000000000 : ℚ) with hzU2
  -- monotonicity: relu z_i ≤ relu zU_i
  have hm1 : relu z1 ≤ relu zU1 := relu_mono huz1
  have hm2 : relu z2 ≤ relu zU2 := relu_mono huz2
  -- the four per-pattern branch values are ≤ B over the box (affine corner maxima)
  have hpp : (1:ℚ) * zU1 + (1:ℚ) * zU2 ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) := by rw [hzU1, hzU2]; linarith [hl0,hu0,hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]
  have hpn : (1:ℚ) * zU1 ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) := by rw [hzU1]; linarith [hl0,hu0,hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]
  have hnp : (1:ℚ) * zU2 ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) := by rw [hzU2]; linarith [hl0,hu0,hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]
  have hnn : (0:ℚ) ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) := by norm_num
  have hcut : (1:ℚ) * relu zU1 + (1:ℚ) * relu zU2 ≤ (37280776499832889268229 / 1099511627776000000000 : ℚ) :=
    twoReluCut_pattern_dominance 1 1 zU1 zU2 (37280776499832889268229 / 1099511627776000000000 : ℚ) (by norm_num) (by norm_num) hpp hpn hnp hnn
  -- combine monotonicity with the cut bound
  have : relu z1 + relu z2 ≤ relu zU1 + relu zU2 := by linarith
  linarith [hcut]

#print axioms relu_mono
#print axioms acas_deep_36_46_cut

end Crownproof

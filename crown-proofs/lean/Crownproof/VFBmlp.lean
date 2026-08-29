import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem mlp_c0 (rl : Fin 96 → ℝ)
    (hl : ∀ jj, ((rLo jj:ℚ):ℝ) ≤ rl jj) (hh : ∀ jj, rl jj ≤ ((rHi jj:ℚ):ℝ)) :
    ((mLo 0:ℚ):ℝ) ≤ (((9728007/1073741824):ℚ):ℝ) + ∑ jj, ((W2_0 jj:ℚ):ℝ) * rl jj ∧
    (((9728007/1073741824):ℚ):ℝ) + ∑ jj, ((W2_0 jj:ℚ):ℝ) * rl jj ≤ ((mHi 0:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W2_0 jj:ℚ):ℝ)) (fun jj => ((rLo jj:ℚ):ℝ)) (fun jj => ((rHi jj:ℚ):ℝ)) rl hl hh
  refine ⟨?_,?_⟩
  · have hs : ((mLo 0:ℚ):ℝ) - (((9728007/1073741824):ℚ):ℝ) ≤ ∑ jj, min (((W2_0 jj:ℚ):ℝ)*((rLo jj:ℚ):ℝ)) (((W2_0 jj:ℚ):ℝ)*((rHi jj:ℚ):ℝ)) := by
      simp only [mLo, W2_0, rLo, rHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W2_0 jj:ℚ):ℝ)*((rLo jj:ℚ):ℝ)) (((W2_0 jj:ℚ):ℝ)*((rHi jj:ℚ):ℝ))) ≤ ((mHi 0:ℚ):ℝ) - (((9728007/1073741824):ℚ):ℝ) := by
      simp only [mHi, W2_0, rLo, rHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]


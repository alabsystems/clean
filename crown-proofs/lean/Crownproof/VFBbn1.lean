import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem bn1_c0 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 0:ℚ):ℝ) ≤ ((bn1_bias 0 : ℚ):ℝ) + ((bn1_weight 0 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 0 : ℚ):ℝ) * (x 0 - ((bn1_mean 0 : ℚ):ℝ))) ∧
    ((bn1_bias 0 : ℚ):ℝ) + ((bn1_weight 0 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 0 : ℚ):ℝ) * (x 0 - ((bn1_mean 0 : ℚ):ℝ))) ≤ ((n1Hi 0:ℚ):ℝ) := by
  have hlo := hl 0; have hho := hh 0
  apply bn_channel_box ((bn1_weight 0 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 0 : ℚ):ℝ) ((bn1_glo 0 : ℚ):ℝ) ((bn1_ghi 0 : ℚ):ℝ) ((bn1_mean 0 : ℚ):ℝ) ((bn1_bias 0 : ℚ):ℝ) ((xLo 0:ℚ):ℝ) ((xHi 0:ℚ):ℝ) ((n1Lo 0:ℚ):ℝ) ((n1Hi 0:ℚ):ℝ) (x 0)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c1 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 1:ℚ):ℝ) ≤ ((bn1_bias 1 : ℚ):ℝ) + ((bn1_weight 1 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 1 : ℚ):ℝ) * (x 1 - ((bn1_mean 1 : ℚ):ℝ))) ∧
    ((bn1_bias 1 : ℚ):ℝ) + ((bn1_weight 1 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 1 : ℚ):ℝ) * (x 1 - ((bn1_mean 1 : ℚ):ℝ))) ≤ ((n1Hi 1:ℚ):ℝ) := by
  have hlo := hl 1; have hho := hh 1
  apply bn_channel_box ((bn1_weight 1 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 1 : ℚ):ℝ) ((bn1_glo 1 : ℚ):ℝ) ((bn1_ghi 1 : ℚ):ℝ) ((bn1_mean 1 : ℚ):ℝ) ((bn1_bias 1 : ℚ):ℝ) ((xLo 1:ℚ):ℝ) ((xHi 1:ℚ):ℝ) ((n1Lo 1:ℚ):ℝ) ((n1Hi 1:ℚ):ℝ) (x 1)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c2 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 2:ℚ):ℝ) ≤ ((bn1_bias 2 : ℚ):ℝ) + ((bn1_weight 2 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 2 : ℚ):ℝ) * (x 2 - ((bn1_mean 2 : ℚ):ℝ))) ∧
    ((bn1_bias 2 : ℚ):ℝ) + ((bn1_weight 2 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 2 : ℚ):ℝ) * (x 2 - ((bn1_mean 2 : ℚ):ℝ))) ≤ ((n1Hi 2:ℚ):ℝ) := by
  have hlo := hl 2; have hho := hh 2
  apply bn_channel_box ((bn1_weight 2 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 2 : ℚ):ℝ) ((bn1_glo 2 : ℚ):ℝ) ((bn1_ghi 2 : ℚ):ℝ) ((bn1_mean 2 : ℚ):ℝ) ((bn1_bias 2 : ℚ):ℝ) ((xLo 2:ℚ):ℝ) ((xHi 2:ℚ):ℝ) ((n1Lo 2:ℚ):ℝ) ((n1Hi 2:ℚ):ℝ) (x 2)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c3 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 3:ℚ):ℝ) ≤ ((bn1_bias 3 : ℚ):ℝ) + ((bn1_weight 3 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 3 : ℚ):ℝ) * (x 3 - ((bn1_mean 3 : ℚ):ℝ))) ∧
    ((bn1_bias 3 : ℚ):ℝ) + ((bn1_weight 3 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 3 : ℚ):ℝ) * (x 3 - ((bn1_mean 3 : ℚ):ℝ))) ≤ ((n1Hi 3:ℚ):ℝ) := by
  have hlo := hl 3; have hho := hh 3
  apply bn_channel_box ((bn1_weight 3 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 3 : ℚ):ℝ) ((bn1_glo 3 : ℚ):ℝ) ((bn1_ghi 3 : ℚ):ℝ) ((bn1_mean 3 : ℚ):ℝ) ((bn1_bias 3 : ℚ):ℝ) ((xLo 3:ℚ):ℝ) ((xHi 3:ℚ):ℝ) ((n1Lo 3:ℚ):ℝ) ((n1Hi 3:ℚ):ℝ) (x 3)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c4 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 4:ℚ):ℝ) ≤ ((bn1_bias 4 : ℚ):ℝ) + ((bn1_weight 4 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 4 : ℚ):ℝ) * (x 4 - ((bn1_mean 4 : ℚ):ℝ))) ∧
    ((bn1_bias 4 : ℚ):ℝ) + ((bn1_weight 4 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 4 : ℚ):ℝ) * (x 4 - ((bn1_mean 4 : ℚ):ℝ))) ≤ ((n1Hi 4:ℚ):ℝ) := by
  have hlo := hl 4; have hho := hh 4
  apply bn_channel_box ((bn1_weight 4 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 4 : ℚ):ℝ) ((bn1_glo 4 : ℚ):ℝ) ((bn1_ghi 4 : ℚ):ℝ) ((bn1_mean 4 : ℚ):ℝ) ((bn1_bias 4 : ℚ):ℝ) ((xLo 4:ℚ):ℝ) ((xHi 4:ℚ):ℝ) ((n1Lo 4:ℚ):ℝ) ((n1Hi 4:ℚ):ℝ) (x 4)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c5 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 5:ℚ):ℝ) ≤ ((bn1_bias 5 : ℚ):ℝ) + ((bn1_weight 5 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 5 : ℚ):ℝ) * (x 5 - ((bn1_mean 5 : ℚ):ℝ))) ∧
    ((bn1_bias 5 : ℚ):ℝ) + ((bn1_weight 5 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 5 : ℚ):ℝ) * (x 5 - ((bn1_mean 5 : ℚ):ℝ))) ≤ ((n1Hi 5:ℚ):ℝ) := by
  have hlo := hl 5; have hho := hh 5
  apply bn_channel_box ((bn1_weight 5 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 5 : ℚ):ℝ) ((bn1_glo 5 : ℚ):ℝ) ((bn1_ghi 5 : ℚ):ℝ) ((bn1_mean 5 : ℚ):ℝ) ((bn1_bias 5 : ℚ):ℝ) ((xLo 5:ℚ):ℝ) ((xHi 5:ℚ):ℝ) ((n1Lo 5:ℚ):ℝ) ((n1Hi 5:ℚ):ℝ) (x 5)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c6 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 6:ℚ):ℝ) ≤ ((bn1_bias 6 : ℚ):ℝ) + ((bn1_weight 6 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 6 : ℚ):ℝ) * (x 6 - ((bn1_mean 6 : ℚ):ℝ))) ∧
    ((bn1_bias 6 : ℚ):ℝ) + ((bn1_weight 6 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 6 : ℚ):ℝ) * (x 6 - ((bn1_mean 6 : ℚ):ℝ))) ≤ ((n1Hi 6:ℚ):ℝ) := by
  have hlo := hl 6; have hho := hh 6
  apply bn_channel_box ((bn1_weight 6 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 6 : ℚ):ℝ) ((bn1_glo 6 : ℚ):ℝ) ((bn1_ghi 6 : ℚ):ℝ) ((bn1_mean 6 : ℚ):ℝ) ((bn1_bias 6 : ℚ):ℝ) ((xLo 6:ℚ):ℝ) ((xHi 6:ℚ):ℝ) ((n1Lo 6:ℚ):ℝ) ((n1Hi 6:ℚ):ℝ) (x 6)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c7 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 7:ℚ):ℝ) ≤ ((bn1_bias 7 : ℚ):ℝ) + ((bn1_weight 7 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 7 : ℚ):ℝ) * (x 7 - ((bn1_mean 7 : ℚ):ℝ))) ∧
    ((bn1_bias 7 : ℚ):ℝ) + ((bn1_weight 7 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 7 : ℚ):ℝ) * (x 7 - ((bn1_mean 7 : ℚ):ℝ))) ≤ ((n1Hi 7:ℚ):ℝ) := by
  have hlo := hl 7; have hho := hh 7
  apply bn_channel_box ((bn1_weight 7 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 7 : ℚ):ℝ) ((bn1_glo 7 : ℚ):ℝ) ((bn1_ghi 7 : ℚ):ℝ) ((bn1_mean 7 : ℚ):ℝ) ((bn1_bias 7 : ℚ):ℝ) ((xLo 7:ℚ):ℝ) ((xHi 7:ℚ):ℝ) ((n1Lo 7:ℚ):ℝ) ((n1Hi 7:ℚ):ℝ) (x 7)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c8 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 8:ℚ):ℝ) ≤ ((bn1_bias 8 : ℚ):ℝ) + ((bn1_weight 8 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 8 : ℚ):ℝ) * (x 8 - ((bn1_mean 8 : ℚ):ℝ))) ∧
    ((bn1_bias 8 : ℚ):ℝ) + ((bn1_weight 8 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 8 : ℚ):ℝ) * (x 8 - ((bn1_mean 8 : ℚ):ℝ))) ≤ ((n1Hi 8:ℚ):ℝ) := by
  have hlo := hl 8; have hho := hh 8
  apply bn_channel_box ((bn1_weight 8 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 8 : ℚ):ℝ) ((bn1_glo 8 : ℚ):ℝ) ((bn1_ghi 8 : ℚ):ℝ) ((bn1_mean 8 : ℚ):ℝ) ((bn1_bias 8 : ℚ):ℝ) ((xLo 8:ℚ):ℝ) ((xHi 8:ℚ):ℝ) ((n1Lo 8:ℚ):ℝ) ((n1Hi 8:ℚ):ℝ) (x 8)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c9 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 9:ℚ):ℝ) ≤ ((bn1_bias 9 : ℚ):ℝ) + ((bn1_weight 9 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 9 : ℚ):ℝ) * (x 9 - ((bn1_mean 9 : ℚ):ℝ))) ∧
    ((bn1_bias 9 : ℚ):ℝ) + ((bn1_weight 9 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 9 : ℚ):ℝ) * (x 9 - ((bn1_mean 9 : ℚ):ℝ))) ≤ ((n1Hi 9:ℚ):ℝ) := by
  have hlo := hl 9; have hho := hh 9
  apply bn_channel_box ((bn1_weight 9 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 9 : ℚ):ℝ) ((bn1_glo 9 : ℚ):ℝ) ((bn1_ghi 9 : ℚ):ℝ) ((bn1_mean 9 : ℚ):ℝ) ((bn1_bias 9 : ℚ):ℝ) ((xLo 9:ℚ):ℝ) ((xHi 9:ℚ):ℝ) ((n1Lo 9:ℚ):ℝ) ((n1Hi 9:ℚ):ℝ) (x 9)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c10 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 10:ℚ):ℝ) ≤ ((bn1_bias 10 : ℚ):ℝ) + ((bn1_weight 10 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 10 : ℚ):ℝ) * (x 10 - ((bn1_mean 10 : ℚ):ℝ))) ∧
    ((bn1_bias 10 : ℚ):ℝ) + ((bn1_weight 10 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 10 : ℚ):ℝ) * (x 10 - ((bn1_mean 10 : ℚ):ℝ))) ≤ ((n1Hi 10:ℚ):ℝ) := by
  have hlo := hl 10; have hho := hh 10
  apply bn_channel_box ((bn1_weight 10 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 10 : ℚ):ℝ) ((bn1_glo 10 : ℚ):ℝ) ((bn1_ghi 10 : ℚ):ℝ) ((bn1_mean 10 : ℚ):ℝ) ((bn1_bias 10 : ℚ):ℝ) ((xLo 10:ℚ):ℝ) ((xHi 10:ℚ):ℝ) ((n1Lo 10:ℚ):ℝ) ((n1Hi 10:ℚ):ℝ) (x 10)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c11 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 11:ℚ):ℝ) ≤ ((bn1_bias 11 : ℚ):ℝ) + ((bn1_weight 11 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 11 : ℚ):ℝ) * (x 11 - ((bn1_mean 11 : ℚ):ℝ))) ∧
    ((bn1_bias 11 : ℚ):ℝ) + ((bn1_weight 11 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 11 : ℚ):ℝ) * (x 11 - ((bn1_mean 11 : ℚ):ℝ))) ≤ ((n1Hi 11:ℚ):ℝ) := by
  have hlo := hl 11; have hho := hh 11
  apply bn_channel_box ((bn1_weight 11 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 11 : ℚ):ℝ) ((bn1_glo 11 : ℚ):ℝ) ((bn1_ghi 11 : ℚ):ℝ) ((bn1_mean 11 : ℚ):ℝ) ((bn1_bias 11 : ℚ):ℝ) ((xLo 11:ℚ):ℝ) ((xHi 11:ℚ):ℝ) ((n1Lo 11:ℚ):ℝ) ((n1Hi 11:ℚ):ℝ) (x 11)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c12 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 12:ℚ):ℝ) ≤ ((bn1_bias 12 : ℚ):ℝ) + ((bn1_weight 12 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 12 : ℚ):ℝ) * (x 12 - ((bn1_mean 12 : ℚ):ℝ))) ∧
    ((bn1_bias 12 : ℚ):ℝ) + ((bn1_weight 12 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 12 : ℚ):ℝ) * (x 12 - ((bn1_mean 12 : ℚ):ℝ))) ≤ ((n1Hi 12:ℚ):ℝ) := by
  have hlo := hl 12; have hho := hh 12
  apply bn_channel_box ((bn1_weight 12 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 12 : ℚ):ℝ) ((bn1_glo 12 : ℚ):ℝ) ((bn1_ghi 12 : ℚ):ℝ) ((bn1_mean 12 : ℚ):ℝ) ((bn1_bias 12 : ℚ):ℝ) ((xLo 12:ℚ):ℝ) ((xHi 12:ℚ):ℝ) ((n1Lo 12:ℚ):ℝ) ((n1Hi 12:ℚ):ℝ) (x 12)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c13 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 13:ℚ):ℝ) ≤ ((bn1_bias 13 : ℚ):ℝ) + ((bn1_weight 13 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 13 : ℚ):ℝ) * (x 13 - ((bn1_mean 13 : ℚ):ℝ))) ∧
    ((bn1_bias 13 : ℚ):ℝ) + ((bn1_weight 13 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 13 : ℚ):ℝ) * (x 13 - ((bn1_mean 13 : ℚ):ℝ))) ≤ ((n1Hi 13:ℚ):ℝ) := by
  have hlo := hl 13; have hho := hh 13
  apply bn_channel_box ((bn1_weight 13 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 13 : ℚ):ℝ) ((bn1_glo 13 : ℚ):ℝ) ((bn1_ghi 13 : ℚ):ℝ) ((bn1_mean 13 : ℚ):ℝ) ((bn1_bias 13 : ℚ):ℝ) ((xLo 13:ℚ):ℝ) ((xHi 13:ℚ):ℝ) ((n1Lo 13:ℚ):ℝ) ((n1Hi 13:ℚ):ℝ) (x 13)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c14 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 14:ℚ):ℝ) ≤ ((bn1_bias 14 : ℚ):ℝ) + ((bn1_weight 14 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 14 : ℚ):ℝ) * (x 14 - ((bn1_mean 14 : ℚ):ℝ))) ∧
    ((bn1_bias 14 : ℚ):ℝ) + ((bn1_weight 14 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 14 : ℚ):ℝ) * (x 14 - ((bn1_mean 14 : ℚ):ℝ))) ≤ ((n1Hi 14:ℚ):ℝ) := by
  have hlo := hl 14; have hho := hh 14
  apply bn_channel_box ((bn1_weight 14 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 14 : ℚ):ℝ) ((bn1_glo 14 : ℚ):ℝ) ((bn1_ghi 14 : ℚ):ℝ) ((bn1_mean 14 : ℚ):ℝ) ((bn1_bias 14 : ℚ):ℝ) ((xLo 14:ℚ):ℝ) ((xHi 14:ℚ):ℝ) ((n1Lo 14:ℚ):ℝ) ((n1Hi 14:ℚ):ℝ) (x 14)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c15 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 15:ℚ):ℝ) ≤ ((bn1_bias 15 : ℚ):ℝ) + ((bn1_weight 15 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 15 : ℚ):ℝ) * (x 15 - ((bn1_mean 15 : ℚ):ℝ))) ∧
    ((bn1_bias 15 : ℚ):ℝ) + ((bn1_weight 15 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 15 : ℚ):ℝ) * (x 15 - ((bn1_mean 15 : ℚ):ℝ))) ≤ ((n1Hi 15:ℚ):ℝ) := by
  have hlo := hl 15; have hho := hh 15
  apply bn_channel_box ((bn1_weight 15 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 15 : ℚ):ℝ) ((bn1_glo 15 : ℚ):ℝ) ((bn1_ghi 15 : ℚ):ℝ) ((bn1_mean 15 : ℚ):ℝ) ((bn1_bias 15 : ℚ):ℝ) ((xLo 15:ℚ):ℝ) ((xHi 15:ℚ):ℝ) ((n1Lo 15:ℚ):ℝ) ((n1Hi 15:ℚ):ℝ) (x 15)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c16 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 16:ℚ):ℝ) ≤ ((bn1_bias 16 : ℚ):ℝ) + ((bn1_weight 16 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 16 : ℚ):ℝ) * (x 16 - ((bn1_mean 16 : ℚ):ℝ))) ∧
    ((bn1_bias 16 : ℚ):ℝ) + ((bn1_weight 16 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 16 : ℚ):ℝ) * (x 16 - ((bn1_mean 16 : ℚ):ℝ))) ≤ ((n1Hi 16:ℚ):ℝ) := by
  have hlo := hl 16; have hho := hh 16
  apply bn_channel_box ((bn1_weight 16 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 16 : ℚ):ℝ) ((bn1_glo 16 : ℚ):ℝ) ((bn1_ghi 16 : ℚ):ℝ) ((bn1_mean 16 : ℚ):ℝ) ((bn1_bias 16 : ℚ):ℝ) ((xLo 16:ℚ):ℝ) ((xHi 16:ℚ):ℝ) ((n1Lo 16:ℚ):ℝ) ((n1Hi 16:ℚ):ℝ) (x 16)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c17 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 17:ℚ):ℝ) ≤ ((bn1_bias 17 : ℚ):ℝ) + ((bn1_weight 17 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 17 : ℚ):ℝ) * (x 17 - ((bn1_mean 17 : ℚ):ℝ))) ∧
    ((bn1_bias 17 : ℚ):ℝ) + ((bn1_weight 17 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 17 : ℚ):ℝ) * (x 17 - ((bn1_mean 17 : ℚ):ℝ))) ≤ ((n1Hi 17:ℚ):ℝ) := by
  have hlo := hl 17; have hho := hh 17
  apply bn_channel_box ((bn1_weight 17 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 17 : ℚ):ℝ) ((bn1_glo 17 : ℚ):ℝ) ((bn1_ghi 17 : ℚ):ℝ) ((bn1_mean 17 : ℚ):ℝ) ((bn1_bias 17 : ℚ):ℝ) ((xLo 17:ℚ):ℝ) ((xHi 17:ℚ):ℝ) ((n1Lo 17:ℚ):ℝ) ((n1Hi 17:ℚ):ℝ) (x 17)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c18 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 18:ℚ):ℝ) ≤ ((bn1_bias 18 : ℚ):ℝ) + ((bn1_weight 18 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 18 : ℚ):ℝ) * (x 18 - ((bn1_mean 18 : ℚ):ℝ))) ∧
    ((bn1_bias 18 : ℚ):ℝ) + ((bn1_weight 18 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 18 : ℚ):ℝ) * (x 18 - ((bn1_mean 18 : ℚ):ℝ))) ≤ ((n1Hi 18:ℚ):ℝ) := by
  have hlo := hl 18; have hho := hh 18
  apply bn_channel_box ((bn1_weight 18 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 18 : ℚ):ℝ) ((bn1_glo 18 : ℚ):ℝ) ((bn1_ghi 18 : ℚ):ℝ) ((bn1_mean 18 : ℚ):ℝ) ((bn1_bias 18 : ℚ):ℝ) ((xLo 18:ℚ):ℝ) ((xHi 18:ℚ):ℝ) ((n1Lo 18:ℚ):ℝ) ((n1Hi 18:ℚ):ℝ) (x 18)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c19 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 19:ℚ):ℝ) ≤ ((bn1_bias 19 : ℚ):ℝ) + ((bn1_weight 19 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 19 : ℚ):ℝ) * (x 19 - ((bn1_mean 19 : ℚ):ℝ))) ∧
    ((bn1_bias 19 : ℚ):ℝ) + ((bn1_weight 19 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 19 : ℚ):ℝ) * (x 19 - ((bn1_mean 19 : ℚ):ℝ))) ≤ ((n1Hi 19:ℚ):ℝ) := by
  have hlo := hl 19; have hho := hh 19
  apply bn_channel_box ((bn1_weight 19 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 19 : ℚ):ℝ) ((bn1_glo 19 : ℚ):ℝ) ((bn1_ghi 19 : ℚ):ℝ) ((bn1_mean 19 : ℚ):ℝ) ((bn1_bias 19 : ℚ):ℝ) ((xLo 19:ℚ):ℝ) ((xHi 19:ℚ):ℝ) ((n1Lo 19:ℚ):ℝ) ((n1Hi 19:ℚ):ℝ) (x 19)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c20 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 20:ℚ):ℝ) ≤ ((bn1_bias 20 : ℚ):ℝ) + ((bn1_weight 20 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 20 : ℚ):ℝ) * (x 20 - ((bn1_mean 20 : ℚ):ℝ))) ∧
    ((bn1_bias 20 : ℚ):ℝ) + ((bn1_weight 20 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 20 : ℚ):ℝ) * (x 20 - ((bn1_mean 20 : ℚ):ℝ))) ≤ ((n1Hi 20:ℚ):ℝ) := by
  have hlo := hl 20; have hho := hh 20
  apply bn_channel_box ((bn1_weight 20 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 20 : ℚ):ℝ) ((bn1_glo 20 : ℚ):ℝ) ((bn1_ghi 20 : ℚ):ℝ) ((bn1_mean 20 : ℚ):ℝ) ((bn1_bias 20 : ℚ):ℝ) ((xLo 20:ℚ):ℝ) ((xHi 20:ℚ):ℝ) ((n1Lo 20:ℚ):ℝ) ((n1Hi 20:ℚ):ℝ) (x 20)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c21 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 21:ℚ):ℝ) ≤ ((bn1_bias 21 : ℚ):ℝ) + ((bn1_weight 21 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 21 : ℚ):ℝ) * (x 21 - ((bn1_mean 21 : ℚ):ℝ))) ∧
    ((bn1_bias 21 : ℚ):ℝ) + ((bn1_weight 21 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 21 : ℚ):ℝ) * (x 21 - ((bn1_mean 21 : ℚ):ℝ))) ≤ ((n1Hi 21:ℚ):ℝ) := by
  have hlo := hl 21; have hho := hh 21
  apply bn_channel_box ((bn1_weight 21 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 21 : ℚ):ℝ) ((bn1_glo 21 : ℚ):ℝ) ((bn1_ghi 21 : ℚ):ℝ) ((bn1_mean 21 : ℚ):ℝ) ((bn1_bias 21 : ℚ):ℝ) ((xLo 21:ℚ):ℝ) ((xHi 21:ℚ):ℝ) ((n1Lo 21:ℚ):ℝ) ((n1Hi 21:ℚ):ℝ) (x 21)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c22 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 22:ℚ):ℝ) ≤ ((bn1_bias 22 : ℚ):ℝ) + ((bn1_weight 22 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 22 : ℚ):ℝ) * (x 22 - ((bn1_mean 22 : ℚ):ℝ))) ∧
    ((bn1_bias 22 : ℚ):ℝ) + ((bn1_weight 22 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 22 : ℚ):ℝ) * (x 22 - ((bn1_mean 22 : ℚ):ℝ))) ≤ ((n1Hi 22:ℚ):ℝ) := by
  have hlo := hl 22; have hho := hh 22
  apply bn_channel_box ((bn1_weight 22 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 22 : ℚ):ℝ) ((bn1_glo 22 : ℚ):ℝ) ((bn1_ghi 22 : ℚ):ℝ) ((bn1_mean 22 : ℚ):ℝ) ((bn1_bias 22 : ℚ):ℝ) ((xLo 22:ℚ):ℝ) ((xHi 22:ℚ):ℝ) ((n1Lo 22:ℚ):ℝ) ((n1Hi 22:ℚ):ℝ) (x 22)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c23 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 23:ℚ):ℝ) ≤ ((bn1_bias 23 : ℚ):ℝ) + ((bn1_weight 23 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 23 : ℚ):ℝ) * (x 23 - ((bn1_mean 23 : ℚ):ℝ))) ∧
    ((bn1_bias 23 : ℚ):ℝ) + ((bn1_weight 23 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 23 : ℚ):ℝ) * (x 23 - ((bn1_mean 23 : ℚ):ℝ))) ≤ ((n1Hi 23:ℚ):ℝ) := by
  have hlo := hl 23; have hho := hh 23
  apply bn_channel_box ((bn1_weight 23 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 23 : ℚ):ℝ) ((bn1_glo 23 : ℚ):ℝ) ((bn1_ghi 23 : ℚ):ℝ) ((bn1_mean 23 : ℚ):ℝ) ((bn1_bias 23 : ℚ):ℝ) ((xLo 23:ℚ):ℝ) ((xHi 23:ℚ):ℝ) ((n1Lo 23:ℚ):ℝ) ((n1Hi 23:ℚ):ℝ) (x 23)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c24 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 24:ℚ):ℝ) ≤ ((bn1_bias 24 : ℚ):ℝ) + ((bn1_weight 24 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 24 : ℚ):ℝ) * (x 24 - ((bn1_mean 24 : ℚ):ℝ))) ∧
    ((bn1_bias 24 : ℚ):ℝ) + ((bn1_weight 24 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 24 : ℚ):ℝ) * (x 24 - ((bn1_mean 24 : ℚ):ℝ))) ≤ ((n1Hi 24:ℚ):ℝ) := by
  have hlo := hl 24; have hho := hh 24
  apply bn_channel_box ((bn1_weight 24 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 24 : ℚ):ℝ) ((bn1_glo 24 : ℚ):ℝ) ((bn1_ghi 24 : ℚ):ℝ) ((bn1_mean 24 : ℚ):ℝ) ((bn1_bias 24 : ℚ):ℝ) ((xLo 24:ℚ):ℝ) ((xHi 24:ℚ):ℝ) ((n1Lo 24:ℚ):ℝ) ((n1Hi 24:ℚ):ℝ) (x 24)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c25 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 25:ℚ):ℝ) ≤ ((bn1_bias 25 : ℚ):ℝ) + ((bn1_weight 25 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 25 : ℚ):ℝ) * (x 25 - ((bn1_mean 25 : ℚ):ℝ))) ∧
    ((bn1_bias 25 : ℚ):ℝ) + ((bn1_weight 25 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 25 : ℚ):ℝ) * (x 25 - ((bn1_mean 25 : ℚ):ℝ))) ≤ ((n1Hi 25:ℚ):ℝ) := by
  have hlo := hl 25; have hho := hh 25
  apply bn_channel_box ((bn1_weight 25 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 25 : ℚ):ℝ) ((bn1_glo 25 : ℚ):ℝ) ((bn1_ghi 25 : ℚ):ℝ) ((bn1_mean 25 : ℚ):ℝ) ((bn1_bias 25 : ℚ):ℝ) ((xLo 25:ℚ):ℝ) ((xHi 25:ℚ):ℝ) ((n1Lo 25:ℚ):ℝ) ((n1Hi 25:ℚ):ℝ) (x 25)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c26 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 26:ℚ):ℝ) ≤ ((bn1_bias 26 : ℚ):ℝ) + ((bn1_weight 26 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 26 : ℚ):ℝ) * (x 26 - ((bn1_mean 26 : ℚ):ℝ))) ∧
    ((bn1_bias 26 : ℚ):ℝ) + ((bn1_weight 26 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 26 : ℚ):ℝ) * (x 26 - ((bn1_mean 26 : ℚ):ℝ))) ≤ ((n1Hi 26:ℚ):ℝ) := by
  have hlo := hl 26; have hho := hh 26
  apply bn_channel_box ((bn1_weight 26 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 26 : ℚ):ℝ) ((bn1_glo 26 : ℚ):ℝ) ((bn1_ghi 26 : ℚ):ℝ) ((bn1_mean 26 : ℚ):ℝ) ((bn1_bias 26 : ℚ):ℝ) ((xLo 26:ℚ):ℝ) ((xHi 26:ℚ):ℝ) ((n1Lo 26:ℚ):ℝ) ((n1Hi 26:ℚ):ℝ) (x 26)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c27 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 27:ℚ):ℝ) ≤ ((bn1_bias 27 : ℚ):ℝ) + ((bn1_weight 27 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 27 : ℚ):ℝ) * (x 27 - ((bn1_mean 27 : ℚ):ℝ))) ∧
    ((bn1_bias 27 : ℚ):ℝ) + ((bn1_weight 27 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 27 : ℚ):ℝ) * (x 27 - ((bn1_mean 27 : ℚ):ℝ))) ≤ ((n1Hi 27:ℚ):ℝ) := by
  have hlo := hl 27; have hho := hh 27
  apply bn_channel_box ((bn1_weight 27 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 27 : ℚ):ℝ) ((bn1_glo 27 : ℚ):ℝ) ((bn1_ghi 27 : ℚ):ℝ) ((bn1_mean 27 : ℚ):ℝ) ((bn1_bias 27 : ℚ):ℝ) ((xLo 27:ℚ):ℝ) ((xHi 27:ℚ):ℝ) ((n1Lo 27:ℚ):ℝ) ((n1Hi 27:ℚ):ℝ) (x 27)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c28 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 28:ℚ):ℝ) ≤ ((bn1_bias 28 : ℚ):ℝ) + ((bn1_weight 28 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 28 : ℚ):ℝ) * (x 28 - ((bn1_mean 28 : ℚ):ℝ))) ∧
    ((bn1_bias 28 : ℚ):ℝ) + ((bn1_weight 28 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 28 : ℚ):ℝ) * (x 28 - ((bn1_mean 28 : ℚ):ℝ))) ≤ ((n1Hi 28:ℚ):ℝ) := by
  have hlo := hl 28; have hho := hh 28
  apply bn_channel_box ((bn1_weight 28 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 28 : ℚ):ℝ) ((bn1_glo 28 : ℚ):ℝ) ((bn1_ghi 28 : ℚ):ℝ) ((bn1_mean 28 : ℚ):ℝ) ((bn1_bias 28 : ℚ):ℝ) ((xLo 28:ℚ):ℝ) ((xHi 28:ℚ):ℝ) ((n1Lo 28:ℚ):ℝ) ((n1Hi 28:ℚ):ℝ) (x 28)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c29 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 29:ℚ):ℝ) ≤ ((bn1_bias 29 : ℚ):ℝ) + ((bn1_weight 29 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 29 : ℚ):ℝ) * (x 29 - ((bn1_mean 29 : ℚ):ℝ))) ∧
    ((bn1_bias 29 : ℚ):ℝ) + ((bn1_weight 29 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 29 : ℚ):ℝ) * (x 29 - ((bn1_mean 29 : ℚ):ℝ))) ≤ ((n1Hi 29:ℚ):ℝ) := by
  have hlo := hl 29; have hho := hh 29
  apply bn_channel_box ((bn1_weight 29 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 29 : ℚ):ℝ) ((bn1_glo 29 : ℚ):ℝ) ((bn1_ghi 29 : ℚ):ℝ) ((bn1_mean 29 : ℚ):ℝ) ((bn1_bias 29 : ℚ):ℝ) ((xLo 29:ℚ):ℝ) ((xHi 29:ℚ):ℝ) ((n1Lo 29:ℚ):ℝ) ((n1Hi 29:ℚ):ℝ) (x 29)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c30 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 30:ℚ):ℝ) ≤ ((bn1_bias 30 : ℚ):ℝ) + ((bn1_weight 30 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 30 : ℚ):ℝ) * (x 30 - ((bn1_mean 30 : ℚ):ℝ))) ∧
    ((bn1_bias 30 : ℚ):ℝ) + ((bn1_weight 30 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 30 : ℚ):ℝ) * (x 30 - ((bn1_mean 30 : ℚ):ℝ))) ≤ ((n1Hi 30:ℚ):ℝ) := by
  have hlo := hl 30; have hho := hh 30
  apply bn_channel_box ((bn1_weight 30 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 30 : ℚ):ℝ) ((bn1_glo 30 : ℚ):ℝ) ((bn1_ghi 30 : ℚ):ℝ) ((bn1_mean 30 : ℚ):ℝ) ((bn1_bias 30 : ℚ):ℝ) ((xLo 30:ℚ):ℝ) ((xHi 30:ℚ):ℝ) ((n1Lo 30:ℚ):ℝ) ((n1Hi 30:ℚ):ℝ) (x 30)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c31 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 31:ℚ):ℝ) ≤ ((bn1_bias 31 : ℚ):ℝ) + ((bn1_weight 31 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 31 : ℚ):ℝ) * (x 31 - ((bn1_mean 31 : ℚ):ℝ))) ∧
    ((bn1_bias 31 : ℚ):ℝ) + ((bn1_weight 31 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 31 : ℚ):ℝ) * (x 31 - ((bn1_mean 31 : ℚ):ℝ))) ≤ ((n1Hi 31:ℚ):ℝ) := by
  have hlo := hl 31; have hho := hh 31
  apply bn_channel_box ((bn1_weight 31 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 31 : ℚ):ℝ) ((bn1_glo 31 : ℚ):ℝ) ((bn1_ghi 31 : ℚ):ℝ) ((bn1_mean 31 : ℚ):ℝ) ((bn1_bias 31 : ℚ):ℝ) ((xLo 31:ℚ):ℝ) ((xHi 31:ℚ):ℝ) ((n1Lo 31:ℚ):ℝ) ((n1Hi 31:ℚ):ℝ) (x 31)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c32 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 32:ℚ):ℝ) ≤ ((bn1_bias 32 : ℚ):ℝ) + ((bn1_weight 32 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 32 : ℚ):ℝ) * (x 32 - ((bn1_mean 32 : ℚ):ℝ))) ∧
    ((bn1_bias 32 : ℚ):ℝ) + ((bn1_weight 32 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 32 : ℚ):ℝ) * (x 32 - ((bn1_mean 32 : ℚ):ℝ))) ≤ ((n1Hi 32:ℚ):ℝ) := by
  have hlo := hl 32; have hho := hh 32
  apply bn_channel_box ((bn1_weight 32 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 32 : ℚ):ℝ) ((bn1_glo 32 : ℚ):ℝ) ((bn1_ghi 32 : ℚ):ℝ) ((bn1_mean 32 : ℚ):ℝ) ((bn1_bias 32 : ℚ):ℝ) ((xLo 32:ℚ):ℝ) ((xHi 32:ℚ):ℝ) ((n1Lo 32:ℚ):ℝ) ((n1Hi 32:ℚ):ℝ) (x 32)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c33 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 33:ℚ):ℝ) ≤ ((bn1_bias 33 : ℚ):ℝ) + ((bn1_weight 33 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 33 : ℚ):ℝ) * (x 33 - ((bn1_mean 33 : ℚ):ℝ))) ∧
    ((bn1_bias 33 : ℚ):ℝ) + ((bn1_weight 33 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 33 : ℚ):ℝ) * (x 33 - ((bn1_mean 33 : ℚ):ℝ))) ≤ ((n1Hi 33:ℚ):ℝ) := by
  have hlo := hl 33; have hho := hh 33
  apply bn_channel_box ((bn1_weight 33 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 33 : ℚ):ℝ) ((bn1_glo 33 : ℚ):ℝ) ((bn1_ghi 33 : ℚ):ℝ) ((bn1_mean 33 : ℚ):ℝ) ((bn1_bias 33 : ℚ):ℝ) ((xLo 33:ℚ):ℝ) ((xHi 33:ℚ):ℝ) ((n1Lo 33:ℚ):ℝ) ((n1Hi 33:ℚ):ℝ) (x 33)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c34 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 34:ℚ):ℝ) ≤ ((bn1_bias 34 : ℚ):ℝ) + ((bn1_weight 34 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 34 : ℚ):ℝ) * (x 34 - ((bn1_mean 34 : ℚ):ℝ))) ∧
    ((bn1_bias 34 : ℚ):ℝ) + ((bn1_weight 34 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 34 : ℚ):ℝ) * (x 34 - ((bn1_mean 34 : ℚ):ℝ))) ≤ ((n1Hi 34:ℚ):ℝ) := by
  have hlo := hl 34; have hho := hh 34
  apply bn_channel_box ((bn1_weight 34 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 34 : ℚ):ℝ) ((bn1_glo 34 : ℚ):ℝ) ((bn1_ghi 34 : ℚ):ℝ) ((bn1_mean 34 : ℚ):ℝ) ((bn1_bias 34 : ℚ):ℝ) ((xLo 34:ℚ):ℝ) ((xHi 34:ℚ):ℝ) ((n1Lo 34:ℚ):ℝ) ((n1Hi 34:ℚ):ℝ) (x 34)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c35 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 35:ℚ):ℝ) ≤ ((bn1_bias 35 : ℚ):ℝ) + ((bn1_weight 35 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 35 : ℚ):ℝ) * (x 35 - ((bn1_mean 35 : ℚ):ℝ))) ∧
    ((bn1_bias 35 : ℚ):ℝ) + ((bn1_weight 35 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 35 : ℚ):ℝ) * (x 35 - ((bn1_mean 35 : ℚ):ℝ))) ≤ ((n1Hi 35:ℚ):ℝ) := by
  have hlo := hl 35; have hho := hh 35
  apply bn_channel_box ((bn1_weight 35 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 35 : ℚ):ℝ) ((bn1_glo 35 : ℚ):ℝ) ((bn1_ghi 35 : ℚ):ℝ) ((bn1_mean 35 : ℚ):ℝ) ((bn1_bias 35 : ℚ):ℝ) ((xLo 35:ℚ):ℝ) ((xHi 35:ℚ):ℝ) ((n1Lo 35:ℚ):ℝ) ((n1Hi 35:ℚ):ℝ) (x 35)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c36 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 36:ℚ):ℝ) ≤ ((bn1_bias 36 : ℚ):ℝ) + ((bn1_weight 36 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 36 : ℚ):ℝ) * (x 36 - ((bn1_mean 36 : ℚ):ℝ))) ∧
    ((bn1_bias 36 : ℚ):ℝ) + ((bn1_weight 36 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 36 : ℚ):ℝ) * (x 36 - ((bn1_mean 36 : ℚ):ℝ))) ≤ ((n1Hi 36:ℚ):ℝ) := by
  have hlo := hl 36; have hho := hh 36
  apply bn_channel_box ((bn1_weight 36 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 36 : ℚ):ℝ) ((bn1_glo 36 : ℚ):ℝ) ((bn1_ghi 36 : ℚ):ℝ) ((bn1_mean 36 : ℚ):ℝ) ((bn1_bias 36 : ℚ):ℝ) ((xLo 36:ℚ):ℝ) ((xHi 36:ℚ):ℝ) ((n1Lo 36:ℚ):ℝ) ((n1Hi 36:ℚ):ℝ) (x 36)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c37 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 37:ℚ):ℝ) ≤ ((bn1_bias 37 : ℚ):ℝ) + ((bn1_weight 37 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 37 : ℚ):ℝ) * (x 37 - ((bn1_mean 37 : ℚ):ℝ))) ∧
    ((bn1_bias 37 : ℚ):ℝ) + ((bn1_weight 37 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 37 : ℚ):ℝ) * (x 37 - ((bn1_mean 37 : ℚ):ℝ))) ≤ ((n1Hi 37:ℚ):ℝ) := by
  have hlo := hl 37; have hho := hh 37
  apply bn_channel_box ((bn1_weight 37 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 37 : ℚ):ℝ) ((bn1_glo 37 : ℚ):ℝ) ((bn1_ghi 37 : ℚ):ℝ) ((bn1_mean 37 : ℚ):ℝ) ((bn1_bias 37 : ℚ):ℝ) ((xLo 37:ℚ):ℝ) ((xHi 37:ℚ):ℝ) ((n1Lo 37:ℚ):ℝ) ((n1Hi 37:ℚ):ℝ) (x 37)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c38 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 38:ℚ):ℝ) ≤ ((bn1_bias 38 : ℚ):ℝ) + ((bn1_weight 38 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 38 : ℚ):ℝ) * (x 38 - ((bn1_mean 38 : ℚ):ℝ))) ∧
    ((bn1_bias 38 : ℚ):ℝ) + ((bn1_weight 38 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 38 : ℚ):ℝ) * (x 38 - ((bn1_mean 38 : ℚ):ℝ))) ≤ ((n1Hi 38:ℚ):ℝ) := by
  have hlo := hl 38; have hho := hh 38
  apply bn_channel_box ((bn1_weight 38 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 38 : ℚ):ℝ) ((bn1_glo 38 : ℚ):ℝ) ((bn1_ghi 38 : ℚ):ℝ) ((bn1_mean 38 : ℚ):ℝ) ((bn1_bias 38 : ℚ):ℝ) ((xLo 38:ℚ):ℝ) ((xHi 38:ℚ):ℝ) ((n1Lo 38:ℚ):ℝ) ((n1Hi 38:ℚ):ℝ) (x 38)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c39 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 39:ℚ):ℝ) ≤ ((bn1_bias 39 : ℚ):ℝ) + ((bn1_weight 39 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 39 : ℚ):ℝ) * (x 39 - ((bn1_mean 39 : ℚ):ℝ))) ∧
    ((bn1_bias 39 : ℚ):ℝ) + ((bn1_weight 39 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 39 : ℚ):ℝ) * (x 39 - ((bn1_mean 39 : ℚ):ℝ))) ≤ ((n1Hi 39:ℚ):ℝ) := by
  have hlo := hl 39; have hho := hh 39
  apply bn_channel_box ((bn1_weight 39 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 39 : ℚ):ℝ) ((bn1_glo 39 : ℚ):ℝ) ((bn1_ghi 39 : ℚ):ℝ) ((bn1_mean 39 : ℚ):ℝ) ((bn1_bias 39 : ℚ):ℝ) ((xLo 39:ℚ):ℝ) ((xHi 39:ℚ):ℝ) ((n1Lo 39:ℚ):ℝ) ((n1Hi 39:ℚ):ℝ) (x 39)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c40 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 40:ℚ):ℝ) ≤ ((bn1_bias 40 : ℚ):ℝ) + ((bn1_weight 40 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 40 : ℚ):ℝ) * (x 40 - ((bn1_mean 40 : ℚ):ℝ))) ∧
    ((bn1_bias 40 : ℚ):ℝ) + ((bn1_weight 40 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 40 : ℚ):ℝ) * (x 40 - ((bn1_mean 40 : ℚ):ℝ))) ≤ ((n1Hi 40:ℚ):ℝ) := by
  have hlo := hl 40; have hho := hh 40
  apply bn_channel_box ((bn1_weight 40 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 40 : ℚ):ℝ) ((bn1_glo 40 : ℚ):ℝ) ((bn1_ghi 40 : ℚ):ℝ) ((bn1_mean 40 : ℚ):ℝ) ((bn1_bias 40 : ℚ):ℝ) ((xLo 40:ℚ):ℝ) ((xHi 40:ℚ):ℝ) ((n1Lo 40:ℚ):ℝ) ((n1Hi 40:ℚ):ℝ) (x 40)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c41 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 41:ℚ):ℝ) ≤ ((bn1_bias 41 : ℚ):ℝ) + ((bn1_weight 41 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 41 : ℚ):ℝ) * (x 41 - ((bn1_mean 41 : ℚ):ℝ))) ∧
    ((bn1_bias 41 : ℚ):ℝ) + ((bn1_weight 41 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 41 : ℚ):ℝ) * (x 41 - ((bn1_mean 41 : ℚ):ℝ))) ≤ ((n1Hi 41:ℚ):ℝ) := by
  have hlo := hl 41; have hho := hh 41
  apply bn_channel_box ((bn1_weight 41 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 41 : ℚ):ℝ) ((bn1_glo 41 : ℚ):ℝ) ((bn1_ghi 41 : ℚ):ℝ) ((bn1_mean 41 : ℚ):ℝ) ((bn1_bias 41 : ℚ):ℝ) ((xLo 41:ℚ):ℝ) ((xHi 41:ℚ):ℝ) ((n1Lo 41:ℚ):ℝ) ((n1Hi 41:ℚ):ℝ) (x 41)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c42 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 42:ℚ):ℝ) ≤ ((bn1_bias 42 : ℚ):ℝ) + ((bn1_weight 42 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 42 : ℚ):ℝ) * (x 42 - ((bn1_mean 42 : ℚ):ℝ))) ∧
    ((bn1_bias 42 : ℚ):ℝ) + ((bn1_weight 42 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 42 : ℚ):ℝ) * (x 42 - ((bn1_mean 42 : ℚ):ℝ))) ≤ ((n1Hi 42:ℚ):ℝ) := by
  have hlo := hl 42; have hho := hh 42
  apply bn_channel_box ((bn1_weight 42 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 42 : ℚ):ℝ) ((bn1_glo 42 : ℚ):ℝ) ((bn1_ghi 42 : ℚ):ℝ) ((bn1_mean 42 : ℚ):ℝ) ((bn1_bias 42 : ℚ):ℝ) ((xLo 42:ℚ):ℝ) ((xHi 42:ℚ):ℝ) ((n1Lo 42:ℚ):ℝ) ((n1Hi 42:ℚ):ℝ) (x 42)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c43 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 43:ℚ):ℝ) ≤ ((bn1_bias 43 : ℚ):ℝ) + ((bn1_weight 43 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 43 : ℚ):ℝ) * (x 43 - ((bn1_mean 43 : ℚ):ℝ))) ∧
    ((bn1_bias 43 : ℚ):ℝ) + ((bn1_weight 43 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 43 : ℚ):ℝ) * (x 43 - ((bn1_mean 43 : ℚ):ℝ))) ≤ ((n1Hi 43:ℚ):ℝ) := by
  have hlo := hl 43; have hho := hh 43
  apply bn_channel_box ((bn1_weight 43 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 43 : ℚ):ℝ) ((bn1_glo 43 : ℚ):ℝ) ((bn1_ghi 43 : ℚ):ℝ) ((bn1_mean 43 : ℚ):ℝ) ((bn1_bias 43 : ℚ):ℝ) ((xLo 43:ℚ):ℝ) ((xHi 43:ℚ):ℝ) ((n1Lo 43:ℚ):ℝ) ((n1Hi 43:ℚ):ℝ) (x 43)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c44 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 44:ℚ):ℝ) ≤ ((bn1_bias 44 : ℚ):ℝ) + ((bn1_weight 44 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 44 : ℚ):ℝ) * (x 44 - ((bn1_mean 44 : ℚ):ℝ))) ∧
    ((bn1_bias 44 : ℚ):ℝ) + ((bn1_weight 44 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 44 : ℚ):ℝ) * (x 44 - ((bn1_mean 44 : ℚ):ℝ))) ≤ ((n1Hi 44:ℚ):ℝ) := by
  have hlo := hl 44; have hho := hh 44
  apply bn_channel_box ((bn1_weight 44 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 44 : ℚ):ℝ) ((bn1_glo 44 : ℚ):ℝ) ((bn1_ghi 44 : ℚ):ℝ) ((bn1_mean 44 : ℚ):ℝ) ((bn1_bias 44 : ℚ):ℝ) ((xLo 44:ℚ):ℝ) ((xHi 44:ℚ):ℝ) ((n1Lo 44:ℚ):ℝ) ((n1Hi 44:ℚ):ℝ) (x 44)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c45 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 45:ℚ):ℝ) ≤ ((bn1_bias 45 : ℚ):ℝ) + ((bn1_weight 45 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 45 : ℚ):ℝ) * (x 45 - ((bn1_mean 45 : ℚ):ℝ))) ∧
    ((bn1_bias 45 : ℚ):ℝ) + ((bn1_weight 45 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 45 : ℚ):ℝ) * (x 45 - ((bn1_mean 45 : ℚ):ℝ))) ≤ ((n1Hi 45:ℚ):ℝ) := by
  have hlo := hl 45; have hho := hh 45
  apply bn_channel_box ((bn1_weight 45 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 45 : ℚ):ℝ) ((bn1_glo 45 : ℚ):ℝ) ((bn1_ghi 45 : ℚ):ℝ) ((bn1_mean 45 : ℚ):ℝ) ((bn1_bias 45 : ℚ):ℝ) ((xLo 45:ℚ):ℝ) ((xHi 45:ℚ):ℝ) ((n1Lo 45:ℚ):ℝ) ((n1Hi 45:ℚ):ℝ) (x 45)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c46 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 46:ℚ):ℝ) ≤ ((bn1_bias 46 : ℚ):ℝ) + ((bn1_weight 46 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 46 : ℚ):ℝ) * (x 46 - ((bn1_mean 46 : ℚ):ℝ))) ∧
    ((bn1_bias 46 : ℚ):ℝ) + ((bn1_weight 46 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 46 : ℚ):ℝ) * (x 46 - ((bn1_mean 46 : ℚ):ℝ))) ≤ ((n1Hi 46:ℚ):ℝ) := by
  have hlo := hl 46; have hho := hh 46
  apply bn_channel_box ((bn1_weight 46 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 46 : ℚ):ℝ) ((bn1_glo 46 : ℚ):ℝ) ((bn1_ghi 46 : ℚ):ℝ) ((bn1_mean 46 : ℚ):ℝ) ((bn1_bias 46 : ℚ):ℝ) ((xLo 46:ℚ):ℝ) ((xHi 46:ℚ):ℝ) ((n1Lo 46:ℚ):ℝ) ((n1Hi 46:ℚ):ℝ) (x 46)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num

theorem bn1_c47 (x : Fin 48 → ℝ)
    (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((n1Lo 47:ℚ):ℝ) ≤ ((bn1_bias 47 : ℚ):ℝ) + ((bn1_weight 47 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 47 : ℚ):ℝ) * (x 47 - ((bn1_mean 47 : ℚ):ℝ))) ∧
    ((bn1_bias 47 : ℚ):ℝ) + ((bn1_weight 47 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 47 : ℚ):ℝ) * (x 47 - ((bn1_mean 47 : ℚ):ℝ))) ≤ ((n1Hi 47:ℚ):ℝ) := by
  have hlo := hl 47; have hho := hh 47
  apply bn_channel_box ((bn1_weight 47 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn1_var 47 : ℚ):ℝ) ((bn1_glo 47 : ℚ):ℝ) ((bn1_ghi 47 : ℚ):ℝ) ((bn1_mean 47 : ℚ):ℝ) ((bn1_bias 47 : ℚ):ℝ) ((xLo 47:ℚ):ℝ) ((xHi 47:ℚ):ℝ) ((n1Lo 47:ℚ):ℝ) ((n1Hi 47:ℚ):ℝ) (x 47)
  · push_cast [bn1_var]; norm_num
  · push_cast [bn1_glo]; norm_num
  · push_cast [bn1_ghi]; norm_num
  · push_cast [bn1_glo, bn1_var]; norm_num
  · push_cast [bn1_ghi, bn1_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n1Lo, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num
  · push_cast [n1Hi, bn1_bias, bn1_weight, bn1_glo, bn1_ghi, xLo, xHi, bn1_mean]; norm_num


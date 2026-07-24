import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem bn2_c0 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 0:ℚ):ℝ) ≤ ((bn2_bias 0 : ℚ):ℝ) + ((bn2_weight 0 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 0 : ℚ):ℝ) * (y 0 - ((bn2_mean 0 : ℚ):ℝ))) ∧
    ((bn2_bias 0 : ℚ):ℝ) + ((bn2_weight 0 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 0 : ℚ):ℝ) * (y 0 - ((bn2_mean 0 : ℚ):ℝ))) ≤ ((n2Hi 0:ℚ):ℝ) := by
  have hlo := hl 0; have hho := hh 0
  apply bn_channel_box ((bn2_weight 0 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 0 : ℚ):ℝ) ((bn2_glo 0 : ℚ):ℝ) ((bn2_ghi 0 : ℚ):ℝ) ((bn2_mean 0 : ℚ):ℝ) ((bn2_bias 0 : ℚ):ℝ) ((yLo 0:ℚ):ℝ) ((yHi 0:ℚ):ℝ) ((n2Lo 0:ℚ):ℝ) ((n2Hi 0:ℚ):ℝ) (y 0)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c1 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 1:ℚ):ℝ) ≤ ((bn2_bias 1 : ℚ):ℝ) + ((bn2_weight 1 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 1 : ℚ):ℝ) * (y 1 - ((bn2_mean 1 : ℚ):ℝ))) ∧
    ((bn2_bias 1 : ℚ):ℝ) + ((bn2_weight 1 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 1 : ℚ):ℝ) * (y 1 - ((bn2_mean 1 : ℚ):ℝ))) ≤ ((n2Hi 1:ℚ):ℝ) := by
  have hlo := hl 1; have hho := hh 1
  apply bn_channel_box ((bn2_weight 1 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 1 : ℚ):ℝ) ((bn2_glo 1 : ℚ):ℝ) ((bn2_ghi 1 : ℚ):ℝ) ((bn2_mean 1 : ℚ):ℝ) ((bn2_bias 1 : ℚ):ℝ) ((yLo 1:ℚ):ℝ) ((yHi 1:ℚ):ℝ) ((n2Lo 1:ℚ):ℝ) ((n2Hi 1:ℚ):ℝ) (y 1)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c2 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 2:ℚ):ℝ) ≤ ((bn2_bias 2 : ℚ):ℝ) + ((bn2_weight 2 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 2 : ℚ):ℝ) * (y 2 - ((bn2_mean 2 : ℚ):ℝ))) ∧
    ((bn2_bias 2 : ℚ):ℝ) + ((bn2_weight 2 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 2 : ℚ):ℝ) * (y 2 - ((bn2_mean 2 : ℚ):ℝ))) ≤ ((n2Hi 2:ℚ):ℝ) := by
  have hlo := hl 2; have hho := hh 2
  apply bn_channel_box ((bn2_weight 2 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 2 : ℚ):ℝ) ((bn2_glo 2 : ℚ):ℝ) ((bn2_ghi 2 : ℚ):ℝ) ((bn2_mean 2 : ℚ):ℝ) ((bn2_bias 2 : ℚ):ℝ) ((yLo 2:ℚ):ℝ) ((yHi 2:ℚ):ℝ) ((n2Lo 2:ℚ):ℝ) ((n2Hi 2:ℚ):ℝ) (y 2)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c3 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 3:ℚ):ℝ) ≤ ((bn2_bias 3 : ℚ):ℝ) + ((bn2_weight 3 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 3 : ℚ):ℝ) * (y 3 - ((bn2_mean 3 : ℚ):ℝ))) ∧
    ((bn2_bias 3 : ℚ):ℝ) + ((bn2_weight 3 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 3 : ℚ):ℝ) * (y 3 - ((bn2_mean 3 : ℚ):ℝ))) ≤ ((n2Hi 3:ℚ):ℝ) := by
  have hlo := hl 3; have hho := hh 3
  apply bn_channel_box ((bn2_weight 3 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 3 : ℚ):ℝ) ((bn2_glo 3 : ℚ):ℝ) ((bn2_ghi 3 : ℚ):ℝ) ((bn2_mean 3 : ℚ):ℝ) ((bn2_bias 3 : ℚ):ℝ) ((yLo 3:ℚ):ℝ) ((yHi 3:ℚ):ℝ) ((n2Lo 3:ℚ):ℝ) ((n2Hi 3:ℚ):ℝ) (y 3)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c4 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 4:ℚ):ℝ) ≤ ((bn2_bias 4 : ℚ):ℝ) + ((bn2_weight 4 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 4 : ℚ):ℝ) * (y 4 - ((bn2_mean 4 : ℚ):ℝ))) ∧
    ((bn2_bias 4 : ℚ):ℝ) + ((bn2_weight 4 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 4 : ℚ):ℝ) * (y 4 - ((bn2_mean 4 : ℚ):ℝ))) ≤ ((n2Hi 4:ℚ):ℝ) := by
  have hlo := hl 4; have hho := hh 4
  apply bn_channel_box ((bn2_weight 4 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 4 : ℚ):ℝ) ((bn2_glo 4 : ℚ):ℝ) ((bn2_ghi 4 : ℚ):ℝ) ((bn2_mean 4 : ℚ):ℝ) ((bn2_bias 4 : ℚ):ℝ) ((yLo 4:ℚ):ℝ) ((yHi 4:ℚ):ℝ) ((n2Lo 4:ℚ):ℝ) ((n2Hi 4:ℚ):ℝ) (y 4)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c5 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 5:ℚ):ℝ) ≤ ((bn2_bias 5 : ℚ):ℝ) + ((bn2_weight 5 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 5 : ℚ):ℝ) * (y 5 - ((bn2_mean 5 : ℚ):ℝ))) ∧
    ((bn2_bias 5 : ℚ):ℝ) + ((bn2_weight 5 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 5 : ℚ):ℝ) * (y 5 - ((bn2_mean 5 : ℚ):ℝ))) ≤ ((n2Hi 5:ℚ):ℝ) := by
  have hlo := hl 5; have hho := hh 5
  apply bn_channel_box ((bn2_weight 5 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 5 : ℚ):ℝ) ((bn2_glo 5 : ℚ):ℝ) ((bn2_ghi 5 : ℚ):ℝ) ((bn2_mean 5 : ℚ):ℝ) ((bn2_bias 5 : ℚ):ℝ) ((yLo 5:ℚ):ℝ) ((yHi 5:ℚ):ℝ) ((n2Lo 5:ℚ):ℝ) ((n2Hi 5:ℚ):ℝ) (y 5)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c6 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 6:ℚ):ℝ) ≤ ((bn2_bias 6 : ℚ):ℝ) + ((bn2_weight 6 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 6 : ℚ):ℝ) * (y 6 - ((bn2_mean 6 : ℚ):ℝ))) ∧
    ((bn2_bias 6 : ℚ):ℝ) + ((bn2_weight 6 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 6 : ℚ):ℝ) * (y 6 - ((bn2_mean 6 : ℚ):ℝ))) ≤ ((n2Hi 6:ℚ):ℝ) := by
  have hlo := hl 6; have hho := hh 6
  apply bn_channel_box ((bn2_weight 6 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 6 : ℚ):ℝ) ((bn2_glo 6 : ℚ):ℝ) ((bn2_ghi 6 : ℚ):ℝ) ((bn2_mean 6 : ℚ):ℝ) ((bn2_bias 6 : ℚ):ℝ) ((yLo 6:ℚ):ℝ) ((yHi 6:ℚ):ℝ) ((n2Lo 6:ℚ):ℝ) ((n2Hi 6:ℚ):ℝ) (y 6)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c7 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 7:ℚ):ℝ) ≤ ((bn2_bias 7 : ℚ):ℝ) + ((bn2_weight 7 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 7 : ℚ):ℝ) * (y 7 - ((bn2_mean 7 : ℚ):ℝ))) ∧
    ((bn2_bias 7 : ℚ):ℝ) + ((bn2_weight 7 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 7 : ℚ):ℝ) * (y 7 - ((bn2_mean 7 : ℚ):ℝ))) ≤ ((n2Hi 7:ℚ):ℝ) := by
  have hlo := hl 7; have hho := hh 7
  apply bn_channel_box ((bn2_weight 7 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 7 : ℚ):ℝ) ((bn2_glo 7 : ℚ):ℝ) ((bn2_ghi 7 : ℚ):ℝ) ((bn2_mean 7 : ℚ):ℝ) ((bn2_bias 7 : ℚ):ℝ) ((yLo 7:ℚ):ℝ) ((yHi 7:ℚ):ℝ) ((n2Lo 7:ℚ):ℝ) ((n2Hi 7:ℚ):ℝ) (y 7)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c8 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 8:ℚ):ℝ) ≤ ((bn2_bias 8 : ℚ):ℝ) + ((bn2_weight 8 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 8 : ℚ):ℝ) * (y 8 - ((bn2_mean 8 : ℚ):ℝ))) ∧
    ((bn2_bias 8 : ℚ):ℝ) + ((bn2_weight 8 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 8 : ℚ):ℝ) * (y 8 - ((bn2_mean 8 : ℚ):ℝ))) ≤ ((n2Hi 8:ℚ):ℝ) := by
  have hlo := hl 8; have hho := hh 8
  apply bn_channel_box ((bn2_weight 8 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 8 : ℚ):ℝ) ((bn2_glo 8 : ℚ):ℝ) ((bn2_ghi 8 : ℚ):ℝ) ((bn2_mean 8 : ℚ):ℝ) ((bn2_bias 8 : ℚ):ℝ) ((yLo 8:ℚ):ℝ) ((yHi 8:ℚ):ℝ) ((n2Lo 8:ℚ):ℝ) ((n2Hi 8:ℚ):ℝ) (y 8)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c9 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 9:ℚ):ℝ) ≤ ((bn2_bias 9 : ℚ):ℝ) + ((bn2_weight 9 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 9 : ℚ):ℝ) * (y 9 - ((bn2_mean 9 : ℚ):ℝ))) ∧
    ((bn2_bias 9 : ℚ):ℝ) + ((bn2_weight 9 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 9 : ℚ):ℝ) * (y 9 - ((bn2_mean 9 : ℚ):ℝ))) ≤ ((n2Hi 9:ℚ):ℝ) := by
  have hlo := hl 9; have hho := hh 9
  apply bn_channel_box ((bn2_weight 9 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 9 : ℚ):ℝ) ((bn2_glo 9 : ℚ):ℝ) ((bn2_ghi 9 : ℚ):ℝ) ((bn2_mean 9 : ℚ):ℝ) ((bn2_bias 9 : ℚ):ℝ) ((yLo 9:ℚ):ℝ) ((yHi 9:ℚ):ℝ) ((n2Lo 9:ℚ):ℝ) ((n2Hi 9:ℚ):ℝ) (y 9)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c10 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 10:ℚ):ℝ) ≤ ((bn2_bias 10 : ℚ):ℝ) + ((bn2_weight 10 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 10 : ℚ):ℝ) * (y 10 - ((bn2_mean 10 : ℚ):ℝ))) ∧
    ((bn2_bias 10 : ℚ):ℝ) + ((bn2_weight 10 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 10 : ℚ):ℝ) * (y 10 - ((bn2_mean 10 : ℚ):ℝ))) ≤ ((n2Hi 10:ℚ):ℝ) := by
  have hlo := hl 10; have hho := hh 10
  apply bn_channel_box ((bn2_weight 10 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 10 : ℚ):ℝ) ((bn2_glo 10 : ℚ):ℝ) ((bn2_ghi 10 : ℚ):ℝ) ((bn2_mean 10 : ℚ):ℝ) ((bn2_bias 10 : ℚ):ℝ) ((yLo 10:ℚ):ℝ) ((yHi 10:ℚ):ℝ) ((n2Lo 10:ℚ):ℝ) ((n2Hi 10:ℚ):ℝ) (y 10)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c11 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 11:ℚ):ℝ) ≤ ((bn2_bias 11 : ℚ):ℝ) + ((bn2_weight 11 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 11 : ℚ):ℝ) * (y 11 - ((bn2_mean 11 : ℚ):ℝ))) ∧
    ((bn2_bias 11 : ℚ):ℝ) + ((bn2_weight 11 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 11 : ℚ):ℝ) * (y 11 - ((bn2_mean 11 : ℚ):ℝ))) ≤ ((n2Hi 11:ℚ):ℝ) := by
  have hlo := hl 11; have hho := hh 11
  apply bn_channel_box ((bn2_weight 11 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 11 : ℚ):ℝ) ((bn2_glo 11 : ℚ):ℝ) ((bn2_ghi 11 : ℚ):ℝ) ((bn2_mean 11 : ℚ):ℝ) ((bn2_bias 11 : ℚ):ℝ) ((yLo 11:ℚ):ℝ) ((yHi 11:ℚ):ℝ) ((n2Lo 11:ℚ):ℝ) ((n2Hi 11:ℚ):ℝ) (y 11)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c12 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 12:ℚ):ℝ) ≤ ((bn2_bias 12 : ℚ):ℝ) + ((bn2_weight 12 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 12 : ℚ):ℝ) * (y 12 - ((bn2_mean 12 : ℚ):ℝ))) ∧
    ((bn2_bias 12 : ℚ):ℝ) + ((bn2_weight 12 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 12 : ℚ):ℝ) * (y 12 - ((bn2_mean 12 : ℚ):ℝ))) ≤ ((n2Hi 12:ℚ):ℝ) := by
  have hlo := hl 12; have hho := hh 12
  apply bn_channel_box ((bn2_weight 12 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 12 : ℚ):ℝ) ((bn2_glo 12 : ℚ):ℝ) ((bn2_ghi 12 : ℚ):ℝ) ((bn2_mean 12 : ℚ):ℝ) ((bn2_bias 12 : ℚ):ℝ) ((yLo 12:ℚ):ℝ) ((yHi 12:ℚ):ℝ) ((n2Lo 12:ℚ):ℝ) ((n2Hi 12:ℚ):ℝ) (y 12)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c13 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 13:ℚ):ℝ) ≤ ((bn2_bias 13 : ℚ):ℝ) + ((bn2_weight 13 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 13 : ℚ):ℝ) * (y 13 - ((bn2_mean 13 : ℚ):ℝ))) ∧
    ((bn2_bias 13 : ℚ):ℝ) + ((bn2_weight 13 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 13 : ℚ):ℝ) * (y 13 - ((bn2_mean 13 : ℚ):ℝ))) ≤ ((n2Hi 13:ℚ):ℝ) := by
  have hlo := hl 13; have hho := hh 13
  apply bn_channel_box ((bn2_weight 13 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 13 : ℚ):ℝ) ((bn2_glo 13 : ℚ):ℝ) ((bn2_ghi 13 : ℚ):ℝ) ((bn2_mean 13 : ℚ):ℝ) ((bn2_bias 13 : ℚ):ℝ) ((yLo 13:ℚ):ℝ) ((yHi 13:ℚ):ℝ) ((n2Lo 13:ℚ):ℝ) ((n2Hi 13:ℚ):ℝ) (y 13)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c14 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 14:ℚ):ℝ) ≤ ((bn2_bias 14 : ℚ):ℝ) + ((bn2_weight 14 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 14 : ℚ):ℝ) * (y 14 - ((bn2_mean 14 : ℚ):ℝ))) ∧
    ((bn2_bias 14 : ℚ):ℝ) + ((bn2_weight 14 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 14 : ℚ):ℝ) * (y 14 - ((bn2_mean 14 : ℚ):ℝ))) ≤ ((n2Hi 14:ℚ):ℝ) := by
  have hlo := hl 14; have hho := hh 14
  apply bn_channel_box ((bn2_weight 14 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 14 : ℚ):ℝ) ((bn2_glo 14 : ℚ):ℝ) ((bn2_ghi 14 : ℚ):ℝ) ((bn2_mean 14 : ℚ):ℝ) ((bn2_bias 14 : ℚ):ℝ) ((yLo 14:ℚ):ℝ) ((yHi 14:ℚ):ℝ) ((n2Lo 14:ℚ):ℝ) ((n2Hi 14:ℚ):ℝ) (y 14)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c15 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 15:ℚ):ℝ) ≤ ((bn2_bias 15 : ℚ):ℝ) + ((bn2_weight 15 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 15 : ℚ):ℝ) * (y 15 - ((bn2_mean 15 : ℚ):ℝ))) ∧
    ((bn2_bias 15 : ℚ):ℝ) + ((bn2_weight 15 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 15 : ℚ):ℝ) * (y 15 - ((bn2_mean 15 : ℚ):ℝ))) ≤ ((n2Hi 15:ℚ):ℝ) := by
  have hlo := hl 15; have hho := hh 15
  apply bn_channel_box ((bn2_weight 15 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 15 : ℚ):ℝ) ((bn2_glo 15 : ℚ):ℝ) ((bn2_ghi 15 : ℚ):ℝ) ((bn2_mean 15 : ℚ):ℝ) ((bn2_bias 15 : ℚ):ℝ) ((yLo 15:ℚ):ℝ) ((yHi 15:ℚ):ℝ) ((n2Lo 15:ℚ):ℝ) ((n2Hi 15:ℚ):ℝ) (y 15)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c16 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 16:ℚ):ℝ) ≤ ((bn2_bias 16 : ℚ):ℝ) + ((bn2_weight 16 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 16 : ℚ):ℝ) * (y 16 - ((bn2_mean 16 : ℚ):ℝ))) ∧
    ((bn2_bias 16 : ℚ):ℝ) + ((bn2_weight 16 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 16 : ℚ):ℝ) * (y 16 - ((bn2_mean 16 : ℚ):ℝ))) ≤ ((n2Hi 16:ℚ):ℝ) := by
  have hlo := hl 16; have hho := hh 16
  apply bn_channel_box ((bn2_weight 16 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 16 : ℚ):ℝ) ((bn2_glo 16 : ℚ):ℝ) ((bn2_ghi 16 : ℚ):ℝ) ((bn2_mean 16 : ℚ):ℝ) ((bn2_bias 16 : ℚ):ℝ) ((yLo 16:ℚ):ℝ) ((yHi 16:ℚ):ℝ) ((n2Lo 16:ℚ):ℝ) ((n2Hi 16:ℚ):ℝ) (y 16)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c17 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 17:ℚ):ℝ) ≤ ((bn2_bias 17 : ℚ):ℝ) + ((bn2_weight 17 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 17 : ℚ):ℝ) * (y 17 - ((bn2_mean 17 : ℚ):ℝ))) ∧
    ((bn2_bias 17 : ℚ):ℝ) + ((bn2_weight 17 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 17 : ℚ):ℝ) * (y 17 - ((bn2_mean 17 : ℚ):ℝ))) ≤ ((n2Hi 17:ℚ):ℝ) := by
  have hlo := hl 17; have hho := hh 17
  apply bn_channel_box ((bn2_weight 17 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 17 : ℚ):ℝ) ((bn2_glo 17 : ℚ):ℝ) ((bn2_ghi 17 : ℚ):ℝ) ((bn2_mean 17 : ℚ):ℝ) ((bn2_bias 17 : ℚ):ℝ) ((yLo 17:ℚ):ℝ) ((yHi 17:ℚ):ℝ) ((n2Lo 17:ℚ):ℝ) ((n2Hi 17:ℚ):ℝ) (y 17)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c18 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 18:ℚ):ℝ) ≤ ((bn2_bias 18 : ℚ):ℝ) + ((bn2_weight 18 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 18 : ℚ):ℝ) * (y 18 - ((bn2_mean 18 : ℚ):ℝ))) ∧
    ((bn2_bias 18 : ℚ):ℝ) + ((bn2_weight 18 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 18 : ℚ):ℝ) * (y 18 - ((bn2_mean 18 : ℚ):ℝ))) ≤ ((n2Hi 18:ℚ):ℝ) := by
  have hlo := hl 18; have hho := hh 18
  apply bn_channel_box ((bn2_weight 18 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 18 : ℚ):ℝ) ((bn2_glo 18 : ℚ):ℝ) ((bn2_ghi 18 : ℚ):ℝ) ((bn2_mean 18 : ℚ):ℝ) ((bn2_bias 18 : ℚ):ℝ) ((yLo 18:ℚ):ℝ) ((yHi 18:ℚ):ℝ) ((n2Lo 18:ℚ):ℝ) ((n2Hi 18:ℚ):ℝ) (y 18)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c19 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 19:ℚ):ℝ) ≤ ((bn2_bias 19 : ℚ):ℝ) + ((bn2_weight 19 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 19 : ℚ):ℝ) * (y 19 - ((bn2_mean 19 : ℚ):ℝ))) ∧
    ((bn2_bias 19 : ℚ):ℝ) + ((bn2_weight 19 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 19 : ℚ):ℝ) * (y 19 - ((bn2_mean 19 : ℚ):ℝ))) ≤ ((n2Hi 19:ℚ):ℝ) := by
  have hlo := hl 19; have hho := hh 19
  apply bn_channel_box ((bn2_weight 19 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 19 : ℚ):ℝ) ((bn2_glo 19 : ℚ):ℝ) ((bn2_ghi 19 : ℚ):ℝ) ((bn2_mean 19 : ℚ):ℝ) ((bn2_bias 19 : ℚ):ℝ) ((yLo 19:ℚ):ℝ) ((yHi 19:ℚ):ℝ) ((n2Lo 19:ℚ):ℝ) ((n2Hi 19:ℚ):ℝ) (y 19)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c20 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 20:ℚ):ℝ) ≤ ((bn2_bias 20 : ℚ):ℝ) + ((bn2_weight 20 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 20 : ℚ):ℝ) * (y 20 - ((bn2_mean 20 : ℚ):ℝ))) ∧
    ((bn2_bias 20 : ℚ):ℝ) + ((bn2_weight 20 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 20 : ℚ):ℝ) * (y 20 - ((bn2_mean 20 : ℚ):ℝ))) ≤ ((n2Hi 20:ℚ):ℝ) := by
  have hlo := hl 20; have hho := hh 20
  apply bn_channel_box ((bn2_weight 20 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 20 : ℚ):ℝ) ((bn2_glo 20 : ℚ):ℝ) ((bn2_ghi 20 : ℚ):ℝ) ((bn2_mean 20 : ℚ):ℝ) ((bn2_bias 20 : ℚ):ℝ) ((yLo 20:ℚ):ℝ) ((yHi 20:ℚ):ℝ) ((n2Lo 20:ℚ):ℝ) ((n2Hi 20:ℚ):ℝ) (y 20)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c21 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 21:ℚ):ℝ) ≤ ((bn2_bias 21 : ℚ):ℝ) + ((bn2_weight 21 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 21 : ℚ):ℝ) * (y 21 - ((bn2_mean 21 : ℚ):ℝ))) ∧
    ((bn2_bias 21 : ℚ):ℝ) + ((bn2_weight 21 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 21 : ℚ):ℝ) * (y 21 - ((bn2_mean 21 : ℚ):ℝ))) ≤ ((n2Hi 21:ℚ):ℝ) := by
  have hlo := hl 21; have hho := hh 21
  apply bn_channel_box ((bn2_weight 21 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 21 : ℚ):ℝ) ((bn2_glo 21 : ℚ):ℝ) ((bn2_ghi 21 : ℚ):ℝ) ((bn2_mean 21 : ℚ):ℝ) ((bn2_bias 21 : ℚ):ℝ) ((yLo 21:ℚ):ℝ) ((yHi 21:ℚ):ℝ) ((n2Lo 21:ℚ):ℝ) ((n2Hi 21:ℚ):ℝ) (y 21)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c22 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 22:ℚ):ℝ) ≤ ((bn2_bias 22 : ℚ):ℝ) + ((bn2_weight 22 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 22 : ℚ):ℝ) * (y 22 - ((bn2_mean 22 : ℚ):ℝ))) ∧
    ((bn2_bias 22 : ℚ):ℝ) + ((bn2_weight 22 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 22 : ℚ):ℝ) * (y 22 - ((bn2_mean 22 : ℚ):ℝ))) ≤ ((n2Hi 22:ℚ):ℝ) := by
  have hlo := hl 22; have hho := hh 22
  apply bn_channel_box ((bn2_weight 22 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 22 : ℚ):ℝ) ((bn2_glo 22 : ℚ):ℝ) ((bn2_ghi 22 : ℚ):ℝ) ((bn2_mean 22 : ℚ):ℝ) ((bn2_bias 22 : ℚ):ℝ) ((yLo 22:ℚ):ℝ) ((yHi 22:ℚ):ℝ) ((n2Lo 22:ℚ):ℝ) ((n2Hi 22:ℚ):ℝ) (y 22)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c23 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 23:ℚ):ℝ) ≤ ((bn2_bias 23 : ℚ):ℝ) + ((bn2_weight 23 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 23 : ℚ):ℝ) * (y 23 - ((bn2_mean 23 : ℚ):ℝ))) ∧
    ((bn2_bias 23 : ℚ):ℝ) + ((bn2_weight 23 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 23 : ℚ):ℝ) * (y 23 - ((bn2_mean 23 : ℚ):ℝ))) ≤ ((n2Hi 23:ℚ):ℝ) := by
  have hlo := hl 23; have hho := hh 23
  apply bn_channel_box ((bn2_weight 23 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 23 : ℚ):ℝ) ((bn2_glo 23 : ℚ):ℝ) ((bn2_ghi 23 : ℚ):ℝ) ((bn2_mean 23 : ℚ):ℝ) ((bn2_bias 23 : ℚ):ℝ) ((yLo 23:ℚ):ℝ) ((yHi 23:ℚ):ℝ) ((n2Lo 23:ℚ):ℝ) ((n2Hi 23:ℚ):ℝ) (y 23)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c24 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 24:ℚ):ℝ) ≤ ((bn2_bias 24 : ℚ):ℝ) + ((bn2_weight 24 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 24 : ℚ):ℝ) * (y 24 - ((bn2_mean 24 : ℚ):ℝ))) ∧
    ((bn2_bias 24 : ℚ):ℝ) + ((bn2_weight 24 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 24 : ℚ):ℝ) * (y 24 - ((bn2_mean 24 : ℚ):ℝ))) ≤ ((n2Hi 24:ℚ):ℝ) := by
  have hlo := hl 24; have hho := hh 24
  apply bn_channel_box ((bn2_weight 24 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 24 : ℚ):ℝ) ((bn2_glo 24 : ℚ):ℝ) ((bn2_ghi 24 : ℚ):ℝ) ((bn2_mean 24 : ℚ):ℝ) ((bn2_bias 24 : ℚ):ℝ) ((yLo 24:ℚ):ℝ) ((yHi 24:ℚ):ℝ) ((n2Lo 24:ℚ):ℝ) ((n2Hi 24:ℚ):ℝ) (y 24)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c25 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 25:ℚ):ℝ) ≤ ((bn2_bias 25 : ℚ):ℝ) + ((bn2_weight 25 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 25 : ℚ):ℝ) * (y 25 - ((bn2_mean 25 : ℚ):ℝ))) ∧
    ((bn2_bias 25 : ℚ):ℝ) + ((bn2_weight 25 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 25 : ℚ):ℝ) * (y 25 - ((bn2_mean 25 : ℚ):ℝ))) ≤ ((n2Hi 25:ℚ):ℝ) := by
  have hlo := hl 25; have hho := hh 25
  apply bn_channel_box ((bn2_weight 25 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 25 : ℚ):ℝ) ((bn2_glo 25 : ℚ):ℝ) ((bn2_ghi 25 : ℚ):ℝ) ((bn2_mean 25 : ℚ):ℝ) ((bn2_bias 25 : ℚ):ℝ) ((yLo 25:ℚ):ℝ) ((yHi 25:ℚ):ℝ) ((n2Lo 25:ℚ):ℝ) ((n2Hi 25:ℚ):ℝ) (y 25)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c26 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 26:ℚ):ℝ) ≤ ((bn2_bias 26 : ℚ):ℝ) + ((bn2_weight 26 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 26 : ℚ):ℝ) * (y 26 - ((bn2_mean 26 : ℚ):ℝ))) ∧
    ((bn2_bias 26 : ℚ):ℝ) + ((bn2_weight 26 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 26 : ℚ):ℝ) * (y 26 - ((bn2_mean 26 : ℚ):ℝ))) ≤ ((n2Hi 26:ℚ):ℝ) := by
  have hlo := hl 26; have hho := hh 26
  apply bn_channel_box ((bn2_weight 26 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 26 : ℚ):ℝ) ((bn2_glo 26 : ℚ):ℝ) ((bn2_ghi 26 : ℚ):ℝ) ((bn2_mean 26 : ℚ):ℝ) ((bn2_bias 26 : ℚ):ℝ) ((yLo 26:ℚ):ℝ) ((yHi 26:ℚ):ℝ) ((n2Lo 26:ℚ):ℝ) ((n2Hi 26:ℚ):ℝ) (y 26)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c27 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 27:ℚ):ℝ) ≤ ((bn2_bias 27 : ℚ):ℝ) + ((bn2_weight 27 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 27 : ℚ):ℝ) * (y 27 - ((bn2_mean 27 : ℚ):ℝ))) ∧
    ((bn2_bias 27 : ℚ):ℝ) + ((bn2_weight 27 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 27 : ℚ):ℝ) * (y 27 - ((bn2_mean 27 : ℚ):ℝ))) ≤ ((n2Hi 27:ℚ):ℝ) := by
  have hlo := hl 27; have hho := hh 27
  apply bn_channel_box ((bn2_weight 27 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 27 : ℚ):ℝ) ((bn2_glo 27 : ℚ):ℝ) ((bn2_ghi 27 : ℚ):ℝ) ((bn2_mean 27 : ℚ):ℝ) ((bn2_bias 27 : ℚ):ℝ) ((yLo 27:ℚ):ℝ) ((yHi 27:ℚ):ℝ) ((n2Lo 27:ℚ):ℝ) ((n2Hi 27:ℚ):ℝ) (y 27)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c28 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 28:ℚ):ℝ) ≤ ((bn2_bias 28 : ℚ):ℝ) + ((bn2_weight 28 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 28 : ℚ):ℝ) * (y 28 - ((bn2_mean 28 : ℚ):ℝ))) ∧
    ((bn2_bias 28 : ℚ):ℝ) + ((bn2_weight 28 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 28 : ℚ):ℝ) * (y 28 - ((bn2_mean 28 : ℚ):ℝ))) ≤ ((n2Hi 28:ℚ):ℝ) := by
  have hlo := hl 28; have hho := hh 28
  apply bn_channel_box ((bn2_weight 28 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 28 : ℚ):ℝ) ((bn2_glo 28 : ℚ):ℝ) ((bn2_ghi 28 : ℚ):ℝ) ((bn2_mean 28 : ℚ):ℝ) ((bn2_bias 28 : ℚ):ℝ) ((yLo 28:ℚ):ℝ) ((yHi 28:ℚ):ℝ) ((n2Lo 28:ℚ):ℝ) ((n2Hi 28:ℚ):ℝ) (y 28)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c29 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 29:ℚ):ℝ) ≤ ((bn2_bias 29 : ℚ):ℝ) + ((bn2_weight 29 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 29 : ℚ):ℝ) * (y 29 - ((bn2_mean 29 : ℚ):ℝ))) ∧
    ((bn2_bias 29 : ℚ):ℝ) + ((bn2_weight 29 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 29 : ℚ):ℝ) * (y 29 - ((bn2_mean 29 : ℚ):ℝ))) ≤ ((n2Hi 29:ℚ):ℝ) := by
  have hlo := hl 29; have hho := hh 29
  apply bn_channel_box ((bn2_weight 29 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 29 : ℚ):ℝ) ((bn2_glo 29 : ℚ):ℝ) ((bn2_ghi 29 : ℚ):ℝ) ((bn2_mean 29 : ℚ):ℝ) ((bn2_bias 29 : ℚ):ℝ) ((yLo 29:ℚ):ℝ) ((yHi 29:ℚ):ℝ) ((n2Lo 29:ℚ):ℝ) ((n2Hi 29:ℚ):ℝ) (y 29)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c30 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 30:ℚ):ℝ) ≤ ((bn2_bias 30 : ℚ):ℝ) + ((bn2_weight 30 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 30 : ℚ):ℝ) * (y 30 - ((bn2_mean 30 : ℚ):ℝ))) ∧
    ((bn2_bias 30 : ℚ):ℝ) + ((bn2_weight 30 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 30 : ℚ):ℝ) * (y 30 - ((bn2_mean 30 : ℚ):ℝ))) ≤ ((n2Hi 30:ℚ):ℝ) := by
  have hlo := hl 30; have hho := hh 30
  apply bn_channel_box ((bn2_weight 30 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 30 : ℚ):ℝ) ((bn2_glo 30 : ℚ):ℝ) ((bn2_ghi 30 : ℚ):ℝ) ((bn2_mean 30 : ℚ):ℝ) ((bn2_bias 30 : ℚ):ℝ) ((yLo 30:ℚ):ℝ) ((yHi 30:ℚ):ℝ) ((n2Lo 30:ℚ):ℝ) ((n2Hi 30:ℚ):ℝ) (y 30)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c31 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 31:ℚ):ℝ) ≤ ((bn2_bias 31 : ℚ):ℝ) + ((bn2_weight 31 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 31 : ℚ):ℝ) * (y 31 - ((bn2_mean 31 : ℚ):ℝ))) ∧
    ((bn2_bias 31 : ℚ):ℝ) + ((bn2_weight 31 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 31 : ℚ):ℝ) * (y 31 - ((bn2_mean 31 : ℚ):ℝ))) ≤ ((n2Hi 31:ℚ):ℝ) := by
  have hlo := hl 31; have hho := hh 31
  apply bn_channel_box ((bn2_weight 31 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 31 : ℚ):ℝ) ((bn2_glo 31 : ℚ):ℝ) ((bn2_ghi 31 : ℚ):ℝ) ((bn2_mean 31 : ℚ):ℝ) ((bn2_bias 31 : ℚ):ℝ) ((yLo 31:ℚ):ℝ) ((yHi 31:ℚ):ℝ) ((n2Lo 31:ℚ):ℝ) ((n2Hi 31:ℚ):ℝ) (y 31)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c32 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 32:ℚ):ℝ) ≤ ((bn2_bias 32 : ℚ):ℝ) + ((bn2_weight 32 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 32 : ℚ):ℝ) * (y 32 - ((bn2_mean 32 : ℚ):ℝ))) ∧
    ((bn2_bias 32 : ℚ):ℝ) + ((bn2_weight 32 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 32 : ℚ):ℝ) * (y 32 - ((bn2_mean 32 : ℚ):ℝ))) ≤ ((n2Hi 32:ℚ):ℝ) := by
  have hlo := hl 32; have hho := hh 32
  apply bn_channel_box ((bn2_weight 32 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 32 : ℚ):ℝ) ((bn2_glo 32 : ℚ):ℝ) ((bn2_ghi 32 : ℚ):ℝ) ((bn2_mean 32 : ℚ):ℝ) ((bn2_bias 32 : ℚ):ℝ) ((yLo 32:ℚ):ℝ) ((yHi 32:ℚ):ℝ) ((n2Lo 32:ℚ):ℝ) ((n2Hi 32:ℚ):ℝ) (y 32)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c33 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 33:ℚ):ℝ) ≤ ((bn2_bias 33 : ℚ):ℝ) + ((bn2_weight 33 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 33 : ℚ):ℝ) * (y 33 - ((bn2_mean 33 : ℚ):ℝ))) ∧
    ((bn2_bias 33 : ℚ):ℝ) + ((bn2_weight 33 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 33 : ℚ):ℝ) * (y 33 - ((bn2_mean 33 : ℚ):ℝ))) ≤ ((n2Hi 33:ℚ):ℝ) := by
  have hlo := hl 33; have hho := hh 33
  apply bn_channel_box ((bn2_weight 33 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 33 : ℚ):ℝ) ((bn2_glo 33 : ℚ):ℝ) ((bn2_ghi 33 : ℚ):ℝ) ((bn2_mean 33 : ℚ):ℝ) ((bn2_bias 33 : ℚ):ℝ) ((yLo 33:ℚ):ℝ) ((yHi 33:ℚ):ℝ) ((n2Lo 33:ℚ):ℝ) ((n2Hi 33:ℚ):ℝ) (y 33)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c34 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 34:ℚ):ℝ) ≤ ((bn2_bias 34 : ℚ):ℝ) + ((bn2_weight 34 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 34 : ℚ):ℝ) * (y 34 - ((bn2_mean 34 : ℚ):ℝ))) ∧
    ((bn2_bias 34 : ℚ):ℝ) + ((bn2_weight 34 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 34 : ℚ):ℝ) * (y 34 - ((bn2_mean 34 : ℚ):ℝ))) ≤ ((n2Hi 34:ℚ):ℝ) := by
  have hlo := hl 34; have hho := hh 34
  apply bn_channel_box ((bn2_weight 34 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 34 : ℚ):ℝ) ((bn2_glo 34 : ℚ):ℝ) ((bn2_ghi 34 : ℚ):ℝ) ((bn2_mean 34 : ℚ):ℝ) ((bn2_bias 34 : ℚ):ℝ) ((yLo 34:ℚ):ℝ) ((yHi 34:ℚ):ℝ) ((n2Lo 34:ℚ):ℝ) ((n2Hi 34:ℚ):ℝ) (y 34)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c35 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 35:ℚ):ℝ) ≤ ((bn2_bias 35 : ℚ):ℝ) + ((bn2_weight 35 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 35 : ℚ):ℝ) * (y 35 - ((bn2_mean 35 : ℚ):ℝ))) ∧
    ((bn2_bias 35 : ℚ):ℝ) + ((bn2_weight 35 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 35 : ℚ):ℝ) * (y 35 - ((bn2_mean 35 : ℚ):ℝ))) ≤ ((n2Hi 35:ℚ):ℝ) := by
  have hlo := hl 35; have hho := hh 35
  apply bn_channel_box ((bn2_weight 35 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 35 : ℚ):ℝ) ((bn2_glo 35 : ℚ):ℝ) ((bn2_ghi 35 : ℚ):ℝ) ((bn2_mean 35 : ℚ):ℝ) ((bn2_bias 35 : ℚ):ℝ) ((yLo 35:ℚ):ℝ) ((yHi 35:ℚ):ℝ) ((n2Lo 35:ℚ):ℝ) ((n2Hi 35:ℚ):ℝ) (y 35)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c36 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 36:ℚ):ℝ) ≤ ((bn2_bias 36 : ℚ):ℝ) + ((bn2_weight 36 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 36 : ℚ):ℝ) * (y 36 - ((bn2_mean 36 : ℚ):ℝ))) ∧
    ((bn2_bias 36 : ℚ):ℝ) + ((bn2_weight 36 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 36 : ℚ):ℝ) * (y 36 - ((bn2_mean 36 : ℚ):ℝ))) ≤ ((n2Hi 36:ℚ):ℝ) := by
  have hlo := hl 36; have hho := hh 36
  apply bn_channel_box ((bn2_weight 36 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 36 : ℚ):ℝ) ((bn2_glo 36 : ℚ):ℝ) ((bn2_ghi 36 : ℚ):ℝ) ((bn2_mean 36 : ℚ):ℝ) ((bn2_bias 36 : ℚ):ℝ) ((yLo 36:ℚ):ℝ) ((yHi 36:ℚ):ℝ) ((n2Lo 36:ℚ):ℝ) ((n2Hi 36:ℚ):ℝ) (y 36)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c37 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 37:ℚ):ℝ) ≤ ((bn2_bias 37 : ℚ):ℝ) + ((bn2_weight 37 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 37 : ℚ):ℝ) * (y 37 - ((bn2_mean 37 : ℚ):ℝ))) ∧
    ((bn2_bias 37 : ℚ):ℝ) + ((bn2_weight 37 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 37 : ℚ):ℝ) * (y 37 - ((bn2_mean 37 : ℚ):ℝ))) ≤ ((n2Hi 37:ℚ):ℝ) := by
  have hlo := hl 37; have hho := hh 37
  apply bn_channel_box ((bn2_weight 37 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 37 : ℚ):ℝ) ((bn2_glo 37 : ℚ):ℝ) ((bn2_ghi 37 : ℚ):ℝ) ((bn2_mean 37 : ℚ):ℝ) ((bn2_bias 37 : ℚ):ℝ) ((yLo 37:ℚ):ℝ) ((yHi 37:ℚ):ℝ) ((n2Lo 37:ℚ):ℝ) ((n2Hi 37:ℚ):ℝ) (y 37)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c38 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 38:ℚ):ℝ) ≤ ((bn2_bias 38 : ℚ):ℝ) + ((bn2_weight 38 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 38 : ℚ):ℝ) * (y 38 - ((bn2_mean 38 : ℚ):ℝ))) ∧
    ((bn2_bias 38 : ℚ):ℝ) + ((bn2_weight 38 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 38 : ℚ):ℝ) * (y 38 - ((bn2_mean 38 : ℚ):ℝ))) ≤ ((n2Hi 38:ℚ):ℝ) := by
  have hlo := hl 38; have hho := hh 38
  apply bn_channel_box ((bn2_weight 38 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 38 : ℚ):ℝ) ((bn2_glo 38 : ℚ):ℝ) ((bn2_ghi 38 : ℚ):ℝ) ((bn2_mean 38 : ℚ):ℝ) ((bn2_bias 38 : ℚ):ℝ) ((yLo 38:ℚ):ℝ) ((yHi 38:ℚ):ℝ) ((n2Lo 38:ℚ):ℝ) ((n2Hi 38:ℚ):ℝ) (y 38)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c39 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 39:ℚ):ℝ) ≤ ((bn2_bias 39 : ℚ):ℝ) + ((bn2_weight 39 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 39 : ℚ):ℝ) * (y 39 - ((bn2_mean 39 : ℚ):ℝ))) ∧
    ((bn2_bias 39 : ℚ):ℝ) + ((bn2_weight 39 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 39 : ℚ):ℝ) * (y 39 - ((bn2_mean 39 : ℚ):ℝ))) ≤ ((n2Hi 39:ℚ):ℝ) := by
  have hlo := hl 39; have hho := hh 39
  apply bn_channel_box ((bn2_weight 39 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 39 : ℚ):ℝ) ((bn2_glo 39 : ℚ):ℝ) ((bn2_ghi 39 : ℚ):ℝ) ((bn2_mean 39 : ℚ):ℝ) ((bn2_bias 39 : ℚ):ℝ) ((yLo 39:ℚ):ℝ) ((yHi 39:ℚ):ℝ) ((n2Lo 39:ℚ):ℝ) ((n2Hi 39:ℚ):ℝ) (y 39)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c40 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 40:ℚ):ℝ) ≤ ((bn2_bias 40 : ℚ):ℝ) + ((bn2_weight 40 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 40 : ℚ):ℝ) * (y 40 - ((bn2_mean 40 : ℚ):ℝ))) ∧
    ((bn2_bias 40 : ℚ):ℝ) + ((bn2_weight 40 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 40 : ℚ):ℝ) * (y 40 - ((bn2_mean 40 : ℚ):ℝ))) ≤ ((n2Hi 40:ℚ):ℝ) := by
  have hlo := hl 40; have hho := hh 40
  apply bn_channel_box ((bn2_weight 40 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 40 : ℚ):ℝ) ((bn2_glo 40 : ℚ):ℝ) ((bn2_ghi 40 : ℚ):ℝ) ((bn2_mean 40 : ℚ):ℝ) ((bn2_bias 40 : ℚ):ℝ) ((yLo 40:ℚ):ℝ) ((yHi 40:ℚ):ℝ) ((n2Lo 40:ℚ):ℝ) ((n2Hi 40:ℚ):ℝ) (y 40)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c41 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 41:ℚ):ℝ) ≤ ((bn2_bias 41 : ℚ):ℝ) + ((bn2_weight 41 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 41 : ℚ):ℝ) * (y 41 - ((bn2_mean 41 : ℚ):ℝ))) ∧
    ((bn2_bias 41 : ℚ):ℝ) + ((bn2_weight 41 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 41 : ℚ):ℝ) * (y 41 - ((bn2_mean 41 : ℚ):ℝ))) ≤ ((n2Hi 41:ℚ):ℝ) := by
  have hlo := hl 41; have hho := hh 41
  apply bn_channel_box ((bn2_weight 41 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 41 : ℚ):ℝ) ((bn2_glo 41 : ℚ):ℝ) ((bn2_ghi 41 : ℚ):ℝ) ((bn2_mean 41 : ℚ):ℝ) ((bn2_bias 41 : ℚ):ℝ) ((yLo 41:ℚ):ℝ) ((yHi 41:ℚ):ℝ) ((n2Lo 41:ℚ):ℝ) ((n2Hi 41:ℚ):ℝ) (y 41)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c42 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 42:ℚ):ℝ) ≤ ((bn2_bias 42 : ℚ):ℝ) + ((bn2_weight 42 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 42 : ℚ):ℝ) * (y 42 - ((bn2_mean 42 : ℚ):ℝ))) ∧
    ((bn2_bias 42 : ℚ):ℝ) + ((bn2_weight 42 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 42 : ℚ):ℝ) * (y 42 - ((bn2_mean 42 : ℚ):ℝ))) ≤ ((n2Hi 42:ℚ):ℝ) := by
  have hlo := hl 42; have hho := hh 42
  apply bn_channel_box ((bn2_weight 42 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 42 : ℚ):ℝ) ((bn2_glo 42 : ℚ):ℝ) ((bn2_ghi 42 : ℚ):ℝ) ((bn2_mean 42 : ℚ):ℝ) ((bn2_bias 42 : ℚ):ℝ) ((yLo 42:ℚ):ℝ) ((yHi 42:ℚ):ℝ) ((n2Lo 42:ℚ):ℝ) ((n2Hi 42:ℚ):ℝ) (y 42)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c43 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 43:ℚ):ℝ) ≤ ((bn2_bias 43 : ℚ):ℝ) + ((bn2_weight 43 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 43 : ℚ):ℝ) * (y 43 - ((bn2_mean 43 : ℚ):ℝ))) ∧
    ((bn2_bias 43 : ℚ):ℝ) + ((bn2_weight 43 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 43 : ℚ):ℝ) * (y 43 - ((bn2_mean 43 : ℚ):ℝ))) ≤ ((n2Hi 43:ℚ):ℝ) := by
  have hlo := hl 43; have hho := hh 43
  apply bn_channel_box ((bn2_weight 43 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 43 : ℚ):ℝ) ((bn2_glo 43 : ℚ):ℝ) ((bn2_ghi 43 : ℚ):ℝ) ((bn2_mean 43 : ℚ):ℝ) ((bn2_bias 43 : ℚ):ℝ) ((yLo 43:ℚ):ℝ) ((yHi 43:ℚ):ℝ) ((n2Lo 43:ℚ):ℝ) ((n2Hi 43:ℚ):ℝ) (y 43)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c44 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 44:ℚ):ℝ) ≤ ((bn2_bias 44 : ℚ):ℝ) + ((bn2_weight 44 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 44 : ℚ):ℝ) * (y 44 - ((bn2_mean 44 : ℚ):ℝ))) ∧
    ((bn2_bias 44 : ℚ):ℝ) + ((bn2_weight 44 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 44 : ℚ):ℝ) * (y 44 - ((bn2_mean 44 : ℚ):ℝ))) ≤ ((n2Hi 44:ℚ):ℝ) := by
  have hlo := hl 44; have hho := hh 44
  apply bn_channel_box ((bn2_weight 44 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 44 : ℚ):ℝ) ((bn2_glo 44 : ℚ):ℝ) ((bn2_ghi 44 : ℚ):ℝ) ((bn2_mean 44 : ℚ):ℝ) ((bn2_bias 44 : ℚ):ℝ) ((yLo 44:ℚ):ℝ) ((yHi 44:ℚ):ℝ) ((n2Lo 44:ℚ):ℝ) ((n2Hi 44:ℚ):ℝ) (y 44)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c45 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 45:ℚ):ℝ) ≤ ((bn2_bias 45 : ℚ):ℝ) + ((bn2_weight 45 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 45 : ℚ):ℝ) * (y 45 - ((bn2_mean 45 : ℚ):ℝ))) ∧
    ((bn2_bias 45 : ℚ):ℝ) + ((bn2_weight 45 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 45 : ℚ):ℝ) * (y 45 - ((bn2_mean 45 : ℚ):ℝ))) ≤ ((n2Hi 45:ℚ):ℝ) := by
  have hlo := hl 45; have hho := hh 45
  apply bn_channel_box ((bn2_weight 45 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 45 : ℚ):ℝ) ((bn2_glo 45 : ℚ):ℝ) ((bn2_ghi 45 : ℚ):ℝ) ((bn2_mean 45 : ℚ):ℝ) ((bn2_bias 45 : ℚ):ℝ) ((yLo 45:ℚ):ℝ) ((yHi 45:ℚ):ℝ) ((n2Lo 45:ℚ):ℝ) ((n2Hi 45:ℚ):ℝ) (y 45)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c46 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 46:ℚ):ℝ) ≤ ((bn2_bias 46 : ℚ):ℝ) + ((bn2_weight 46 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 46 : ℚ):ℝ) * (y 46 - ((bn2_mean 46 : ℚ):ℝ))) ∧
    ((bn2_bias 46 : ℚ):ℝ) + ((bn2_weight 46 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 46 : ℚ):ℝ) * (y 46 - ((bn2_mean 46 : ℚ):ℝ))) ≤ ((n2Hi 46:ℚ):ℝ) := by
  have hlo := hl 46; have hho := hh 46
  apply bn_channel_box ((bn2_weight 46 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 46 : ℚ):ℝ) ((bn2_glo 46 : ℚ):ℝ) ((bn2_ghi 46 : ℚ):ℝ) ((bn2_mean 46 : ℚ):ℝ) ((bn2_bias 46 : ℚ):ℝ) ((yLo 46:ℚ):ℝ) ((yHi 46:ℚ):ℝ) ((n2Lo 46:ℚ):ℝ) ((n2Hi 46:ℚ):ℝ) (y 46)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num

theorem bn2_c47 (y : Fin 48 → ℝ)
    (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ((n2Lo 47:ℚ):ℝ) ≤ ((bn2_bias 47 : ℚ):ℝ) + ((bn2_weight 47 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 47 : ℚ):ℝ) * (y 47 - ((bn2_mean 47 : ℚ):ℝ))) ∧
    ((bn2_bias 47 : ℚ):ℝ) + ((bn2_weight 47 : ℚ):ℝ) * (rsqrt ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 47 : ℚ):ℝ) * (y 47 - ((bn2_mean 47 : ℚ):ℝ))) ≤ ((n2Hi 47:ℚ):ℝ) := by
  have hlo := hl 47; have hho := hh 47
  apply bn_channel_box ((bn2_weight 47 : ℚ):ℝ) ((2748779/274877906944 : ℚ):ℝ) ((bn2_var 47 : ℚ):ℝ) ((bn2_glo 47 : ℚ):ℝ) ((bn2_ghi 47 : ℚ):ℝ) ((bn2_mean 47 : ℚ):ℝ) ((bn2_bias 47 : ℚ):ℝ) ((yLo 47:ℚ):ℝ) ((yHi 47:ℚ):ℝ) ((n2Lo 47:ℚ):ℝ) ((n2Hi 47:ℚ):ℝ) (y 47)
  · push_cast [bn2_var]; norm_num
  · push_cast [bn2_glo]; norm_num
  · push_cast [bn2_ghi]; norm_num
  · push_cast [bn2_glo, bn2_var]; norm_num
  · push_cast [bn2_ghi, bn2_var]; norm_num
  · exact hlo
  · exact hho
  · push_cast [n2Lo, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num
  · push_cast [n2Hi, bn2_bias, bn2_weight, bn2_glo, bn2_ghi, yLo, yHi, bn2_mean]; norm_num


import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem hid_c0 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 0:ℚ):ℝ) ≤ (((-6872831/16777216):ℚ):ℝ) + ∑ jj, ((W1_0 jj:ℚ):ℝ) * n2 jj ∧
    (((-6872831/16777216):ℚ):ℝ) + ∑ jj, ((W1_0 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 0:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_0 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 0:ℚ):ℝ) - (((-6872831/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_0 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_0 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_0, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_0 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_0 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 0:ℚ):ℝ) - (((-6872831/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_0, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c1 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 1:ℚ):ℝ) ≤ (((-13352245/16777216):ℚ):ℝ) + ∑ jj, ((W1_1 jj:ℚ):ℝ) * n2 jj ∧
    (((-13352245/16777216):ℚ):ℝ) + ∑ jj, ((W1_1 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 1:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_1 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 1:ℚ):ℝ) - (((-13352245/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_1 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_1 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_1, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_1 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_1 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 1:ℚ):ℝ) - (((-13352245/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_1, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c2 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 2:ℚ):ℝ) ≤ (((-3647675/134217728):ℚ):ℝ) + ∑ jj, ((W1_2 jj:ℚ):ℝ) * n2 jj ∧
    (((-3647675/134217728):ℚ):ℝ) + ∑ jj, ((W1_2 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 2:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_2 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 2:ℚ):ℝ) - (((-3647675/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_2 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_2 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_2, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_2 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_2 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 2:ℚ):ℝ) - (((-3647675/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_2, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c3 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 3:ℚ):ℝ) ≤ (((-6609297/8388608):ℚ):ℝ) + ∑ jj, ((W1_3 jj:ℚ):ℝ) * n2 jj ∧
    (((-6609297/8388608):ℚ):ℝ) + ∑ jj, ((W1_3 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 3:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_3 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 3:ℚ):ℝ) - (((-6609297/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_3 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_3 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_3, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_3 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_3 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 3:ℚ):ℝ) - (((-6609297/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_3, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c4 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 4:ℚ):ℝ) ≤ (((-2793161/33554432):ℚ):ℝ) + ∑ jj, ((W1_4 jj:ℚ):ℝ) * n2 jj ∧
    (((-2793161/33554432):ℚ):ℝ) + ∑ jj, ((W1_4 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 4:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_4 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 4:ℚ):ℝ) - (((-2793161/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_4 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_4 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_4, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_4 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_4 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 4:ℚ):ℝ) - (((-2793161/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_4, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c5 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 5:ℚ):ℝ) ≤ (((-13642847/16777216):ℚ):ℝ) + ∑ jj, ((W1_5 jj:ℚ):ℝ) * n2 jj ∧
    (((-13642847/16777216):ℚ):ℝ) + ∑ jj, ((W1_5 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 5:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_5 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 5:ℚ):ℝ) - (((-13642847/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_5 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_5 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_5, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_5 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_5 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 5:ℚ):ℝ) - (((-13642847/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_5, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c6 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 6:ℚ):ℝ) ≤ (((-772723/16777216):ℚ):ℝ) + ∑ jj, ((W1_6 jj:ℚ):ℝ) * n2 jj ∧
    (((-772723/16777216):ℚ):ℝ) + ∑ jj, ((W1_6 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 6:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_6 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 6:ℚ):ℝ) - (((-772723/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_6 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_6 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_6, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_6 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_6 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 6:ℚ):ℝ) - (((-772723/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_6, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c7 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 7:ℚ):ℝ) ≤ (((-4934107/33554432):ℚ):ℝ) + ∑ jj, ((W1_7 jj:ℚ):ℝ) * n2 jj ∧
    (((-4934107/33554432):ℚ):ℝ) + ∑ jj, ((W1_7 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 7:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_7 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 7:ℚ):ℝ) - (((-4934107/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_7 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_7 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_7, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_7 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_7 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 7:ℚ):ℝ) - (((-4934107/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_7, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c8 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 8:ℚ):ℝ) ≤ (((-1153469/2097152):ℚ):ℝ) + ∑ jj, ((W1_8 jj:ℚ):ℝ) * n2 jj ∧
    (((-1153469/2097152):ℚ):ℝ) + ∑ jj, ((W1_8 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 8:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_8 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 8:ℚ):ℝ) - (((-1153469/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_8 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_8 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_8, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_8 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_8 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 8:ℚ):ℝ) - (((-1153469/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_8, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c9 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 9:ℚ):ℝ) ≤ (((-638711/524288):ℚ):ℝ) + ∑ jj, ((W1_9 jj:ℚ):ℝ) * n2 jj ∧
    (((-638711/524288):ℚ):ℝ) + ∑ jj, ((W1_9 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 9:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_9 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 9:ℚ):ℝ) - (((-638711/524288):ℚ):ℝ) ≤ ∑ jj, min (((W1_9 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_9 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_9, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_9 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_9 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 9:ℚ):ℝ) - (((-638711/524288):ℚ):ℝ) := by
      simp only [hHi, W1_9, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c10 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 10:ℚ):ℝ) ≤ (((9769761/134217728):ℚ):ℝ) + ∑ jj, ((W1_10 jj:ℚ):ℝ) * n2 jj ∧
    (((9769761/134217728):ℚ):ℝ) + ∑ jj, ((W1_10 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 10:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_10 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 10:ℚ):ℝ) - (((9769761/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_10 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_10 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_10, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_10 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_10 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 10:ℚ):ℝ) - (((9769761/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_10, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c11 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 11:ℚ):ℝ) ≤ (((-10507531/33554432):ℚ):ℝ) + ∑ jj, ((W1_11 jj:ℚ):ℝ) * n2 jj ∧
    (((-10507531/33554432):ℚ):ℝ) + ∑ jj, ((W1_11 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 11:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_11 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 11:ℚ):ℝ) - (((-10507531/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_11 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_11 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_11, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_11 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_11 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 11:ℚ):ℝ) - (((-10507531/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_11, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c12 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 12:ℚ):ℝ) ≤ (((-8328237/16777216):ℚ):ℝ) + ∑ jj, ((W1_12 jj:ℚ):ℝ) * n2 jj ∧
    (((-8328237/16777216):ℚ):ℝ) + ∑ jj, ((W1_12 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 12:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_12 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 12:ℚ):ℝ) - (((-8328237/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_12 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_12 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_12, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_12 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_12 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 12:ℚ):ℝ) - (((-8328237/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_12, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c13 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 13:ℚ):ℝ) ≤ (((-5640541/4194304):ℚ):ℝ) + ∑ jj, ((W1_13 jj:ℚ):ℝ) * n2 jj ∧
    (((-5640541/4194304):ℚ):ℝ) + ∑ jj, ((W1_13 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 13:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_13 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 13:ℚ):ℝ) - (((-5640541/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_13 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_13 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_13, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_13 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_13 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 13:ℚ):ℝ) - (((-5640541/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_13, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c14 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 14:ℚ):ℝ) ≤ (((11143047/33554432):ℚ):ℝ) + ∑ jj, ((W1_14 jj:ℚ):ℝ) * n2 jj ∧
    (((11143047/33554432):ℚ):ℝ) + ∑ jj, ((W1_14 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 14:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_14 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 14:ℚ):ℝ) - (((11143047/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_14 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_14 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_14, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_14 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_14 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 14:ℚ):ℝ) - (((11143047/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_14, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c15 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 15:ℚ):ℝ) ≤ (((4387685/2097152):ℚ):ℝ) + ∑ jj, ((W1_15 jj:ℚ):ℝ) * n2 jj ∧
    (((4387685/2097152):ℚ):ℝ) + ∑ jj, ((W1_15 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 15:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_15 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 15:ℚ):ℝ) - (((4387685/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_15 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_15 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_15, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_15 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_15 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 15:ℚ):ℝ) - (((4387685/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_15, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c16 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 16:ℚ):ℝ) ≤ (((5544177/33554432):ℚ):ℝ) + ∑ jj, ((W1_16 jj:ℚ):ℝ) * n2 jj ∧
    (((5544177/33554432):ℚ):ℝ) + ∑ jj, ((W1_16 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 16:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_16 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 16:ℚ):ℝ) - (((5544177/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_16 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_16 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_16, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_16 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_16 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 16:ℚ):ℝ) - (((5544177/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_16, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c17 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 17:ℚ):ℝ) ≤ (((-5494207/4194304):ℚ):ℝ) + ∑ jj, ((W1_17 jj:ℚ):ℝ) * n2 jj ∧
    (((-5494207/4194304):ℚ):ℝ) + ∑ jj, ((W1_17 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 17:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_17 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 17:ℚ):ℝ) - (((-5494207/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_17 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_17 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_17, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_17 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_17 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 17:ℚ):ℝ) - (((-5494207/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_17, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c18 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 18:ℚ):ℝ) ≤ (((-4550279/33554432):ℚ):ℝ) + ∑ jj, ((W1_18 jj:ℚ):ℝ) * n2 jj ∧
    (((-4550279/33554432):ℚ):ℝ) + ∑ jj, ((W1_18 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 18:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_18 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 18:ℚ):ℝ) - (((-4550279/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_18 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_18 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_18, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_18 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_18 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 18:ℚ):ℝ) - (((-4550279/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_18, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c19 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 19:ℚ):ℝ) ≤ (((-3639715/8388608):ℚ):ℝ) + ∑ jj, ((W1_19 jj:ℚ):ℝ) * n2 jj ∧
    (((-3639715/8388608):ℚ):ℝ) + ∑ jj, ((W1_19 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 19:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_19 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 19:ℚ):ℝ) - (((-3639715/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_19 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_19 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_19, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_19 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_19 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 19:ℚ):ℝ) - (((-3639715/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_19, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c20 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 20:ℚ):ℝ) ≤ (((-2317659/33554432):ℚ):ℝ) + ∑ jj, ((W1_20 jj:ℚ):ℝ) * n2 jj ∧
    (((-2317659/33554432):ℚ):ℝ) + ∑ jj, ((W1_20 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 20:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_20 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 20:ℚ):ℝ) - (((-2317659/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_20 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_20 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_20, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_20 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_20 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 20:ℚ):ℝ) - (((-2317659/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_20, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c21 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 21:ℚ):ℝ) ≤ (((-2115475/2097152):ℚ):ℝ) + ∑ jj, ((W1_21 jj:ℚ):ℝ) * n2 jj ∧
    (((-2115475/2097152):ℚ):ℝ) + ∑ jj, ((W1_21 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 21:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_21 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 21:ℚ):ℝ) - (((-2115475/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_21 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_21 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_21, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_21 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_21 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 21:ℚ):ℝ) - (((-2115475/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_21, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c22 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 22:ℚ):ℝ) ≤ (((16162583/67108864):ℚ):ℝ) + ∑ jj, ((W1_22 jj:ℚ):ℝ) * n2 jj ∧
    (((16162583/67108864):ℚ):ℝ) + ∑ jj, ((W1_22 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 22:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_22 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 22:ℚ):ℝ) - (((16162583/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_22 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_22 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_22, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_22 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_22 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 22:ℚ):ℝ) - (((16162583/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_22, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c23 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 23:ℚ):ℝ) ≤ (((-3900519/4194304):ℚ):ℝ) + ∑ jj, ((W1_23 jj:ℚ):ℝ) * n2 jj ∧
    (((-3900519/4194304):ℚ):ℝ) + ∑ jj, ((W1_23 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 23:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_23 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 23:ℚ):ℝ) - (((-3900519/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_23 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_23 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_23, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_23 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_23 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 23:ℚ):ℝ) - (((-3900519/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_23, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c24 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 24:ℚ):ℝ) ≤ (((-10985335/134217728):ℚ):ℝ) + ∑ jj, ((W1_24 jj:ℚ):ℝ) * n2 jj ∧
    (((-10985335/134217728):ℚ):ℝ) + ∑ jj, ((W1_24 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 24:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_24 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 24:ℚ):ℝ) - (((-10985335/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_24 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_24 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_24, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_24 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_24 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 24:ℚ):ℝ) - (((-10985335/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_24, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c25 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 25:ℚ):ℝ) ≤ (((-4476169/8388608):ℚ):ℝ) + ∑ jj, ((W1_25 jj:ℚ):ℝ) * n2 jj ∧
    (((-4476169/8388608):ℚ):ℝ) + ∑ jj, ((W1_25 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 25:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_25 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 25:ℚ):ℝ) - (((-4476169/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_25 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_25 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_25, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_25 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_25 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 25:ℚ):ℝ) - (((-4476169/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_25, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c26 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 26:ℚ):ℝ) ≤ (((-12967475/16777216):ℚ):ℝ) + ∑ jj, ((W1_26 jj:ℚ):ℝ) * n2 jj ∧
    (((-12967475/16777216):ℚ):ℝ) + ∑ jj, ((W1_26 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 26:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_26 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 26:ℚ):ℝ) - (((-12967475/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_26 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_26 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_26, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_26 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_26 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 26:ℚ):ℝ) - (((-12967475/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_26, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c27 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 27:ℚ):ℝ) ≤ (((-650751/16777216):ℚ):ℝ) + ∑ jj, ((W1_27 jj:ℚ):ℝ) * n2 jj ∧
    (((-650751/16777216):ℚ):ℝ) + ∑ jj, ((W1_27 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 27:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_27 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 27:ℚ):ℝ) - (((-650751/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_27 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_27 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_27, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_27 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_27 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 27:ℚ):ℝ) - (((-650751/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_27, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c28 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 28:ℚ):ℝ) ≤ (((-10234557/4194304):ℚ):ℝ) + ∑ jj, ((W1_28 jj:ℚ):ℝ) * n2 jj ∧
    (((-10234557/4194304):ℚ):ℝ) + ∑ jj, ((W1_28 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 28:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_28 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 28:ℚ):ℝ) - (((-10234557/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_28 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_28 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_28, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_28 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_28 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 28:ℚ):ℝ) - (((-10234557/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_28, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c29 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 29:ℚ):ℝ) ≤ (((-1562439/2097152):ℚ):ℝ) + ∑ jj, ((W1_29 jj:ℚ):ℝ) * n2 jj ∧
    (((-1562439/2097152):ℚ):ℝ) + ∑ jj, ((W1_29 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 29:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_29 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 29:ℚ):ℝ) - (((-1562439/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_29 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_29 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_29, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_29 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_29 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 29:ℚ):ℝ) - (((-1562439/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_29, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c30 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 30:ℚ):ℝ) ≤ (((5393139/16777216):ℚ):ℝ) + ∑ jj, ((W1_30 jj:ℚ):ℝ) * n2 jj ∧
    (((5393139/16777216):ℚ):ℝ) + ∑ jj, ((W1_30 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 30:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_30 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 30:ℚ):ℝ) - (((5393139/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_30 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_30 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_30, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_30 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_30 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 30:ℚ):ℝ) - (((5393139/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_30, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c31 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 31:ℚ):ℝ) ≤ (((-8874343/134217728):ℚ):ℝ) + ∑ jj, ((W1_31 jj:ℚ):ℝ) * n2 jj ∧
    (((-8874343/134217728):ℚ):ℝ) + ∑ jj, ((W1_31 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 31:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_31 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 31:ℚ):ℝ) - (((-8874343/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_31 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_31 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_31, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_31 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_31 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 31:ℚ):ℝ) - (((-8874343/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_31, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c32 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 32:ℚ):ℝ) ≤ (((-8736221/67108864):ℚ):ℝ) + ∑ jj, ((W1_32 jj:ℚ):ℝ) * n2 jj ∧
    (((-8736221/67108864):ℚ):ℝ) + ∑ jj, ((W1_32 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 32:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_32 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 32:ℚ):ℝ) - (((-8736221/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_32 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_32 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_32, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_32 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_32 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 32:ℚ):ℝ) - (((-8736221/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_32, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c33 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 33:ℚ):ℝ) ≤ (((-9413953/8388608):ℚ):ℝ) + ∑ jj, ((W1_33 jj:ℚ):ℝ) * n2 jj ∧
    (((-9413953/8388608):ℚ):ℝ) + ∑ jj, ((W1_33 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 33:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_33 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 33:ℚ):ℝ) - (((-9413953/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_33 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_33 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_33, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_33 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_33 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 33:ℚ):ℝ) - (((-9413953/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_33, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c34 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 34:ℚ):ℝ) ≤ (((-13880627/33554432):ℚ):ℝ) + ∑ jj, ((W1_34 jj:ℚ):ℝ) * n2 jj ∧
    (((-13880627/33554432):ℚ):ℝ) + ∑ jj, ((W1_34 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 34:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_34 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 34:ℚ):ℝ) - (((-13880627/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_34 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_34 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_34, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_34 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_34 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 34:ℚ):ℝ) - (((-13880627/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_34, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c35 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 35:ℚ):ℝ) ≤ (((-16776817/8388608):ℚ):ℝ) + ∑ jj, ((W1_35 jj:ℚ):ℝ) * n2 jj ∧
    (((-16776817/8388608):ℚ):ℝ) + ∑ jj, ((W1_35 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 35:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_35 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 35:ℚ):ℝ) - (((-16776817/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_35 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_35 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_35, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_35 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_35 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 35:ℚ):ℝ) - (((-16776817/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_35, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c36 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 36:ℚ):ℝ) ≤ (((16424459/134217728):ℚ):ℝ) + ∑ jj, ((W1_36 jj:ℚ):ℝ) * n2 jj ∧
    (((16424459/134217728):ℚ):ℝ) + ∑ jj, ((W1_36 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 36:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_36 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 36:ℚ):ℝ) - (((16424459/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_36 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_36 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_36, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_36 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_36 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 36:ℚ):ℝ) - (((16424459/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_36, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c37 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 37:ℚ):ℝ) ≤ (((-5150943/134217728):ℚ):ℝ) + ∑ jj, ((W1_37 jj:ℚ):ℝ) * n2 jj ∧
    (((-5150943/134217728):ℚ):ℝ) + ∑ jj, ((W1_37 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 37:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_37 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 37:ℚ):ℝ) - (((-5150943/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_37 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_37 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_37, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_37 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_37 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 37:ℚ):ℝ) - (((-5150943/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_37, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c38 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 38:ℚ):ℝ) ≤ (((-9730433/33554432):ℚ):ℝ) + ∑ jj, ((W1_38 jj:ℚ):ℝ) * n2 jj ∧
    (((-9730433/33554432):ℚ):ℝ) + ∑ jj, ((W1_38 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 38:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_38 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 38:ℚ):ℝ) - (((-9730433/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_38 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_38 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_38, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_38 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_38 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 38:ℚ):ℝ) - (((-9730433/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_38, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c39 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 39:ℚ):ℝ) ≤ (((-5906987/67108864):ℚ):ℝ) + ∑ jj, ((W1_39 jj:ℚ):ℝ) * n2 jj ∧
    (((-5906987/67108864):ℚ):ℝ) + ∑ jj, ((W1_39 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 39:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_39 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 39:ℚ):ℝ) - (((-5906987/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_39 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_39 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_39, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_39 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_39 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 39:ℚ):ℝ) - (((-5906987/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_39, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c40 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 40:ℚ):ℝ) ≤ (((-7549317/67108864):ℚ):ℝ) + ∑ jj, ((W1_40 jj:ℚ):ℝ) * n2 jj ∧
    (((-7549317/67108864):ℚ):ℝ) + ∑ jj, ((W1_40 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 40:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_40 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 40:ℚ):ℝ) - (((-7549317/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_40 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_40 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_40, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_40 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_40 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 40:ℚ):ℝ) - (((-7549317/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_40, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c41 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 41:ℚ):ℝ) ≤ (((-6242439/8388608):ℚ):ℝ) + ∑ jj, ((W1_41 jj:ℚ):ℝ) * n2 jj ∧
    (((-6242439/8388608):ℚ):ℝ) + ∑ jj, ((W1_41 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 41:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_41 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 41:ℚ):ℝ) - (((-6242439/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_41 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_41 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_41, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_41 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_41 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 41:ℚ):ℝ) - (((-6242439/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_41, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c42 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 42:ℚ):ℝ) ≤ (((3837163/16777216):ℚ):ℝ) + ∑ jj, ((W1_42 jj:ℚ):ℝ) * n2 jj ∧
    (((3837163/16777216):ℚ):ℝ) + ∑ jj, ((W1_42 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 42:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_42 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 42:ℚ):ℝ) - (((3837163/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_42 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_42 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_42, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_42 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_42 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 42:ℚ):ℝ) - (((3837163/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_42, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c43 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 43:ℚ):ℝ) ≤ (((-11310435/8388608):ℚ):ℝ) + ∑ jj, ((W1_43 jj:ℚ):ℝ) * n2 jj ∧
    (((-11310435/8388608):ℚ):ℝ) + ∑ jj, ((W1_43 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 43:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_43 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 43:ℚ):ℝ) - (((-11310435/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_43 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_43 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_43, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_43 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_43 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 43:ℚ):ℝ) - (((-11310435/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_43, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c44 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 44:ℚ):ℝ) ≤ (((9259801/16777216):ℚ):ℝ) + ∑ jj, ((W1_44 jj:ℚ):ℝ) * n2 jj ∧
    (((9259801/16777216):ℚ):ℝ) + ∑ jj, ((W1_44 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 44:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_44 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 44:ℚ):ℝ) - (((9259801/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_44 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_44 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_44, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_44 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_44 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 44:ℚ):ℝ) - (((9259801/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_44, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c45 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 45:ℚ):ℝ) ≤ (((-11757417/67108864):ℚ):ℝ) + ∑ jj, ((W1_45 jj:ℚ):ℝ) * n2 jj ∧
    (((-11757417/67108864):ℚ):ℝ) + ∑ jj, ((W1_45 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 45:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_45 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 45:ℚ):ℝ) - (((-11757417/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_45 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_45 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_45, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_45 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_45 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 45:ℚ):ℝ) - (((-11757417/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_45, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c46 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 46:ℚ):ℝ) ≤ (((-4866297/16777216):ℚ):ℝ) + ∑ jj, ((W1_46 jj:ℚ):ℝ) * n2 jj ∧
    (((-4866297/16777216):ℚ):ℝ) + ∑ jj, ((W1_46 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 46:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_46 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 46:ℚ):ℝ) - (((-4866297/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_46 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_46 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_46, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_46 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_46 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 46:ℚ):ℝ) - (((-4866297/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_46, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c47 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 47:ℚ):ℝ) ≤ (((14181223/134217728):ℚ):ℝ) + ∑ jj, ((W1_47 jj:ℚ):ℝ) * n2 jj ∧
    (((14181223/134217728):ℚ):ℝ) + ∑ jj, ((W1_47 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 47:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_47 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 47:ℚ):ℝ) - (((14181223/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_47 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_47 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_47, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_47 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_47 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 47:ℚ):ℝ) - (((14181223/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_47, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c48 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 48:ℚ):ℝ) ≤ (((-2294063/4194304):ℚ):ℝ) + ∑ jj, ((W1_48 jj:ℚ):ℝ) * n2 jj ∧
    (((-2294063/4194304):ℚ):ℝ) + ∑ jj, ((W1_48 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 48:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_48 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 48:ℚ):ℝ) - (((-2294063/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_48 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_48 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_48, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_48 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_48 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 48:ℚ):ℝ) - (((-2294063/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_48, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c49 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 49:ℚ):ℝ) ≤ (((-4861977/33554432):ℚ):ℝ) + ∑ jj, ((W1_49 jj:ℚ):ℝ) * n2 jj ∧
    (((-4861977/33554432):ℚ):ℝ) + ∑ jj, ((W1_49 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 49:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_49 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 49:ℚ):ℝ) - (((-4861977/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_49 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_49 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_49, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_49 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_49 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 49:ℚ):ℝ) - (((-4861977/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_49, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c50 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 50:ℚ):ℝ) ≤ (((-11588965/33554432):ℚ):ℝ) + ∑ jj, ((W1_50 jj:ℚ):ℝ) * n2 jj ∧
    (((-11588965/33554432):ℚ):ℝ) + ∑ jj, ((W1_50 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 50:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_50 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 50:ℚ):ℝ) - (((-11588965/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_50 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_50 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_50, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_50 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_50 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 50:ℚ):ℝ) - (((-11588965/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_50, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c51 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 51:ℚ):ℝ) ≤ (((-16670097/33554432):ℚ):ℝ) + ∑ jj, ((W1_51 jj:ℚ):ℝ) * n2 jj ∧
    (((-16670097/33554432):ℚ):ℝ) + ∑ jj, ((W1_51 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 51:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_51 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 51:ℚ):ℝ) - (((-16670097/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_51 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_51 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_51, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_51 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_51 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 51:ℚ):ℝ) - (((-16670097/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_51, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c52 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 52:ℚ):ℝ) ≤ (((-12829105/8388608):ℚ):ℝ) + ∑ jj, ((W1_52 jj:ℚ):ℝ) * n2 jj ∧
    (((-12829105/8388608):ℚ):ℝ) + ∑ jj, ((W1_52 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 52:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_52 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 52:ℚ):ℝ) - (((-12829105/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_52 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_52 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_52, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_52 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_52 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 52:ℚ):ℝ) - (((-12829105/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_52, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c53 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 53:ℚ):ℝ) ≤ (((-5456869/8388608):ℚ):ℝ) + ∑ jj, ((W1_53 jj:ℚ):ℝ) * n2 jj ∧
    (((-5456869/8388608):ℚ):ℝ) + ∑ jj, ((W1_53 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 53:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_53 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 53:ℚ):ℝ) - (((-5456869/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_53 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_53 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_53, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_53 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_53 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 53:ℚ):ℝ) - (((-5456869/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_53, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c54 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 54:ℚ):ℝ) ≤ (((-5907993/8388608):ℚ):ℝ) + ∑ jj, ((W1_54 jj:ℚ):ℝ) * n2 jj ∧
    (((-5907993/8388608):ℚ):ℝ) + ∑ jj, ((W1_54 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 54:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_54 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 54:ℚ):ℝ) - (((-5907993/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_54 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_54 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_54, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_54 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_54 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 54:ℚ):ℝ) - (((-5907993/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_54, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c55 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 55:ℚ):ℝ) ≤ (((-8692335/67108864):ℚ):ℝ) + ∑ jj, ((W1_55 jj:ℚ):ℝ) * n2 jj ∧
    (((-8692335/67108864):ℚ):ℝ) + ∑ jj, ((W1_55 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 55:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_55 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 55:ℚ):ℝ) - (((-8692335/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_55 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_55 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_55, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_55 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_55 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 55:ℚ):ℝ) - (((-8692335/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_55, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c56 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 56:ℚ):ℝ) ≤ (((-11633705/16777216):ℚ):ℝ) + ∑ jj, ((W1_56 jj:ℚ):ℝ) * n2 jj ∧
    (((-11633705/16777216):ℚ):ℝ) + ∑ jj, ((W1_56 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 56:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_56 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 56:ℚ):ℝ) - (((-11633705/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_56 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_56 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_56, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_56 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_56 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 56:ℚ):ℝ) - (((-11633705/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_56, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c57 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 57:ℚ):ℝ) ≤ (((-1044569/2097152):ℚ):ℝ) + ∑ jj, ((W1_57 jj:ℚ):ℝ) * n2 jj ∧
    (((-1044569/2097152):ℚ):ℝ) + ∑ jj, ((W1_57 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 57:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_57 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 57:ℚ):ℝ) - (((-1044569/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_57 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_57 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_57, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_57 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_57 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 57:ℚ):ℝ) - (((-1044569/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_57, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c58 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 58:ℚ):ℝ) ≤ (((8931459/8388608):ℚ):ℝ) + ∑ jj, ((W1_58 jj:ℚ):ℝ) * n2 jj ∧
    (((8931459/8388608):ℚ):ℝ) + ∑ jj, ((W1_58 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 58:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_58 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 58:ℚ):ℝ) - (((8931459/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_58 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_58 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_58, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_58 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_58 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 58:ℚ):ℝ) - (((8931459/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_58, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c59 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 59:ℚ):ℝ) ≤ (((-12629791/67108864):ℚ):ℝ) + ∑ jj, ((W1_59 jj:ℚ):ℝ) * n2 jj ∧
    (((-12629791/67108864):ℚ):ℝ) + ∑ jj, ((W1_59 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 59:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_59 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 59:ℚ):ℝ) - (((-12629791/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_59 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_59 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_59, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_59 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_59 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 59:ℚ):ℝ) - (((-12629791/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_59, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c60 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 60:ℚ):ℝ) ≤ (((-11376827/134217728):ℚ):ℝ) + ∑ jj, ((W1_60 jj:ℚ):ℝ) * n2 jj ∧
    (((-11376827/134217728):ℚ):ℝ) + ∑ jj, ((W1_60 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 60:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_60 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 60:ℚ):ℝ) - (((-11376827/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_60 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_60 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_60, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_60 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_60 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 60:ℚ):ℝ) - (((-11376827/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_60, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c61 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 61:ℚ):ℝ) ≤ (((-9272273/16777216):ℚ):ℝ) + ∑ jj, ((W1_61 jj:ℚ):ℝ) * n2 jj ∧
    (((-9272273/16777216):ℚ):ℝ) + ∑ jj, ((W1_61 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 61:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_61 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 61:ℚ):ℝ) - (((-9272273/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_61 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_61 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_61, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_61 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_61 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 61:ℚ):ℝ) - (((-9272273/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_61, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c62 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 62:ℚ):ℝ) ≤ (((15400253/16777216):ℚ):ℝ) + ∑ jj, ((W1_62 jj:ℚ):ℝ) * n2 jj ∧
    (((15400253/16777216):ℚ):ℝ) + ∑ jj, ((W1_62 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 62:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_62 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 62:ℚ):ℝ) - (((15400253/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_62 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_62 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_62, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_62 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_62 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 62:ℚ):ℝ) - (((15400253/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_62, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c63 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 63:ℚ):ℝ) ≤ (((7409085/16777216):ℚ):ℝ) + ∑ jj, ((W1_63 jj:ℚ):ℝ) * n2 jj ∧
    (((7409085/16777216):ℚ):ℝ) + ∑ jj, ((W1_63 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 63:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_63 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 63:ℚ):ℝ) - (((7409085/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_63 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_63 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_63, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_63 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_63 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 63:ℚ):ℝ) - (((7409085/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_63, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c64 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 64:ℚ):ℝ) ≤ (((-7296363/8388608):ℚ):ℝ) + ∑ jj, ((W1_64 jj:ℚ):ℝ) * n2 jj ∧
    (((-7296363/8388608):ℚ):ℝ) + ∑ jj, ((W1_64 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 64:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_64 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 64:ℚ):ℝ) - (((-7296363/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_64 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_64 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_64, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_64 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_64 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 64:ℚ):ℝ) - (((-7296363/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_64, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c65 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 65:ℚ):ℝ) ≤ (((-5581791/8388608):ℚ):ℝ) + ∑ jj, ((W1_65 jj:ℚ):ℝ) * n2 jj ∧
    (((-5581791/8388608):ℚ):ℝ) + ∑ jj, ((W1_65 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 65:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_65 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 65:ℚ):ℝ) - (((-5581791/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_65 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_65 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_65, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_65 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_65 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 65:ℚ):ℝ) - (((-5581791/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_65, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c66 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 66:ℚ):ℝ) ≤ (((-1770415/1048576):ℚ):ℝ) + ∑ jj, ((W1_66 jj:ℚ):ℝ) * n2 jj ∧
    (((-1770415/1048576):ℚ):ℝ) + ∑ jj, ((W1_66 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 66:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_66 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 66:ℚ):ℝ) - (((-1770415/1048576):ℚ):ℝ) ≤ ∑ jj, min (((W1_66 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_66 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_66, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_66 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_66 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 66:ℚ):ℝ) - (((-1770415/1048576):ℚ):ℝ) := by
      simp only [hHi, W1_66, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c67 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 67:ℚ):ℝ) ≤ (((-8506611/4194304):ℚ):ℝ) + ∑ jj, ((W1_67 jj:ℚ):ℝ) * n2 jj ∧
    (((-8506611/4194304):ℚ):ℝ) + ∑ jj, ((W1_67 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 67:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_67 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 67:ℚ):ℝ) - (((-8506611/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_67 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_67 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_67, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_67 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_67 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 67:ℚ):ℝ) - (((-8506611/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_67, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c68 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 68:ℚ):ℝ) ≤ (((-2626991/4194304):ℚ):ℝ) + ∑ jj, ((W1_68 jj:ℚ):ℝ) * n2 jj ∧
    (((-2626991/4194304):ℚ):ℝ) + ∑ jj, ((W1_68 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 68:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_68 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 68:ℚ):ℝ) - (((-2626991/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_68 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_68 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_68, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_68 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_68 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 68:ℚ):ℝ) - (((-2626991/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_68, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c69 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 69:ℚ):ℝ) ≤ (((-10510835/67108864):ℚ):ℝ) + ∑ jj, ((W1_69 jj:ℚ):ℝ) * n2 jj ∧
    (((-10510835/67108864):ℚ):ℝ) + ∑ jj, ((W1_69 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 69:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_69 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 69:ℚ):ℝ) - (((-10510835/67108864):ℚ):ℝ) ≤ ∑ jj, min (((W1_69 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_69 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_69, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_69 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_69 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 69:ℚ):ℝ) - (((-10510835/67108864):ℚ):ℝ) := by
      simp only [hHi, W1_69, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c70 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 70:ℚ):ℝ) ≤ (((-10789881/16777216):ℚ):ℝ) + ∑ jj, ((W1_70 jj:ℚ):ℝ) * n2 jj ∧
    (((-10789881/16777216):ℚ):ℝ) + ∑ jj, ((W1_70 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 70:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_70 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 70:ℚ):ℝ) - (((-10789881/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_70 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_70 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_70, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_70 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_70 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 70:ℚ):ℝ) - (((-10789881/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_70, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c71 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 71:ℚ):ℝ) ≤ (((-915911/8388608):ℚ):ℝ) + ∑ jj, ((W1_71 jj:ℚ):ℝ) * n2 jj ∧
    (((-915911/8388608):ℚ):ℝ) + ∑ jj, ((W1_71 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 71:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_71 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 71:ℚ):ℝ) - (((-915911/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_71 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_71 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_71, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_71 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_71 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 71:ℚ):ℝ) - (((-915911/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_71, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c72 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 72:ℚ):ℝ) ≤ (((5320289/8388608):ℚ):ℝ) + ∑ jj, ((W1_72 jj:ℚ):ℝ) * n2 jj ∧
    (((5320289/8388608):ℚ):ℝ) + ∑ jj, ((W1_72 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 72:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_72 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 72:ℚ):ℝ) - (((5320289/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_72 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_72 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_72, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_72 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_72 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 72:ℚ):ℝ) - (((5320289/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_72, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c73 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 73:ℚ):ℝ) ≤ (((-7623919/8388608):ℚ):ℝ) + ∑ jj, ((W1_73 jj:ℚ):ℝ) * n2 jj ∧
    (((-7623919/8388608):ℚ):ℝ) + ∑ jj, ((W1_73 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 73:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_73 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 73:ℚ):ℝ) - (((-7623919/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_73 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_73 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_73, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_73 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_73 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 73:ℚ):ℝ) - (((-7623919/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_73, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c74 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 74:ℚ):ℝ) ≤ (((-9012697/16777216):ℚ):ℝ) + ∑ jj, ((W1_74 jj:ℚ):ℝ) * n2 jj ∧
    (((-9012697/16777216):ℚ):ℝ) + ∑ jj, ((W1_74 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 74:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_74 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 74:ℚ):ℝ) - (((-9012697/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_74 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_74 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_74, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_74 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_74 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 74:ℚ):ℝ) - (((-9012697/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_74, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c75 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 75:ℚ):ℝ) ≤ (((-4701711/4194304):ℚ):ℝ) + ∑ jj, ((W1_75 jj:ℚ):ℝ) * n2 jj ∧
    (((-4701711/4194304):ℚ):ℝ) + ∑ jj, ((W1_75 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 75:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_75 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 75:ℚ):ℝ) - (((-4701711/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_75 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_75 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_75, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_75 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_75 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 75:ℚ):ℝ) - (((-4701711/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_75, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c76 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 76:ℚ):ℝ) ≤ (((-1001341/16777216):ℚ):ℝ) + ∑ jj, ((W1_76 jj:ℚ):ℝ) * n2 jj ∧
    (((-1001341/16777216):ℚ):ℝ) + ∑ jj, ((W1_76 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 76:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_76 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 76:ℚ):ℝ) - (((-1001341/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_76 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_76 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_76, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_76 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_76 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 76:ℚ):ℝ) - (((-1001341/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_76, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c77 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 77:ℚ):ℝ) ≤ (((9585243/8388608):ℚ):ℝ) + ∑ jj, ((W1_77 jj:ℚ):ℝ) * n2 jj ∧
    (((9585243/8388608):ℚ):ℝ) + ∑ jj, ((W1_77 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 77:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_77 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 77:ℚ):ℝ) - (((9585243/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_77 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_77 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_77, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_77 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_77 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 77:ℚ):ℝ) - (((9585243/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_77, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c78 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 78:ℚ):ℝ) ≤ (((-14200009/268435456):ℚ):ℝ) + ∑ jj, ((W1_78 jj:ℚ):ℝ) * n2 jj ∧
    (((-14200009/268435456):ℚ):ℝ) + ∑ jj, ((W1_78 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 78:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_78 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 78:ℚ):ℝ) - (((-14200009/268435456):ℚ):ℝ) ≤ ∑ jj, min (((W1_78 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_78 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_78, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_78 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_78 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 78:ℚ):ℝ) - (((-14200009/268435456):ℚ):ℝ) := by
      simp only [hHi, W1_78, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c79 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 79:ℚ):ℝ) ≤ (((-11458291/134217728):ℚ):ℝ) + ∑ jj, ((W1_79 jj:ℚ):ℝ) * n2 jj ∧
    (((-11458291/134217728):ℚ):ℝ) + ∑ jj, ((W1_79 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 79:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_79 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 79:ℚ):ℝ) - (((-11458291/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_79 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_79 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_79, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_79 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_79 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 79:ℚ):ℝ) - (((-11458291/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_79, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c80 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 80:ℚ):ℝ) ≤ (((-1328445/2097152):ℚ):ℝ) + ∑ jj, ((W1_80 jj:ℚ):ℝ) * n2 jj ∧
    (((-1328445/2097152):ℚ):ℝ) + ∑ jj, ((W1_80 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 80:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_80 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 80:ℚ):ℝ) - (((-1328445/2097152):ℚ):ℝ) ≤ ∑ jj, min (((W1_80 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_80 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_80, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_80 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_80 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 80:ℚ):ℝ) - (((-1328445/2097152):ℚ):ℝ) := by
      simp only [hHi, W1_80, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c81 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 81:ℚ):ℝ) ≤ (((-13496547/8388608):ℚ):ℝ) + ∑ jj, ((W1_81 jj:ℚ):ℝ) * n2 jj ∧
    (((-13496547/8388608):ℚ):ℝ) + ∑ jj, ((W1_81 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 81:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_81 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 81:ℚ):ℝ) - (((-13496547/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_81 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_81 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_81, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_81 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_81 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 81:ℚ):ℝ) - (((-13496547/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_81, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c82 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 82:ℚ):ℝ) ≤ (((-3891469/4194304):ℚ):ℝ) + ∑ jj, ((W1_82 jj:ℚ):ℝ) * n2 jj ∧
    (((-3891469/4194304):ℚ):ℝ) + ∑ jj, ((W1_82 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 82:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_82 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 82:ℚ):ℝ) - (((-3891469/4194304):ℚ):ℝ) ≤ ∑ jj, min (((W1_82 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_82 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_82, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_82 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_82 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 82:ℚ):ℝ) - (((-3891469/4194304):ℚ):ℝ) := by
      simp only [hHi, W1_82, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c83 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 83:ℚ):ℝ) ≤ (((-10499055/8388608):ℚ):ℝ) + ∑ jj, ((W1_83 jj:ℚ):ℝ) * n2 jj ∧
    (((-10499055/8388608):ℚ):ℝ) + ∑ jj, ((W1_83 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 83:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_83 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 83:ℚ):ℝ) - (((-10499055/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_83 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_83 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_83, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_83 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_83 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 83:ℚ):ℝ) - (((-10499055/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_83, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c84 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 84:ℚ):ℝ) ≤ (((-13779039/33554432):ℚ):ℝ) + ∑ jj, ((W1_84 jj:ℚ):ℝ) * n2 jj ∧
    (((-13779039/33554432):ℚ):ℝ) + ∑ jj, ((W1_84 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 84:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_84 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 84:ℚ):ℝ) - (((-13779039/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_84 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_84 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_84, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_84 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_84 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 84:ℚ):ℝ) - (((-13779039/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_84, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c85 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 85:ℚ):ℝ) ≤ (((-5588977/16777216):ℚ):ℝ) + ∑ jj, ((W1_85 jj:ℚ):ℝ) * n2 jj ∧
    (((-5588977/16777216):ℚ):ℝ) + ∑ jj, ((W1_85 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 85:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_85 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 85:ℚ):ℝ) - (((-5588977/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_85 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_85 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_85, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_85 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_85 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 85:ℚ):ℝ) - (((-5588977/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_85, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c86 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 86:ℚ):ℝ) ≤ (((8973265/33554432):ℚ):ℝ) + ∑ jj, ((W1_86 jj:ℚ):ℝ) * n2 jj ∧
    (((8973265/33554432):ℚ):ℝ) + ∑ jj, ((W1_86 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 86:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_86 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 86:ℚ):ℝ) - (((8973265/33554432):ℚ):ℝ) ≤ ∑ jj, min (((W1_86 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_86 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_86, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_86 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_86 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 86:ℚ):ℝ) - (((8973265/33554432):ℚ):ℝ) := by
      simp only [hHi, W1_86, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c87 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 87:ℚ):ℝ) ≤ (((-8829139/16777216):ℚ):ℝ) + ∑ jj, ((W1_87 jj:ℚ):ℝ) * n2 jj ∧
    (((-8829139/16777216):ℚ):ℝ) + ∑ jj, ((W1_87 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 87:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_87 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 87:ℚ):ℝ) - (((-8829139/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_87 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_87 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_87, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_87 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_87 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 87:ℚ):ℝ) - (((-8829139/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_87, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c88 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 88:ℚ):ℝ) ≤ (((-14830557/8388608):ℚ):ℝ) + ∑ jj, ((W1_88 jj:ℚ):ℝ) * n2 jj ∧
    (((-14830557/8388608):ℚ):ℝ) + ∑ jj, ((W1_88 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 88:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_88 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 88:ℚ):ℝ) - (((-14830557/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_88 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_88 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_88, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_88 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_88 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 88:ℚ):ℝ) - (((-14830557/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_88, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c89 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 89:ℚ):ℝ) ≤ (((-13866301/16777216):ℚ):ℝ) + ∑ jj, ((W1_89 jj:ℚ):ℝ) * n2 jj ∧
    (((-13866301/16777216):ℚ):ℝ) + ∑ jj, ((W1_89 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 89:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_89 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 89:ℚ):ℝ) - (((-13866301/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_89 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_89 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_89, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_89 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_89 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 89:ℚ):ℝ) - (((-13866301/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_89, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c90 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 90:ℚ):ℝ) ≤ (((-10741747/4294967296):ℚ):ℝ) + ∑ jj, ((W1_90 jj:ℚ):ℝ) * n2 jj ∧
    (((-10741747/4294967296):ℚ):ℝ) + ∑ jj, ((W1_90 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 90:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_90 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 90:ℚ):ℝ) - (((-10741747/4294967296):ℚ):ℝ) ≤ ∑ jj, min (((W1_90 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_90 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_90, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_90 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_90 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 90:ℚ):ℝ) - (((-10741747/4294967296):ℚ):ℝ) := by
      simp only [hHi, W1_90, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c91 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 91:ℚ):ℝ) ≤ (((-11785159/8388608):ℚ):ℝ) + ∑ jj, ((W1_91 jj:ℚ):ℝ) * n2 jj ∧
    (((-11785159/8388608):ℚ):ℝ) + ∑ jj, ((W1_91 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 91:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_91 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 91:ℚ):ℝ) - (((-11785159/8388608):ℚ):ℝ) ≤ ∑ jj, min (((W1_91 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_91 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_91, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_91 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_91 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 91:ℚ):ℝ) - (((-11785159/8388608):ℚ):ℝ) := by
      simp only [hHi, W1_91, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c92 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 92:ℚ):ℝ) ≤ (((-14983347/134217728):ℚ):ℝ) + ∑ jj, ((W1_92 jj:ℚ):ℝ) * n2 jj ∧
    (((-14983347/134217728):ℚ):ℝ) + ∑ jj, ((W1_92 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 92:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_92 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 92:ℚ):ℝ) - (((-14983347/134217728):ℚ):ℝ) ≤ ∑ jj, min (((W1_92 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_92 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_92, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_92 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_92 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 92:ℚ):ℝ) - (((-14983347/134217728):ℚ):ℝ) := by
      simp only [hHi, W1_92, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c93 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 93:ℚ):ℝ) ≤ (((-5090165/16777216):ℚ):ℝ) + ∑ jj, ((W1_93 jj:ℚ):ℝ) * n2 jj ∧
    (((-5090165/16777216):ℚ):ℝ) + ∑ jj, ((W1_93 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 93:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_93 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 93:ℚ):ℝ) - (((-5090165/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_93 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_93 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_93, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_93 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_93 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 93:ℚ):ℝ) - (((-5090165/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_93, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c94 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 94:ℚ):ℝ) ≤ (((-9184041/16777216):ℚ):ℝ) + ∑ jj, ((W1_94 jj:ℚ):ℝ) * n2 jj ∧
    (((-9184041/16777216):ℚ):ℝ) + ∑ jj, ((W1_94 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 94:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_94 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 94:ℚ):ℝ) - (((-9184041/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_94 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_94 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_94, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_94 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_94 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 94:ℚ):ℝ) - (((-9184041/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_94, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem hid_c95 (n2 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ((hLo 95:ℚ):ℝ) ≤ (((-3033805/16777216):ℚ):ℝ) + ∑ jj, ((W1_95 jj:ℚ):ℝ) * n2 jj ∧
    (((-3033805/16777216):ℚ):ℝ) + ∑ jj, ((W1_95 jj:ℚ):ℝ) * n2 jj ≤ ((hHi 95:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((W1_95 jj:ℚ):ℝ)) (fun jj => ((n2Lo jj:ℚ):ℝ)) (fun jj => ((n2Hi jj:ℚ):ℝ)) n2 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((hLo 95:ℚ):ℝ) - (((-3033805/16777216):ℚ):ℝ) ≤ ∑ jj, min (((W1_95 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_95 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ)) := by
      simp only [hLo, W1_95, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((W1_95 jj:ℚ):ℝ)*((n2Lo jj:ℚ):ℝ)) (((W1_95 jj:ℚ):ℝ)*((n2Hi jj:ℚ):ℝ))) ≤ ((hHi 95:ℚ):ℝ) - (((-3033805/16777216):ℚ):ℝ) := by
      simp only [hHi, W1_95, n2Lo, n2Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]


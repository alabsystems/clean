import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem ao_c0 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 0:ℚ):ℝ) ≤ (((11858621/536870912):ℚ):ℝ) + ∑ jj, ((Wo0 jj:ℚ):ℝ) * att jj ∧
    (((11858621/536870912):ℚ):ℝ) + ∑ jj, ((Wo0 jj:ℚ):ℝ) * att jj ≤ ((aoHi 0:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo0 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 0:ℚ):ℝ) - (((11858621/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wo0 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo0 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo0, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo0 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo0 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 0:ℚ):ℝ) - (((11858621/536870912):ℚ):ℝ) := by
      simp only [aoHi, Wo0, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c1 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 1:ℚ):ℝ) ≤ (((-14957377/134217728):ℚ):ℝ) + ∑ jj, ((Wo1 jj:ℚ):ℝ) * att jj ∧
    (((-14957377/134217728):ℚ):ℝ) + ∑ jj, ((Wo1 jj:ℚ):ℝ) * att jj ≤ ((aoHi 1:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo1 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 1:ℚ):ℝ) - (((-14957377/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo1 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo1 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo1, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo1 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo1 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 1:ℚ):ℝ) - (((-14957377/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo1, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c2 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 2:ℚ):ℝ) ≤ (((-4073987/134217728):ℚ):ℝ) + ∑ jj, ((Wo2 jj:ℚ):ℝ) * att jj ∧
    (((-4073987/134217728):ℚ):ℝ) + ∑ jj, ((Wo2 jj:ℚ):ℝ) * att jj ≤ ((aoHi 2:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo2 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 2:ℚ):ℝ) - (((-4073987/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo2 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo2 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo2, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo2 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo2 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 2:ℚ):ℝ) - (((-4073987/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo2, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c3 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 3:ℚ):ℝ) ≤ (((-15608359/268435456):ℚ):ℝ) + ∑ jj, ((Wo3 jj:ℚ):ℝ) * att jj ∧
    (((-15608359/268435456):ℚ):ℝ) + ∑ jj, ((Wo3 jj:ℚ):ℝ) * att jj ≤ ((aoHi 3:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo3 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 3:ℚ):ℝ) - (((-15608359/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo3 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo3 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo3, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo3 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo3 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 3:ℚ):ℝ) - (((-15608359/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo3, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c4 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 4:ℚ):ℝ) ≤ (((6169579/33554432):ℚ):ℝ) + ∑ jj, ((Wo4 jj:ℚ):ℝ) * att jj ∧
    (((6169579/33554432):ℚ):ℝ) + ∑ jj, ((Wo4 jj:ℚ):ℝ) * att jj ≤ ((aoHi 4:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo4 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 4:ℚ):ℝ) - (((6169579/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo4 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo4 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo4, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo4 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo4 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 4:ℚ):ℝ) - (((6169579/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo4, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c5 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 5:ℚ):ℝ) ≤ (((4789201/33554432):ℚ):ℝ) + ∑ jj, ((Wo5 jj:ℚ):ℝ) * att jj ∧
    (((4789201/33554432):ℚ):ℝ) + ∑ jj, ((Wo5 jj:ℚ):ℝ) * att jj ≤ ((aoHi 5:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo5 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 5:ℚ):ℝ) - (((4789201/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo5 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo5 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo5, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo5 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo5 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 5:ℚ):ℝ) - (((4789201/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo5, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c6 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 6:ℚ):ℝ) ≤ (((3401709/134217728):ℚ):ℝ) + ∑ jj, ((Wo6 jj:ℚ):ℝ) * att jj ∧
    (((3401709/134217728):ℚ):ℝ) + ∑ jj, ((Wo6 jj:ℚ):ℝ) * att jj ≤ ((aoHi 6:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo6 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 6:ℚ):ℝ) - (((3401709/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo6 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo6 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo6, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo6 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo6 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 6:ℚ):ℝ) - (((3401709/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo6, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c7 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 7:ℚ):ℝ) ≤ (((14773671/134217728):ℚ):ℝ) + ∑ jj, ((Wo7 jj:ℚ):ℝ) * att jj ∧
    (((14773671/134217728):ℚ):ℝ) + ∑ jj, ((Wo7 jj:ℚ):ℝ) * att jj ≤ ((aoHi 7:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo7 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 7:ℚ):ℝ) - (((14773671/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo7 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo7 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo7, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo7 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo7 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 7:ℚ):ℝ) - (((14773671/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo7, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c8 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 8:ℚ):ℝ) ≤ (((3893795/268435456):ℚ):ℝ) + ∑ jj, ((Wo8 jj:ℚ):ℝ) * att jj ∧
    (((3893795/268435456):ℚ):ℝ) + ∑ jj, ((Wo8 jj:ℚ):ℝ) * att jj ≤ ((aoHi 8:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo8 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 8:ℚ):ℝ) - (((3893795/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo8 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo8 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo8, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo8 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo8 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 8:ℚ):ℝ) - (((3893795/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo8, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c9 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 9:ℚ):ℝ) ≤ (((-8781393/268435456):ℚ):ℝ) + ∑ jj, ((Wo9 jj:ℚ):ℝ) * att jj ∧
    (((-8781393/268435456):ℚ):ℝ) + ∑ jj, ((Wo9 jj:ℚ):ℝ) * att jj ≤ ((aoHi 9:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo9 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 9:ℚ):ℝ) - (((-8781393/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo9 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo9 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo9, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo9 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo9 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 9:ℚ):ℝ) - (((-8781393/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo9, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c10 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 10:ℚ):ℝ) ≤ (((-3849221/33554432):ℚ):ℝ) + ∑ jj, ((Wo10 jj:ℚ):ℝ) * att jj ∧
    (((-3849221/33554432):ℚ):ℝ) + ∑ jj, ((Wo10 jj:ℚ):ℝ) * att jj ≤ ((aoHi 10:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo10 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 10:ℚ):ℝ) - (((-3849221/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo10 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo10 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo10, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo10 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo10 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 10:ℚ):ℝ) - (((-3849221/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo10, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c11 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 11:ℚ):ℝ) ≤ (((14567651/134217728):ℚ):ℝ) + ∑ jj, ((Wo11 jj:ℚ):ℝ) * att jj ∧
    (((14567651/134217728):ℚ):ℝ) + ∑ jj, ((Wo11 jj:ℚ):ℝ) * att jj ≤ ((aoHi 11:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo11 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 11:ℚ):ℝ) - (((14567651/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo11 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo11 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo11, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo11 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo11 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 11:ℚ):ℝ) - (((14567651/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo11, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c12 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 12:ℚ):ℝ) ≤ (((3590867/67108864):ℚ):ℝ) + ∑ jj, ((Wo12 jj:ℚ):ℝ) * att jj ∧
    (((3590867/67108864):ℚ):ℝ) + ∑ jj, ((Wo12 jj:ℚ):ℝ) * att jj ≤ ((aoHi 12:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo12 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 12:ℚ):ℝ) - (((3590867/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo12 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo12 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo12, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo12 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo12 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 12:ℚ):ℝ) - (((3590867/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo12, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c13 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 13:ℚ):ℝ) ≤ (((-11105143/536870912):ℚ):ℝ) + ∑ jj, ((Wo13 jj:ℚ):ℝ) * att jj ∧
    (((-11105143/536870912):ℚ):ℝ) + ∑ jj, ((Wo13 jj:ℚ):ℝ) * att jj ≤ ((aoHi 13:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo13 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 13:ℚ):ℝ) - (((-11105143/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wo13 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo13 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo13, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo13 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo13 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 13:ℚ):ℝ) - (((-11105143/536870912):ℚ):ℝ) := by
      simp only [aoHi, Wo13, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c14 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 14:ℚ):ℝ) ≤ (((-778145/8388608):ℚ):ℝ) + ∑ jj, ((Wo14 jj:ℚ):ℝ) * att jj ∧
    (((-778145/8388608):ℚ):ℝ) + ∑ jj, ((Wo14 jj:ℚ):ℝ) * att jj ≤ ((aoHi 14:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo14 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 14:ℚ):ℝ) - (((-778145/8388608):ℚ):ℝ) ≤ ∑ jj, min (((Wo14 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo14 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo14, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo14 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo14 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 14:ℚ):ℝ) - (((-778145/8388608):ℚ):ℝ) := by
      simp only [aoHi, Wo14, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c15 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 15:ℚ):ℝ) ≤ (((15276627/134217728):ℚ):ℝ) + ∑ jj, ((Wo15 jj:ℚ):ℝ) * att jj ∧
    (((15276627/134217728):ℚ):ℝ) + ∑ jj, ((Wo15 jj:ℚ):ℝ) * att jj ≤ ((aoHi 15:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo15 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 15:ℚ):ℝ) - (((15276627/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo15 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo15 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo15, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo15 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo15 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 15:ℚ):ℝ) - (((15276627/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo15, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c16 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 16:ℚ):ℝ) ≤ (((2426937/33554432):ℚ):ℝ) + ∑ jj, ((Wo16 jj:ℚ):ℝ) * att jj ∧
    (((2426937/33554432):ℚ):ℝ) + ∑ jj, ((Wo16 jj:ℚ):ℝ) * att jj ≤ ((aoHi 16:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo16 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 16:ℚ):ℝ) - (((2426937/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo16 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo16 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo16, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo16 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo16 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 16:ℚ):ℝ) - (((2426937/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo16, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c17 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 17:ℚ):ℝ) ≤ (((-4931749/67108864):ℚ):ℝ) + ∑ jj, ((Wo17 jj:ℚ):ℝ) * att jj ∧
    (((-4931749/67108864):ℚ):ℝ) + ∑ jj, ((Wo17 jj:ℚ):ℝ) * att jj ≤ ((aoHi 17:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo17 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 17:ℚ):ℝ) - (((-4931749/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo17 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo17 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo17, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo17 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo17 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 17:ℚ):ℝ) - (((-4931749/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo17, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c18 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 18:ℚ):ℝ) ≤ (((9165293/67108864):ℚ):ℝ) + ∑ jj, ((Wo18 jj:ℚ):ℝ) * att jj ∧
    (((9165293/67108864):ℚ):ℝ) + ∑ jj, ((Wo18 jj:ℚ):ℝ) * att jj ≤ ((aoHi 18:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo18 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 18:ℚ):ℝ) - (((9165293/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo18 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo18 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo18, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo18 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo18 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 18:ℚ):ℝ) - (((9165293/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo18, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c19 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 19:ℚ):ℝ) ≤ (((-833717/8388608):ℚ):ℝ) + ∑ jj, ((Wo19 jj:ℚ):ℝ) * att jj ∧
    (((-833717/8388608):ℚ):ℝ) + ∑ jj, ((Wo19 jj:ℚ):ℝ) * att jj ≤ ((aoHi 19:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo19 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 19:ℚ):ℝ) - (((-833717/8388608):ℚ):ℝ) ≤ ∑ jj, min (((Wo19 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo19 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo19, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo19 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo19 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 19:ℚ):ℝ) - (((-833717/8388608):ℚ):ℝ) := by
      simp only [aoHi, Wo19, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c20 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 20:ℚ):ℝ) ≤ (((-13648761/536870912):ℚ):ℝ) + ∑ jj, ((Wo20 jj:ℚ):ℝ) * att jj ∧
    (((-13648761/536870912):ℚ):ℝ) + ∑ jj, ((Wo20 jj:ℚ):ℝ) * att jj ≤ ((aoHi 20:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo20 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 20:ℚ):ℝ) - (((-13648761/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wo20 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo20 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo20, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo20 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo20 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 20:ℚ):ℝ) - (((-13648761/536870912):ℚ):ℝ) := by
      simp only [aoHi, Wo20, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c21 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 21:ℚ):ℝ) ≤ (((339505/33554432):ℚ):ℝ) + ∑ jj, ((Wo21 jj:ℚ):ℝ) * att jj ∧
    (((339505/33554432):ℚ):ℝ) + ∑ jj, ((Wo21 jj:ℚ):ℝ) * att jj ≤ ((aoHi 21:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo21 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 21:ℚ):ℝ) - (((339505/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo21 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo21 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo21, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo21 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo21 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 21:ℚ):ℝ) - (((339505/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo21, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c22 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 22:ℚ):ℝ) ≤ (((8418327/67108864):ℚ):ℝ) + ∑ jj, ((Wo22 jj:ℚ):ℝ) * att jj ∧
    (((8418327/67108864):ℚ):ℝ) + ∑ jj, ((Wo22 jj:ℚ):ℝ) * att jj ≤ ((aoHi 22:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo22 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 22:ℚ):ℝ) - (((8418327/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo22 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo22 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo22, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo22 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo22 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 22:ℚ):ℝ) - (((8418327/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo22, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c23 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 23:ℚ):ℝ) ≤ (((14200207/1073741824):ℚ):ℝ) + ∑ jj, ((Wo23 jj:ℚ):ℝ) * att jj ∧
    (((14200207/1073741824):ℚ):ℝ) + ∑ jj, ((Wo23 jj:ℚ):ℝ) * att jj ≤ ((aoHi 23:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo23 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 23:ℚ):ℝ) - (((14200207/1073741824):ℚ):ℝ) ≤ ∑ jj, min (((Wo23 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo23 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo23, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo23 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo23 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 23:ℚ):ℝ) - (((14200207/1073741824):ℚ):ℝ) := by
      simp only [aoHi, Wo23, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c24 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 24:ℚ):ℝ) ≤ (((7237779/67108864):ℚ):ℝ) + ∑ jj, ((Wo24 jj:ℚ):ℝ) * att jj ∧
    (((7237779/67108864):ℚ):ℝ) + ∑ jj, ((Wo24 jj:ℚ):ℝ) * att jj ≤ ((aoHi 24:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo24 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 24:ℚ):ℝ) - (((7237779/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo24 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo24 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo24, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo24 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo24 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 24:ℚ):ℝ) - (((7237779/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo24, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c25 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 25:ℚ):ℝ) ≤ (((-188539/2097152):ℚ):ℝ) + ∑ jj, ((Wo25 jj:ℚ):ℝ) * att jj ∧
    (((-188539/2097152):ℚ):ℝ) + ∑ jj, ((Wo25 jj:ℚ):ℝ) * att jj ≤ ((aoHi 25:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo25 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 25:ℚ):ℝ) - (((-188539/2097152):ℚ):ℝ) ≤ ∑ jj, min (((Wo25 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo25 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo25, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo25 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo25 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 25:ℚ):ℝ) - (((-188539/2097152):ℚ):ℝ) := by
      simp only [aoHi, Wo25, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c26 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 26:ℚ):ℝ) ≤ (((10850525/134217728):ℚ):ℝ) + ∑ jj, ((Wo26 jj:ℚ):ℝ) * att jj ∧
    (((10850525/134217728):ℚ):ℝ) + ∑ jj, ((Wo26 jj:ℚ):ℝ) * att jj ≤ ((aoHi 26:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo26 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 26:ℚ):ℝ) - (((10850525/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo26 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo26 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo26, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo26 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo26 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 26:ℚ):ℝ) - (((10850525/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo26, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c27 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 27:ℚ):ℝ) ≤ (((16254697/134217728):ℚ):ℝ) + ∑ jj, ((Wo27 jj:ℚ):ℝ) * att jj ∧
    (((16254697/134217728):ℚ):ℝ) + ∑ jj, ((Wo27 jj:ℚ):ℝ) * att jj ≤ ((aoHi 27:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo27 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 27:ℚ):ℝ) - (((16254697/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo27 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo27 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo27, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo27 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo27 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 27:ℚ):ℝ) - (((16254697/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo27, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c28 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 28:ℚ):ℝ) ≤ (((-11413475/134217728):ℚ):ℝ) + ∑ jj, ((Wo28 jj:ℚ):ℝ) * att jj ∧
    (((-11413475/134217728):ℚ):ℝ) + ∑ jj, ((Wo28 jj:ℚ):ℝ) * att jj ≤ ((aoHi 28:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo28 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 28:ℚ):ℝ) - (((-11413475/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo28 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo28 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo28, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo28 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo28 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 28:ℚ):ℝ) - (((-11413475/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo28, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c29 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 29:ℚ):ℝ) ≤ (((-11416341/268435456):ℚ):ℝ) + ∑ jj, ((Wo29 jj:ℚ):ℝ) * att jj ∧
    (((-11416341/268435456):ℚ):ℝ) + ∑ jj, ((Wo29 jj:ℚ):ℝ) * att jj ≤ ((aoHi 29:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo29 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 29:ℚ):ℝ) - (((-11416341/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo29 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo29 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo29, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo29 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo29 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 29:ℚ):ℝ) - (((-11416341/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo29, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c30 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 30:ℚ):ℝ) ≤ (((1381529/33554432):ℚ):ℝ) + ∑ jj, ((Wo30 jj:ℚ):ℝ) * att jj ∧
    (((1381529/33554432):ℚ):ℝ) + ∑ jj, ((Wo30 jj:ℚ):ℝ) * att jj ≤ ((aoHi 30:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo30 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 30:ℚ):ℝ) - (((1381529/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo30 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo30 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo30, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo30 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo30 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 30:ℚ):ℝ) - (((1381529/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo30, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c31 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 31:ℚ):ℝ) ≤ (((3774273/134217728):ℚ):ℝ) + ∑ jj, ((Wo31 jj:ℚ):ℝ) * att jj ∧
    (((3774273/134217728):ℚ):ℝ) + ∑ jj, ((Wo31 jj:ℚ):ℝ) * att jj ≤ ((aoHi 31:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo31 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 31:ℚ):ℝ) - (((3774273/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo31 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo31 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo31, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo31 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo31 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 31:ℚ):ℝ) - (((3774273/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo31, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c32 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 32:ℚ):ℝ) ≤ (((4320239/134217728):ℚ):ℝ) + ∑ jj, ((Wo32 jj:ℚ):ℝ) * att jj ∧
    (((4320239/134217728):ℚ):ℝ) + ∑ jj, ((Wo32 jj:ℚ):ℝ) * att jj ≤ ((aoHi 32:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo32 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 32:ℚ):ℝ) - (((4320239/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo32 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo32 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo32, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo32 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo32 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 32:ℚ):ℝ) - (((4320239/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo32, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c33 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 33:ℚ):ℝ) ≤ (((-8700849/268435456):ℚ):ℝ) + ∑ jj, ((Wo33 jj:ℚ):ℝ) * att jj ∧
    (((-8700849/268435456):ℚ):ℝ) + ∑ jj, ((Wo33 jj:ℚ):ℝ) * att jj ≤ ((aoHi 33:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo33 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 33:ℚ):ℝ) - (((-8700849/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo33 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo33 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo33, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo33 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo33 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 33:ℚ):ℝ) - (((-8700849/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo33, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c34 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 34:ℚ):ℝ) ≤ (((-5480185/134217728):ℚ):ℝ) + ∑ jj, ((Wo34 jj:ℚ):ℝ) * att jj ∧
    (((-5480185/134217728):ℚ):ℝ) + ∑ jj, ((Wo34 jj:ℚ):ℝ) * att jj ≤ ((aoHi 34:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo34 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 34:ℚ):ℝ) - (((-5480185/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo34 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo34 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo34, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo34 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo34 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 34:ℚ):ℝ) - (((-5480185/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo34, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c35 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 35:ℚ):ℝ) ≤ (((15054631/134217728):ℚ):ℝ) + ∑ jj, ((Wo35 jj:ℚ):ℝ) * att jj ∧
    (((15054631/134217728):ℚ):ℝ) + ∑ jj, ((Wo35 jj:ℚ):ℝ) * att jj ≤ ((aoHi 35:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo35 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 35:ℚ):ℝ) - (((15054631/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo35 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo35 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo35, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo35 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo35 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 35:ℚ):ℝ) - (((15054631/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo35, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c36 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 36:ℚ):ℝ) ≤ (((-4341217/67108864):ℚ):ℝ) + ∑ jj, ((Wo36 jj:ℚ):ℝ) * att jj ∧
    (((-4341217/67108864):ℚ):ℝ) + ∑ jj, ((Wo36 jj:ℚ):ℝ) * att jj ≤ ((aoHi 36:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo36 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 36:ℚ):ℝ) - (((-4341217/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo36 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo36 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo36, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo36 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo36 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 36:ℚ):ℝ) - (((-4341217/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo36, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c37 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 37:ℚ):ℝ) ≤ (((15440753/268435456):ℚ):ℝ) + ∑ jj, ((Wo37 jj:ℚ):ℝ) * att jj ∧
    (((15440753/268435456):ℚ):ℝ) + ∑ jj, ((Wo37 jj:ℚ):ℝ) * att jj ≤ ((aoHi 37:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo37 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 37:ℚ):ℝ) - (((15440753/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo37 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo37 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo37, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo37 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo37 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 37:ℚ):ℝ) - (((15440753/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo37, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c38 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 38:ℚ):ℝ) ≤ (((-12526709/134217728):ℚ):ℝ) + ∑ jj, ((Wo38 jj:ℚ):ℝ) * att jj ∧
    (((-12526709/134217728):ℚ):ℝ) + ∑ jj, ((Wo38 jj:ℚ):ℝ) * att jj ≤ ((aoHi 38:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo38 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 38:ℚ):ℝ) - (((-12526709/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo38 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo38 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo38, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo38 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo38 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 38:ℚ):ℝ) - (((-12526709/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo38, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c39 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 39:ℚ):ℝ) ≤ (((-15281647/134217728):ℚ):ℝ) + ∑ jj, ((Wo39 jj:ℚ):ℝ) * att jj ∧
    (((-15281647/134217728):ℚ):ℝ) + ∑ jj, ((Wo39 jj:ℚ):ℝ) * att jj ≤ ((aoHi 39:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo39 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 39:ℚ):ℝ) - (((-15281647/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo39 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo39 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo39, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo39 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo39 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 39:ℚ):ℝ) - (((-15281647/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo39, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c40 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 40:ℚ):ℝ) ≤ (((-3543553/33554432):ℚ):ℝ) + ∑ jj, ((Wo40 jj:ℚ):ℝ) * att jj ∧
    (((-3543553/33554432):ℚ):ℝ) + ∑ jj, ((Wo40 jj:ℚ):ℝ) * att jj ≤ ((aoHi 40:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo40 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 40:ℚ):ℝ) - (((-3543553/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo40 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo40 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo40, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo40 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo40 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 40:ℚ):ℝ) - (((-3543553/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo40, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c41 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 41:ℚ):ℝ) ≤ (((16264875/134217728):ℚ):ℝ) + ∑ jj, ((Wo41 jj:ℚ):ℝ) * att jj ∧
    (((16264875/134217728):ℚ):ℝ) + ∑ jj, ((Wo41 jj:ℚ):ℝ) * att jj ≤ ((aoHi 41:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo41 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 41:ℚ):ℝ) - (((16264875/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo41 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo41 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo41, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo41 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo41 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 41:ℚ):ℝ) - (((16264875/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo41, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c42 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 42:ℚ):ℝ) ≤ (((-1592109/33554432):ℚ):ℝ) + ∑ jj, ((Wo42 jj:ℚ):ℝ) * att jj ∧
    (((-1592109/33554432):ℚ):ℝ) + ∑ jj, ((Wo42 jj:ℚ):ℝ) * att jj ≤ ((aoHi 42:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo42 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 42:ℚ):ℝ) - (((-1592109/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wo42 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo42 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo42, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo42 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo42 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 42:ℚ):ℝ) - (((-1592109/33554432):ℚ):ℝ) := by
      simp only [aoHi, Wo42, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c43 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 43:ℚ):ℝ) ≤ (((-6226875/67108864):ℚ):ℝ) + ∑ jj, ((Wo43 jj:ℚ):ℝ) * att jj ∧
    (((-6226875/67108864):ℚ):ℝ) + ∑ jj, ((Wo43 jj:ℚ):ℝ) * att jj ≤ ((aoHi 43:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo43 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 43:ℚ):ℝ) - (((-6226875/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wo43 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo43 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo43, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo43 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo43 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 43:ℚ):ℝ) - (((-6226875/67108864):ℚ):ℝ) := by
      simp only [aoHi, Wo43, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c44 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 44:ℚ):ℝ) ≤ (((5216749/268435456):ℚ):ℝ) + ∑ jj, ((Wo44 jj:ℚ):ℝ) * att jj ∧
    (((5216749/268435456):ℚ):ℝ) + ∑ jj, ((Wo44 jj:ℚ):ℝ) * att jj ≤ ((aoHi 44:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo44 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 44:ℚ):ℝ) - (((5216749/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wo44 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo44 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo44, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo44 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo44 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 44:ℚ):ℝ) - (((5216749/268435456):ℚ):ℝ) := by
      simp only [aoHi, Wo44, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c45 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 45:ℚ):ℝ) ≤ (((16662505/134217728):ℚ):ℝ) + ∑ jj, ((Wo45 jj:ℚ):ℝ) * att jj ∧
    (((16662505/134217728):ℚ):ℝ) + ∑ jj, ((Wo45 jj:ℚ):ℝ) * att jj ≤ ((aoHi 45:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo45 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 45:ℚ):ℝ) - (((16662505/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wo45 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo45 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo45, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo45 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo45 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 45:ℚ):ℝ) - (((16662505/134217728):ℚ):ℝ) := by
      simp only [aoHi, Wo45, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c46 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 46:ℚ):ℝ) ≤ (((13866335/17179869184):ℚ):ℝ) + ∑ jj, ((Wo46 jj:ℚ):ℝ) * att jj ∧
    (((13866335/17179869184):ℚ):ℝ) + ∑ jj, ((Wo46 jj:ℚ):ℝ) * att jj ≤ ((aoHi 46:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo46 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 46:ℚ):ℝ) - (((13866335/17179869184):ℚ):ℝ) ≤ ∑ jj, min (((Wo46 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo46 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo46, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo46 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo46 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 46:ℚ):ℝ) - (((13866335/17179869184):ℚ):ℝ) := by
      simp only [aoHi, Wo46, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem ao_c47 (att : Fin 48 → ℝ)
    (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ((aoLo 47:ℚ):ℝ) ≤ (((10913905/536870912):ℚ):ℝ) + ∑ jj, ((Wo47 jj:ℚ):ℝ) * att jj ∧
    (((10913905/536870912):ℚ):ℝ) + ∑ jj, ((Wo47 jj:ℚ):ℝ) * att jj ≤ ((aoHi 47:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wo47 jj:ℚ):ℝ)) (fun jj => ((vLo jj:ℚ):ℝ)) (fun jj => ((vHi jj:ℚ):ℝ)) att hl hh
  refine ⟨?_,?_⟩
  · have hs : ((aoLo 47:ℚ):ℝ) - (((10913905/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wo47 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo47 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ)) := by
      simp only [aoLo, Wo47, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wo47 jj:ℚ):ℝ)*((vLo jj:ℚ):ℝ)) (((Wo47 jj:ℚ):ℝ)*((vHi jj:ℚ):ℝ))) ≤ ((aoHi 47:ℚ):ℝ) - (((10913905/536870912):ℚ):ℝ) := by
      simp only [aoHi, Wo47, vLo, vHi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]


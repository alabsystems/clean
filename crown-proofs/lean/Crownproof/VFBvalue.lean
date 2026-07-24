import Crownproof.VitFullBlock
open Crownproof Crownproof.VitFullBlock Real Finset
namespace Crownproof.VitFullBlock
set_option maxHeartbeats 2000000

theorem value_c0 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 0:ℚ):ℝ) ≤ (((637035/4194304):ℚ):ℝ) + ∑ jj, ((Wv0 jj:ℚ):ℝ) * n1 jj ∧
    (((637035/4194304):ℚ):ℝ) + ∑ jj, ((Wv0 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 0:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv0 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 0:ℚ):ℝ) - (((637035/4194304):ℚ):ℝ) ≤ ∑ jj, min (((Wv0 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv0 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv0, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv0 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv0 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 0:ℚ):ℝ) - (((637035/4194304):ℚ):ℝ) := by
      simp only [vHi, Wv0, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c1 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 1:ℚ):ℝ) ≤ (((8623141/268435456):ℚ):ℝ) + ∑ jj, ((Wv1 jj:ℚ):ℝ) * n1 jj ∧
    (((8623141/268435456):ℚ):ℝ) + ∑ jj, ((Wv1 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 1:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv1 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 1:ℚ):ℝ) - (((8623141/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv1 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv1 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv1, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv1 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv1 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 1:ℚ):ℝ) - (((8623141/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv1, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c2 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 2:ℚ):ℝ) ≤ (((-11402589/268435456):ℚ):ℝ) + ∑ jj, ((Wv2 jj:ℚ):ℝ) * n1 jj ∧
    (((-11402589/268435456):ℚ):ℝ) + ∑ jj, ((Wv2 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 2:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv2 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 2:ℚ):ℝ) - (((-11402589/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv2 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv2 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv2, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv2 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv2 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 2:ℚ):ℝ) - (((-11402589/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv2, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c3 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 3:ℚ):ℝ) ≤ (((5929069/268435456):ℚ):ℝ) + ∑ jj, ((Wv3 jj:ℚ):ℝ) * n1 jj ∧
    (((5929069/268435456):ℚ):ℝ) + ∑ jj, ((Wv3 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 3:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv3 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 3:ℚ):ℝ) - (((5929069/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv3 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv3 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv3, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv3 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv3 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 3:ℚ):ℝ) - (((5929069/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv3, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c4 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 4:ℚ):ℝ) ≤ (((-11034523/1073741824):ℚ):ℝ) + ∑ jj, ((Wv4 jj:ℚ):ℝ) * n1 jj ∧
    (((-11034523/1073741824):ℚ):ℝ) + ∑ jj, ((Wv4 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 4:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv4 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 4:ℚ):ℝ) - (((-11034523/1073741824):ℚ):ℝ) ≤ ∑ jj, min (((Wv4 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv4 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv4, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv4 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv4 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 4:ℚ):ℝ) - (((-11034523/1073741824):ℚ):ℝ) := by
      simp only [vHi, Wv4, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c5 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 5:ℚ):ℝ) ≤ (((-8912905/2147483648):ℚ):ℝ) + ∑ jj, ((Wv5 jj:ℚ):ℝ) * n1 jj ∧
    (((-8912905/2147483648):ℚ):ℝ) + ∑ jj, ((Wv5 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 5:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv5 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 5:ℚ):ℝ) - (((-8912905/2147483648):ℚ):ℝ) ≤ ∑ jj, min (((Wv5 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv5 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv5, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv5 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv5 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 5:ℚ):ℝ) - (((-8912905/2147483648):ℚ):ℝ) := by
      simp only [vHi, Wv5, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c6 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 6:ℚ):ℝ) ≤ (((14131957/4294967296):ℚ):ℝ) + ∑ jj, ((Wv6 jj:ℚ):ℝ) * n1 jj ∧
    (((14131957/4294967296):ℚ):ℝ) + ∑ jj, ((Wv6 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 6:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv6 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 6:ℚ):ℝ) - (((14131957/4294967296):ℚ):ℝ) ≤ ∑ jj, min (((Wv6 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv6 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv6, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv6 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv6 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 6:ℚ):ℝ) - (((14131957/4294967296):ℚ):ℝ) := by
      simp only [vHi, Wv6, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c7 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 7:ℚ):ℝ) ≤ (((15055495/536870912):ℚ):ℝ) + ∑ jj, ((Wv7 jj:ℚ):ℝ) * n1 jj ∧
    (((15055495/536870912):ℚ):ℝ) + ∑ jj, ((Wv7 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 7:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv7 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 7:ℚ):ℝ) - (((15055495/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wv7 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv7 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv7, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv7 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv7 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 7:ℚ):ℝ) - (((15055495/536870912):ℚ):ℝ) := by
      simp only [vHi, Wv7, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c8 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 8:ℚ):ℝ) ≤ (((-8868687/67108864):ℚ):ℝ) + ∑ jj, ((Wv8 jj:ℚ):ℝ) * n1 jj ∧
    (((-8868687/67108864):ℚ):ℝ) + ∑ jj, ((Wv8 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 8:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv8 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 8:ℚ):ℝ) - (((-8868687/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv8 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv8 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv8, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv8 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv8 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 8:ℚ):ℝ) - (((-8868687/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv8, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c9 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 9:ℚ):ℝ) ≤ (((12750141/134217728):ℚ):ℝ) + ∑ jj, ((Wv9 jj:ℚ):ℝ) * n1 jj ∧
    (((12750141/134217728):ℚ):ℝ) + ∑ jj, ((Wv9 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 9:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv9 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 9:ℚ):ℝ) - (((12750141/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv9 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv9 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv9, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv9 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv9 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 9:ℚ):ℝ) - (((12750141/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv9, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c10 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 10:ℚ):ℝ) ≤ (((9052091/67108864):ℚ):ℝ) + ∑ jj, ((Wv10 jj:ℚ):ℝ) * n1 jj ∧
    (((9052091/67108864):ℚ):ℝ) + ∑ jj, ((Wv10 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 10:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv10 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 10:ℚ):ℝ) - (((9052091/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv10 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv10 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv10, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv10 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv10 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 10:ℚ):ℝ) - (((9052091/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv10, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c11 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 11:ℚ):ℝ) ≤ (((-12969957/134217728):ℚ):ℝ) + ∑ jj, ((Wv11 jj:ℚ):ℝ) * n1 jj ∧
    (((-12969957/134217728):ℚ):ℝ) + ∑ jj, ((Wv11 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 11:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv11 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 11:ℚ):ℝ) - (((-12969957/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv11 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv11 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv11, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv11 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv11 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 11:ℚ):ℝ) - (((-12969957/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv11, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c12 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 12:ℚ):ℝ) ≤ (((-8986967/536870912):ℚ):ℝ) + ∑ jj, ((Wv12 jj:ℚ):ℝ) * n1 jj ∧
    (((-8986967/536870912):ℚ):ℝ) + ∑ jj, ((Wv12 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 12:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv12 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 12:ℚ):ℝ) - (((-8986967/536870912):ℚ):ℝ) ≤ ∑ jj, min (((Wv12 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv12 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv12, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv12 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv12 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 12:ℚ):ℝ) - (((-8986967/536870912):ℚ):ℝ) := by
      simp only [vHi, Wv12, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c13 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 13:ℚ):ℝ) ≤ (((14730433/134217728):ℚ):ℝ) + ∑ jj, ((Wv13 jj:ℚ):ℝ) * n1 jj ∧
    (((14730433/134217728):ℚ):ℝ) + ∑ jj, ((Wv13 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 13:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv13 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 13:ℚ):ℝ) - (((14730433/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv13 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv13 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv13, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv13 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv13 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 13:ℚ):ℝ) - (((14730433/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv13, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c14 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 14:ℚ):ℝ) ≤ (((-15885221/268435456):ℚ):ℝ) + ∑ jj, ((Wv14 jj:ℚ):ℝ) * n1 jj ∧
    (((-15885221/268435456):ℚ):ℝ) + ∑ jj, ((Wv14 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 14:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv14 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 14:ℚ):ℝ) - (((-15885221/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv14 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv14 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv14, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv14 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv14 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 14:ℚ):ℝ) - (((-15885221/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv14, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c15 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 15:ℚ):ℝ) ≤ (((-11412131/134217728):ℚ):ℝ) + ∑ jj, ((Wv15 jj:ℚ):ℝ) * n1 jj ∧
    (((-11412131/134217728):ℚ):ℝ) + ∑ jj, ((Wv15 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 15:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv15 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 15:ℚ):ℝ) - (((-11412131/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv15 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv15 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv15, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv15 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv15 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 15:ℚ):ℝ) - (((-11412131/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv15, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c16 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 16:ℚ):ℝ) ≤ (((5205779/67108864):ℚ):ℝ) + ∑ jj, ((Wv16 jj:ℚ):ℝ) * n1 jj ∧
    (((5205779/67108864):ℚ):ℝ) + ∑ jj, ((Wv16 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 16:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv16 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 16:ℚ):ℝ) - (((5205779/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv16 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv16 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv16, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv16 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv16 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 16:ℚ):ℝ) - (((5205779/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv16, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c17 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 17:ℚ):ℝ) ≤ (((-10952625/268435456):ℚ):ℝ) + ∑ jj, ((Wv17 jj:ℚ):ℝ) * n1 jj ∧
    (((-10952625/268435456):ℚ):ℝ) + ∑ jj, ((Wv17 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 17:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv17 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 17:ℚ):ℝ) - (((-10952625/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv17 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv17 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv17, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv17 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv17 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 17:ℚ):ℝ) - (((-10952625/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv17, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c18 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 18:ℚ):ℝ) ≤ (((8297445/134217728):ℚ):ℝ) + ∑ jj, ((Wv18 jj:ℚ):ℝ) * n1 jj ∧
    (((8297445/134217728):ℚ):ℝ) + ∑ jj, ((Wv18 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 18:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv18 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 18:ℚ):ℝ) - (((8297445/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv18 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv18 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv18, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv18 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv18 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 18:ℚ):ℝ) - (((8297445/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv18, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c19 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 19:ℚ):ℝ) ≤ (((-7803393/134217728):ℚ):ℝ) + ∑ jj, ((Wv19 jj:ℚ):ℝ) * n1 jj ∧
    (((-7803393/134217728):ℚ):ℝ) + ∑ jj, ((Wv19 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 19:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv19 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 19:ℚ):ℝ) - (((-7803393/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv19 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv19 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv19, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv19 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv19 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 19:ℚ):ℝ) - (((-7803393/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv19, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c20 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 20:ℚ):ℝ) ≤ (((14953293/134217728):ℚ):ℝ) + ∑ jj, ((Wv20 jj:ℚ):ℝ) * n1 jj ∧
    (((14953293/134217728):ℚ):ℝ) + ∑ jj, ((Wv20 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 20:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv20 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 20:ℚ):ℝ) - (((14953293/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv20 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv20 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv20, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv20 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv20 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 20:ℚ):ℝ) - (((14953293/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv20, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c21 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 21:ℚ):ℝ) ≤ (((902631/8388608):ℚ):ℝ) + ∑ jj, ((Wv21 jj:ℚ):ℝ) * n1 jj ∧
    (((902631/8388608):ℚ):ℝ) + ∑ jj, ((Wv21 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 21:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv21 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 21:ℚ):ℝ) - (((902631/8388608):ℚ):ℝ) ≤ ∑ jj, min (((Wv21 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv21 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv21, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv21 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv21 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 21:ℚ):ℝ) - (((902631/8388608):ℚ):ℝ) := by
      simp only [vHi, Wv21, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c22 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 22:ℚ):ℝ) ≤ (((3554927/33554432):ℚ):ℝ) + ∑ jj, ((Wv22 jj:ℚ):ℝ) * n1 jj ∧
    (((3554927/33554432):ℚ):ℝ) + ∑ jj, ((Wv22 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 22:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv22 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 22:ℚ):ℝ) - (((3554927/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wv22 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv22 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv22, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv22 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv22 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 22:ℚ):ℝ) - (((3554927/33554432):ℚ):ℝ) := by
      simp only [vHi, Wv22, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c23 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 23:ℚ):ℝ) ≤ (((-12956763/268435456):ℚ):ℝ) + ∑ jj, ((Wv23 jj:ℚ):ℝ) * n1 jj ∧
    (((-12956763/268435456):ℚ):ℝ) + ∑ jj, ((Wv23 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 23:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv23 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 23:ℚ):ℝ) - (((-12956763/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv23 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv23 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv23, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv23 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv23 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 23:ℚ):ℝ) - (((-12956763/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv23, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c24 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 24:ℚ):ℝ) ≤ (((5541929/33554432):ℚ):ℝ) + ∑ jj, ((Wv24 jj:ℚ):ℝ) * n1 jj ∧
    (((5541929/33554432):ℚ):ℝ) + ∑ jj, ((Wv24 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 24:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv24 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 24:ℚ):ℝ) - (((5541929/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wv24 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv24 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv24, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv24 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv24 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 24:ℚ):ℝ) - (((5541929/33554432):ℚ):ℝ) := by
      simp only [vHi, Wv24, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c25 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 25:ℚ):ℝ) ≤ (((-13757819/1073741824):ℚ):ℝ) + ∑ jj, ((Wv25 jj:ℚ):ℝ) * n1 jj ∧
    (((-13757819/1073741824):ℚ):ℝ) + ∑ jj, ((Wv25 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 25:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv25 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 25:ℚ):ℝ) - (((-13757819/1073741824):ℚ):ℝ) ≤ ∑ jj, min (((Wv25 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv25 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv25, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv25 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv25 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 25:ℚ):ℝ) - (((-13757819/1073741824):ℚ):ℝ) := by
      simp only [vHi, Wv25, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c26 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 26:ℚ):ℝ) ≤ (((13631803/134217728):ℚ):ℝ) + ∑ jj, ((Wv26 jj:ℚ):ℝ) * n1 jj ∧
    (((13631803/134217728):ℚ):ℝ) + ∑ jj, ((Wv26 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 26:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv26 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 26:ℚ):ℝ) - (((13631803/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv26 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv26 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv26, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv26 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv26 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 26:ℚ):ℝ) - (((13631803/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv26, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c27 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 27:ℚ):ℝ) ≤ (((-12564167/268435456):ℚ):ℝ) + ∑ jj, ((Wv27 jj:ℚ):ℝ) * n1 jj ∧
    (((-12564167/268435456):ℚ):ℝ) + ∑ jj, ((Wv27 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 27:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv27 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 27:ℚ):ℝ) - (((-12564167/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv27 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv27 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv27, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv27 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv27 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 27:ℚ):ℝ) - (((-12564167/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv27, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c28 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 28:ℚ):ℝ) ≤ (((2160099/33554432):ℚ):ℝ) + ∑ jj, ((Wv28 jj:ℚ):ℝ) * n1 jj ∧
    (((2160099/33554432):ℚ):ℝ) + ∑ jj, ((Wv28 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 28:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv28 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 28:ℚ):ℝ) - (((2160099/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wv28 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv28 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv28, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv28 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv28 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 28:ℚ):ℝ) - (((2160099/33554432):ℚ):ℝ) := by
      simp only [vHi, Wv28, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c29 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 29:ℚ):ℝ) ≤ (((-13856073/134217728):ℚ):ℝ) + ∑ jj, ((Wv29 jj:ℚ):ℝ) * n1 jj ∧
    (((-13856073/134217728):ℚ):ℝ) + ∑ jj, ((Wv29 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 29:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv29 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 29:ℚ):ℝ) - (((-13856073/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv29 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv29 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv29, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv29 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv29 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 29:ℚ):ℝ) - (((-13856073/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv29, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c30 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 30:ℚ):ℝ) ≤ (((2754177/67108864):ℚ):ℝ) + ∑ jj, ((Wv30 jj:ℚ):ℝ) * n1 jj ∧
    (((2754177/67108864):ℚ):ℝ) + ∑ jj, ((Wv30 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 30:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv30 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 30:ℚ):ℝ) - (((2754177/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv30 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv30 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv30, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv30 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv30 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 30:ℚ):ℝ) - (((2754177/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv30, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c31 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 31:ℚ):ℝ) ≤ (((4402007/67108864):ℚ):ℝ) + ∑ jj, ((Wv31 jj:ℚ):ℝ) * n1 jj ∧
    (((4402007/67108864):ℚ):ℝ) + ∑ jj, ((Wv31 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 31:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv31 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 31:ℚ):ℝ) - (((4402007/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv31 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv31 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv31, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv31 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv31 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 31:ℚ):ℝ) - (((4402007/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv31, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c32 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 32:ℚ):ℝ) ≤ (((12400953/67108864):ℚ):ℝ) + ∑ jj, ((Wv32 jj:ℚ):ℝ) * n1 jj ∧
    (((12400953/67108864):ℚ):ℝ) + ∑ jj, ((Wv32 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 32:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv32 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 32:ℚ):ℝ) - (((12400953/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv32 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv32 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv32, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv32 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv32 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 32:ℚ):ℝ) - (((12400953/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv32, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c33 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 33:ℚ):ℝ) ≤ (((-9308059/67108864):ℚ):ℝ) + ∑ jj, ((Wv33 jj:ℚ):ℝ) * n1 jj ∧
    (((-9308059/67108864):ℚ):ℝ) + ∑ jj, ((Wv33 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 33:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv33 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 33:ℚ):ℝ) - (((-9308059/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv33 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv33 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv33, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv33 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv33 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 33:ℚ):ℝ) - (((-9308059/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv33, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c34 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 34:ℚ):ℝ) ≤ (((7914533/268435456):ℚ):ℝ) + ∑ jj, ((Wv34 jj:ℚ):ℝ) * n1 jj ∧
    (((7914533/268435456):ℚ):ℝ) + ∑ jj, ((Wv34 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 34:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv34 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 34:ℚ):ℝ) - (((7914533/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv34 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv34 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv34, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv34 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv34 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 34:ℚ):ℝ) - (((7914533/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv34, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c35 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 35:ℚ):ℝ) ≤ (((-8496707/67108864):ℚ):ℝ) + ∑ jj, ((Wv35 jj:ℚ):ℝ) * n1 jj ∧
    (((-8496707/67108864):ℚ):ℝ) + ∑ jj, ((Wv35 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 35:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv35 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 35:ℚ):ℝ) - (((-8496707/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv35 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv35 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv35, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv35 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv35 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 35:ℚ):ℝ) - (((-8496707/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv35, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c36 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 36:ℚ):ℝ) ≤ (((-8491777/67108864):ℚ):ℝ) + ∑ jj, ((Wv36 jj:ℚ):ℝ) * n1 jj ∧
    (((-8491777/67108864):ℚ):ℝ) + ∑ jj, ((Wv36 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 36:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv36 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 36:ℚ):ℝ) - (((-8491777/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv36 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv36 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv36, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv36 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv36 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 36:ℚ):ℝ) - (((-8491777/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv36, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c37 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 37:ℚ):ℝ) ≤ (((3444655/33554432):ℚ):ℝ) + ∑ jj, ((Wv37 jj:ℚ):ℝ) * n1 jj ∧
    (((3444655/33554432):ℚ):ℝ) + ∑ jj, ((Wv37 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 37:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv37 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 37:ℚ):ℝ) - (((3444655/33554432):ℚ):ℝ) ≤ ∑ jj, min (((Wv37 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv37 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv37, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv37 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv37 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 37:ℚ):ℝ) - (((3444655/33554432):ℚ):ℝ) := by
      simp only [vHi, Wv37, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c38 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 38:ℚ):ℝ) ≤ (((9337207/134217728):ℚ):ℝ) + ∑ jj, ((Wv38 jj:ℚ):ℝ) * n1 jj ∧
    (((9337207/134217728):ℚ):ℝ) + ∑ jj, ((Wv38 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 38:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv38 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 38:ℚ):ℝ) - (((9337207/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv38 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv38 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv38, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv38 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv38 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 38:ℚ):ℝ) - (((9337207/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv38, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c39 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 39:ℚ):ℝ) ≤ (((16032367/134217728):ℚ):ℝ) + ∑ jj, ((Wv39 jj:ℚ):ℝ) * n1 jj ∧
    (((16032367/134217728):ℚ):ℝ) + ∑ jj, ((Wv39 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 39:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv39 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 39:ℚ):ℝ) - (((16032367/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv39 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv39 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv39, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv39 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv39 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 39:ℚ):ℝ) - (((16032367/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv39, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c40 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 40:ℚ):ℝ) ≤ (((5497051/67108864):ℚ):ℝ) + ∑ jj, ((Wv40 jj:ℚ):ℝ) * n1 jj ∧
    (((5497051/67108864):ℚ):ℝ) + ∑ jj, ((Wv40 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 40:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv40 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 40:ℚ):ℝ) - (((5497051/67108864):ℚ):ℝ) ≤ ∑ jj, min (((Wv40 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv40 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv40, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv40 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv40 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 40:ℚ):ℝ) - (((5497051/67108864):ℚ):ℝ) := by
      simp only [vHi, Wv40, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c41 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 41:ℚ):ℝ) ≤ (((-533143/8388608):ℚ):ℝ) + ∑ jj, ((Wv41 jj:ℚ):ℝ) * n1 jj ∧
    (((-533143/8388608):ℚ):ℝ) + ∑ jj, ((Wv41 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 41:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv41 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 41:ℚ):ℝ) - (((-533143/8388608):ℚ):ℝ) ≤ ∑ jj, min (((Wv41 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv41 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv41, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv41 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv41 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 41:ℚ):ℝ) - (((-533143/8388608):ℚ):ℝ) := by
      simp only [vHi, Wv41, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c42 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 42:ℚ):ℝ) ≤ (((11063695/4294967296):ℚ):ℝ) + ∑ jj, ((Wv42 jj:ℚ):ℝ) * n1 jj ∧
    (((11063695/4294967296):ℚ):ℝ) + ∑ jj, ((Wv42 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 42:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv42 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 42:ℚ):ℝ) - (((11063695/4294967296):ℚ):ℝ) ≤ ∑ jj, min (((Wv42 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv42 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv42, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv42 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv42 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 42:ℚ):ℝ) - (((11063695/4294967296):ℚ):ℝ) := by
      simp only [vHi, Wv42, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c43 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 43:ℚ):ℝ) ≤ (((15721161/134217728):ℚ):ℝ) + ∑ jj, ((Wv43 jj:ℚ):ℝ) * n1 jj ∧
    (((15721161/134217728):ℚ):ℝ) + ∑ jj, ((Wv43 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 43:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv43 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 43:ℚ):ℝ) - (((15721161/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv43 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv43 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv43, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv43 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv43 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 43:ℚ):ℝ) - (((15721161/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv43, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c44 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 44:ℚ):ℝ) ≤ (((-4202759/268435456):ℚ):ℝ) + ∑ jj, ((Wv44 jj:ℚ):ℝ) * n1 jj ∧
    (((-4202759/268435456):ℚ):ℝ) + ∑ jj, ((Wv44 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 44:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv44 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 44:ℚ):ℝ) - (((-4202759/268435456):ℚ):ℝ) ≤ ∑ jj, min (((Wv44 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv44 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv44, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv44 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv44 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 44:ℚ):ℝ) - (((-4202759/268435456):ℚ):ℝ) := by
      simp only [vHi, Wv44, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c45 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 45:ℚ):ℝ) ≤ (((2169457/16777216):ℚ):ℝ) + ∑ jj, ((Wv45 jj:ℚ):ℝ) * n1 jj ∧
    (((2169457/16777216):ℚ):ℝ) + ∑ jj, ((Wv45 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 45:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv45 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 45:ℚ):ℝ) - (((2169457/16777216):ℚ):ℝ) ≤ ∑ jj, min (((Wv45 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv45 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv45, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv45 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv45 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 45:ℚ):ℝ) - (((2169457/16777216):ℚ):ℝ) := by
      simp only [vHi, Wv45, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c46 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 46:ℚ):ℝ) ≤ (((-332127/16777216):ℚ):ℝ) + ∑ jj, ((Wv46 jj:ℚ):ℝ) * n1 jj ∧
    (((-332127/16777216):ℚ):ℝ) + ∑ jj, ((Wv46 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 46:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv46 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 46:ℚ):ℝ) - (((-332127/16777216):ℚ):ℝ) ≤ ∑ jj, min (((Wv46 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv46 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv46, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv46 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv46 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 46:ℚ):ℝ) - (((-332127/16777216):ℚ):ℝ) := by
      simp only [vHi, Wv46, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]

theorem value_c47 (n1 : Fin 48 → ℝ)
    (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ((vLo 47:ℚ):ℝ) ≤ (((11280707/134217728):ℚ):ℝ) + ∑ jj, ((Wv47 jj:ℚ):ℝ) * n1 jj ∧
    (((11280707/134217728):ℚ):ℝ) + ∑ jj, ((Wv47 jj:ℚ):ℝ) * n1 jj ≤ ((vHi 47:ℚ):ℝ) := by
  have hd := dot_ibpR (fun jj => ((Wv47 jj:ℚ):ℝ)) (fun jj => ((n1Lo jj:ℚ):ℝ)) (fun jj => ((n1Hi jj:ℚ):ℝ)) n1 hl hh
  refine ⟨?_,?_⟩
  · have hs : ((vLo 47:ℚ):ℝ) - (((11280707/134217728):ℚ):ℝ) ≤ ∑ jj, min (((Wv47 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv47 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ)) := by
      simp only [vLo, Wv47, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.1, hs]
  · have hs : (∑ jj, max (((Wv47 jj:ℚ):ℝ)*((n1Lo jj:ℚ):ℝ)) (((Wv47 jj:ℚ):ℝ)*((n1Hi jj:ℚ):ℝ))) ≤ ((vHi 47:ℚ):ℝ) - (((11280707/134217728):ℚ):ℝ) := by
      simp only [vHi, Wv47, n1Lo, n1Hi, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]; push_cast; norm_num
    linarith [hd.2, hs]


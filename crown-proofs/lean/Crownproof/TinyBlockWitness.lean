import Crownproof.TinyBlock
namespace Crownproof.TinyBlock
open Crownproof
-- Non-vacuity: the genuine-execution predicate is inhabited at the LOWER-tight corner
-- x=0, att=-1/2 (p0=0,p1=1), t=1/2  => h=-1/2, p=-1/4, ln=-1/4, z=-3/4, mr=0, m=0, o=-1/2.
-- and at the UPPER-tight corner x=1, att=1/2 (p0=1,p1=0), t=1 => h=3/2,p=3/2,ln=3/2,z=1,mr=1,m=1,o=5/2.
def stLo : TBState :=
  { p0 := 0, p1 := 1, x := 0, att := -1/2, h := -1/2, t := 1/2,
    p := -1/4, ln := -1/4, z := -3/4, mr := 0, m := 0, o := -1/2 }
def stHi : TBState :=
  { p0 := 1, p1 := 0, x := 1, att := 1/2, h := 3/2, t := 1,
    p := 3/2, ln := 3/2, z := 1, mr := 1, m := 1, o := 5/2 }
theorem stLo_valid : stLo.valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [stLo, relu] <;> norm_num
theorem stHi_valid : stHi.valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [stHi, relu] <;> norm_num
-- the bound is attained, so it is TIGHT (not vacuous, not loose):
theorem lower_attained : stLo.o = -1/2 := rfl
theorem upper_attained : stHi.o = 5/2 := rfl
-- and both endpoints satisfy the proven bound:
example : (-1/2 : ℚ) ≤ stLo.o ∧ stLo.o ≤ (5/2:ℚ) := tinyblock_bound stLo stLo_valid
example : (-1/2 : ℚ) ≤ stHi.o ∧ stHi.o ≤ (5/2:ℚ) := tinyblock_bound stHi stHi_valid
#print axioms stLo_valid
#print axioms stHi_valid
end Crownproof.TinyBlock

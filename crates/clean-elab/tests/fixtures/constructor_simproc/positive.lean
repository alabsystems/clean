-- Pinned Lean 4.30: distinct constructors only, with ordinary simproc scope.
theorem ctorNamed (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp only [reduceCtorEq] at h

theorem ctorDefault (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp at h

theorem ctorReadded (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp only [reduceCtorEq, -reduceCtorEq, reduceCtorEq] at h

theorem ctorEqFalse (n : Nat) : ((none : Option Nat) = some n) = False := by
  simp only [reduceCtorEq]

theorem ctorAll (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp_all only [reduceCtorEq]

theorem ctorWildcard (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp only [reduceCtorEq] at *

theorem ctorSimpa (n : Nat) : ((none : Option Nat) = some n) = False := by
  simpa only [reduceCtorEq]

abbrev ctorNone : Option Nat := none

theorem ctorAlias (n : Nat) (h : ctorNone = some n) : False := by
  simp only [reduceCtorEq] at h

theorem ctorLocalShadow (n m : Nat) (reduceCtorEq : n = m) : n = m := by
  simp only [reduceCtorEq]

theorem ctorDefaultReadded (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp [-reduceCtorEq, reduceCtorEq] at h

theorem ctorNested (n : Nat) (h : (none : Option Nat) = some n) : False := by
  have hf : False := by
    simp only [reduceCtorEq] at h
  exact hf

-- isSimproc recognizes a registered builtin by its resolved global name.
theorem reduceCtorEq : True := True.intro

theorem ctorRegisteredName (n : Nat) (h : (none : Option Nat) = some n) : False := by
  simp only [reduceCtorEq] at h

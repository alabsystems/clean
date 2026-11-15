/-
Laws of the unchanged canonical SpecrPrelude used by native Size/Align calls.
These facts are not a Rust library refinement: the actual primitive, source
type/representation, effects and oracle bindings must still be supplied and
checked. In particular canonical pow has a wider exponent domain than the
pinned Rust test runtime's to_u32 conversion, so that missing duty must refuse.
-/
import MiniRust

noncomputable section
namespace TrustSem.LibraryWrappers

def ValidSize (size : Int) : Prop := 0 ≤ size
def U64Domain (value : Int) : Prop := 0 ≤ value ∧ value ≤ 18446744073709551615
def PowDomain (value : Int) : Prop := 0 ≤ value ∧ value ≤ 4294967295
def ShiftDomain (value : Int) : Prop := 0 ≤ value ∧ value ≤ 340282366920938463463374607431768211455

def ConstructorGoal : Prop := ∀ value : Int,
  SSize.from_bytes value = if value < 0 then none else some value

theorem size_constructor_exact : ConstructorGoal := by
  intro value
  by_cases h : value < 0 <;> simp [SSize.from_bytes, SInt.blt, h]

theorem size_constructor_some_iff (value result : Int) :
    SSize.from_bytes value = some result ↔ ValidSize value ∧ result = value := by
  rw [size_constructor_exact value]
  unfold ValidSize
  by_cases h : value < 0 <;> simp [h] <;> omega

theorem size_constructor_none_iff (value : Int) :
    SSize.from_bytes value = none ↔ value < 0 := by
  rw [size_constructor_exact value]
  by_cases h : value < 0 <;> simp [h]

theorem valid_size_constructs (value : Int) (h : ValidSize value) :
    SSize.from_bytes value = some value := by
  exact (size_constructor_some_iff value value).mpr ⟨h, rfl⟩

theorem successful_size_is_valid (value result : Int)
    (h : SSize.from_bytes value = some result) : ValidSize result := by
  rcases (size_constructor_some_iff value result).mp h with ⟨hvalid, heq⟩
  rw [heq]
  exact hvalid

theorem zero_size_constructs : SSize.from_bytes 0 = some 0 := rfl

theorem negative_size_rejected (value : Int) (h : value < 0) :
    SSize.from_bytes value = none := (size_constructor_none_iff value).mpr h

theorem constant_size_retains_u64_domain (value : Int) (h : U64Domain value) :
    U64Domain (SSize.from_bytes_const value) := h

theorem size_add_preserves_validity (left right : Int)
    (hl : ValidSize left) (hr : ValidSize right) :
    SSize.add left right = .ok (left + right) := by
  have hsum : ValidSize (left + right) := by unfold ValidSize at *; omega
  unfold SSize.add
  rw [valid_size_constructs _ hsum]

theorem size_multiply_preserves_validity (left right : Int)
    (hl : ValidSize left) (hr : 0 ≤ right) :
    SSize.mul left right = .ok (left * right) := by
  have hproduct : ValidSize (left * right) := Int.mul_nonneg hl hr
  unfold SSize.mul
  rw [valid_size_constructs _ hproduct]

theorem size_bits_exact (size : Int) : SSize.bits size = size * 8 := rfl

theorem alignment_constructor_preserves_value (value result : Int)
    (h : SAlign.from_bytes value = some result) :
    result = value ∧ SInt.is_power_of_two value = true := by
  unfold SAlign.from_bytes at h
  cases hp : SInt.is_power_of_two value with
  | false => rw [hp] at h; cases h
  | true => rw [hp] at h; cases h; exact ⟨rfl, rfl⟩

theorem constructed_alignment_is_positive (value result : Int)
    (h : SAlign.from_bytes value = some result) : 0 < result := by
  rcases alignment_constructor_preserves_value value result h with ⟨heq, hp⟩
  rw [heq]
  cases value with
  | negSucc n => cases hp
  | ofNat n =>
    cases n with
    | zero => cases hp
    | succ n => exact Int.natCast_pos.mpr (Nat.succ_pos n)

theorem zero_alignment_rejected : SAlign.from_bytes 0 = none := rfl
theorem unit_alignment_constructs : SAlign.from_bytes 1 = some 1 := rfl

theorem const_alignment_keeps_constructor_check (value : Int) :
    SAlign.from_bytes_const value = SAlign.from_bytes value := rfl

theorem successful_unwrap_is_exact {α : Type} (value : α) :
    SOption.unwrap (some value) = .ok value := rfl

theorem canonical_one_power (exponent : Nat) : SInt.pow 1 (Int.ofNat exponent) = .ok 1 := by
  change SOut.ok (Int.ofNat (Nat.pow 1 exponent)) = .ok 1
  have hpower : Nat.pow 1 exponent = 1 := Nat.one_pow exponent
  exact congrArg (fun value : Nat => SOut.ok (Int.ofNat value)) hpower

/-- Deliberately outside the actual Rust exponent conversion domain. This model
theorem cannot license that Rust call without its separate conversion duty. -/
theorem canonical_wide_power_is_defined : SInt.pow 1 4294967296 = .ok 1 :=
  canonical_one_power 4294967296

theorem wide_power_lacks_conversion_domain : ¬ PowDomain 4294967296 := by
  unfold PowDomain
  omega

theorem canonical_zero_right_shift (shift : Nat) : SInt.shr 0 (Int.ofNat shift) = .ok 0 := by
  change SOut.ok (Int.ofNat (0 / SNat.pow2 shift)) = .ok 0
  exact congrArg (fun value : Nat => SOut.ok (Int.ofNat value)) (Nat.zero_div _)

theorem canonical_wide_right_shift_is_defined :
    SInt.shr 0 340282366920938463463374607431768211456 = .ok 0 :=
  canonical_zero_right_shift 340282366920938463463374607431768211456

theorem wide_right_shift_lacks_conversion_domain :
    ¬ ShiftDomain 340282366920938463463374607431768211456 := by
  unfold ShiftDomain
  omega

def AllIntegersAreSizesGoal : Prop := ∀ value : Int, SSize.from_bytes value = some value

theorem all_integers_are_sizes_goal_false : ¬ AllIntegersAreSizesGoal := by
  intro h
  have wrong := h (-1)
  change (none : Option Int) = some (-1) at wrong
  cases wrong

def CanonicalWidePowerGoal : Prop := SInt.pow 1 4294967296 = .ok 1
def CanonicalWidePowerPanicsGoal : Prop := ∃ message, SInt.pow 1 4294967296 = .panic message

theorem canonical_wide_power_panics_goal_false : ¬ CanonicalWidePowerPanicsGoal := by
  intro ⟨message, h⟩
  rw [canonical_wide_power_is_defined] at h
  cases h

end TrustSem.LibraryWrappers

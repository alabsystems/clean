-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
-- A numeral waiting inside a nested β-redex is undone with the branch that
-- minted it, and a `have` whose annotation holds without computing on a
-- waiting numeral leaves it waiting.
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def sNestedRedex : Nat := (fun k => (fun j => Tag.tag (j - 7)) k + Tag.tag (k : Int)) 5
def sHaveSelf : Nat := let k := 5; have _h : k = k := rfl; Tag.tag (k - 7) + Tag.tag (k : Int)

theorem sNestedRedex_eq : sNestedRedex = 205 := rfl
theorem sHaveSelf_eq : sHaveSelf = 205 := rfl

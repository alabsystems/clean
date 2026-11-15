prelude
import ChkLIASpec
import ChkLIACases

/-! The negative control of `vf4_chk_lia.rs`'s Ax0 audit: a non-Ax0 axiom and a
"soundness" theorem resting on it. Kept out of `ChkLIA` so the deliverable module
declares no axiom. `planted_mut_u8_add_unsat` states that the problem of
`ChkLIA.mut_u8_add` (whose certificate the checker refuses) is unsatisfiable; it is
true, but its proof rests on `planted`, so its closure is outside Ax0. It imports
`ChkLIASpec` and `ChkLIACases` (which import `ChkLIA`) only so the test's one load
reaches the whole theory `theories/chk_lia`. -/

namespace ChkLIA

axiom planted : False

theorem planted_mut_u8_add_unsat :
    ¬ ∃ ρ : Nat → Int, ∀ c ∈ [(⟨[1, 0], 255⟩ : Cons), ⟨[0, 1], 255⟩, ⟨[-1, -2], -511⟩],
      c.sat ρ :=
  planted.elim

/-! The negative controls of `vf4_chk_lia.rs`'s check of `chk_LIA_cases_sound`'s
statement: each is a true theorem weaker than the pinned statement, within Ax0, so
only the shape check (and the kernel, at the pin's type) can tell it apart. -/

/-- Vacuous: every case is padded with the unsatisfiable `0 ≤ -1`, so it is proved
without the hypothesis. -/
theorem weak_cases_padded : ∀ (ps : List (List Cons × List Step)),
    chk_LIA_cases ps = true →
      ∀ p ∈ ps, ¬ ∃ ρ : Nat → Int, ∀ c ∈ ((⟨[], -1⟩ : Cons) :: p.1), c.sat ρ :=
  fun _ _ _ _ ⟨_, h⟩ =>
    absurd (h ⟨[], -1⟩ (List.Mem.head _)) (show ¬ (0 : Int) ≤ -1 by decide)

/-- Narrowed: only assignments into `Nat`. -/
theorem weak_cases_nat_rho : ∀ (ps : List (List Cons × List Step)),
    chk_LIA_cases ps = true →
      ∀ p ∈ ps, ¬ ∃ ρ : Nat → Nat, ∀ c ∈ p.1, c.sat (fun i => Int.ofNat (ρ i)) :=
  fun ps h p hp ⟨ρ, hall⟩ => chk_LIA_cases_sound ps h p hp ⟨fun i => Int.ofNat (ρ i), hall⟩

end ChkLIA

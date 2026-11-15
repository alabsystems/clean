/- Checked integer assignment rules composed with the existing Boolean WP.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRBooleanWPBranches
import SemRUnsignedSelect

namespace SemRBooleanWPComposition
open SemR SemRBooleanWP SemRUnsignedSelect

/-- Extend the existing dispatcher through the canonical integer step rules.
    The Boolean calculus is reused unchanged, including its refusals. -/
def scalarWPWithUInt (m : Module) (node : Node) (Q : Core → Prop) (k : Core) : Prop :=
  match node.inst, node.results with
  | .const (.int t) (.int pattern), [dst] => constUIntWP m dst t pattern Q k
  | .copy (.int t) src, [dst] => copyUIntWP m dst src t Q k
  | .select (.int t) cond yes no, [dst] => selectUIntWP m dst cond yes no t Q k
  | .icmp .eq (.int t) lhs rhs, [dst] => icmpEqUIntWP m dst lhs rhs t Q k
  | _, _ => scalarWP node Q k

theorem scalar_with_uint_wp_step (m : Module) (k : Core) (node : Node)
    (Q : Core → Prop) (hat : nth? k.block.body k.pc = some node)
    (h : scalarWPWithUInt m node Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  unfold scalarWPWithUInt at h
  split at h
  case h_1 _ _ t pattern dst hi hr =>
    have hn : node = constUInt dst t pattern := by cases node; simp_all [constUInt]
    subst node
    exact constUInt_wp_step m k dst t pattern Q hat h
  case h_2 _ _ t src dst hi hr =>
    have hn : node = copyUInt dst src t := by cases node; simp_all [copyUInt]
    subst node
    exact copyUInt_wp_step m k dst src t Q hat h
  case h_3 _ _ t cond yes no dst hi hr =>
    have hn : node = selectUInt dst cond yes no t := by cases node; simp_all [selectUInt]
    subst node
    exact selectUInt_wp_step m k dst cond yes no t Q hat h
  case h_4 _ _ t lhs rhs dst hi hr =>
    have hn : node = icmpEqUInt dst lhs rhs t := by cases node; simp_all [icmpEqUInt]
    subst node
    exact icmpEqUInt_wp_step m k dst lhs rhs t Q hat h
  case h_5 => exact scalar_wp_step m k node Q hat h

abbrev returnUIntWP := SemRUnsignedSelect.returnUIntWP

theorem returnUInt_wp_sound (m : Module) (k : Core) (src : Nat) (t : IntTy)
    (Q : List Val → Prop)
    (hat : nth? k.block.body k.pc = some (returnUInt src))
    (h : returnUIntWP m src t Q k) :
    ∃ vs, Step m k (.done (.ret vs)) ∧ Q vs :=
  SemRUnsignedSelect.returnUInt_wp_step m k src t Q hat h

end SemRBooleanWPComposition

/-
  Checked finite CFG witnesses over the existing SemR WP rules.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRUnsignedWP

namespace SemRNativeWPPlan
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches

/-- Original question data transported by the native consumer. The kernel
    does not decode or authenticate these identities; the consumer regenerates
    them from the complete original bundle and exact emitted typed claim. -/
structure QuestionIdentity where
  bundleDigest : List Nat
  moduleDigest : List Nat
  requestDigest : List Nat
  bodyDigest : List Nat
  requestId : Nat
  functionId : Nat
  obligations : List Nat
  contractBytes : List Nat
  questionBytes : List Nat

/-- An indexed theorem cannot be replayed under a different question identity.
    The index grants no source authority or engine proof grade. -/
structure BoundTranslation (identity : QuestionIdentity) (claim : Prop) : Prop where
  proof : claim

/-- A finite proof plan, not a program or an operational semantics. Each
    constructor must match the instruction at the actual SemR program counter.
    Branches use SemR's existing simultaneous block-parameter binding. -/
inductive Plan where
  | returns (src : Nat)
  | returnsUInt (src : Nat) (ty : IntTy)
  | scalar (node : Node) (rest : Plan)
  | jump (target : Nat) (args : List Nat) (rest : Plan)
  | branch (cond tt : Nat) (ta : List Nat) (et : Nat) (ea : List Nat)
      (yes no : Plan)

/-- The existing instruction WPs compose along the checked plan. Unsupported
    scalar instructions have False WP under scalarWP; no fallback can prove
    them. The exact caller-supplied postcondition remains the return leaf. -/
def wp (m : Module) (Q : List Val → Prop) : Plan → Core → Prop
  | .returns src, k =>
      nth? k.block.body k.pc = some (returnNode src) ∧ returnWP src Q k
  | .returnsUInt src ty, k =>
      nth? k.block.body k.pc = some (SemRUnsignedSelect.returnUInt src) ∧
        returnUIntWP m src ty Q k
  | .scalar node rest, k =>
      nth? k.block.body k.pc = some node ∧ scalarWPWithUInt m node (wp m Q rest) k
  | .jump target args rest, k =>
      nth? k.block.body k.pc = some (branchNode target args) ∧
        jumpWP m target args (wp m Q rest) k
  | .branch cond tt ta et ea yes no, k =>
      nth? k.block.body k.pc = some (conditionalNode cond tt ta et ea) ∧
        conditionalWP m cond tt ta (wp m Q yes) et ea (wp m Q no) k

/-- A checked plan proves a finite returned execution of the actual SemR
    module. Neither a summary, a solver verdict nor an assumed translation
    theorem enters the induction. -/
theorem wp_sound (m : Module) (Q : List Val → Prop) (plan : Plan) (k : Core)
    (h : wp m Q plan k) :
    ∃ fuel vs, Exec m fuel k (.ret vs) ∧ Q vs := by
  induction plan generalizing k with
  | returns src =>
      obtain ⟨vs, hs, hq⟩ := return_wp_sound m k src Q h.1 h.2
      exact ⟨1, vs, Exec.done 0 k (.ret vs) hs, hq⟩
  | returnsUInt src ty =>
      obtain ⟨vs, hs, hq⟩ := returnUInt_wp_sound m k src ty Q h.1 h.2
      exact ⟨1, vs, Exec.done 0 k (.ret vs) hs, hq⟩
  | scalar node rest ih =>
      obtain ⟨next, hs, _, _, hq⟩ := scalar_with_uint_wp_step m k node _ h.1 h.2
      obtain ⟨fuel, vs, he, hp⟩ := ih next hq
      exact ⟨fuel + 1, vs, Exec.step fuel k next (.ret vs) hs he, hp⟩
  | jump target args rest ih =>
      obtain ⟨next, hs, hq⟩ := branch_wp_sound m k target args _ h.1 h.2
      obtain ⟨fuel, vs, he, hp⟩ := ih next hq
      exact ⟨fuel + 1, vs, Exec.step fuel k next (.ret vs) hs he, hp⟩
  | branch cond tt ta et ea yes no ihYes ihNo =>
      obtain ⟨c, next, _, hs, hq⟩ :=
        conditional_wp_sound m k cond tt ta _ et ea _ h.1 h.2
      cases c with
      | false =>
          obtain ⟨fuel, vs, he, hp⟩ := ihNo next hq
          exact ⟨fuel + 1, vs, Exec.step fuel k next (.ret vs) hs he, hp⟩
      | true =>
          obtain ⟨fuel, vs, he, hp⟩ := ihYes next hq
          exact ⟨fuel + 1, vs, Exec.step fuel k next (.ret vs) hs he, hp⟩

theorem wp_run (m : Module) (Q : List Val → Prop) (plan : Plan) (k : Core)
    (h : wp m Q plan k) :
    ∃ fuel vs, run m fuel k = .ret vs ∧ Q vs := by
  obtain ⟨fuel, vs, he, hp⟩ := wp_sound m Q plan k h
  exact ⟨fuel, vs, run_complete m fuel k (.ret vs) he, hp⟩

theorem wp_excludes_violation (m : Module) (Q : List Val → Prop)
    (plan : Plan) (k : Core) (h : wp m Q plan k) : ¬ BodyViolation m k := by
  obtain ⟨fuel, vs, hr, _⟩ := wp_run m Q plan k h
  exact returned_excludes_body_violation m k fuel vs hr

end SemRNativeWPPlan

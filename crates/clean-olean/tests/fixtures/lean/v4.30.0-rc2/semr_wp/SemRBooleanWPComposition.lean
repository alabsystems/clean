/-
  Computed straight-line Boolean WPs over the existing SemR instructions.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanWP

namespace SemRBooleanWPComposition
open SemR SemRBooleanWP

/-- Compute the precondition for a supported scalar instruction. Other
    instruction or result shapes have no admitted precondition. -/
def scalarWP (node : Node) (Q : Core → Prop) (k : Core) : Prop :=
  match node.inst, node.results with
  | .const .bool (.bool b), [dst] => constWP dst b Q k
  | .copy .bool src, [dst] => copyWP dst src Q k
  | .select .bool cond yes no, [dst] => selectWP dst cond yes no Q k
  | _, _ => False

/-- A syntactic connection to the actual block and program counter. -/
def codeAt (body : List Node) (pc : Nat) : List Node → Prop
  | [] => True
  | node :: rest => nth? body pc = some node ∧ codeAt body (pc + 1) rest

/-- Backward substitution, ending at a Boolean return. The definition contains
    no execution relation or premise asserting soundness of a generated WP. -/
def straightLineWP (nodes : List Node) (src : Nat) (Q : List Val → Prop) : Core → Prop :=
  match nodes with
  | [] => returnWP src Q
  | node :: rest => scalarWP node (straightLineWP rest src Q)

theorem scalar_wp_step (m : Module) (k : Core) (node : Node) (Q : Core → Prop)
    (hat : nth? k.block.body k.pc = some node) (h : scalarWP node Q k) :
    ∃ k', Step m k (.cont k') ∧ k'.block = k.block ∧ k'.pc = k.pc + 1 ∧ Q k' := by
  unfold scalarWP at h
  split at h
  case h_1 _ _ b dst hi hr =>
    have hn : node = constNode dst b := by cases node; simp_all [constNode]
    subst node
    refine ⟨writeBool k dst b, ?_, rfl, rfl, h⟩
    have hs : stepCore m k = .cont (writeBool k dst b) := by
      simp [stepCore, hat, const_step]
    rw [← hs]
    exact step_complete m k
  case h_2 _ _ src dst hi hr =>
    have hn : node = copyNode dst src := by cases node; simp_all [copyNode]
    subst node
    obtain ⟨b, hb, hq⟩ := h
    refine ⟨writeBool k dst b, ?_, rfl, rfl, hq⟩
    have hs : stepCore m k = .cont (writeBool k dst b) := by
      simp [stepCore, hat, copy_step m k dst src b hb]
    rw [← hs]
    exact step_complete m k
  case h_3 _ _ cond yes no dst hi hr =>
    have hn : node = selectNode dst cond yes no := by
      cases node
      simp_all [selectNode]
    subst node
    obtain ⟨c, t, e, hc, ht, he, hq⟩ := h
    refine ⟨writeBool k dst (if c then t else e), ?_, rfl, rfl, hq⟩
    have hs : stepCore m k = .cont (writeBool k dst (if c then t else e)) := by
      simp [stepCore, hat, select_step m k dst cond yes no c t e hc ht he]
    rw [← hs]
    exact step_complete m k
  case h_4 => exact False.elim h

/-- A computed precondition suffices for any finite supported instruction
    sequence at the actual program counter, with exactly one fuel unit per
    scalar instruction and one for its Boolean return. -/
theorem straightLine_wp_sound (m : Module) (nodes : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core)
    (hat : codeAt k.block.body k.pc (nodes ++ [returnNode src]))
    (hwp : straightLineWP nodes src Q k) :
    ∃ vs, Exec m (nodes.length + 1) k (.ret vs) ∧ Q vs := by
  induction nodes generalizing k with
  | nil =>
    obtain ⟨vs, hs, hq⟩ := return_wp_sound m k src Q hat.1 hwp
    exact ⟨vs, Exec.done 0 k (.ret vs) hs, hq⟩
  | cons node rest ih =>
    obtain ⟨k', hs, hb, hp, hq⟩ := scalar_wp_step m k node _ hat.1 hwp
    have hrest : codeAt k'.block.body k'.pc (rest ++ [returnNode src]) := by
      simpa only [hb, hp] using hat.2
    obtain ⟨vs, hex, hpost⟩ := ih k' hrest hq
    exact ⟨vs, Exec.step (rest.length + 1) k k' (.ret vs) hs hex, hpost⟩

/-- The proof speaks about SemR's executable interpreter, not only its relation. -/
theorem straightLine_wp_run (m : Module) (nodes : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core)
    (hat : codeAt k.block.body k.pc (nodes ++ [returnNode src]))
    (hwp : straightLineWP nodes src Q k) :
    ∃ vs, run m (nodes.length + 1) k = .ret vs ∧ Q vs := by
  obtain ⟨vs, hex, hq⟩ := straightLine_wp_sound m nodes src Q k hat hwp
  exact ⟨vs, run_complete m _ k (.ret vs) hex, hq⟩

/-- A returned straight-line execution excludes bad reachability at every
    finite prefix according to the same SemR body semantics. -/
theorem straightLine_wp_excludes_violation (m : Module) (nodes : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core)
    (hat : codeAt k.block.body k.pc (nodes ++ [returnNode src]))
    (hwp : straightLineWP nodes src Q k) : ¬ BodyViolation m k := by
  obtain ⟨vs, hr, _⟩ := straightLine_wp_run m nodes src Q k hat hwp
  exact returned_excludes_body_violation m k (nodes.length + 1) vs hr

/-- The actual entry state of the existing serialized negation fixture. -/
def negateInitial (b : Bool) (depth : Nat) : Core :=
  { fn := negateModule.functions[0], sig := negateModule.funcTys[0],
    block := negateBlock, pc := 0, env := [(0, .bool b)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

/-- The existing real-body example now follows from the quantified computed
    WP theorem, rather than evaluating the whole execution in the proof. -/
theorem negate_correct_via_composition (b : Bool) (depth : Nat) :
    runFunction negateModule 0 [.bool b] 4 depth = .ret [.bool (!b)] := by
  have hat : codeAt (negateInitial b depth).block.body (negateInitial b depth).pc
      ([constNode 1 false, constNode 2 true, selectNode 3 0 1 2] ++ [returnNode 3]) := by
    simp [codeAt, negateInitial, negateBlock, nth?, returnNode]
  have hwp : straightLineWP [constNode 1 false, constNode 2 true, selectNode 3 0 1 2]
      3 (fun vs => vs = [.bool (!b)]) (negateInitial b depth) := by
    cases b <;> simp [straightLineWP, scalarWP, constNode, selectNode,
      constWP, selectWP, returnWP, negateInitial, negateModule,
      writeBool, next, lookupEnv]
  obtain ⟨vs, hr, hpost⟩ := straightLine_wp_run negateModule
    [constNode 1 false, constNode 2 true, selectNode 3 0 1 2] 3
    (fun vs => vs = [.bool (!b)]) (negateInitial b depth) hat hwp
  have hstart : start negateModule 0 [.bool b] depth = .ok (negateInitial b depth) := by
    cases b <;> rfl
  simpa only [runFunction, hstart, hpost] using hr

end SemRBooleanWPComposition

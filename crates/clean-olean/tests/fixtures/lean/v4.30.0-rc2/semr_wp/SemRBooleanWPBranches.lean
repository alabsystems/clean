/-
  Computed Boolean branch WPs over SemR's canonical argument transfer.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanWPComposition

namespace SemRBooleanWPBranches
open SemR SemRBooleanWP SemRBooleanWPComposition

/-- Read every initialized scalar from the predecessor environment before
    simultaneous parameter binding. The canonical binder still checks each
    target type, integer range and arity. Poison and other values refuse. -/
def argsWP (env : List (Nat × Val)) : List Nat → (List Val → Prop) → Prop
  | [], Q => Q []
  | src :: rest, Q =>
      match lookupEnv env src with
      | some (.bool value) => argsWP env rest (fun vs => Q (.bool value :: vs))
      | some (.int ty raw) => argsWP env rest (fun vs => Q (.int ty raw :: vs))
      | _ => False

theorem args_wp_sound (k : Core) (args : List Nat) (Q : List Val → Prop)
    (h : argsWP k.env args Q) : ∃ vs, getVs k args = .ok vs ∧ Q vs := by
  induction args generalizing Q with
  | nil => exact ⟨[], rfl, h⟩
  | cons src rest ih =>
    cases hv : lookupEnv k.env src with
    | none => simp [argsWP, hv] at h
    | some value =>
      cases value <;> simp only [argsWP, hv] at h
      case bool value =>
        obtain ⟨vs, hvs, hq⟩ := ih (fun vs => Q (.bool value :: vs)) h
        refine ⟨.bool value :: vs, ?_, hq⟩
        simp [getVs, getV, hv, hvs, ok_bind] <;> rfl
      case int ty raw =>
        obtain ⟨vs, hvs, hq⟩ := ih (fun vs => Q (.int ty raw :: vs)) h
        refine ⟨.int ty raw :: vs, ?_, hq⟩
        simp [getVs, getV, hv, hvs, ok_bind] <;> rfl

/-- The existing SemR binder computes the parameter type/arity checks and
    substitution. No second operational model or argument-binding algorithm
    is introduced. Its inputs have all been read from the original state. -/
def jumpWP (m : Module) (target : Nat) (args : List Nat) (Q : Core → Prop)
    (k : Core) : Prop :=
  match findBlock k.fn.blocks target with
  | none => False
  | some block => argsWP k.env args (fun vs =>
      match bindParams m.pointerBits k.env block.params vs with
      | .stop _ => False
      | .ok env => Q { k with block := block, pc := 0, env := env })

theorem jump_wp_sound (m : Module) (k : Core) (target : Nat) (args : List Nat)
    (Q : Core → Prop) (h : jumpWP m target args Q k) :
    ∃ vs k', getVs k args = .ok vs ∧
      jump m.pointerBits k target vs = .ok k' ∧ Q k' := by
  cases hb : findBlock k.fn.blocks target with
  | none => simp [jumpWP, hb] at h
  | some block =>
    simp only [jumpWP, hb] at h
    obtain ⟨vs, hv, hq⟩ := args_wp_sound k args _ h
    cases he : bindParams m.pointerBits k.env block.params vs with
    | stop out => simp [he] at hq
    | ok env =>
      refine ⟨vs, { k with block := block, pc := 0, env := env }, hv, ?_, ?_⟩
      · simp [jump, hb, he, ok_bind] <;> rfl
      · simpa only [he] using hq

def branchNode (target : Nat) (args : List Nat) : Node :=
  { inst := .br target args, results := [] }

def conditionalNode (cond tt : Nat) (ta : List Nat) (et : Nat) (ea : List Nat) : Node :=
  { inst := .condBr cond tt ta et ea, results := [] }

theorem branch_wp_sound (m : Module) (k : Core) (target : Nat) (args : List Nat)
    (Q : Core → Prop) (hat : nth? k.block.body k.pc = some (branchNode target args))
    (h : jumpWP m target args Q k) : ∃ k', Step m k (.cont k') ∧ Q k' := by
  obtain ⟨vs, k', hv, hj, hq⟩ := jump_wp_sound m k target args Q h
  exact at_pc m k _ Q hat ⟨k', branch_step m k k' target args vs hv hj, hq⟩

def conditionalWP (m : Module) (cond tt : Nat) (ta : List Nat) (Qt : Core → Prop)
    (et : Nat) (ea : List Nat) (Qe : Core → Prop) (k : Core) : Prop :=
  ∃ c, lookupEnv k.env cond = some (.bool c) ∧
    if c then jumpWP m tt ta Qt k else jumpWP m et ea Qe k

theorem conditional_wp_sound (m : Module) (k : Core) (cond tt : Nat) (ta : List Nat)
    (Qt : Core → Prop) (et : Nat) (ea : List Nat) (Qe : Core → Prop)
    (hat : nth? k.block.body k.pc = some (conditionalNode cond tt ta et ea))
    (h : conditionalWP m cond tt ta Qt et ea Qe k) :
    ∃ c k', lookupEnv k.env cond = some (.bool c) ∧ Step m k (.cont k') ∧
      (if c then Qt else Qe) k' := by
  obtain ⟨c, hc, hwp⟩ := h
  cases c with
  | false =>
    obtain ⟨vs, k', hv, hj, hq⟩ := jump_wp_sound m k et ea Qe hwp
    refine ⟨false, k', hc, ?_, hq⟩
    have he : stepCore m k = .cont k' := by
      simp [stepCore, hat, conditionalNode,
        conditional_step m k k' cond tt et ta ea false vs hc hv hj]
    rw [← he]
    exact step_complete m k
  | true =>
    obtain ⟨vs, k', hv, hj, hq⟩ := jump_wp_sound m k tt ta Qt hwp
    refine ⟨true, k', hc, ?_, hq⟩
    have he : stepCore m k = .cont k' := by
      simp [stepCore, hat, conditionalNode,
        conditional_step m k k' cond tt et ta ea true vs hc hv hj]
    rw [← he]
    exact step_complete m k

/-- Scalar substitution before a terminator, over actual SemR nodes. -/
def prefixWP : List Node → (Core → Prop) → Core → Prop
  | [], Q => Q
  | node :: rest, Q => scalarWP node (prefixWP rest Q)

def returnPathWP (nodes : List Node) (src : Nat) (Q : List Val → Prop) (k : Core) : Prop :=
  codeAt k.block.body k.pc (nodes ++ [returnNode src]) ∧ straightLineWP nodes src Q k

/-- One arm executes finite scalar instructions, transfers block arguments to
    the shared join, and executes a finite scalar/Boolean-return suffix. -/
def armWP (m : Module) (nodes : List Node) (join : Nat) (args : List Nat)
    (suffix : List Node) (src : Nat) (Q : List Val → Prop) (k : Core) : Prop :=
  codeAt k.block.body k.pc (nodes ++ [branchNode join args]) ∧
    prefixWP nodes (jumpWP m join args (returnPathWP suffix src Q)) k

theorem arm_wp_sound (m : Module) (nodes : List Node) (join : Nat) (args : List Nat)
    (suffix : List Node) (src : Nat) (Q : List Val → Prop) (k : Core)
    (h : armWP m nodes join args suffix src Q k) :
    ∃ vs, Exec m (nodes.length + suffix.length + 2) k (.ret vs) ∧ Q vs := by
  induction nodes generalizing k with
  | nil =>
    obtain ⟨hat, hwp⟩ := h
    obtain ⟨k', hs, hq⟩ := branch_wp_sound m k join args _ hat.1 hwp
    obtain ⟨vs, hex, hp⟩ := straightLine_wp_sound m suffix src Q k' hq.1 hq.2
    refine ⟨vs, ?_, hp⟩
    simpa [Nat.add_assoc] using Exec.step (suffix.length + 1) k k' (.ret vs) hs hex
  | cons node rest ih =>
    obtain ⟨hat, hwp⟩ := h
    obtain ⟨k', hs, hb, hp, hq⟩ := scalar_wp_step m k node _ hat.1 hwp
    have hc : codeAt k'.block.body k'.pc (rest ++ [branchNode join args]) := by
      simpa only [hb, hp] using hat.2
    obtain ⟨vs, hex, hpost⟩ := ih k' ⟨hc, hq⟩
    refine ⟨vs, ?_, hpost⟩
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Exec.step (rest.length + suffix.length + 2) k k' (.ret vs) hs hex

def diamondWP (m : Module) (cond tt : Nat) (ta : List Nat) (left : List Node)
    (et : Nat) (ea : List Nat) (right : List Node) (join : Nat)
    (leftArgs rightArgs : List Nat) (suffix : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core) : Prop :=
  nth? k.block.body k.pc = some (conditionalNode cond tt ta et ea) ∧
    conditionalWP m cond tt ta (armWP m left join leftArgs suffix src Q)
      et ea (armWP m right join rightArgs suffix src Q) k

/-- Unequal arm lengths are admitted: the actual Boolean condition selects
    both the branch and its exact fuel. The only semantic hypothesis is the
    computed WP; there is no assumed branch, transfer, or summary soundness. -/
theorem diamond_wp_sound (m : Module) (cond tt : Nat) (ta : List Nat) (left : List Node)
    (et : Nat) (ea : List Nat) (right : List Node) (join : Nat)
    (leftArgs rightArgs : List Nat) (suffix : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core)
    (h : diamondWP m cond tt ta left et ea right join leftArgs rightArgs suffix src Q k) :
    ∃ c vs, lookupEnv k.env cond = some (.bool c) ∧
      Exec m ((if c then left.length else right.length) + suffix.length + 3) k (.ret vs) ∧ Q vs := by
  obtain ⟨hat, hwp⟩ := h
  obtain ⟨c, k', hc, hs, hq⟩ := conditional_wp_sound m k cond tt ta _ et ea _ hat hwp
  cases c with
  | false =>
    obtain ⟨vs, hex, hp⟩ := arm_wp_sound m right join rightArgs suffix src Q k' hq
    refine ⟨false, vs, hc, ?_, hp⟩
    simpa [Nat.add_assoc] using
      Exec.step (right.length + suffix.length + 2) k k' (.ret vs) hs hex
  | true =>
    obtain ⟨vs, hex, hp⟩ := arm_wp_sound m left join leftArgs suffix src Q k' hq
    refine ⟨true, vs, hc, ?_, hp⟩
    simpa [Nat.add_assoc] using
      Exec.step (left.length + suffix.length + 2) k k' (.ret vs) hs hex

theorem diamond_wp_run (m : Module) (cond tt : Nat) (ta : List Nat) (left : List Node)
    (et : Nat) (ea : List Nat) (right : List Node) (join : Nat)
    (leftArgs rightArgs : List Nat) (suffix : List Node) (src : Nat)
    (Q : List Val → Prop) (k : Core)
    (h : diamondWP m cond tt ta left et ea right join leftArgs rightArgs suffix src Q k) :
    ∃ c vs, lookupEnv k.env cond = some (.bool c) ∧
      run m ((if c then left.length else right.length) + suffix.length + 3) k = .ret vs ∧ Q vs := by
  obtain ⟨c, vs, hc, he, hq⟩ :=
    diamond_wp_sound m cond tt ta left et ea right join leftArgs rightArgs suffix src Q k h
  exact ⟨c, vs, hc, run_complete m _ k (.ret vs) he, hq⟩

/-- Reusing destination IDs must not turn parallel argument transfer into
    sequential assignment: both reads are from the predecessor environment. -/
theorem swap_precondition (m : Module) (k : Core) (target : Nat) (body : List Node)
    (a b : Bool)
    (h0 : lookupEnv k.env 0 = some (.bool a))
    (h1 : lookupEnv k.env 1 = some (.bool b))
    (hb : findBlock k.fn.blocks target =
      some { id := target, params := [(0, .bool), (1, .bool)], body := body }) :
    jumpWP m target [1, 0]
      (fun k' => lookupEnv k'.env 0 = some (.bool b) ∧
        lookupEnv k'.env 1 = some (.bool a)) k := by
  simp [jumpWP, hb, argsWP, h0, h1, bindParams, expectTy, Val.ty, Ty.beq,
    ok_bind, lookupEnv]

theorem alias_precondition (m : Module) (k : Core) (target : Nat) (body : List Node)
    (a : Bool) (h0 : lookupEnv k.env 0 = some (.bool a))
    (hb : findBlock k.fn.blocks target =
      some { id := target, params := [(0, .bool), (1, .bool)], body := body }) :
    jumpWP m target [0, 0]
      (fun k' => lookupEnv k'.env 0 = some (.bool a) ∧
        lookupEnv k'.env 1 = some (.bool a)) k := by
  simp [jumpWP, hb, argsWP, h0, bindParams, expectTy, Val.ty, Ty.beq,
    ok_bind, lookupEnv]

/-- Explicit calculus witness, not a claim about the current Rust lowering.
    Both edges permute old IDs 1 and 2 into fresh SSA block parameters. -/
def chooseEntry : Block :=
  { id := 0, params := [(0, .bool), (1, .bool), (2, .bool)],
    body := [conditionalNode 0 1 [2, 1] 2 [2, 1]] }

def chooseLeft : Block :=
  { id := 1, params := [(3, .bool), (4, .bool)], body := [branchNode 3 [4]] }

def chooseRight : Block :=
  { id := 2, params := [(5, .bool), (6, .bool)], body := [branchNode 3 [5]] }

def chooseJoin : Block :=
  { id := 3, params := [(7, .bool)], body := [returnNode 7] }

def chooseSignature : FuncTy :=
  { params := [.bool, .bool, .bool], returns := [.bool], vararg := false }

def chooseFunction : Func :=
  { id := 0, ty := 0, entry := 0,
    blocks := [chooseEntry, chooseLeft, chooseRight, chooseJoin], name := [99,104,111,111,115,101] }

def chooseModule : Module :=
  { funcTys := [chooseSignature], enums := [], functions := [chooseFunction] }

def chooseInitial (c a b : Bool) (depth : Nat) : Core :=
  { fn := chooseFunction, sig := chooseSignature, block := chooseEntry, pc := 0,
    env := [(2, .bool b), (1, .bool a), (0, .bool c)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

theorem choose_precondition (c a b : Bool) (depth : Nat) :
    diamondWP chooseModule 0 1 [2, 1] [] 2 [2, 1] [] 3 [4] [5] [] 7
      (fun vs => vs = [.bool (if c then a else b)]) (chooseInitial c a b depth) := by
  cases c <;> simp [diamondWP, conditionalWP, jumpWP, argsWP, armWP,
    prefixWP, returnPathWP, straightLineWP, returnWP, codeAt,
    chooseInitial, chooseFunction, chooseSignature,
    chooseEntry, chooseLeft, chooseRight, chooseJoin, findBlock, nth?,
    conditionalNode, branchNode, returnNode, lookupEnv, bindParams,
    expectTy, Val.ty, Ty.beq, ok_bind]

theorem wrong_arity_excluded (c a b : Bool) (depth : Nat) :
    ¬ jumpWP chooseModule 1 [1] (fun _ => True) (chooseInitial c a b depth) := by
  simp [jumpWP, argsWP, chooseInitial, chooseFunction, chooseEntry,
    chooseLeft, findBlock, lookupEnv, bindParams, expectTy, Val.ty, Ty.beq, ok_bind, tyR]

theorem missing_operand_excluded (c a b : Bool) (depth : Nat) :
    ¬ jumpWP chooseModule 1 [999, 1] (fun _ => True) (chooseInitial c a b depth) := by
  simp [jumpWP, argsWP, chooseInitial, chooseFunction, chooseEntry,
    chooseLeft, findBlock, lookupEnv]

theorem wrong_parameter_type_excluded (m : Module) (k : Core) (target src dst : Nat)
    (body : List Node) (b : Bool)
    (hb : findBlock k.fn.blocks target =
      some { id := target, params := [(dst, .int .u8)], body := body })
    (hv : lookupEnv k.env src = some (.bool b)) :
    ¬ jumpWP m target [src] (fun _ => True) k := by
  simp [jumpWP, hb, argsWP, hv, bindParams, expectTy, Val.ty, Ty.beq, tyR]
  exact id

/-- The real SemR executable follows from the generic computed diamond WP. -/
theorem choose_correct (c a b : Bool) (depth : Nat) :
    runFunction chooseModule 0 [.bool c, .bool a, .bool b] 3 depth =
      .ret [.bool (if c then a else b)] := by
  obtain ⟨cond, vs, hc, hr, hpost⟩ := diamond_wp_run chooseModule
    0 1 [2, 1] [] 2 [2, 1] [] 3 [4] [5] [] 7
    (fun vs => vs = [.bool (if c then a else b)])
    (chooseInitial c a b depth) (choose_precondition c a b depth)
  have hcond : cond = c := by simpa [chooseInitial, lookupEnv] using hc.symm
  have hstart : start chooseModule 0 [.bool c, .bool a, .bool b] depth =
      .ok (chooseInitial c a b depth) := by cases c <;> cases a <;> cases b <;> rfl
  simpa [runFunction, hstart, hpost] using hr

def variantEntry (cond tt : Nat) (ta : List Nat) (et : Nat) (ea : List Nat) : Block :=
  { chooseEntry with body := [conditionalNode cond tt ta et ea] }

def variantFunction (cond tt : Nat) (ta : List Nat) (et : Nat) (ea : List Nat) : Func :=
  { chooseFunction with blocks :=
    [variantEntry cond tt ta et ea, chooseLeft, chooseRight, chooseJoin] }

def variantModule (cond tt : Nat) (ta : List Nat) (et : Nat) (ea : List Nat) : Module :=
  { chooseModule with functions := [variantFunction cond tt ta et ea] }

def aliasModule : Module := variantModule 0 1 [1, 1] 2 [2, 2]
def wrongBranchModule : Module := variantModule 0 2 [2, 1] 1 [2, 1]
def wrongConditionModule : Module := variantModule 1 1 [2, 1] 2 [2, 1]
def wrongArgumentModule : Module := variantModule 0 1 [2, 2] 2 [2, 1]

def aliasInitial (c a b : Bool) (depth : Nat) : Core :=
  { chooseInitial c a b depth with
    fn := variantFunction 0 1 [1, 1] 2 [2, 2],
    block := variantEntry 0 1 [1, 1] 2 [2, 2] }

theorem alias_precondition_computes (c a b : Bool) (depth : Nat) :
    diamondWP aliasModule 0 1 [1, 1] [] 2 [2, 2] [] 3 [4] [5] [] 7
      (fun vs => vs = [.bool (if c then a else b)]) (aliasInitial c a b depth) := by
  cases c <;> simp [diamondWP, conditionalWP, jumpWP, argsWP, armWP,
    prefixWP, returnPathWP, straightLineWP, returnWP, codeAt,
    aliasInitial, variantFunction, variantEntry, chooseInitial, chooseFunction,
    chooseSignature, chooseEntry, chooseLeft, chooseRight, chooseJoin, findBlock, nth?,
    conditionalNode, branchNode, returnNode, lookupEnv, bindParams,
    expectTy, Val.ty, Ty.beq, ok_bind]

theorem alias_correct (c a b : Bool) (depth : Nat) :
    runFunction aliasModule 0 [.bool c, .bool a, .bool b] 3 depth =
      .ret [.bool (if c then a else b)] := by
  obtain ⟨cond, vs, hc, hr, hpost⟩ := diamond_wp_run aliasModule
    0 1 [1, 1] [] 2 [2, 2] [] 3 [4] [5] [] 7
    (fun vs => vs = [.bool (if c then a else b)])
    (aliasInitial c a b depth) (alias_precondition_computes c a b depth)
  have hstart : start aliasModule 0 [.bool c, .bool a, .bool b] depth =
      .ok (aliasInitial c a b depth) := by cases c <;> cases a <;> cases b <;> rfl
  simpa [runFunction, hstart, hpost] using hr

/-- The original computed precondition is satisfiable at the same input used
    to refute every mutation; the negative controls are not vacuous. -/
theorem mutation_witness :
    diamondWP chooseModule 0 1 [2, 1] [] 2 [2, 1] [] 3 [4] [5] [] 7
      (fun vs => vs = [.bool false]) (chooseInitial true false true 0) ∧
    runFunction wrongBranchModule 0 [.bool true, .bool false, .bool true] 3 0 = .ret [.bool true] ∧
    runFunction wrongConditionModule 0 [.bool true, .bool false, .bool true] 3 0 = .ret [.bool true] ∧
    runFunction wrongArgumentModule 0 [.bool true, .bool false, .bool true] 3 0 = .ret [.bool true] := by
  exact ⟨choose_precondition true false true 0, rfl, rfl, rfl⟩

end SemRBooleanWPBranches

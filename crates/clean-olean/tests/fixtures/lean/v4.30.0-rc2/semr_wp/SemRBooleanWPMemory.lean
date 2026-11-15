/-
  Boolean local byte-memory WPs over the canonical SemR operations.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanWPBranches
import SemRMemory

namespace SemRBooleanWPMemory
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches

def allocaNode (dst : Nat) : Node := ⟨.alloca .bool none none, [dst]⟩
def storeNode (ptr value : Nat) : Node := ⟨.store .bool ptr value false none, []⟩
def loadNode (dst ptr : Nat) : Node := ⟨.load .bool ptr false none, [dst]⟩
def eqNode (dst lhs rhs : Nat) : Node := ⟨.icmp .eq .bool lhs rhs, [dst]⟩

def boolSlot (base : Nat) (data : List AByte) : Alloc :=
  { base := base, size := 1, align := 1, live := true, data := data }

/-- A live, in-bounds, aligned one-byte location. Initialization is a
    separate condition: a valid fresh allocation contains no initialized byte. -/
def ownsBool (mem : Mem) (a base : Nat) (data : List AByte) : Prop :=
  nth? mem.allocs a = some (boolSlot base data) ∧ base < addrSpace

def allocatedBool (k : Core) (dst : Nat) : Core :=
  { next k with
    env := (dst, .ptr k.mem.allocs.length 0) :: k.env
    mem := { allocs := k.mem.allocs ++ [boolSlot k.mem.nextAddr []],
             nextAddr := k.mem.nextAddr + 1 } }

def storedBool (k : Core) (a base : Nat) (data : List AByte) (b : Bool) : Core :=
  { next k with mem := written k.mem a 0 (boolSlot base data) [.init (b2n b)] }

def allocaWP (bits dst : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  k.mem.Below ∧ k.mem.nextAddr + 1 < addrSpace ∧
    k.mem.nextAddr + 1 ≤ 2 ^ bits ∧ Q (allocatedBool k dst)

def storeWP (ptr value : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  ∃ a base data b, lookupEnv k.env ptr = some (.ptr a 0) ∧
    lookupEnv k.env value = some (.bool b) ∧ ownsBool k.mem a base data ∧
    Q (storedBool k a base data b)

def loadWP (dst ptr : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  ∃ a base data b, lookupEnv k.env ptr = some (.ptr a 0) ∧
    ownsBool k.mem a base data ∧ readBytes data 0 1 = [.init (b2n b)] ∧
    Q (writeBool k dst b)

def eqWP (dst lhs rhs : Nat) (Q : Core → Prop) (k : Core) : Prop :=
  ∃ a b, lookupEnv k.env lhs = some (.bool a) ∧
    lookupEnv k.env rhs = some (.bool b) ∧ Q (writeBool k dst (a == b))

theorem bool_slot_access (mem : Mem) (a base : Nat) (data : List AByte)
    (h : ownsBool mem a base data) (op : String) :
    accessAt mem op a 0 1 1 = .ok (boolSlot base data) := by
  apply accessAt_ok mem op a 0 1 1 (boolSlot base data) h.1 rfl
  · simpa [boolSlot] using h.2
  · simp [boolSlot, Nat.mod_one]
  · decide
  · simp [boolSlot]

theorem alloca_step (m : Module) (k : Core) (dst : Nat)
    (hfit : k.mem.nextAddr + 1 < addrSpace)
    (htarget : k.mem.nextAddr + 1 ≤ 2 ^ m.pointerBits) :
    execNode m k (allocaNode dst) = .cont (allocatedBool k dst) := by
  have hfirst : ¬ addrSpace ≤ k.mem.nextAddr := by omega
  have hsecond : ¬ addrSpace ≤ k.mem.nextAddr + 1 := by omega
  have hthird : ¬ 2 ^ m.pointerBits < k.mem.nextAddr + 1 := by omega
  have hsize : ¬ addrSpace ≤ 1 := by decide
  simp [execNode, allocaNode, allocaStep, getCount, layoutOf, scalarLayout,
    allocSize, checkAlign, isPow2, allocAt, alignUp, hfirst, hsecond, hthird,
    hsize, Nat.mod_one, ofR, bindResults, allocatedBool, boolSlot, next, ok_bind]

/-- Allocation appends a new allocation id; old ids remain unchanged. The
    Below premise additionally establishes address separation, not just ids. -/
theorem allocated_owns_fresh (k : Core) (dst : Nat)
    (h : k.mem.nextAddr + 1 < addrSpace) :
    ownsBool (allocatedBool k dst).mem k.mem.allocs.length k.mem.nextAddr [] := by
  constructor
  · simp [allocatedBool, nth?_append_one]
  · omega

theorem allocated_preserves_old (k : Core) (dst a : Nat) (h : a < k.mem.allocs.length) :
    nth? (allocatedBool k dst).mem.allocs a = nth? k.mem.allocs a := by
  simp [allocatedBool, nth?_append_one, h]

theorem allocated_address_fresh (k : Core) (dst : Nat) (hb : k.mem.Below) :
    ∀ a al, nth? k.mem.allocs a = some al →
      al.base + max al.size 1 ≤ (allocatedBool k dst).mem.nextAddr - 1 := by
  intro a al ha
  simpa [allocatedBool] using hb a al ha

theorem store_step (m : Module) (k : Core) (ptr value a base : Nat)
    (data : List AByte) (b : Bool)
    (hp : lookupEnv k.env ptr = some (.ptr a 0))
    (hv : lookupEnv k.env value = some (.bool b))
    (ho : ownsBool k.mem a base data) :
    execNode m k (storeNode ptr value) = .cont (storedBool k a base data b) := by
  have ha := bool_slot_access k.mem a base data ho "Store"
  simp [execNode, storeNode, storeStep, getV, hp, hv, scalarLayout,
    storeImage, expectTy, Val.ty, Ty.beq, encodeVal, checkAlign, isPow2, expectPtr,
    rejectPoison, ha, ofR, bindResults, storedBool, next, ok_bind, pure]

/-- The same allocated cell becomes initialized with the byte just stored. -/
theorem stored_owns (k : Core) (a base : Nat) (data : List AByte) (b : Bool)
    (h : ownsBool k.mem a base data) :
    ownsBool (storedBool k a base data b).mem a base
      (writeBytes data 0 [.init (b2n b)]) := by
  constructor
  · have hlt := nth?_lt k.mem.allocs a (boolSlot base data) h.1
    simp [storedBool, written, nth?_setNth, hlt, boolSlot]
  · exact h.2

theorem stored_initialized (data : List AByte) (b : Bool) :
    readBytes (writeBytes data 0 [.init (b2n b)]) 0 1 = [.init (b2n b)] :=
  readBytes_writeBytes data 0 [.init (b2n b)]

/-- Disjoint allocation ids retain their bytes. If two operands alias the
    stored allocation, this lemma deliberately does not apply. -/
theorem stored_preserves_other (k : Core) (a base other : Nat)
    (data : List AByte) (b : Bool) (hne : other ≠ a) :
    nth? (storedBool k a base data b).mem.allocs other = nth? k.mem.allocs other := by
  simp [storedBool, written, nth?_setNth, hne]

theorem load_step (m : Module) (k : Core) (dst ptr a base : Nat)
    (data : List AByte) (b : Bool)
    (hp : lookupEnv k.env ptr = some (.ptr a 0))
    (ho : ownsBool k.mem a base data)
    (hi : readBytes data 0 1 = [.init (b2n b)]) :
    execNode m k (loadNode dst ptr) = .cont (writeBool k dst b) := by
  have ha := bool_slot_access k.mem a base data ho "Load"
  cases b <;>
    simp [execNode, loadNode, loadStep, getV, hp, scalarLayout, checkAlign,
      isPow2, expectPtr, rejectPoison, ha, boolSlot, hi, readOut, firstUninit, b2n, decodeVal, ofR,
      bindResults, writeBool, next, ok_bind, pure]

theorem load_after_store (m : Module) (k : Core) (dst ptr a base : Nat)
    (data : List AByte) (b : Bool)
    (hp : lookupEnv k.env ptr = some (.ptr a 0))
    (ho : ownsBool k.mem a base data) :
    execNode m (storedBool k a base data b) (loadNode dst ptr) =
      .cont (writeBool (storedBool k a base data b) dst b) := by
  apply load_step m (storedBool k a base data b) dst ptr a base
    (writeBytes data 0 [.init (b2n b)]) b
  · exact hp
  · exact stored_owns k a base data b ho
  · exact stored_initialized data b

/-- Fresh storage is not initialized Boolean storage. A plain SemR load
    propagates these bytes as poison; this WP never treats them as a Bool. -/
theorem fresh_not_initialized (b : Bool) :
    readBytes [] 0 1 ≠ [.init (b2n b)] := by
  simp [readBytes, byteAt, nth?]

theorem eq_step (m : Module) (k : Core) (dst lhs rhs : Nat) (a b : Bool)
    (ha : lookupEnv k.env lhs = some (.bool a))
    (hb : lookupEnv k.env rhs = some (.bool b)) :
    execNode m k (eqNode dst lhs rhs) = .cont (writeBool k dst (a == b)) := by
  cases a <;> cases b <;>
    simp [execNode, eqNode, icmpStep, getV, ha, hb, rejectPoison, evalIcmp, icmpR,
      isBoolTy, expectBool, b2n, expectTy, Val.ty, Ty.beq, ofR, bindResults, writeBool, next, ok_bind, pure]

/-- A Boolean instruction WP includes its operand, allocation, initialization,
    and exact result-shape checks. Branches use the existing transfer calculus. -/
def instructionWP (m : Module) (node : Node) (Q : Core → Prop) (k : Core) : Prop :=
  match node.inst, node.results with
  | .alloca .bool none none, [dst] => allocaWP m.pointerBits dst Q k
  | .store .bool ptr value false none, [] => storeWP ptr value Q k
  | .load .bool ptr false none, [dst] => loadWP dst ptr Q k
  | .icmp .eq .bool lhs rhs, [dst] => eqWP dst lhs rhs Q k
  | .br target args, [] => jumpWP m target args Q k
  | .condBr cond tt ta et ea, [] => conditionalWP m cond tt ta Q et ea Q k
  | _, _ => scalarWP node Q k

theorem instruction_wp_sound (m : Module) (node : Node) (Q : Core → Prop) (k : Core)
    (hat : nth? k.block.body k.pc = some node) (h : instructionWP m node Q k) :
    ∃ k', Step m k (.cont k') ∧ Q k' := by
  unfold instructionWP at h
  split at h
  · rename_i dst hi hr
    have hn : node = allocaNode dst := by cases node; simp_all [allocaNode]
    subst node
    exact at_pc m k _ Q hat ⟨allocatedBool k dst, alloca_step m k dst h.2.1 h.2.2.1, h.2.2.2⟩
  · rename_i ptr value hi hr
    have hn : node = storeNode ptr value := by cases node; simp_all [storeNode]
    subst node
    obtain ⟨a, base, data, b, hp, hv, ho, hq⟩ := h
    exact at_pc m k _ Q hat ⟨storedBool k a base data b, store_step m k ptr value a base data b hp hv ho, hq⟩
  · rename_i ptr dst hi hr
    have hn : node = loadNode dst ptr := by cases node; simp_all [loadNode]
    subst node
    obtain ⟨a, base, data, b, hp, ho, hi, hq⟩ := h
    exact at_pc m k _ Q hat ⟨writeBool k dst b, load_step m k dst ptr a base data b hp ho hi, hq⟩
  · rename_i lhs rhs dst hi hr
    have hn : node = eqNode dst lhs rhs := by cases node; simp_all [eqNode]
    subst node
    obtain ⟨a, b, ha, hb, hq⟩ := h
    exact at_pc m k _ Q hat ⟨writeBool k dst (a == b), eq_step m k dst lhs rhs a b ha hb, hq⟩
  · rename_i target args hi hr
    have hn : node = branchNode target args := by cases node; simp_all [branchNode]
    subst node
    exact branch_wp_sound m k target args Q hat h
  · rename_i cond tt ta et ea hi hr
    have hn : node = conditionalNode cond tt ta et ea := by cases node; simp_all [conditionalNode]
    subst node
    obtain ⟨c, k', _, hs, hq⟩ := conditional_wp_sound m k cond tt ta Q et ea Q hat h
    exact ⟨k', hs, by cases c <;> exact hq⟩
  · obtain ⟨k', hs, _, _, hq⟩ := scalar_wp_step m k node Q hat h
    exact ⟨k', hs, hq⟩

/-- A finite instruction path through actual blocks, ending at Return. Each
    instruction must be at the actual current PC; jumps are never flattened
    into a second operational model. The precondition is computed backwards. -/
def pathWP (m : Module) : List Node → (List Val → Prop) → Core → Prop
  | [], _, _ => False
  | [node], Q, k => match node.inst, node.results with
      | .ret [src], [] => nth? k.block.body k.pc = some node ∧ returnWP src Q k
      | _, _ => False
  | node :: nextNode :: rest, Q, k =>
      nth? k.block.body k.pc = some node ∧ instructionWP m node (pathWP m (nextNode :: rest) Q) k

theorem path_wp_sound (m : Module) (nodes : List Node) (Q : List Val → Prop) (k : Core)
    (h : pathWP m nodes Q k) : ∃ vs, Exec m nodes.length k (.ret vs) ∧ Q vs := by
  induction nodes generalizing k with
  | nil => exact False.elim h
  | cons node rest ih =>
    cases rest with
    | nil =>
      unfold pathWP at h
      split at h
      · rename_i src hi hr
        have hn : node = returnNode src := by cases node; simp_all [returnNode]
        subst node
        obtain ⟨vs, hs, hq⟩ := return_wp_sound m k src Q h.1 h.2
        exact ⟨vs, Exec.done 0 k (.ret vs) hs, hq⟩
      · exact False.elim h
    | cons nextNode tail =>
      obtain ⟨k', hs, hq⟩ := instruction_wp_sound m node _ k h.1 h.2
      obtain ⟨vs, he, hp⟩ := ih k' hq
      exact ⟨vs, Exec.step (nextNode :: tail).length k k' (.ret vs) hs he, hp⟩

/-- The instruction and block shape of the unchanged compiler export. The
    artifact test binds its serialized bytes and exact target to this value. -/
def chooseBlocks : List Block :=
  [{ id := 0, params := [(0, .bool), (1, .bool), (2, .bool)], body :=
      [allocaNode 4, constNode 5 false, eqNode 6 0 5, conditionalNode 6 2 [] 1 []] },
   { id := 1, params := [], body := [copyNode 7 1, storeNode 4 7, branchNode 3 []] },
   { id := 2, params := [], body := [copyNode 8 2, storeNode 4 8, branchNode 3 []] },
   { id := 3, params := [], body := [loadNode 9 4, returnNode 9] }]

def chooseModule (target : Option TargetInfo) : Module :=
  { funcTys := [{ params := [.bool, .bool, .bool], returns := [.bool], vararg := false }],
    enums := [], functions :=
      [{ id := 0, ty := 0, entry := 0, blocks := chooseBlocks, name := [99,104,111,111,115,101] }],
    target := target }

def chooseInitial (target : Option TargetInfo) (c a b : Bool) (depth : Nat) : Core :=
  { fn := (chooseModule target).functions[0]'(by simp [chooseModule]),
    sig := (chooseModule target).funcTys[0]'(by simp [chooseModule]),
    block := chooseBlocks[0], pc := 0, env := [(2, .bool b), (1, .bool a), (0, .bool c)],
    depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

def choosePath (c : Bool) : List Node :=
  [allocaNode 4, constNode 5 false, eqNode 6 0 5, conditionalNode 6 2 [] 1 []] ++
  (if c then [copyNode 7 1, storeNode 4 7] else [copyNode 8 2, storeNode 4 8]) ++
  [branchNode 3 [], loadNode 9 4, returnNode 9]

theorem choose_path_wp (target : Option TargetInfo)
    (hb : (chooseModule target).pointerBits = 64) (c a b : Bool) (depth : Nat) :
    pathWP (chooseModule target) (choosePath c)
      (fun vs => vs = [.bool (if c then a else b)]) (chooseInitial target c a b depth) := by
  simp only [chooseModule, Module.pointerBits] at hb
  cases c <;> cases a <;> cases b <;>
    simp [choosePath, pathWP, instructionWP, chooseInitial, chooseModule, chooseBlocks,
      allocaNode, storeNode, loadNode, eqNode, constNode, copyNode, returnNode, branchNode,
      conditionalNode, allocaWP, storeWP, loadWP, eqWP, constWP, copyWP, scalarWP,
      conditionalWP, jumpWP, argsWP, returnWP, allocatedBool, storedBool,
      writeBool, ownsBool, boolSlot, written, writeBytes, setByte, setNth,
      readBytes, byteAt, lookupEnv, next, findBlock, bindParams, nth?,
      Mem.Below, Mem.empty, below_empty, Module.pointerBits, hb, addrSpace, b2n] <;>
    first
    | (refine ⟨1024, [], by decide, 1024, [.init 0], ?_⟩; solve | simp [setByte, nth?])
    | (refine ⟨1024, [], by decide, 1024, [.init 1], ?_⟩; simp [setByte, nth?])

/-- The generic path theorem, rather than evaluation of the whole run,
    discharges the exact nine-instruction compiler path for every input. -/
theorem choose_correct (target : Option TargetInfo)
    (hb : (chooseModule target).pointerBits = 64)
    (ht : (chooseModule target).executableTarget = true)
    (c a b : Bool) (depth : Nat) :
    runFunction (chooseModule target) 0 [.bool c, .bool a, .bool b] 9 depth =
      .ret [.bool (if c then a else b)] := by
  obtain ⟨vs, he, hp⟩ := path_wp_sound (chooseModule target) (choosePath c)
    (fun vs => vs = [.bool (if c then a else b)]) (chooseInitial target c a b depth)
    (choose_path_wp target hb c a b depth)
  have hn : (choosePath c).length = 9 := by cases c <;> rfl
  have hs : start (chooseModule target) 0 [.bool c, .bool a, .bool b] depth =
      .ok (chooseInitial target c a b depth) := by
    simp [chooseModule, Module.executableTarget] at ht
    cases c <;> cases a <;> cases b <;>
      simp [start, chooseModule, chooseBlocks, chooseInitial, ht, bindParams,
        nth?, findBlock, expectTy, rejectPoison, Val.ty, Ty.beq, Module.executableTarget, checkSig, ok_bind, pure]
  rw [hn] at he
  have hr := run_complete (chooseModule target) 9 _ _ he
  simpa only [runFunction, hs, hp] using hr

end SemRBooleanWPMemory

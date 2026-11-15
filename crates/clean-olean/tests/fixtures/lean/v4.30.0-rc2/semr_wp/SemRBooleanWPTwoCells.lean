/- Two fresh Boolean cells, framed through the canonical SemR byte memory. -/
import SemRBooleanWPMemory
import SemRNativeWP

namespace SemRBooleanWPTwoCells
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches
open SemRBooleanWPMemory

theorem allocated_below (k : Core) (dst : Nat) (h : k.mem.Below) :
    (allocatedBool k dst).mem.Below := by
  simpa [allocatedBool, boolSlot, alignUp, Nat.mod_one] using
    (alloc_fresh k.mem h 1 1 (by decide)).2.2

theorem allocated_preserves_owns (k : Core) (dst a base : Nat) (data : List AByte)
    (h : ownsBool k.mem a base data) :
    ownsBool (allocatedBool k dst).mem a base data := by
  refine ⟨?_, h.2⟩
  rw [allocated_preserves_old k dst a (nth?_lt _ _ _ h.1)]
  exact h.1

/-- Two successive fresh allocations have distinct ids, adjacent disjoint
    one-byte address ranges, and preserve every existing Boolean cell. -/
theorem two_allocations_separate (k : Core) (first second : Nat)
    (hb : k.mem.Below) (hfit : k.mem.nextAddr + 2 < addrSpace) :
    let k₁ := allocatedBool k first
    let k₂ := allocatedBool k₁ second
    ownsBool k₂.mem k.mem.allocs.length k.mem.nextAddr [] ∧
    ownsBool k₂.mem (k.mem.allocs.length + 1) (k.mem.nextAddr + 1) [] ∧
    k.mem.allocs.length ≠ k.mem.allocs.length + 1 ∧ k₂.mem.Below ∧
    (∀ a base data, ownsBool k.mem a base data → ownsBool k₂.mem a base data) := by
  dsimp only
  refine ⟨?_, ?_, by omega, allocated_below _ second (allocated_below k first hb), ?_⟩
  · exact allocated_preserves_owns _ second _ _ _
      (allocated_owns_fresh k first (by omega))
  · simpa [allocatedBool] using allocated_owns_fresh (allocatedBool k first) second (by
      simp only [allocatedBool]; omega)
  · intro a base data h
    exact allocated_preserves_owns _ second _ _ _ (allocated_preserves_owns k first _ _ _ h)

theorem stored_preserves_owns (k : Core) (a base other otherBase : Nat)
    (data otherData : List AByte) (b : Bool) (hne : other ≠ a)
    (h : ownsBool k.mem other otherBase otherData) :
    ownsBool (storedBool k a base data b).mem other otherBase otherData := by
  exact ⟨(stored_preserves_other k a base other data b hne).trans h.1, h.2⟩

/-- Both stores initialize only their own allocation; the first initialized
    value survives the second store. All ids and initial bytes are quantified. -/
theorem two_stores_frame (k : Core) (a base other otherBase : Nat)
    (data otherData : List AByte) (v w : Bool) (hne : a ≠ other)
    (ha : ownsBool k.mem a base data) (hb : ownsBool k.mem other otherBase otherData) :
    let first := storedBool k a base data v
    let second := storedBool first other otherBase otherData w
    ownsBool second.mem a base (writeBytes data 0 [.init (b2n v)]) ∧
    ownsBool second.mem other otherBase (writeBytes otherData 0 [.init (b2n w)]) := by
  dsimp only
  have hfirst := stored_owns k a base data v ha
  have hother := stored_preserves_owns k a base other otherBase data otherData v (Ne.symm hne) hb
  exact ⟨stored_preserves_owns _ other otherBase a base otherData _ w hne hfirst,
    stored_owns _ other otherBase otherData w hother⟩

/-- A write to the other cell preserves both ownership and the initialized
    byte read from this cell. Aliasing is explicitly excluded. -/
theorem load_after_disjoint_store (m : Module) (k : Core)
    (dst ptr a base other otherBase : Nat) (data otherData : List AByte) (b v : Bool)
    (hne : a ≠ other) (hp : lookupEnv k.env ptr = some (.ptr a 0))
    (ho : ownsBool k.mem a base data) (hi : readBytes data 0 1 = [.init (b2n b)]) :
    execNode m (storedBool k other otherBase otherData v) (loadNode dst ptr) =
      .cont (writeBool (storedBool k other otherBase otherData v) dst b) := by
  apply load_step m (storedBool k other otherBase otherData v) dst ptr a base data b hp
    (stored_preserves_owns k other otherBase a base otherData data v hne ho) hi

/-- This is the exact two-cell mutation used by native WP's regression:
    insert a fresh cell, then store and read false in it at the join. -/
def blocks : List Block :=
  [{ id := 0, params := [(0, .bool), (1, .bool), (2, .bool)], body :=
      [allocaNode 4, allocaNode 16, constNode 5 false, eqNode 6 0 5,
       conditionalNode 6 2 [] 1 []] },
   { id := 1, params := [], body := [copyNode 7 1, storeNode 4 7, branchNode 3 []] },
   { id := 2, params := [], body := [copyNode 8 2, storeNode 4 8, branchNode 3 []] },
   { id := 3, params := [], body :=
      [storeNode 16 5, loadNode 17 16, loadNode 9 4, returnNode 9] }]

def module (target : Option TargetInfo) : Module :=
  { funcTys := [{ params := [.bool, .bool, .bool], returns := [.bool], vararg := false }],
    enums := [], functions :=
      [{ id := 0, ty := 0, entry := 0, blocks := blocks, name := [99,104,111,111,115,101] }],
    target := target }

def initial (target : Option TargetInfo) (c a b : Bool) (depth : Nat) (mem : Mem) : Core :=
  { fn := (module target).functions[0]'(by simp [module]),
    sig := (module target).funcTys[0]'(by simp [module]),
    block := blocks[0], pc := 0, env := [(2, .bool b), (1, .bool a), (0, .bool c)],
    depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := mem }

def path (c : Bool) : List Node :=
  [allocaNode 4, allocaNode 16, constNode 5 false, eqNode 6 0 5, conditionalNode 6 2 [] 1 []] ++
  (if c then [copyNode 7 1, storeNode 4 7] else [copyNode 8 2, storeNode 4 8]) ++
  [branchNode 3 [], storeNode 16 5, loadNode 17 16, loadNode 9 4, returnNode 9]

theorem path_wp (target : Option TargetInfo) (hb : (module target).pointerBits = 64)
    (c a b : Bool) (depth : Nat) (mem : Mem) (hm : mem.Below)
    (hfit : mem.nextAddr + 2 < addrSpace) :
    pathWP (module target) (path c) (fun vs => vs = [.bool (if c then a else b)])
      (initial target c a b depth mem) := by
  have hfit₁ : mem.nextAddr + 1 < addrSpace := by omega
  have hbelow := allocated_below (initial target c a b depth mem) 4 hm
  let k₂ := allocatedBool (allocatedBool (initial target c a b depth mem) 4) 16
  have hs := two_allocations_separate (initial target c a b depth mem) 4 16 hm hfit
  have hfirst : ownsBool k₂.mem mem.allocs.length mem.nextAddr [] := hs.1
  have hsecond : ownsBool k₂.mem (mem.allocs.length + 1) (mem.nextAddr + 1) [] := hs.2.1
  have hother (v : Bool) := stored_preserves_owns k₂ mem.allocs.length mem.nextAddr
    (mem.allocs.length + 1) (mem.nextAddr + 1) [] [] v (by omega) hsecond
  have hframe (v : Bool) := two_stores_frame k₂ mem.allocs.length mem.nextAddr
    (mem.allocs.length + 1) (mem.nextAddr + 1) [] [] v false (by omega) hfirst hsecond
  simp only [module, Module.pointerBits] at hb
  cases c <;>
    simp [path, pathWP, instructionWP, initial, module, blocks,
      allocaNode, storeNode, loadNode, eqNode, constNode, copyNode, returnNode, branchNode,
      conditionalNode, allocaWP, storeWP, loadWP, eqWP, constWP, copyWP, scalarWP,
      conditionalWP, jumpWP, argsWP, returnWP, allocatedBool, storedBool,
      writeBool, boolSlot, lookupEnv, next, findBlock, bindParams, nth?,
      hm, Module.pointerBits, hb, addrSpace, b2n]
  case false =>
    refine ⟨by simpa [addrSpace] using hfit₁, by simp [addrSpace] at hfit; omega,
      by simpa [allocatedBool, initial, boolSlot] using hbelow,
      by simp [addrSpace] at hfit; omega, by simp [addrSpace] at hfit; omega,
      mem.nextAddr, [], ?_, mem.nextAddr + 1, [], ?_,
      mem.nextAddr + 1, writeBytes [] 0 [.init 0], ?_, ?_,
      mem.nextAddr, writeBytes [] 0 [.init (b2n b)], ?_, ?_⟩
    all_goals first
      | simpa [List.append_assoc, k₂, allocatedBool, initial, boolSlot] using hfirst
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using hother a
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using hother b
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe a).2
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe b).2
      | exact Or.inl (stored_initialized [] false)
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe a).1
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe b).1
      | exact stored_initialized [] a
      | exact stored_initialized [] b
  case true =>
    refine ⟨by simpa [addrSpace] using hfit₁, by simp [addrSpace] at hfit; omega,
      by simpa [allocatedBool, initial, boolSlot] using hbelow,
      by simp [addrSpace] at hfit; omega, by simp [addrSpace] at hfit; omega,
      mem.nextAddr, [], ?_, mem.nextAddr + 1, [], ?_,
      mem.nextAddr + 1, writeBytes [] 0 [.init 0], ?_, ?_,
      mem.nextAddr, writeBytes [] 0 [.init (b2n a)], ?_, ?_⟩
    all_goals first
      | simpa [List.append_assoc, k₂, allocatedBool, initial, boolSlot] using hfirst
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using hother a
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using hother b
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe a).2
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe b).2
      | exact Or.inl (stored_initialized [] false)
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe a).1
      | simpa [List.append_assoc, k₂, allocatedBool, initial, storedBool, boolSlot, b2n] using (hframe b).1
      | exact stored_initialized [] a
      | exact stored_initialized [] b

/-- Execution is quantified over any initial byte memory satisfying the
    allocator invariant and space bound, not just the empty sample heap. -/
theorem run_correct (target : Option TargetInfo) (hb : (module target).pointerBits = 64)
    (c a b : Bool) (depth : Nat) (mem : Mem) (hm : mem.Below)
    (hfit : mem.nextAddr + 2 < addrSpace) :
    run (module target) 12 (initial target c a b depth mem) =
      .ret [.bool (if c then a else b)] := by
  obtain ⟨vs, he, hp⟩ := path_wp_sound (module target) (path c)
    (fun vs => vs = [.bool (if c then a else b)]) (initial target c a b depth mem)
    (path_wp target hb c a b depth mem hm hfit)
  have hn : (path c).length = 12 := by cases c <;> rfl
  rw [hn] at he
  simpa only [hp] using run_complete (module target) 12 _ _ he

theorem function_correct (target : Option TargetInfo) (hb : (module target).pointerBits = 64)
    (ht : (module target).executableTarget = true) (c a b : Bool) (depth : Nat) :
    runFunction (module target) 0 [.bool c, .bool a, .bool b] 12 depth =
      .ret [.bool (if c then a else b)] := by
  have hs : start (module target) 0 [.bool c, .bool a, .bool b] depth =
      .ok (initial target c a b depth Mem.empty) := by
    simp [module, Module.executableTarget] at ht
    simp [start, module, blocks, initial, ht, bindParams, nth?, findBlock,
      expectTy, rejectPoison, Val.ty, Ty.beq, Module.executableTarget, checkSig, ok_bind, pure]
  simp only [runFunction, hs]
  exact run_correct target hb c a b depth Mem.empty below_empty (by decide)

/-- Exact guarded shape generated by native WP: the compiler tests c == false,
    so its then edge selects b and its else edge selects a. -/
def nativeVC (post : Bool → Bool → Bool → Bool → Bool) (c a b : Bool) : Bool :=
  SemRNativeWP.guardedVC (c == false) (post c a b b) (post c a b a)

theorem vc_implies_execution (target : Option TargetInfo)
    (hb : (module target).pointerBits = 64) (ht : (module target).executableTarget = true)
    (post : Bool → Bool → Bool → Bool → Bool) (c a b : Bool) (depth : Nat)
    (hvc : nativeVC post c a b = true) :
    ∃ vs, runFunction (module target) 0 [.bool c, .bool a, .bool b] 12 depth = .ret vs ∧
      SemRNativeWP.postHolds post c a b vs := by
  refine ⟨[.bool (if c then a else b)], function_correct target hb ht c a b depth,
    (if c then a else b), rfl, ?_⟩
  cases c <;> simpa [nativeVC, SemRNativeWP.guardedVC] using hvc

end SemRBooleanWPTwoCells

/- Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemR

namespace SemR

theorem intTy_code_injective (a b : IntTy) : a.code = b.code ↔ a = b := by
  cases a <;> cases b <;> simp [IntTy.code]

theorem ty_beq_exact (a b : Ty) : a.beq b = true ↔ a = b := by
  cases a <;> cases b <;> simp [Ty.beq, intTy_code_injective]

theorem tyListEq_exact (a b : List Ty) : tyListEq a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [tyListEq]
  | cons a as ih => cases b <;> simp [tyListEq, ty_beq_exact, ih]

/-- A successful independently specified constructor has an actual nominal
    row and matching nonvariadic physical signature; no shape-based alias. -/
theorem makesClosure_contract (m : Module) (k after : Core) (results : List Nat)
    (cid target : Nat) (captures : List Val)
    (h : MakesClosure m k results cid target captures (.cont after)) :
    ∃ c apparent f physical,
      nth? m.closures cid = some c ∧ nth? m.funcTys c.func = some apparent ∧
      m.functions.find? (fun f => f.id == target) = some f ∧
      nth? m.funcTys f.ty = some physical ∧
      apparent.vararg = false ∧ physical.vararg = false ∧
      physical.params = c.captures ++ apparent.params ∧
      physical.returns = apparent.returns := by
  cases h with
  | checked c apparent f physical _ hc ha hf hp hb _ =>
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hb
    exact ⟨c, apparent, f, physical, hc, ha, hf, hp,
      hb.1.1.1, hb.1.1.2, (tyListEq_exact _ _).mp hb.1.2,
      (tyListEq_exact _ _).mp hb.2⟩

/-- A successful result binding changes only the SSA environment. -/
theorem bindResults_success (k : Core) (node : Node) (vs : List Val) (after : Core)
    (h : bindResults k node vs = .ok after) :
    after = { k with env := (node.results.zip vs).reverse ++ k.env } := by
  unfold bindResults at h
  split at h
  · cases h
  · cases h
    rfl

/-- Construction success contains the original capture values, in order, and
    changes only the PC and the declared SSA results. No lifetime fact is a premise. -/
theorem makeClosureOn_success (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Val) (after : Core)
    (h : makeClosureOn m k node cid target captures = .ok after) :
    after = { next k with env := (node.results.zip [.closure cid target captures]).reverse ++ k.env } := by
  unfold makeClosureOn at h
  cases hc : nth? m.closures cid with
  | none => simp [hc, tyR] at h
  | some c =>
    simp only [hc] at h
    cases ha : nth? m.funcTys c.func with
    | none => simp [ha, tyR] at h
    | some apparent =>
      simp only [ha] at h
      cases hf : m.functions.find? (fun f => f.id == target) with
      | none => simp [hf, tyR] at h
      | some f =>
        simp only [hf] at h
        cases hp : nth? m.funcTys f.ty with
        | none => simp [hp, tyR] at h
        | some physical =>
          simp only [hp] at h
          split at h
          · cases h
          · cases hs : checkSig m.pointerBits captures c.captures with
            | stop o => rw [hs] at h; cases h
            | ok u =>
              cases u
              rw [hs, ok_bind] at h
              exact bindResults_success (next k) node [.closure cid target captures] after h

/-- Actual SSA operand resolution supplies the captured values; construction
    cannot manufacture a pointer or substitute a constant environment. -/
theorem makeClosureStep_success (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (ids : List Nat) (after : Core)
    (h : makeClosureStep m k node cid target ids = .ok after) :
    ∃ captures, getVs k ids = .ok captures ∧
      after = { next k with env := (node.results.zip [.closure cid target captures]).reverse ++ k.env } := by
  unfold makeClosureStep at h
  cases hs : getVs k ids with
  | stop o => rw [hs] at h; cases h
  | ok captures =>
    rw [hs, ok_bind] at h
    exact ⟨captures, rfl, makeClosureOn_success m k node cid target captures after h⟩

/-- The independently specified Step relation has the same exact-capture
    success guarantee, through step_sound and the real evaluator dispatch. -/
theorem makeClosure_step_success (m : Module) (k after : Core) (results : List Nat)
    (cid target : Nat) (ids : List Nat)
    (hn : nth? k.block.body k.pc = some ⟨.makeClosure cid target ids, results⟩)
    (h : Step m k (.cont after)) :
    ∃ captures, getVs k ids = .ok captures ∧
      after = { next k with env := (results.zip [.closure cid target captures]).reverse ++ k.env } := by
  have run := step_sound m k (.cont after) h
  simp only [stepCore, hn, execNode] at run
  cases hs : makeClosureStep m k ⟨.makeClosure cid target ids, results⟩ cid target ids with
  | stop o => simp [hs, ofR] at run
  | ok produced =>
    simp only [hs, ofR, StepR.cont.injEq] at run
    cases run
    exact makeClosureStep_success m k ⟨.makeClosure cid target ids, results⟩ cid target ids _ hs

/-- No successful constructor changes any allocation, liveness or byte. -/
theorem makeClosure_step_preserves_memory (m : Module) (k after : Core) (results : List Nat)
    (cid target : Nat) (ids : List Nat)
    (hn : nth? k.block.body k.pc = some ⟨.makeClosure cid target ids, results⟩)
    (h : Step m k (.cont after)) : after.mem = k.mem := by
  obtain ⟨captures, _, hs⟩ := makeClosure_step_success m k after results cid target ids hn h
  rw [hs]
  rfl

/-- Looking up a successful singleton result returns the same nominal value
    and all original capture pointers, including allocation and offset. -/
theorem makeClosure_step_exact_result (m : Module) (k after : Core) (result : Nat)
    (cid target : Nat) (ids : List Nat)
    (hn : nth? k.block.body k.pc = some ⟨.makeClosure cid target ids, [result]⟩)
    (h : Step m k (.cont after)) :
    ∃ captures, getVs k ids = .ok captures ∧
      getV after result = .ok (.closure cid target captures) := by
  obtain ⟨captures, hc, hs⟩ := makeClosure_step_success m k after [result] cid target ids hn h
  refine ⟨captures, hc, ?_⟩
  rw [hs]
  simp [getV, lookupEnv]

private def apparent : FuncTy := ⟨[], [], false⟩
private def physical : FuncTy := ⟨[.ptr], [], false⟩
private def target : Func := ⟨1, 1, 0, [], []⟩
private def construction : Node := ⟨.makeClosure 0 1 [0], [1]⟩
private def hostSignature : FuncTy := ⟨[.ptr], [.closure 0], false⟩
private def hostBlock : Block :=
  ⟨0, [(0, .ptr)], [construction, ⟨.ret [1], []⟩]⟩
private def host : Func := ⟨0, 2, 0, [hostBlock], []⟩
private def module : Module :=
  { funcTys := [apparent, physical, hostSignature], enums := [], functions := [target, host],
    closures := [⟨0, [.ptr]⟩] }
private def initial (memory : Mem) (allocation offset : Nat) : Core :=
  { fn := host, sig := hostSignature, block := hostBlock,
    pc := 0, env := [(0, .ptr allocation offset)], depth := 0,
    stack := [], openFrames := [], nextFrame := 0, mem := memory }

/-- The concrete control starts at an actual module function/signature/block. -/
theorem construction_module_entry (allocation offset : Nat) :
    start module 0 [.ptr allocation offset] 0 = .ok (initial Mem.empty allocation offset) := rfl

theorem construction_module_return (allocation offset : Nat) :
    runFunction module 0 [.ptr allocation offset] 2 0 =
      .ret [.closure 0 1 [.ptr allocation offset]] := rfl

/-- The full constructor dispatch is kernel reduced for every pointer
    allocation/offset and every initial memory, even at call depth zero and
    with a declaration as target. It is a value operation, not a call. -/
theorem construction_pointer_exact (memory : Mem) (allocation offset : Nat) :
    stepCore module (initial memory allocation offset) =
      .cont { next (initial memory allocation offset) with
        env := [(1, .closure 0 1 [.ptr allocation offset]), (0, .ptr allocation offset)] } := by
  rfl

theorem construction_pointer_relational (memory : Mem) (allocation offset : Nat) :
    Step module (initial memory allocation offset)
      (.cont { next (initial memory allocation offset) with
        env := [(1, .closure 0 1 [.ptr allocation offset]), (0, .ptr allocation offset)] }) := by
  rw [← construction_pointer_exact]
  exact step_complete _ _

theorem construction_pointer_return (memory : Mem) (allocation offset : Nat) :
    run module 2 (initial memory allocation offset) =
      .ret [.closure 0 1 [.ptr allocation offset]] := by
  rfl

theorem construction_nominal_identity (a b : Nat) :
    (Val.closure a 1 []).ty.beq (.closure b) = (a == b) := rfl

theorem construction_missing_definition :
    makeClosureOn { module with closures := [] } (initial Mem.empty 0 0)
      construction 0 1 [.ptr 0 0] = .stop (.typeError "MakeClosure: undefined closure type") := rfl

theorem construction_missing_apparent :
    makeClosureOn { module with closures := [⟨9, [.ptr]⟩] } (initial Mem.empty 0 0)
      construction 0 1 [.ptr 0 0] = .stop (.typeError "MakeClosure: undefined apparent signature") := rfl

theorem construction_missing_target :
    makeClosureOn { module with functions := [] } (initial Mem.empty 0 0)
      construction 0 1 [.ptr 0 0] = .stop (.typeError "MakeClosure: undefined function") := rfl

theorem construction_missing_physical :
    makeClosureOn { module with functions := [{ target with ty := 9 }] } (initial Mem.empty 0 0)
      construction 0 1 [.ptr 0 0] = .stop (.typeError "MakeClosure: undefined physical signature") := rfl

theorem construction_bad_prefix :
    makeClosureOn { module with funcTys := [apparent, ⟨[.bool], [], false⟩] }
      (initial Mem.empty 0 0) construction 0 1 [.ptr 0 0] =
        .stop (.typeError "MakeClosure: target signature mismatch") := rfl

theorem construction_bad_return :
    makeClosureOn { module with funcTys := [apparent, ⟨[.ptr], [.bool], false⟩] }
      (initial Mem.empty 0 0) construction 0 1 [.ptr 0 0] =
        .stop (.typeError "MakeClosure: target signature mismatch") := rfl

theorem construction_vararg_apparent :
    makeClosureOn { module with funcTys := [⟨[], [], true⟩, physical] }
      (initial Mem.empty 0 0) construction 0 1 [.ptr 0 0] =
        .stop (.typeError "MakeClosure: target signature mismatch") := rfl

theorem construction_vararg_physical :
    makeClosureOn { module with funcTys := [apparent, ⟨[.ptr], [], true⟩] }
      (initial Mem.empty 0 0) construction 0 1 [.ptr 0 0] =
        .stop (.typeError "MakeClosure: target signature mismatch") := rfl

theorem construction_wrong_capture_type :
    makeClosureOn module (initial Mem.empty 0 0) construction 0 1 [.bool true] =
      .stop (.typeError "SignatureMismatch: type mismatch") := rfl

theorem construction_wrong_capture_arity :
    makeClosureOn module (initial Mem.empty 0 0) construction 0 1 [] =
      .stop (.typeError "SignatureMismatch: arity mismatch") := rfl

theorem construction_poison_capture :
    makeClosureOn module (initial Mem.empty 0 0) construction 0 1 [.poison .ptr] =
      .stop (.ub "signature boundary: use of an uninitialized value (poison)") := rfl

theorem construction_missing_operand :
    makeClosureStep module (initial Mem.empty 0 0) construction 0 1 [9] =
      .stop (.typeError "MissingValue: value is not defined") := rfl

theorem construction_wrong_result_arity :
    makeClosureOn module (initial Mem.empty 0 0) ⟨.makeClosure 0 1 [0], []⟩ 0 1 [.ptr 0 0] =
      .stop (.typeError "MalformedInstruction: instruction result arity mismatch") := rfl

/-- Current v63 scalar spelling does not admit closure construction: the
    actual new instruction is refused explicitly, and older versions still
    reject its tag as malformed. Nonempty closure tables also stay refused. -/
theorem construction_instruction_v63_refused :
    inst 63 #[] [70, 0, 0, 0] = .err (.unsupported "inst.make_closure") := rfl

/-- Future wire versions (past the v70 content-addressed weight blobs) remain
    unsupported before their payload is read. -/
theorem construction_wire_future_refused (payload : List Nat) :
    decode (magic ++ [71, 0, 0, 0] ++ payload) = .error (.unsupported "wire_version") := rfl


/-- Previously supported version64 still requires a complete payload. -/
theorem construction_wire_v64_payload_required :
    decode (magic ++ [64, 0, 0, 0]) =
      .error (.malformed "unexpected end of input") := rfl

/-- Current wire65 is recognized without granting a new enum profile. -/
theorem construction_wire_v65_payload_required :
    decode (magic ++ [65, 0, 0, 0]) =
      .error (.malformed "unexpected end of input") := rfl

/-- One fieldless variant, exact SingleInhabited0 descriptor, size0/align1.
    The selector is read faithfully; the fragment does not admit this layout. -/
private def singleInhabitedWireRow : List Nat :=
  [0, 0, 1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 1, 0, 0]

theorem single_inhabited_v65_remains_explicitly_unsupported :
    enumDef 65 #[[]] singleInhabitedWireRow = .err (.unsupported "enum.layout") := rfl

theorem single_inhabited_tag_is_malformed_under_old_header :
    enumDef 64 #[[]] singleInhabitedWireRow = .err (.malformed "invalid tag") := rfl

theorem empty_nominal_does_not_fabricate_a_semr_tag :
    enumDef 65 #[[]] [0, 0, 0, 0, 0, 0, 0] = .err (.unsupported "enum.tag_width") := rfl

/-- Projection reads the selected original capture. The constructor checked its
    declared type; projection itself rechecks the requested result type and
    rejects an unwritten lane, exactly like the reference interpreter. -/
theorem evalExtract_closure_of_checked (m : Module) (ty : Ty) (cid target field : Nat)
    (captures : List Val) (value : Val)
    (hf : nth? captures field = some value)
    (hw : ∀ t, value ≠ .unwritten t)
    (ht : expectTy m.pointerBits value ty = .ok ()) :
    evalExtract m ty (.closure cid target captures) field = .ok value := by
  cases value <;> simp_all [evalExtract, rejectPoison, ok_bind] <;> rfl

/-- At an actual SSA projection node, only the PC and declared result binding
    change. In particular neither memory nor allocation/provenance is rebuilt. -/
theorem extractClosureStep_exact (m : Module) (k : Core) (ty : Ty)
    (cid target aggregate field result : Nat) (captures : List Val) (value : Val)
    (ha : getV k aggregate = .ok (.closure cid target captures))
    (hf : nth? captures field = some value)
    (hw : ∀ t, value ≠ .unwritten t)
    (ht : expectTy m.pointerBits value ty = .ok ()) :
    extractFieldStep m k ⟨.extractField ty aggregate field, [result]⟩ ty aggregate field =
      .ok { next k with env := (result, value) :: k.env } := by
  simp only [extractFieldStep, ha, ok_bind,
    evalExtract_closure_of_checked m ty cid target field captures value hf hw ht]
  rfl

/-- The independent Step relation resolves to the same original capture and
    exact PC/result update, using the real evaluator dispatch and step_sound. -/
theorem extractClosure_step_exact (m : Module) (k after : Core) (ty : Ty)
    (cid target aggregate field result : Nat) (captures : List Val) (value : Val)
    (hn : nth? k.block.body k.pc = some ⟨.extractField ty aggregate field, [result]⟩)
    (ha : getV k aggregate = .ok (.closure cid target captures))
    (hf : nth? captures field = some value)
    (hw : ∀ t, value ≠ .unwritten t)
    (ht : expectTy m.pointerBits value ty = .ok ())
    (h : Step m k (.cont after)) :
    after = { next k with env := (result, value) :: k.env } := by
  have run := step_sound m k (.cont after) h
  simp only [stepCore, hn, execNode,
    extractClosureStep_exact m k ty cid target aggregate field result captures value ha hf hw ht,
    ofR, StepR.cont.injEq] at run
  exact run.symm

/-- Successful capture projection changes no abstract byte, allocation or
    liveness. This is not a theorem about a native closure storage frame. -/
theorem extractClosure_step_preserves_memory (m : Module) (k after : Core) (ty : Ty)
    (cid target aggregate field result : Nat) (captures : List Val) (value : Val)
    (hn : nth? k.block.body k.pc = some ⟨.extractField ty aggregate field, [result]⟩)
    (ha : getV k aggregate = .ok (.closure cid target captures))
    (hf : nth? captures field = some value)
    (hw : ∀ t, value ≠ .unwritten t)
    (ht : expectTy m.pointerBits value ty = .ok ())
    (h : Step m k (.cont after)) : after.mem = k.mem := by
  rw [extractClosure_step_exact m k after ty cid target aggregate field result captures value
    hn ha hf hw ht h]
  rfl

private def pointerApparent : FuncTy := ⟨[], [.ptr], false⟩
private def pointerPhysical : FuncTy := ⟨[.ptr], [.ptr], false⟩
private def pointerBodySig : FuncTy := ⟨[.closure 0], [.ptr], false⟩
private def pointerCallerBlock : Block :=
  ⟨0, [(0, .ptr)],
    [⟨.makeClosure 0 2 [0], [1]⟩, ⟨.call 1 [1], [2]⟩, ⟨.ret [2], []⟩]⟩
private def pointerBodyBlock : Block :=
  ⟨0, [(0, .closure 0)], [⟨.extractField .ptr 0 0, [1]⟩, ⟨.ret [1], []⟩]⟩
private def pointerCaller : Func := ⟨0, 1, 0, [pointerCallerBlock], []⟩
private def pointerBody : Func := ⟨1, 2, 0, [pointerBodyBlock], []⟩
private def pointerAdapter : Func := ⟨2, 1, 0, [pointerCallerBlock], []⟩
private def pointerModule : Module :=
  { funcTys := [pointerApparent, pointerPhysical, pointerBodySig], enums := [],
    functions := [pointerCaller, pointerBody, pointerAdapter], closures := [⟨0, [.ptr]⟩] }
private def pointerInitial (memory : Mem) (allocation offset : Nat) : Core :=
  { fn := pointerCaller, sig := pointerPhysical, block := pointerCallerBlock,
    pc := 0, env := [(0, .ptr allocation offset)], depth := 1,
    stack := [], openFrames := [], nextFrame := 0, mem := memory }

/-- This quoted module has the real source FnOnce pointer-return protocol:
    runtime construction, a direct call on the closure value, capture
    projection, and ordinary returns. No closure application is admitted. -/
theorem closure_direct_pointer_return (allocation offset : Nat) :
    runFunction pointerModule 0 [.ptr allocation offset] 5 1 =
      .ret [.ptr allocation offset] := rfl

/-- The canonical source-derived adapter follows the same protocol. Its own
    identity is construction metadata, never a recursive call or stored field. -/
theorem closure_adapter_pointer_return (allocation offset : Nat) :
    runFunction pointerModule 2 [.ptr allocation offset] 5 1 =
      .ret [.ptr allocation offset] := rfl

/-- Pointer-return computation is independent of every initial abstract byte,
    allocation and liveness state; it never dereferences the captured pointer. -/
theorem closure_direct_pointer_return_any_memory (memory : Mem) (allocation offset : Nat) :
    run pointerModule 5 (pointerInitial memory allocation offset) =
      .ret [.ptr allocation offset] := rfl

/-- Even null is carried unchanged: projection invents no non-null, bounds or
    lifetime premise. Such facts must be established at an actual access. -/
theorem closure_extract_null :
    evalExtract pointerModule .ptr (.closure 0 2 [.nullPtr]) 0 = .ok .nullPtr := rfl

theorem closure_extract_wrong_result_type :
    evalExtract pointerModule .bool (.closure 0 2 [.ptr 7 11]) 0 =
      .stop (.typeError "TypeError: value does not have the expected type") := rfl

theorem closure_extract_wrong_value_kind :
    evalExtract pointerModule .ptr (.closure 0 2 [.int .u64 7]) 0 =
      .stop (.typeError "TypeError: value does not have the expected type") := rfl

/-- The target id cannot be read as a field after the final capture. -/
theorem closure_extract_target_is_not_a_field :
    evalExtract pointerModule .ptr (.closure 0 2 [.ptr 7 11]) 1 =
      .stop (.ub "field is out of bounds") := rfl

theorem closure_extract_wrong_nominal_argument :
    runFunction pointerModule 1 [.closure 1 2 [.ptr 7 11]] 2 0 =
      .typeError "SignatureMismatch: type mismatch" := rfl

theorem closure_extract_unwritten :
    evalExtract pointerModule .ptr (.closure 0 2 [.unwritten .ptr]) 0 =
      .stop (.ub "extract_field: read of an unwritten aggregate lane (uninit)") := rfl

theorem closure_extract_poison_aggregate :
    evalExtract pointerModule .ptr (.poison (.closure 0)) 0 =
      .stop (.ub "extract_field: use of an uninitialized value (poison)") := rfl

/-- Projection observes the captured data, even if the code target is absent.
    Constructor/call validation owns that separate contract; this adds none. -/
theorem closure_extract_does_not_invoke_target (allocation offset : Nat) :
    evalExtract { pointerModule with functions := [] } .ptr
      (.closure 0 999 [.ptr allocation offset]) 0 = .ok (.ptr allocation offset) := rfl

theorem closure_extract_scalar_is_not_an_environment :
    evalExtract pointerModule .ptr (.int .u64 7) 0 =
      .stop (.typeError "TypeError: extract_field requires an aggregate") := rfl

theorem closure_extract_nominal_capture_type_is_exact :
    evalExtract pointerModule (.closure 1) (.closure 0 2 [.closure 2 2 []]) 0 =
      .stop (.typeError "TypeError: value does not have the expected type") := rfl

theorem closure_direct_pointer_wrong_offset_refuted :
    runFunction pointerModule 0 [.ptr 7 11] 5 1 ≠ .ret [.ptr 7 12] := by
  intro h
  cases h

end SemR

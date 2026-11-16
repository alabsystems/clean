/- Exact native WP translation vocabulary and a canonical unsigned return link.
   This adds neither an evaluator nor a program/claim syntax.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRNativeExecutionClaim

namespace SemRNativeUnsignedTranslation
open SemR SemRUnsignedSelect SemRBooleanClaim SemRNativeExecutionClaim

/-- Interpret the actual emitted VC under the original initialized parameters,
    then execute the complete original blob and check its original contract.
    The nonempty domain and every signature-valid input/depth are retained.
    This conditional statement does not establish that the VC itself is valid. -/
def originalWpTranslation (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (contractBytes : Bytes) (bindings : List ContractBinding)
    (vcBytes : Bytes) (vc : Json) (vcBindings : List ContractBinding) : Prop :=
  encodeJson codecFuel vc = some vcBytes ∧
  (∃ expression, decodeClaim codecFuel vc = some expression) ∧
  ∃ m f sig, decode blob = .ok m ∧
    m.functions.find? (fun candidate => candidate.id == fid) = some f ∧
    nth? m.funcTys f.ty = some sig ∧
    (∃ inputs, checkSig m.pointerBits inputs sig.params = .ok ()) ∧
    ∀ inputs depth, checkSig m.pointerBits inputs sig.params = .ok () →
      ∃ env value, contractTypedEnv m vcBindings inputs [] = some env ∧
        checkedTypedJson codecFuel vcBytes vc env = some value ∧
        (value = true → ∃ fuel returned,
          runBlob blob fid inputs fuel depth = .ok (.ret returned) ∧
          originalContractHolds codecFuel m format contractBytes bindings inputs returned)

/-- Exact question indices stay visible to the kernel before it unfolds the
    semantic proposition. The only field is the actual semantic proof. -/
structure TranslationCertificate (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (contractBytes : Bytes) (bindings : List ContractBinding)
    (vcBytes : Bytes) (vc : Json) (vcBindings : List ContractBinding) : Prop where
  holds : originalWpTranslation codecFuel blob fid format contractBytes bindings vcBytes vc vcBindings

/-- The indexed carrier grants exactly the existing semantic proposition. -/
theorem certificate_sound (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (contractBytes : Bytes) (bindings : List ContractBinding)
    (vcBytes : Bytes) (vc : Json) (vcBindings : List ContractBinding)
    (certificate : TranslationCertificate codecFuel blob fid format contractBytes bindings vcBytes vc vcBindings) :
    originalWpTranslation codecFuel blob fid format contractBytes bindings vcBytes vc vcBindings :=
  certificate.holds

/-- A source-independent rule over the actual two instructions at the current
    PC. Both operand reads and widths are eager; return reads the selected SSA
    result, not an input or a caller-supplied result summary. -/
theorem select_return_run (m : Module) (k : Core)
    (dst cond yes no : Nat) (ty : IntTy) (c : Bool) (a b : Nat)
    (selectAt : nth? k.block.body k.pc = some (selectUInt dst cond yes no ty))
    (returnAt : nth? k.block.body (k.pc + 1) = some (returnUInt dst))
    (condition : getV k cond = .ok (.bool c))
    (left : getV k yes = .ok (.int ty a))
    (right : getV k no = .ok (.int ty b))
    (leftBound : a < modulus (ty.bits m.pointerBits))
    (rightBound : b < modulus (ty.bits m.pointerBits))
    (stack : k.stack = []) (signature : k.sig.returns = [.int ty]) :
    run m 2 k = .ret [.int ty (if c then a else b)] := by
  let raw := if c then a else b
  let after := writeUInt k dst ty raw
  have bound : raw < modulus (ty.bits m.pointerBits) := by
    cases c <;> simp_all [raw]
  have selected := selectUInt_step m k dst cond yes no ty c a b
    condition left right leftBound rightBound
  have stepSelected : stepCore m k = .cont after := by
    simpa only [stepCore, selectAt] using selected
  have value : getV after dst = .ok (.int ty raw) := by
    simp [after, writeUInt, getV, lookupEnv]
  have returned := returnUInt_step m after dst ty raw value bound
    (by simpa [after, writeUInt, SemR.next] using stack)
    (by simpa [after, writeUInt, SemR.next] using signature)
  have atReturn : nth? after.block.body after.pc = some (returnUInt dst) := by
    simpa [after, writeUInt, SemR.next] using returnAt
  have stepReturned : stepCore m after = .done (.ret [.int ty raw]) := by
    simpa only [stepCore, atReturn] using returned
  simpa only [run, stepSelected, stepReturned, raw]

/-- The guarded obligations are the only postcondition premise. This conclusion
    uses the canonical evaluator and the actual returned value. -/
theorem guarded_select_return (m : Module) (k : Core)
    (dst cond yes no : Nat) (ty : IntTy) (c : Bool) (a b : Nat)
    (post : Nat → Prop)
    (selectAt : nth? k.block.body k.pc = some (selectUInt dst cond yes no ty))
    (returnAt : nth? k.block.body (k.pc + 1) = some (returnUInt dst))
    (condition : getV k cond = .ok (.bool c))
    (left : getV k yes = .ok (.int ty a))
    (right : getV k no = .ok (.int ty b))
    (leftBound : a < modulus (ty.bits m.pointerBits))
    (rightBound : b < modulus (ty.bits m.pointerBits))
    (stack : k.stack = []) (signature : k.sig.returns = [.int ty])
    (vc : (c = true → post a) ∧ (c = false → post b)) :
    ∃ raw, run m 2 k = .ret [.int ty raw] ∧ post raw := by
  refine ⟨if c then a else b,
    select_return_run m k dst cond yes no ty c a b selectAt returnAt condition
      left right leftBound rightBound stack signature, ?_⟩
  cases c with
  | false => exact vc.2 rfl
  | true => exact vc.1 rfl

end SemRNativeUnsignedTranslation

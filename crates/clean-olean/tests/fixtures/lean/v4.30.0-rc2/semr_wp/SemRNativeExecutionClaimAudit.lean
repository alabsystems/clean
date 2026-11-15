/- Actual original-byte execution claim and hostile domain/contract controls.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRNativeExecutionClaim

set_option maxRecDepth 8192

namespace SemRNativeExecutionClaimAudit
open SemR SemRBooleanClaim SemRNativeExecutionClaim SemRBooleanWPBranches

private theorem stopped {α β : Type} (out : Out) (next : α → R β) :
    ((R.stop out : R α) >>= next) = .stop out := rfl

/-- The original wire image from fixtures/native_wp/universal-permuted.json. -/
def bodyBlob : Bytes := [84,82,85,83,84,95,73,82,38,0,0,0,2,24,115,101,109,114,95,98,111,111,108,101,97,110,95,119,112,95,98,114,97,110,99,104,101,115,6,99,104,111,111,115,101,0,1,3,12,12,12,1,12,0,0,0,0,0,0,0,1,0,1,0,0,4,0,3,0,12,1,12,2,12,1,16,0,1,2,2,1,2,2,2,1,0,0,0,0,0,1,2,3,12,4,12,1,15,3,1,4,0,0,0,0,0,2,2,5,12,6,12,1,15,3,1,5,0,0,0,0,0,3,1,7,12,1,20,1,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Swap only the two valid branch targets, retaining a well-typed false body. -/
def wrongBodyBlob : Bytes := (bodyBlob.set 77 2).set 81 1

def bindings : List ContractBinding :=
  [([99], .param 0, .bool), ([97], .param 1, .bool),
   ([98], .param 2, .bool), ([114], .result 0, .bool)]
def contractBytes : Bytes := "(c ==> r == a) && (!c ==> r == b)".toList.map Char.toNat
def falseBytes : Bytes := [102,97,108,115,101]

theorem decoded : decode bodyBlob = .ok chooseModule := rfl
theorem wrong_body_decoded : decode wrongBodyBlob =
    .ok (variantModule 0 2 [2, 1] 1 [2, 1]) := rfl

theorem selected_contract (c a b : Bool) :
    originalContractHolds 4096 chooseModule .booleanText contractBytes bindings
      [.bool c, .bool a, .bool b] [.bool (if c then a else b)] := by
  refine ⟨([([99], c), ([97], a), ([98], b),
    ([114], if c then a else b)], []), ?_, ?_⟩
  · cases c <;> cases a <;> cases b <;> rfl
  · cases c <;> cases a <;> cases b <;> rfl

theorem original_choose :
    originalExecution 4096 bodyBlob 0 .booleanText contractBytes bindings := by
  apply originalExecution_of_surjective (α := Bool × Bool × Bool)
    4096 bodyBlob 0 .booleanText contractBytes bindings
    chooseModule chooseFunction chooseSignature decoded (by rfl) (by rfl)
    (fun values => [.bool values.1, .bool values.2.1, .bool values.2.2])
    (false, false, false)
  · intro values
    rcases values with ⟨c, a, b⟩
    cases c <;> cases a <;> cases b <;> rfl
  · intro inputs valid
    obtain ⟨c, tail1, h1, v1⟩ :=
      (signatureBool chooseModule.pointerBits inputs [.bool, .bool]).mp valid
    obtain ⟨a, tail2, h2, v2⟩ :=
      (signatureBool chooseModule.pointerBits tail1 [.bool]).mp v1
    obtain ⟨b, tail3, h3, v3⟩ :=
      (signatureBool chooseModule.pointerBits tail2 []).mp v2
    have empty := (signatureNil _ _).mp v3
    refine ⟨(c, a, b), ?_⟩
    rw [h1, h2, h3, empty]
  · rintro ⟨c, a, b⟩ depth
    refine ⟨3, [.bool (if c then a else b)], ?_, selected_contract c a b⟩
    simp only [runBlob, decoded]
    exact congrArg Except.ok (choose_correct c a b depth)

def ExecutionClaim : Prop :=
  originalExecution 4096 bodyBlob 0 .booleanText contractBytes bindings
def FalseBody : Prop :=
  originalExecution 4096 wrongBodyBlob 0 .booleanText contractBytes bindings
def FalseContract : Prop :=
  originalExecution 4096 bodyBlob 0 .booleanText falseBytes bindings

def expression : Expr := .binary .and
  (.binary .implies (.var [99]) (.binary .eq (.var [114]) (.var [97])))
  (.binary .implies (.not (.var [99])) (.binary .eq (.var [114]) (.var [98])))
theorem original_contract_decoded :
    decodeText 4096 (bindings.map Prod.fst) contractBytes = some expression := rfl
theorem false_contract_decoded :
    decodeText 4096 (bindings.map Prod.fst) falseBytes = some (.literal false) := rfl

def modelPost (m : SemR.Module) (post : Expr) (inputs returned : List Val) : Prop :=
  ∃ env, contractTypedEnv m bindings inputs returned = some env ∧ eval env.1 post = some true

theorem original_contract_equiv (m : SemR.Module) (inputs returned : List Val) :
    originalContractHolds 4096 m .booleanText contractBytes bindings inputs returned ↔
      modelPost m expression inputs returned := by
  simp only [originalContractHolds, modelPost,
    checked_text_eval 4096 contractBytes (bindings.map Prod.fst) expression _ original_contract_decoded]

theorem false_contract_equiv (m : SemR.Module) (inputs returned : List Val) :
    originalContractHolds 4096 m .booleanText falseBytes bindings inputs returned ↔
      modelPost m (.literal false) inputs returned := by
  simp only [originalContractHolds, modelPost,
    checked_text_eval 4096 falseBytes (bindings.map Prod.fst) (.literal false) _ false_contract_decoded]

/-- Normalization changes no quantifier, program, contract byte or binding. -/
def ModelExecution : Prop := ∀ inputs depth,
  checkSig chooseModule.pointerBits inputs chooseSignature.params = .ok () →
    ∃ fuel returned, runFunction chooseModule 0 inputs fuel depth = .ret returned ∧
      modelPost chooseModule expression inputs returned
def ModelFalseBody : Prop := ∀ inputs depth,
  checkSig (variantModule 0 2 [2, 1] 1 [2, 1]).pointerBits inputs chooseSignature.params = .ok () →
    ∃ fuel returned, runFunction (variantModule 0 2 [2, 1] 1 [2, 1]) 0 inputs fuel depth = .ret returned ∧
      modelPost (variantModule 0 2 [2, 1] 1 [2, 1]) expression inputs returned
def ModelFalseContract : Prop := ∀ inputs depth,
  checkSig chooseModule.pointerBits inputs chooseSignature.params = .ok () →
    ∃ fuel returned, runFunction chooseModule 0 inputs fuel depth = .ret returned ∧
      modelPost chooseModule (.literal false) inputs returned

theorem execution_model_equiv : ExecutionClaim ↔ ModelExecution := by
  simpa only [ExecutionClaim, ModelExecution, original_contract_equiv] using
    originalExecution_model_iff 4096 bodyBlob 0 .booleanText contractBytes bindings
      chooseModule chooseFunction chooseSignature decoded (by rfl) (by rfl)
      ⟨[.bool false, .bool false, .bool false], rfl⟩
theorem false_body_model_equiv : FalseBody ↔ ModelFalseBody := by
  simpa only [FalseBody, ModelFalseBody, original_contract_equiv] using
    originalExecution_model_iff 4096 wrongBodyBlob 0 .booleanText contractBytes bindings
      (variantModule 0 2 [2, 1] 1 [2, 1]) (variantFunction 0 2 [2, 1] 1 [2, 1])
      chooseSignature wrong_body_decoded (by rfl) (by rfl)
      ⟨[.bool false, .bool false, .bool false], rfl⟩
theorem false_contract_model_equiv : FalseContract ↔ ModelFalseContract := by
  simpa only [FalseContract, ModelFalseContract, false_contract_equiv] using
    originalExecution_model_iff 4096 bodyBlob 0 .booleanText falseBytes bindings
      chooseModule chooseFunction chooseSignature decoded (by rfl) (by rfl)
      ⟨[.bool false, .bool false, .bool false], rfl⟩
theorem model_execution : ModelExecution := execution_model_equiv.mp original_choose

theorem false_contract_refused (inputs returned : List Val) :
    ¬ originalContractHolds 4096 chooseModule .booleanText falseBytes bindings inputs returned := by
  rintro ⟨env, _, checked⟩
  have falseCheck : checkedText 4096 falseBytes (bindings.map Prod.fst) env.1 = some false := rfl
  rw [falseCheck] at checked
  cases checked

/-- There is no initialized value of a storage-only type, regardless of arity. -/
theorem storage_domain_empty (pointerBits : Nat) (inputs : List Val) :
    checkSig pointerBits inputs [.storage 0 1] ≠ .ok () := by
  cases inputs with
  | nil => simp [checkSig, tyR]
  | cons value tail =>
      cases value <;>
        simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, tyR, ubR, ok_bind, stopped]

def EmptyInvalidDomain : Prop := ∃ inputs, checkSig 64 inputs [.storage 0 1] = .ok ()
theorem empty_invalid_domain : ¬ EmptyInvalidDomain := by
  rintro ⟨inputs, valid⟩
  exact storage_domain_empty 64 inputs valid

theorem empty_signature_cannot_execute (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (bytes : Bytes) (typedBindings : List ContractBinding)
    (m : SemR.Module) (f : Func) (sig : FuncTy)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig)
    (invalid : sig.params = [.storage 0 1]) :
    ¬ originalExecution codecFuel blob fid format bytes typedBindings := by
  intro claim
  obtain ⟨inputs, valid⟩ := originalExecution_has_input codecFuel blob fid format bytes
    typedBindings claim m f sig decoded found signature
  rw [invalid] at valid
  exact storage_domain_empty m.pointerBits inputs valid

end SemRNativeExecutionClaimAudit

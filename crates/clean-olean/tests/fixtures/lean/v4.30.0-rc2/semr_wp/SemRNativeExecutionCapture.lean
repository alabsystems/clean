/- Full captured native artifact and its original stored WP contract.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRNativeExecutionClaim
import SemRBooleanWPBranches

set_option maxRecDepth 8192
namespace SemRNativeExecutionCapture
open SemR SemRBooleanClaim SemRNativeExecutionClaim SemRBooleanWPBranches
private theorem stopped {α β : Type} (out : Out) (next : α → R β) :
    ((R.stop out : R α) >>= next) = .stop out := rfl

/-- Entire canonical serialization of capture.bundle.module: proof records,
    original strings and typed bindings are retained, not projected away. -/
def moduleBytes : Bytes := [84,82,85,83,84,95,73,82,41,0,0,0,12,24,115,101,109,114,95,98,111,111,108,101,97,110,95,119,112,95,98,114,97,110,99,104,101,115,6,99,104,111,111,115,101,41,101,120,112,108,105,99,105,116,32,115,104,97,114,101,100,45,73,82,32,99,97,108,99,117,108,117,115,32,112,111,115,116,99,111,110,100,105,116,105,111,110,21,116,114,117,115,116,45,119,112,46,112,117,114,101,45,101,120,112,114,46,118,49,89,40,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,108,32,58,32,98,111,111,108,41,41,41,32,124,124,32,40,33,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,113,32,58,32,98,111,111,108,41,41,41,1,99,1,108,1,113,1,114,33,101,120,112,108,105,99,105,116,45,99,97,108,99,117,108,117,115,58,112,101,114,109,117,116,101,100,58,99,104,111,111,115,101,11,97,115,115,101,114,116,105,111,110,58,48,27,118,99,58,116,114,117,115,116,45,119,112,58,112,111,115,116,99,111,110,100,105,116,105,111,110,58,48,0,1,3,12,12,12,1,12,0,0,0,0,0,0,0,1,0,1,0,0,4,0,3,0,12,1,12,2,12,1,16,0,1,2,2,1,2,2,2,1,0,0,0,0,0,1,2,3,12,4,12,1,15,3,1,4,0,0,0,0,0,2,2,5,12,6,12,1,15,3,1,5,0,0,0,0,0,3,1,7,12,1,20,1,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,1,3,4,0,0,4,5,0,0,0,6,0,0,1,7,0,0,2,8,0,1,0,1,0,1,9,10,0,1,11,0,107,22,142,17,27,81,138,175,202,82,2,89,93,64,13,153,17,100,17,91,159,67,165,154,167,196,119,45,73,59,38,144,0,0,0,0,0,0,0,0,0,0]
def wrongModuleBytes : Bytes := [84,82,85,83,84,95,73,82,41,0,0,0,12,24,115,101,109,114,95,98,111,111,108,101,97,110,95,119,112,95,98,114,97,110,99,104,101,115,6,99,104,111,111,115,101,41,101,120,112,108,105,99,105,116,32,115,104,97,114,101,100,45,73,82,32,99,97,108,99,117,108,117,115,32,112,111,115,116,99,111,110,100,105,116,105,111,110,21,116,114,117,115,116,45,119,112,46,112,117,114,101,45,101,120,112,114,46,118,49,89,40,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,108,32,58,32,98,111,111,108,41,41,41,32,124,124,32,40,33,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,113,32,58,32,98,111,111,108,41,41,41,1,99,1,108,1,113,1,114,33,101,120,112,108,105,99,105,116,45,99,97,108,99,117,108,117,115,58,112,101,114,109,117,116,101,100,58,99,104,111,111,115,101,11,97,115,115,101,114,116,105,111,110,58,48,27,118,99,58,116,114,117,115,116,45,119,112,58,112,111,115,116,99,111,110,100,105,116,105,111,110,58,48,0,1,3,12,12,12,1,12,0,0,0,0,0,0,0,1,0,1,0,0,4,0,3,0,12,1,12,2,12,1,16,0,2,2,2,1,1,2,2,1,0,0,0,0,0,1,2,3,12,4,12,1,15,3,1,4,0,0,0,0,0,2,2,5,12,6,12,1,15,3,1,5,0,0,0,0,0,3,1,7,12,1,20,1,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,1,3,4,0,0,4,5,0,0,0,6,0,0,1,7,0,0,2,8,0,1,0,1,0,1,9,10,0,1,11,0,107,22,142,17,27,81,138,175,202,82,2,89,93,64,13,153,17,100,17,91,159,67,165,154,167,196,119,45,73,59,38,144,0,0,0,0,0,0,0,0,0,0]
def emptyModuleBytes : Bytes := [84,82,85,83,84,95,73,82,41,0,0,0,12,24,115,101,109,114,95,98,111,111,108,101,97,110,95,119,112,95,98,114,97,110,99,104,101,115,6,99,104,111,111,115,101,41,101,120,112,108,105,99,105,116,32,115,104,97,114,101,100,45,73,82,32,99,97,108,99,117,108,117,115,32,112,111,115,116,99,111,110,100,105,116,105,111,110,21,116,114,117,115,116,45,119,112,46,112,117,114,101,45,101,120,112,114,46,118,49,89,40,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,108,32,58,32,98,111,111,108,41,41,41,32,124,124,32,40,33,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,113,32,58,32,98,111,111,108,41,41,41,1,99,1,108,1,113,1,114,33,101,120,112,108,105,99,105,116,45,99,97,108,99,117,108,117,115,58,112,101,114,109,117,116,101,100,58,99,104,111,111,115,101,11,97,115,115,101,114,116,105,111,110,58,48,27,118,99,58,116,114,117,115,116,45,119,112,58,112,111,115,116,99,111,110,100,105,116,105,111,110,58,48,0,1,3,15,12,12,1,12,0,0,0,0,0,0,0,1,0,1,0,0,4,0,3,0,12,1,12,2,12,1,16,0,1,2,2,1,2,2,2,1,0,0,0,0,0,1,2,3,12,4,12,1,15,3,1,4,0,0,0,0,0,2,2,5,12,6,12,1,15,3,1,5,0,0,0,0,0,3,1,7,12,1,20,1,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,1,3,4,0,0,4,5,0,0,0,6,0,0,1,7,0,0,2,8,0,1,0,1,0,1,9,10,0,1,11,0,107,22,142,17,27,81,138,175,202,82,2,89,93,64,13,153,17,100,17,91,159,67,165,154,167,196,119,45,73,59,38,144,0,0,0,0,0,0,0,0,0,0]
def contractBytes : Bytes := [40,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,108,32,58,32,98,111,111,108,41,41,41,32,124,124,32,40,33,40,99,32,58,32,98,111,111,108,41,32,38,38,32,40,40,114,32,58,32,98,111,111,108,41,32,61,61,32,40,113,32,58,32,98,111,111,108,41,41,41]

def bindings : List ContractBinding :=
  [([99], .param 0, .bool), ([108], .param 1, .bool),
   ([113], .param 2, .bool), ([114], .result 0, .bool)]
def widthBindings : List ContractBinding :=
  [([99], .param 0, .int .u8), ([108], .param 1, .bool),
   ([113], .param 2, .bool), ([114], .result 0, .bool)]
def placeBindings : List ContractBinding :=
  [([99], .param 0, .bool), ([108], .param 1, .bool),
   ([113], .param 2, .bool), ([114], .param 0, .bool)]
def namespaceBindings : List ContractBinding :=
  [([120], .param 0, .bool), ([108], .param 1, .bool),
   ([113], .param 2, .bool), ([114], .result 0, .bool)]
def falseBytes : Bytes := [102,97,108,115,101]
def emptySignature : FuncTy := { chooseSignature with params := [.never, .bool, .bool] }
def emptyModule : SemR.Module := { chooseModule with funcTys := [emptySignature] }

theorem decoded : decode moduleBytes = .ok chooseModule := rfl
theorem wrong_decoded : decode wrongModuleBytes =
    .ok (variantModule 0 2 [2, 1] 1 [2, 1]) := rfl
theorem empty_decoded : decode emptyModuleBytes = .ok emptyModule := rfl

def expression : Expr := .binary .or
  (.binary .and (.var [99]) (.binary .eq (.var [114]) (.var [108])))
  (.binary .and (.not (.var [99])) (.binary .eq (.var [114]) (.var [113])))
theorem contract_decoded : decodeTypedText 4096 (booleanBindingNames bindings) (integerBindingNames bindings) contractBytes =
    some expression := rfl

def modelPost (m : SemR.Module) (bound : List ContractBinding) (post : Expr)
    (inputs returned : List Val) : Prop :=
  ∃ env, contractTypedEnv m bound inputs returned = some env ∧ evalTyped env.1 env.2 post = some true

theorem contract_equiv (m : SemR.Module) (bound : List ContractBinding)
    (bytes : Bytes) (post : Expr)
    (parsed : decodeTypedText 4096 (booleanBindingNames bound) (integerBindingNames bound) bytes = some post)
    (inputs returned : List Val) :
    originalContractHolds 4096 m .booleanText bytes bound inputs returned ↔
      modelPost m bound post inputs returned := by
  simp only [originalContractHolds, modelPost, checkedContractText, checkedTypedText, parsed, Option.bind_some]

def modelExecution (m : SemR.Module) (bound : List ContractBinding) (post : Expr) : Prop :=
  ∀ inputs depth, checkSig m.pointerBits inputs chooseSignature.params = .ok () →
    ∃ fuel returned, runFunction m 0 inputs fuel depth = .ret returned ∧
      modelPost m bound post inputs returned

theorem normalize (blob : Bytes) (m : SemR.Module) (f : Func)
    (bytes : Bytes) (bound : List ContractBinding) (post : Expr)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == 0) = some f)
    (signature : nth? m.funcTys f.ty = some chooseSignature)
    (inhabited : ∃ inputs, checkSig m.pointerBits inputs chooseSignature.params = .ok ())
    (parsed : decodeTypedText 4096 (booleanBindingNames bound) (integerBindingNames bound) bytes = some post) :
    originalExecution 4096 blob 0 .booleanText bytes bound ↔ modelExecution m bound post := by
  simpa only [modelExecution, contract_equiv m bound bytes post parsed] using
    originalExecution_model_iff 4096 blob 0 .booleanText bytes bound m f
      chooseSignature decoded found signature inhabited

def ExecutionClaim : Prop := originalExecution 4096 moduleBytes 0 .booleanText contractBytes bindings
def WrongProgram : Prop := originalExecution 4096 wrongModuleBytes 0 .booleanText contractBytes bindings
def WrongContract : Prop := originalExecution 4096 moduleBytes 0 .booleanText falseBytes bindings
def WrongWidth : Prop := originalExecution 4096 moduleBytes 0 .booleanText contractBytes widthBindings
def WrongPlace : Prop := originalExecution 4096 moduleBytes 0 .booleanText contractBytes placeBindings
def WrongNamespace : Prop := originalExecution 4096 moduleBytes 0 .booleanText contractBytes namespaceBindings
def EmptyDomainClaim : Prop := originalExecution 4096 emptyModuleBytes 0 .booleanText contractBytes bindings

def ModelExecution : Prop := modelExecution chooseModule bindings expression
def ModelWrongProgram : Prop := modelExecution (variantModule 0 2 [2, 1] 1 [2, 1]) bindings expression
def ModelWrongContract : Prop := modelExecution chooseModule bindings (.literal false)
def ModelWrongWidth : Prop := modelExecution chooseModule widthBindings expression
def ModelWrongPlace : Prop := modelExecution chooseModule placeBindings expression

theorem execution_equiv : ExecutionClaim ↔ ModelExecution :=
  normalize moduleBytes chooseModule chooseFunction contractBytes bindings expression
    decoded (by rfl) (by rfl) ⟨[.bool false, .bool false, .bool false], rfl⟩ contract_decoded
theorem program_equiv : WrongProgram ↔ ModelWrongProgram :=
  normalize wrongModuleBytes (variantModule 0 2 [2, 1] 1 [2, 1])
    (variantFunction 0 2 [2, 1] 1 [2, 1]) contractBytes bindings expression
    wrong_decoded (by rfl) (by rfl) ⟨[.bool false, .bool false, .bool false], rfl⟩ contract_decoded
theorem false_equiv : WrongContract ↔ ModelWrongContract :=
  normalize moduleBytes chooseModule chooseFunction falseBytes bindings (.literal false)
    decoded (by rfl) (by rfl) ⟨[.bool false, .bool false, .bool false], rfl⟩ (by rfl)
theorem wrong_width_text_refused :
    decodeTypedText 4096 (booleanBindingNames widthBindings)
      (integerBindingNames widthBindings) contractBytes = none := rfl

/-- The wrong-width mutant already fails native binding and now also fails
    sort decoding. Preserve both original execution/model refusal claims. -/
theorem width_equiv : WrongWidth ↔ ModelWrongWidth := by
  have bindingRefused (returned : List Val) :
      contractTypedEnv chooseModule widthBindings
        [.bool false, .bool false, .bool false] returned = none := rfl
  constructor
  · intro claim
    obtain ⟨_, returned, _, env, bound, _⟩ := originalExecution_at 4096 moduleBytes 0
      .booleanText contractBytes widthBindings claim chooseModule chooseFunction
      chooseSignature decoded (by rfl) (by rfl)
      [.bool false, .bool false, .bool false] 0 (by rfl)
    rw [bindingRefused returned] at bound
    cases bound
  · intro claim
    obtain ⟨_, returned, _, env, bound, _⟩ := claim
      [.bool false, .bool false, .bool false] 0 (by rfl)
    rw [bindingRefused returned] at bound
    cases bound
theorem place_equiv : WrongPlace ↔ ModelWrongPlace :=
  normalize moduleBytes chooseModule chooseFunction contractBytes placeBindings expression
    decoded (by rfl) (by rfl) ⟨[.bool false, .bool false, .bool false], rfl⟩ (by rfl)

theorem selected_contract (c l q : Bool) :
    originalContractHolds 4096 chooseModule .booleanText contractBytes bindings
      [.bool c, .bool l, .bool q] [.bool (if c then l else q)] := by
  refine ⟨([([99], c), ([108], l), ([113], q),
    ([114], if c then l else q)], []), ?_, ?_⟩
  · cases c <;> cases l <;> cases q <;> rfl
  · cases c <;> cases l <;> cases q <;> rfl

theorem original_execution : ExecutionClaim := by
  apply originalExecution_of_surjective (α := Bool × Bool × Bool)
    4096 moduleBytes 0 .booleanText contractBytes bindings
    chooseModule chooseFunction chooseSignature decoded (by rfl) (by rfl)
    (fun values => [.bool values.1, .bool values.2.1, .bool values.2.2])
    (false, false, false)
  · intro values
    rcases values with ⟨c, l, q⟩
    cases c <;> cases l <;> cases q <;> rfl
  · intro inputs valid
    obtain ⟨c, rest, same, valid⟩ := (signatureBool 64 inputs [.bool, .bool]).mp valid
    obtain ⟨l, rest', same', valid⟩ := (signatureBool 64 rest [.bool]).mp valid
    obtain ⟨q, tail, same'', valid⟩ := (signatureBool 64 rest' []).mp valid
    have empty := (signatureNil 64 tail).mp valid
    subst tail
    subst rest'
    subst rest
    subst inputs
    exact ⟨(c, l, q), rfl⟩
  · rintro ⟨c, l, q⟩ depth
    refine ⟨3, [.bool (if c then l else q)], ?_, selected_contract c l q⟩
    simpa only [runBlob, decoded] using congrArg Except.ok (choose_correct c l q depth)

theorem model_execution : ModelExecution := execution_equiv.mp original_execution

theorem namespace_none (m : SemR.Module) (inputs returned : List Val) :
    originalContractHolds 4096 m .booleanText contractBytes namespaceBindings inputs returned ↔ False := by
  constructor
  · rintro ⟨env, _, checked⟩
    have none : checkedContractText 4096 contractBytes namespaceBindings env = none := rfl
    rw [none] at checked
    cases checked
  · exact False.elim

def ModelWrongNamespace : Prop := ∀ inputs depth,
  checkSig 64 inputs chooseSignature.params = .ok () →
    ∃ fuel returned, runFunction chooseModule 0 inputs fuel depth = .ret returned ∧ False

theorem namespace_equiv : WrongNamespace ↔ ModelWrongNamespace := by
  simpa only [ModelWrongNamespace, namespace_none] using
    originalExecution_model_iff 4096 moduleBytes 0 .booleanText contractBytes namespaceBindings
      chooseModule chooseFunction chooseSignature decoded (by rfl) (by rfl)
      ⟨[.bool false, .bool false, .bool false], rfl⟩

theorem never_domain_empty (inputs : List Val) :
    checkSig 64 inputs emptySignature.params ≠ .ok () := by
  cases inputs with
  | nil => simp [emptySignature, checkSig, tyR]
  | cons value tail =>
    cases value <;> simp [emptySignature, checkSig, rejectPoison, expectTy, Val.ty,
      Ty.beq, tyR, ubR, ok_bind, stopped]

/-- This deliberately omits the inhabited-domain witness; the API may not
    accept it as a proof of the fixed originalExecution proposition. -/
def MissingDomain : Prop := ∀ inputs depth,
  checkSig 64 inputs emptySignature.params = .ok () →
    ∃ fuel returned, runBlob emptyModuleBytes 0 inputs fuel depth = .ok (.ret returned) ∧
      originalContractHolds 4096 emptyModule .booleanText contractBytes bindings inputs returned

theorem missing_domain : MissingDomain := by
  intro inputs _ valid
  exact False.elim (never_domain_empty inputs valid)

theorem empty_domain_refused : ¬ EmptyDomainClaim := by
  intro claim
  obtain ⟨inputs, valid⟩ := originalExecution_has_input 4096 emptyModuleBytes 0
    .booleanText contractBytes bindings claim emptyModule chooseFunction emptySignature
    empty_decoded (by rfl) (by rfl)
  exact never_domain_empty inputs valid
end SemRNativeExecutionCapture

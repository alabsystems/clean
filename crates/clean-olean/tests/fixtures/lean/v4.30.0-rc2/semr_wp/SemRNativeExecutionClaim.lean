/- Original native execution and contract propositions over the existing SemR
   decoder, evaluator and exact-byte claim checkers. This is mathematical input
   vocabulary, not a proof grade or a source-ABI authority.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRBooleanClaimText
import SemRScalarClaim

namespace SemRNativeExecutionClaim
open SemR SemRBooleanClaim

private theorem stop_bind {α β : Type} (out : Out) (next : α → R β) :
    ((R.stop out : R α) >>= next) = .stop out := rfl

inductive ContractFormat where
  | booleanText
  | typedJson

def booleanBindingNames (bindings : List ContractBinding) : List Name :=
  bindings.filterMap fun (name, _, ty) => match ty with
    | .bool => some name
    | _ => none

def integerBindingNames (bindings : List ContractBinding) : List Name :=
  bindings.filterMap fun (name, _, ty) => match ty with
    | .int _ => some name
    | _ => none

/-- The original place/type inventory selects the text codec's sorts. Actual
    values still come only from contractTypedEnv and its native range checks. -/
def checkedContractText (codecFuel : Nat) (bytes : Bytes)
    (bindings : List ContractBinding) (env : TypedEnv) : Option Bool :=
  checkedTypedText codecFuel bytes (booleanBindingNames bindings)
    (integerBindingNames bindings) env

theorem checked_contract_text_eval (fuel : Nat) (bytes : Bytes)
    (bindings : List ContractBinding) (expression : Expr) (env : TypedEnv)
    (decoded : decodeTypedText fuel (booleanBindingNames bindings)
      (integerBindingNames bindings) bytes = some expression) :
    checkedContractText fuel bytes bindings env = evalTyped env.1 env.2 expression := by
  simp [checkedContractText, checkedTypedText, decoded]

/-- Bind the original typed parameter/result places before interpreting the
    original contract bytes. A proposed JSON tree must encode to those bytes. -/
def originalContractHolds (codecFuel : Nat) (m : SemR.Module)
    (format : ContractFormat) (contractBytes : Bytes)
    (typedBindings : List ContractBinding) (inputs returned : List Val) : Prop :=
  ∃ env, contractTypedEnv m typedBindings inputs returned = some env ∧
    match format with
    | .booleanText =>
        checkedContractText codecFuel contractBytes typedBindings env = some true
    | .typedJson =>
        ∃ proposed, checkedTypedJson codecFuel contractBytes proposed env = some true

/-- Total successful execution for every initialized, exactly typed input and
    every call-depth budget. The inhabited domain rules out vacuous signatures.
    Call-free programs can satisfy the depth-zero instance; calls cannot hide it.
    The run always consumes the ORIGINAL blob, not a decoded replacement model. -/
def originalExecution (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (contractBytes : Bytes)
    (typedBindings : List ContractBinding) : Prop :=
  ∃ m f sig, decode blob = .ok m ∧
    m.functions.find? (fun candidate => candidate.id == fid) = some f ∧
    nth? m.funcTys f.ty = some sig ∧
    (∃ inputs, checkSig m.pointerBits inputs sig.params = .ok ()) ∧
    ∀ inputs depth, checkSig m.pointerBits inputs sig.params = .ok () →
      ∃ fuel returned, runBlob blob fid inputs fuel depth = .ok (.ret returned) ∧
        originalContractHolds codecFuel m format contractBytes typedBindings inputs returned

theorem originalExecution_iff (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (contractBytes : Bytes) (bindings : List ContractBinding) :
    originalExecution codecFuel blob fid format contractBytes bindings ↔
      ∃ m f sig, decode blob = .ok m ∧
        m.functions.find? (fun candidate => candidate.id == fid) = some f ∧
        nth? m.funcTys f.ty = some sig ∧
        (∃ inputs, checkSig m.pointerBits inputs sig.params = .ok ()) ∧
        ∀ inputs depth, checkSig m.pointerBits inputs sig.params = .ok () →
          ∃ fuel returned, runBlob blob fid inputs fuel depth = .ok (.ret returned) ∧
            originalContractHolds codecFuel m format contractBytes bindings inputs returned := Iff.rfl

theorem originalContractHolds_text_sound (codecFuel : Nat) (m : SemR.Module)
    (bytes : Bytes) (bindings : List ContractBinding) (inputs returned : List Val)
    (accepted : originalContractHolds codecFuel m .booleanText bytes bindings inputs returned) :
    ∃ env expression, contractTypedEnv m bindings inputs returned = some env ∧
      decodeTypedText codecFuel (booleanBindingNames bindings)
        (integerBindingNames bindings) bytes = some expression ∧
      evalTyped env.1 env.2 expression = some true := by
  obtain ⟨env, bound, checked⟩ := accepted
  obtain ⟨expression, decoded, evaluated⟩ :=
    checked_typed_text_sound codecFuel bytes (booleanBindingNames bindings)
      (integerBindingNames bindings) env true checked
  exact ⟨env, expression, bound, decoded, evaluated⟩

theorem originalContractHolds_json_sound (codecFuel : Nat) (m : SemR.Module)
    (bytes : Bytes) (bindings : List ContractBinding) (inputs returned : List Val)
    (accepted : originalContractHolds codecFuel m .typedJson bytes bindings inputs returned) :
    ∃ env proposed expression, contractTypedEnv m bindings inputs returned = some env ∧
      encodeJson codecFuel proposed = some bytes ∧
      decodeClaim codecFuel proposed = some expression ∧
      evalTyped env.1 env.2 expression = some true := by
  obtain ⟨env, bound, proposed, checked⟩ := accepted
  obtain ⟨expression, encoded, decoded, evaluated⟩ :=
    checked_typed_json_sound codecFuel bytes proposed env true checked
  exact ⟨env, proposed, expression, bound, encoded, decoded, evaluated⟩

theorem originalExecution_at (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (bytes : Bytes) (bindings : List ContractBinding)
    (claim : originalExecution codecFuel blob fid format bytes bindings)
    (m : SemR.Module) (f : Func) (sig : FuncTy)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig)
    (inputs : List Val) (depth : Nat)
    (valid : checkSig m.pointerBits inputs sig.params = .ok ()) :
    ∃ fuel returned, runBlob blob fid inputs fuel depth = .ok (.ret returned) ∧
      originalContractHolds codecFuel m format bytes bindings inputs returned := by
  obtain ⟨actual, fn, ty, hm, hf, hs, _, executes⟩ := claim
  rw [decoded] at hm
  cases hm
  rw [found] at hf
  cases hf
  rw [signature] at hs
  cases hs
  exact executes inputs depth valid

theorem originalExecution_has_input (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (bytes : Bytes) (bindings : List ContractBinding)
    (claim : originalExecution codecFuel blob fid format bytes bindings)
    (m : SemR.Module) (f : Func) (sig : FuncTy)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig) :
    ∃ inputs, checkSig m.pointerBits inputs sig.params = .ok () := by
  obtain ⟨actual, fn, ty, hm, hf, hs, inhabited, _⟩ := claim
  rw [decoded] at hm
  cases hm
  rw [found] at hf
  cases hf
  rw [signature] at hs
  cases hs
  exact inhabited

/-- Exact decoding and signature selection expose the evaluator form of the
    SAME original-byte claim. All signature-valid inputs and depths remain. -/
theorem originalExecution_model_iff (codecFuel : Nat) (blob : Bytes) (fid : Nat)
    (format : ContractFormat) (bytes : Bytes) (bindings : List ContractBinding)
    (m : SemR.Module) (f : Func) (sig : FuncTy)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig)
    (inhabited : ∃ inputs, checkSig m.pointerBits inputs sig.params = .ok ()) :
    originalExecution codecFuel blob fid format bytes bindings ↔
      ∀ inputs depth, checkSig m.pointerBits inputs sig.params = .ok () →
        ∃ fuel returned, runFunction m fid inputs fuel depth = .ret returned ∧
          originalContractHolds codecFuel m format bytes bindings inputs returned := by
  constructor
  · intro claim inputs depth valid
    obtain ⟨fuel, returned, ran, holds⟩ := originalExecution_at codecFuel blob fid
      format bytes bindings claim m f sig decoded found signature inputs depth valid
    exact ⟨fuel, returned, by simpa only [runBlob, decoded, Except.ok.injEq] using ran, holds⟩
  · intro executes
    refine ⟨m, f, sig, decoded, found, signature, inhabited, ?_⟩
    intro inputs depth valid
    obtain ⟨fuel, returned, ran, holds⟩ := executes inputs depth valid
    exact ⟨fuel, returned, by simpa only [runBlob, decoded] using congrArg Except.ok ran, holds⟩

/-- A specialized mathematical input domain suffices only when it covers ALL
    signature-valid values. Neither an empty domain nor bounded sampling works. -/
theorem originalExecution_of_surjective {α : Type} (codecFuel : Nat)
    (blob : Bytes) (fid : Nat) (format : ContractFormat) (bytes : Bytes)
    (bindings : List ContractBinding) (m : SemR.Module) (f : Func) (sig : FuncTy)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig)
    (encode : α → List Val) (witness : α)
    (typed : ∀ a, checkSig m.pointerBits (encode a) sig.params = .ok ())
    (covers : ∀ inputs, checkSig m.pointerBits inputs sig.params = .ok () →
      ∃ a, encode a = inputs)
    (executes : ∀ a depth, ∃ fuel returned,
      runBlob blob fid (encode a) fuel depth = .ok (.ret returned) ∧
        originalContractHolds codecFuel m format bytes bindings (encode a) returned) :
    originalExecution codecFuel blob fid format bytes bindings := by
  refine ⟨m, f, sig, decoded, found, signature, ⟨encode witness, typed witness⟩, ?_⟩
  intro inputs depth valid
  obtain ⟨a, same⟩ := covers inputs valid
  rw [← same]
  exact executes a depth

theorem signatureNil (pointerBits : Nat) (inputs : List Val) :
    checkSig pointerBits inputs [] = .ok () ↔ inputs = [] := by
  cases inputs <;> simp [checkSig, tyR]

/-- Constructor-exact domain surjection, composable with the remaining signature. -/
theorem signatureBool (pointerBits : Nat) (inputs : List Val) (types : List Ty) :
    checkSig pointerBits inputs (.bool :: types) = .ok () ↔
      ∃ value tail, inputs = .bool value :: tail ∧
        checkSig pointerBits tail types = .ok () := by
  cases inputs with
  | nil => simp [checkSig, tyR]
  | cons value tail =>
      cases value <;>
        simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, tyR, ubR, ok_bind, stop_bind]

      case bool b => cases b <;> simp

theorem signatureU8 (pointerBits : Nat) (inputs : List Val) (types : List Ty) :
    checkSig pointerBits inputs (.int .u8 :: types) = .ok () ↔
      ∃ value tail, inputs = .int .u8 value :: tail ∧ value < modulus 8 ∧
        checkSig pointerBits tail types = .ok () := by
  cases inputs with
  | nil => simp [checkSig, tyR]
  | cons value tail =>
      cases value <;>
        try { simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, tyR, ubR, ok_bind, stop_bind] }
      case int ty raw =>
        cases ty <;>
          simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, IntTy.code,
            IntTy.bits, tyR, ok_bind]
        by_cases bounded : raw < modulus 8 <;> simp [bounded, ok_bind, stop_bind]
        constructor
        · intro valid
          exact ⟨raw, tail, ⟨rfl, rfl⟩, bounded, valid⟩
        · rintro ⟨value, rest, ⟨same, tailSame⟩, _, valid⟩
          cases same
          cases tailSame
          exact valid

theorem signatureU32 (pointerBits : Nat) (inputs : List Val) (types : List Ty) :
    checkSig pointerBits inputs (.int .u32 :: types) = .ok () ↔
      ∃ value tail, inputs = .int .u32 value :: tail ∧ value < modulus 32 ∧
        checkSig pointerBits tail types = .ok () := by
  cases inputs with
  | nil => simp [checkSig, tyR]
  | cons value tail =>
      cases value <;>
        try { simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, tyR, ubR, ok_bind, stop_bind] }
      case int ty raw =>
        cases ty <;>
          simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, IntTy.code,
            IntTy.bits, tyR, ok_bind]
        by_cases bounded : raw < modulus 32 <;> simp [bounded, ok_bind, stop_bind]
        constructor
        · intro valid
          exact ⟨raw, tail, ⟨rfl, rfl⟩, bounded, valid⟩
        · rintro ⟨value, rest, ⟨same, tailSame⟩, _, valid⟩
          cases same
          cases tailSame
          exact valid

theorem signatureU64 (pointerBits : Nat) (inputs : List Val) (types : List Ty) :
    checkSig pointerBits inputs (.int .u64 :: types) = .ok () ↔
      ∃ value tail, inputs = .int .u64 value :: tail ∧ value < modulus 64 ∧
        checkSig pointerBits tail types = .ok () := by
  cases inputs with
  | nil => simp [checkSig, tyR]
  | cons value tail =>
      cases value <;>
        try { simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, tyR, ubR, ok_bind, stop_bind] }
      case int ty raw =>
        cases ty <;>
          simp [checkSig, rejectPoison, expectTy, Val.ty, Ty.beq, IntTy.code,
            IntTy.bits, tyR, ok_bind]
        by_cases bounded : raw < modulus 64 <;> simp [bounded, ok_bind, stop_bind]
        constructor
        · intro valid
          exact ⟨raw, tail, ⟨rfl, rfl⟩, bounded, valid⟩
        · rintro ⟨value, rest, ⟨same, tailSame⟩, _, valid⟩
          cases same
          cases tailSame
          exact valid

end SemRNativeExecutionClaim

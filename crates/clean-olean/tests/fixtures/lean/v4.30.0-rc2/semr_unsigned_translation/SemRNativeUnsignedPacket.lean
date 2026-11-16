/- Actual complete native packet: all U64 inputs, exact emitted VC, original return. -/
import SemRNativeUnsignedPacketData
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace SemRNativeUnsignedPacket
open SemR SemRBooleanClaim SemRNativeExecutionClaim SemRNativeUnsignedTranslation

def vcEnv (c : Bool) (a b : Nat) : TypedEnv :=
  ([([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,48],c)],
   [([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,49],Int.ofNat a),
    ([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,50],Int.ofNat b)])
def postEnv (c : Bool) (a b r : Nat) : TypedEnv :=
  ([([99],c)], [([120],Int.ofNat a),([121],Int.ofNat b),([114],Int.ofNat r)])

theorem found : model.functions.find? (fun f => f.id == 0) = some func := rfl
theorem sig_found : nth? model.funcTys func.ty = some signature := rfl

theorem input_domain (vs : List Val) :
    checkSig model.pointerBits vs signature.params = .ok () ↔
      ∃ c a b, vs = inputs c a b ∧ a < modulus 64 ∧ b < modulus 64 := by
  change checkSig 64 vs [.bool, .int .u64, .int .u64] = .ok () ↔ _
  constructor
  · intro valid
    obtain ⟨c, rest, same, hv⟩ := (signatureBool 64 vs [.int .u64, .int .u64]).mp valid
    obtain ⟨a, rest', same', ha, hv'⟩ := (signatureU64 64 rest [.int .u64]).mp hv
    obtain ⟨b, tail, same'', hb, hv''⟩ := (signatureU64 64 rest' []).mp hv'
    have empty := (signatureNil 64 tail).mp hv''
    subst tail; subst rest'; subst rest; subst vs
    exact ⟨c,a,b,rfl,ha,hb⟩
  · rintro ⟨c,a,b,rfl,ha,hb⟩
    apply (signatureBool 64 _ _).mpr
    refine ⟨c,_,rfl,?_⟩
    apply (signatureU64 64 _ _).mpr
    refine ⟨a,_,rfl,ha,?_⟩
    exact (signatureU64 64 _ _).mpr ⟨b,[],rfl,hb,rfl⟩

theorem typed_vc (c : Bool) (a b : Nat) (ha : a < modulus 64) (hb : b < modulus 64) :
    contractTypedEnv model vcBindings (inputs c a b) [] = some (vcEnv c a b) := by
  simp [contractTypedEnv, vcBindings, inputs, boundValue, expectTy, Val.ty, Ty.beq,
    rejectPoison, IntTy.signed, IntTy.bits, ha, hb, typedEnv, vcEnv, tyR, ubR, ok_bind] <;> rfl

theorem typed_post (c : Bool) (a b r : Nat) (ha : a < modulus 64)
    (hb : b < modulus 64) (hr : r < modulus 64) :
    contractTypedEnv model bindings (inputs c a b) [.int .u64 r] = some (postEnv c a b r) := by
  simp [contractTypedEnv, bindings, inputs, boundValue, expectTy, Val.ty, Ty.beq,
    rejectPoison, IntTy.signed, IntTy.bits, ha, hb, hr, typedEnv, postEnv, tyR, ubR, ok_bind] <;> rfl

/-- Computational normalization of the existing decoder, not another parser. -/
def maxTree : Nat → IntExpr
  | 0 => .literal 2
  | n + 1 => .binary .mul (maxTree n) (maxTree n)
def maximum : IntExpr := .binary .sub (maxTree 6) (.literal 1)
def cx : SemRBooleanClaim.Expr := .var [95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,48]
def ax : IntExpr := .var [95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,49]
def bx : IntExpr := .var [95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,50]
def domainExpr (v : IntExpr) : SemRBooleanClaim.Expr := .binary .and
  (.intCompare .le (.literal 0) v) (.intCompare .le v maximum)
def selectedPost (r : IntExpr) : SemRBooleanClaim.Expr := .binary .and
  (.binary .implies cx (.intCompare .eq r ax))
  (.binary .implies (.not cx) (.intCompare .eq r bx))
theorem vc_shape : vcExpression = .binary .implies
    (.binary .and (.binary .and (.literal true) (domainExpr ax)) (domainExpr bx))
    (.binary .and (.binary .implies cx (selectedPost ax))
      (.binary .implies (.not cx) (selectedPost bx))) := rfl

theorem post_shape : postExpression = .binary .and
    (.binary .implies (.var [99]) (.intCompare .eq (.var [114]) (.var [120])))
    (.binary .implies (.not (.var [99])) (.intCompare .eq (.var [114]) (.var [121]))) := rfl

theorem vc_eval (c : Bool) (a b : Nat) :
    checkedTypedJson 4096 vcBytes vcJson (vcEnv c a b) = some true := by
  rw [checked_typed_json_eval 4096 vcBytes vcJson vcExpression _ vc_encoded vc_decoded, vc_shape]
  cases c <;> simp [domainExpr, selectedPost, cx, ax, bx, maximum, maxTree,
    evalTyped, vcEnv, lookup, IntExpr.eval, IntBinary.apply, IntComparison.apply, Binary.apply]

theorem post_eval (c : Bool) (a b r : Nat) :
    checkedTypedJson 4096 postBytes postJson (postEnv c a b r) =
      some (((!c) || ((Int.ofNat r) == (Int.ofNat a))) && (c || ((Int.ofNat r) == (Int.ofNat b)))) := by
  rw [checked_typed_json_eval 4096 postBytes postJson postExpression _ post_encoded post_decoded, post_shape]
  cases c <;> simp [evalTyped, postEnv, lookup, IntExpr.eval, IntComparison.apply, Binary.apply]

theorem started (c : Bool) (a b depth : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) :
    start model 0 (inputs c a b) depth = .ok (initial c a b depth) := by
  have valid := (input_domain (inputs c a b)).mpr ⟨c,a,b,rfl,ha,hb⟩
  change checkSig 64 (inputs c a b) [.bool, .int .u64, .int .u64] = .ok () at valid
  change (do
    checkSig 64 (inputs c a b) [.bool, .int .u64, .int .u64]
    let env ← bindParams 64 [] [(0,.bool),(1,.int .u64),(2,.int .u64)] (inputs c a b)
    pure { fn := func, sig := signature, block := block, pc := 0, env := env, depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty } : R Core) =
    .ok (initial c a b depth)
  rw [valid]
  simp [initial, inputs, bindParams, expectTy, Val.ty, Ty.beq, IntTy.bits, ha, hb, ok_bind] <;> rfl

theorem body_run (c : Bool) (a b depth : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) :
    run model 2 (initial c a b depth) = .ret [.int .u64 (if c then a else b)] := by
  apply select_return_run model (initial c a b depth) 3 0 1 2 .u64 c a b
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ha
  · exact hb
  · rfl
  · rfl

def TranslationClaim : Prop := originalWpTranslation 4096 moduleBytes 0 .typedJson postBytes bindings
  vcBytes vcJson vcBindings

theorem translation : TranslationClaim := by
  refine ⟨vc_encoded, ⟨vcExpression,vc_decoded⟩, model,func,signature,decoded,found,sig_found,
    ⟨inputs false 0 0,rfl⟩,?_⟩
  intro vs depth valid
  obtain ⟨c,a,b,rfl,ha,hb⟩ := (input_domain vs).mp valid
  refine ⟨vcEnv c a b,true,typed_vc c a b ha hb,vc_eval c a b,?_⟩
  intro _actualVc
  refine ⟨2,[.int .u64 (if c then a else b)],?_,?_⟩
  · simp only [runBlob, decoded, runFunction, started c a b depth ha hb]
    exact congrArg Except.ok (body_run c a b depth ha hb)
  · have hr : (if c then a else b) < modulus 64 := by cases c <;> simp_all
    refine ⟨postEnv c a b (if c then a else b),typed_post c a b _ ha hb hr,postJson,?_⟩
    rw [post_eval]
    cases c <;> simp

theorem translation_certificate : TranslationCertificate 4096 moduleBytes 0 .typedJson postBytes bindings
    vcBytes vcJson vcBindings := ⟨translation⟩

/-- End-to-end use of the proved translation and exact emitted VC validity.
    Neither this step nor its caller supplies a translation-soundness premise. -/
theorem original_execution : originalExecution 4096 moduleBytes 0 .typedJson postBytes bindings := by
  obtain ⟨_,_,m,f,sig,hm,hf,hs,inhabited,all⟩ := translation
  rw [decoded] at hm
  cases hm
  rw [found] at hf
  cases hf
  rw [sig_found] at hs
  cases hs
  refine ⟨model,func,signature,decoded,found,sig_found,inhabited,?_⟩
  intro vs depth valid
  obtain ⟨env,value,bound,checked,sound⟩ := all vs depth valid
  obtain ⟨c,a,b,rfl,ha,hb⟩ := (input_domain vs).mp valid
  rw [typed_vc c a b ha hb] at bound
  cases bound
  rw [vc_eval] at checked
  cases checked
  exact sound rfl

/-- The upper half of U64 is interpreted as its full unsigned residue. -/
theorem full_u64_return : runBlob moduleBytes 0 (inputs false 0 18446744073709551615) 2 0 =
    .ok (.ret [.int .u64 18446744073709551615]) := by
  simp only [runBlob,decoded,runFunction,started false 0 18446744073709551615 0 (by decide) (by decide)]
  exact congrArg Except.ok (body_run false 0 18446744073709551615 0 (by decide) (by decide))

/-- A wrong result-to-input binding is inhabited and well typed; its original
    contract really evaluates false at the full-width counterexample. -/
theorem full_u64_wrong_binding :
    contractTypedEnv model wrongBindings (inputs false 0 18446744073709551615)
      [.int .u64 18446744073709551615] = some (postEnv false 0 18446744073709551615 0) ∧
    checkedTypedJson 4096 postBytes postJson (postEnv false 0 18446744073709551615 0) = some false := by
  constructor
  · rfl
  · rw [post_eval]
    rfl

theorem full_u64_swapped_return :
    runBlob swappedBytes 0 (inputs false 0 18446744073709551615) 2 0 = .ok (.ret [.int .u64 0]) := rfl

theorem full_u64_wrong_return :
    runBlob wrongReturnBytes 0 (inputs false 0 18446744073709551615) 2 0 = .ok (.ret [.int .u64 0]) := rfl

end SemRNativeUnsignedPacket

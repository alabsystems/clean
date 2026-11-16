/- A checked original-byte family for the canonical unsigned Select/Return rule.
   The hypotheses are syntax/codec facts about the actual question, never a
   translation-soundness assumption or source/ABI authority. -/
import SemRNativeUnsignedTranslation
namespace SemRNativeUnsignedFamily
open SemR SemRUnsignedSelect SemRBooleanClaim SemRNativeExecutionClaim SemRNativeUnsignedTranslation

def inputs (c : Bool) (a b : Nat) : List Val := [.bool c, .int .u64 a, .int .u64 b]
def entry (id : Nat) : Block :=
  { id := id,
    params := [(0,.bool),(1,.int .u64),(2,.int .u64)],
    body := [selectUInt 3 0 1 2 .u64, returnUInt 3] }
def core (f : Func) (sig : FuncTy) (c : Bool) (a b depth : Nat) : Core :=
  { fn := f, sig := sig, block := entry f.entry, pc := 0,
    env := [(2,.int .u64 b),(1,.int .u64 a),(0,.bool c)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }
def bindings : List ContractBinding := [([99],.param 0,.bool),([120],.param 1,.int .u64),
  ([121],.param 2,.int .u64),([114],.result 0,.int .u64)]
def vcBindings : List ContractBinding :=
  [([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,48],.param 0,.bool),
   ([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,49],.param 1,.int .u64),
   ([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,50],.param 2,.int .u64)]
def vcEnv (c : Bool) (a b : Nat) : TypedEnv :=
  ([([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,48],c)],
   [([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,49],Int.ofNat a),
    ([95,95,116,114,117,115,116,95,119,112,95,98,111,100,121,95,118,50],Int.ofNat b)])
def postEnv (c : Bool) (a b r : Nat) : TypedEnv :=
  ([([99],c)],[([120],Int.ofNat a),([121],Int.ofNat b),([114],Int.ofNat r)])
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
def vcExpression : SemRBooleanClaim.Expr := .binary .implies
  (.binary .and (.binary .and (.literal true) (domainExpr ax)) (domainExpr bx))
  (.binary .and (.binary .implies cx (selectedPost ax))
    (.binary .implies (.not cx) (selectedPost bx)))
def postExpression : SemRBooleanClaim.Expr := .binary .and
  (.binary .implies (.var [99]) (.intCompare .eq (.var [114]) (.var [120])))
  (.binary .implies (.not (.var [99])) (.intCompare .eq (.var [114]) (.var [121])))

theorem input_domain (m : Module) (sig : FuncTy)
    (pointer : m.pointerBits = 64) (params : sig.params = [.bool,.int .u64,.int .u64])
    (vs : List Val) : checkSig m.pointerBits vs sig.params = .ok () ↔
      ∃ c a b, vs = inputs c a b ∧ a < modulus 64 ∧ b < modulus 64 := by
  rw [pointer,params]
  constructor
  · intro valid
    obtain ⟨c, rest, same, hv⟩ := (signatureBool 64 vs [.int .u64,.int .u64]).mp valid
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

theorem typed_vc (m : Module) (pointer : m.pointerBits = 64)
    (c : Bool) (a b : Nat) (ha : a < modulus 64) (hb : b < modulus 64) :
    contractTypedEnv m vcBindings (inputs c a b) [] = some (vcEnv c a b) := by
  simp [contractTypedEnv,vcBindings,inputs,pointer,boundValue,expectTy,Val.ty,Ty.beq,
    rejectPoison,IntTy.signed,IntTy.bits,ha,hb,typedEnv,vcEnv,tyR,ubR,ok_bind] <;> rfl

theorem typed_post (m : Module) (pointer : m.pointerBits = 64)
    (c : Bool) (a b r : Nat) (ha : a < modulus 64)
    (hb : b < modulus 64) (hr : r < modulus 64) :
    contractTypedEnv m bindings (inputs c a b) [.int .u64 r] = some (postEnv c a b r) := by
  simp [contractTypedEnv,bindings,inputs,pointer,boundValue,expectTy,Val.ty,Ty.beq,
    rejectPoison,IntTy.signed,IntTy.bits,ha,hb,hr,typedEnv,postEnv,tyR,ubR,ok_bind] <;> rfl

theorem vc_eval (bytes : Bytes) (json : Json)
    (encoded : encodeJson 4096 json = some bytes)
    (decoded : decodeClaim 4096 json = some vcExpression) (c : Bool) (a b : Nat) :
    checkedTypedJson 4096 bytes json (vcEnv c a b) = some true := by
  rw [checked_typed_json_eval 4096 bytes json vcExpression _ encoded decoded]
  cases c <;> simp [vcExpression,domainExpr,selectedPost,cx,ax,bx,maximum,maxTree,
    evalTyped,vcEnv,lookup,IntExpr.eval,IntBinary.apply,IntComparison.apply,Binary.apply]

theorem post_eval (bytes : Bytes) (json : Json)
    (encoded : encodeJson 4096 json = some bytes)
    (decoded : decodeClaim 4096 json = some postExpression) (c : Bool) (a b r : Nat) :
    checkedTypedJson 4096 bytes json (postEnv c a b r) =
      some (((!c) || ((Int.ofNat r) == (Int.ofNat a))) && (c || ((Int.ofNat r) == (Int.ofNat b)))) := by
  rw [checked_typed_json_eval 4096 bytes json postExpression _ encoded decoded]
  cases c <;> simp [postExpression,evalTyped,postEnv,lookup,IntExpr.eval,IntComparison.apply,Binary.apply]

theorem started (m : Module) (fid : Nat) (f : Func) (sig : FuncTy)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig) (pointer : m.pointerBits = 64)
    (target : m.executableTarget = true)
    (params : sig.params = [.bool,.int .u64,.int .u64]) (vararg : sig.vararg = false)
    (body : f.blocks = [entry f.entry]) (c : Bool) (a b depth : Nat)
    (ha : a < modulus 64) (hb : b < modulus 64) :
    start m fid (inputs c a b) depth = .ok (core f sig c a b depth) := by
  have valid := (input_domain m sig pointer params (inputs c a b)).mpr ⟨c,a,b,rfl,ha,hb⟩
  simp only [start,found,signature,body,List.isEmpty_cons,vararg,target,Bool.not_true,
    Bool.false_eq_true,ite_false,findBlock,entry,beq_self_eq_true,List.find?,ite_true]
  rw [valid]
  simp [core,entry,inputs,bindParams,pointer,expectTy,Val.ty,Ty.beq,IntTy.bits,ha,hb,ok_bind] <;> rfl

theorem body_run (m : Module) (f : Func) (sig : FuncTy)
    (pointer : m.pointerBits = 64) (returns : sig.returns = [.int .u64])
    (c : Bool) (a b depth : Nat) (ha : a < modulus 64) (hb : b < modulus 64) :
    run m 2 (core f sig c a b depth) = .ret [.int .u64 (if c then a else b)] := by
  apply select_return_run m (core f sig c a b depth) 3 0 1 2 .u64 c a b
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [pointer] using ha
  · simpa [pointer] using hb
  · rfl
  · exact returns

/-- Every premise is a codec/shape check of the actual original question.
    Arbitrary admitted metadata and sibling tables remain in the indexed blob. -/
theorem select_return_original_translation (blob : Bytes) (m : Module)
    (fid : Nat) (f : Func) (sig : FuncTy)
    (postBytes vcBytes : Bytes) (postJson vcJson : Json)
    (decoded : decode blob = .ok m)
    (found : m.functions.find? (fun candidate => candidate.id == fid) = some f)
    (signature : nth? m.funcTys f.ty = some sig) (pointer : m.pointerBits = 64)
    (target : m.executableTarget = true)
    (params : sig.params = [.bool,.int .u64,.int .u64])
    (returns : sig.returns = [.int .u64]) (vararg : sig.vararg = false)
    (body : f.blocks = [entry f.entry])
    (postEncoded : encodeJson 4096 postJson = some postBytes)
    (postDecoded : decodeClaim 4096 postJson = some postExpression)
    (vcEncoded : encodeJson 4096 vcJson = some vcBytes)
    (vcDecoded : decodeClaim 4096 vcJson = some vcExpression) :
    TranslationCertificate 4096 blob fid .typedJson postBytes bindings vcBytes vcJson vcBindings := by
  constructor
  refine ⟨vcEncoded,⟨vcExpression,vcDecoded⟩,m,f,sig,decoded,found,signature,
    ⟨inputs false 0 0, (input_domain m sig pointer params _).mpr ⟨false,0,0,rfl,by decide,by decide⟩⟩,?_⟩
  intro vs depth valid
  obtain ⟨c,a,b,rfl,ha,hb⟩ := (input_domain m sig pointer params vs).mp valid
  refine ⟨vcEnv c a b,true,typed_vc m pointer c a b ha hb,
    vc_eval vcBytes vcJson vcEncoded vcDecoded c a b,?_⟩
  intro _actualVc
  refine ⟨2,[.int .u64 (if c then a else b)],?_,?_⟩
  · simp only [runBlob,decoded,runFunction,
      started m fid f sig found signature pointer target params vararg body c a b depth ha hb]
    exact congrArg Except.ok (body_run m f sig pointer returns c a b depth ha hb)
  · have hr : (if c then a else b) < modulus 64 := by cases c <;> simp_all
    refine ⟨postEnv c a b (if c then a else b),typed_post m pointer c a b _ ha hb hr,postJson,?_⟩
    rw [post_eval postBytes postJson postEncoded postDecoded]
    cases c <;> simp

end SemRNativeUnsignedFamily

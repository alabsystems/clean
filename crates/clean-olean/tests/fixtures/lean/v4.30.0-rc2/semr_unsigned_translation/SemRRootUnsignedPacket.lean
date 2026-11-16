/- Instantiate the checked family with Root's exact original/derived question. -/
import SemRRootUnsignedPacketData
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace SemRRootUnsignedPacket
open SemR SemRBooleanClaim SemRNativeExecutionClaim SemRNativeUnsignedTranslation

theorem translation_certificate : TranslationCertificate 4096 moduleBytes 0 .typedJson postBytes
    SemRNativeUnsignedFamily.bindings vcBytes vcJson SemRNativeUnsignedFamily.vcBindings :=
  SemRNativeUnsignedFamily.select_return_original_translation moduleBytes model 0 func signature
    postBytes vcBytes postJson vcJson decoded found sig_found pointer target params returns vararg body
    post_encoded post_decoded vc_encoded vc_decoded

/-- Use the actual emitted VC validity and checked translation to discharge the
    original complete-module execution goal, with every valid U64 input/depth. -/
theorem original_execution : originalExecution 4096 moduleBytes 0 .typedJson postBytes
    SemRNativeUnsignedFamily.bindings := by
  obtain ⟨_,_,m,f,sig,hm,hf,hs,inhabited,all⟩ := translation_certificate.holds
  rw [decoded] at hm
  cases hm
  rw [found] at hf
  cases hf
  rw [sig_found] at hs
  cases hs
  refine ⟨model,func,signature,decoded,found,sig_found,inhabited,?_⟩
  intro vs depth valid
  obtain ⟨env,value,bound,checked,sound⟩ := all vs depth valid
  obtain ⟨c,a,b,rfl,ha,hb⟩ := (SemRNativeUnsignedFamily.input_domain model signature pointer params vs).mp valid
  rw [SemRNativeUnsignedFamily.typed_vc model pointer c a b ha hb] at bound
  cases bound
  rw [SemRNativeUnsignedFamily.vc_eval vcBytes vcJson vc_encoded vc_decoded] at checked
  cases checked
  exact sound rfl

theorem full_u64_return : runBlob moduleBytes 0
    (SemRNativeUnsignedFamily.inputs false 0 18446744073709551615) 2 0 =
    .ok (.ret [.int .u64 18446744073709551615]) := by
  simp only [runBlob,decoded,runFunction,SemRNativeUnsignedFamily.started model 0 func signature
    found sig_found pointer target params vararg body false 0 18446744073709551615 0 (by decide) (by decide)]
  exact congrArg Except.ok (SemRNativeUnsignedFamily.body_run model func signature pointer returns
    false 0 18446744073709551615 0 (by decide) (by decide))

/-- A well-typed result/input confusion is false at an initialized full-width
    input. Its rejection is not explained by an empty or ill-typed domain. -/
def wrongBindings : List ContractBinding := [([99],.param 0,.bool),
  ([120],.param 1,.int .u64),([121],.param 2,.int .u64),([114],.param 1,.int .u64)]
theorem full_u64_wrong_binding :
    contractTypedEnv model wrongBindings (SemRNativeUnsignedFamily.inputs false 0 18446744073709551615)
      [.int .u64 18446744073709551615] =
      some (SemRNativeUnsignedFamily.postEnv false 0 18446744073709551615 0) ∧
    checkedTypedJson 4096 postBytes postJson
      (SemRNativeUnsignedFamily.postEnv false 0 18446744073709551615 0) = some false := by
  constructor
  · rfl
  · rw [SemRNativeUnsignedFamily.post_eval postBytes postJson post_encoded post_decoded]
    rfl

end SemRRootUnsignedPacket

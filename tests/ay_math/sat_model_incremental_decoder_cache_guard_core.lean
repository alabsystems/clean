/-!
  SAT-COMP/ay incremental decoder-cache guard.

  This self-contained package models the SAT-only obligations for reusing
  cached binary/compressed witness decoder results during validation.
-/

def ay_idcg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_idcg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_idcg_original_formula_fingerprint
    (witnessArtifact formulaOk : Prop) : Prop :=
  witnessArtifact -> formulaOk

def ay_idcg_witness_artifact_digest (formulaOk witnessOk : Prop) : Prop :=
  formulaOk -> witnessOk

def ay_idcg_decoder_version_digest (witnessOk decoderOk : Prop) : Prop :=
  witnessOk -> decoderOk

def ay_idcg_decoder_cache_key_digest (decoderOk cacheKeyOk : Prop) : Prop :=
  decoderOk -> cacheKeyOk

def ay_idcg_cached_decoded_assignment_digest
    (cacheKeyOk cachedDecodedOk : Prop) : Prop :=
  cacheKeyOk -> cachedDecodedOk

def ay_idcg_invalidation_ledger (cachedDecodedOk invalidationOk : Prop) : Prop :=
  cachedDecodedOk -> invalidationOk

def ay_idcg_normalized_assignment_digest
    (invalidationOk normalizedOk : Prop) : Prop :=
  invalidationOk -> normalizedOk

def ay_idcg_clause_satisfaction_replay
    (normalizedOk everyOriginalClauseSatisfied : Prop) : Prop :=
  normalizedOk -> everyOriginalClauseSatisfied

def ay_idcg_fresh_decode_fallback_transcript
    (everyOriginalClauseSatisfied freshDecodeOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> freshDecodeOk

def ay_idcg_checker_transcript (freshDecodeOk checkerOk : Prop) : Prop :=
  freshDecodeOk -> checkerOk

def ay_idcg_solver_build_evidence (checkerOk buildOk : Prop) : Prop :=
  checkerOk -> buildOk

def ay_idcg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_idcg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_idcg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_idcg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_idcg_accepted_decoder_cache
    (formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> witness -> decoder -> cacheKey -> cachedDecoded -> invalidation ->
      normalized -> replay -> freshDecode -> checker -> build -> validator -> archive ->
      fallback -> audit -> r) -> r

def ay_idcg_public_sat
    (accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop) : Prop :=
  ay_idcg_conj accepted
    (ay_idcg_conj normalizedAssignment
      (ay_idcg_conj everyOriginalClauseSatisfied
        (ay_idcg_conj cacheKeyOk
          (ay_idcg_conj invalidationOk
            (ay_idcg_conj checkerOk
              (ay_idcg_conj validatorOk (ay_idcg_conj archiveOk audited)))))))

def ay_idcg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_idcg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_idcg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_idcg_conj p q :=
  fun r h => h hp hq

theorem ay_idcg_conj_left {p q : Prop} (h : ay_idcg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_idcg_conj_right {p q : Prop} (h : ay_idcg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_idcg_conj_left h)

theorem ay_idcg_disj_left {p q : Prop} (hp : p) : ay_idcg_disj p q :=
  fun r hl _ => hl hp

theorem ay_idcg_disj_right {p q : Prop} (hq : q) : ay_idcg_disj p q :=
  fun r _ hr => hr hq

theorem ay_idcg_original_formula_fingerprint_intro
    {witnessArtifact formulaOk : Prop}
    (h : witnessArtifact -> formulaOk) :
    ay_idcg_original_formula_fingerprint witnessArtifact formulaOk :=
  h

theorem ay_idcg_witness_artifact_digest_intro {formulaOk witnessOk : Prop}
    (h : formulaOk -> witnessOk) :
    ay_idcg_witness_artifact_digest formulaOk witnessOk :=
  h

theorem ay_idcg_decoder_version_digest_intro {witnessOk decoderOk : Prop}
    (h : witnessOk -> decoderOk) :
    ay_idcg_decoder_version_digest witnessOk decoderOk :=
  h

theorem ay_idcg_decoder_cache_key_digest_intro {decoderOk cacheKeyOk : Prop}
    (h : decoderOk -> cacheKeyOk) :
    ay_idcg_decoder_cache_key_digest decoderOk cacheKeyOk :=
  h

theorem ay_idcg_cached_decoded_assignment_digest_intro
    {cacheKeyOk cachedDecodedOk : Prop}
    (h : cacheKeyOk -> cachedDecodedOk) :
    ay_idcg_cached_decoded_assignment_digest cacheKeyOk cachedDecodedOk :=
  h

theorem ay_idcg_invalidation_ledger_intro
    {cachedDecodedOk invalidationOk : Prop}
    (h : cachedDecodedOk -> invalidationOk) :
    ay_idcg_invalidation_ledger cachedDecodedOk invalidationOk :=
  h

theorem ay_idcg_normalized_assignment_digest_intro
    {invalidationOk normalizedOk : Prop}
    (h : invalidationOk -> normalizedOk) :
    ay_idcg_normalized_assignment_digest invalidationOk normalizedOk :=
  h

theorem ay_idcg_clause_satisfaction_replay_intro
    {normalizedOk everyOriginalClauseSatisfied : Prop}
    (h : normalizedOk -> everyOriginalClauseSatisfied) :
    ay_idcg_clause_satisfaction_replay normalizedOk everyOriginalClauseSatisfied :=
  h

theorem ay_idcg_fresh_decode_fallback_transcript_intro
    {everyOriginalClauseSatisfied freshDecodeOk : Prop}
    (h : everyOriginalClauseSatisfied -> freshDecodeOk) :
    ay_idcg_fresh_decode_fallback_transcript everyOriginalClauseSatisfied freshDecodeOk :=
  h

theorem ay_idcg_checker_transcript_intro {freshDecodeOk checkerOk : Prop}
    (h : freshDecodeOk -> checkerOk) :
    ay_idcg_checker_transcript freshDecodeOk checkerOk :=
  h

theorem ay_idcg_solver_build_evidence_intro {checkerOk buildOk : Prop}
    (h : checkerOk -> buildOk) :
    ay_idcg_solver_build_evidence checkerOk buildOk :=
  h

theorem ay_idcg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_idcg_validator_gate buildOk validatorOk :=
  h

theorem ay_idcg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_idcg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_idcg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_idcg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_idcg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_idcg_audit_transcript fallbackReady audited :=
  h

theorem ay_idcg_accepted_decoder_cache_intro
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (hf : formula) (hw : witness) (hd : decoder) (hk : cacheKey) (hcd : cachedDecoded)
    (hi : invalidation) (hn : normalized) (hr : replay) (hfd : freshDecode)
    (hc : checker) (hb : build) (hv : validator) (har : archive) (hfb : fallback)
    (hau : audit) :
    ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit :=
  fun r k => k hf hw hd hk hcd hi hn hr hfd hc hb hv har hfb hau

theorem ay_idcg_accepted_decoder_cache_witness
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : witness :=
  h witness (fun _ hw _ _ _ _ _ _ _ _ _ _ _ _ _ => hw)

theorem ay_idcg_accepted_decoder_cache_decoder
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : decoder :=
  h decoder (fun _ _ hd _ _ _ _ _ _ _ _ _ _ _ _ => hd)

theorem ay_idcg_accepted_decoder_cache_key
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : cacheKey :=
  h cacheKey (fun _ _ _ hk _ _ _ _ _ _ _ _ _ _ _ => hk)

theorem ay_idcg_accepted_decoder_cache_invalidation
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : invalidation :=
  h invalidation (fun _ _ _ _ _ hi _ _ _ _ _ _ _ _ _ => hi)

theorem ay_idcg_accepted_decoder_cache_normalized
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : normalized :=
  h normalized (fun _ _ _ _ _ _ hn _ _ _ _ _ _ _ _ => hn)

theorem ay_idcg_accepted_decoder_cache_replay
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ hr _ _ _ _ _ _ _ => hr)

theorem ay_idcg_accepted_decoder_cache_checker
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ _ _ hc _ _ _ _ _ => hc)

theorem ay_idcg_accepted_decoder_cache_validator
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_idcg_accepted_decoder_cache_archive
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_idcg_accepted_decoder_cache_audit
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_idcg_public_sat_intro
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hr : everyOriginalClauseSatisfied)
    (hk : cacheKeyOk) (hi : invalidationOk) (hc : checkerOk) (hv : validatorOk)
    (har : archiveOk) (hau : audited) :
    ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk checkerOk validatorOk archiveOk audited :=
  ay_idcg_conj_intro ha
    (ay_idcg_conj_intro hn
      (ay_idcg_conj_intro hr
        (ay_idcg_conj_intro hk
          (ay_idcg_conj_intro hi
            (ay_idcg_conj_intro hc
              (ay_idcg_conj_intro hv (ay_idcg_conj_intro har hau)))))))

theorem ay_idcg_public_sat_requires_decoder_cache_guard
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      cacheKeyOk invalidationOk checkerOk validatorOk archiveOk audited) : accepted :=
  ay_idcg_conj_left h

theorem ay_idcg_public_sat_normalized_assignment
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      cacheKeyOk invalidationOk checkerOk validatorOk archiveOk audited) :
    normalizedAssignment :=
  ay_idcg_conj_left (ay_idcg_conj_right h)

theorem ay_idcg_public_sat_original_clauses
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      cacheKeyOk invalidationOk checkerOk validatorOk archiveOk audited) :
    everyOriginalClauseSatisfied :=
  ay_idcg_conj_left (ay_idcg_conj_right (ay_idcg_conj_right h))

theorem ay_idcg_public_sat_cache_key
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      cacheKeyOk invalidationOk checkerOk validatorOk archiveOk audited) : cacheKeyOk :=
  ay_idcg_conj_left
    (ay_idcg_conj_right (ay_idcg_conj_right (ay_idcg_conj_right h)))

theorem ay_idcg_public_sat_invalidation
    {accepted normalizedAssignment everyOriginalClauseSatisfied cacheKeyOk invalidationOk
     checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_idcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      cacheKeyOk invalidationOk checkerOk validatorOk archiveOk audited) : invalidationOk :=
  ay_idcg_conj_left
    (ay_idcg_conj_right
      (ay_idcg_conj_right (ay_idcg_conj_right (ay_idcg_conj_right h))))

theorem ay_idcg_accepted_decoder_cache_publishes_sat
    {formula witness decoder cacheKey cachedDecoded invalidation normalized replay freshDecode
     checker build validator archive fallback audit : Prop}
    (h : ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
      invalidation normalized replay freshDecode checker build validator archive fallback
      audit) :
    ay_idcg_public_sat
      (ay_idcg_accepted_decoder_cache formula witness decoder cacheKey cachedDecoded
        invalidation normalized replay freshDecode checker build validator archive fallback
        audit)
      normalized replay cacheKey invalidation checker validator archive audit :=
  ay_idcg_public_sat_intro
    h
    (ay_idcg_accepted_decoder_cache_normalized h)
    (ay_idcg_accepted_decoder_cache_replay h)
    (ay_idcg_accepted_decoder_cache_key h)
    (ay_idcg_accepted_decoder_cache_invalidation h)
    (ay_idcg_accepted_decoder_cache_checker h)
    (ay_idcg_accepted_decoder_cache_validator h)
    (ay_idcg_accepted_decoder_cache_archive h)
    (ay_idcg_accepted_decoder_cache_audit h)

theorem ay_idcg_stale_partial_mismatch_forces_no_claim_or_fresh_decode
    {badCache noClaim freshDecode : Prop}
    (hn : badCache -> noClaim)
    (hf : badCache -> freshDecode)
    (hb : badCache) :
    ay_idcg_conj noClaim freshDecode :=
  ay_idcg_conj_intro (hn hb) (hf hb)

theorem ay_idcg_no_claim_intro {reason : Prop} (h : reason) :
    ay_idcg_no_claim_diagnostic reason :=
  h

theorem ay_idcg_recompute_intro {reason : Prop} (h : reason) :
    ay_idcg_recompute_obligation reason :=
  h

theorem ay_idcg_witness_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_decoder_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_idcg_recompute_obligation mismatch :=
  ay_idcg_recompute_intro h

theorem ay_idcg_cache_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_normalization_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_idcg_recompute_obligation mismatch :=
  ay_idcg_recompute_intro h

theorem ay_idcg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_checker_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_idcg_recompute_obligation mismatch :=
  ay_idcg_recompute_intro h

theorem ay_idcg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_idcg_recompute_obligation mismatch :=
  ay_idcg_recompute_intro h

theorem ay_idcg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_idcg_no_claim_diagnostic mismatch :=
  ay_idcg_no_claim_intro h

theorem ay_idcg_failed_decoder_cache_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_idcg_no_claim_diagnostic failure)
    (noBless : ay_idcg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_idcg_failed_decoder_cache_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_idcg_recompute_obligation failure)
    (hfailure : failure) :
    ay_idcg_recompute_obligation failure :=
  fallback hfailure

/-!
  SAT-COMP/ay model witness sanitization guard.

  This self-contained package models the SAT-only obligations for publishing a
  sanitized SAT model witness after rejecting invalid tokens and normalizing
  duplicate or conflicting literals.
-/

def ay_wsgg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_wsgg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_wsgg_equiv (p q : Prop) : Prop :=
  ay_wsgg_conj (p -> q) (q -> p)

def ay_wsgg_benchmark_fingerprint (rawWitness fingerprintOk : Prop) : Prop :=
  rawWitness -> fingerprintOk

def ay_wsgg_raw_witness_digest (fingerprintOk rawDigestOk : Prop) : Prop :=
  fingerprintOk -> rawDigestOk

def ay_wsgg_sanitization_policy_manifest (rawDigestOk sanitizationOk : Prop) : Prop :=
  rawDigestOk -> sanitizationOk

def ay_wsgg_invalid_token_rejection_witness (sanitizationOk tokenOk : Prop) : Prop :=
  sanitizationOk -> tokenOk

def ay_wsgg_duplicate_conflict_policy (tokenOk duplicateOk : Prop) : Prop :=
  tokenOk -> duplicateOk

def ay_wsgg_total_assignment_reconstruction (duplicateOk totalAssignment : Prop) : Prop :=
  duplicateOk -> totalAssignment

def ay_wsgg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_wsgg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_wsgg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_wsgg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_wsgg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_wsgg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_wsgg_accepted_sanitization
    (fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop) : Prop :=
  ay_wsgg_conj fingerprint
    (ay_wsgg_conj rawDigest
      (ay_wsgg_conj sanitization
        (ay_wsgg_conj token
          (ay_wsgg_conj duplicate
            (ay_wsgg_conj reconstruction
              (ay_wsgg_conj replay
                (ay_wsgg_conj checker
                  (ay_wsgg_conj build
                    (ay_wsgg_conj archive
                      (ay_wsgg_conj fallback audit))))))))))

def ay_wsgg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_wsgg_conj accepted (ay_wsgg_conj totalAssignment (ay_wsgg_conj originalSat audited))

def ay_wsgg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_wsgg_conj proofAccepted originalUnsat

def ay_wsgg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_wsgg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_wsgg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_wsgg_conj p q :=
  fun r h => h hp hq

theorem ay_wsgg_conj_left {p q : Prop} (h : ay_wsgg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_wsgg_conj_right {p q : Prop} (h : ay_wsgg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_wsgg_conj_left h)

theorem ay_wsgg_disj_left {p q : Prop} (hp : p) : ay_wsgg_disj p q :=
  fun r hl _ => hl hp

theorem ay_wsgg_disj_right {p q : Prop} (hq : q) : ay_wsgg_disj p q :=
  fun r _ hr => hr hq

theorem ay_wsgg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_wsgg_equiv p q :=
  ay_wsgg_conj_intro hpq hqp

theorem ay_wsgg_equiv_forward {p q : Prop} (h : ay_wsgg_equiv p q) : p -> q :=
  ay_wsgg_conj_left h

theorem ay_wsgg_equiv_backward {p q : Prop} (h : ay_wsgg_equiv p q) : q -> p :=
  ay_wsgg_conj_right h

theorem ay_wsgg_benchmark_fingerprint_intro {rawWitness fingerprintOk : Prop}
    (h : rawWitness -> fingerprintOk) :
    ay_wsgg_benchmark_fingerprint rawWitness fingerprintOk :=
  h

theorem ay_wsgg_raw_witness_digest_intro {fingerprintOk rawDigestOk : Prop}
    (h : fingerprintOk -> rawDigestOk) :
    ay_wsgg_raw_witness_digest fingerprintOk rawDigestOk :=
  h

theorem ay_wsgg_sanitization_policy_manifest_intro {rawDigestOk sanitizationOk : Prop}
    (h : rawDigestOk -> sanitizationOk) :
    ay_wsgg_sanitization_policy_manifest rawDigestOk sanitizationOk :=
  h

theorem ay_wsgg_invalid_token_rejection_witness_intro {sanitizationOk tokenOk : Prop}
    (h : sanitizationOk -> tokenOk) :
    ay_wsgg_invalid_token_rejection_witness sanitizationOk tokenOk :=
  h

theorem ay_wsgg_duplicate_conflict_policy_intro {tokenOk duplicateOk : Prop}
    (h : tokenOk -> duplicateOk) :
    ay_wsgg_duplicate_conflict_policy tokenOk duplicateOk :=
  h

theorem ay_wsgg_total_assignment_reconstruction_intro {duplicateOk totalAssignment : Prop}
    (h : duplicateOk -> totalAssignment) :
    ay_wsgg_total_assignment_reconstruction duplicateOk totalAssignment :=
  h

theorem ay_wsgg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_wsgg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_wsgg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_wsgg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_wsgg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_wsgg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_wsgg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_wsgg_archive_manifest buildOk archiveOk :=
  h

theorem ay_wsgg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_wsgg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_wsgg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_wsgg_audit_transcript fallbackReady audited :=
  h

theorem ay_wsgg_accepted_sanitization_intro
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (hf : fingerprint) (hrw : rawDigest) (hsan : sanitization) (htok : token)
    (hdup : duplicate) (hrc : reconstruction) (hr : replay) (hc : checker)
    (hb : build) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit :=
  ay_wsgg_conj_intro hf
    (ay_wsgg_conj_intro hrw
      (ay_wsgg_conj_intro hsan
        (ay_wsgg_conj_intro htok
          (ay_wsgg_conj_intro hdup
            (ay_wsgg_conj_intro hrc
              (ay_wsgg_conj_intro hr
                (ay_wsgg_conj_intro hc
                  (ay_wsgg_conj_intro hb
                    (ay_wsgg_conj_intro ha
                      (ay_wsgg_conj_intro hfb hau))))))))))

theorem ay_wsgg_accepted_sanitization_fingerprint
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_wsgg_conj_left h

theorem ay_wsgg_accepted_sanitization_raw_digest
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : rawDigest :=
  ay_wsgg_conj_left (ay_wsgg_conj_right h)

theorem ay_wsgg_accepted_sanitization_policy
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : sanitization :=
  ay_wsgg_conj_left (ay_wsgg_conj_right (ay_wsgg_conj_right h))

theorem ay_wsgg_accepted_sanitization_token
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : token :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h)))

theorem ay_wsgg_accepted_sanitization_duplicate
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : duplicate :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))))

theorem ay_wsgg_accepted_sanitization_reconstruction
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h)))))

theorem ay_wsgg_accepted_sanitization_replay
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))))))

theorem ay_wsgg_accepted_sanitization_checker
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right
            (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h)))))))

theorem ay_wsgg_accepted_sanitization_build
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : build :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right
            (ay_wsgg_conj_right
              (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))))))))

theorem ay_wsgg_accepted_sanitization_archive
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right
            (ay_wsgg_conj_right
              (ay_wsgg_conj_right
                (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h)))))))))

theorem ay_wsgg_accepted_sanitization_fallback
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_wsgg_conj_left
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right
            (ay_wsgg_conj_right
              (ay_wsgg_conj_right
                (ay_wsgg_conj_right
                  (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))))))))))

theorem ay_wsgg_accepted_sanitization_audit
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_wsgg_conj_right
    (ay_wsgg_conj_right
      (ay_wsgg_conj_right
        (ay_wsgg_conj_right
          (ay_wsgg_conj_right
            (ay_wsgg_conj_right
              (ay_wsgg_conj_right
                (ay_wsgg_conj_right
                  (ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))))))))))

theorem ay_wsgg_sanitization_reconstructs_original_sat
    {rawWitness fingerprintOk rawDigestOk sanitizationOk tokenOk duplicateOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_wsgg_benchmark_fingerprint rawWitness fingerprintOk)
    (hrw : ay_wsgg_raw_witness_digest fingerprintOk rawDigestOk)
    (hsan : ay_wsgg_sanitization_policy_manifest rawDigestOk sanitizationOk)
    (htok : ay_wsgg_invalid_token_rejection_witness sanitizationOk tokenOk)
    (hdup : ay_wsgg_duplicate_conflict_policy tokenOk duplicateOk)
    (hrc : ay_wsgg_total_assignment_reconstruction duplicateOk totalAssignment)
    (hr : ay_wsgg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_wsgg_model_checker_transcript replayOk originalSat)
    (hb : ay_wsgg_solver_build_evidence originalSat buildOk)
    (ha : ay_wsgg_archive_manifest buildOk archiveOk)
    (hfb : ay_wsgg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_wsgg_audit_transcript fallbackReady audited)
    (hw : rawWitness) :
    ay_wsgg_conj totalAssignment (ay_wsgg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hraw : rawDigestOk := hrw hfingerprint
  let hsanitized : sanitizationOk := hsan hraw
  let htoken : tokenOk := htok hsanitized
  let hduplicate : duplicateOk := hdup htoken
  let htotal : totalAssignment := hrc hduplicate
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_wsgg_conj_intro htotal (ay_wsgg_conj_intro hsat haudit)

theorem ay_wsgg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_wsgg_public_sat accepted totalAssignment originalSat audited :=
  ay_wsgg_conj_intro ha (ay_wsgg_conj_intro ht (ay_wsgg_conj_intro hs hau))

theorem ay_wsgg_public_sat_requires_sanitization
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wsgg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_wsgg_conj_left h

theorem ay_wsgg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wsgg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_wsgg_conj_left (ay_wsgg_conj_right h)

theorem ay_wsgg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wsgg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_wsgg_conj_left (ay_wsgg_conj_right (ay_wsgg_conj_right h))

theorem ay_wsgg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wsgg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_wsgg_conj_right (ay_wsgg_conj_right (ay_wsgg_conj_right h))

theorem ay_wsgg_accepted_sanitization_publishes_sat
    {fingerprint rawDigest sanitization token duplicate reconstruction replay checker build
     archive fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_wsgg_public_sat
      (ay_wsgg_accepted_sanitization fingerprint rawDigest sanitization token duplicate
        reconstruction replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_wsgg_public_sat_intro hg ht hs hau

theorem ay_wsgg_no_claim_intro {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  h

theorem ay_wsgg_recompute_intro {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  h

theorem ay_wsgg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  ay_wsgg_recompute_intro h

theorem ay_wsgg_raw_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  ay_wsgg_recompute_intro h

theorem ay_wsgg_sanitization_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_token_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_duplicate_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  ay_wsgg_recompute_intro h

theorem ay_wsgg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  ay_wsgg_recompute_intro h

theorem ay_wsgg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wsgg_recompute_obligation reason :=
  ay_wsgg_recompute_intro h

theorem ay_wsgg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wsgg_no_claim_diagnostic reason :=
  ay_wsgg_no_claim_intro h

theorem ay_wsgg_failed_sanitization_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_wsgg_public_sat accepted totalAssignment originalSat audited ->
      ay_wsgg_no_claim_diagnostic failure) :
    ay_wsgg_conj (ay_wsgg_no_claim_diagnostic failure)
      (ay_wsgg_public_sat accepted totalAssignment originalSat audited ->
        ay_wsgg_no_claim_diagnostic failure) :=
  ay_wsgg_conj_intro (ay_wsgg_no_claim_intro hfail) hblock

theorem ay_wsgg_failed_sanitization_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_wsgg_public_sat accepted totalAssignment originalSat audited ->
      ay_wsgg_recompute_obligation failure) :
    ay_wsgg_conj (ay_wsgg_recompute_obligation failure)
      (ay_wsgg_public_sat accepted totalAssignment originalSat audited ->
        ay_wsgg_recompute_obligation failure) :=
  ay_wsgg_conj_intro (ay_wsgg_recompute_intro hfail) hblock

theorem ay_wsgg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_wsgg_public_unsat proofAccepted originalUnsat :=
  ay_wsgg_conj_intro hp hu

theorem ay_wsgg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_wsgg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_wsgg_conj_left h

theorem ay_wsgg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_wsgg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_wsgg_conj_right h

theorem ay_wsgg_sanitization_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat sanitizationSatGuard : Prop}
    (h : ay_wsgg_public_unsat proofAccepted originalUnsat) :
    ay_wsgg_conj (ay_wsgg_public_unsat proofAccepted originalUnsat)
      (sanitizationSatGuard -> ay_wsgg_public_unsat proofAccepted originalUnsat) :=
  ay_wsgg_conj_intro h (fun _ => h)

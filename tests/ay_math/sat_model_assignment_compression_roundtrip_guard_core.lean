/-!
  SAT-COMP/ay assignment-compression roundtrip guard.

  This self-contained package models the SAT-only obligations for publishing a
  compressed assignment witness after decompression and roundtrip validation.
-/

def ay_acrg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_acrg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_acrg_equiv (p q : Prop) : Prop :=
  ay_acrg_conj (p -> q) (q -> p)

def ay_acrg_benchmark_fingerprint (compressedWitness fingerprintOk : Prop) : Prop :=
  compressedWitness -> fingerprintOk

def ay_acrg_variable_domain_manifest (fingerprintOk domainOk : Prop) : Prop :=
  fingerprintOk -> domainOk

def ay_acrg_compressed_assignment_digest (domainOk compressionOk : Prop) : Prop :=
  domainOk -> compressionOk

def ay_acrg_decompression_policy (compressionOk decompressionOk : Prop) : Prop :=
  compressionOk -> decompressionOk

def ay_acrg_roundtrip_reconstruction_witness (decompressionOk totalAssignment : Prop) : Prop :=
  decompressionOk -> totalAssignment

def ay_acrg_duplicate_conflict_policy (totalAssignment duplicateOk : Prop) : Prop :=
  totalAssignment -> duplicateOk

def ay_acrg_original_clause_satisfaction_replay (duplicateOk replayOk : Prop) : Prop :=
  duplicateOk -> replayOk

def ay_acrg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_acrg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_acrg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_acrg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_acrg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_acrg_accepted_roundtrip
    (fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop) : Prop :=
  ay_acrg_conj fingerprint
    (ay_acrg_conj domain
      (ay_acrg_conj compression
        (ay_acrg_conj decompression
          (ay_acrg_conj roundtrip
            (ay_acrg_conj duplicate
              (ay_acrg_conj replay
                (ay_acrg_conj checker
                  (ay_acrg_conj build
                    (ay_acrg_conj archive
                      (ay_acrg_conj fallback audit))))))))))

def ay_acrg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_acrg_conj accepted (ay_acrg_conj totalAssignment (ay_acrg_conj originalSat audited))

def ay_acrg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_acrg_conj proofAccepted originalUnsat

def ay_acrg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_acrg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_acrg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_acrg_conj p q :=
  fun r h => h hp hq

theorem ay_acrg_conj_left {p q : Prop} (h : ay_acrg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_acrg_conj_right {p q : Prop} (h : ay_acrg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_acrg_conj_left h)

theorem ay_acrg_disj_left {p q : Prop} (hp : p) : ay_acrg_disj p q :=
  fun r hl _ => hl hp

theorem ay_acrg_disj_right {p q : Prop} (hq : q) : ay_acrg_disj p q :=
  fun r _ hr => hr hq

theorem ay_acrg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_acrg_equiv p q :=
  ay_acrg_conj_intro hpq hqp

theorem ay_acrg_equiv_forward {p q : Prop} (h : ay_acrg_equiv p q) : p -> q :=
  ay_acrg_conj_left h

theorem ay_acrg_equiv_backward {p q : Prop} (h : ay_acrg_equiv p q) : q -> p :=
  ay_acrg_conj_right h

theorem ay_acrg_benchmark_fingerprint_intro {compressedWitness fingerprintOk : Prop}
    (h : compressedWitness -> fingerprintOk) :
    ay_acrg_benchmark_fingerprint compressedWitness fingerprintOk :=
  h

theorem ay_acrg_variable_domain_manifest_intro {fingerprintOk domainOk : Prop}
    (h : fingerprintOk -> domainOk) :
    ay_acrg_variable_domain_manifest fingerprintOk domainOk :=
  h

theorem ay_acrg_compressed_assignment_digest_intro {domainOk compressionOk : Prop}
    (h : domainOk -> compressionOk) :
    ay_acrg_compressed_assignment_digest domainOk compressionOk :=
  h

theorem ay_acrg_decompression_policy_intro {compressionOk decompressionOk : Prop}
    (h : compressionOk -> decompressionOk) :
    ay_acrg_decompression_policy compressionOk decompressionOk :=
  h

theorem ay_acrg_roundtrip_reconstruction_witness_intro
    {decompressionOk totalAssignment : Prop}
    (h : decompressionOk -> totalAssignment) :
    ay_acrg_roundtrip_reconstruction_witness decompressionOk totalAssignment :=
  h

theorem ay_acrg_duplicate_conflict_policy_intro {totalAssignment duplicateOk : Prop}
    (h : totalAssignment -> duplicateOk) :
    ay_acrg_duplicate_conflict_policy totalAssignment duplicateOk :=
  h

theorem ay_acrg_original_clause_satisfaction_replay_intro {duplicateOk replayOk : Prop}
    (h : duplicateOk -> replayOk) :
    ay_acrg_original_clause_satisfaction_replay duplicateOk replayOk :=
  h

theorem ay_acrg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_acrg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_acrg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_acrg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_acrg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_acrg_archive_manifest buildOk archiveOk :=
  h

theorem ay_acrg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_acrg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_acrg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_acrg_audit_transcript fallbackReady audited :=
  h

theorem ay_acrg_accepted_roundtrip_intro
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (hf : fingerprint) (hd : domain) (hc : compression) (hdec : decompression)
    (hrt : roundtrip) (hdup : duplicate) (hr : replay) (hchk : checker)
    (hb : build) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit :=
  ay_acrg_conj_intro hf
    (ay_acrg_conj_intro hd
      (ay_acrg_conj_intro hc
        (ay_acrg_conj_intro hdec
          (ay_acrg_conj_intro hrt
            (ay_acrg_conj_intro hdup
              (ay_acrg_conj_intro hr
                (ay_acrg_conj_intro hchk
                  (ay_acrg_conj_intro hb
                    (ay_acrg_conj_intro ha
                      (ay_acrg_conj_intro hfb hau))))))))))

theorem ay_acrg_accepted_roundtrip_fingerprint
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : fingerprint :=
  ay_acrg_conj_left h

theorem ay_acrg_accepted_roundtrip_domain
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : domain :=
  ay_acrg_conj_left (ay_acrg_conj_right h)

theorem ay_acrg_accepted_roundtrip_compression
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : compression :=
  ay_acrg_conj_left (ay_acrg_conj_right (ay_acrg_conj_right h))

theorem ay_acrg_accepted_roundtrip_decompression
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : decompression :=
  ay_acrg_conj_left
    (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h)))

theorem ay_acrg_accepted_roundtrip_roundtrip
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : roundtrip :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))))

theorem ay_acrg_accepted_roundtrip_duplicate
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : duplicate :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h)))))

theorem ay_acrg_accepted_roundtrip_replay
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : replay :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))))))

theorem ay_acrg_accepted_roundtrip_checker
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : checker :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right
            (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h)))))))

theorem ay_acrg_accepted_roundtrip_build
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : build :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right
            (ay_acrg_conj_right
              (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))))))))

theorem ay_acrg_accepted_roundtrip_archive
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : archive :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right
            (ay_acrg_conj_right
              (ay_acrg_conj_right
                (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h)))))))))

theorem ay_acrg_accepted_roundtrip_fallback
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : fallback :=
  ay_acrg_conj_left
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right
            (ay_acrg_conj_right
              (ay_acrg_conj_right
                (ay_acrg_conj_right
                  (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))))))))))

theorem ay_acrg_accepted_roundtrip_audit
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit : Prop}
    (h : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit) : audit :=
  ay_acrg_conj_right
    (ay_acrg_conj_right
      (ay_acrg_conj_right
        (ay_acrg_conj_right
          (ay_acrg_conj_right
            (ay_acrg_conj_right
              (ay_acrg_conj_right
                (ay_acrg_conj_right
                  (ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))))))))))

theorem ay_acrg_compression_roundtrip_reconstructs_original_sat
    {compressedWitness fingerprintOk domainOk compressionOk decompressionOk totalAssignment
     duplicateOk replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_acrg_benchmark_fingerprint compressedWitness fingerprintOk)
    (hd : ay_acrg_variable_domain_manifest fingerprintOk domainOk)
    (hc : ay_acrg_compressed_assignment_digest domainOk compressionOk)
    (hdec : ay_acrg_decompression_policy compressionOk decompressionOk)
    (hrt : ay_acrg_roundtrip_reconstruction_witness decompressionOk totalAssignment)
    (hdup : ay_acrg_duplicate_conflict_policy totalAssignment duplicateOk)
    (hr : ay_acrg_original_clause_satisfaction_replay duplicateOk replayOk)
    (hchk : ay_acrg_model_checker_transcript replayOk originalSat)
    (hb : ay_acrg_solver_build_evidence originalSat buildOk)
    (ha : ay_acrg_archive_manifest buildOk archiveOk)
    (hfb : ay_acrg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_acrg_audit_transcript fallbackReady audited)
    (hw : compressedWitness) :
    ay_acrg_conj totalAssignment (ay_acrg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hdomain : domainOk := hd hfingerprint
  let hcompression : compressionOk := hc hdomain
  let hdecompression : decompressionOk := hdec hcompression
  let htotal : totalAssignment := hrt hdecompression
  let hduplicate : duplicateOk := hdup htotal
  let hreplay : replayOk := hr hduplicate
  let hsat : originalSat := hchk hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_acrg_conj_intro htotal (ay_acrg_conj_intro hsat haudit)

theorem ay_acrg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_acrg_public_sat accepted totalAssignment originalSat audited :=
  ay_acrg_conj_intro ha (ay_acrg_conj_intro ht (ay_acrg_conj_intro hs hau))

theorem ay_acrg_public_sat_requires_compression_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_acrg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_acrg_conj_left h

theorem ay_acrg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_acrg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_acrg_conj_left (ay_acrg_conj_right h)

theorem ay_acrg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_acrg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_acrg_conj_left (ay_acrg_conj_right (ay_acrg_conj_right h))

theorem ay_acrg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_acrg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_acrg_conj_right (ay_acrg_conj_right (ay_acrg_conj_right h))

theorem ay_acrg_accepted_roundtrip_publishes_sat
    {fingerprint domain compression decompression roundtrip duplicate replay checker build
     archive fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
      duplicate replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_acrg_public_sat
      (ay_acrg_accepted_roundtrip fingerprint domain compression decompression roundtrip
        duplicate replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_acrg_public_sat_intro hg ht hs hau

theorem ay_acrg_no_claim_intro {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  h

theorem ay_acrg_recompute_intro {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  h

theorem ay_acrg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  ay_acrg_recompute_intro h

theorem ay_acrg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_compression_mismatch_recompute {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  ay_acrg_recompute_intro h

theorem ay_acrg_decompression_mismatch_recompute {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  ay_acrg_recompute_intro h

theorem ay_acrg_roundtrip_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_duplicate_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  ay_acrg_recompute_intro h

theorem ay_acrg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_acrg_recompute_obligation reason :=
  ay_acrg_recompute_intro h

theorem ay_acrg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_acrg_no_claim_diagnostic reason :=
  ay_acrg_no_claim_intro h

theorem ay_acrg_failed_compression_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_acrg_public_sat accepted totalAssignment originalSat audited ->
      ay_acrg_no_claim_diagnostic failure) :
    ay_acrg_conj (ay_acrg_no_claim_diagnostic failure)
      (ay_acrg_public_sat accepted totalAssignment originalSat audited ->
        ay_acrg_no_claim_diagnostic failure) :=
  ay_acrg_conj_intro (ay_acrg_no_claim_intro hfail) hblock

theorem ay_acrg_failed_compression_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_acrg_public_sat accepted totalAssignment originalSat audited ->
      ay_acrg_recompute_obligation failure) :
    ay_acrg_conj (ay_acrg_recompute_obligation failure)
      (ay_acrg_public_sat accepted totalAssignment originalSat audited ->
        ay_acrg_recompute_obligation failure) :=
  ay_acrg_conj_intro (ay_acrg_recompute_intro hfail) hblock

theorem ay_acrg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_acrg_public_unsat proofAccepted originalUnsat :=
  ay_acrg_conj_intro hp hu

theorem ay_acrg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_acrg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_acrg_conj_left h

theorem ay_acrg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_acrg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_acrg_conj_right h

theorem ay_acrg_compression_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat compressionSatGuard : Prop}
    (h : ay_acrg_public_unsat proofAccepted originalUnsat) :
    ay_acrg_conj (ay_acrg_public_unsat proofAccepted originalUnsat)
      (compressionSatGuard -> ay_acrg_public_unsat proofAccepted originalUnsat) :=
  ay_acrg_conj_intro h (fun _ => h)

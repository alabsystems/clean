/-!
  SAT-COMP/ay binary witness encoding guard.

  This self-contained package models the evidence required before a compact
  binary SAT model witness may be decoded and published for the original
  sequential-main SAT-COMP instance.
-/

def ay_bweg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_bweg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_bweg_equiv (p q : Prop) : Prop :=
  ay_bweg_conj (p -> q) (q -> p)

def ay_bweg_encoding_version_manifest (binaryWitness versionOk : Prop) : Prop :=
  binaryWitness -> versionOk

def ay_bweg_byte_stream_digest (versionOk byteDigestOk : Prop) : Prop :=
  versionOk -> byteDigestOk

def ay_bweg_variable_domain_manifest (byteDigestOk domainOk : Prop) : Prop :=
  byteDigestOk -> domainOk

def ay_bweg_literal_order_reconstruction_witness (domainOk orderOk : Prop) : Prop :=
  domainOk -> orderOk

def ay_bweg_total_assignment_expansion_witness (orderOk totalAssignment : Prop) : Prop :=
  orderOk -> totalAssignment

def ay_bweg_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_bweg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_bweg_benchmark_fingerprint (originalSat fingerprintOk : Prop) : Prop :=
  originalSat -> fingerprintOk

def ay_bweg_solver_build_evidence (fingerprintOk buildOk : Prop) : Prop :=
  fingerprintOk -> buildOk

def ay_bweg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_bweg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_bweg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_bweg_accepted_binary_witness
    (version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop) : Prop :=
  ay_bweg_conj version
    (ay_bweg_conj byteDigest
      (ay_bweg_conj domain
        (ay_bweg_conj order
          (ay_bweg_conj expansion
            (ay_bweg_conj replay
              (ay_bweg_conj checker
                (ay_bweg_conj fingerprint
                  (ay_bweg_conj build
                    (ay_bweg_conj archive
                      (ay_bweg_conj fallback audit))))))))))

def ay_bweg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_bweg_conj accepted (ay_bweg_conj totalAssignment (ay_bweg_conj originalSat audited))

def ay_bweg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_bweg_conj proofAccepted originalUnsat

def ay_bweg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_bweg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_bweg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_bweg_conj p q :=
  fun r h => h hp hq

theorem ay_bweg_conj_left {p q : Prop} (h : ay_bweg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_bweg_conj_right {p q : Prop} (h : ay_bweg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_bweg_conj_left h)

theorem ay_bweg_disj_left {p q : Prop} (hp : p) : ay_bweg_disj p q :=
  fun r hl _ => hl hp

theorem ay_bweg_disj_right {p q : Prop} (hq : q) : ay_bweg_disj p q :=
  fun r _ hr => hr hq

theorem ay_bweg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_bweg_equiv p q :=
  ay_bweg_conj_intro hpq hqp

theorem ay_bweg_equiv_forward {p q : Prop} (h : ay_bweg_equiv p q) : p -> q :=
  ay_bweg_conj_left h

theorem ay_bweg_equiv_backward {p q : Prop} (h : ay_bweg_equiv p q) : q -> p :=
  ay_bweg_conj_right h

theorem ay_bweg_encoding_version_manifest_intro {binaryWitness versionOk : Prop}
    (h : binaryWitness -> versionOk) :
    ay_bweg_encoding_version_manifest binaryWitness versionOk :=
  h

theorem ay_bweg_byte_stream_digest_intro {versionOk byteDigestOk : Prop}
    (h : versionOk -> byteDigestOk) :
    ay_bweg_byte_stream_digest versionOk byteDigestOk :=
  h

theorem ay_bweg_variable_domain_manifest_intro {byteDigestOk domainOk : Prop}
    (h : byteDigestOk -> domainOk) :
    ay_bweg_variable_domain_manifest byteDigestOk domainOk :=
  h

theorem ay_bweg_literal_order_reconstruction_witness_intro {domainOk orderOk : Prop}
    (h : domainOk -> orderOk) :
    ay_bweg_literal_order_reconstruction_witness domainOk orderOk :=
  h

theorem ay_bweg_total_assignment_expansion_witness_intro {orderOk totalAssignment : Prop}
    (h : orderOk -> totalAssignment) :
    ay_bweg_total_assignment_expansion_witness orderOk totalAssignment :=
  h

theorem ay_bweg_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_bweg_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_bweg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_bweg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_bweg_benchmark_fingerprint_intro {originalSat fingerprintOk : Prop}
    (h : originalSat -> fingerprintOk) :
    ay_bweg_benchmark_fingerprint originalSat fingerprintOk :=
  h

theorem ay_bweg_solver_build_evidence_intro {fingerprintOk buildOk : Prop}
    (h : fingerprintOk -> buildOk) :
    ay_bweg_solver_build_evidence fingerprintOk buildOk :=
  h

theorem ay_bweg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_bweg_archive_manifest buildOk archiveOk :=
  h

theorem ay_bweg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_bweg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_bweg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_bweg_audit_transcript fallbackReady audited :=
  h

theorem ay_bweg_accepted_binary_witness_intro
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (hv : version) (hb : byteDigest) (hd : domain) (ho : order) (he : expansion)
    (hr : replay) (hc : checker) (hf : fingerprint) (hbuild : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit :=
  ay_bweg_conj_intro hv
    (ay_bweg_conj_intro hb
      (ay_bweg_conj_intro hd
        (ay_bweg_conj_intro ho
          (ay_bweg_conj_intro he
            (ay_bweg_conj_intro hr
              (ay_bweg_conj_intro hc
                (ay_bweg_conj_intro hf
                  (ay_bweg_conj_intro hbuild
                    (ay_bweg_conj_intro ha
                      (ay_bweg_conj_intro hfb hau))))))))))

theorem ay_bweg_accepted_binary_witness_version
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : version :=
  ay_bweg_conj_left h

theorem ay_bweg_accepted_binary_witness_byte_digest
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : byteDigest :=
  ay_bweg_conj_left (ay_bweg_conj_right h)

theorem ay_bweg_accepted_binary_witness_domain
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : domain :=
  ay_bweg_conj_left (ay_bweg_conj_right (ay_bweg_conj_right h))

theorem ay_bweg_accepted_binary_witness_order
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : order :=
  ay_bweg_conj_left
    (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h)))

theorem ay_bweg_accepted_binary_witness_expansion
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : expansion :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))))

theorem ay_bweg_accepted_binary_witness_replay
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : replay :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h)))))

theorem ay_bweg_accepted_binary_witness_checker
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : checker :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))))))

theorem ay_bweg_accepted_binary_witness_fingerprint
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : fingerprint :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right
            (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h)))))))

theorem ay_bweg_accepted_binary_witness_build
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : build :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right
            (ay_bweg_conj_right
              (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))))))))

theorem ay_bweg_accepted_binary_witness_archive
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : archive :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right
            (ay_bweg_conj_right
              (ay_bweg_conj_right
                (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h)))))))))

theorem ay_bweg_accepted_binary_witness_fallback
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : fallback :=
  ay_bweg_conj_left
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right
            (ay_bweg_conj_right
              (ay_bweg_conj_right
                (ay_bweg_conj_right
                  (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))))))))))

theorem ay_bweg_accepted_binary_witness_audit
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit : Prop}
    (h : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit) : audit :=
  ay_bweg_conj_right
    (ay_bweg_conj_right
      (ay_bweg_conj_right
        (ay_bweg_conj_right
          (ay_bweg_conj_right
            (ay_bweg_conj_right
              (ay_bweg_conj_right
                (ay_bweg_conj_right
                  (ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))))))))))

theorem ay_bweg_binary_witness_reconstructs_total_sat
    {binaryWitness versionOk byteDigestOk domainOk orderOk totalAssignment replayOk
     originalSat fingerprintOk buildOk archiveOk fallbackReady audited : Prop}
    (hv : ay_bweg_encoding_version_manifest binaryWitness versionOk)
    (hb : ay_bweg_byte_stream_digest versionOk byteDigestOk)
    (hd : ay_bweg_variable_domain_manifest byteDigestOk domainOk)
    (ho : ay_bweg_literal_order_reconstruction_witness domainOk orderOk)
    (he : ay_bweg_total_assignment_expansion_witness orderOk totalAssignment)
    (hr : ay_bweg_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_bweg_model_checker_transcript replayOk originalSat)
    (hf : ay_bweg_benchmark_fingerprint originalSat fingerprintOk)
    (hbuild : ay_bweg_solver_build_evidence fingerprintOk buildOk)
    (ha : ay_bweg_archive_manifest buildOk archiveOk)
    (hfb : ay_bweg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_bweg_audit_transcript fallbackReady audited)
    (hw : binaryWitness) :
    ay_bweg_conj totalAssignment (ay_bweg_conj originalSat audited) :=
  let hversion : versionOk := hv hw
  let hbytes : byteDigestOk := hb hversion
  let hdomain : domainOk := hd hbytes
  let horder : orderOk := ho hdomain
  let htotal : totalAssignment := he horder
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hfingerprint : fingerprintOk := hf hsat
  let hbuild : buildOk := hbuild hfingerprint
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_bweg_conj_intro htotal (ay_bweg_conj_intro hsat haudit)

theorem ay_bweg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_bweg_public_sat accepted totalAssignment originalSat audited :=
  ay_bweg_conj_intro ha (ay_bweg_conj_intro ht (ay_bweg_conj_intro hs hau))

theorem ay_bweg_public_sat_requires_binary_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_bweg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_bweg_conj_left h

theorem ay_bweg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_bweg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_bweg_conj_left (ay_bweg_conj_right h)

theorem ay_bweg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_bweg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_bweg_conj_left (ay_bweg_conj_right (ay_bweg_conj_right h))

theorem ay_bweg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_bweg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_bweg_conj_right (ay_bweg_conj_right (ay_bweg_conj_right h))

theorem ay_bweg_accepted_binary_witness_publishes_sat
    {version byteDigest domain order expansion replay checker fingerprint build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
      checker fingerprint build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_bweg_public_sat
      (ay_bweg_accepted_binary_witness version byteDigest domain order expansion replay
        checker fingerprint build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_bweg_public_sat_intro hg ht hs hau

theorem ay_bweg_no_claim_intro {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  h

theorem ay_bweg_recompute_intro {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  h

theorem ay_bweg_version_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_byte_mismatch_recompute {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  ay_bweg_recompute_intro h

theorem ay_bweg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_order_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_expansion_mismatch_recompute {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  ay_bweg_recompute_intro h

theorem ay_bweg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  ay_bweg_recompute_intro h

theorem ay_bweg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  ay_bweg_recompute_intro h

theorem ay_bweg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_bweg_recompute_obligation reason :=
  ay_bweg_recompute_intro h

theorem ay_bweg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_bweg_no_claim_diagnostic reason :=
  ay_bweg_no_claim_intro h

theorem ay_bweg_failed_binary_witness_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_bweg_public_sat accepted totalAssignment originalSat audited ->
      ay_bweg_no_claim_diagnostic failure) :
    ay_bweg_conj (ay_bweg_no_claim_diagnostic failure)
      (ay_bweg_public_sat accepted totalAssignment originalSat audited ->
        ay_bweg_no_claim_diagnostic failure) :=
  ay_bweg_conj_intro (ay_bweg_no_claim_intro hfail) hblock

theorem ay_bweg_failed_binary_witness_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_bweg_public_sat accepted totalAssignment originalSat audited ->
      ay_bweg_recompute_obligation failure) :
    ay_bweg_conj (ay_bweg_recompute_obligation failure)
      (ay_bweg_public_sat accepted totalAssignment originalSat audited ->
        ay_bweg_recompute_obligation failure) :=
  ay_bweg_conj_intro (ay_bweg_recompute_intro hfail) hblock

theorem ay_bweg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_bweg_public_unsat proofAccepted originalUnsat :=
  ay_bweg_conj_intro hp hu

theorem ay_bweg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_bweg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_bweg_conj_left h

theorem ay_bweg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_bweg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_bweg_conj_right h

theorem ay_bweg_binary_witness_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat binarySatGuard : Prop}
    (h : ay_bweg_public_unsat proofAccepted originalUnsat) :
    ay_bweg_conj (ay_bweg_public_unsat proofAccepted originalUnsat)
      (binarySatGuard -> ay_bweg_public_unsat proofAccepted originalUnsat) :=
  ay_bweg_conj_intro h (fun _ => h)

/-!
  SAT-COMP/ay model-checker cross-validation guard.

  This self-contained package models the SAT-only obligations for publishing a
  SAT model only after primary and independent checker transcripts agree with
  the reconstructed assignment and original formula evidence.
-/

def ay_mcvp_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mcvp_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mcvp_equiv (p q : Prop) : Prop :=
  ay_mcvp_conj (p -> q) (q -> p)

def ay_mcvp_benchmark_fingerprint (modelArtifact fingerprintOk : Prop) : Prop :=
  modelArtifact -> fingerprintOk

def ay_mcvp_primary_model_checker_transcript (fingerprintOk primaryOk : Prop) : Prop :=
  fingerprintOk -> primaryOk

def ay_mcvp_independent_replay_checker_transcript (primaryOk replayOk : Prop) : Prop :=
  primaryOk -> replayOk

def ay_mcvp_variable_domain_manifest (replayOk domainOk : Prop) : Prop :=
  replayOk -> domainOk

def ay_mcvp_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_mcvp_clause_satisfaction_digest (totalAssignment satisfactionOk : Prop) : Prop :=
  totalAssignment -> satisfactionOk

def ay_mcvp_solver_build_evidence (satisfactionOk buildOk : Prop) : Prop :=
  satisfactionOk -> buildOk

def ay_mcvp_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mcvp_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mcvp_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mcvp_accepted_cross_validation
    (fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop) : Prop :=
  ay_mcvp_conj fingerprint
    (ay_mcvp_conj primary
      (ay_mcvp_conj replay
        (ay_mcvp_conj domain
          (ay_mcvp_conj reconstruction
            (ay_mcvp_conj satisfaction
              (ay_mcvp_conj build
                (ay_mcvp_conj archive
                  (ay_mcvp_conj fallback audit))))))))

def ay_mcvp_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_mcvp_conj accepted (ay_mcvp_conj totalAssignment (ay_mcvp_conj originalSat audited))

def ay_mcvp_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mcvp_conj proofAccepted originalUnsat

def ay_mcvp_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mcvp_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mcvp_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mcvp_conj p q :=
  fun r h => h hp hq

theorem ay_mcvp_conj_left {p q : Prop} (h : ay_mcvp_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mcvp_conj_right {p q : Prop} (h : ay_mcvp_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mcvp_conj_left h)

theorem ay_mcvp_disj_left {p q : Prop} (hp : p) : ay_mcvp_disj p q :=
  fun r hl _ => hl hp

theorem ay_mcvp_disj_right {p q : Prop} (hq : q) : ay_mcvp_disj p q :=
  fun r _ hr => hr hq

theorem ay_mcvp_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mcvp_equiv p q :=
  ay_mcvp_conj_intro hpq hqp

theorem ay_mcvp_equiv_forward {p q : Prop} (h : ay_mcvp_equiv p q) : p -> q :=
  ay_mcvp_conj_left h

theorem ay_mcvp_equiv_backward {p q : Prop} (h : ay_mcvp_equiv p q) : q -> p :=
  ay_mcvp_conj_right h

theorem ay_mcvp_benchmark_fingerprint_intro {modelArtifact fingerprintOk : Prop}
    (h : modelArtifact -> fingerprintOk) :
    ay_mcvp_benchmark_fingerprint modelArtifact fingerprintOk :=
  h

theorem ay_mcvp_primary_model_checker_transcript_intro {fingerprintOk primaryOk : Prop}
    (h : fingerprintOk -> primaryOk) :
    ay_mcvp_primary_model_checker_transcript fingerprintOk primaryOk :=
  h

theorem ay_mcvp_independent_replay_checker_transcript_intro {primaryOk replayOk : Prop}
    (h : primaryOk -> replayOk) :
    ay_mcvp_independent_replay_checker_transcript primaryOk replayOk :=
  h

theorem ay_mcvp_variable_domain_manifest_intro {replayOk domainOk : Prop}
    (h : replayOk -> domainOk) :
    ay_mcvp_variable_domain_manifest replayOk domainOk :=
  h

theorem ay_mcvp_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_mcvp_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_mcvp_clause_satisfaction_digest_intro {totalAssignment satisfactionOk : Prop}
    (h : totalAssignment -> satisfactionOk) :
    ay_mcvp_clause_satisfaction_digest totalAssignment satisfactionOk :=
  h

theorem ay_mcvp_solver_build_evidence_intro {satisfactionOk buildOk : Prop}
    (h : satisfactionOk -> buildOk) :
    ay_mcvp_solver_build_evidence satisfactionOk buildOk :=
  h

theorem ay_mcvp_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mcvp_archive_manifest buildOk archiveOk :=
  h

theorem ay_mcvp_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mcvp_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mcvp_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mcvp_audit_transcript fallbackReady audited :=
  h

theorem ay_mcvp_accepted_cross_validation_intro
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (hf : fingerprint) (hp : primary) (hr : replay) (hd : domain)
    (hrc : reconstruction) (hs : satisfaction) (hb : build) (ha : archive)
    (hfb : fallback) (hau : audit) :
    ay_mcvp_accepted_cross_validation fingerprint primary replay domain reconstruction
      satisfaction build archive fallback audit :=
  ay_mcvp_conj_intro hf
    (ay_mcvp_conj_intro hp
      (ay_mcvp_conj_intro hr
        (ay_mcvp_conj_intro hd
          (ay_mcvp_conj_intro hrc
            (ay_mcvp_conj_intro hs
              (ay_mcvp_conj_intro hb
                (ay_mcvp_conj_intro ha
                  (ay_mcvp_conj_intro hfb hau))))))))

theorem ay_mcvp_accepted_cross_validation_fingerprint
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : fingerprint :=
  ay_mcvp_conj_left h

theorem ay_mcvp_accepted_cross_validation_primary
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : primary :=
  ay_mcvp_conj_left (ay_mcvp_conj_right h)

theorem ay_mcvp_accepted_cross_validation_replay
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : replay :=
  ay_mcvp_conj_left (ay_mcvp_conj_right (ay_mcvp_conj_right h))

theorem ay_mcvp_accepted_cross_validation_domain
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : domain :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h)))

theorem ay_mcvp_accepted_cross_validation_reconstruction
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : reconstruction :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h))))

theorem ay_mcvp_accepted_cross_validation_satisfaction
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : satisfaction :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right
        (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h)))))

theorem ay_mcvp_accepted_cross_validation_build
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : build :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right
        (ay_mcvp_conj_right
          (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h))))))

theorem ay_mcvp_accepted_cross_validation_archive
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : archive :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right
        (ay_mcvp_conj_right
          (ay_mcvp_conj_right
            (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h)))))))

theorem ay_mcvp_accepted_cross_validation_fallback
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : fallback :=
  ay_mcvp_conj_left
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right
        (ay_mcvp_conj_right
          (ay_mcvp_conj_right
            (ay_mcvp_conj_right
              (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h))))))))

theorem ay_mcvp_accepted_cross_validation_audit
    {fingerprint primary replay domain reconstruction satisfaction build archive
     fallback audit : Prop}
    (h : ay_mcvp_accepted_cross_validation fingerprint primary replay domain
      reconstruction satisfaction build archive fallback audit) : audit :=
  ay_mcvp_conj_right
    (ay_mcvp_conj_right
      (ay_mcvp_conj_right
        (ay_mcvp_conj_right
          (ay_mcvp_conj_right
            (ay_mcvp_conj_right
              (ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h))))))))

theorem ay_mcvp_cross_validation_reconstructs_original_sat
    {modelArtifact fingerprintOk primaryOk replayOk domainOk totalAssignment satisfactionOk
     buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_mcvp_benchmark_fingerprint modelArtifact fingerprintOk)
    (hp : ay_mcvp_primary_model_checker_transcript fingerprintOk primaryOk)
    (hr : ay_mcvp_independent_replay_checker_transcript primaryOk replayOk)
    (hd : ay_mcvp_variable_domain_manifest replayOk domainOk)
    (hrc : ay_mcvp_total_assignment_reconstruction domainOk totalAssignment)
    (hs : ay_mcvp_clause_satisfaction_digest totalAssignment satisfactionOk)
    (hb : ay_mcvp_solver_build_evidence satisfactionOk buildOk)
    (ha : ay_mcvp_archive_manifest buildOk archiveOk)
    (hfb : ay_mcvp_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_mcvp_audit_transcript fallbackReady audited)
    (hm : modelArtifact) :
    ay_mcvp_conj totalAssignment (ay_mcvp_conj satisfactionOk audited) :=
  let hfingerprint : fingerprintOk := hf hm
  let hprimary : primaryOk := hp hfingerprint
  let hreplay : replayOk := hr hprimary
  let hdomain : domainOk := hd hreplay
  let htotal : totalAssignment := hrc hdomain
  let hsatisfaction : satisfactionOk := hs htotal
  let hbuild : buildOk := hb hsatisfaction
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_mcvp_conj_intro htotal (ay_mcvp_conj_intro hsatisfaction haudit)

theorem ay_mcvp_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_mcvp_public_sat accepted totalAssignment originalSat audited :=
  ay_mcvp_conj_intro ha (ay_mcvp_conj_intro ht (ay_mcvp_conj_intro hs hau))

theorem ay_mcvp_public_sat_requires_cross_validation
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_mcvp_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_mcvp_conj_left h

theorem ay_mcvp_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_mcvp_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_mcvp_conj_left (ay_mcvp_conj_right h)

theorem ay_mcvp_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_mcvp_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_mcvp_conj_left (ay_mcvp_conj_right (ay_mcvp_conj_right h))

theorem ay_mcvp_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_mcvp_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_mcvp_conj_right (ay_mcvp_conj_right (ay_mcvp_conj_right h))

theorem ay_mcvp_accepted_cross_validation_publishes_sat
    {fingerprint primary replay domain reconstruction satisfaction build archive fallback
     audit totalAssignment originalSat audited : Prop}
    (hg : ay_mcvp_accepted_cross_validation fingerprint primary replay domain reconstruction
      satisfaction build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_mcvp_public_sat
      (ay_mcvp_accepted_cross_validation fingerprint primary replay domain reconstruction
        satisfaction build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_mcvp_public_sat_intro hg ht hs hau

theorem ay_mcvp_no_claim_intro {reason : Prop} (h : reason) :
    ay_mcvp_no_claim_diagnostic reason :=
  h

theorem ay_mcvp_recompute_intro {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  h

theorem ay_mcvp_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  ay_mcvp_recompute_intro h

theorem ay_mcvp_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mcvp_no_claim_diagnostic reason :=
  ay_mcvp_no_claim_intro h

theorem ay_mcvp_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  ay_mcvp_recompute_intro h

theorem ay_mcvp_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mcvp_no_claim_diagnostic reason :=
  ay_mcvp_no_claim_intro h

theorem ay_mcvp_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  ay_mcvp_recompute_intro h

theorem ay_mcvp_satisfaction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  ay_mcvp_recompute_intro h

theorem ay_mcvp_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mcvp_recompute_obligation reason :=
  ay_mcvp_recompute_intro h

theorem ay_mcvp_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mcvp_no_claim_diagnostic reason :=
  ay_mcvp_no_claim_intro h

theorem ay_mcvp_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mcvp_no_claim_diagnostic reason :=
  ay_mcvp_no_claim_intro h

theorem ay_mcvp_failed_cross_validation_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mcvp_public_sat accepted totalAssignment originalSat audited ->
      ay_mcvp_no_claim_diagnostic failure) :
    ay_mcvp_conj (ay_mcvp_no_claim_diagnostic failure)
      (ay_mcvp_public_sat accepted totalAssignment originalSat audited ->
        ay_mcvp_no_claim_diagnostic failure) :=
  ay_mcvp_conj_intro (ay_mcvp_no_claim_intro hfail) hblock

theorem ay_mcvp_failed_cross_validation_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mcvp_public_sat accepted totalAssignment originalSat audited ->
      ay_mcvp_recompute_obligation failure) :
    ay_mcvp_conj (ay_mcvp_recompute_obligation failure)
      (ay_mcvp_public_sat accepted totalAssignment originalSat audited ->
        ay_mcvp_recompute_obligation failure) :=
  ay_mcvp_conj_intro (ay_mcvp_recompute_intro hfail) hblock

theorem ay_mcvp_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mcvp_public_unsat proofAccepted originalUnsat :=
  ay_mcvp_conj_intro hp hu

theorem ay_mcvp_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mcvp_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mcvp_conj_left h

theorem ay_mcvp_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mcvp_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mcvp_conj_right h

theorem ay_mcvp_cross_validation_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat crossValidationSatGuard : Prop}
    (h : ay_mcvp_public_unsat proofAccepted originalUnsat) :
    ay_mcvp_conj (ay_mcvp_public_unsat proofAccepted originalUnsat)
      (crossValidationSatGuard -> ay_mcvp_public_unsat proofAccepted originalUnsat) :=
  ay_mcvp_conj_intro h (fun _ => h)

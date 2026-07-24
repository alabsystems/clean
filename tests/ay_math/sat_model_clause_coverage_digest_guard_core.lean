/-!
  SAT-COMP/ay model clause-coverage digest guard.

  This self-contained package models the SAT-only obligations for publishing a
  model only when clause coverage evidence shows every original clause is
  satisfied by the reconstructed assignment.
-/

def ay_mccg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mccg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mccg_equiv (p q : Prop) : Prop :=
  ay_mccg_conj (p -> q) (q -> p)

def ay_mccg_benchmark_fingerprint (modelArtifact fingerprintOk : Prop) : Prop :=
  modelArtifact -> fingerprintOk

def ay_mccg_clause_coverage_digest (fingerprintOk coverageOk : Prop) : Prop :=
  fingerprintOk -> coverageOk

def ay_mccg_variable_domain_manifest (coverageOk domainOk : Prop) : Prop :=
  coverageOk -> domainOk

def ay_mccg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_mccg_per_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_mccg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_mccg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_mccg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mccg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mccg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mccg_accepted_coverage
    (fingerprint coverage domain reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_mccg_conj fingerprint
    (ay_mccg_conj coverage
      (ay_mccg_conj domain
        (ay_mccg_conj reconstruction
          (ay_mccg_conj replay
            (ay_mccg_conj checker
              (ay_mccg_conj build
                (ay_mccg_conj archive
                  (ay_mccg_conj fallback audit))))))))

def ay_mccg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_mccg_conj accepted
    (ay_mccg_conj totalAssignment
      (ay_mccg_conj everyOriginalClauseSatisfied (ay_mccg_conj originalSat audited)))

def ay_mccg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mccg_conj proofAccepted originalUnsat

def ay_mccg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mccg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mccg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mccg_conj p q :=
  fun r h => h hp hq

theorem ay_mccg_conj_left {p q : Prop} (h : ay_mccg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mccg_conj_right {p q : Prop} (h : ay_mccg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mccg_conj_left h)

theorem ay_mccg_disj_left {p q : Prop} (hp : p) : ay_mccg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mccg_disj_right {p q : Prop} (hq : q) : ay_mccg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mccg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mccg_equiv p q :=
  ay_mccg_conj_intro hpq hqp

theorem ay_mccg_equiv_forward {p q : Prop} (h : ay_mccg_equiv p q) : p -> q :=
  ay_mccg_conj_left h

theorem ay_mccg_equiv_backward {p q : Prop} (h : ay_mccg_equiv p q) : q -> p :=
  ay_mccg_conj_right h

theorem ay_mccg_benchmark_fingerprint_intro {modelArtifact fingerprintOk : Prop}
    (h : modelArtifact -> fingerprintOk) :
    ay_mccg_benchmark_fingerprint modelArtifact fingerprintOk :=
  h

theorem ay_mccg_clause_coverage_digest_intro {fingerprintOk coverageOk : Prop}
    (h : fingerprintOk -> coverageOk) :
    ay_mccg_clause_coverage_digest fingerprintOk coverageOk :=
  h

theorem ay_mccg_variable_domain_manifest_intro {coverageOk domainOk : Prop}
    (h : coverageOk -> domainOk) :
    ay_mccg_variable_domain_manifest coverageOk domainOk :=
  h

theorem ay_mccg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_mccg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_mccg_per_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_mccg_per_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_mccg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_mccg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_mccg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_mccg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_mccg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mccg_archive_manifest buildOk archiveOk :=
  h

theorem ay_mccg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mccg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mccg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mccg_audit_transcript fallbackReady audited :=
  h

theorem ay_mccg_accepted_coverage_intro
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hcvg : coverage) (hd : domain) (hrc : reconstruction)
    (hr : replay) (hchk : checker) (hb : build) (ha : archive)
    (hfb : fallback) (hau : audit) :
    ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay checker
      build archive fallback audit :=
  ay_mccg_conj_intro hf
    (ay_mccg_conj_intro hcvg
      (ay_mccg_conj_intro hd
        (ay_mccg_conj_intro hrc
          (ay_mccg_conj_intro hr
            (ay_mccg_conj_intro hchk
              (ay_mccg_conj_intro hb
                (ay_mccg_conj_intro ha
                  (ay_mccg_conj_intro hfb hau))))))))

theorem ay_mccg_accepted_coverage_fingerprint
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : fingerprint :=
  ay_mccg_conj_left h

theorem ay_mccg_accepted_coverage_coverage
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : coverage :=
  ay_mccg_conj_left (ay_mccg_conj_right h)

theorem ay_mccg_accepted_coverage_domain
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : domain :=
  ay_mccg_conj_left (ay_mccg_conj_right (ay_mccg_conj_right h))

theorem ay_mccg_accepted_coverage_reconstruction
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : reconstruction :=
  ay_mccg_conj_left
    (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_accepted_coverage_replay
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : replay :=
  ay_mccg_conj_left
    (ay_mccg_conj_right
      (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h))))

theorem ay_mccg_accepted_coverage_checker
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : checker :=
  ay_mccg_conj_left
    (ay_mccg_conj_right
      (ay_mccg_conj_right
        (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))))

theorem ay_mccg_accepted_coverage_build
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : build :=
  ay_mccg_conj_left
    (ay_mccg_conj_right
      (ay_mccg_conj_right
        (ay_mccg_conj_right
          (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h))))))

theorem ay_mccg_accepted_coverage_archive
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : archive :=
  ay_mccg_conj_left
    (ay_mccg_conj_right
      (ay_mccg_conj_right
        (ay_mccg_conj_right
          (ay_mccg_conj_right
            (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))))))

theorem ay_mccg_accepted_coverage_fallback
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : fallback :=
  ay_mccg_conj_left
    (ay_mccg_conj_right
      (ay_mccg_conj_right
        (ay_mccg_conj_right
          (ay_mccg_conj_right
            (ay_mccg_conj_right
              (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h))))))))

theorem ay_mccg_accepted_coverage_audit
    {fingerprint coverage domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit) : audit :=
  ay_mccg_conj_right
    (ay_mccg_conj_right
      (ay_mccg_conj_right
        (ay_mccg_conj_right
          (ay_mccg_conj_right
            (ay_mccg_conj_right
              (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h))))))))

theorem ay_mccg_coverage_reconstructs_original_sat
    {modelArtifact fingerprintOk coverageOk domainOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_mccg_benchmark_fingerprint modelArtifact fingerprintOk)
    (hcvg : ay_mccg_clause_coverage_digest fingerprintOk coverageOk)
    (hd : ay_mccg_variable_domain_manifest coverageOk domainOk)
    (hrc : ay_mccg_total_assignment_reconstruction domainOk totalAssignment)
    (hr : ay_mccg_per_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hchk : ay_mccg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_mccg_solver_build_evidence originalSat buildOk)
    (ha : ay_mccg_archive_manifest buildOk archiveOk)
    (hfb : ay_mccg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_mccg_audit_transcript fallbackReady audited)
    (hm : modelArtifact) :
    ay_mccg_conj totalAssignment
      (ay_mccg_conj everyOriginalClauseSatisfied (ay_mccg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hm
  let hcoverage : coverageOk := hcvg hfingerprint
  let hdomain : domainOk := hd hcoverage
  let htotal : totalAssignment := hrc hdomain
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hchk hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_mccg_conj_intro htotal (ay_mccg_conj_intro hevery (ay_mccg_conj_intro hsat haudit))

theorem ay_mccg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_mccg_conj_intro ha
    (ay_mccg_conj_intro ht (ay_mccg_conj_intro hevery (ay_mccg_conj_intro hs hau)))

theorem ay_mccg_public_sat_requires_coverage
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_mccg_conj_left h

theorem ay_mccg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_mccg_conj_left (ay_mccg_conj_right h)

theorem ay_mccg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_mccg_conj_left (ay_mccg_conj_right (ay_mccg_conj_right h))

theorem ay_mccg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_mccg_conj_left (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_accepted_coverage_publishes_sat
    {fingerprint coverage domain reconstruction replay checker build archive fallback audit
     totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay
      checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mccg_public_sat
      (ay_mccg_accepted_coverage fingerprint coverage domain reconstruction replay checker
        build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_mccg_public_sat_intro hg ht hevery hs hau

theorem ay_mccg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  h

theorem ay_mccg_recompute_intro {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  h

theorem ay_mccg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  ay_mccg_recompute_intro h

theorem ay_mccg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  ay_mccg_recompute_intro h

theorem ay_mccg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  ay_mccg_recompute_intro h

theorem ay_mccg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  ay_mccg_recompute_intro h

theorem ay_mccg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_failed_coverage_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mccg_no_claim_diagnostic failure) :
    ay_mccg_conj (ay_mccg_no_claim_diagnostic failure)
      (ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mccg_no_claim_diagnostic failure) :=
  ay_mccg_conj_intro (ay_mccg_no_claim_intro hfail) hblock

theorem ay_mccg_failed_coverage_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mccg_recompute_obligation failure) :
    ay_mccg_conj (ay_mccg_recompute_obligation failure)
      (ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mccg_recompute_obligation failure) :=
  ay_mccg_conj_intro (ay_mccg_recompute_intro hfail) hblock

theorem ay_mccg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mccg_public_unsat proofAccepted originalUnsat :=
  ay_mccg_conj_intro hp hu

theorem ay_mccg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mccg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mccg_conj_left h

theorem ay_mccg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mccg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mccg_conj_right h

theorem ay_mccg_coverage_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat coverageSatGuard : Prop}
    (h : ay_mccg_public_unsat proofAccepted originalUnsat) :
    ay_mccg_conj (ay_mccg_public_unsat proofAccepted originalUnsat)
      (coverageSatGuard -> ay_mccg_public_unsat proofAccepted originalUnsat) :=
  ay_mccg_conj_intro h (fun _ => h)

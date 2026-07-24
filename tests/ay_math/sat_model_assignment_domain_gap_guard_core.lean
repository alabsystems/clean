/-!
  SAT-COMP/ay assignment domain-gap guard.

  This self-contained package models the SAT-only obligations for filling gaps
  in a partial assignment before publishing a total model for the original
  sequential-main benchmark.
-/

def ay_mdg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mdg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mdg_equiv (p q : Prop) : Prop :=
  ay_mdg_conj (p -> q) (q -> p)

def ay_mdg_benchmark_fingerprint (partialAssignment fingerprintOk : Prop) : Prop :=
  partialAssignment -> fingerprintOk

def ay_mdg_declared_variable_domain_manifest (fingerprintOk domainOk : Prop) : Prop :=
  fingerprintOk -> domainOk

def ay_mdg_assigned_variable_ledger (domainOk assignedOk : Prop) : Prop :=
  domainOk -> assignedOk

def ay_mdg_gap_fill_policy_witness (assignedOk gapFillOk : Prop) : Prop :=
  assignedOk -> gapFillOk

def ay_mdg_total_assignment_reconstruction (gapFillOk totalAssignment : Prop) : Prop :=
  gapFillOk -> totalAssignment

def ay_mdg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_mdg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_mdg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_mdg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mdg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mdg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mdg_accepted_domain_gap
    (fingerprint domain assigned gap reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_mdg_conj fingerprint
    (ay_mdg_conj domain
      (ay_mdg_conj assigned
        (ay_mdg_conj gap
          (ay_mdg_conj reconstruction
            (ay_mdg_conj replay
              (ay_mdg_conj checker
                (ay_mdg_conj build
                  (ay_mdg_conj archive
                    (ay_mdg_conj fallback audit)))))))))

def ay_mdg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_mdg_conj accepted
    (ay_mdg_conj totalAssignment
      (ay_mdg_conj everyOriginalClauseSatisfied (ay_mdg_conj originalSat audited)))

def ay_mdg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mdg_conj proofAccepted originalUnsat

def ay_mdg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mdg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mdg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mdg_conj p q :=
  fun r h => h hp hq

theorem ay_mdg_conj_left {p q : Prop} (h : ay_mdg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mdg_conj_right {p q : Prop} (h : ay_mdg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mdg_conj_left h)

theorem ay_mdg_disj_left {p q : Prop} (hp : p) : ay_mdg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mdg_disj_right {p q : Prop} (hq : q) : ay_mdg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mdg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mdg_equiv p q :=
  ay_mdg_conj_intro hpq hqp

theorem ay_mdg_equiv_forward {p q : Prop} (h : ay_mdg_equiv p q) : p -> q :=
  ay_mdg_conj_left h

theorem ay_mdg_equiv_backward {p q : Prop} (h : ay_mdg_equiv p q) : q -> p :=
  ay_mdg_conj_right h

theorem ay_mdg_benchmark_fingerprint_intro {partialAssignment fingerprintOk : Prop}
    (h : partialAssignment -> fingerprintOk) :
    ay_mdg_benchmark_fingerprint partialAssignment fingerprintOk :=
  h

theorem ay_mdg_declared_variable_domain_manifest_intro {fingerprintOk domainOk : Prop}
    (h : fingerprintOk -> domainOk) :
    ay_mdg_declared_variable_domain_manifest fingerprintOk domainOk :=
  h

theorem ay_mdg_assigned_variable_ledger_intro {domainOk assignedOk : Prop}
    (h : domainOk -> assignedOk) :
    ay_mdg_assigned_variable_ledger domainOk assignedOk :=
  h

theorem ay_mdg_gap_fill_policy_witness_intro {assignedOk gapFillOk : Prop}
    (h : assignedOk -> gapFillOk) :
    ay_mdg_gap_fill_policy_witness assignedOk gapFillOk :=
  h

theorem ay_mdg_total_assignment_reconstruction_intro {gapFillOk totalAssignment : Prop}
    (h : gapFillOk -> totalAssignment) :
    ay_mdg_total_assignment_reconstruction gapFillOk totalAssignment :=
  h

theorem ay_mdg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_mdg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_mdg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_mdg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_mdg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_mdg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_mdg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mdg_archive_manifest buildOk archiveOk :=
  h

theorem ay_mdg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mdg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mdg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mdg_audit_transcript fallbackReady audited :=
  h

theorem ay_mdg_accepted_domain_gap_intro
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hd : domain) (ha : assigned) (hg : gap)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay checker
      build archive fallback audit :=
  ay_mdg_conj_intro hf
    (ay_mdg_conj_intro hd
      (ay_mdg_conj_intro ha
        (ay_mdg_conj_intro hg
          (ay_mdg_conj_intro hrc
            (ay_mdg_conj_intro hr
              (ay_mdg_conj_intro hc
                (ay_mdg_conj_intro hb
                  (ay_mdg_conj_intro har
                    (ay_mdg_conj_intro hfb hau)))))))))

theorem ay_mdg_accepted_domain_gap_fingerprint
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : fingerprint :=
  ay_mdg_conj_left h

theorem ay_mdg_accepted_domain_gap_domain
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : domain :=
  ay_mdg_conj_left (ay_mdg_conj_right h)

theorem ay_mdg_accepted_domain_gap_assigned
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : assigned :=
  ay_mdg_conj_left (ay_mdg_conj_right (ay_mdg_conj_right h))

theorem ay_mdg_accepted_domain_gap_gap
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : gap :=
  ay_mdg_conj_left
    (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))

theorem ay_mdg_accepted_domain_gap_reconstruction
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : reconstruction :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h))))

theorem ay_mdg_accepted_domain_gap_replay
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : replay :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))))

theorem ay_mdg_accepted_domain_gap_checker
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : checker :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right
          (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h))))))

theorem ay_mdg_accepted_domain_gap_build
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : build :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right
          (ay_mdg_conj_right
            (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))))))

theorem ay_mdg_accepted_domain_gap_archive
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : archive :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right
          (ay_mdg_conj_right
            (ay_mdg_conj_right
              (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h))))))))

theorem ay_mdg_accepted_domain_gap_fallback
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : fallback :=
  ay_mdg_conj_left
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right
          (ay_mdg_conj_right
            (ay_mdg_conj_right
              (ay_mdg_conj_right
                (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))))))))

theorem ay_mdg_accepted_domain_gap_audit
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit) : audit :=
  ay_mdg_conj_right
    (ay_mdg_conj_right
      (ay_mdg_conj_right
        (ay_mdg_conj_right
          (ay_mdg_conj_right
            (ay_mdg_conj_right
              (ay_mdg_conj_right
                (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))))))))

theorem ay_mdg_domain_gap_reconstructs_original_sat
    {partialAssignment fingerprintOk domainOk assignedOk gapFillOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_mdg_benchmark_fingerprint partialAssignment fingerprintOk)
    (hd : ay_mdg_declared_variable_domain_manifest fingerprintOk domainOk)
    (ha : ay_mdg_assigned_variable_ledger domainOk assignedOk)
    (hg : ay_mdg_gap_fill_policy_witness assignedOk gapFillOk)
    (hrc : ay_mdg_total_assignment_reconstruction gapFillOk totalAssignment)
    (hr : ay_mdg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_mdg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_mdg_solver_build_evidence originalSat buildOk)
    (har : ay_mdg_archive_manifest buildOk archiveOk)
    (hfb : ay_mdg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_mdg_audit_transcript fallbackReady audited)
    (hw : partialAssignment) :
    ay_mdg_conj totalAssignment
      (ay_mdg_conj everyOriginalClauseSatisfied (ay_mdg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hdomain : domainOk := hd hfingerprint
  let hassigned : assignedOk := ha hdomain
  let hgap : gapFillOk := hg hassigned
  let htotal : totalAssignment := hrc hgap
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := har hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_mdg_conj_intro htotal (ay_mdg_conj_intro hevery (ay_mdg_conj_intro hsat haudit))

theorem ay_mdg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_mdg_conj_intro ha
    (ay_mdg_conj_intro ht (ay_mdg_conj_intro hevery (ay_mdg_conj_intro hs hau)))

theorem ay_mdg_public_sat_requires_domain_gap
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_mdg_conj_left h

theorem ay_mdg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_mdg_conj_left (ay_mdg_conj_right h)

theorem ay_mdg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_mdg_conj_left (ay_mdg_conj_right (ay_mdg_conj_right h))

theorem ay_mdg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_mdg_conj_left (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))

theorem ay_mdg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right (ay_mdg_conj_right h)))

theorem ay_mdg_accepted_domain_gap_publishes_sat
    {fingerprint domain assigned gap reconstruction replay checker build archive fallback
     audit totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
      checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mdg_public_sat
      (ay_mdg_accepted_domain_gap fingerprint domain assigned gap reconstruction replay
        checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_mdg_public_sat_intro hg ht hevery hs hau

theorem ay_mdg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  h

theorem ay_mdg_recompute_intro {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  h

theorem ay_mdg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  ay_mdg_recompute_intro h

theorem ay_mdg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  ay_mdg_no_claim_intro h

theorem ay_mdg_assigned_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  ay_mdg_no_claim_intro h

theorem ay_mdg_gap_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  ay_mdg_recompute_intro h

theorem ay_mdg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  ay_mdg_recompute_intro h

theorem ay_mdg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  ay_mdg_recompute_intro h

theorem ay_mdg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  ay_mdg_no_claim_intro h

theorem ay_mdg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mdg_recompute_obligation reason :=
  ay_mdg_recompute_intro h

theorem ay_mdg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  ay_mdg_no_claim_intro h

theorem ay_mdg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mdg_no_claim_diagnostic reason :=
  ay_mdg_no_claim_intro h

theorem ay_mdg_failed_domain_gap_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mdg_no_claim_diagnostic failure) :
    ay_mdg_conj (ay_mdg_no_claim_diagnostic failure)
      (ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mdg_no_claim_diagnostic failure) :=
  ay_mdg_conj_intro (ay_mdg_no_claim_intro hfail) hblock

theorem ay_mdg_failed_domain_gap_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mdg_recompute_obligation failure) :
    ay_mdg_conj (ay_mdg_recompute_obligation failure)
      (ay_mdg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mdg_recompute_obligation failure) :=
  ay_mdg_conj_intro (ay_mdg_recompute_intro hfail) hblock

theorem ay_mdg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mdg_public_unsat proofAccepted originalUnsat :=
  ay_mdg_conj_intro hp hu

theorem ay_mdg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mdg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mdg_conj_left h

theorem ay_mdg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mdg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mdg_conj_right h

theorem ay_mdg_domain_gap_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat domainGapSatGuard : Prop}
    (h : ay_mdg_public_unsat proofAccepted originalUnsat) :
    ay_mdg_conj (ay_mdg_public_unsat proofAccepted originalUnsat)
      (domainGapSatGuard -> ay_mdg_public_unsat proofAccepted originalUnsat) :=
  ay_mdg_conj_intro h (fun _ => h)

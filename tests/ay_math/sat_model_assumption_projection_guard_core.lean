/-!
  SAT-COMP/ay assumption-projection guard.

  This self-contained package records the SAT-only obligations for publishing a
  model produced under incremental assumptions as a model for the original
  benchmark formula.
-/

def ay_aprg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_aprg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_aprg_equiv (p q : Prop) : Prop :=
  ay_aprg_conj (p -> q) (q -> p)

def ay_aprg_base_benchmark_fingerprint (assumptionModel fingerprintOk : Prop) : Prop :=
  assumptionModel -> fingerprintOk

def ay_aprg_assumption_ledger (fingerprintOk assumptionsOk : Prop) : Prop :=
  fingerprintOk -> assumptionsOk

def ay_aprg_solved_under_assumptions_witness (assumptionsOk solvedOk : Prop) : Prop :=
  assumptionsOk -> solvedOk

def ay_aprg_assumption_removal_projection_policy (solvedOk projectionOk : Prop) : Prop :=
  solvedOk -> projectionOk

def ay_aprg_total_assignment_reconstruction (projectionOk totalAssignment : Prop) : Prop :=
  projectionOk -> totalAssignment

def ay_aprg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_aprg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_aprg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_aprg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_aprg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_aprg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_aprg_accepted_projection
    (fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_aprg_conj fingerprint
    (ay_aprg_conj assumption
      (ay_aprg_conj solved
        (ay_aprg_conj projection
          (ay_aprg_conj reconstruction
            (ay_aprg_conj replay
              (ay_aprg_conj checker
                (ay_aprg_conj build
                  (ay_aprg_conj archive
                    (ay_aprg_conj fallback audit)))))))))

def ay_aprg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_aprg_conj accepted (ay_aprg_conj totalAssignment (ay_aprg_conj originalSat audited))

def ay_aprg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_aprg_conj proofAccepted originalUnsat

def ay_aprg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_aprg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_aprg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_aprg_conj p q :=
  fun r h => h hp hq

theorem ay_aprg_conj_left {p q : Prop} (h : ay_aprg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_aprg_conj_right {p q : Prop} (h : ay_aprg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_aprg_conj_left h)

theorem ay_aprg_disj_left {p q : Prop} (hp : p) : ay_aprg_disj p q :=
  fun r hl _ => hl hp

theorem ay_aprg_disj_right {p q : Prop} (hq : q) : ay_aprg_disj p q :=
  fun r _ hr => hr hq

theorem ay_aprg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_aprg_equiv p q :=
  ay_aprg_conj_intro hpq hqp

theorem ay_aprg_equiv_forward {p q : Prop} (h : ay_aprg_equiv p q) : p -> q :=
  ay_aprg_conj_left h

theorem ay_aprg_equiv_backward {p q : Prop} (h : ay_aprg_equiv p q) : q -> p :=
  ay_aprg_conj_right h

theorem ay_aprg_base_benchmark_fingerprint_intro {assumptionModel fingerprintOk : Prop}
    (h : assumptionModel -> fingerprintOk) :
    ay_aprg_base_benchmark_fingerprint assumptionModel fingerprintOk :=
  h

theorem ay_aprg_assumption_ledger_intro {fingerprintOk assumptionsOk : Prop}
    (h : fingerprintOk -> assumptionsOk) :
    ay_aprg_assumption_ledger fingerprintOk assumptionsOk :=
  h

theorem ay_aprg_solved_under_assumptions_witness_intro {assumptionsOk solvedOk : Prop}
    (h : assumptionsOk -> solvedOk) :
    ay_aprg_solved_under_assumptions_witness assumptionsOk solvedOk :=
  h

theorem ay_aprg_assumption_removal_projection_policy_intro {solvedOk projectionOk : Prop}
    (h : solvedOk -> projectionOk) :
    ay_aprg_assumption_removal_projection_policy solvedOk projectionOk :=
  h

theorem ay_aprg_total_assignment_reconstruction_intro {projectionOk totalAssignment : Prop}
    (h : projectionOk -> totalAssignment) :
    ay_aprg_total_assignment_reconstruction projectionOk totalAssignment :=
  h

theorem ay_aprg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_aprg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_aprg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_aprg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_aprg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_aprg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_aprg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_aprg_archive_manifest buildOk archiveOk :=
  h

theorem ay_aprg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_aprg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_aprg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_aprg_audit_transcript fallbackReady audited :=
  h

theorem ay_aprg_accepted_projection_intro
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (ha : assumption) (hs : solved) (hp : projection)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit :=
  ay_aprg_conj_intro hf
    (ay_aprg_conj_intro ha
      (ay_aprg_conj_intro hs
        (ay_aprg_conj_intro hp
          (ay_aprg_conj_intro hrc
            (ay_aprg_conj_intro hr
              (ay_aprg_conj_intro hc
                (ay_aprg_conj_intro hb
                  (ay_aprg_conj_intro har
                    (ay_aprg_conj_intro hfb hau)))))))))

theorem ay_aprg_accepted_projection_fingerprint
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : fingerprint :=
  ay_aprg_conj_left h

theorem ay_aprg_accepted_projection_assumption
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : assumption :=
  ay_aprg_conj_left (ay_aprg_conj_right h)

theorem ay_aprg_accepted_projection_solved
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : solved :=
  ay_aprg_conj_left (ay_aprg_conj_right (ay_aprg_conj_right h))

theorem ay_aprg_accepted_projection_policy
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : projection :=
  ay_aprg_conj_left
    (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h)))

theorem ay_aprg_accepted_projection_reconstruction
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : reconstruction :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h))))

theorem ay_aprg_accepted_projection_replay
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : replay :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h)))))

theorem ay_aprg_accepted_projection_checker
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : checker :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right
          (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h))))))

theorem ay_aprg_accepted_projection_build
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : build :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right
          (ay_aprg_conj_right
            (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h)))))))

theorem ay_aprg_accepted_projection_archive
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : archive :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right
          (ay_aprg_conj_right
            (ay_aprg_conj_right
              (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h))))))))

theorem ay_aprg_accepted_projection_fallback
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : fallback :=
  ay_aprg_conj_left
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right
          (ay_aprg_conj_right
            (ay_aprg_conj_right
              (ay_aprg_conj_right
                (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h)))))))))

theorem ay_aprg_accepted_projection_audit
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_aprg_accepted_projection fingerprint assumption solved projection reconstruction
      replay checker build archive fallback audit) : audit :=
  ay_aprg_conj_right
    (ay_aprg_conj_right
      (ay_aprg_conj_right
        (ay_aprg_conj_right
          (ay_aprg_conj_right
            (ay_aprg_conj_right
              (ay_aprg_conj_right
                (ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h)))))))))

theorem ay_aprg_assumption_projection_reconstructs_original_sat
    {assumptionModel fingerprintOk assumptionsOk solvedOk projectionOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_aprg_base_benchmark_fingerprint assumptionModel fingerprintOk)
    (ha : ay_aprg_assumption_ledger fingerprintOk assumptionsOk)
    (hs : ay_aprg_solved_under_assumptions_witness assumptionsOk solvedOk)
    (hp : ay_aprg_assumption_removal_projection_policy solvedOk projectionOk)
    (hrc : ay_aprg_total_assignment_reconstruction projectionOk totalAssignment)
    (hr : ay_aprg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_aprg_model_checker_transcript replayOk originalSat)
    (hb : ay_aprg_solver_build_evidence originalSat buildOk)
    (har : ay_aprg_archive_manifest buildOk archiveOk)
    (hfb : ay_aprg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_aprg_audit_transcript fallbackReady audited)
    (hm : assumptionModel) :
    ay_aprg_conj totalAssignment (ay_aprg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hm
  let hassumptions : assumptionsOk := ha hfingerprint
  let hsolved : solvedOk := hs hassumptions
  let hprojection : projectionOk := hp hsolved
  let htotal : totalAssignment := hrc hprojection
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := har hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_aprg_conj_intro htotal (ay_aprg_conj_intro hsat haudit)

theorem ay_aprg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_aprg_public_sat accepted totalAssignment originalSat audited :=
  ay_aprg_conj_intro ha (ay_aprg_conj_intro ht (ay_aprg_conj_intro hs hau))

theorem ay_aprg_public_sat_requires_projection
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_aprg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_aprg_conj_left h

theorem ay_aprg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_aprg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_aprg_conj_left (ay_aprg_conj_right h)

theorem ay_aprg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_aprg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_aprg_conj_left (ay_aprg_conj_right (ay_aprg_conj_right h))

theorem ay_aprg_public_sat_audited
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_aprg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_aprg_conj_right (ay_aprg_conj_right (ay_aprg_conj_right h))

theorem ay_aprg_accepted_projection_publishes_sat
    {fingerprint assumption solved projection reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_aprg_accepted_projection fingerprint assumption solved projection
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_aprg_public_sat
      (ay_aprg_accepted_projection fingerprint assumption solved projection
        reconstruction replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_aprg_public_sat_intro hg ht hs hau

theorem ay_aprg_no_claim_intro {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  h

theorem ay_aprg_recompute_intro {reason : Prop} (h : reason) :
    ay_aprg_recompute_obligation reason :=
  h

theorem ay_aprg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_aprg_recompute_obligation reason :=
  ay_aprg_recompute_intro h

theorem ay_aprg_assumption_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  ay_aprg_no_claim_intro h

theorem ay_aprg_projection_mismatch_recompute {reason : Prop} (h : reason) :
    ay_aprg_recompute_obligation reason :=
  ay_aprg_recompute_intro h

theorem ay_aprg_reconstruction_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  ay_aprg_no_claim_intro h

theorem ay_aprg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_aprg_recompute_obligation reason :=
  ay_aprg_recompute_intro h

theorem ay_aprg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  ay_aprg_no_claim_intro h

theorem ay_aprg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_aprg_recompute_obligation reason :=
  ay_aprg_recompute_intro h

theorem ay_aprg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  ay_aprg_no_claim_intro h

theorem ay_aprg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_aprg_no_claim_diagnostic reason :=
  ay_aprg_no_claim_intro h

theorem ay_aprg_failed_assumption_projection_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_aprg_public_sat accepted totalAssignment originalSat audited ->
      ay_aprg_no_claim_diagnostic failure) :
    ay_aprg_conj (ay_aprg_no_claim_diagnostic failure)
      (ay_aprg_public_sat accepted totalAssignment originalSat audited ->
        ay_aprg_no_claim_diagnostic failure) :=
  ay_aprg_conj_intro (ay_aprg_no_claim_intro hfail) hblock

theorem ay_aprg_failed_assumption_projection_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_aprg_public_sat accepted totalAssignment originalSat audited ->
      ay_aprg_recompute_obligation failure) :
    ay_aprg_conj (ay_aprg_recompute_obligation failure)
      (ay_aprg_public_sat accepted totalAssignment originalSat audited ->
        ay_aprg_recompute_obligation failure) :=
  ay_aprg_conj_intro (ay_aprg_recompute_intro hfail) hblock

theorem ay_aprg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_aprg_public_unsat proofAccepted originalUnsat :=
  ay_aprg_conj_intro hp hu

theorem ay_aprg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_aprg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_aprg_conj_left h

theorem ay_aprg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_aprg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_aprg_conj_right h

theorem ay_aprg_assumption_projection_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat assumptionSatGuard : Prop}
    (h : ay_aprg_public_unsat proofAccepted originalUnsat) :
    ay_aprg_conj (ay_aprg_public_unsat proofAccepted originalUnsat)
      (assumptionSatGuard -> ay_aprg_public_unsat proofAccepted originalUnsat) :=
  ay_aprg_conj_intro h (fun _ => h)

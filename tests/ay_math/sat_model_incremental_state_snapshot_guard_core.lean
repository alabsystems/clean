/-!
  SAT-COMP/ay incremental-state snapshot guard.

  This self-contained package records the SAT-only obligations for publishing a
  model produced after reusing incremental solver state.
-/

def ay_issg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_issg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_issg_equiv (p q : Prop) : Prop :=
  ay_issg_conj (p -> q) (q -> p)

def ay_issg_base_benchmark_fingerprint (snapshotModel fingerprintOk : Prop) : Prop :=
  snapshotModel -> fingerprintOk

def ay_issg_incremental_state_snapshot_digest (fingerprintOk snapshotOk : Prop) : Prop :=
  fingerprintOk -> snapshotOk

def ay_issg_active_assumption_ledger (snapshotOk assumptionsOk : Prop) : Prop :=
  snapshotOk -> assumptionsOk

def ay_issg_learnt_clause_compatibility_witness (assumptionsOk compatibilityOk : Prop) : Prop :=
  assumptionsOk -> compatibilityOk

def ay_issg_model_reconstruction_witness (compatibilityOk totalAssignment : Prop) : Prop :=
  compatibilityOk -> totalAssignment

def ay_issg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_issg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_issg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_issg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_issg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_issg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_issg_accepted_snapshot
    (fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_issg_conj fingerprint
    (ay_issg_conj snapshot
      (ay_issg_conj assumptions
        (ay_issg_conj compatibility
          (ay_issg_conj reconstruction
            (ay_issg_conj replay
              (ay_issg_conj checker
                (ay_issg_conj build
                  (ay_issg_conj archive
                    (ay_issg_conj fallback audit)))))))))

def ay_issg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_issg_conj accepted (ay_issg_conj totalAssignment (ay_issg_conj originalSat audited))

def ay_issg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_issg_conj proofAccepted originalUnsat

def ay_issg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_issg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_issg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_issg_conj p q :=
  fun r h => h hp hq

theorem ay_issg_conj_left {p q : Prop} (h : ay_issg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_issg_conj_right {p q : Prop} (h : ay_issg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_issg_conj_left h)

theorem ay_issg_disj_left {p q : Prop} (hp : p) : ay_issg_disj p q :=
  fun r hl _ => hl hp

theorem ay_issg_disj_right {p q : Prop} (hq : q) : ay_issg_disj p q :=
  fun r _ hr => hr hq

theorem ay_issg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_issg_equiv p q :=
  ay_issg_conj_intro hpq hqp

theorem ay_issg_equiv_forward {p q : Prop} (h : ay_issg_equiv p q) : p -> q :=
  ay_issg_conj_left h

theorem ay_issg_equiv_backward {p q : Prop} (h : ay_issg_equiv p q) : q -> p :=
  ay_issg_conj_right h

theorem ay_issg_base_benchmark_fingerprint_intro {snapshotModel fingerprintOk : Prop}
    (h : snapshotModel -> fingerprintOk) :
    ay_issg_base_benchmark_fingerprint snapshotModel fingerprintOk :=
  h

theorem ay_issg_incremental_state_snapshot_digest_intro {fingerprintOk snapshotOk : Prop}
    (h : fingerprintOk -> snapshotOk) :
    ay_issg_incremental_state_snapshot_digest fingerprintOk snapshotOk :=
  h

theorem ay_issg_active_assumption_ledger_intro {snapshotOk assumptionsOk : Prop}
    (h : snapshotOk -> assumptionsOk) :
    ay_issg_active_assumption_ledger snapshotOk assumptionsOk :=
  h

theorem ay_issg_learnt_clause_compatibility_witness_intro
    {assumptionsOk compatibilityOk : Prop}
    (h : assumptionsOk -> compatibilityOk) :
    ay_issg_learnt_clause_compatibility_witness assumptionsOk compatibilityOk :=
  h

theorem ay_issg_model_reconstruction_witness_intro {compatibilityOk totalAssignment : Prop}
    (h : compatibilityOk -> totalAssignment) :
    ay_issg_model_reconstruction_witness compatibilityOk totalAssignment :=
  h

theorem ay_issg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_issg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_issg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_issg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_issg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_issg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_issg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_issg_archive_manifest buildOk archiveOk :=
  h

theorem ay_issg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_issg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_issg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_issg_audit_transcript fallbackReady audited :=
  h

theorem ay_issg_accepted_snapshot_intro
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hsnap : snapshot) (ha : assumptions) (hcpt : compatibility)
    (hrc : reconstruction) (hr : replay) (hchk : checker) (hb : build)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility reconstruction
      replay checker build archive fallback audit :=
  ay_issg_conj_intro hf
    (ay_issg_conj_intro hsnap
      (ay_issg_conj_intro ha
        (ay_issg_conj_intro hcpt
          (ay_issg_conj_intro hrc
            (ay_issg_conj_intro hr
              (ay_issg_conj_intro hchk
                (ay_issg_conj_intro hb
                  (ay_issg_conj_intro har
                    (ay_issg_conj_intro hfb hau)))))))))

theorem ay_issg_accepted_snapshot_fingerprint
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_issg_conj_left h

theorem ay_issg_accepted_snapshot_snapshot
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : snapshot :=
  ay_issg_conj_left (ay_issg_conj_right h)

theorem ay_issg_accepted_snapshot_assumptions
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : assumptions :=
  ay_issg_conj_left (ay_issg_conj_right (ay_issg_conj_right h))

theorem ay_issg_accepted_snapshot_compatibility
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : compatibility :=
  ay_issg_conj_left
    (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h)))

theorem ay_issg_accepted_snapshot_reconstruction
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h))))

theorem ay_issg_accepted_snapshot_replay
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h)))))

theorem ay_issg_accepted_snapshot_checker
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right
          (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h))))))

theorem ay_issg_accepted_snapshot_build
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : build :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right
          (ay_issg_conj_right
            (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h)))))))

theorem ay_issg_accepted_snapshot_archive
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right
          (ay_issg_conj_right
            (ay_issg_conj_right
              (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h))))))))

theorem ay_issg_accepted_snapshot_fallback
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_issg_conj_left
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right
          (ay_issg_conj_right
            (ay_issg_conj_right
              (ay_issg_conj_right
                (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h)))))))))

theorem ay_issg_accepted_snapshot_audit
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_issg_conj_right
    (ay_issg_conj_right
      (ay_issg_conj_right
        (ay_issg_conj_right
          (ay_issg_conj_right
            (ay_issg_conj_right
              (ay_issg_conj_right
                (ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h)))))))))

theorem ay_issg_snapshot_reconstructs_original_sat
    {snapshotModel fingerprintOk snapshotOk assumptionsOk compatibilityOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_issg_base_benchmark_fingerprint snapshotModel fingerprintOk)
    (hsnap : ay_issg_incremental_state_snapshot_digest fingerprintOk snapshotOk)
    (ha : ay_issg_active_assumption_ledger snapshotOk assumptionsOk)
    (hcpt : ay_issg_learnt_clause_compatibility_witness assumptionsOk compatibilityOk)
    (hrc : ay_issg_model_reconstruction_witness compatibilityOk totalAssignment)
    (hr : ay_issg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hchk : ay_issg_model_checker_transcript replayOk originalSat)
    (hb : ay_issg_solver_build_evidence originalSat buildOk)
    (har : ay_issg_archive_manifest buildOk archiveOk)
    (hfb : ay_issg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_issg_audit_transcript fallbackReady audited)
    (hm : snapshotModel) :
    ay_issg_conj totalAssignment (ay_issg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hm
  let hsnapshot : snapshotOk := hsnap hfingerprint
  let hassumptions : assumptionsOk := ha hsnapshot
  let hcompat : compatibilityOk := hcpt hassumptions
  let htotal : totalAssignment := hrc hcompat
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hchk hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := har hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_issg_conj_intro htotal (ay_issg_conj_intro hsat haudit)

theorem ay_issg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_issg_public_sat accepted totalAssignment originalSat audited :=
  ay_issg_conj_intro ha (ay_issg_conj_intro ht (ay_issg_conj_intro hs hau))

theorem ay_issg_public_sat_requires_snapshot_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_issg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_issg_conj_left h

theorem ay_issg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_issg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_issg_conj_left (ay_issg_conj_right h)

theorem ay_issg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_issg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_issg_conj_left (ay_issg_conj_right (ay_issg_conj_right h))

theorem ay_issg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_issg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_issg_conj_right (ay_issg_conj_right (ay_issg_conj_right h))

theorem ay_issg_accepted_snapshot_publishes_sat
    {fingerprint snapshot assumptions compatibility reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_issg_public_sat
      (ay_issg_accepted_snapshot fingerprint snapshot assumptions compatibility
        reconstruction replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_issg_public_sat_intro hg ht hs hau

theorem ay_issg_no_claim_intro {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  h

theorem ay_issg_recompute_intro {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  h

theorem ay_issg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  ay_issg_recompute_intro h

theorem ay_issg_snapshot_mismatch_recompute {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  ay_issg_recompute_intro h

theorem ay_issg_assumption_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  ay_issg_no_claim_intro h

theorem ay_issg_compatibility_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  ay_issg_no_claim_intro h

theorem ay_issg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  ay_issg_recompute_intro h

theorem ay_issg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  ay_issg_recompute_intro h

theorem ay_issg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  ay_issg_no_claim_intro h

theorem ay_issg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_issg_recompute_obligation reason :=
  ay_issg_recompute_intro h

theorem ay_issg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  ay_issg_no_claim_intro h

theorem ay_issg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_issg_no_claim_diagnostic reason :=
  ay_issg_no_claim_intro h

theorem ay_issg_failed_snapshot_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_issg_public_sat accepted totalAssignment originalSat audited ->
      ay_issg_no_claim_diagnostic failure) :
    ay_issg_conj (ay_issg_no_claim_diagnostic failure)
      (ay_issg_public_sat accepted totalAssignment originalSat audited ->
        ay_issg_no_claim_diagnostic failure) :=
  ay_issg_conj_intro (ay_issg_no_claim_intro hfail) hblock

theorem ay_issg_failed_snapshot_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_issg_public_sat accepted totalAssignment originalSat audited ->
      ay_issg_recompute_obligation failure) :
    ay_issg_conj (ay_issg_recompute_obligation failure)
      (ay_issg_public_sat accepted totalAssignment originalSat audited ->
        ay_issg_recompute_obligation failure) :=
  ay_issg_conj_intro (ay_issg_recompute_intro hfail) hblock

theorem ay_issg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_issg_public_unsat proofAccepted originalUnsat :=
  ay_issg_conj_intro hp hu

theorem ay_issg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_issg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_issg_conj_left h

theorem ay_issg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_issg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_issg_conj_right h

theorem ay_issg_snapshot_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat snapshotSatGuard : Prop}
    (h : ay_issg_public_unsat proofAccepted originalUnsat) :
    ay_issg_conj (ay_issg_public_unsat proofAccepted originalUnsat)
      (snapshotSatGuard -> ay_issg_public_unsat proofAccepted originalUnsat) :=
  ay_issg_conj_intro h (fun _ => h)

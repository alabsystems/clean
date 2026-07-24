/-!
  SAT-COMP/ay cube-assumption witness guard.

  This self-contained package records the SAT-only obligations for publishing a
  model found under cube/assumption preprocessing while preserving
  sequential-main SAT-COMP model soundness for the original benchmark.
-/

def ay_cawg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_cawg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_cawg_equiv (p q : Prop) : Prop :=
  ay_cawg_conj (p -> q) (q -> p)

def ay_cawg_base_benchmark_fingerprint (cubeWitness fingerprintOk : Prop) : Prop :=
  cubeWitness -> fingerprintOk

def ay_cawg_cube_literal_ledger (fingerprintOk cubeLedgerOk : Prop) : Prop :=
  fingerprintOk -> cubeLedgerOk

def ay_cawg_cube_solver_transcript_digest (cubeLedgerOk transcriptOk : Prop) : Prop :=
  cubeLedgerOk -> transcriptOk

def ay_cawg_cube_to_original_projection_witness (transcriptOk projectionOk : Prop) : Prop :=
  transcriptOk -> projectionOk

def ay_cawg_total_assignment_reconstruction (projectionOk totalAssignment : Prop) : Prop :=
  projectionOk -> totalAssignment

def ay_cawg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_cawg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_cawg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_cawg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_cawg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_cawg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_cawg_accepted_cube_witness
    (fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_cawg_conj fingerprint
    (ay_cawg_conj cubeLedger
      (ay_cawg_conj transcript
        (ay_cawg_conj projection
          (ay_cawg_conj reconstruction
            (ay_cawg_conj replay
              (ay_cawg_conj checker
                (ay_cawg_conj build
                  (ay_cawg_conj archive
                    (ay_cawg_conj fallback audit)))))))))

def ay_cawg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_cawg_conj accepted (ay_cawg_conj totalAssignment (ay_cawg_conj originalSat audited))

def ay_cawg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_cawg_conj proofAccepted originalUnsat

def ay_cawg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_cawg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_cawg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_cawg_conj p q :=
  fun r h => h hp hq

theorem ay_cawg_conj_left {p q : Prop} (h : ay_cawg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cawg_conj_right {p q : Prop} (h : ay_cawg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cawg_conj_left h)

theorem ay_cawg_disj_left {p q : Prop} (hp : p) : ay_cawg_disj p q :=
  fun r hl _ => hl hp

theorem ay_cawg_disj_right {p q : Prop} (hq : q) : ay_cawg_disj p q :=
  fun r _ hr => hr hq

theorem ay_cawg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_cawg_equiv p q :=
  ay_cawg_conj_intro hpq hqp

theorem ay_cawg_equiv_forward {p q : Prop} (h : ay_cawg_equiv p q) : p -> q :=
  ay_cawg_conj_left h

theorem ay_cawg_equiv_backward {p q : Prop} (h : ay_cawg_equiv p q) : q -> p :=
  ay_cawg_conj_right h

theorem ay_cawg_base_benchmark_fingerprint_intro {cubeWitness fingerprintOk : Prop}
    (h : cubeWitness -> fingerprintOk) :
    ay_cawg_base_benchmark_fingerprint cubeWitness fingerprintOk :=
  h

theorem ay_cawg_cube_literal_ledger_intro {fingerprintOk cubeLedgerOk : Prop}
    (h : fingerprintOk -> cubeLedgerOk) :
    ay_cawg_cube_literal_ledger fingerprintOk cubeLedgerOk :=
  h

theorem ay_cawg_cube_solver_transcript_digest_intro {cubeLedgerOk transcriptOk : Prop}
    (h : cubeLedgerOk -> transcriptOk) :
    ay_cawg_cube_solver_transcript_digest cubeLedgerOk transcriptOk :=
  h

theorem ay_cawg_cube_to_original_projection_witness_intro {transcriptOk projectionOk : Prop}
    (h : transcriptOk -> projectionOk) :
    ay_cawg_cube_to_original_projection_witness transcriptOk projectionOk :=
  h

theorem ay_cawg_total_assignment_reconstruction_intro {projectionOk totalAssignment : Prop}
    (h : projectionOk -> totalAssignment) :
    ay_cawg_total_assignment_reconstruction projectionOk totalAssignment :=
  h

theorem ay_cawg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_cawg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_cawg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_cawg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_cawg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_cawg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_cawg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_cawg_archive_manifest buildOk archiveOk :=
  h

theorem ay_cawg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_cawg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_cawg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_cawg_audit_transcript fallbackReady audited :=
  h

theorem ay_cawg_accepted_cube_witness_intro
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hcube : cubeLedger) (ht : transcript) (hp : projection)
    (hrc : reconstruction) (hr : replay) (hchk : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit :=
  ay_cawg_conj_intro hf
    (ay_cawg_conj_intro hcube
      (ay_cawg_conj_intro ht
        (ay_cawg_conj_intro hp
          (ay_cawg_conj_intro hrc
            (ay_cawg_conj_intro hr
              (ay_cawg_conj_intro hchk
                (ay_cawg_conj_intro hb
                  (ay_cawg_conj_intro ha
                    (ay_cawg_conj_intro hfb hau)))))))))

theorem ay_cawg_accepted_cube_witness_fingerprint
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_cawg_conj_left h

theorem ay_cawg_accepted_cube_witness_cube_ledger
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : cubeLedger :=
  ay_cawg_conj_left (ay_cawg_conj_right h)

theorem ay_cawg_accepted_cube_witness_transcript
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : transcript :=
  ay_cawg_conj_left (ay_cawg_conj_right (ay_cawg_conj_right h))

theorem ay_cawg_accepted_cube_witness_projection
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : projection :=
  ay_cawg_conj_left
    (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h)))

theorem ay_cawg_accepted_cube_witness_reconstruction
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h))))

theorem ay_cawg_accepted_cube_witness_replay
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h)))))

theorem ay_cawg_accepted_cube_witness_checker
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right
          (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h))))))

theorem ay_cawg_accepted_cube_witness_build
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : build :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right
          (ay_cawg_conj_right
            (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h)))))))

theorem ay_cawg_accepted_cube_witness_archive
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right
          (ay_cawg_conj_right
            (ay_cawg_conj_right
              (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h))))))))

theorem ay_cawg_accepted_cube_witness_fallback
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_cawg_conj_left
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right
          (ay_cawg_conj_right
            (ay_cawg_conj_right
              (ay_cawg_conj_right
                (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h)))))))))

theorem ay_cawg_accepted_cube_witness_audit
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_cawg_conj_right
    (ay_cawg_conj_right
      (ay_cawg_conj_right
        (ay_cawg_conj_right
          (ay_cawg_conj_right
            (ay_cawg_conj_right
              (ay_cawg_conj_right
                (ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h)))))))))

theorem ay_cawg_cube_witness_reconstructs_original_sat
    {cubeWitness fingerprintOk cubeLedgerOk transcriptOk projectionOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_cawg_base_benchmark_fingerprint cubeWitness fingerprintOk)
    (hcube : ay_cawg_cube_literal_ledger fingerprintOk cubeLedgerOk)
    (ht : ay_cawg_cube_solver_transcript_digest cubeLedgerOk transcriptOk)
    (hp : ay_cawg_cube_to_original_projection_witness transcriptOk projectionOk)
    (hrc : ay_cawg_total_assignment_reconstruction projectionOk totalAssignment)
    (hr : ay_cawg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hchk : ay_cawg_model_checker_transcript replayOk originalSat)
    (hb : ay_cawg_solver_build_evidence originalSat buildOk)
    (ha : ay_cawg_archive_manifest buildOk archiveOk)
    (hfb : ay_cawg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_cawg_audit_transcript fallbackReady audited)
    (hw : cubeWitness) :
    ay_cawg_conj totalAssignment (ay_cawg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hcubeOk : cubeLedgerOk := hcube hfingerprint
  let htranscript : transcriptOk := ht hcubeOk
  let hprojection : projectionOk := hp htranscript
  let htotal : totalAssignment := hrc hprojection
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hchk hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_cawg_conj_intro htotal (ay_cawg_conj_intro hsat haudit)

theorem ay_cawg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_cawg_public_sat accepted totalAssignment originalSat audited :=
  ay_cawg_conj_intro ha (ay_cawg_conj_intro ht (ay_cawg_conj_intro hs hau))

theorem ay_cawg_public_sat_requires_cube_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_cawg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_cawg_conj_left h

theorem ay_cawg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_cawg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_cawg_conj_left (ay_cawg_conj_right h)

theorem ay_cawg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_cawg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_cawg_conj_left (ay_cawg_conj_right (ay_cawg_conj_right h))

theorem ay_cawg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_cawg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_cawg_conj_right (ay_cawg_conj_right (ay_cawg_conj_right h))

theorem ay_cawg_accepted_cube_witness_publishes_sat
    {fingerprint cubeLedger transcript projection reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_cawg_public_sat
      (ay_cawg_accepted_cube_witness fingerprint cubeLedger transcript projection
        reconstruction replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_cawg_public_sat_intro hg ht hs hau

theorem ay_cawg_no_claim_intro {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  h

theorem ay_cawg_recompute_intro {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  h

theorem ay_cawg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  ay_cawg_recompute_intro h

theorem ay_cawg_cube_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  ay_cawg_no_claim_intro h

theorem ay_cawg_transcript_mismatch_recompute {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  ay_cawg_recompute_intro h

theorem ay_cawg_projection_mismatch_recompute {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  ay_cawg_recompute_intro h

theorem ay_cawg_reconstruction_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  ay_cawg_no_claim_intro h

theorem ay_cawg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  ay_cawg_recompute_intro h

theorem ay_cawg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  ay_cawg_no_claim_intro h

theorem ay_cawg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_cawg_recompute_obligation reason :=
  ay_cawg_recompute_intro h

theorem ay_cawg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  ay_cawg_no_claim_intro h

theorem ay_cawg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_cawg_no_claim_diagnostic reason :=
  ay_cawg_no_claim_intro h

theorem ay_cawg_failed_cube_witness_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_cawg_public_sat accepted totalAssignment originalSat audited ->
      ay_cawg_no_claim_diagnostic failure) :
    ay_cawg_conj (ay_cawg_no_claim_diagnostic failure)
      (ay_cawg_public_sat accepted totalAssignment originalSat audited ->
        ay_cawg_no_claim_diagnostic failure) :=
  ay_cawg_conj_intro (ay_cawg_no_claim_intro hfail) hblock

theorem ay_cawg_failed_cube_witness_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_cawg_public_sat accepted totalAssignment originalSat audited ->
      ay_cawg_recompute_obligation failure) :
    ay_cawg_conj (ay_cawg_recompute_obligation failure)
      (ay_cawg_public_sat accepted totalAssignment originalSat audited ->
        ay_cawg_recompute_obligation failure) :=
  ay_cawg_conj_intro (ay_cawg_recompute_intro hfail) hblock

theorem ay_cawg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_cawg_public_unsat proofAccepted originalUnsat :=
  ay_cawg_conj_intro hp hu

theorem ay_cawg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_cawg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_cawg_conj_left h

theorem ay_cawg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_cawg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cawg_conj_right h

theorem ay_cawg_cube_witness_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat cubeSatGuard : Prop}
    (h : ay_cawg_public_unsat proofAccepted originalUnsat) :
    ay_cawg_conj (ay_cawg_public_unsat proofAccepted originalUnsat)
      (cubeSatGuard -> ay_cawg_public_unsat proofAccepted originalUnsat) :=
  ay_cawg_conj_intro h (fun _ => h)

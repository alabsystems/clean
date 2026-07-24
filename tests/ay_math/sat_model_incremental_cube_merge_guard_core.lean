/-!
  SAT-COMP/ay incremental cube-merge guard.

  This self-contained package models the SAT-only obligations for publishing a
  model merged from multiple assumption/cube frames.
-/

def ay_icmg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_icmg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_icmg_equiv (p q : Prop) : Prop :=
  ay_icmg_conj (p -> q) (q -> p)

def ay_icmg_benchmark_fingerprint (cubeMergeWitness fingerprintOk : Prop) : Prop :=
  cubeMergeWitness -> fingerprintOk

def ay_icmg_cube_frame_ledger (fingerprintOk frameOk : Prop) : Prop :=
  fingerprintOk -> frameOk

def ay_icmg_merge_policy_witness (frameOk mergeOk : Prop) : Prop :=
  frameOk -> mergeOk

def ay_icmg_conflict_free_assignment_merge_witness (mergeOk conflictFreeOk : Prop) : Prop :=
  mergeOk -> conflictFreeOk

def ay_icmg_total_assignment_reconstruction (conflictFreeOk totalAssignment : Prop) : Prop :=
  conflictFreeOk -> totalAssignment

def ay_icmg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_icmg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_icmg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_icmg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_icmg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_icmg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_icmg_accepted_cube_merge
    (fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_icmg_conj fingerprint
    (ay_icmg_conj frame
      (ay_icmg_conj merge
        (ay_icmg_conj conflictFree
          (ay_icmg_conj reconstruction
            (ay_icmg_conj replay
              (ay_icmg_conj checker
                (ay_icmg_conj build
                  (ay_icmg_conj archive
                    (ay_icmg_conj fallback audit)))))))))

def ay_icmg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_icmg_conj accepted (ay_icmg_conj totalAssignment (ay_icmg_conj originalSat audited))

def ay_icmg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_icmg_conj proofAccepted originalUnsat

def ay_icmg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_icmg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_icmg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_icmg_conj p q :=
  fun r h => h hp hq

theorem ay_icmg_conj_left {p q : Prop} (h : ay_icmg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_icmg_conj_right {p q : Prop} (h : ay_icmg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_icmg_conj_left h)

theorem ay_icmg_disj_left {p q : Prop} (hp : p) : ay_icmg_disj p q :=
  fun r hl _ => hl hp

theorem ay_icmg_disj_right {p q : Prop} (hq : q) : ay_icmg_disj p q :=
  fun r _ hr => hr hq

theorem ay_icmg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_icmg_equiv p q :=
  ay_icmg_conj_intro hpq hqp

theorem ay_icmg_equiv_forward {p q : Prop} (h : ay_icmg_equiv p q) : p -> q :=
  ay_icmg_conj_left h

theorem ay_icmg_equiv_backward {p q : Prop} (h : ay_icmg_equiv p q) : q -> p :=
  ay_icmg_conj_right h

theorem ay_icmg_benchmark_fingerprint_intro {cubeMergeWitness fingerprintOk : Prop}
    (h : cubeMergeWitness -> fingerprintOk) :
    ay_icmg_benchmark_fingerprint cubeMergeWitness fingerprintOk :=
  h

theorem ay_icmg_cube_frame_ledger_intro {fingerprintOk frameOk : Prop}
    (h : fingerprintOk -> frameOk) :
    ay_icmg_cube_frame_ledger fingerprintOk frameOk :=
  h

theorem ay_icmg_merge_policy_witness_intro {frameOk mergeOk : Prop}
    (h : frameOk -> mergeOk) :
    ay_icmg_merge_policy_witness frameOk mergeOk :=
  h

theorem ay_icmg_conflict_free_assignment_merge_witness_intro
    {mergeOk conflictFreeOk : Prop}
    (h : mergeOk -> conflictFreeOk) :
    ay_icmg_conflict_free_assignment_merge_witness mergeOk conflictFreeOk :=
  h

theorem ay_icmg_total_assignment_reconstruction_intro
    {conflictFreeOk totalAssignment : Prop}
    (h : conflictFreeOk -> totalAssignment) :
    ay_icmg_total_assignment_reconstruction conflictFreeOk totalAssignment :=
  h

theorem ay_icmg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_icmg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_icmg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_icmg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_icmg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_icmg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_icmg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_icmg_archive_manifest buildOk archiveOk :=
  h

theorem ay_icmg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_icmg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_icmg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_icmg_audit_transcript fallbackReady audited :=
  h

theorem ay_icmg_accepted_cube_merge_intro
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hframe : frame) (hm : merge) (hcf : conflictFree)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit :=
  ay_icmg_conj_intro hf
    (ay_icmg_conj_intro hframe
      (ay_icmg_conj_intro hm
        (ay_icmg_conj_intro hcf
          (ay_icmg_conj_intro hrc
            (ay_icmg_conj_intro hr
              (ay_icmg_conj_intro hc
                (ay_icmg_conj_intro hb
                  (ay_icmg_conj_intro ha
                    (ay_icmg_conj_intro hfb hau)))))))))

theorem ay_icmg_accepted_cube_merge_fingerprint
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : fingerprint :=
  ay_icmg_conj_left h

theorem ay_icmg_accepted_cube_merge_frame
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : frame :=
  ay_icmg_conj_left (ay_icmg_conj_right h)

theorem ay_icmg_accepted_cube_merge_merge
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : merge :=
  ay_icmg_conj_left (ay_icmg_conj_right (ay_icmg_conj_right h))

theorem ay_icmg_accepted_cube_merge_conflict_free
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : conflictFree :=
  ay_icmg_conj_left
    (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h)))

theorem ay_icmg_accepted_cube_merge_reconstruction
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : reconstruction :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h))))

theorem ay_icmg_accepted_cube_merge_replay
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : replay :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h)))))

theorem ay_icmg_accepted_cube_merge_checker
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : checker :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right
          (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h))))))

theorem ay_icmg_accepted_cube_merge_build
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : build :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right
          (ay_icmg_conj_right
            (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h)))))))

theorem ay_icmg_accepted_cube_merge_archive
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : archive :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right
          (ay_icmg_conj_right
            (ay_icmg_conj_right
              (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h))))))))

theorem ay_icmg_accepted_cube_merge_fallback
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : fallback :=
  ay_icmg_conj_left
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right
          (ay_icmg_conj_right
            (ay_icmg_conj_right
              (ay_icmg_conj_right
                (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h)))))))))

theorem ay_icmg_accepted_cube_merge_audit
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit) : audit :=
  ay_icmg_conj_right
    (ay_icmg_conj_right
      (ay_icmg_conj_right
        (ay_icmg_conj_right
          (ay_icmg_conj_right
            (ay_icmg_conj_right
              (ay_icmg_conj_right
                (ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h)))))))))

theorem ay_icmg_cube_merge_reconstructs_original_sat
    {cubeMergeWitness fingerprintOk frameOk mergeOk conflictFreeOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_icmg_benchmark_fingerprint cubeMergeWitness fingerprintOk)
    (hframe : ay_icmg_cube_frame_ledger fingerprintOk frameOk)
    (hm : ay_icmg_merge_policy_witness frameOk mergeOk)
    (hcf : ay_icmg_conflict_free_assignment_merge_witness mergeOk conflictFreeOk)
    (hrc : ay_icmg_total_assignment_reconstruction conflictFreeOk totalAssignment)
    (hr : ay_icmg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_icmg_model_checker_transcript replayOk originalSat)
    (hb : ay_icmg_solver_build_evidence originalSat buildOk)
    (ha : ay_icmg_archive_manifest buildOk archiveOk)
    (hfb : ay_icmg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_icmg_audit_transcript fallbackReady audited)
    (hw : cubeMergeWitness) :
    ay_icmg_conj totalAssignment (ay_icmg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hframeOk : frameOk := hframe hfingerprint
  let hmerge : mergeOk := hm hframeOk
  let hconflictFree : conflictFreeOk := hcf hmerge
  let htotal : totalAssignment := hrc hconflictFree
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_icmg_conj_intro htotal (ay_icmg_conj_intro hsat haudit)

theorem ay_icmg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_icmg_public_sat accepted totalAssignment originalSat audited :=
  ay_icmg_conj_intro ha (ay_icmg_conj_intro ht (ay_icmg_conj_intro hs hau))

theorem ay_icmg_public_sat_requires_cube_merge
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_icmg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_icmg_conj_left h

theorem ay_icmg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_icmg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_icmg_conj_left (ay_icmg_conj_right h)

theorem ay_icmg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_icmg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_icmg_conj_left (ay_icmg_conj_right (ay_icmg_conj_right h))

theorem ay_icmg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_icmg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_icmg_conj_right (ay_icmg_conj_right (ay_icmg_conj_right h))

theorem ay_icmg_accepted_cube_merge_publishes_sat
    {fingerprint frame merge conflictFree reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
      replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_icmg_public_sat
      (ay_icmg_accepted_cube_merge fingerprint frame merge conflictFree reconstruction
        replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_icmg_public_sat_intro hg ht hs hau

theorem ay_icmg_no_claim_intro {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  h

theorem ay_icmg_recompute_intro {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  h

theorem ay_icmg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  ay_icmg_recompute_intro h

theorem ay_icmg_frame_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  ay_icmg_no_claim_intro h

theorem ay_icmg_merge_mismatch_recompute {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  ay_icmg_recompute_intro h

theorem ay_icmg_conflict_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  ay_icmg_no_claim_intro h

theorem ay_icmg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  ay_icmg_recompute_intro h

theorem ay_icmg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  ay_icmg_recompute_intro h

theorem ay_icmg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  ay_icmg_no_claim_intro h

theorem ay_icmg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_icmg_recompute_obligation reason :=
  ay_icmg_recompute_intro h

theorem ay_icmg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  ay_icmg_no_claim_intro h

theorem ay_icmg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_icmg_no_claim_diagnostic reason :=
  ay_icmg_no_claim_intro h

theorem ay_icmg_failed_cube_merge_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_icmg_public_sat accepted totalAssignment originalSat audited ->
      ay_icmg_no_claim_diagnostic failure) :
    ay_icmg_conj (ay_icmg_no_claim_diagnostic failure)
      (ay_icmg_public_sat accepted totalAssignment originalSat audited ->
        ay_icmg_no_claim_diagnostic failure) :=
  ay_icmg_conj_intro (ay_icmg_no_claim_intro hfail) hblock

theorem ay_icmg_failed_cube_merge_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_icmg_public_sat accepted totalAssignment originalSat audited ->
      ay_icmg_recompute_obligation failure) :
    ay_icmg_conj (ay_icmg_recompute_obligation failure)
      (ay_icmg_public_sat accepted totalAssignment originalSat audited ->
        ay_icmg_recompute_obligation failure) :=
  ay_icmg_conj_intro (ay_icmg_recompute_intro hfail) hblock

theorem ay_icmg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_icmg_public_unsat proofAccepted originalUnsat :=
  ay_icmg_conj_intro hp hu

theorem ay_icmg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_icmg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_icmg_conj_left h

theorem ay_icmg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_icmg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_icmg_conj_right h

theorem ay_icmg_cube_merge_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat cubeMergeSatGuard : Prop}
    (h : ay_icmg_public_unsat proofAccepted originalUnsat) :
    ay_icmg_conj (ay_icmg_public_unsat proofAccepted originalUnsat)
      (cubeMergeSatGuard -> ay_icmg_public_unsat proofAccepted originalUnsat) :=
  ay_icmg_conj_intro h (fun _ => h)

/-!
  SAT-COMP/ay model projection audit-chain guard.

  This self-contained package models the SAT-only obligations for publishing a
  model projected back through multiple transformations with an audit-chain
  digest.
-/

def ay_pacg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_pacg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_pacg_equiv (p q : Prop) : Prop :=
  ay_pacg_conj (p -> q) (q -> p)

def ay_pacg_benchmark_fingerprint (projectedWitness fingerprintOk : Prop) : Prop :=
  projectedWitness -> fingerprintOk

def ay_pacg_transform_chain_digest (fingerprintOk chainOk : Prop) : Prop :=
  fingerprintOk -> chainOk

def ay_pacg_per_transform_projection_ledger (chainOk projectionOk : Prop) : Prop :=
  chainOk -> projectionOk

def ay_pacg_audit_chain_hash (projectionOk auditHashOk : Prop) : Prop :=
  projectionOk -> auditHashOk

def ay_pacg_total_assignment_reconstruction (auditHashOk totalAssignment : Prop) : Prop :=
  auditHashOk -> totalAssignment

def ay_pacg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_pacg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_pacg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_pacg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_pacg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_pacg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_pacg_accepted_audit_chain
    (fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_pacg_conj fingerprint
    (ay_pacg_conj chain
      (ay_pacg_conj projection
        (ay_pacg_conj auditHash
          (ay_pacg_conj reconstruction
            (ay_pacg_conj replay
              (ay_pacg_conj checker
                (ay_pacg_conj build
                  (ay_pacg_conj archive
                    (ay_pacg_conj fallback audit)))))))))

def ay_pacg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_pacg_conj accepted (ay_pacg_conj totalAssignment (ay_pacg_conj originalSat audited))

def ay_pacg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_pacg_conj proofAccepted originalUnsat

def ay_pacg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_pacg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_pacg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_pacg_conj p q :=
  fun r h => h hp hq

theorem ay_pacg_conj_left {p q : Prop} (h : ay_pacg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_pacg_conj_right {p q : Prop} (h : ay_pacg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_pacg_conj_left h)

theorem ay_pacg_disj_left {p q : Prop} (hp : p) : ay_pacg_disj p q :=
  fun r hl _ => hl hp

theorem ay_pacg_disj_right {p q : Prop} (hq : q) : ay_pacg_disj p q :=
  fun r _ hr => hr hq

theorem ay_pacg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_pacg_equiv p q :=
  ay_pacg_conj_intro hpq hqp

theorem ay_pacg_equiv_forward {p q : Prop} (h : ay_pacg_equiv p q) : p -> q :=
  ay_pacg_conj_left h

theorem ay_pacg_equiv_backward {p q : Prop} (h : ay_pacg_equiv p q) : q -> p :=
  ay_pacg_conj_right h

theorem ay_pacg_benchmark_fingerprint_intro {projectedWitness fingerprintOk : Prop}
    (h : projectedWitness -> fingerprintOk) :
    ay_pacg_benchmark_fingerprint projectedWitness fingerprintOk :=
  h

theorem ay_pacg_transform_chain_digest_intro {fingerprintOk chainOk : Prop}
    (h : fingerprintOk -> chainOk) :
    ay_pacg_transform_chain_digest fingerprintOk chainOk :=
  h

theorem ay_pacg_per_transform_projection_ledger_intro {chainOk projectionOk : Prop}
    (h : chainOk -> projectionOk) :
    ay_pacg_per_transform_projection_ledger chainOk projectionOk :=
  h

theorem ay_pacg_audit_chain_hash_intro {projectionOk auditHashOk : Prop}
    (h : projectionOk -> auditHashOk) :
    ay_pacg_audit_chain_hash projectionOk auditHashOk :=
  h

theorem ay_pacg_total_assignment_reconstruction_intro {auditHashOk totalAssignment : Prop}
    (h : auditHashOk -> totalAssignment) :
    ay_pacg_total_assignment_reconstruction auditHashOk totalAssignment :=
  h

theorem ay_pacg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_pacg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_pacg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_pacg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_pacg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_pacg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_pacg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_pacg_archive_manifest buildOk archiveOk :=
  h

theorem ay_pacg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_pacg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_pacg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_pacg_audit_transcript fallbackReady audited :=
  h

theorem ay_pacg_accepted_audit_chain_intro
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hchain : chain) (hp : projection) (hah : auditHash)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_pacg_accepted_audit_chain fingerprint chain projection auditHash reconstruction
      replay checker build archive fallback audit :=
  ay_pacg_conj_intro hf
    (ay_pacg_conj_intro hchain
      (ay_pacg_conj_intro hp
        (ay_pacg_conj_intro hah
          (ay_pacg_conj_intro hrc
            (ay_pacg_conj_intro hr
              (ay_pacg_conj_intro hc
                (ay_pacg_conj_intro hb
                  (ay_pacg_conj_intro ha
                    (ay_pacg_conj_intro hfb hau)))))))))

theorem ay_pacg_accepted_audit_chain_fingerprint
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_pacg_conj_left h

theorem ay_pacg_accepted_audit_chain_chain
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : chain :=
  ay_pacg_conj_left (ay_pacg_conj_right h)

theorem ay_pacg_accepted_audit_chain_projection
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : projection :=
  ay_pacg_conj_left (ay_pacg_conj_right (ay_pacg_conj_right h))

theorem ay_pacg_accepted_audit_chain_audit_hash
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : auditHash :=
  ay_pacg_conj_left
    (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))

theorem ay_pacg_accepted_audit_chain_reconstruction
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h))))

theorem ay_pacg_accepted_audit_chain_replay
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))))

theorem ay_pacg_accepted_audit_chain_checker
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right
          (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h))))))

theorem ay_pacg_accepted_audit_chain_build
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : build :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right
          (ay_pacg_conj_right
            (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))))))

theorem ay_pacg_accepted_audit_chain_archive
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right
          (ay_pacg_conj_right
            (ay_pacg_conj_right
              (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h))))))))

theorem ay_pacg_accepted_audit_chain_fallback
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_pacg_conj_left
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right
          (ay_pacg_conj_right
            (ay_pacg_conj_right
              (ay_pacg_conj_right
                (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))))))))

theorem ay_pacg_accepted_audit_chain_audit
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_pacg_conj_right
    (ay_pacg_conj_right
      (ay_pacg_conj_right
        (ay_pacg_conj_right
          (ay_pacg_conj_right
            (ay_pacg_conj_right
              (ay_pacg_conj_right
                (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))))))))

theorem ay_pacg_projection_audit_chain_reconstructs_original_sat
    {projectedWitness fingerprintOk chainOk projectionOk auditHashOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_pacg_benchmark_fingerprint projectedWitness fingerprintOk)
    (hchain : ay_pacg_transform_chain_digest fingerprintOk chainOk)
    (hp : ay_pacg_per_transform_projection_ledger chainOk projectionOk)
    (hah : ay_pacg_audit_chain_hash projectionOk auditHashOk)
    (hrc : ay_pacg_total_assignment_reconstruction auditHashOk totalAssignment)
    (hr : ay_pacg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_pacg_model_checker_transcript replayOk originalSat)
    (hb : ay_pacg_solver_build_evidence originalSat buildOk)
    (ha : ay_pacg_archive_manifest buildOk archiveOk)
    (hfb : ay_pacg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_pacg_audit_transcript fallbackReady audited)
    (hw : projectedWitness) :
    ay_pacg_conj totalAssignment (ay_pacg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hchainOk : chainOk := hchain hfingerprint
  let hprojection : projectionOk := hp hchainOk
  let hauditHash : auditHashOk := hah hprojection
  let htotal : totalAssignment := hrc hauditHash
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_pacg_conj_intro htotal (ay_pacg_conj_intro hsat haudit)

theorem ay_pacg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_pacg_public_sat accepted totalAssignment originalSat audited :=
  ay_pacg_conj_intro ha (ay_pacg_conj_intro ht (ay_pacg_conj_intro hs hau))

theorem ay_pacg_public_sat_requires_audit_chain
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_pacg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_pacg_conj_left h

theorem ay_pacg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_pacg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_pacg_conj_left (ay_pacg_conj_right h)

theorem ay_pacg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_pacg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_pacg_conj_left (ay_pacg_conj_right (ay_pacg_conj_right h))

theorem ay_pacg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_pacg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h))

theorem ay_pacg_accepted_audit_chain_publishes_sat
    {fingerprint chain projection auditHash reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_pacg_accepted_audit_chain fingerprint chain projection auditHash
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_pacg_public_sat
      (ay_pacg_accepted_audit_chain fingerprint chain projection auditHash reconstruction
        replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_pacg_public_sat_intro hg ht hs hau

theorem ay_pacg_no_claim_intro {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  h

theorem ay_pacg_recompute_intro {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  h

theorem ay_pacg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  ay_pacg_recompute_intro h

theorem ay_pacg_chain_mismatch_recompute {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  ay_pacg_recompute_intro h

theorem ay_pacg_projection_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_audit_hash_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  ay_pacg_recompute_intro h

theorem ay_pacg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  ay_pacg_recompute_intro h

theorem ay_pacg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  ay_pacg_recompute_intro h

theorem ay_pacg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_failed_audit_chain_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_pacg_public_sat accepted totalAssignment originalSat audited ->
      ay_pacg_no_claim_diagnostic failure) :
    ay_pacg_conj (ay_pacg_no_claim_diagnostic failure)
      (ay_pacg_public_sat accepted totalAssignment originalSat audited ->
        ay_pacg_no_claim_diagnostic failure) :=
  ay_pacg_conj_intro (ay_pacg_no_claim_intro hfail) hblock

theorem ay_pacg_failed_audit_chain_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_pacg_public_sat accepted totalAssignment originalSat audited ->
      ay_pacg_recompute_obligation failure) :
    ay_pacg_conj (ay_pacg_recompute_obligation failure)
      (ay_pacg_public_sat accepted totalAssignment originalSat audited ->
        ay_pacg_recompute_obligation failure) :=
  ay_pacg_conj_intro (ay_pacg_recompute_intro hfail) hblock

theorem ay_pacg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_pacg_public_unsat proofAccepted originalUnsat :=
  ay_pacg_conj_intro hp hu

theorem ay_pacg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_pacg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_pacg_conj_left h

theorem ay_pacg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_pacg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_pacg_conj_right h

theorem ay_pacg_audit_chain_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat auditChainSatGuard : Prop}
    (h : ay_pacg_public_unsat proofAccepted originalUnsat) :
    ay_pacg_conj (ay_pacg_public_unsat proofAccepted originalUnsat)
      (auditChainSatGuard -> ay_pacg_public_unsat proofAccepted originalUnsat) :=
  ay_pacg_conj_intro h (fun _ => h)

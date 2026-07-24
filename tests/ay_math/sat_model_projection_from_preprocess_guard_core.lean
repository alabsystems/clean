/-!
  SAT-COMP/ay model projection guard from preprocessing.

  This self-contained package records the SAT-only obligations for publishing a
  model found on a preprocessed formula as a model for the original DIMACS
  instance.
-/

def ay_mppg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mppg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mppg_equiv (p q : Prop) : Prop :=
  ay_mppg_conj (p -> q) (q -> p)

def ay_mppg_preprocessing_transform_digest (transformedSat transformOk : Prop) : Prop :=
  transformedSat -> transformOk

def ay_mppg_eliminated_variable_ledger (transformOk ledgerOk : Prop) : Prop :=
  transformOk -> ledgerOk

def ay_mppg_extension_assignment_witness (ledgerOk extensionOk : Prop) : Prop :=
  ledgerOk -> extensionOk

def ay_mppg_clause_origin_map (extensionOk originOk : Prop) : Prop :=
  extensionOk -> originOk

def ay_mppg_original_clause_satisfaction_replay (originOk replayOk : Prop) : Prop :=
  originOk -> replayOk

def ay_mppg_dimacs_reconstruction (replayOk originalAssignment : Prop) : Prop :=
  replayOk -> originalAssignment

def ay_mppg_model_checker_transcript (originalAssignment originalSat : Prop) : Prop :=
  originalAssignment -> originalSat

def ay_mppg_benchmark_fingerprint (originalSat fingerprintOk : Prop) : Prop :=
  originalSat -> fingerprintOk

def ay_mppg_solver_build_evidence (fingerprintOk buildOk : Prop) : Prop :=
  fingerprintOk -> buildOk

def ay_mppg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mppg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mppg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mppg_accepted_projection
    (transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop) : Prop :=
  ay_mppg_conj transform
    (ay_mppg_conj ledger
      (ay_mppg_conj extension
        (ay_mppg_conj origin
          (ay_mppg_conj replay
            (ay_mppg_conj reconstruction
              (ay_mppg_conj checker
                (ay_mppg_conj fingerprint
                  (ay_mppg_conj build
                    (ay_mppg_conj archive
                      (ay_mppg_conj fallback audit))))))))))

def ay_mppg_public_sat (accepted originalAssignment originalSat audited : Prop) : Prop :=
  ay_mppg_conj accepted (ay_mppg_conj originalAssignment (ay_mppg_conj originalSat audited))

def ay_mppg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mppg_conj proofAccepted originalUnsat

def ay_mppg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mppg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mppg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mppg_conj p q :=
  fun r h => h hp hq

theorem ay_mppg_conj_left {p q : Prop} (h : ay_mppg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mppg_conj_right {p q : Prop} (h : ay_mppg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mppg_conj_left h)

theorem ay_mppg_disj_left {p q : Prop} (hp : p) : ay_mppg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mppg_disj_right {p q : Prop} (hq : q) : ay_mppg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mppg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mppg_equiv p q :=
  ay_mppg_conj_intro hpq hqp

theorem ay_mppg_equiv_forward {p q : Prop} (h : ay_mppg_equiv p q) : p -> q :=
  ay_mppg_conj_left h

theorem ay_mppg_equiv_backward {p q : Prop} (h : ay_mppg_equiv p q) : q -> p :=
  ay_mppg_conj_right h

theorem ay_mppg_preprocessing_transform_digest_intro {transformedSat transformOk : Prop}
    (h : transformedSat -> transformOk) :
    ay_mppg_preprocessing_transform_digest transformedSat transformOk :=
  h

theorem ay_mppg_eliminated_variable_ledger_intro {transformOk ledgerOk : Prop}
    (h : transformOk -> ledgerOk) :
    ay_mppg_eliminated_variable_ledger transformOk ledgerOk :=
  h

theorem ay_mppg_extension_assignment_witness_intro {ledgerOk extensionOk : Prop}
    (h : ledgerOk -> extensionOk) :
    ay_mppg_extension_assignment_witness ledgerOk extensionOk :=
  h

theorem ay_mppg_clause_origin_map_intro {extensionOk originOk : Prop}
    (h : extensionOk -> originOk) :
    ay_mppg_clause_origin_map extensionOk originOk :=
  h

theorem ay_mppg_original_clause_satisfaction_replay_intro {originOk replayOk : Prop}
    (h : originOk -> replayOk) :
    ay_mppg_original_clause_satisfaction_replay originOk replayOk :=
  h

theorem ay_mppg_dimacs_reconstruction_intro {replayOk originalAssignment : Prop}
    (h : replayOk -> originalAssignment) :
    ay_mppg_dimacs_reconstruction replayOk originalAssignment :=
  h

theorem ay_mppg_model_checker_transcript_intro {originalAssignment originalSat : Prop}
    (h : originalAssignment -> originalSat) :
    ay_mppg_model_checker_transcript originalAssignment originalSat :=
  h

theorem ay_mppg_benchmark_fingerprint_intro {originalSat fingerprintOk : Prop}
    (h : originalSat -> fingerprintOk) :
    ay_mppg_benchmark_fingerprint originalSat fingerprintOk :=
  h

theorem ay_mppg_solver_build_evidence_intro {fingerprintOk buildOk : Prop}
    (h : fingerprintOk -> buildOk) :
    ay_mppg_solver_build_evidence fingerprintOk buildOk :=
  h

theorem ay_mppg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mppg_archive_manifest buildOk archiveOk :=
  h

theorem ay_mppg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mppg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mppg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mppg_audit_transcript fallbackReady audited :=
  h

theorem ay_mppg_accepted_projection_intro
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (ht : transform) (hl : ledger) (he : extension) (ho : origin) (hr : replay)
    (hrec : reconstruction) (hc : checker) (hf : fingerprint) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_mppg_accepted_projection transform ledger extension origin replay reconstruction
      checker fingerprint build archive fallback audit :=
  ay_mppg_conj_intro ht
    (ay_mppg_conj_intro hl
      (ay_mppg_conj_intro he
        (ay_mppg_conj_intro ho
          (ay_mppg_conj_intro hr
            (ay_mppg_conj_intro hrec
              (ay_mppg_conj_intro hc
                (ay_mppg_conj_intro hf
                  (ay_mppg_conj_intro hb
                    (ay_mppg_conj_intro ha
                      (ay_mppg_conj_intro hfb hau))))))))))

theorem ay_mppg_accepted_projection_transform
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : transform :=
  ay_mppg_conj_left h

theorem ay_mppg_accepted_projection_ledger
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : ledger :=
  ay_mppg_conj_left (ay_mppg_conj_right h)

theorem ay_mppg_accepted_projection_extension
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : extension :=
  ay_mppg_conj_left (ay_mppg_conj_right (ay_mppg_conj_right h))

theorem ay_mppg_accepted_projection_origin
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : origin :=
  ay_mppg_conj_left
    (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h)))

theorem ay_mppg_accepted_projection_replay
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : replay :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))))

theorem ay_mppg_accepted_projection_reconstruction
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : reconstruction :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h)))))

theorem ay_mppg_accepted_projection_checker
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : checker :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))))))

theorem ay_mppg_accepted_projection_fingerprint
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : fingerprint :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right
            (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h)))))))

theorem ay_mppg_accepted_projection_build
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : build :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right
            (ay_mppg_conj_right
              (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))))))))

theorem ay_mppg_accepted_projection_archive
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : archive :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right
            (ay_mppg_conj_right
              (ay_mppg_conj_right
                (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h)))))))))

theorem ay_mppg_accepted_projection_fallback
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : fallback :=
  ay_mppg_conj_left
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right
            (ay_mppg_conj_right
              (ay_mppg_conj_right
                (ay_mppg_conj_right
                  (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))))))))))

theorem ay_mppg_accepted_projection_audit
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit : Prop}
    (h : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit) : audit :=
  ay_mppg_conj_right
    (ay_mppg_conj_right
      (ay_mppg_conj_right
        (ay_mppg_conj_right
          (ay_mppg_conj_right
            (ay_mppg_conj_right
              (ay_mppg_conj_right
                (ay_mppg_conj_right
                  (ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))))))))))

theorem ay_mppg_projection_reconstructs_original_sat
    {transformedSat transformOk ledgerOk extensionOk originOk replayOk
     originalAssignment originalSat fingerprintOk buildOk archiveOk fallbackReady audited : Prop}
    (ht : ay_mppg_preprocessing_transform_digest transformedSat transformOk)
    (hl : ay_mppg_eliminated_variable_ledger transformOk ledgerOk)
    (he : ay_mppg_extension_assignment_witness ledgerOk extensionOk)
    (ho : ay_mppg_clause_origin_map extensionOk originOk)
    (hr : ay_mppg_original_clause_satisfaction_replay originOk replayOk)
    (hrec : ay_mppg_dimacs_reconstruction replayOk originalAssignment)
    (hc : ay_mppg_model_checker_transcript originalAssignment originalSat)
    (hf : ay_mppg_benchmark_fingerprint originalSat fingerprintOk)
    (hb : ay_mppg_solver_build_evidence fingerprintOk buildOk)
    (ha : ay_mppg_archive_manifest buildOk archiveOk)
    (hfb : ay_mppg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_mppg_audit_transcript fallbackReady audited)
    (hsat : transformedSat) :
    ay_mppg_conj originalAssignment (ay_mppg_conj originalSat audited) :=
  let htransform : transformOk := ht hsat
  let hledger : ledgerOk := hl htransform
  let hextension : extensionOk := he hledger
  let horigin : originOk := ho hextension
  let hreplay : replayOk := hr horigin
  let hassignment : originalAssignment := hrec hreplay
  let horiginal : originalSat := hc hassignment
  let hfingerprint : fingerprintOk := hf horiginal
  let hbuild : buildOk := hb hfingerprint
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_mppg_conj_intro hassignment (ay_mppg_conj_intro horiginal haudit)

theorem ay_mppg_public_sat_intro {accepted originalAssignment originalSat audited : Prop}
    (ha : accepted) (hm : originalAssignment) (hs : originalSat) (hau : audited) :
    ay_mppg_public_sat accepted originalAssignment originalSat audited :=
  ay_mppg_conj_intro ha (ay_mppg_conj_intro hm (ay_mppg_conj_intro hs hau))

theorem ay_mppg_public_sat_requires_projection
    {accepted originalAssignment originalSat audited : Prop}
    (h : ay_mppg_public_sat accepted originalAssignment originalSat audited) : accepted :=
  ay_mppg_conj_left h

theorem ay_mppg_public_sat_original_assignment
    {accepted originalAssignment originalSat audited : Prop}
    (h : ay_mppg_public_sat accepted originalAssignment originalSat audited) :
    originalAssignment :=
  ay_mppg_conj_left (ay_mppg_conj_right h)

theorem ay_mppg_public_sat_original_formula
    {accepted originalAssignment originalSat audited : Prop}
    (h : ay_mppg_public_sat accepted originalAssignment originalSat audited) : originalSat :=
  ay_mppg_conj_left (ay_mppg_conj_right (ay_mppg_conj_right h))

theorem ay_mppg_public_sat_audit
    {accepted originalAssignment originalSat audited : Prop}
    (h : ay_mppg_public_sat accepted originalAssignment originalSat audited) : audited :=
  ay_mppg_conj_right (ay_mppg_conj_right (ay_mppg_conj_right h))

theorem ay_mppg_accepted_projection_publishes_sat
    {transform ledger extension origin replay reconstruction checker fingerprint build
     archive fallback audit originalAssignment originalSat audited : Prop}
    (hg : ay_mppg_accepted_projection transform ledger extension origin replay
      reconstruction checker fingerprint build archive fallback audit)
    (hm : originalAssignment) (hs : originalSat) (hau : audited) :
    ay_mppg_public_sat
      (ay_mppg_accepted_projection transform ledger extension origin replay reconstruction
        checker fingerprint build archive fallback audit)
      originalAssignment originalSat audited :=
  ay_mppg_public_sat_intro hg hm hs hau

theorem ay_mppg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  h

theorem ay_mppg_recompute_intro {reason : Prop} (h : reason) :
    ay_mppg_recompute_obligation reason :=
  h

theorem ay_mppg_transform_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_ledger_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_extension_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mppg_recompute_obligation reason :=
  ay_mppg_recompute_intro h

theorem ay_mppg_origin_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mppg_recompute_obligation reason :=
  ay_mppg_recompute_intro h

theorem ay_mppg_reconstruction_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mppg_recompute_obligation reason :=
  ay_mppg_recompute_intro h

theorem ay_mppg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mppg_recompute_obligation reason :=
  ay_mppg_recompute_intro h

theorem ay_mppg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mppg_no_claim_diagnostic reason :=
  ay_mppg_no_claim_intro h

theorem ay_mppg_failed_projection_cannot_create_public_sat
    {failure accepted originalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mppg_public_sat accepted originalAssignment originalSat audited ->
      ay_mppg_no_claim_diagnostic failure) :
    ay_mppg_conj (ay_mppg_no_claim_diagnostic failure)
      (ay_mppg_public_sat accepted originalAssignment originalSat audited ->
        ay_mppg_no_claim_diagnostic failure) :=
  ay_mppg_conj_intro (ay_mppg_no_claim_intro hfail) hblock

theorem ay_mppg_failed_projection_forces_recompute
    {failure accepted originalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mppg_public_sat accepted originalAssignment originalSat audited ->
      ay_mppg_recompute_obligation failure) :
    ay_mppg_conj (ay_mppg_recompute_obligation failure)
      (ay_mppg_public_sat accepted originalAssignment originalSat audited ->
        ay_mppg_recompute_obligation failure) :=
  ay_mppg_conj_intro (ay_mppg_recompute_intro hfail) hblock

theorem ay_mppg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mppg_public_unsat proofAccepted originalUnsat :=
  ay_mppg_conj_intro hp hu

theorem ay_mppg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mppg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mppg_conj_left h

theorem ay_mppg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mppg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mppg_conj_right h

theorem ay_mppg_unsat_claims_not_strengthened_by_sat_projection_guard
    {proofAccepted originalUnsat satProjectionGuard : Prop}
    (h : ay_mppg_public_unsat proofAccepted originalUnsat) :
    ay_mppg_conj (ay_mppg_public_unsat proofAccepted originalUnsat)
      (satProjectionGuard -> ay_mppg_public_unsat proofAccepted originalUnsat) :=
  ay_mppg_conj_intro h (fun _ => h)

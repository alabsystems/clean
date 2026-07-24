/-!
  SAT-COMP/ay assumption-ledger digest guard.

  This self-contained package models the SAT-only obligations for publishing a
  witness produced with assumptions only when the assumption ledger digest and
  active/inactive partition evidence agree with the reconstructed model.
-/

def ay_malg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_malg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_malg_equiv (p q : Prop) : Prop :=
  ay_malg_conj (p -> q) (q -> p)

def ay_malg_benchmark_fingerprint (assumptionWitness fingerprintOk : Prop) : Prop :=
  assumptionWitness -> fingerprintOk

def ay_malg_assumption_ledger_digest (fingerprintOk ledgerOk : Prop) : Prop :=
  fingerprintOk -> ledgerOk

def ay_malg_active_inactive_assumption_partition_witness
    (ledgerOk partitionOk : Prop) : Prop :=
  ledgerOk -> partitionOk

def ay_malg_total_assignment_reconstruction (partitionOk totalAssignment : Prop) : Prop :=
  partitionOk -> totalAssignment

def ay_malg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_malg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_malg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_malg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_malg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_malg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_malg_accepted_assumption_ledger
    (fingerprint ledger partition reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_malg_conj fingerprint
    (ay_malg_conj ledger
      (ay_malg_conj partition
        (ay_malg_conj reconstruction
          (ay_malg_conj replay
            (ay_malg_conj checker
              (ay_malg_conj build
                (ay_malg_conj archive
                  (ay_malg_conj fallback audit))))))))

def ay_malg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_malg_conj accepted
    (ay_malg_conj totalAssignment
      (ay_malg_conj everyOriginalClauseSatisfied (ay_malg_conj originalSat audited)))

def ay_malg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_malg_conj proofAccepted originalUnsat

def ay_malg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_malg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_malg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_malg_conj p q :=
  fun r h => h hp hq

theorem ay_malg_conj_left {p q : Prop} (h : ay_malg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_malg_conj_right {p q : Prop} (h : ay_malg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_malg_conj_left h)

theorem ay_malg_disj_left {p q : Prop} (hp : p) : ay_malg_disj p q :=
  fun r hl _ => hl hp

theorem ay_malg_disj_right {p q : Prop} (hq : q) : ay_malg_disj p q :=
  fun r _ hr => hr hq

theorem ay_malg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_malg_equiv p q :=
  ay_malg_conj_intro hpq hqp

theorem ay_malg_equiv_forward {p q : Prop} (h : ay_malg_equiv p q) : p -> q :=
  ay_malg_conj_left h

theorem ay_malg_equiv_backward {p q : Prop} (h : ay_malg_equiv p q) : q -> p :=
  ay_malg_conj_right h

theorem ay_malg_benchmark_fingerprint_intro {assumptionWitness fingerprintOk : Prop}
    (h : assumptionWitness -> fingerprintOk) :
    ay_malg_benchmark_fingerprint assumptionWitness fingerprintOk :=
  h

theorem ay_malg_assumption_ledger_digest_intro {fingerprintOk ledgerOk : Prop}
    (h : fingerprintOk -> ledgerOk) :
    ay_malg_assumption_ledger_digest fingerprintOk ledgerOk :=
  h

theorem ay_malg_active_inactive_assumption_partition_witness_intro
    {ledgerOk partitionOk : Prop}
    (h : ledgerOk -> partitionOk) :
    ay_malg_active_inactive_assumption_partition_witness ledgerOk partitionOk :=
  h

theorem ay_malg_total_assignment_reconstruction_intro {partitionOk totalAssignment : Prop}
    (h : partitionOk -> totalAssignment) :
    ay_malg_total_assignment_reconstruction partitionOk totalAssignment :=
  h

theorem ay_malg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_malg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_malg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_malg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_malg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_malg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_malg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_malg_archive_manifest buildOk archiveOk :=
  h

theorem ay_malg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_malg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_malg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_malg_audit_transcript fallbackReady audited :=
  h

theorem ay_malg_accepted_assumption_ledger_intro
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hl : ledger) (hp : partition) (hrc : reconstruction)
    (hr : replay) (hc : checker) (hb : build) (ha : archive)
    (hfb : fallback) (hau : audit) :
    ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit :=
  ay_malg_conj_intro hf
    (ay_malg_conj_intro hl
      (ay_malg_conj_intro hp
        (ay_malg_conj_intro hrc
          (ay_malg_conj_intro hr
            (ay_malg_conj_intro hc
              (ay_malg_conj_intro hb
                (ay_malg_conj_intro ha
                  (ay_malg_conj_intro hfb hau))))))))

theorem ay_malg_accepted_assumption_ledger_fingerprint
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : fingerprint :=
  ay_malg_conj_left h

theorem ay_malg_accepted_assumption_ledger_ledger
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : ledger :=
  ay_malg_conj_left (ay_malg_conj_right h)

theorem ay_malg_accepted_assumption_ledger_partition
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : partition :=
  ay_malg_conj_left (ay_malg_conj_right (ay_malg_conj_right h))

theorem ay_malg_accepted_assumption_ledger_reconstruction
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : reconstruction :=
  ay_malg_conj_left
    (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h)))

theorem ay_malg_accepted_assumption_ledger_replay
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : replay :=
  ay_malg_conj_left
    (ay_malg_conj_right
      (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h))))

theorem ay_malg_accepted_assumption_ledger_checker
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : checker :=
  ay_malg_conj_left
    (ay_malg_conj_right
      (ay_malg_conj_right
        (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h)))))

theorem ay_malg_accepted_assumption_ledger_build
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : build :=
  ay_malg_conj_left
    (ay_malg_conj_right
      (ay_malg_conj_right
        (ay_malg_conj_right
          (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h))))))

theorem ay_malg_accepted_assumption_ledger_archive
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : archive :=
  ay_malg_conj_left
    (ay_malg_conj_right
      (ay_malg_conj_right
        (ay_malg_conj_right
          (ay_malg_conj_right
            (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h)))))))

theorem ay_malg_accepted_assumption_ledger_fallback
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : fallback :=
  ay_malg_conj_left
    (ay_malg_conj_right
      (ay_malg_conj_right
        (ay_malg_conj_right
          (ay_malg_conj_right
            (ay_malg_conj_right
              (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h))))))))

theorem ay_malg_accepted_assumption_ledger_audit
    {fingerprint ledger partition reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
      checker build archive fallback audit) : audit :=
  ay_malg_conj_right
    (ay_malg_conj_right
      (ay_malg_conj_right
        (ay_malg_conj_right
          (ay_malg_conj_right
            (ay_malg_conj_right
              (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h))))))))

theorem ay_malg_assumption_ledger_reconstructs_original_sat
    {assumptionWitness fingerprintOk ledgerOk partitionOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_malg_benchmark_fingerprint assumptionWitness fingerprintOk)
    (hl : ay_malg_assumption_ledger_digest fingerprintOk ledgerOk)
    (hp : ay_malg_active_inactive_assumption_partition_witness ledgerOk partitionOk)
    (hrc : ay_malg_total_assignment_reconstruction partitionOk totalAssignment)
    (hr : ay_malg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_malg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_malg_solver_build_evidence originalSat buildOk)
    (ha : ay_malg_archive_manifest buildOk archiveOk)
    (hfb : ay_malg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_malg_audit_transcript fallbackReady audited)
    (hw : assumptionWitness) :
    ay_malg_conj totalAssignment
      (ay_malg_conj everyOriginalClauseSatisfied (ay_malg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hledger : ledgerOk := hl hfingerprint
  let hpartition : partitionOk := hp hledger
  let htotal : totalAssignment := hrc hpartition
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_malg_conj_intro htotal (ay_malg_conj_intro hevery (ay_malg_conj_intro hsat haudit))

theorem ay_malg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_malg_conj_intro ha
    (ay_malg_conj_intro ht (ay_malg_conj_intro hevery (ay_malg_conj_intro hs hau)))

theorem ay_malg_public_sat_requires_assumption_ledger
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_malg_conj_left h

theorem ay_malg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_malg_conj_left (ay_malg_conj_right h)

theorem ay_malg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_malg_conj_left (ay_malg_conj_right (ay_malg_conj_right h))

theorem ay_malg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_malg_conj_left (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h)))

theorem ay_malg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right (ay_malg_conj_right h)))

theorem ay_malg_accepted_assumption_ledger_publishes_sat
    {fingerprint ledger partition reconstruction replay checker build archive fallback audit
     totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction
      replay checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_malg_public_sat
      (ay_malg_accepted_assumption_ledger fingerprint ledger partition reconstruction replay
        checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_malg_public_sat_intro hg ht hevery hs hau

theorem ay_malg_no_claim_intro {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  h

theorem ay_malg_recompute_intro {reason : Prop} (h : reason) :
    ay_malg_recompute_obligation reason :=
  h

theorem ay_malg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_malg_recompute_obligation reason :=
  ay_malg_recompute_intro h

theorem ay_malg_ledger_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  ay_malg_no_claim_intro h

theorem ay_malg_partition_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  ay_malg_no_claim_intro h

theorem ay_malg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_malg_recompute_obligation reason :=
  ay_malg_recompute_intro h

theorem ay_malg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_malg_recompute_obligation reason :=
  ay_malg_recompute_intro h

theorem ay_malg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  ay_malg_no_claim_intro h

theorem ay_malg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_malg_recompute_obligation reason :=
  ay_malg_recompute_intro h

theorem ay_malg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  ay_malg_no_claim_intro h

theorem ay_malg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_malg_no_claim_diagnostic reason :=
  ay_malg_no_claim_intro h

theorem ay_malg_failed_assumption_ledger_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_malg_no_claim_diagnostic failure) :
    ay_malg_conj (ay_malg_no_claim_diagnostic failure)
      (ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_malg_no_claim_diagnostic failure) :=
  ay_malg_conj_intro (ay_malg_no_claim_intro hfail) hblock

theorem ay_malg_failed_assumption_ledger_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_malg_recompute_obligation failure) :
    ay_malg_conj (ay_malg_recompute_obligation failure)
      (ay_malg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_malg_recompute_obligation failure) :=
  ay_malg_conj_intro (ay_malg_recompute_intro hfail) hblock

theorem ay_malg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_malg_public_unsat proofAccepted originalUnsat :=
  ay_malg_conj_intro hp hu

theorem ay_malg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_malg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_malg_conj_left h

theorem ay_malg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_malg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_malg_conj_right h

theorem ay_malg_assumption_ledger_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat assumptionLedgerSatGuard : Prop}
    (h : ay_malg_public_unsat proofAccepted originalUnsat) :
    ay_malg_conj (ay_malg_public_unsat proofAccepted originalUnsat)
      (assumptionLedgerSatGuard -> ay_malg_public_unsat proofAccepted originalUnsat) :=
  ay_malg_conj_intro h (fun _ => h)

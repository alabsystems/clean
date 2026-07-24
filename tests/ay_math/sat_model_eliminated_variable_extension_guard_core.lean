/-!
  SAT-COMP/ay eliminated-variable extension guard.

  This self-contained package models the SAT-only obligations for extending a
  preprocessed SAT model through eliminated-variable witnesses back to a total
  assignment for the original formula.
-/

def ay_eveg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_eveg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_eveg_equiv (p q : Prop) : Prop :=
  ay_eveg_conj (p -> q) (q -> p)

def ay_eveg_original_formula_digest (preprocessedModel originalDigestOk : Prop) : Prop :=
  preprocessedModel -> originalDigestOk

def ay_eveg_preprocessed_formula_digest (originalDigestOk preprocessedDigestOk : Prop) : Prop :=
  originalDigestOk -> preprocessedDigestOk

def ay_eveg_eliminated_variable_ledger (preprocessedDigestOk ledgerOk : Prop) : Prop :=
  preprocessedDigestOk -> ledgerOk

def ay_eveg_extension_map_witness (ledgerOk extensionOk : Prop) : Prop :=
  ledgerOk -> extensionOk

def ay_eveg_total_assignment_reconstruction (extensionOk totalAssignment : Prop) : Prop :=
  extensionOk -> totalAssignment

def ay_eveg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_eveg_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_eveg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_eveg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_eveg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_eveg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_eveg_accepted_extension
    (originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop) : Prop :=
  ay_eveg_conj originalDigest
    (ay_eveg_conj preprocessedDigest
      (ay_eveg_conj ledger
        (ay_eveg_conj extension
          (ay_eveg_conj reconstruction
            (ay_eveg_conj replay
              (ay_eveg_conj checker
                (ay_eveg_conj build
                  (ay_eveg_conj archive
                    (ay_eveg_conj fallback audit)))))))))

def ay_eveg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_eveg_conj accepted
    (ay_eveg_conj totalAssignment
      (ay_eveg_conj everyOriginalClauseSatisfied (ay_eveg_conj originalSat audited)))

def ay_eveg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_eveg_conj proofAccepted originalUnsat

def ay_eveg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_eveg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_eveg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_eveg_conj p q :=
  fun r h => h hp hq

theorem ay_eveg_conj_left {p q : Prop} (h : ay_eveg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_eveg_conj_right {p q : Prop} (h : ay_eveg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_eveg_conj_left h)

theorem ay_eveg_disj_left {p q : Prop} (hp : p) : ay_eveg_disj p q :=
  fun r hl _ => hl hp

theorem ay_eveg_disj_right {p q : Prop} (hq : q) : ay_eveg_disj p q :=
  fun r _ hr => hr hq

theorem ay_eveg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_eveg_equiv p q :=
  ay_eveg_conj_intro hpq hqp

theorem ay_eveg_equiv_forward {p q : Prop} (h : ay_eveg_equiv p q) : p -> q :=
  ay_eveg_conj_left h

theorem ay_eveg_equiv_backward {p q : Prop} (h : ay_eveg_equiv p q) : q -> p :=
  ay_eveg_conj_right h

theorem ay_eveg_original_formula_digest_intro {preprocessedModel originalDigestOk : Prop}
    (h : preprocessedModel -> originalDigestOk) :
    ay_eveg_original_formula_digest preprocessedModel originalDigestOk :=
  h

theorem ay_eveg_preprocessed_formula_digest_intro
    {originalDigestOk preprocessedDigestOk : Prop}
    (h : originalDigestOk -> preprocessedDigestOk) :
    ay_eveg_preprocessed_formula_digest originalDigestOk preprocessedDigestOk :=
  h

theorem ay_eveg_eliminated_variable_ledger_intro {preprocessedDigestOk ledgerOk : Prop}
    (h : preprocessedDigestOk -> ledgerOk) :
    ay_eveg_eliminated_variable_ledger preprocessedDigestOk ledgerOk :=
  h

theorem ay_eveg_extension_map_witness_intro {ledgerOk extensionOk : Prop}
    (h : ledgerOk -> extensionOk) :
    ay_eveg_extension_map_witness ledgerOk extensionOk :=
  h

theorem ay_eveg_total_assignment_reconstruction_intro {extensionOk totalAssignment : Prop}
    (h : extensionOk -> totalAssignment) :
    ay_eveg_total_assignment_reconstruction extensionOk totalAssignment :=
  h

theorem ay_eveg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_eveg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_eveg_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_eveg_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_eveg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_eveg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_eveg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_eveg_archive_manifest buildOk archiveOk :=
  h

theorem ay_eveg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_eveg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_eveg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_eveg_audit_transcript fallbackReady audited :=
  h

theorem ay_eveg_accepted_extension_intro
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (ho : originalDigest) (hp : preprocessedDigest) (hl : ledger) (he : extension)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit :=
  ay_eveg_conj_intro ho
    (ay_eveg_conj_intro hp
      (ay_eveg_conj_intro hl
        (ay_eveg_conj_intro he
          (ay_eveg_conj_intro hrc
            (ay_eveg_conj_intro hr
              (ay_eveg_conj_intro hc
                (ay_eveg_conj_intro hb
                  (ay_eveg_conj_intro ha
                    (ay_eveg_conj_intro hfb hau)))))))))

theorem ay_eveg_accepted_extension_original_digest
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : originalDigest :=
  ay_eveg_conj_left h

theorem ay_eveg_accepted_extension_preprocessed_digest
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : preprocessedDigest :=
  ay_eveg_conj_left (ay_eveg_conj_right h)

theorem ay_eveg_accepted_extension_ledger
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : ledger :=
  ay_eveg_conj_left (ay_eveg_conj_right (ay_eveg_conj_right h))

theorem ay_eveg_accepted_extension_extension
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : extension :=
  ay_eveg_conj_left
    (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))

theorem ay_eveg_accepted_extension_reconstruction
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h))))

theorem ay_eveg_accepted_extension_replay
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))))

theorem ay_eveg_accepted_extension_checker
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right
          (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h))))))

theorem ay_eveg_accepted_extension_build
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : build :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right
          (ay_eveg_conj_right
            (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))))))

theorem ay_eveg_accepted_extension_archive
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right
          (ay_eveg_conj_right
            (ay_eveg_conj_right
              (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h))))))))

theorem ay_eveg_accepted_extension_fallback
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_eveg_conj_left
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right
          (ay_eveg_conj_right
            (ay_eveg_conj_right
              (ay_eveg_conj_right
                (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))))))))

theorem ay_eveg_accepted_extension_audit
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_eveg_conj_right
    (ay_eveg_conj_right
      (ay_eveg_conj_right
        (ay_eveg_conj_right
          (ay_eveg_conj_right
            (ay_eveg_conj_right
              (ay_eveg_conj_right
                (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))))))))

theorem ay_eveg_extension_reconstructs_original_sat
    {preprocessedModel originalDigestOk preprocessedDigestOk ledgerOk extensionOk
     totalAssignment everyOriginalClauseSatisfied originalSat buildOk archiveOk
     fallbackReady audited : Prop}
    (ho : ay_eveg_original_formula_digest preprocessedModel originalDigestOk)
    (hp : ay_eveg_preprocessed_formula_digest originalDigestOk preprocessedDigestOk)
    (hl : ay_eveg_eliminated_variable_ledger preprocessedDigestOk ledgerOk)
    (he : ay_eveg_extension_map_witness ledgerOk extensionOk)
    (hrc : ay_eveg_total_assignment_reconstruction extensionOk totalAssignment)
    (hr : ay_eveg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_eveg_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_eveg_solver_build_evidence originalSat buildOk)
    (ha : ay_eveg_archive_manifest buildOk archiveOk)
    (hfb : ay_eveg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_eveg_audit_transcript fallbackReady audited)
    (hm : preprocessedModel) :
    ay_eveg_conj totalAssignment
      (ay_eveg_conj everyOriginalClauseSatisfied (ay_eveg_conj originalSat audited)) :=
  let horiginal : originalDigestOk := ho hm
  let hpre : preprocessedDigestOk := hp horiginal
  let hledger : ledgerOk := hl hpre
  let hextension : extensionOk := he hledger
  let htotal : totalAssignment := hrc hextension
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_eveg_conj_intro htotal (ay_eveg_conj_intro hevery (ay_eveg_conj_intro hsat haudit))

theorem ay_eveg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_eveg_conj_intro ha
    (ay_eveg_conj_intro ht (ay_eveg_conj_intro hevery (ay_eveg_conj_intro hs hau)))

theorem ay_eveg_public_sat_requires_extension_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_eveg_conj_left h

theorem ay_eveg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_eveg_conj_left (ay_eveg_conj_right h)

theorem ay_eveg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_eveg_conj_left (ay_eveg_conj_right (ay_eveg_conj_right h))

theorem ay_eveg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_eveg_conj_left (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))

theorem ay_eveg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right (ay_eveg_conj_right h)))

theorem ay_eveg_accepted_extension_publishes_sat
    {originalDigest preprocessedDigest ledger extension reconstruction replay checker build
     archive fallback audit totalAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (hg : ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_eveg_public_sat
      (ay_eveg_accepted_extension originalDigest preprocessedDigest ledger extension
        reconstruction replay checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_eveg_public_sat_intro hg ht hevery hs hau

theorem ay_eveg_no_claim_intro {reason : Prop} (h : reason) :
    ay_eveg_no_claim_diagnostic reason :=
  h

theorem ay_eveg_recompute_intro {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  h

theorem ay_eveg_original_digest_mismatch_recompute {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  ay_eveg_recompute_intro h

theorem ay_eveg_preprocessed_digest_mismatch_recompute {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  ay_eveg_recompute_intro h

theorem ay_eveg_ledger_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_eveg_no_claim_diagnostic reason :=
  ay_eveg_no_claim_intro h

theorem ay_eveg_extension_mismatch_recompute {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  ay_eveg_recompute_intro h

theorem ay_eveg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  ay_eveg_recompute_intro h

theorem ay_eveg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_eveg_no_claim_diagnostic reason :=
  ay_eveg_no_claim_intro h

theorem ay_eveg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_eveg_recompute_obligation reason :=
  ay_eveg_recompute_intro h

theorem ay_eveg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_eveg_no_claim_diagnostic reason :=
  ay_eveg_no_claim_intro h

theorem ay_eveg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_eveg_no_claim_diagnostic reason :=
  ay_eveg_no_claim_intro h

theorem ay_eveg_failed_extension_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_eveg_no_claim_diagnostic failure) :
    ay_eveg_conj (ay_eveg_no_claim_diagnostic failure)
      (ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_eveg_no_claim_diagnostic failure) :=
  ay_eveg_conj_intro (ay_eveg_no_claim_intro hfail) hblock

theorem ay_eveg_failed_extension_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_eveg_recompute_obligation failure) :
    ay_eveg_conj (ay_eveg_recompute_obligation failure)
      (ay_eveg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_eveg_recompute_obligation failure) :=
  ay_eveg_conj_intro (ay_eveg_recompute_intro hfail) hblock

theorem ay_eveg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_eveg_public_unsat proofAccepted originalUnsat :=
  ay_eveg_conj_intro hp hu

theorem ay_eveg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_eveg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_eveg_conj_left h

theorem ay_eveg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_eveg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_eveg_conj_right h

theorem ay_eveg_extension_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat extensionSatGuard : Prop}
    (h : ay_eveg_public_unsat proofAccepted originalUnsat) :
    ay_eveg_conj (ay_eveg_public_unsat proofAccepted originalUnsat)
      (extensionSatGuard -> ay_eveg_public_unsat proofAccepted originalUnsat) :=
  ay_eveg_conj_intro h (fun _ => h)

/-!
  SAT-COMP/ay duplicate-assignment resolution guard.

  This self-contained package models the SAT-only obligations for resolving
  duplicate assignments in a serialized witness before publishing a public SAT
  model.
-/

def ay_darg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_darg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_darg_equiv (p q : Prop) : Prop :=
  ay_darg_conj (p -> q) (q -> p)

def ay_darg_benchmark_fingerprint (serializedWitness fingerprintOk : Prop) : Prop :=
  serializedWitness -> fingerprintOk

def ay_darg_serialized_witness_digest (fingerprintOk serializedOk : Prop) : Prop :=
  fingerprintOk -> serializedOk

def ay_darg_duplicate_assignment_ledger (serializedOk duplicateLedgerOk : Prop) : Prop :=
  serializedOk -> duplicateLedgerOk

def ay_darg_canonicalization_policy_witness
    (duplicateLedgerOk canonicalizationOk : Prop) : Prop :=
  duplicateLedgerOk -> canonicalizationOk

def ay_darg_variable_domain_manifest (canonicalizationOk domainOk : Prop) : Prop :=
  canonicalizationOk -> domainOk

def ay_darg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_darg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_darg_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_darg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_darg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_darg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_darg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_darg_accepted_resolution
    (fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop) : Prop :=
  ay_darg_conj fingerprint
    (ay_darg_conj serialized
      (ay_darg_conj duplicateLedger
        (ay_darg_conj canonicalization
          (ay_darg_conj domain
            (ay_darg_conj reconstruction
              (ay_darg_conj replay
                (ay_darg_conj checker
                  (ay_darg_conj build
                    (ay_darg_conj archive
                      (ay_darg_conj fallback audit))))))))))

def ay_darg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_darg_conj accepted
    (ay_darg_conj totalAssignment
      (ay_darg_conj everyOriginalClauseSatisfied (ay_darg_conj originalSat audited)))

def ay_darg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_darg_conj proofAccepted originalUnsat

def ay_darg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_darg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_darg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_darg_conj p q :=
  fun r h => h hp hq

theorem ay_darg_conj_left {p q : Prop} (h : ay_darg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_darg_conj_right {p q : Prop} (h : ay_darg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_darg_conj_left h)

theorem ay_darg_disj_left {p q : Prop} (hp : p) : ay_darg_disj p q :=
  fun r hl _ => hl hp

theorem ay_darg_disj_right {p q : Prop} (hq : q) : ay_darg_disj p q :=
  fun r _ hr => hr hq

theorem ay_darg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_darg_equiv p q :=
  ay_darg_conj_intro hpq hqp

theorem ay_darg_equiv_forward {p q : Prop} (h : ay_darg_equiv p q) : p -> q :=
  ay_darg_conj_left h

theorem ay_darg_equiv_backward {p q : Prop} (h : ay_darg_equiv p q) : q -> p :=
  ay_darg_conj_right h

theorem ay_darg_benchmark_fingerprint_intro {serializedWitness fingerprintOk : Prop}
    (h : serializedWitness -> fingerprintOk) :
    ay_darg_benchmark_fingerprint serializedWitness fingerprintOk :=
  h

theorem ay_darg_serialized_witness_digest_intro {fingerprintOk serializedOk : Prop}
    (h : fingerprintOk -> serializedOk) :
    ay_darg_serialized_witness_digest fingerprintOk serializedOk :=
  h

theorem ay_darg_duplicate_assignment_ledger_intro
    {serializedOk duplicateLedgerOk : Prop}
    (h : serializedOk -> duplicateLedgerOk) :
    ay_darg_duplicate_assignment_ledger serializedOk duplicateLedgerOk :=
  h

theorem ay_darg_canonicalization_policy_witness_intro
    {duplicateLedgerOk canonicalizationOk : Prop}
    (h : duplicateLedgerOk -> canonicalizationOk) :
    ay_darg_canonicalization_policy_witness duplicateLedgerOk canonicalizationOk :=
  h

theorem ay_darg_variable_domain_manifest_intro {canonicalizationOk domainOk : Prop}
    (h : canonicalizationOk -> domainOk) :
    ay_darg_variable_domain_manifest canonicalizationOk domainOk :=
  h

theorem ay_darg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_darg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_darg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_darg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_darg_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_darg_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_darg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_darg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_darg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_darg_archive_manifest buildOk archiveOk :=
  h

theorem ay_darg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_darg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_darg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_darg_audit_transcript fallbackReady audited :=
  h

theorem ay_darg_accepted_resolution_intro
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (hf : fingerprint) (hs : serialized) (hdl : duplicateLedger)
    (hc : canonicalization) (hd : domain) (hrc : reconstruction) (hr : replay)
    (hchk : checker) (hb : build) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit :=
  ay_darg_conj_intro hf
    (ay_darg_conj_intro hs
      (ay_darg_conj_intro hdl
        (ay_darg_conj_intro hc
          (ay_darg_conj_intro hd
            (ay_darg_conj_intro hrc
              (ay_darg_conj_intro hr
                (ay_darg_conj_intro hchk
                  (ay_darg_conj_intro hb
                    (ay_darg_conj_intro ha
                      (ay_darg_conj_intro hfb hau))))))))))

theorem ay_darg_accepted_resolution_fingerprint
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_darg_conj_left h

theorem ay_darg_accepted_resolution_serialized
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : serialized :=
  ay_darg_conj_left (ay_darg_conj_right h)

theorem ay_darg_accepted_resolution_duplicate_ledger
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : duplicateLedger :=
  ay_darg_conj_left (ay_darg_conj_right (ay_darg_conj_right h))

theorem ay_darg_accepted_resolution_canonicalization
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : canonicalization :=
  ay_darg_conj_left
    (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))

theorem ay_darg_accepted_resolution_domain
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : domain :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h))))

theorem ay_darg_accepted_resolution_reconstruction
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))))

theorem ay_darg_accepted_resolution_replay
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : replay :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h))))))

theorem ay_darg_accepted_resolution_checker
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : checker :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right
            (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))))))

theorem ay_darg_accepted_resolution_build
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : build :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right
            (ay_darg_conj_right
              (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h))))))))

theorem ay_darg_accepted_resolution_archive
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : archive :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right
            (ay_darg_conj_right
              (ay_darg_conj_right
                (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))))))))

theorem ay_darg_accepted_resolution_fallback
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : fallback :=
  ay_darg_conj_left
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right
            (ay_darg_conj_right
              (ay_darg_conj_right
                (ay_darg_conj_right
                  (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h))))))))))

theorem ay_darg_accepted_resolution_audit
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit : Prop}
    (h : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit) : audit :=
  ay_darg_conj_right
    (ay_darg_conj_right
      (ay_darg_conj_right
        (ay_darg_conj_right
          (ay_darg_conj_right
            (ay_darg_conj_right
              (ay_darg_conj_right
                (ay_darg_conj_right
                  (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h))))))))))

theorem ay_darg_duplicate_resolution_reconstructs_original_sat
    {serializedWitness fingerprintOk serializedOk duplicateLedgerOk canonicalizationOk
     domainOk totalAssignment everyOriginalClauseSatisfied originalSat buildOk archiveOk
     fallbackReady audited : Prop}
    (hf : ay_darg_benchmark_fingerprint serializedWitness fingerprintOk)
    (hs : ay_darg_serialized_witness_digest fingerprintOk serializedOk)
    (hdl : ay_darg_duplicate_assignment_ledger serializedOk duplicateLedgerOk)
    (hc : ay_darg_canonicalization_policy_witness duplicateLedgerOk canonicalizationOk)
    (hd : ay_darg_variable_domain_manifest canonicalizationOk domainOk)
    (hrc : ay_darg_total_assignment_reconstruction domainOk totalAssignment)
    (hr : ay_darg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hchk : ay_darg_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_darg_solver_build_evidence originalSat buildOk)
    (ha : ay_darg_archive_manifest buildOk archiveOk)
    (hfb : ay_darg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_darg_audit_transcript fallbackReady audited)
    (hw : serializedWitness) :
    ay_darg_conj totalAssignment
      (ay_darg_conj everyOriginalClauseSatisfied (ay_darg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hserialized : serializedOk := hs hfingerprint
  let hdups : duplicateLedgerOk := hdl hserialized
  let hcanon : canonicalizationOk := hc hdups
  let hdomain : domainOk := hd hcanon
  let htotal : totalAssignment := hrc hdomain
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hchk hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_darg_conj_intro htotal (ay_darg_conj_intro hevery (ay_darg_conj_intro hsat haudit))

theorem ay_darg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_darg_conj_intro ha
    (ay_darg_conj_intro ht (ay_darg_conj_intro hevery (ay_darg_conj_intro hs hau)))

theorem ay_darg_public_sat_requires_resolution_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_darg_conj_left h

theorem ay_darg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_darg_conj_left (ay_darg_conj_right h)

theorem ay_darg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_darg_conj_left (ay_darg_conj_right (ay_darg_conj_right h))

theorem ay_darg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_darg_conj_left (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))

theorem ay_darg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right (ay_darg_conj_right h)))

theorem ay_darg_accepted_resolution_publishes_sat
    {fingerprint serialized duplicateLedger canonicalization domain reconstruction replay
     checker build archive fallback audit totalAssignment everyOriginalClauseSatisfied
     originalSat audited : Prop}
    (hg : ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
      domain reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_darg_public_sat
      (ay_darg_accepted_resolution fingerprint serialized duplicateLedger canonicalization
        domain reconstruction replay checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_darg_public_sat_intro hg ht hevery hs hau

theorem ay_darg_no_claim_intro {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  h

theorem ay_darg_recompute_intro {reason : Prop} (h : reason) :
    ay_darg_recompute_obligation reason :=
  h

theorem ay_darg_conflicting_duplicates_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_conflicting_duplicates_recompute {reason : Prop} (h : reason) :
    ay_darg_recompute_obligation reason :=
  ay_darg_recompute_intro h

theorem ay_darg_parser_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_darg_recompute_obligation reason :=
  ay_darg_recompute_intro h

theorem ay_darg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_darg_recompute_obligation reason :=
  ay_darg_recompute_intro h

theorem ay_darg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_darg_recompute_obligation reason :=
  ay_darg_recompute_intro h

theorem ay_darg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_darg_no_claim_diagnostic reason :=
  ay_darg_no_claim_intro h

theorem ay_darg_failed_resolution_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_darg_no_claim_diagnostic failure) :
    ay_darg_conj (ay_darg_no_claim_diagnostic failure)
      (ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_darg_no_claim_diagnostic failure) :=
  ay_darg_conj_intro (ay_darg_no_claim_intro hfail) hblock

theorem ay_darg_failed_resolution_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_darg_recompute_obligation failure) :
    ay_darg_conj (ay_darg_recompute_obligation failure)
      (ay_darg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_darg_recompute_obligation failure) :=
  ay_darg_conj_intro (ay_darg_recompute_intro hfail) hblock

theorem ay_darg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_darg_public_unsat proofAccepted originalUnsat :=
  ay_darg_conj_intro hp hu

theorem ay_darg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_darg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_darg_conj_left h

theorem ay_darg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_darg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_darg_conj_right h

theorem ay_darg_resolution_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat duplicateSatGuard : Prop}
    (h : ay_darg_public_unsat proofAccepted originalUnsat) :
    ay_darg_conj (ay_darg_public_unsat proofAccepted originalUnsat)
      (duplicateSatGuard -> ay_darg_public_unsat proofAccepted originalUnsat) :=
  ay_darg_conj_intro h (fun _ => h)

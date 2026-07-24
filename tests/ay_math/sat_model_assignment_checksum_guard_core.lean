/-!
  SAT-COMP/ay assignment-checksum guard.

  This self-contained package models the SAT-only obligations for using an
  assignment checksum manifest before publishing a public SAT witness.
-/

def ay_acsg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_acsg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_acsg_equiv (p q : Prop) : Prop :=
  ay_acsg_conj (p -> q) (q -> p)

def ay_acsg_benchmark_fingerprint (serializedWitness fingerprintOk : Prop) : Prop :=
  serializedWitness -> fingerprintOk

def ay_acsg_serialized_witness_digest (fingerprintOk serializedOk : Prop) : Prop :=
  fingerprintOk -> serializedOk

def ay_acsg_assignment_checksum_manifest (serializedOk checksumOk : Prop) : Prop :=
  serializedOk -> checksumOk

def ay_acsg_variable_domain_manifest (checksumOk domainOk : Prop) : Prop :=
  checksumOk -> domainOk

def ay_acsg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_acsg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_acsg_model_checker_transcript
    (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_acsg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_acsg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_acsg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_acsg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_acsg_accepted_checksum
    (fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> serialized -> checksum -> domain -> reconstruction -> replay -> checker ->
      build -> archive -> fallback -> audit -> r) -> r

def ay_acsg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_acsg_conj accepted
    (ay_acsg_conj totalAssignment
      (ay_acsg_conj everyOriginalClauseSatisfied (ay_acsg_conj originalSat audited)))

def ay_acsg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_acsg_conj proofAccepted originalUnsat

def ay_acsg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_acsg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_acsg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_acsg_conj p q :=
  fun r h => h hp hq

theorem ay_acsg_conj_left {p q : Prop} (h : ay_acsg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_acsg_conj_right {p q : Prop} (h : ay_acsg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_acsg_conj_left h)

theorem ay_acsg_disj_left {p q : Prop} (hp : p) : ay_acsg_disj p q :=
  fun r hl _ => hl hp

theorem ay_acsg_disj_right {p q : Prop} (hq : q) : ay_acsg_disj p q :=
  fun r _ hr => hr hq

theorem ay_acsg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_acsg_equiv p q :=
  ay_acsg_conj_intro hpq hqp

theorem ay_acsg_equiv_forward {p q : Prop} (h : ay_acsg_equiv p q) : p -> q :=
  ay_acsg_conj_left h

theorem ay_acsg_equiv_backward {p q : Prop} (h : ay_acsg_equiv p q) : q -> p :=
  ay_acsg_conj_right h

theorem ay_acsg_benchmark_fingerprint_intro {serializedWitness fingerprintOk : Prop}
    (h : serializedWitness -> fingerprintOk) :
    ay_acsg_benchmark_fingerprint serializedWitness fingerprintOk :=
  h

theorem ay_acsg_serialized_witness_digest_intro {fingerprintOk serializedOk : Prop}
    (h : fingerprintOk -> serializedOk) :
    ay_acsg_serialized_witness_digest fingerprintOk serializedOk :=
  h

theorem ay_acsg_assignment_checksum_manifest_intro {serializedOk checksumOk : Prop}
    (h : serializedOk -> checksumOk) :
    ay_acsg_assignment_checksum_manifest serializedOk checksumOk :=
  h

theorem ay_acsg_variable_domain_manifest_intro {checksumOk domainOk : Prop}
    (h : checksumOk -> domainOk) :
    ay_acsg_variable_domain_manifest checksumOk domainOk :=
  h

theorem ay_acsg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_acsg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_acsg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_acsg_original_clause_satisfaction_replay totalAssignment
      everyOriginalClauseSatisfied :=
  h

theorem ay_acsg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_acsg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_acsg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_acsg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_acsg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_acsg_archive_manifest buildOk archiveOk :=
  h

theorem ay_acsg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_acsg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_acsg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_acsg_audit_transcript fallbackReady audited :=
  h

theorem ay_acsg_accepted_checksum_intro
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hs : serialized) (hc : checksum) (hd : domain)
    (hrc : reconstruction) (hr : replay) (hchk : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit :=
  fun r k => k hf hs hc hd hrc hr hchk hb ha hfb hau

theorem ay_acsg_accepted_checksum_fingerprint
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : fingerprint :=
  h fingerprint (fun hf _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_acsg_accepted_checksum_serialized
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : serialized :=
  h serialized (fun _ hs _ _ _ _ _ _ _ _ _ => hs)

theorem ay_acsg_accepted_checksum_checksum
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : checksum :=
  h checksum (fun _ _ hc _ _ _ _ _ _ _ _ => hc)

theorem ay_acsg_accepted_checksum_domain
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : domain :=
  h domain (fun _ _ _ hd _ _ _ _ _ _ _ => hd)

theorem ay_acsg_accepted_checksum_reconstruction
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : reconstruction :=
  h reconstruction (fun _ _ _ _ hrc _ _ _ _ _ _ => hrc)

theorem ay_acsg_accepted_checksum_replay
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ hr _ _ _ _ _ => hr)

theorem ay_acsg_accepted_checksum_checker
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ hchk _ _ _ _ => hchk)

theorem ay_acsg_accepted_checksum_build
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : build :=
  h build (fun _ _ _ _ _ _ _ hb _ _ _ => hb)

theorem ay_acsg_accepted_checksum_archive
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ ha _ _ => ha)

theorem ay_acsg_accepted_checksum_fallback
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : fallback :=
  h fallback (fun _ _ _ _ _ _ _ _ _ hfb _ => hfb)

theorem ay_acsg_accepted_checksum_audit
    {fingerprint serialized checksum domain reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain reconstruction replay
      checker build archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_acsg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_acsg_conj_intro ha
    (ay_acsg_conj_intro ht
      (ay_acsg_conj_intro hc (ay_acsg_conj_intro hs hau)))

theorem ay_acsg_public_sat_requires_checksum_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_acsg_conj_left h

theorem ay_acsg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_acsg_conj_left (ay_acsg_conj_right h)

theorem ay_acsg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_acsg_conj_left (ay_acsg_conj_right (ay_acsg_conj_right h))

theorem ay_acsg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_acsg_conj_left
    (ay_acsg_conj_right (ay_acsg_conj_right (ay_acsg_conj_right h)))

theorem ay_acsg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_acsg_conj_right
    (ay_acsg_conj_right (ay_acsg_conj_right (ay_acsg_conj_right h)))

theorem ay_acsg_checksum_preserves_reconstructed_total_assignment
    {fingerprint serialized checksum domain totalAssignment everyOriginalClauseSatisfied
     originalSat build archive fallback audited : Prop}
    (h : ay_acsg_accepted_checksum fingerprint serialized checksum domain totalAssignment
      everyOriginalClauseSatisfied originalSat build archive fallback audited) :
    ay_acsg_public_sat
      (ay_acsg_accepted_checksum fingerprint serialized checksum domain totalAssignment
        everyOriginalClauseSatisfied originalSat build archive fallback audited)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_acsg_public_sat_intro
    h
    (ay_acsg_accepted_checksum_reconstruction h)
    (ay_acsg_accepted_checksum_replay h)
    (ay_acsg_accepted_checksum_checker h)
    (ay_acsg_accepted_checksum_audit h)

theorem ay_acsg_checksum_equivalent_assignments_preserve_truth
    {assignmentFromWitness assignmentFromChecksum originalTruth : Prop}
    (h : ay_acsg_equiv assignmentFromWitness assignmentFromChecksum)
    (hc : assignmentFromChecksum -> originalTruth)
    (hw : assignmentFromWitness) : originalTruth :=
  hc (ay_acsg_equiv_forward h hw)

theorem ay_acsg_no_claim_intro {reason : Prop} (h : reason) :
    ay_acsg_no_claim_diagnostic reason :=
  h

theorem ay_acsg_recompute_intro {reason : Prop} (h : reason) :
    ay_acsg_recompute_obligation reason :=
  h

theorem ay_acsg_checksum_mismatch_no_claim {checksumMismatch : Prop}
    (h : checksumMismatch) :
    ay_acsg_no_claim_diagnostic checksumMismatch :=
  ay_acsg_no_claim_intro h

theorem ay_acsg_checksum_mismatch_recompute {checksumMismatch : Prop}
    (h : checksumMismatch) :
    ay_acsg_recompute_obligation checksumMismatch :=
  ay_acsg_recompute_intro h

theorem ay_acsg_domain_mismatch_no_claim {domainMismatch : Prop}
    (h : domainMismatch) :
    ay_acsg_no_claim_diagnostic domainMismatch :=
  ay_acsg_no_claim_intro h

theorem ay_acsg_reconstruction_mismatch_recompute {reconstructionMismatch : Prop}
    (h : reconstructionMismatch) :
    ay_acsg_recompute_obligation reconstructionMismatch :=
  ay_acsg_recompute_intro h

theorem ay_acsg_replay_mismatch_recompute {replayMismatch : Prop}
    (h : replayMismatch) :
    ay_acsg_recompute_obligation replayMismatch :=
  ay_acsg_recompute_intro h

theorem ay_acsg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_acsg_no_claim_diagnostic checkerMismatch :=
  ay_acsg_no_claim_intro h

theorem ay_acsg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_acsg_recompute_obligation buildMismatch :=
  ay_acsg_recompute_intro h

theorem ay_acsg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_acsg_no_claim_diagnostic archiveMismatch :=
  ay_acsg_no_claim_intro h

theorem ay_acsg_failed_checksum_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_acsg_no_claim_diagnostic failure)
    (noBless : ay_acsg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_acsg_failed_checksum_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_acsg_recompute_obligation failure)
    (hfailure : failure) :
    ay_acsg_recompute_obligation failure :=
  fallback hfailure

theorem ay_acsg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_acsg_public_unsat proofAccepted originalUnsat :=
  ay_acsg_conj_intro hp hu

theorem ay_acsg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_acsg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_acsg_conj_left h

theorem ay_acsg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_acsg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_acsg_conj_right h

theorem ay_acsg_checksum_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_acsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_acsg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_acsg_public_unsat_claim hUnsat

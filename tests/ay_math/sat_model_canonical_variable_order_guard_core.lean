/-!
  SAT-COMP/ay canonical variable-order guard.

  This self-contained package models the SAT-only obligations for treating
  serialized witness variable order as presentation data before publishing a
  public SAT model.
-/

def ay_cvog_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_cvog_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_cvog_equiv (p q : Prop) : Prop :=
  ay_cvog_conj (p -> q) (q -> p)

def ay_cvog_benchmark_fingerprint (serializedWitness fingerprintOk : Prop) : Prop :=
  serializedWitness -> fingerprintOk

def ay_cvog_serialized_witness_digest (fingerprintOk serializedOk : Prop) : Prop :=
  fingerprintOk -> serializedOk

def ay_cvog_parser_transcript (serializedOk parsedOk : Prop) : Prop :=
  serializedOk -> parsedOk

def ay_cvog_variable_order_permutation_ledger (parsedOk orderOk : Prop) : Prop :=
  parsedOk -> orderOk

def ay_cvog_canonicalization_witness (orderOk canonicalOk : Prop) : Prop :=
  orderOk -> canonicalOk

def ay_cvog_total_assignment_reconstruction (canonicalOk totalAssignment : Prop) : Prop :=
  canonicalOk -> totalAssignment

def ay_cvog_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_cvog_model_checker_transcript
    (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_cvog_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_cvog_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_cvog_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_cvog_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_cvog_accepted_canonicalization
    (fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> serialized -> parser -> order -> canonical -> reconstruction -> replay ->
      checker -> build -> archive -> fallback -> audit -> r) -> r

def ay_cvog_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_cvog_conj accepted
    (ay_cvog_conj totalAssignment
      (ay_cvog_conj everyOriginalClauseSatisfied (ay_cvog_conj originalSat audited)))

def ay_cvog_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_cvog_conj proofAccepted originalUnsat

def ay_cvog_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_cvog_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_cvog_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_cvog_conj p q :=
  fun r h => h hp hq

theorem ay_cvog_conj_left {p q : Prop} (h : ay_cvog_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cvog_conj_right {p q : Prop} (h : ay_cvog_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cvog_conj_left h)

theorem ay_cvog_disj_left {p q : Prop} (hp : p) : ay_cvog_disj p q :=
  fun r hl _ => hl hp

theorem ay_cvog_disj_right {p q : Prop} (hq : q) : ay_cvog_disj p q :=
  fun r _ hr => hr hq

theorem ay_cvog_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_cvog_equiv p q :=
  ay_cvog_conj_intro hpq hqp

theorem ay_cvog_equiv_forward {p q : Prop} (h : ay_cvog_equiv p q) : p -> q :=
  ay_cvog_conj_left h

theorem ay_cvog_equiv_backward {p q : Prop} (h : ay_cvog_equiv p q) : q -> p :=
  ay_cvog_conj_right h

theorem ay_cvog_benchmark_fingerprint_intro {serializedWitness fingerprintOk : Prop}
    (h : serializedWitness -> fingerprintOk) :
    ay_cvog_benchmark_fingerprint serializedWitness fingerprintOk :=
  h

theorem ay_cvog_serialized_witness_digest_intro {fingerprintOk serializedOk : Prop}
    (h : fingerprintOk -> serializedOk) :
    ay_cvog_serialized_witness_digest fingerprintOk serializedOk :=
  h

theorem ay_cvog_parser_transcript_intro {serializedOk parsedOk : Prop}
    (h : serializedOk -> parsedOk) :
    ay_cvog_parser_transcript serializedOk parsedOk :=
  h

theorem ay_cvog_variable_order_permutation_ledger_intro {parsedOk orderOk : Prop}
    (h : parsedOk -> orderOk) :
    ay_cvog_variable_order_permutation_ledger parsedOk orderOk :=
  h

theorem ay_cvog_canonicalization_witness_intro {orderOk canonicalOk : Prop}
    (h : orderOk -> canonicalOk) :
    ay_cvog_canonicalization_witness orderOk canonicalOk :=
  h

theorem ay_cvog_total_assignment_reconstruction_intro
    {canonicalOk totalAssignment : Prop}
    (h : canonicalOk -> totalAssignment) :
    ay_cvog_total_assignment_reconstruction canonicalOk totalAssignment :=
  h

theorem ay_cvog_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_cvog_original_clause_satisfaction_replay totalAssignment
      everyOriginalClauseSatisfied :=
  h

theorem ay_cvog_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_cvog_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_cvog_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_cvog_solver_build_evidence originalSat buildOk :=
  h

theorem ay_cvog_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_cvog_archive_manifest buildOk archiveOk :=
  h

theorem ay_cvog_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_cvog_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_cvog_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_cvog_audit_transcript fallbackReady audited :=
  h

theorem ay_cvog_accepted_canonicalization_intro
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hs : serialized) (hp : parser) (ho : order) (hc : canonical)
    (hrc : reconstruction) (hr : replay) (hchk : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit :=
  fun r k => k hf hs hp ho hc hrc hr hchk hb ha hfb hau

theorem ay_cvog_accepted_canonicalization_fingerprint
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  h fingerprint (fun hf _ _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_cvog_accepted_canonicalization_serialized
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : serialized :=
  h serialized (fun _ hs _ _ _ _ _ _ _ _ _ _ => hs)

theorem ay_cvog_accepted_canonicalization_parser
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : parser :=
  h parser (fun _ _ hp _ _ _ _ _ _ _ _ _ => hp)

theorem ay_cvog_accepted_canonicalization_order
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : order :=
  h order (fun _ _ _ ho _ _ _ _ _ _ _ _ => ho)

theorem ay_cvog_accepted_canonicalization_canonical
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : canonical :=
  h canonical (fun _ _ _ _ hc _ _ _ _ _ _ _ => hc)

theorem ay_cvog_accepted_canonicalization_reconstruction
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  h reconstruction (fun _ _ _ _ _ hrc _ _ _ _ _ _ => hrc)

theorem ay_cvog_accepted_canonicalization_replay
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ hr _ _ _ _ _ => hr)

theorem ay_cvog_accepted_canonicalization_checker
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ hchk _ _ _ _ => hchk)

theorem ay_cvog_accepted_canonicalization_build
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : build :=
  h build (fun _ _ _ _ _ _ _ _ hb _ _ _ => hb)

theorem ay_cvog_accepted_canonicalization_archive
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ ha _ _ => ha)

theorem ay_cvog_accepted_canonicalization_fallback
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : fallback :=
  h fallback (fun _ _ _ _ _ _ _ _ _ _ hfb _ => hfb)

theorem ay_cvog_accepted_canonicalization_audit
    {fingerprint serialized parser order canonical reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      reconstruction replay checker build archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_cvog_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_cvog_conj_intro ha
    (ay_cvog_conj_intro ht
      (ay_cvog_conj_intro hc (ay_cvog_conj_intro hs hau)))

theorem ay_cvog_public_sat_requires_order_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_cvog_conj_left h

theorem ay_cvog_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_cvog_conj_left (ay_cvog_conj_right h)

theorem ay_cvog_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_cvog_conj_left (ay_cvog_conj_right (ay_cvog_conj_right h))

theorem ay_cvog_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_cvog_conj_left
    (ay_cvog_conj_right (ay_cvog_conj_right (ay_cvog_conj_right h)))

theorem ay_cvog_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_cvog_conj_right
    (ay_cvog_conj_right (ay_cvog_conj_right (ay_cvog_conj_right h)))

theorem ay_cvog_accepted_canonicalization_reconstructs_original_sat
    {fingerprint serialized parser order canonical totalAssignment everyOriginalClauseSatisfied
     originalSat build archive fallback audited : Prop}
    (h : ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
      totalAssignment everyOriginalClauseSatisfied originalSat build archive fallback audited) :
    ay_cvog_public_sat
      (ay_cvog_accepted_canonicalization fingerprint serialized parser order canonical
        totalAssignment everyOriginalClauseSatisfied originalSat build archive fallback audited)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_cvog_public_sat_intro
    h
    (ay_cvog_accepted_canonicalization_reconstruction h)
    (ay_cvog_accepted_canonicalization_replay h)
    (ay_cvog_accepted_canonicalization_checker h)
    (ay_cvog_accepted_canonicalization_audit h)

theorem ay_cvog_variable_order_is_presentation_only
    {assignmentUnderInputOrder assignmentUnderCanonicalOrder originalTruth : Prop}
    (h : ay_cvog_equiv assignmentUnderInputOrder assignmentUnderCanonicalOrder)
    (hc : assignmentUnderCanonicalOrder -> originalTruth)
    (ha : assignmentUnderInputOrder) : originalTruth :=
  hc (ay_cvog_equiv_forward h ha)

theorem ay_cvog_no_claim_intro {reason : Prop} (h : reason) :
    ay_cvog_no_claim_diagnostic reason :=
  h

theorem ay_cvog_recompute_intro {reason : Prop} (h : reason) :
    ay_cvog_recompute_obligation reason :=
  h

theorem ay_cvog_ordering_mismatch_no_claim {orderingMismatch : Prop}
    (h : orderingMismatch) :
    ay_cvog_no_claim_diagnostic orderingMismatch :=
  ay_cvog_no_claim_intro h

theorem ay_cvog_permutation_mismatch_recompute {permutationMismatch : Prop}
    (h : permutationMismatch) :
    ay_cvog_recompute_obligation permutationMismatch :=
  ay_cvog_recompute_intro h

theorem ay_cvog_parser_mismatch_no_claim {parserMismatch : Prop}
    (h : parserMismatch) :
    ay_cvog_no_claim_diagnostic parserMismatch :=
  ay_cvog_no_claim_intro h

theorem ay_cvog_reconstruction_mismatch_recompute {reconstructionMismatch : Prop}
    (h : reconstructionMismatch) :
    ay_cvog_recompute_obligation reconstructionMismatch :=
  ay_cvog_recompute_intro h

theorem ay_cvog_replay_mismatch_recompute {replayMismatch : Prop}
    (h : replayMismatch) :
    ay_cvog_recompute_obligation replayMismatch :=
  ay_cvog_recompute_intro h

theorem ay_cvog_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_cvog_no_claim_diagnostic checkerMismatch :=
  ay_cvog_no_claim_intro h

theorem ay_cvog_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_cvog_recompute_obligation buildMismatch :=
  ay_cvog_recompute_intro h

theorem ay_cvog_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_cvog_no_claim_diagnostic archiveMismatch :=
  ay_cvog_no_claim_intro h

theorem ay_cvog_failed_order_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_cvog_no_claim_diagnostic failure)
    (noBless : ay_cvog_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_cvog_failed_order_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_cvog_recompute_obligation failure)
    (hfailure : failure) :
    ay_cvog_recompute_obligation failure :=
  fallback hfailure

theorem ay_cvog_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_cvog_public_unsat proofAccepted originalUnsat :=
  ay_cvog_conj_intro hp hu

theorem ay_cvog_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_cvog_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_cvog_conj_left h

theorem ay_cvog_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_cvog_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cvog_conj_right h

theorem ay_cvog_order_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_cvog_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_cvog_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cvog_public_unsat_claim hUnsat

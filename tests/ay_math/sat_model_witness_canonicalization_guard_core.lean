/-!
  SAT-COMP/ay model witness canonicalization guard.

  This self-contained package models the SAT-only obligations for sorting,
  compressing, or normalizing assignment witnesses before publication.
-/

def ay_wcg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_wcg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_wcg_equiv (p q : Prop) : Prop :=
  ay_wcg_conj (p -> q) (q -> p)

def ay_wcg_original_formula_fingerprint
    (rawWitness originalFingerprintOk : Prop) : Prop :=
  rawWitness -> originalFingerprintOk

def ay_wcg_raw_witness_digest (originalFingerprintOk rawDigestOk : Prop) : Prop :=
  originalFingerprintOk -> rawDigestOk

def ay_wcg_canonical_witness_digest (rawDigestOk canonicalDigestOk : Prop) : Prop :=
  rawDigestOk -> canonicalDigestOk

def ay_wcg_canonicalization_policy_manifest
    (canonicalDigestOk policyOk : Prop) : Prop :=
  canonicalDigestOk -> policyOk

def ay_wcg_variable_ordering_digest (policyOk orderOk : Prop) : Prop :=
  policyOk -> orderOk

def ay_wcg_duplicate_conflict_resolution_witness
    (orderOk conflictResolutionOk : Prop) : Prop :=
  orderOk -> conflictResolutionOk

def ay_wcg_parser_transcript
    (conflictResolutionOk parserOk : Prop) : Prop :=
  conflictResolutionOk -> parserOk

def ay_wcg_completed_assignment_digest
    (parserOk completedAssignmentOk : Prop) : Prop :=
  parserOk -> completedAssignmentOk

def ay_wcg_original_clause_satisfaction_replay
    (completedAssignmentOk originalClausesSatisfied : Prop) : Prop :=
  completedAssignmentOk -> originalClausesSatisfied

def ay_wcg_solver_build_evidence (originalClausesSatisfied buildOk : Prop) : Prop :=
  originalClausesSatisfied -> buildOk

def ay_wcg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_wcg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_wcg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_wcg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_wcg_accepted_canonicalization
    (originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (originalFp -> raw -> canonical -> policy -> order -> conflict -> parser -> completed ->
      replay -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_wcg_public_sat
    (accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop) : Prop :=
  ay_wcg_conj accepted
    (ay_wcg_conj completedAssignment
      (ay_wcg_conj rawCanonicalAgreement
        (ay_wcg_conj originalClausesSatisfied
          (ay_wcg_conj validatorOk (ay_wcg_conj archiveOk audited)))))

def ay_wcg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_wcg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_wcg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_wcg_conj p q :=
  fun r h => h hp hq

theorem ay_wcg_conj_left {p q : Prop} (h : ay_wcg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_wcg_conj_right {p q : Prop} (h : ay_wcg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_wcg_conj_left h)

theorem ay_wcg_disj_left {p q : Prop} (hp : p) : ay_wcg_disj p q :=
  fun r hl _ => hl hp

theorem ay_wcg_disj_right {p q : Prop} (hq : q) : ay_wcg_disj p q :=
  fun r _ hr => hr hq

theorem ay_wcg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_wcg_equiv p q :=
  ay_wcg_conj_intro hpq hqp

theorem ay_wcg_equiv_forward {p q : Prop} (h : ay_wcg_equiv p q) : p -> q :=
  ay_wcg_conj_left h

theorem ay_wcg_equiv_backward {p q : Prop} (h : ay_wcg_equiv p q) : q -> p :=
  ay_wcg_conj_right h

theorem ay_wcg_original_formula_fingerprint_intro
    {rawWitness originalFingerprintOk : Prop}
    (h : rawWitness -> originalFingerprintOk) :
    ay_wcg_original_formula_fingerprint rawWitness originalFingerprintOk :=
  h

theorem ay_wcg_raw_witness_digest_intro {originalFingerprintOk rawDigestOk : Prop}
    (h : originalFingerprintOk -> rawDigestOk) :
    ay_wcg_raw_witness_digest originalFingerprintOk rawDigestOk :=
  h

theorem ay_wcg_canonical_witness_digest_intro {rawDigestOk canonicalDigestOk : Prop}
    (h : rawDigestOk -> canonicalDigestOk) :
    ay_wcg_canonical_witness_digest rawDigestOk canonicalDigestOk :=
  h

theorem ay_wcg_canonicalization_policy_manifest_intro
    {canonicalDigestOk policyOk : Prop}
    (h : canonicalDigestOk -> policyOk) :
    ay_wcg_canonicalization_policy_manifest canonicalDigestOk policyOk :=
  h

theorem ay_wcg_variable_ordering_digest_intro {policyOk orderOk : Prop}
    (h : policyOk -> orderOk) :
    ay_wcg_variable_ordering_digest policyOk orderOk :=
  h

theorem ay_wcg_duplicate_conflict_resolution_witness_intro
    {orderOk conflictResolutionOk : Prop}
    (h : orderOk -> conflictResolutionOk) :
    ay_wcg_duplicate_conflict_resolution_witness orderOk conflictResolutionOk :=
  h

theorem ay_wcg_parser_transcript_intro {conflictResolutionOk parserOk : Prop}
    (h : conflictResolutionOk -> parserOk) :
    ay_wcg_parser_transcript conflictResolutionOk parserOk :=
  h

theorem ay_wcg_completed_assignment_digest_intro {parserOk completedAssignmentOk : Prop}
    (h : parserOk -> completedAssignmentOk) :
    ay_wcg_completed_assignment_digest parserOk completedAssignmentOk :=
  h

theorem ay_wcg_original_clause_satisfaction_replay_intro
    {completedAssignmentOk originalClausesSatisfied : Prop}
    (h : completedAssignmentOk -> originalClausesSatisfied) :
    ay_wcg_original_clause_satisfaction_replay completedAssignmentOk
      originalClausesSatisfied :=
  h

theorem ay_wcg_solver_build_evidence_intro
    {originalClausesSatisfied buildOk : Prop}
    (h : originalClausesSatisfied -> buildOk) :
    ay_wcg_solver_build_evidence originalClausesSatisfied buildOk :=
  h

theorem ay_wcg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_wcg_validator_gate buildOk validatorOk :=
  h

theorem ay_wcg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_wcg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_wcg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_wcg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_wcg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_wcg_audit_transcript fallbackReady audited :=
  h

theorem ay_wcg_accepted_canonicalization_intro
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (hof : originalFp) (hr : raw) (hc : canonical) (hp : policy) (ho : order)
    (hcf : conflict) (hpa : parser) (hca : completed) (hre : replay) (hb : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict parser
      completed replay build validator archive fallback audit :=
  fun r k => k hof hr hc hp ho hcf hpa hca hre hb hv har hfb hau

theorem ay_wcg_accepted_canonicalization_raw
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : raw :=
  h raw (fun _ hr _ _ _ _ _ _ _ _ _ _ _ _ => hr)

theorem ay_wcg_accepted_canonicalization_canonical
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : canonical :=
  h canonical (fun _ _ hc _ _ _ _ _ _ _ _ _ _ _ => hc)

theorem ay_wcg_accepted_canonicalization_policy
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : policy :=
  h policy (fun _ _ _ hp _ _ _ _ _ _ _ _ _ _ => hp)

theorem ay_wcg_accepted_canonicalization_order
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : order :=
  h order (fun _ _ _ _ ho _ _ _ _ _ _ _ _ _ => ho)

theorem ay_wcg_accepted_canonicalization_conflict
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : conflict :=
  h conflict (fun _ _ _ _ _ hcf _ _ _ _ _ _ _ _ => hcf)

theorem ay_wcg_accepted_canonicalization_parser
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : parser :=
  h parser (fun _ _ _ _ _ _ hpa _ _ _ _ _ _ _ => hpa)

theorem ay_wcg_accepted_canonicalization_completed
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : completed :=
  h completed (fun _ _ _ _ _ _ _ hca _ _ _ _ _ _ => hca)

theorem ay_wcg_accepted_canonicalization_replay
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ _ hre _ _ _ _ _ => hre)

theorem ay_wcg_accepted_canonicalization_validator
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_wcg_accepted_canonicalization_archive
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_wcg_accepted_canonicalization_audit
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_wcg_public_sat_intro
    {accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (ha : accepted) (hc : completedAssignment) (hag : rawCanonicalAgreement)
    (hr : originalClausesSatisfied) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_wcg_public_sat accepted completedAssignment rawCanonicalAgreement
      originalClausesSatisfied validatorOk archiveOk audited :=
  ay_wcg_conj_intro ha
    (ay_wcg_conj_intro hc
      (ay_wcg_conj_intro hag
        (ay_wcg_conj_intro hr
          (ay_wcg_conj_intro hv (ay_wcg_conj_intro har hau)))))

theorem ay_wcg_public_sat_requires_canonicalization_guard
    {accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_wcg_public_sat accepted completedAssignment rawCanonicalAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : accepted :=
  ay_wcg_conj_left h

theorem ay_wcg_public_sat_completed_assignment
    {accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_wcg_public_sat accepted completedAssignment rawCanonicalAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : completedAssignment :=
  ay_wcg_conj_left (ay_wcg_conj_right h)

theorem ay_wcg_public_sat_raw_canonical_agreement
    {accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_wcg_public_sat accepted completedAssignment rawCanonicalAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : rawCanonicalAgreement :=
  ay_wcg_conj_left (ay_wcg_conj_right (ay_wcg_conj_right h))

theorem ay_wcg_public_sat_original_clauses
    {accepted completedAssignment rawCanonicalAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_wcg_public_sat accepted completedAssignment rawCanonicalAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : originalClausesSatisfied :=
  ay_wcg_conj_left
    (ay_wcg_conj_right (ay_wcg_conj_right (ay_wcg_conj_right h)))

theorem ay_wcg_accepted_canonicalization_preserves_original_sat
    {originalFp raw canonical policy order conflict parser completed replay build validator
     archive fallback audit : Prop}
    (h : ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict
      parser completed replay build validator archive fallback audit) :
    ay_wcg_public_sat
      (ay_wcg_accepted_canonicalization originalFp raw canonical policy order conflict parser
        completed replay build validator archive fallback audit)
      completed canonical replay validator archive audit :=
  ay_wcg_public_sat_intro
    h
    (ay_wcg_accepted_canonicalization_completed h)
    (ay_wcg_accepted_canonicalization_canonical h)
    (ay_wcg_accepted_canonicalization_replay h)
    (ay_wcg_accepted_canonicalization_validator h)
    (ay_wcg_accepted_canonicalization_archive h)
    (ay_wcg_accepted_canonicalization_audit h)

theorem ay_wcg_canonical_witness_agrees_with_raw_justified
    {rawWitness canonicalWitness justifiedNormalization preservedTruth : Prop}
    (h : ay_wcg_equiv rawWitness canonicalWitness)
    (hj : canonicalWitness -> justifiedNormalization)
    (hp : justifiedNormalization -> preservedTruth)
    (hr : rawWitness) : preservedTruth :=
  hp (hj (ay_wcg_equiv_forward h hr))

theorem ay_wcg_no_claim_intro {reason : Prop} (h : reason) :
    ay_wcg_no_claim_diagnostic reason :=
  h

theorem ay_wcg_recompute_intro {reason : Prop} (h : reason) :
    ay_wcg_recompute_obligation reason :=
  h

theorem ay_wcg_raw_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_canonical_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_wcg_recompute_obligation mismatch :=
  ay_wcg_recompute_intro h

theorem ay_wcg_policy_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_order_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_wcg_recompute_obligation mismatch :=
  ay_wcg_recompute_intro h

theorem ay_wcg_conflict_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_parser_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_wcg_recompute_obligation mismatch :=
  ay_wcg_recompute_intro h

theorem ay_wcg_completion_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_wcg_recompute_obligation mismatch :=
  ay_wcg_recompute_intro h

theorem ay_wcg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_wcg_recompute_obligation mismatch :=
  ay_wcg_recompute_intro h

theorem ay_wcg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_wcg_no_claim_diagnostic mismatch :=
  ay_wcg_no_claim_intro h

theorem ay_wcg_failed_canonicalization_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_wcg_no_claim_diagnostic failure)
    (noBless : ay_wcg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_wcg_failed_canonicalization_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_wcg_recompute_obligation failure)
    (hfailure : failure) :
    ay_wcg_recompute_obligation failure :=
  fallback hfailure

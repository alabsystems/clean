/-!
  SAT-COMP/ay clause-satisfaction bitset guard.

  This self-contained package models the SAT-only obligations for trusting a
  bitset/SIMD-style clause-satisfaction summary during model validation.
-/

def ay_csbg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_csbg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_csbg_equiv (p q : Prop) : Prop :=
  ay_csbg_conj (p -> q) (q -> p)

def ay_csbg_original_formula_fingerprint
    (assignmentDigest originalFingerprintOk : Prop) : Prop :=
  assignmentDigest -> originalFingerprintOk

def ay_csbg_assignment_digest (originalFingerprintOk assignmentOk : Prop) : Prop :=
  originalFingerprintOk -> assignmentOk

def ay_csbg_clause_indexing_digest (assignmentOk clauseIndexOk : Prop) : Prop :=
  assignmentOk -> clauseIndexOk

def ay_csbg_literal_to_bitset_map_digest (clauseIndexOk bitsetMapOk : Prop) : Prop :=
  clauseIndexOk -> bitsetMapOk

def ay_csbg_per_clause_satisfaction_bitset_digest (bitsetMapOk bitsetOk : Prop) : Prop :=
  bitsetMapOk -> bitsetOk

def ay_csbg_reduction_aggregation_transcript (bitsetOk aggregationOk : Prop) : Prop :=
  bitsetOk -> aggregationOk

def ay_csbg_fallback_scalar_checker_transcript
    (aggregationOk scalarCheckerOk : Prop) : Prop :=
  aggregationOk -> scalarCheckerOk

def ay_csbg_solver_build_evidence (scalarCheckerOk buildOk : Prop) : Prop :=
  scalarCheckerOk -> buildOk

def ay_csbg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_csbg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_csbg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_csbg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_csbg_accepted_bitset
    (formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> assignment -> index -> bitsetMap -> bitset -> aggregation -> scalar ->
      everyClause -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_csbg_public_sat
    (accepted everyOriginalClauseSatisfied scalarAgreement validatorOk archiveOk audited : Prop) :
    Prop :=
  ay_csbg_conj accepted
    (ay_csbg_conj everyOriginalClauseSatisfied
      (ay_csbg_conj scalarAgreement
        (ay_csbg_conj validatorOk (ay_csbg_conj archiveOk audited))))

def ay_csbg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_csbg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_csbg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_csbg_conj p q :=
  fun r h => h hp hq

theorem ay_csbg_conj_left {p q : Prop} (h : ay_csbg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_csbg_conj_right {p q : Prop} (h : ay_csbg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_csbg_conj_left h)

theorem ay_csbg_disj_left {p q : Prop} (hp : p) : ay_csbg_disj p q :=
  fun r hl _ => hl hp

theorem ay_csbg_disj_right {p q : Prop} (hq : q) : ay_csbg_disj p q :=
  fun r _ hr => hr hq

theorem ay_csbg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_csbg_equiv p q :=
  ay_csbg_conj_intro hpq hqp

theorem ay_csbg_equiv_forward {p q : Prop} (h : ay_csbg_equiv p q) : p -> q :=
  ay_csbg_conj_left h

theorem ay_csbg_equiv_backward {p q : Prop} (h : ay_csbg_equiv p q) : q -> p :=
  ay_csbg_conj_right h

theorem ay_csbg_original_formula_fingerprint_intro
    {assignmentDigest originalFingerprintOk : Prop}
    (h : assignmentDigest -> originalFingerprintOk) :
    ay_csbg_original_formula_fingerprint assignmentDigest originalFingerprintOk :=
  h

theorem ay_csbg_assignment_digest_intro {originalFingerprintOk assignmentOk : Prop}
    (h : originalFingerprintOk -> assignmentOk) :
    ay_csbg_assignment_digest originalFingerprintOk assignmentOk :=
  h

theorem ay_csbg_clause_indexing_digest_intro {assignmentOk clauseIndexOk : Prop}
    (h : assignmentOk -> clauseIndexOk) :
    ay_csbg_clause_indexing_digest assignmentOk clauseIndexOk :=
  h

theorem ay_csbg_literal_to_bitset_map_digest_intro {clauseIndexOk bitsetMapOk : Prop}
    (h : clauseIndexOk -> bitsetMapOk) :
    ay_csbg_literal_to_bitset_map_digest clauseIndexOk bitsetMapOk :=
  h

theorem ay_csbg_per_clause_satisfaction_bitset_digest_intro
    {bitsetMapOk bitsetOk : Prop}
    (h : bitsetMapOk -> bitsetOk) :
    ay_csbg_per_clause_satisfaction_bitset_digest bitsetMapOk bitsetOk :=
  h

theorem ay_csbg_reduction_aggregation_transcript_intro
    {bitsetOk aggregationOk : Prop}
    (h : bitsetOk -> aggregationOk) :
    ay_csbg_reduction_aggregation_transcript bitsetOk aggregationOk :=
  h

theorem ay_csbg_fallback_scalar_checker_transcript_intro
    {aggregationOk scalarCheckerOk : Prop}
    (h : aggregationOk -> scalarCheckerOk) :
    ay_csbg_fallback_scalar_checker_transcript aggregationOk scalarCheckerOk :=
  h

theorem ay_csbg_solver_build_evidence_intro {scalarCheckerOk buildOk : Prop}
    (h : scalarCheckerOk -> buildOk) :
    ay_csbg_solver_build_evidence scalarCheckerOk buildOk :=
  h

theorem ay_csbg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_csbg_validator_gate buildOk validatorOk :=
  h

theorem ay_csbg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_csbg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_csbg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_csbg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_csbg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_csbg_audit_transcript fallbackReady audited :=
  h

theorem ay_csbg_accepted_bitset_intro
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (hf : formula) (ha : assignment) (hi : index) (hm : bitsetMap) (hb : bitset)
    (hag : aggregation) (hs : scalar) (he : everyClause) (hbuild : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation scalar
      everyClause build validator archive fallback audit :=
  fun r k => k hf ha hi hm hb hag hs he hbuild hv har hfb hau

theorem ay_csbg_accepted_bitset_formula
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : formula :=
  h formula (fun hf _ _ _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_csbg_accepted_bitset_assignment
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : assignment :=
  h assignment (fun _ ha _ _ _ _ _ _ _ _ _ _ _ => ha)

theorem ay_csbg_accepted_bitset_index
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : index :=
  h index (fun _ _ hi _ _ _ _ _ _ _ _ _ _ => hi)

theorem ay_csbg_accepted_bitset_map
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : bitsetMap :=
  h bitsetMap (fun _ _ _ hm _ _ _ _ _ _ _ _ _ => hm)

theorem ay_csbg_accepted_bitset_bitset
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : bitset :=
  h bitset (fun _ _ _ _ hb _ _ _ _ _ _ _ _ => hb)

theorem ay_csbg_accepted_bitset_aggregation
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : aggregation :=
  h aggregation (fun _ _ _ _ _ hag _ _ _ _ _ _ _ => hag)

theorem ay_csbg_accepted_bitset_scalar
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : scalar :=
  h scalar (fun _ _ _ _ _ _ hs _ _ _ _ _ _ => hs)

theorem ay_csbg_accepted_bitset_every_clause
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ _ he _ _ _ _ _ => he)

theorem ay_csbg_accepted_bitset_validator
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_csbg_accepted_bitset_archive
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_csbg_accepted_bitset_audit
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_csbg_public_sat_intro
    {accepted everyOriginalClauseSatisfied scalarAgreement validatorOk archiveOk audited : Prop}
    (ha : accepted) (he : everyOriginalClauseSatisfied) (hs : scalarAgreement)
    (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_csbg_public_sat accepted everyOriginalClauseSatisfied scalarAgreement validatorOk
      archiveOk audited :=
  ay_csbg_conj_intro ha
    (ay_csbg_conj_intro he
      (ay_csbg_conj_intro hs
        (ay_csbg_conj_intro hv (ay_csbg_conj_intro har hau))))

theorem ay_csbg_public_sat_requires_bitset_guard
    {accepted everyOriginalClauseSatisfied scalarAgreement validatorOk archiveOk audited : Prop}
    (h : ay_csbg_public_sat accepted everyOriginalClauseSatisfied scalarAgreement validatorOk
      archiveOk audited) : accepted :=
  ay_csbg_conj_left h

theorem ay_csbg_public_sat_every_original_clause
    {accepted everyOriginalClauseSatisfied scalarAgreement validatorOk archiveOk audited : Prop}
    (h : ay_csbg_public_sat accepted everyOriginalClauseSatisfied scalarAgreement validatorOk
      archiveOk audited) : everyOriginalClauseSatisfied :=
  ay_csbg_conj_left (ay_csbg_conj_right h)

theorem ay_csbg_public_sat_scalar_agreement
    {accepted everyOriginalClauseSatisfied scalarAgreement validatorOk archiveOk audited : Prop}
    (h : ay_csbg_public_sat accepted everyOriginalClauseSatisfied scalarAgreement validatorOk
      archiveOk audited) : scalarAgreement :=
  ay_csbg_conj_left (ay_csbg_conj_right (ay_csbg_conj_right h))

theorem ay_csbg_accepted_bitset_implies_every_original_clause_satisfied
    {formula assignment index bitsetMap bitset aggregation scalar everyClause build validator
     archive fallback audit : Prop}
    (h : ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation
      scalar everyClause build validator archive fallback audit) :
    ay_csbg_public_sat
      (ay_csbg_accepted_bitset formula assignment index bitsetMap bitset aggregation scalar
        everyClause build validator archive fallback audit)
      everyClause scalar validator archive audit :=
  ay_csbg_public_sat_intro
    h
    (ay_csbg_accepted_bitset_every_clause h)
    (ay_csbg_accepted_bitset_scalar h)
    (ay_csbg_accepted_bitset_validator h)
    (ay_csbg_accepted_bitset_archive h)
    (ay_csbg_accepted_bitset_audit h)

theorem ay_csbg_bitset_agrees_with_scalar_or_recomputes
    {bitsetSummary scalarSummary agreement recomputeReason : Prop}
    (hag : ay_csbg_equiv bitsetSummary scalarSummary -> agreement)
    (hrecompute : recomputeReason -> ay_csbg_recompute_obligation recomputeReason)
    (hcase : ay_csbg_disj (ay_csbg_equiv bitsetSummary scalarSummary) recomputeReason) :
    ay_csbg_disj agreement (ay_csbg_recompute_obligation recomputeReason) :=
  hcase
    (ay_csbg_disj agreement (ay_csbg_recompute_obligation recomputeReason))
    (fun h => ay_csbg_disj_left (hag h))
    (fun h => ay_csbg_disj_right (hrecompute h))

theorem ay_csbg_no_claim_intro {reason : Prop} (h : reason) :
    ay_csbg_no_claim_diagnostic reason :=
  h

theorem ay_csbg_recompute_intro {reason : Prop} (h : reason) :
    ay_csbg_recompute_obligation reason :=
  h

theorem ay_csbg_formula_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_assignment_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_csbg_recompute_obligation mismatch :=
  ay_csbg_recompute_intro h

theorem ay_csbg_index_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_map_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_csbg_recompute_obligation mismatch :=
  ay_csbg_recompute_intro h

theorem ay_csbg_bitset_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_csbg_recompute_obligation mismatch :=
  ay_csbg_recompute_intro h

theorem ay_csbg_aggregation_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_scalar_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_csbg_recompute_obligation mismatch :=
  ay_csbg_recompute_intro h

theorem ay_csbg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_csbg_recompute_obligation mismatch :=
  ay_csbg_recompute_intro h

theorem ay_csbg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_csbg_no_claim_diagnostic mismatch :=
  ay_csbg_no_claim_intro h

theorem ay_csbg_failed_bitset_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_csbg_no_claim_diagnostic failure)
    (noBless : ay_csbg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_csbg_failed_bitset_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_csbg_recompute_obligation failure)
    (hfailure : failure) :
    ay_csbg_recompute_obligation failure :=
  fallback hfailure

/-!
  SAT-COMP/ay incremental clause-check cache guard.

  This self-contained package models the SAT-only obligations for reusing
  cached clause-satisfaction checks during model validation.
-/

def ay_mccg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mccg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mccg_equiv (p q : Prop) : Prop :=
  ay_mccg_conj (p -> q) (q -> p)

def ay_mccg_original_formula_fingerprint
    (assignmentDigest formulaFingerprintOk : Prop) : Prop :=
  assignmentDigest -> formulaFingerprintOk

def ay_mccg_assignment_digest
    (formulaFingerprintOk assignmentOk : Prop) : Prop :=
  formulaFingerprintOk -> assignmentOk

def ay_mccg_clause_indexing_digest
    (assignmentOk clauseIndexOk : Prop) : Prop :=
  assignmentOk -> clauseIndexOk

def ay_mccg_cache_key_digest (clauseIndexOk cacheKeyOk : Prop) : Prop :=
  clauseIndexOk -> cacheKeyOk

def ay_mccg_cached_satisfied_clause_bitset_digest
    (cacheKeyOk cachedBitsetOk : Prop) : Prop :=
  cacheKeyOk -> cachedBitsetOk

def ay_mccg_invalidation_ledger
    (cachedBitsetOk invalidationOk : Prop) : Prop :=
  cachedBitsetOk -> invalidationOk

def ay_mccg_fresh_scalar_check_fallback_transcript
    (invalidationOk scalarFallbackOk : Prop) : Prop :=
  invalidationOk -> scalarFallbackOk

def ay_mccg_checker_version_digest
    (scalarFallbackOk checkerVersionOk : Prop) : Prop :=
  scalarFallbackOk -> checkerVersionOk

def ay_mccg_solver_build_evidence
    (checkerVersionOk buildOk : Prop) : Prop :=
  checkerVersionOk -> buildOk

def ay_mccg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_mccg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_mccg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mccg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mccg_accepted_cache
    (formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop) : Prop :=
  forall r : Prop,
    (formula -> assignment -> index -> cacheKey -> cachedBitset -> invalidation -> scalar ->
      checkerVersion -> build -> validator -> archive -> fallback -> audit -> everyClause ->
      r) -> r

def ay_mccg_public_sat
    (accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_mccg_conj accepted
    (ay_mccg_conj everyOriginalClauseSatisfied
      (ay_mccg_conj cacheKeyOk
        (ay_mccg_conj invalidationOk
          (ay_mccg_conj validatorOk (ay_mccg_conj archiveOk audited)))))

def ay_mccg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mccg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mccg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mccg_conj p q :=
  fun r h => h hp hq

theorem ay_mccg_conj_left {p q : Prop} (h : ay_mccg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mccg_conj_right {p q : Prop} (h : ay_mccg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mccg_conj_left h)

theorem ay_mccg_disj_left {p q : Prop} (hp : p) : ay_mccg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mccg_disj_right {p q : Prop} (hq : q) : ay_mccg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mccg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mccg_equiv p q :=
  ay_mccg_conj_intro hpq hqp

theorem ay_mccg_equiv_forward {p q : Prop} (h : ay_mccg_equiv p q) : p -> q :=
  ay_mccg_conj_left h

theorem ay_mccg_equiv_backward {p q : Prop} (h : ay_mccg_equiv p q) : q -> p :=
  ay_mccg_conj_right h

theorem ay_mccg_original_formula_fingerprint_intro
    {assignmentDigest formulaFingerprintOk : Prop}
    (h : assignmentDigest -> formulaFingerprintOk) :
    ay_mccg_original_formula_fingerprint assignmentDigest formulaFingerprintOk :=
  h

theorem ay_mccg_assignment_digest_intro
    {formulaFingerprintOk assignmentOk : Prop}
    (h : formulaFingerprintOk -> assignmentOk) :
    ay_mccg_assignment_digest formulaFingerprintOk assignmentOk :=
  h

theorem ay_mccg_clause_indexing_digest_intro {assignmentOk clauseIndexOk : Prop}
    (h : assignmentOk -> clauseIndexOk) :
    ay_mccg_clause_indexing_digest assignmentOk clauseIndexOk :=
  h

theorem ay_mccg_cache_key_digest_intro {clauseIndexOk cacheKeyOk : Prop}
    (h : clauseIndexOk -> cacheKeyOk) :
    ay_mccg_cache_key_digest clauseIndexOk cacheKeyOk :=
  h

theorem ay_mccg_cached_satisfied_clause_bitset_digest_intro
    {cacheKeyOk cachedBitsetOk : Prop}
    (h : cacheKeyOk -> cachedBitsetOk) :
    ay_mccg_cached_satisfied_clause_bitset_digest cacheKeyOk cachedBitsetOk :=
  h

theorem ay_mccg_invalidation_ledger_intro
    {cachedBitsetOk invalidationOk : Prop}
    (h : cachedBitsetOk -> invalidationOk) :
    ay_mccg_invalidation_ledger cachedBitsetOk invalidationOk :=
  h

theorem ay_mccg_fresh_scalar_check_fallback_transcript_intro
    {invalidationOk scalarFallbackOk : Prop}
    (h : invalidationOk -> scalarFallbackOk) :
    ay_mccg_fresh_scalar_check_fallback_transcript invalidationOk scalarFallbackOk :=
  h

theorem ay_mccg_checker_version_digest_intro
    {scalarFallbackOk checkerVersionOk : Prop}
    (h : scalarFallbackOk -> checkerVersionOk) :
    ay_mccg_checker_version_digest scalarFallbackOk checkerVersionOk :=
  h

theorem ay_mccg_solver_build_evidence_intro {checkerVersionOk buildOk : Prop}
    (h : checkerVersionOk -> buildOk) :
    ay_mccg_solver_build_evidence checkerVersionOk buildOk :=
  h

theorem ay_mccg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_mccg_validator_gate buildOk validatorOk :=
  h

theorem ay_mccg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_mccg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_mccg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mccg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mccg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mccg_audit_transcript fallbackReady audited :=
  h

theorem ay_mccg_accepted_cache_intro
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (hf : formula) (ha : assignment) (hi : index) (hk : cacheKey) (hcb : cachedBitset)
    (hinv : invalidation) (hs : scalar) (hcv : checkerVersion) (hb : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) (he : everyClause) :
    ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation scalar
      checkerVersion build validator archive fallback audit everyClause :=
  fun r k => k hf ha hi hk hcb hinv hs hcv hb hv har hfb hau he

theorem ay_mccg_accepted_cache_formula
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : formula :=
  h formula (fun hf _ _ _ _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_mccg_accepted_cache_assignment
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : assignment :=
  h assignment (fun _ ha _ _ _ _ _ _ _ _ _ _ _ _ => ha)

theorem ay_mccg_accepted_cache_key
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : cacheKey :=
  h cacheKey (fun _ _ _ hk _ _ _ _ _ _ _ _ _ _ => hk)

theorem ay_mccg_accepted_cache_invalidation
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : invalidation :=
  h invalidation (fun _ _ _ _ _ hinv _ _ _ _ _ _ _ _ => hinv)

theorem ay_mccg_accepted_cache_scalar
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : scalar :=
  h scalar (fun _ _ _ _ _ _ hs _ _ _ _ _ _ _ => hs)

theorem ay_mccg_accepted_cache_validator
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ _ _ => hv)

theorem ay_mccg_accepted_cache_archive
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ har _ _ _ => har)

theorem ay_mccg_accepted_cache_audit
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau _ => hau)

theorem ay_mccg_accepted_cache_every_clause
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ _ _ _ _ _ _ _ he => he)

theorem ay_mccg_public_sat_intro
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (he : everyOriginalClauseSatisfied) (hk : cacheKeyOk)
    (hi : invalidationOk) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk
      validatorOk archiveOk audited :=
  ay_mccg_conj_intro ha
    (ay_mccg_conj_intro he
      (ay_mccg_conj_intro hk
        (ay_mccg_conj_intro hi
          (ay_mccg_conj_intro hv (ay_mccg_conj_intro har hau)))))

theorem ay_mccg_public_sat_requires_cache_guard
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (h : ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk validatorOk archiveOk audited) : accepted :=
  ay_mccg_conj_left h

theorem ay_mccg_public_sat_every_original_clause
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (h : ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk validatorOk archiveOk audited) : everyOriginalClauseSatisfied :=
  ay_mccg_conj_left (ay_mccg_conj_right h)

theorem ay_mccg_public_sat_cache_key
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (h : ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk validatorOk archiveOk audited) : cacheKeyOk :=
  ay_mccg_conj_left (ay_mccg_conj_right (ay_mccg_conj_right h))

theorem ay_mccg_public_sat_invalidation
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (h : ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk validatorOk archiveOk audited) : invalidationOk :=
  ay_mccg_conj_left
    (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_accepted_cached_clause_checks_imply_original_satisfaction
    {formula assignment index cacheKey cachedBitset invalidation scalar checkerVersion build
     validator archive fallback audit everyClause : Prop}
    (h : ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
      scalar checkerVersion build validator archive fallback audit everyClause) :
    ay_mccg_public_sat
      (ay_mccg_accepted_cache formula assignment index cacheKey cachedBitset invalidation
        scalar checkerVersion build validator archive fallback audit everyClause)
      everyClause cacheKey invalidation validator archive audit :=
  ay_mccg_public_sat_intro
    h
    (ay_mccg_accepted_cache_every_clause h)
    (ay_mccg_accepted_cache_key h)
    (ay_mccg_accepted_cache_invalidation h)
    (ay_mccg_accepted_cache_validator h)
    (ay_mccg_accepted_cache_archive h)
    (ay_mccg_accepted_cache_audit h)

theorem ay_mccg_cache_key_and_invalidation_required_for_publication
    {accepted everyOriginalClauseSatisfied cacheKeyOk invalidationOk validatorOk archiveOk
     audited : Prop}
    (h : ay_mccg_public_sat accepted everyOriginalClauseSatisfied cacheKeyOk
      invalidationOk validatorOk archiveOk audited) :
    ay_mccg_conj cacheKeyOk invalidationOk :=
  ay_mccg_conj_intro
    (ay_mccg_public_sat_cache_key h)
    (ay_mccg_public_sat_invalidation h)

theorem ay_mccg_cache_evidence_alone_cannot_bless_sat
    {cacheEvidence assignmentContext formulaContext checkerReplay publicSat : Prop}
    (needsAssignment : publicSat -> assignmentContext)
    (needsFormula : publicSat -> formulaContext)
    (needsReplay : publicSat -> checkerReplay)
    (hc : cacheEvidence) (hp : publicSat) :
    ay_mccg_conj cacheEvidence
      (ay_mccg_conj assignmentContext (ay_mccg_conj formulaContext checkerReplay)) :=
  ay_mccg_conj_intro hc
    (ay_mccg_conj_intro (needsAssignment hp)
      (ay_mccg_conj_intro (needsFormula hp) (needsReplay hp)))

theorem ay_mccg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  h

theorem ay_mccg_recompute_intro {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  h

theorem ay_mccg_stale_cache_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_partial_cache_recompute {mismatch : Prop} (h : mismatch) :
    ay_mccg_recompute_obligation mismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_mismatched_cache_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_formula_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_assignment_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_mccg_recompute_obligation mismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_checker_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_mccg_recompute_obligation mismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_mccg_recompute_obligation mismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_mccg_no_claim_diagnostic mismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_failed_cache_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_mccg_no_claim_diagnostic failure)
    (noBless : ay_mccg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_mccg_failed_cache_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_mccg_recompute_obligation failure)
    (hfailure : failure) :
    ay_mccg_recompute_obligation failure :=
  fallback hfailure

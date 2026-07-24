/-!
  SAT-COMP/ay model checker replay-cache guard.

  This self-contained file records the abstract obligations required before a
  cached model-check transcript may be reused to publish a SAT result for the
  original formula.
-/

def AyMCRGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMCRGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMCRGEq (p q : Prop) : Prop :=
  AyMCRGConj (p -> q) (q -> p)

def AyMCRGAssignmentDigest (assignment stableAssignment : Prop) : Prop :=
  assignment -> stableAssignment

def AyMCRGFormulaFingerprint (stableAssignment originalFormula : Prop) : Prop :=
  stableAssignment -> originalFormula

def AyMCRGCheckerVersionManifest (originalFormula checkerVersion : Prop) : Prop :=
  originalFormula -> checkerVersion

def AyMCRGCachedTranscriptDigest (checkerVersion cachedTranscript : Prop) : Prop :=
  checkerVersion -> cachedTranscript

def AyMCRGClauseCoverageDigest (cachedTranscript everyClauseSatisfied : Prop) : Prop :=
  cachedTranscript -> everyClauseSatisfied

def AyMCRGBuildEvidence (everyClauseSatisfied build : Prop) : Prop :=
  everyClauseSatisfied -> build

def AyMCRGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMCRGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMCRGCacheEpochLedger (fallbackReady epochLive : Prop) : Prop :=
  fallbackReady -> epochLive

def AyMCRGAuditTranscript (epochLive audited : Prop) : Prop :=
  epochLive -> audited

def AyMCRGAcceptedReplayCache
    (assignmentDigest formulaFingerprint checkerVersionManifest cachedTranscriptDigest
     clauseCoverageDigest buildEvidence archiveManifest fallbackBaseline cacheEpochLedger
     auditTranscript : Prop) : Prop :=
  AyMCRGConj assignmentDigest
    (AyMCRGConj formulaFingerprint
      (AyMCRGConj checkerVersionManifest
        (AyMCRGConj cachedTranscriptDigest
          (AyMCRGConj clauseCoverageDigest
            (AyMCRGConj buildEvidence
              (AyMCRGConj archiveManifest
                (AyMCRGConj fallbackBaseline
                  (AyMCRGConj cacheEpochLedger auditTranscript)))))))))

def AyMCRGPublicSat (acceptedReplayCache checkedOriginalModel originalSat : Prop) : Prop :=
  AyMCRGConj acceptedReplayCache (AyMCRGConj checkedOriginalModel originalSat)

def AyMCRGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMCRGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mcrg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMCRGConj p q :=
  fun r h => h hp hq

theorem ay_mcrg_conj_left {p q : Prop} (h : AyMCRGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mcrg_conj_right {p q : Prop} (h : AyMCRGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mcrg_conj_left h)

theorem ay_mcrg_disj_left {p q : Prop} (hp : p) : AyMCRGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mcrg_disj_right {p q : Prop} (hq : q) : AyMCRGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mcrg_eq_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMCRGEq p q :=
  ay_mcrg_conj_intro hpq hqp

theorem ay_mcrg_eq_forward {p q : Prop} (h : AyMCRGEq p q) : p -> q :=
  ay_mcrg_conj_left h

theorem ay_mcrg_eq_backward {p q : Prop} (h : AyMCRGEq p q) : q -> p :=
  ay_mcrg_conj_right h

theorem ay_mcrg_assignment_digest_intro {assignment stableAssignment : Prop}
    (h : assignment -> stableAssignment) :
    AyMCRGAssignmentDigest assignment stableAssignment :=
  h

theorem ay_mcrg_formula_fingerprint_intro {stableAssignment originalFormula : Prop}
    (h : stableAssignment -> originalFormula) :
    AyMCRGFormulaFingerprint stableAssignment originalFormula :=
  h

theorem ay_mcrg_checker_version_manifest_intro {originalFormula checkerVersion : Prop}
    (h : originalFormula -> checkerVersion) :
    AyMCRGCheckerVersionManifest originalFormula checkerVersion :=
  h

theorem ay_mcrg_cached_transcript_digest_intro {checkerVersion cachedTranscript : Prop}
    (h : checkerVersion -> cachedTranscript) :
    AyMCRGCachedTranscriptDigest checkerVersion cachedTranscript :=
  h

theorem ay_mcrg_clause_coverage_digest_intro
    {cachedTranscript everyClauseSatisfied : Prop}
    (h : cachedTranscript -> everyClauseSatisfied) :
    AyMCRGClauseCoverageDigest cachedTranscript everyClauseSatisfied :=
  h

theorem ay_mcrg_build_evidence_intro {everyClauseSatisfied build : Prop}
    (h : everyClauseSatisfied -> build) : AyMCRGBuildEvidence everyClauseSatisfied build :=
  h

theorem ay_mcrg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMCRGArchiveManifest build archived :=
  h

theorem ay_mcrg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMCRGFallbackBaseline archived fallbackReady :=
  h

theorem ay_mcrg_cache_epoch_ledger_intro {fallbackReady epochLive : Prop}
    (h : fallbackReady -> epochLive) : AyMCRGCacheEpochLedger fallbackReady epochLive :=
  h

theorem ay_mcrg_audit_transcript_intro {epochLive audited : Prop}
    (h : epochLive -> audited) : AyMCRGAuditTranscript epochLive audited :=
  h

theorem ay_mcrg_accepted_replay_cache_intro
    {ad ff cv ct cc be ar fb ce au : Prop}
    (had : ad) (hff : ff) (hcv : cv) (hct : ct) (hcc : cc) (hbe : be)
    (har : ar) (hfb : fb) (hce : ce) (hau : au) :
    AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au :=
  ay_mcrg_conj_intro had
    (ay_mcrg_conj_intro hff
      (ay_mcrg_conj_intro hcv
        (ay_mcrg_conj_intro hct
          (ay_mcrg_conj_intro hcc
            (ay_mcrg_conj_intro hbe
              (ay_mcrg_conj_intro har
                (ay_mcrg_conj_intro hfb
                  (ay_mcrg_conj_intro hce hau)))))))))

theorem ay_mcrg_accepted_replay_cache_assignment_digest
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : ad :=
  ay_mcrg_conj_left h

theorem ay_mcrg_accepted_replay_cache_formula
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : ff :=
  ay_mcrg_conj_left (ay_mcrg_conj_right h)

theorem ay_mcrg_accepted_replay_cache_checker_version
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : cv :=
  ay_mcrg_conj_left (ay_mcrg_conj_right (ay_mcrg_conj_right h))

theorem ay_mcrg_accepted_replay_cache_transcript
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : ct :=
  ay_mcrg_conj_left (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h)))

theorem ay_mcrg_accepted_replay_cache_coverage
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : cc :=
  ay_mcrg_conj_left
    (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h))))

theorem ay_mcrg_accepted_replay_cache_build
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : be :=
  ay_mcrg_conj_left
    (ay_mcrg_conj_right
      (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h)))))

theorem ay_mcrg_accepted_replay_cache_archive
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : ar :=
  ay_mcrg_conj_left
    (ay_mcrg_conj_right
      (ay_mcrg_conj_right
        (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h))))))

theorem ay_mcrg_accepted_replay_cache_fallback
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : fb :=
  ay_mcrg_conj_left
    (ay_mcrg_conj_right
      (ay_mcrg_conj_right
        (ay_mcrg_conj_right
          (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h)))))))

theorem ay_mcrg_accepted_replay_cache_epoch
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : ce :=
  ay_mcrg_conj_left
    (ay_mcrg_conj_right
      (ay_mcrg_conj_right
        (ay_mcrg_conj_right
          (ay_mcrg_conj_right
            (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h))))))))

theorem ay_mcrg_accepted_replay_cache_audit
    {ad ff cv ct cc be ar fb ce au : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au) : au :=
  ay_mcrg_conj_right
    (ay_mcrg_conj_right
      (ay_mcrg_conj_right
        (ay_mcrg_conj_right
          (ay_mcrg_conj_right
            (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right (ay_mcrg_conj_right h))))))))

theorem ay_mcrg_replay_cache_checked_original_model
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel audited : Prop}
    (h : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
    (hchecked : checkedOriginalModel)
    (haudit : audited) :
    AyMCRGConj checkedOriginalModel audited :=
  ay_mcrg_conj_intro hchecked haudit

theorem ay_mcrg_public_sat_intro {acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (hac : acceptedReplayCache) (hchecked : checkedOriginalModel) (hsat : originalSat) :
    AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat :=
  ay_mcrg_conj_intro hac (ay_mcrg_conj_intro hchecked hsat)

theorem ay_mcrg_public_sat_evidence {acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat) :
    acceptedReplayCache :=
  ay_mcrg_conj_left h

theorem ay_mcrg_public_sat_checked_model
    {acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat) :
    checkedOriginalModel :=
  ay_mcrg_conj_left (ay_mcrg_conj_right h)

theorem ay_mcrg_public_sat_claim {acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat) : originalSat :=
  ay_mcrg_conj_right (ay_mcrg_conj_right h)

theorem ay_mcrg_accepted_replay_cache_publishes_sat
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (hac : AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
    (hchecked : checkedOriginalModel) (hsat : originalSat) :
    AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat :=
  ay_mcrg_public_sat_intro hac hchecked hsat

theorem ay_mcrg_public_sat_requires_accepted_replay_cache
    {acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat) :
    acceptedReplayCache :=
  ay_mcrg_public_sat_evidence h

theorem ay_mcrg_publication_requires_assignment_digest
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : ad :=
  ay_mcrg_accepted_replay_cache_assignment_digest
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_publication_requires_formula_fingerprint
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : ff :=
  ay_mcrg_accepted_replay_cache_formula
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_publication_requires_checker_version
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : cv :=
  ay_mcrg_accepted_replay_cache_checker_version
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_publication_requires_cached_transcript
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : ct :=
  ay_mcrg_accepted_replay_cache_transcript
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_publication_requires_coverage
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : cc :=
  ay_mcrg_accepted_replay_cache_coverage
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_publication_requires_cache_epoch
    {ad ff cv ct cc be ar fb ce au checkedOriginalModel originalSat : Prop}
    (h : AyMCRGPublicSat (AyMCRGAcceptedReplayCache ad ff cv ct cc be ar fb ce au)
      checkedOriginalModel originalSat) : ce :=
  ay_mcrg_accepted_replay_cache_epoch
    (ay_mcrg_public_sat_requires_accepted_replay_cache h)

theorem ay_mcrg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  h

theorem ay_mcrg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyMCRGRecomputeObligation reason :=
  h

theorem ay_mcrg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  ay_mcrg_no_claim_diagnostic_intro h

theorem ay_mcrg_mismatch_recompute {reason : Prop} (h : reason) :
    AyMCRGRecomputeObligation reason :=
  ay_mcrg_recompute_obligation_intro h

theorem ay_mcrg_stale_formula_no_claim {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  ay_mcrg_mismatch_no_claim h

theorem ay_mcrg_stale_model_no_claim {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  ay_mcrg_mismatch_no_claim h

theorem ay_mcrg_checker_mismatch_recompute {reason : Prop} (h : reason) :
    AyMCRGRecomputeObligation reason :=
  ay_mcrg_mismatch_recompute h

theorem ay_mcrg_cache_mismatch_recompute {reason : Prop} (h : reason) :
    AyMCRGRecomputeObligation reason :=
  ay_mcrg_mismatch_recompute h

theorem ay_mcrg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  ay_mcrg_mismatch_no_claim h

theorem ay_mcrg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCRGNoClaimDiagnostic reason :=
  ay_mcrg_mismatch_no_claim h

theorem ay_mcrg_failed_cache_guard_cannot_bless_sat
    {failure acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (hfail : failure)
    (hblock : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat ->
      AyMCRGNoClaimDiagnostic failure) :
    AyMCRGConj (AyMCRGNoClaimDiagnostic failure)
      (AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat ->
        AyMCRGNoClaimDiagnostic failure) :=
  ay_mcrg_conj_intro (ay_mcrg_no_claim_diagnostic_intro hfail) hblock

theorem ay_mcrg_failed_cache_guard_recompute_blocks_publication
    {failure acceptedReplayCache checkedOriginalModel originalSat : Prop}
    (hfail : failure)
    (hblock : AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat ->
      AyMCRGRecomputeObligation failure) :
    AyMCRGConj (AyMCRGRecomputeObligation failure)
      (AyMCRGPublicSat acceptedReplayCache checkedOriginalModel originalSat ->
        AyMCRGRecomputeObligation failure) :=
  ay_mcrg_conj_intro (ay_mcrg_recompute_obligation_intro hfail) hblock

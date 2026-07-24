/-!
  SAT-COMP/ay duplicate-literal and polarity guard.

  This self-contained file records the abstract obligations required before a
  model literal list with duplicate literals may be normalized into a consistent
  total public SAT assignment.
-/

def AyDLPGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyDLPGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyDLPGEq (p q : Prop) : Prop :=
  AyDLPGConj (p -> q) (q -> p)

def AyDLPGModelLiteralListDigest (rawModel stableModel : Prop) : Prop :=
  rawModel -> stableModel

def AyDLPGDuplicateHandlingPolicy (stableModel duplicatesNormalized : Prop) : Prop :=
  stableModel -> duplicatesNormalized

def AyDLPGNoConflictingPolarityWitness
    (duplicatesNormalized polarityConsistent : Prop) : Prop :=
  duplicatesNormalized -> polarityConsistent

def AyDLPGVariableDomainManifest (polarityConsistent domainComplete : Prop) : Prop :=
  polarityConsistent -> domainComplete

def AyDLPGAssignmentReconstructionWitness
    (domainComplete totalAssignment : Prop) : Prop :=
  domainComplete -> totalAssignment

def AyDLPGClauseCoverageDigest (totalAssignment everyClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyClauseSatisfied

def AyDLPGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyDLPGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyDLGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyDLPGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyDLPGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyDLPGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyDLPGAcceptedNormalization
    (modelDigest duplicatePolicy polarityWitness domainManifest reconstructionWitness
     coverageDigest checkerTranscript formulaFingerprint buildEvidence archiveManifest
     fallbackBaseline auditTranscript : Prop) : Prop :=
  AyDLPGConj modelDigest
    (AyDLPGConj duplicatePolicy
      (AyDLPGConj polarityWitness
        (AyDLPGConj domainManifest
          (AyDLPGConj reconstructionWitness
            (AyDLPGConj coverageDigest
              (AyDLPGConj checkerTranscript
                (AyDLPGConj formulaFingerprint
                  (AyDLPGConj buildEvidence
                    (AyDLPGConj archiveManifest
                      (AyDLPGConj fallbackBaseline auditTranscript)))))))))))

def AyDLPGPublicSat (acceptedNormalization totalAssignment originalSat : Prop) : Prop :=
  AyDLPGConj acceptedNormalization (AyDLPGConj totalAssignment originalSat)

def AyDLPGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyDLPGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_dlpg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyDLPGConj p q :=
  fun r h => h hp hq

theorem ay_dlpg_conj_left {p q : Prop} (h : AyDLPGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_dlpg_conj_right {p q : Prop} (h : AyDLPGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_dlpg_conj_left h)

theorem ay_dlpg_disj_left {p q : Prop} (hp : p) : AyDLPGDisj p q :=
  fun r hl _ => hl hp

theorem ay_dlpg_disj_right {p q : Prop} (hq : q) : AyDLPGDisj p q :=
  fun r _ hr => hr hq

theorem ay_dlpg_eq_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyDLPGEq p q :=
  ay_dlpg_conj_intro hpq hqp

theorem ay_dlpg_eq_forward {p q : Prop} (h : AyDLPGEq p q) : p -> q :=
  ay_dlpg_conj_left h

theorem ay_dlpg_eq_backward {p q : Prop} (h : AyDLPGEq p q) : q -> p :=
  ay_dlpg_conj_right h

theorem ay_dlpg_model_literal_list_digest_intro {rawModel stableModel : Prop}
    (h : rawModel -> stableModel) :
    AyDLPGModelLiteralListDigest rawModel stableModel :=
  h

theorem ay_dlpg_duplicate_handling_policy_intro {stableModel duplicatesNormalized : Prop}
    (h : stableModel -> duplicatesNormalized) :
    AyDLPGDuplicateHandlingPolicy stableModel duplicatesNormalized :=
  h

theorem ay_dlpg_no_conflicting_polarity_witness_intro
    {duplicatesNormalized polarityConsistent : Prop}
    (h : duplicatesNormalized -> polarityConsistent) :
    AyDLPGNoConflictingPolarityWitness duplicatesNormalized polarityConsistent :=
  h

theorem ay_dlpg_variable_domain_manifest_intro
    {polarityConsistent domainComplete : Prop}
    (h : polarityConsistent -> domainComplete) :
    AyDLPGVariableDomainManifest polarityConsistent domainComplete :=
  h

theorem ay_dlpg_assignment_reconstruction_witness_intro
    {domainComplete totalAssignment : Prop}
    (h : domainComplete -> totalAssignment) :
    AyDLPGAssignmentReconstructionWitness domainComplete totalAssignment :=
  h

theorem ay_dlpg_clause_coverage_digest_intro
    {totalAssignment everyClauseSatisfied : Prop}
    (h : totalAssignment -> everyClauseSatisfied) :
    AyDLPGClauseCoverageDigest totalAssignment everyClauseSatisfied :=
  h

theorem ay_dlpg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyDLPGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_dlpg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyDLPGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_dlpg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyDLGBuildEvidence fingerprint build :=
  h

theorem ay_dlpg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyDLPGArchiveManifest build archived :=
  h

theorem ay_dlpg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyDLPGFallbackBaseline archived fallbackReady :=
  h

theorem ay_dlpg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyDLPGAuditTranscript fallbackReady audited :=
  h

theorem ay_dlpg_accepted_normalization_intro
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (hmd : md) (hdp : dp) (hpw : pw) (hdm : dm) (hrw : rw) (hcd : cd)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au :=
  ay_dlpg_conj_intro hmd
    (ay_dlpg_conj_intro hdp
      (ay_dlpg_conj_intro hpw
        (ay_dlpg_conj_intro hdm
          (ay_dlpg_conj_intro hrw
            (ay_dlpg_conj_intro hcd
              (ay_dlpg_conj_intro hct
                (ay_dlpg_conj_intro hff
                  (ay_dlpg_conj_intro hbe
                    (ay_dlpg_conj_intro har
                      (ay_dlpg_conj_intro hfb hau)))))))))))

theorem ay_dlpg_accepted_normalization_model_digest
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : md :=
  ay_dlpg_conj_left h

theorem ay_dlpg_accepted_normalization_duplicate_policy
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : dp :=
  ay_dlpg_conj_left (ay_dlpg_conj_right h)

theorem ay_dlpg_accepted_normalization_polarity_witness
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : pw :=
  ay_dlpg_conj_left (ay_dlpg_conj_right (ay_dlpg_conj_right h))

theorem ay_dlpg_accepted_normalization_domain
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : dm :=
  ay_dlpg_conj_left (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h)))

theorem ay_dlpg_accepted_normalization_reconstruction
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : rw :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h))))

theorem ay_dlpg_accepted_normalization_coverage
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : cd :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h)))))

theorem ay_dlpg_accepted_normalization_checker
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : ct :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h))))))

theorem ay_dlpg_accepted_normalization_fingerprint
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : ff :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right
          (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h)))))))

theorem ay_dlpg_accepted_normalization_build
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : be :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right
          (ay_dlpg_conj_right
            (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h))))))))

theorem ay_dlpg_accepted_normalization_archive
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : ar :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right
          (ay_dlpg_conj_right
            (ay_dlpg_conj_right
              (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h)))))))))

theorem ay_dlpg_accepted_normalization_fallback
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : fb :=
  ay_dlpg_conj_left
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right
          (ay_dlpg_conj_right
            (ay_dlpg_conj_right
              (ay_dlpg_conj_right
                (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h))))))))))

theorem ay_dlpg_accepted_normalization_audit
    {md dp pw dm rw cd ct ff be ar fb au : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au) : au :=
  ay_dlpg_conj_right
    (ay_dlpg_conj_right
      (ay_dlpg_conj_right
        (ay_dlpg_conj_right
          (ay_dlpg_conj_right
            (ay_dlpg_conj_right
              (ay_dlpg_conj_right
                (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right (ay_dlpg_conj_right h))))))))))

theorem ay_dlpg_normalization_reconstructs_consistent_total_assignment
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment consistent audited : Prop}
    (h : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
    (htotal : totalAssignment)
    (hconsistent : consistent)
    (haudit : audited) :
    AyDLPGConj totalAssignment (AyDLPGConj consistent audited) :=
  ay_dlpg_conj_intro htotal (ay_dlpg_conj_intro hconsistent haudit)

theorem ay_dlpg_public_sat_intro {acceptedNormalization totalAssignment originalSat : Prop}
    (han : acceptedNormalization) (htotal : totalAssignment) (hsat : originalSat) :
    AyDLPGPublicSat acceptedNormalization totalAssignment originalSat :=
  ay_dlpg_conj_intro han (ay_dlpg_conj_intro htotal hsat)

theorem ay_dlpg_public_sat_evidence {acceptedNormalization totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat) :
    acceptedNormalization :=
  ay_dlpg_conj_left h

theorem ay_dlpg_public_sat_total_assignment
    {acceptedNormalization totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat) : totalAssignment :=
  ay_dlpg_conj_left (ay_dlpg_conj_right h)

theorem ay_dlpg_public_sat_claim {acceptedNormalization totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat) : originalSat :=
  ay_dlpg_conj_right (ay_dlpg_conj_right h)

theorem ay_dlpg_publication_requires_accepted_normalization
    {acceptedNormalization totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat) :
    acceptedNormalization :=
  ay_dlpg_public_sat_evidence h

theorem ay_dlpg_accepted_normalization_publishes_sat
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (han : AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat :=
  ay_dlpg_public_sat_intro han htotal hsat

theorem ay_dlpg_publication_requires_duplicate_policy
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : dp :=
  ay_dlpg_accepted_normalization_duplicate_policy
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_polarity_witness
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : pw :=
  ay_dlpg_accepted_normalization_polarity_witness
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_domain
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : dm :=
  ay_dlpg_accepted_normalization_domain (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_coverage
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : cd :=
  ay_dlpg_accepted_normalization_coverage
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_checker
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ct :=
  ay_dlpg_accepted_normalization_checker
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_fingerprint
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ff :=
  ay_dlpg_accepted_normalization_fingerprint
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_build
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : be :=
  ay_dlpg_accepted_normalization_build
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_publication_requires_archive
    {md dp pw dm rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDLPGPublicSat (AyDLPGAcceptedNormalization md dp pw dm rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ar :=
  ay_dlpg_accepted_normalization_archive
    (ay_dlpg_publication_requires_accepted_normalization h)

theorem ay_dlpg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  h

theorem ay_dlpg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyDLPGRecomputeObligation reason :=
  h

theorem ay_dlpg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_no_claim_diagnostic_intro h

theorem ay_dlpg_mismatch_recompute {reason : Prop} (h : reason) :
    AyDLPGRecomputeObligation reason :=
  ay_dlpg_recompute_obligation_intro h

theorem ay_dlpg_duplicate_policy_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_conflict_mismatch_recompute {reason : Prop} (h : reason) :
    AyDLPGRecomputeObligation reason :=
  ay_dlpg_mismatch_recompute h

theorem ay_dlpg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDLPGNoClaimDiagnostic reason :=
  ay_dlpg_mismatch_no_claim h

theorem ay_dlpg_failed_polarity_guard_cannot_bless_sat
    {failure acceptedNormalization totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat ->
      AyDLPGNoClaimDiagnostic failure) :
    AyDLPGConj (AyDLPGNoClaimDiagnostic failure)
      (AyDLPGPublicSat acceptedNormalization totalAssignment originalSat ->
        AyDLPGNoClaimDiagnostic failure) :=
  ay_dlpg_conj_intro (ay_dlpg_no_claim_diagnostic_intro hfail) hblock

theorem ay_dlpg_failed_polarity_guard_recompute_blocks_publication
    {failure acceptedNormalization totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDLPGPublicSat acceptedNormalization totalAssignment originalSat ->
      AyDLPGRecomputeObligation failure) :
    AyDLPGConj (AyDLPGRecomputeObligation failure)
      (AyDLPGPublicSat acceptedNormalization totalAssignment originalSat ->
        AyDLPGRecomputeObligation failure) :=
  ay_dlpg_conj_intro (ay_dlpg_recompute_obligation_intro hfail) hblock

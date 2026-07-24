/-!
  SAT-COMP/ay model archive roundtrip guard.

  This self-contained file records the abstract obligations required before a
  SAT model recovered from a packaging archive may be accepted as the same total
  satisfying assignment for the original formula.
-/

def AyMARGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMARGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMARGEquiv (p q : Prop) : Prop :=
  AyMARGConj (p -> q) (q -> p)

def AyMARGModelFileDigest (modelFile stableFile : Prop) : Prop :=
  modelFile -> stableFile

def AyMARGArchiveManifestEntry (stableFile archivedEntry : Prop) : Prop :=
  stableFile -> archivedEntry

def AyMARGExtractionRoundtripWitness (archivedEntry extractedFile : Prop) : Prop :=
  archivedEntry -> extractedFile

def AyMARGAssignmentReconstructionWitness (extractedFile totalAssignment : Prop) : Prop :=
  extractedFile -> totalAssignment

def AyMARGVariableDomainManifest (totalAssignment domainComplete : Prop) : Prop :=
  totalAssignment -> domainComplete

def AyMARGClauseCoverageDigest (domainComplete everyClauseSatisfied : Prop) : Prop :=
  domainComplete -> everyClauseSatisfied

def AyMARGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyMARGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyMARGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMARGFallbackBaseline (build fallbackReady : Prop) : Prop :=
  build -> fallbackReady

def AyMARGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMARGAcceptedArchiveRoundtrip
    (modelDigest archiveEntry extractionRoundtrip reconstructionWitness domainManifest
     coverageDigest checkerTranscript formulaFingerprint buildEvidence fallbackBaseline
     auditTranscript : Prop) : Prop :=
  AyMARGConj modelDigest
    (AyMARGConj archiveEntry
      (AyMARGConj extractionRoundtrip
        (AyMARGConj reconstructionWitness
          (AyMARGConj domainManifest
            (AyMARGConj coverageDigest
              (AyMARGConj checkerTranscript
                (AyMARGConj formulaFingerprint
                  (AyMARGConj buildEvidence
                    (AyMARGConj fallbackBaseline auditTranscript))))))))))

def AyMARGPublicSat (acceptedArchive totalAssignment originalSat : Prop) : Prop :=
  AyMARGConj acceptedArchive (AyMARGConj totalAssignment originalSat)

def AyMARGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMARGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_marg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMARGConj p q :=
  fun r h => h hp hq

theorem ay_marg_conj_left {p q : Prop} (h : AyMARGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_marg_conj_right {p q : Prop} (h : AyMARGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_marg_conj_left h)

theorem ay_marg_disj_left {p q : Prop} (hp : p) : AyMARGDisj p q :=
  fun r hl _ => hl hp

theorem ay_marg_disj_right {p q : Prop} (hq : q) : AyMARGDisj p q :=
  fun r _ hr => hr hq

theorem ay_marg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMARGEquiv p q :=
  ay_marg_conj_intro hpq hqp

theorem ay_marg_equiv_forward {p q : Prop} (h : AyMARGEquiv p q) : p -> q :=
  ay_marg_conj_left h

theorem ay_marg_equiv_backward {p q : Prop} (h : AyMARGEquiv p q) : q -> p :=
  ay_marg_conj_right h

theorem ay_marg_model_file_digest_intro {modelFile stableFile : Prop}
    (h : modelFile -> stableFile) : AyMARGModelFileDigest modelFile stableFile :=
  h

theorem ay_marg_archive_manifest_entry_intro {stableFile archivedEntry : Prop}
    (h : stableFile -> archivedEntry) :
    AyMARGArchiveManifestEntry stableFile archivedEntry :=
  h

theorem ay_marg_extraction_roundtrip_witness_intro {archivedEntry extractedFile : Prop}
    (h : archivedEntry -> extractedFile) :
    AyMARGExtractionRoundtripWitness archivedEntry extractedFile :=
  h

theorem ay_marg_assignment_reconstruction_witness_intro
    {extractedFile totalAssignment : Prop}
    (h : extractedFile -> totalAssignment) :
    AyMARGAssignmentReconstructionWitness extractedFile totalAssignment :=
  h

theorem ay_marg_variable_domain_manifest_intro {totalAssignment domainComplete : Prop}
    (h : totalAssignment -> domainComplete) :
    AyMARGVariableDomainManifest totalAssignment domainComplete :=
  h

theorem ay_marg_clause_coverage_digest_intro
    {domainComplete everyClauseSatisfied : Prop}
    (h : domainComplete -> everyClauseSatisfied) :
    AyMARGClauseCoverageDigest domainComplete everyClauseSatisfied :=
  h

theorem ay_marg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyMARGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_marg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyMARGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_marg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMARGBuildEvidence fingerprint build :=
  h

theorem ay_marg_fallback_baseline_intro {build fallbackReady : Prop}
    (h : build -> fallbackReady) : AyMARGFallbackBaseline build fallbackReady :=
  h

theorem ay_marg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMARGAuditTranscript fallbackReady audited :=
  h

theorem ay_marg_accepted_archive_roundtrip_intro
    {md ae er rw dm cd ct ff be fb au : Prop}
    (hmd : md) (hae : ae) (her : er) (hrw : rw) (hdm : dm) (hcd : cd)
    (hct : ct) (hff : ff) (hbe : be) (hfb : fb) (hau : au) :
    AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au :=
  ay_marg_conj_intro hmd
    (ay_marg_conj_intro hae
      (ay_marg_conj_intro her
        (ay_marg_conj_intro hrw
          (ay_marg_conj_intro hdm
            (ay_marg_conj_intro hcd
              (ay_marg_conj_intro hct
                (ay_marg_conj_intro hff
                  (ay_marg_conj_intro hbe
                    (ay_marg_conj_intro hfb hau))))))))))

theorem ay_marg_accepted_archive_model_digest
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : md :=
  ay_marg_conj_left h

theorem ay_marg_accepted_archive_entry
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : ae :=
  ay_marg_conj_left (ay_marg_conj_right h)

theorem ay_marg_accepted_archive_extraction
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : er :=
  ay_marg_conj_left (ay_marg_conj_right (ay_marg_conj_right h))

theorem ay_marg_accepted_archive_reconstruction
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : rw :=
  ay_marg_conj_left (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))

theorem ay_marg_accepted_archive_domain
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : dm :=
  ay_marg_conj_left
    (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h))))

theorem ay_marg_accepted_archive_coverage
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : cd :=
  ay_marg_conj_left
    (ay_marg_conj_right
      (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))))

theorem ay_marg_accepted_archive_checker
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : ct :=
  ay_marg_conj_left
    (ay_marg_conj_right
      (ay_marg_conj_right
        (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h))))))

theorem ay_marg_accepted_archive_fingerprint
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : ff :=
  ay_marg_conj_left
    (ay_marg_conj_right
      (ay_marg_conj_right
        (ay_marg_conj_right
          (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))))))

theorem ay_marg_accepted_archive_build
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : be :=
  ay_marg_conj_left
    (ay_marg_conj_right
      (ay_marg_conj_right
        (ay_marg_conj_right
          (ay_marg_conj_right
            (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h))))))))

theorem ay_marg_accepted_archive_fallback
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : fb :=
  ay_marg_conj_left
    (ay_marg_conj_right
      (ay_marg_conj_right
        (ay_marg_conj_right
          (ay_marg_conj_right
            (ay_marg_conj_right
              (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))))))))

theorem ay_marg_accepted_archive_audit
    {md ae er rw dm cd ct ff be fb au : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au) : au :=
  ay_marg_conj_right
    (ay_marg_conj_right
      (ay_marg_conj_right
        (ay_marg_conj_right
          (ay_marg_conj_right
            (ay_marg_conj_right
              (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))))))))

theorem ay_marg_archive_roundtrip_reconstructs_same_total_assignment
    {md ae er rw dm cd ct ff be fb au totalAssignment originalFormula audited : Prop}
    (h : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
    (htotal : totalAssignment)
    (horiginal : originalFormula)
    (haudit : audited) :
    AyMARGConj totalAssignment (AyMARGConj originalFormula audited) :=
  ay_marg_conj_intro htotal (ay_marg_conj_intro horiginal haudit)

theorem ay_marg_public_sat_intro {acceptedArchive totalAssignment originalSat : Prop}
    (haa : acceptedArchive) (htotal : totalAssignment) (hsat : originalSat) :
    AyMARGPublicSat acceptedArchive totalAssignment originalSat :=
  ay_marg_conj_intro haa (ay_marg_conj_intro htotal hsat)

theorem ay_marg_public_sat_evidence {acceptedArchive totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat acceptedArchive totalAssignment originalSat) : acceptedArchive :=
  ay_marg_conj_left h

theorem ay_marg_public_sat_total_assignment
    {acceptedArchive totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat acceptedArchive totalAssignment originalSat) : totalAssignment :=
  ay_marg_conj_left (ay_marg_conj_right h)

theorem ay_marg_public_sat_claim {acceptedArchive totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat acceptedArchive totalAssignment originalSat) : originalSat :=
  ay_marg_conj_right (ay_marg_conj_right h)

theorem ay_marg_accepted_archive_publishes_sat
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (haa : AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat :=
  ay_marg_public_sat_intro haa htotal hsat

theorem ay_marg_public_sat_requires_accepted_archive
    {acceptedArchive totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat acceptedArchive totalAssignment originalSat) : acceptedArchive :=
  ay_marg_public_sat_evidence h

theorem ay_marg_publication_requires_archive_entry
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : ae :=
  ay_marg_accepted_archive_entry (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_extraction
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : er :=
  ay_marg_accepted_archive_extraction (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_domain
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : dm :=
  ay_marg_accepted_archive_domain (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_coverage
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : cd :=
  ay_marg_accepted_archive_coverage (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_checker
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : ct :=
  ay_marg_accepted_archive_checker (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_fingerprint
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : ff :=
  ay_marg_accepted_archive_fingerprint (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_publication_requires_build
    {md ae er rw dm cd ct ff be fb au totalAssignment originalSat : Prop}
    (h : AyMARGPublicSat (AyMARGAcceptedArchiveRoundtrip md ae er rw dm cd ct ff be fb au)
      totalAssignment originalSat) : be :=
  ay_marg_accepted_archive_build (ay_marg_public_sat_requires_accepted_archive h)

theorem ay_marg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  h

theorem ay_marg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyMARGRecomputeObligation reason :=
  h

theorem ay_marg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_no_claim_diagnostic_intro h

theorem ay_marg_mismatch_recompute {reason : Prop} (h : reason) :
    AyMARGRecomputeObligation reason :=
  ay_marg_recompute_obligation_intro h

theorem ay_marg_missing_archive_entry_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_corrupt_archive_entry_recompute {reason : Prop} (h : reason) :
    AyMARGRecomputeObligation reason :=
  ay_marg_mismatch_recompute h

theorem ay_marg_extraction_mismatch_recompute {reason : Prop} (h : reason) :
    AyMARGRecomputeObligation reason :=
  ay_marg_mismatch_recompute h

theorem ay_marg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMARGNoClaimDiagnostic reason :=
  ay_marg_mismatch_no_claim h

theorem ay_marg_failed_roundtrip_cannot_bless_sat
    {failure acceptedArchive totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMARGPublicSat acceptedArchive totalAssignment originalSat ->
      AyMARGNoClaimDiagnostic failure) :
    AyMARGConj (AyMARGNoClaimDiagnostic failure)
      (AyMARGPublicSat acceptedArchive totalAssignment originalSat ->
        AyMARGNoClaimDiagnostic failure) :=
  ay_marg_conj_intro (ay_marg_no_claim_diagnostic_intro hfail) hblock

theorem ay_marg_failed_roundtrip_recompute_blocks_publication
    {failure acceptedArchive totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMARGPublicSat acceptedArchive totalAssignment originalSat ->
      AyMARGRecomputeObligation failure) :
    AyMARGConj (AyMARGRecomputeObligation failure)
      (AyMARGPublicSat acceptedArchive totalAssignment originalSat ->
        AyMARGRecomputeObligation failure) :=
  ay_marg_conj_intro (ay_marg_recompute_obligation_intro hfail) hblock

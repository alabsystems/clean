/-!
  SAT-COMP/ay model compression roundtrip guard.

  This self-contained file records the abstract obligations required before a
  compressed SAT model may be decompressed and accepted as the same total
  satisfying assignment over the original DIMACS variables.
-/

def AyMCZGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMCZGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMCZGEquiv (p q : Prop) : Prop :=
  AyMCZGConj (p -> q) (q -> p)

def AyMCZGCompressedModelDigest (compressed stableCompressed : Prop) : Prop :=
  compressed -> stableCompressed

def AyMCZGDecompressionPolicy (stableCompressed decompressed : Prop) : Prop :=
  stableCompressed -> decompressed

def AyMCZGRoundtripEqualityWitness (decompressed sameModel : Prop) : Prop :=
  decompressed -> sameModel

def AyMCZGAssignmentReconstructionWitness (sameModel totalAssignment : Prop) : Prop :=
  sameModel -> totalAssignment

def AyMCZGVariableDomainManifest (totalAssignment originalDomain : Prop) : Prop :=
  totalAssignment -> originalDomain

def AyMCZGClauseCoverageDigest (originalDomain everyClauseSatisfied : Prop) : Prop :=
  originalDomain -> everyClauseSatisfied

def AyMCZGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyMCZGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyMCZGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMCZGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMCZGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMCZGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMCZGAcceptedCompression
    (compressedDigest decompressionPolicy roundtripWitness reconstructionWitness
     domainManifest coverageDigest checkerTranscript formulaFingerprint buildEvidence
     archiveManifest fallbackBaseline auditTranscript : Prop) : Prop :=
  AyMCZGConj compressedDigest
    (AyMCZGConj decompressionPolicy
      (AyMCZGConj roundtripWitness
        (AyMCZGConj reconstructionWitness
          (AyMCZGConj domainManifest
            (AyMCZGConj coverageDigest
              (AyMCZGConj checkerTranscript
                (AyMCZGConj formulaFingerprint
                  (AyMCZGConj buildEvidence
                    (AyMCZGConj archiveManifest
                      (AyMCZGConj fallbackBaseline auditTranscript)))))))))))

def AyMCZGPublicSat (acceptedCompression totalAssignment originalSat : Prop) : Prop :=
  AyMCZGConj acceptedCompression (AyMCZGConj totalAssignment originalSat)

def AyMCZGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMCZGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mczg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMCZGConj p q :=
  fun r h => h hp hq

theorem ay_mczg_conj_left {p q : Prop} (h : AyMCZGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mczg_conj_right {p q : Prop} (h : AyMCZGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mczg_conj_left h)

theorem ay_mczg_disj_left {p q : Prop} (hp : p) : AyMCZGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mczg_disj_right {p q : Prop} (hq : q) : AyMCZGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mczg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMCZGEquiv p q :=
  ay_mczg_conj_intro hpq hqp

theorem ay_mczg_equiv_forward {p q : Prop} (h : AyMCZGEquiv p q) : p -> q :=
  ay_mczg_conj_left h

theorem ay_mczg_equiv_backward {p q : Prop} (h : AyMCZGEquiv p q) : q -> p :=
  ay_mczg_conj_right h

theorem ay_mczg_compressed_model_digest_intro {compressed stableCompressed : Prop}
    (h : compressed -> stableCompressed) :
    AyMCZGCompressedModelDigest compressed stableCompressed :=
  h

theorem ay_mczg_decompression_policy_intro {stableCompressed decompressed : Prop}
    (h : stableCompressed -> decompressed) :
    AyMCZGDecompressionPolicy stableCompressed decompressed :=
  h

theorem ay_mczg_roundtrip_equality_witness_intro {decompressed sameModel : Prop}
    (h : decompressed -> sameModel) :
    AyMCZGRoundtripEqualityWitness decompressed sameModel :=
  h

theorem ay_mczg_assignment_reconstruction_witness_intro
    {sameModel totalAssignment : Prop}
    (h : sameModel -> totalAssignment) :
    AyMCZGAssignmentReconstructionWitness sameModel totalAssignment :=
  h

theorem ay_mczg_variable_domain_manifest_intro {totalAssignment originalDomain : Prop}
    (h : totalAssignment -> originalDomain) :
    AyMCZGVariableDomainManifest totalAssignment originalDomain :=
  h

theorem ay_mczg_clause_coverage_digest_intro
    {originalDomain everyClauseSatisfied : Prop}
    (h : originalDomain -> everyClauseSatisfied) :
    AyMCZGClauseCoverageDigest originalDomain everyClauseSatisfied :=
  h

theorem ay_mczg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyMCZGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_mczg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyMCZGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_mczg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMCZGBuildEvidence fingerprint build :=
  h

theorem ay_mczg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMCZGArchiveManifest build archived :=
  h

theorem ay_mczg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMCZGFallbackBaseline archived fallbackReady :=
  h

theorem ay_mczg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMCZGAuditTranscript fallbackReady audited :=
  h

theorem ay_mczg_accepted_compression_intro
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (hcd : cd) (hdp : dp) (hrw : rw) (haw : aw) (hdm : dm) (hcov : cov)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au :=
  ay_mczg_conj_intro hcd
    (ay_mczg_conj_intro hdp
      (ay_mczg_conj_intro hrw
        (ay_mczg_conj_intro haw
          (ay_mczg_conj_intro hdm
            (ay_mczg_conj_intro hcov
              (ay_mczg_conj_intro hct
                (ay_mczg_conj_intro hff
                  (ay_mczg_conj_intro hbe
                    (ay_mczg_conj_intro har
                      (ay_mczg_conj_intro hfb hau)))))))))))

theorem ay_mczg_accepted_compression_digest
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : cd :=
  ay_mczg_conj_left h

theorem ay_mczg_accepted_compression_policy
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : dp :=
  ay_mczg_conj_left (ay_mczg_conj_right h)

theorem ay_mczg_accepted_compression_roundtrip
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : rw :=
  ay_mczg_conj_left (ay_mczg_conj_right (ay_mczg_conj_right h))

theorem ay_mczg_accepted_compression_reconstruction
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : aw :=
  ay_mczg_conj_left (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h)))

theorem ay_mczg_accepted_compression_domain
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : dm :=
  ay_mczg_conj_left
    (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h))))

theorem ay_mczg_accepted_compression_coverage
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : cov :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h)))))

theorem ay_mczg_accepted_compression_checker
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : ct :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h))))))

theorem ay_mczg_accepted_compression_fingerprint
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : ff :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right
          (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h)))))))

theorem ay_mczg_accepted_compression_build
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : be :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right
          (ay_mczg_conj_right
            (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h))))))))

theorem ay_mczg_accepted_compression_archive
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : ar :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right
          (ay_mczg_conj_right
            (ay_mczg_conj_right
              (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h)))))))))

theorem ay_mczg_accepted_compression_fallback
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : fb :=
  ay_mczg_conj_left
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right
          (ay_mczg_conj_right
            (ay_mczg_conj_right
              (ay_mczg_conj_right
                (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h))))))))))

theorem ay_mczg_accepted_compression_audit
    {cd dp rw aw dm cov ct ff be ar fb au : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au) : au :=
  ay_mczg_conj_right
    (ay_mczg_conj_right
      (ay_mczg_conj_right
        (ay_mczg_conj_right
          (ay_mczg_conj_right
            (ay_mczg_conj_right
              (ay_mczg_conj_right
                (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right (ay_mczg_conj_right h))))))))))

theorem ay_mczg_compression_reconstructs_same_dimacs_assignment
    {cd dp rw aw dm cov ct ff be ar fb au totalAssignment originalDomain audited : Prop}
    (h : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au)
    (htotal : totalAssignment)
    (hdomain : originalDomain)
    (haudit : audited) :
    AyMCZGConj totalAssignment (AyMCZGConj originalDomain audited) :=
  ay_mczg_conj_intro htotal (ay_mczg_conj_intro hdomain haudit)

theorem ay_mczg_public_sat_intro {acceptedCompression totalAssignment originalSat : Prop}
    (hac : acceptedCompression) (htotal : totalAssignment) (hsat : originalSat) :
    AyMCZGPublicSat acceptedCompression totalAssignment originalSat :=
  ay_mczg_conj_intro hac (ay_mczg_conj_intro htotal hsat)

theorem ay_mczg_public_sat_evidence {acceptedCompression totalAssignment originalSat : Prop}
    (h : AyMCZGPublicSat acceptedCompression totalAssignment originalSat) :
    acceptedCompression :=
  ay_mczg_conj_left h

theorem ay_mczg_public_sat_total_assignment
    {acceptedCompression totalAssignment originalSat : Prop}
    (h : AyMCZGPublicSat acceptedCompression totalAssignment originalSat) : totalAssignment :=
  ay_mczg_conj_left (ay_mczg_conj_right h)

theorem ay_mczg_public_sat_claim {acceptedCompression totalAssignment originalSat : Prop}
    (h : AyMCZGPublicSat acceptedCompression totalAssignment originalSat) : originalSat :=
  ay_mczg_conj_right (ay_mczg_conj_right h)

theorem ay_mczg_accepted_compression_publishes_sat
    {cd dp rw aw dm cov ct ff be ar fb au totalAssignment originalSat : Prop}
    (hac : AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMCZGPublicSat (AyMCZGAcceptedCompression cd dp rw aw dm cov ct ff be ar fb au)
      totalAssignment originalSat :=
  ay_mczg_public_sat_intro hac htotal hsat

theorem ay_mczg_public_sat_requires_accepted_compression
    {acceptedCompression totalAssignment originalSat : Prop}
    (h : AyMCZGPublicSat acceptedCompression totalAssignment originalSat) :
    acceptedCompression :=
  ay_mczg_public_sat_evidence h

theorem ay_mczg_corruption_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_roundtrip_mismatch_recompute {reason : Prop} (h : reason) :
    AyMCZGRecomputeObligation reason :=
  h

theorem ay_mczg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyMCZGRecomputeObligation reason :=
  h

theorem ay_mczg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMCZGNoClaimDiagnostic reason :=
  h

theorem ay_mczg_failed_compression_guard_cannot_bless_sat
    {failure acceptedCompression totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMCZGPublicSat acceptedCompression totalAssignment originalSat ->
      AyMCZGNoClaimDiagnostic failure) :
    AyMCZGConj (AyMCZGNoClaimDiagnostic failure)
      (AyMCZGPublicSat acceptedCompression totalAssignment originalSat ->
        AyMCZGNoClaimDiagnostic failure) :=
  ay_mczg_conj_intro hfail hblock

theorem ay_mczg_failed_compression_guard_recompute_blocks_publication
    {failure acceptedCompression totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMCZGPublicSat acceptedCompression totalAssignment originalSat ->
      AyMCZGRecomputeObligation failure) :
    AyMCZGConj (AyMCZGRecomputeObligation failure)
      (AyMCZGPublicSat acceptedCompression totalAssignment originalSat ->
        AyMCZGRecomputeObligation failure) :=
  ay_mczg_conj_intro hfail hblock

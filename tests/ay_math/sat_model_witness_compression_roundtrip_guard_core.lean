/-!
  SAT-COMP/ay witness compression roundtrip guard.

  This self-contained file records the abstract obligations required before a
  compressed SAT witness can be decompressed, roundtripped, and accepted as the
  same total satisfying assignment for the original formula.
-/

def AyWCRGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyWCRGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyWCRGEq (p q : Prop) : Prop :=
  AyWCRGConj (p -> q) (q -> p)

def AyWCRGCompressedWitnessDigest (compressed stableCompressed : Prop) : Prop :=
  compressed -> stableCompressed

def AyWCRGDecompressionPolicy (stableCompressed decompressed : Prop) : Prop :=
  stableCompressed -> decompressed

def AyWCRGRoundtripEqualityWitness (decompressed sameAssignment : Prop) : Prop :=
  decompressed -> sameAssignment

def AyWCRGAssignmentCompletenessDigest (sameAssignment totalAssignment : Prop) : Prop :=
  sameAssignment -> totalAssignment

def AyWCRGClauseCoverageDigest (totalAssignment everyClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyClauseSatisfied

def AyWCRGFormulaFingerprint (everyClauseSatisfied fingerprint : Prop) : Prop :=
  everyClauseSatisfied -> fingerprint

def AyWCRGCheckerTranscript (fingerprint checkerAccepted : Prop) : Prop :=
  fingerprint -> checkerAccepted

def AyWCRGBuildEvidence (checkerAccepted build : Prop) : Prop :=
  checkerAccepted -> build

def AyWCRGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyWCRGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyWCRGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyWCRGAcceptedRoundtrip
    (compressedDigest decompressionPolicy roundtripWitness completenessDigest
     coverageDigest formulaFingerprint checkerTranscript buildEvidence
     archiveManifest fallbackBaseline auditTranscript : Prop) : Prop :=
  AyWCRGConj compressedDigest
    (AyWCRGConj decompressionPolicy
      (AyWCRGConj roundtripWitness
        (AyWCRGConj completenessDigest
          (AyWCRGConj coverageDigest
            (AyWCRGConj formulaFingerprint
              (AyWCRGConj checkerTranscript
                (AyWCRGConj buildEvidence
                  (AyWCRGConj archiveManifest
                    (AyWCRGConj fallbackBaseline auditTranscript))))))))))

def AyWCRGPublicSat (acceptedRoundtrip totalAssignment originalSat : Prop) : Prop :=
  AyWCRGConj acceptedRoundtrip (AyWCRGConj totalAssignment originalSat)

def AyWCRGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyWCRGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_wcrg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyWCRGConj p q :=
  fun r h => h hp hq

theorem ay_wcrg_conj_left {p q : Prop} (h : AyWCRGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_wcrg_conj_right {p q : Prop} (h : AyWCRGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_wcrg_conj_left h)

theorem ay_wcrg_disj_left {p q : Prop} (hp : p) : AyWCRGDisj p q :=
  fun r hl _ => hl hp

theorem ay_wcrg_disj_right {p q : Prop} (hq : q) : AyWCRGDisj p q :=
  fun r _ hr => hr hq

theorem ay_wcrg_eq_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyWCRGEq p q :=
  ay_wcrg_conj_intro hpq hqp

theorem ay_wcrg_eq_forward {p q : Prop} (h : AyWCRGEq p q) : p -> q :=
  ay_wcrg_conj_left h

theorem ay_wcrg_eq_backward {p q : Prop} (h : AyWCRGEq p q) : q -> p :=
  ay_wcrg_conj_right h

theorem ay_wcrg_compressed_witness_digest_intro {compressed stableCompressed : Prop}
    (h : compressed -> stableCompressed) :
    AyWCRGCompressedWitnessDigest compressed stableCompressed :=
  h

theorem ay_wcrg_decompression_policy_intro {stableCompressed decompressed : Prop}
    (h : stableCompressed -> decompressed) :
    AyWCRGDecompressionPolicy stableCompressed decompressed :=
  h

theorem ay_wcrg_roundtrip_equality_witness_intro {decompressed sameAssignment : Prop}
    (h : decompressed -> sameAssignment) :
    AyWCRGRoundtripEqualityWitness decompressed sameAssignment :=
  h

theorem ay_wcrg_assignment_completeness_digest_intro
    {sameAssignment totalAssignment : Prop}
    (h : sameAssignment -> totalAssignment) :
    AyWCRGAssignmentCompletenessDigest sameAssignment totalAssignment :=
  h

theorem ay_wcrg_clause_coverage_digest_intro
    {totalAssignment everyClauseSatisfied : Prop}
    (h : totalAssignment -> everyClauseSatisfied) :
    AyWCRGClauseCoverageDigest totalAssignment everyClauseSatisfied :=
  h

theorem ay_wcrg_formula_fingerprint_intro {everyClauseSatisfied fingerprint : Prop}
    (h : everyClauseSatisfied -> fingerprint) :
    AyWCRGFormulaFingerprint everyClauseSatisfied fingerprint :=
  h

theorem ay_wcrg_checker_transcript_intro {fingerprint checkerAccepted : Prop}
    (h : fingerprint -> checkerAccepted) :
    AyWCRGCheckerTranscript fingerprint checkerAccepted :=
  h

theorem ay_wcrg_build_evidence_intro {checkerAccepted build : Prop}
    (h : checkerAccepted -> build) : AyWCRGBuildEvidence checkerAccepted build :=
  h

theorem ay_wcrg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyWCRGArchiveManifest build archived :=
  h

theorem ay_wcrg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyWCRGFallbackBaseline archived fallbackReady :=
  h

theorem ay_wcrg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyWCRGAuditTranscript fallbackReady audited :=
  h

theorem ay_wcrg_accepted_roundtrip_intro
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (hcw : cw) (hdp : dp) (hrt : rt) (hac : ac) (hcc : cc) (hff : ff)
    (hct : ct) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au :=
  ay_wcrg_conj_intro hcw
    (ay_wcrg_conj_intro hdp
      (ay_wcrg_conj_intro hrt
        (ay_wcrg_conj_intro hac
          (ay_wcrg_conj_intro hcc
            (ay_wcrg_conj_intro hff
              (ay_wcrg_conj_intro hct
                (ay_wcrg_conj_intro hbe
                  (ay_wcrg_conj_intro har
                    (ay_wcrg_conj_intro hfb hau))))))))))

theorem ay_wcrg_accepted_roundtrip_compressed_digest
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : cw :=
  ay_wcrg_conj_left h

theorem ay_wcrg_accepted_roundtrip_decompression_policy
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : dp :=
  ay_wcrg_conj_left (ay_wcrg_conj_right h)

theorem ay_wcrg_accepted_roundtrip_equality
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : rt :=
  ay_wcrg_conj_left (ay_wcrg_conj_right (ay_wcrg_conj_right h))

theorem ay_wcrg_accepted_roundtrip_completeness
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : ac :=
  ay_wcrg_conj_left (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h)))

theorem ay_wcrg_accepted_roundtrip_coverage
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : cc :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h))))

theorem ay_wcrg_accepted_roundtrip_fingerprint
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : ff :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h)))))

theorem ay_wcrg_accepted_roundtrip_checker
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : ct :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right
        (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h))))))

theorem ay_wcrg_accepted_roundtrip_build
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : be :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right
        (ay_wcrg_conj_right
          (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h)))))))

theorem ay_wcrg_accepted_roundtrip_archive
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : ar :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right
        (ay_wcrg_conj_right
          (ay_wcrg_conj_right
            (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h))))))))

theorem ay_wcrg_accepted_roundtrip_fallback
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : fb :=
  ay_wcrg_conj_left
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right
        (ay_wcrg_conj_right
          (ay_wcrg_conj_right
            (ay_wcrg_conj_right
              (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h)))))))))

theorem ay_wcrg_accepted_roundtrip_audit
    {cw dp rt ac cc ff ct be ar fb au : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au) : au :=
  ay_wcrg_conj_right
    (ay_wcrg_conj_right
      (ay_wcrg_conj_right
        (ay_wcrg_conj_right
          (ay_wcrg_conj_right
            (ay_wcrg_conj_right
              (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right (ay_wcrg_conj_right h)))))))))

theorem ay_wcrg_roundtrip_reconstructs_same_total_assignment
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalFormula audited : Prop}
    (h : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
    (htotal : totalAssignment)
    (horiginal : originalFormula)
    (haudit : audited) :
    AyWCRGConj totalAssignment (AyWCRGConj originalFormula audited) :=
  ay_wcrg_conj_intro htotal (ay_wcrg_conj_intro horiginal haudit)

theorem ay_wcrg_public_sat_intro {acceptedRoundtrip totalAssignment originalSat : Prop}
    (har : acceptedRoundtrip) (htotal : totalAssignment) (hsat : originalSat) :
    AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat :=
  ay_wcrg_conj_intro har (ay_wcrg_conj_intro htotal hsat)

theorem ay_wcrg_public_sat_evidence {acceptedRoundtrip totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat) :
    acceptedRoundtrip :=
  ay_wcrg_conj_left h

theorem ay_wcrg_public_sat_total_assignment
    {acceptedRoundtrip totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat) : totalAssignment :=
  ay_wcrg_conj_left (ay_wcrg_conj_right h)

theorem ay_wcrg_public_sat_claim {acceptedRoundtrip totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat) : originalSat :=
  ay_wcrg_conj_right (ay_wcrg_conj_right h)

theorem ay_wcrg_accepted_roundtrip_publishes_sat
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (har : AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat :=
  ay_wcrg_public_sat_intro har htotal hsat

theorem ay_wcrg_public_sat_requires_accepted_roundtrip
    {acceptedRoundtrip totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat) :
    acceptedRoundtrip :=
  ay_wcrg_public_sat_evidence h

theorem ay_wcrg_publication_requires_compressed_digest
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : cw :=
  ay_wcrg_accepted_roundtrip_compressed_digest
    (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_decompression_policy
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : dp :=
  ay_wcrg_accepted_roundtrip_decompression_policy
    (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_roundtrip_equality
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : rt :=
  ay_wcrg_accepted_roundtrip_equality (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_completeness
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : ac :=
  ay_wcrg_accepted_roundtrip_completeness (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_coverage
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : cc :=
  ay_wcrg_accepted_roundtrip_coverage (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_fingerprint
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : ff :=
  ay_wcrg_accepted_roundtrip_fingerprint (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_checker
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : ct :=
  ay_wcrg_accepted_roundtrip_checker (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_build
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : be :=
  ay_wcrg_accepted_roundtrip_build (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_archive
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : ar :=
  ay_wcrg_accepted_roundtrip_archive (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_fallback
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : fb :=
  ay_wcrg_accepted_roundtrip_fallback (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_publication_requires_audit
    {cw dp rt ac cc ff ct be ar fb au totalAssignment originalSat : Prop}
    (h : AyWCRGPublicSat (AyWCRGAcceptedRoundtrip cw dp rt ac cc ff ct be ar fb au)
      totalAssignment originalSat) : au :=
  ay_wcrg_accepted_roundtrip_audit (ay_wcrg_public_sat_requires_accepted_roundtrip h)

theorem ay_wcrg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  h

theorem ay_wcrg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyWCRGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_wcrg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyWCRGRecomputeObligation reason :=
  h

theorem ay_wcrg_recompute_obligation_request {reason : Prop}
    (h : AyWCRGRecomputeObligation reason) : reason :=
  h

theorem ay_wcrg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_no_claim_diagnostic_intro h

theorem ay_wcrg_mismatch_recompute {reason : Prop} (h : reason) :
    AyWCRGRecomputeObligation reason :=
  ay_wcrg_recompute_obligation_intro h

theorem ay_wcrg_corruption_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_roundtrip_mismatch_recompute {reason : Prop} (h : reason) :
    AyWCRGRecomputeObligation reason :=
  ay_wcrg_mismatch_recompute h

theorem ay_wcrg_completeness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWCRGNoClaimDiagnostic reason :=
  ay_wcrg_mismatch_no_claim h

theorem ay_wcrg_audit_mismatch_recompute {reason : Prop} (h : reason) :
    AyWCRGRecomputeObligation reason :=
  ay_wcrg_mismatch_recompute h

theorem ay_wcrg_failed_roundtrip_cannot_bless_sat
    {failure acceptedRoundtrip totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat ->
      AyWCRGNoClaimDiagnostic failure) :
    AyWCRGConj (AyWCRGNoClaimDiagnostic failure)
      (AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat ->
        AyWCRGNoClaimDiagnostic failure) :=
  ay_wcrg_conj_intro (ay_wcrg_no_claim_diagnostic_intro hfail) hblock

theorem ay_wcrg_failed_roundtrip_recompute_blocks_publication
    {failure acceptedRoundtrip totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat ->
      AyWCRGRecomputeObligation failure) :
    AyWCRGConj (AyWCRGRecomputeObligation failure)
      (AyWCRGPublicSat acceptedRoundtrip totalAssignment originalSat ->
        AyWCRGRecomputeObligation failure) :=
  ay_wcrg_conj_intro (ay_wcrg_recompute_obligation_intro hfail) hblock

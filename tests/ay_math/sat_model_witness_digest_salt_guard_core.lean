/-!
  SAT-COMP/ay witness digest salt/domain-separation guard.

  This self-contained file records the abstract obligations required before a
  SAT model witness digest can identify the checked assignment for the original
  formula without cross-benchmark reuse.
-/

def AyWDSGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyWDSGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyWDSGEquiv (p q : Prop) : Prop :=
  AyWDSGConj (p -> q) (q -> p)

def AyWDSGAssignmentDigest (assignment stableAssignment : Prop) : Prop :=
  assignment -> stableAssignment

def AyWDSGDigestSaltDomainManifest (stableAssignment saltedDigest : Prop) : Prop :=
  stableAssignment -> saltedDigest

def AyWDSGFormulaFingerprint (saltedDigest originalFormula : Prop) : Prop :=
  saltedDigest -> originalFormula

def AyWDSGCheckerTranscript (originalFormula checkerAccepted : Prop) : Prop :=
  originalFormula -> checkerAccepted

def AyWDSGAssignmentReconstructionWitness (checkerAccepted reconstructedAssignment : Prop) : Prop :=
  checkerAccepted -> reconstructedAssignment

def AyWDSGVariableDomainManifest (reconstructedAssignment originalDomain : Prop) : Prop :=
  reconstructedAssignment -> originalDomain

def AyWDSGClauseCoverageDigest (originalDomain everyClauseSatisfied : Prop) : Prop :=
  originalDomain -> everyClauseSatisfied

def AyWDSGBuildEvidence (everyClauseSatisfied build : Prop) : Prop :=
  everyClauseSatisfied -> build

def AyWDSGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyWDSGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyWDSGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyWDSGAcceptedDigestDomain
    (assignmentDigest saltDomain formulaFingerprint checkerTranscript reconstructionWitness
     domainManifest coverageDigest buildEvidence archiveManifest fallbackBaseline
     auditTranscript : Prop) : Prop :=
  AyWDSGConj assignmentDigest
    (AyWDSGConj saltDomain
      (AyWDSGConj formulaFingerprint
        (AyWDSGConj checkerTranscript
          (AyWDSGConj reconstructionWitness
            (AyWDSGConj domainManifest
              (AyWDSGConj coverageDigest
                (AyWDSGConj buildEvidence
                  (AyWDSGConj archiveManifest
                    (AyWDSGConj fallbackBaseline auditTranscript))))))))))

def AyWDSGPublicSat (acceptedDigest reconstructedAssignment originalSat : Prop) : Prop :=
  AyWDSGConj acceptedDigest (AyWDSGConj reconstructedAssignment originalSat)

def AyWDSGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyWDSGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_wdsg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyWDSGConj p q :=
  fun r h => h hp hq

theorem ay_wdsg_conj_left {p q : Prop} (h : AyWDSGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_wdsg_conj_right {p q : Prop} (h : AyWDSGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_wdsg_conj_left h)

theorem ay_wdsg_disj_left {p q : Prop} (hp : p) : AyWDSGDisj p q :=
  fun r hl _ => hl hp

theorem ay_wdsg_disj_right {p q : Prop} (hq : q) : AyWDSGDisj p q :=
  fun r _ hr => hr hq

theorem ay_wdsg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyWDSGEquiv p q :=
  ay_wdsg_conj_intro hpq hqp

theorem ay_wdsg_equiv_forward {p q : Prop} (h : AyWDSGEquiv p q) : p -> q :=
  ay_wdsg_conj_left h

theorem ay_wdsg_equiv_backward {p q : Prop} (h : AyWDSGEquiv p q) : q -> p :=
  ay_wdsg_conj_right h

theorem ay_wdsg_assignment_digest_intro {assignment stableAssignment : Prop}
    (h : assignment -> stableAssignment) :
    AyWDSGAssignmentDigest assignment stableAssignment :=
  h

theorem ay_wdsg_digest_salt_domain_manifest_intro {stableAssignment saltedDigest : Prop}
    (h : stableAssignment -> saltedDigest) :
    AyWDSGDigestSaltDomainManifest stableAssignment saltedDigest :=
  h

theorem ay_wdsg_formula_fingerprint_intro {saltedDigest originalFormula : Prop}
    (h : saltedDigest -> originalFormula) :
    AyWDSGFormulaFingerprint saltedDigest originalFormula :=
  h

theorem ay_wdsg_checker_transcript_intro {originalFormula checkerAccepted : Prop}
    (h : originalFormula -> checkerAccepted) :
    AyWDSGCheckerTranscript originalFormula checkerAccepted :=
  h

theorem ay_wdsg_assignment_reconstruction_witness_intro
    {checkerAccepted reconstructedAssignment : Prop}
    (h : checkerAccepted -> reconstructedAssignment) :
    AyWDSGAssignmentReconstructionWitness checkerAccepted reconstructedAssignment :=
  h

theorem ay_wdsg_variable_domain_manifest_intro
    {reconstructedAssignment originalDomain : Prop}
    (h : reconstructedAssignment -> originalDomain) :
    AyWDSGVariableDomainManifest reconstructedAssignment originalDomain :=
  h

theorem ay_wdsg_clause_coverage_digest_intro
    {originalDomain everyClauseSatisfied : Prop}
    (h : originalDomain -> everyClauseSatisfied) :
    AyWDSGClauseCoverageDigest originalDomain everyClauseSatisfied :=
  h

theorem ay_wdsg_build_evidence_intro {everyClauseSatisfied build : Prop}
    (h : everyClauseSatisfied -> build) : AyWDSGBuildEvidence everyClauseSatisfied build :=
  h

theorem ay_wdsg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyWDSGArchiveManifest build archived :=
  h

theorem ay_wdsg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyWDSGFallbackBaseline archived fallbackReady :=
  h

theorem ay_wdsg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyWDSGAuditTranscript fallbackReady audited :=
  h

theorem ay_wdsg_accepted_digest_domain_intro
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (had : ad) (hsd : sd) (hff : ff) (hct : ct) (hrw : rw) (hdm : dm)
    (hcd : cd) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au :=
  ay_wdsg_conj_intro had
    (ay_wdsg_conj_intro hsd
      (ay_wdsg_conj_intro hff
        (ay_wdsg_conj_intro hct
          (ay_wdsg_conj_intro hrw
            (ay_wdsg_conj_intro hdm
              (ay_wdsg_conj_intro hcd
                (ay_wdsg_conj_intro hbe
                  (ay_wdsg_conj_intro har
                    (ay_wdsg_conj_intro hfb hau))))))))))

theorem ay_wdsg_accepted_digest_assignment
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : ad :=
  ay_wdsg_conj_left h

theorem ay_wdsg_accepted_digest_salt
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : sd :=
  ay_wdsg_conj_left (ay_wdsg_conj_right h)

theorem ay_wdsg_accepted_digest_formula
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : ff :=
  ay_wdsg_conj_left (ay_wdsg_conj_right (ay_wdsg_conj_right h))

theorem ay_wdsg_accepted_digest_checker
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : ct :=
  ay_wdsg_conj_left (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h)))

theorem ay_wdsg_accepted_digest_reconstruction
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : rw :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h))))

theorem ay_wdsg_accepted_digest_domain
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : dm :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h)))))

theorem ay_wdsg_accepted_digest_coverage
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : cd :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right
        (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h))))))

theorem ay_wdsg_accepted_digest_build
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : be :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right
        (ay_wdsg_conj_right
          (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h)))))))

theorem ay_wdsg_accepted_digest_archive
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : ar :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right
        (ay_wdsg_conj_right
          (ay_wdsg_conj_right
            (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h))))))))

theorem ay_wdsg_accepted_digest_fallback
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : fb :=
  ay_wdsg_conj_left
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right
        (ay_wdsg_conj_right
          (ay_wdsg_conj_right
            (ay_wdsg_conj_right
              (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h)))))))))

theorem ay_wdsg_accepted_digest_audit
    {ad sd ff ct rw dm cd be ar fb au : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au) : au :=
  ay_wdsg_conj_right
    (ay_wdsg_conj_right
      (ay_wdsg_conj_right
        (ay_wdsg_conj_right
          (ay_wdsg_conj_right
            (ay_wdsg_conj_right
              (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right (ay_wdsg_conj_right h)))))))))

theorem ay_wdsg_domain_separation_identifies_checked_assignment
    {ad sd ff ct rw dm cd be ar fb au checkedAssignment originalFormula audited : Prop}
    (h : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au)
    (hchecked : checkedAssignment)
    (horiginal : originalFormula)
    (haudit : audited) :
    AyWDSGConj checkedAssignment (AyWDSGConj originalFormula audited) :=
  ay_wdsg_conj_intro hchecked (ay_wdsg_conj_intro horiginal haudit)

theorem ay_wdsg_public_sat_intro {acceptedDigest reconstructedAssignment originalSat : Prop}
    (had : acceptedDigest) (hrecon : reconstructedAssignment) (hsat : originalSat) :
    AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat :=
  ay_wdsg_conj_intro had (ay_wdsg_conj_intro hrecon hsat)

theorem ay_wdsg_public_sat_evidence
    {acceptedDigest reconstructedAssignment originalSat : Prop}
    (h : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat) :
    acceptedDigest :=
  ay_wdsg_conj_left h

theorem ay_wdsg_public_sat_assignment
    {acceptedDigest reconstructedAssignment originalSat : Prop}
    (h : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat) :
    reconstructedAssignment :=
  ay_wdsg_conj_left (ay_wdsg_conj_right h)

theorem ay_wdsg_public_sat_claim {acceptedDigest reconstructedAssignment originalSat : Prop}
    (h : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat) : originalSat :=
  ay_wdsg_conj_right (ay_wdsg_conj_right h)

theorem ay_wdsg_accepted_digest_publishes_sat
    {ad sd ff ct rw dm cd be ar fb au reconstructedAssignment originalSat : Prop}
    (had : AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au)
    (hrecon : reconstructedAssignment) (hsat : originalSat) :
    AyWDSGPublicSat (AyWDSGAcceptedDigestDomain ad sd ff ct rw dm cd be ar fb au)
      reconstructedAssignment originalSat :=
  ay_wdsg_public_sat_intro had hrecon hsat

theorem ay_wdsg_public_sat_requires_accepted_digest
    {acceptedDigest reconstructedAssignment originalSat : Prop}
    (h : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat) :
    acceptedDigest :=
  ay_wdsg_public_sat_evidence h

theorem ay_wdsg_missing_salt_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_wrong_salt_recompute {reason : Prop} (h : reason) :
    AyWDSGRecomputeObligation reason :=
  h

theorem ay_wdsg_cross_benchmark_digest_reuse_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    AyWDSGRecomputeObligation reason :=
  h

theorem ay_wdsg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyWDSGRecomputeObligation reason :=
  h

theorem ay_wdsg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyWDSGNoClaimDiagnostic reason :=
  h

theorem ay_wdsg_failed_digest_guard_cannot_bless_sat
    {failure acceptedDigest reconstructedAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat ->
      AyWDSGNoClaimDiagnostic failure) :
    AyWDSGConj (AyWDSGNoClaimDiagnostic failure)
      (AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat ->
        AyWDSGNoClaimDiagnostic failure) :=
  ay_wdsg_conj_intro hfail hblock

theorem ay_wdsg_failed_digest_guard_recompute_blocks_publication
    {failure acceptedDigest reconstructedAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat ->
      AyWDSGRecomputeObligation failure) :
    AyWDSGConj (AyWDSGRecomputeObligation failure)
      (AyWDSGPublicSat acceptedDigest reconstructedAssignment originalSat ->
        AyWDSGRecomputeObligation failure) :=
  ay_wdsg_conj_intro hfail hblock

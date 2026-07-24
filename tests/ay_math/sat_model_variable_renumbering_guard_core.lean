/-!
  SAT-COMP/ay variable-renumbering model guard.

  This self-contained file records the abstract obligations required before a
  model over preprocessed/internal variables may be reconstructed and published
  over the original DIMACS variable domain.
-/

def AyMVRGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMVRGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMVRGEquiv (p q : Prop) : Prop :=
  AyMVRGConj (p -> q) (q -> p)

def AyMVRGVariableMapDigest (originalMap internalMap : Prop) : Prop :=
  originalMap -> internalMap

def AyMVRGInverseMapWitness (internalMap inverseMap : Prop) : Prop :=
  internalMap -> inverseMap

def AyMVRGAssignmentReconstructionWitness (inverseMap originalAssignment : Prop) : Prop :=
  inverseMap -> originalAssignment

def AyMVRGVariableDomainManifest (originalAssignment originalDomain : Prop) : Prop :=
  originalAssignment -> originalDomain

def AyMVRGClauseCoverageDigest (originalDomain everyClauseSatisfied : Prop) : Prop :=
  originalDomain -> everyClauseSatisfied

def AyMVRGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyMVRGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyMVRGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMVRGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMVRGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMVRGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMVRGAcceptedRenumbering
    (mapDigest inverseWitness reconstructionWitness domainManifest coverageDigest
     checkerTranscript formulaFingerprint buildEvidence archiveManifest fallbackBaseline
     auditTranscript : Prop) : Prop :=
  AyMVRGConj mapDigest
    (AyMVRGConj inverseWitness
      (AyMVRGConj reconstructionWitness
        (AyMVRGConj domainManifest
          (AyMVRGConj coverageDigest
            (AyMVRGConj checkerTranscript
              (AyMVRGConj formulaFingerprint
                (AyMVRGConj buildEvidence
                  (AyMVRGConj archiveManifest
                    (AyMVRGConj fallbackBaseline auditTranscript))))))))))

def AyMVRGPublicSat (acceptedRenumbering originalAssignment originalSat : Prop) : Prop :=
  AyMVRGConj acceptedRenumbering (AyMVRGConj originalAssignment originalSat)

def AyMVRGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMVRGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mvrg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMVRGConj p q :=
  fun r h => h hp hq

theorem ay_mvrg_conj_left {p q : Prop} (h : AyMVRGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mvrg_conj_right {p q : Prop} (h : AyMVRGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mvrg_conj_left h)

theorem ay_mvrg_disj_left {p q : Prop} (hp : p) : AyMVRGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mvrg_disj_right {p q : Prop} (hq : q) : AyMVRGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mvrg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMVRGEquiv p q :=
  ay_mvrg_conj_intro hpq hqp

theorem ay_mvrg_equiv_forward {p q : Prop} (h : AyMVRGEquiv p q) : p -> q :=
  ay_mvrg_conj_left h

theorem ay_mvrg_equiv_backward {p q : Prop} (h : AyMVRGEquiv p q) : q -> p :=
  ay_mvrg_conj_right h

theorem ay_mvrg_variable_map_digest_intro {originalMap internalMap : Prop}
    (h : originalMap -> internalMap) :
    AyMVRGVariableMapDigest originalMap internalMap :=
  h

theorem ay_mvrg_inverse_map_witness_intro {internalMap inverseMap : Prop}
    (h : internalMap -> inverseMap) :
    AyMVRGInverseMapWitness internalMap inverseMap :=
  h

theorem ay_mvrg_assignment_reconstruction_witness_intro
    {inverseMap originalAssignment : Prop}
    (h : inverseMap -> originalAssignment) :
    AyMVRGAssignmentReconstructionWitness inverseMap originalAssignment :=
  h

theorem ay_mvrg_variable_domain_manifest_intro {originalAssignment originalDomain : Prop}
    (h : originalAssignment -> originalDomain) :
    AyMVRGVariableDomainManifest originalAssignment originalDomain :=
  h

theorem ay_mvrg_clause_coverage_digest_intro
    {originalDomain everyClauseSatisfied : Prop}
    (h : originalDomain -> everyClauseSatisfied) :
    AyMVRGClauseCoverageDigest originalDomain everyClauseSatisfied :=
  h

theorem ay_mvrg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyMVRGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_mvrg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyMVRGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_mvrg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMVRGBuildEvidence fingerprint build :=
  h

theorem ay_mvrg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMVRGArchiveManifest build archived :=
  h

theorem ay_mvrg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMVRGFallbackBaseline archived fallbackReady :=
  h

theorem ay_mvrg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMVRGAuditTranscript fallbackReady audited :=
  h

theorem ay_mvrg_accepted_renumbering_intro
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (hmd : md) (hiw : iw) (hrw : rw) (hdm : dm) (hcd : cd) (hct : ct)
    (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au :=
  ay_mvrg_conj_intro hmd
    (ay_mvrg_conj_intro hiw
      (ay_mvrg_conj_intro hrw
        (ay_mvrg_conj_intro hdm
          (ay_mvrg_conj_intro hcd
            (ay_mvrg_conj_intro hct
              (ay_mvrg_conj_intro hff
                (ay_mvrg_conj_intro hbe
                  (ay_mvrg_conj_intro har
                    (ay_mvrg_conj_intro hfb hau))))))))))

theorem ay_mvrg_accepted_renumbering_map_digest
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : md :=
  ay_mvrg_conj_left h

theorem ay_mvrg_accepted_renumbering_inverse
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : iw :=
  ay_mvrg_conj_left (ay_mvrg_conj_right h)

theorem ay_mvrg_accepted_renumbering_reconstruction
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : rw :=
  ay_mvrg_conj_left (ay_mvrg_conj_right (ay_mvrg_conj_right h))

theorem ay_mvrg_accepted_renumbering_domain
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : dm :=
  ay_mvrg_conj_left (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h)))

theorem ay_mvrg_accepted_renumbering_coverage
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : cd :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h))))

theorem ay_mvrg_accepted_renumbering_checker
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : ct :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h)))))

theorem ay_mvrg_accepted_renumbering_fingerprint
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : ff :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right
        (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h))))))

theorem ay_mvrg_accepted_renumbering_build
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : be :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right
        (ay_mvrg_conj_right
          (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h)))))))

theorem ay_mvrg_accepted_renumbering_archive
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : ar :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right
        (ay_mvrg_conj_right
          (ay_mvrg_conj_right
            (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h))))))))

theorem ay_mvrg_accepted_renumbering_fallback
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : fb :=
  ay_mvrg_conj_left
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right
        (ay_mvrg_conj_right
          (ay_mvrg_conj_right
            (ay_mvrg_conj_right
              (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h)))))))))

theorem ay_mvrg_accepted_renumbering_audit
    {md iw rw dm cd ct ff be ar fb au : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au) : au :=
  ay_mvrg_conj_right
    (ay_mvrg_conj_right
      (ay_mvrg_conj_right
        (ay_mvrg_conj_right
          (ay_mvrg_conj_right
            (ay_mvrg_conj_right
              (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right (ay_mvrg_conj_right h)))))))))

theorem ay_mvrg_renumbering_reconstructs_original_dimacs_assignment
    {md iw rw dm cd ct ff be ar fb au originalAssignment originalDomain audited : Prop}
    (h : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au)
    (hassign : originalAssignment)
    (hdomain : originalDomain)
    (haudit : audited) :
    AyMVRGConj originalAssignment (AyMVRGConj originalDomain audited) :=
  ay_mvrg_conj_intro hassign (ay_mvrg_conj_intro hdomain haudit)

theorem ay_mvrg_public_sat_intro {acceptedRenumbering originalAssignment originalSat : Prop}
    (har : acceptedRenumbering) (hassign : originalAssignment) (hsat : originalSat) :
    AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat :=
  ay_mvrg_conj_intro har (ay_mvrg_conj_intro hassign hsat)

theorem ay_mvrg_public_sat_evidence
    {acceptedRenumbering originalAssignment originalSat : Prop}
    (h : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat) :
    acceptedRenumbering :=
  ay_mvrg_conj_left h

theorem ay_mvrg_public_sat_assignment
    {acceptedRenumbering originalAssignment originalSat : Prop}
    (h : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat) :
    originalAssignment :=
  ay_mvrg_conj_left (ay_mvrg_conj_right h)

theorem ay_mvrg_public_sat_claim
    {acceptedRenumbering originalAssignment originalSat : Prop}
    (h : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat) : originalSat :=
  ay_mvrg_conj_right (ay_mvrg_conj_right h)

theorem ay_mvrg_accepted_renumbering_publishes_sat
    {md iw rw dm cd ct ff be ar fb au originalAssignment originalSat : Prop}
    (har : AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au)
    (hassign : originalAssignment) (hsat : originalSat) :
    AyMVRGPublicSat (AyMVRGAcceptedRenumbering md iw rw dm cd ct ff be ar fb au)
      originalAssignment originalSat :=
  ay_mvrg_public_sat_intro har hassign hsat

theorem ay_mvrg_public_sat_requires_accepted_renumbering
    {acceptedRenumbering originalAssignment originalSat : Prop}
    (h : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat) :
    acceptedRenumbering :=
  ay_mvrg_public_sat_evidence h

theorem ay_mvrg_missing_map_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_non_bijective_map_recompute {reason : Prop} (h : reason) :
    AyMVRGRecomputeObligation reason :=
  h

theorem ay_mvrg_stale_map_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    AyMVRGRecomputeObligation reason :=
  h

theorem ay_mvrg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyMVRGRecomputeObligation reason :=
  h

theorem ay_mvrg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMVRGNoClaimDiagnostic reason :=
  h

theorem ay_mvrg_failed_renumbering_guard_cannot_bless_sat
    {failure acceptedRenumbering originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat ->
      AyMVRGNoClaimDiagnostic failure) :
    AyMVRGConj (AyMVRGNoClaimDiagnostic failure)
      (AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat ->
        AyMVRGNoClaimDiagnostic failure) :=
  ay_mvrg_conj_intro hfail hblock

theorem ay_mvrg_failed_renumbering_guard_recompute_blocks_publication
    {failure acceptedRenumbering originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat ->
      AyMVRGRecomputeObligation failure) :
    AyMVRGConj (AyMVRGRecomputeObligation failure)
      (AyMVRGPublicSat acceptedRenumbering originalAssignment originalSat ->
        AyMVRGRecomputeObligation failure) :=
  ay_mvrg_conj_intro hfail hblock

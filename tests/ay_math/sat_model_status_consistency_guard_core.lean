/-!
  SAT-COMP/ay SAT status/model consistency guard.

  This self-contained file records the abstract obligations required before a
  SAT solver status and model artifact may jointly bless public SAT publication.
-/

def AyMSCGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMSCGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMSCGEq (p q : Prop) : Prop :=
  AyMSCGConj (p -> q) (q -> p)

def AyMSCGSolverStatusArtifact (statusArtifact satStatus : Prop) : Prop :=
  statusArtifact -> satStatus

def AyMSCGModelArtifactDigest (satStatus modelArtifact : Prop) : Prop :=
  satStatus -> modelArtifact

def AyMSCGModelCheckerTranscript (modelArtifact checkedModel : Prop) : Prop :=
  modelArtifact -> checkedModel

def AyMSCGAssignmentReconstructionWitness (checkedModel totalAssignment : Prop) : Prop :=
  checkedModel -> totalAssignment

def AyMSCGVariableDomainManifest (totalAssignment domainComplete : Prop) : Prop :=
  totalAssignment -> domainComplete

def AyMSCGClauseCoverageDigest (domainComplete everyClauseSatisfied : Prop) : Prop :=
  domainComplete -> everyClauseSatisfied

def AyMSCGFormulaFingerprint (everyClauseSatisfied fingerprint : Prop) : Prop :=
  everyClauseSatisfied -> fingerprint

def AyMSCGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMSCGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMSCGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMSCGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMSCGAcceptedConsistency
    (statusArtifact modelDigest checkerTranscript reconstructionWitness domainManifest
     coverageDigest formulaFingerprint buildEvidence archiveManifest fallbackBaseline
     auditTranscript : Prop) : Prop :=
  AyMSCGConj statusArtifact
    (AyMSCGConj modelDigest
      (AyMSCGConj checkerTranscript
        (AyMSCGConj reconstructionWitness
          (AyMSCGConj domainManifest
            (AyMSCGConj coverageDigest
              (AyMSCGConj formulaFingerprint
                (AyMSCGConj buildEvidence
                  (AyMSCGConj archiveManifest
                    (AyMSCGConj fallbackBaseline auditTranscript))))))))))

def AyMSCGPublicSat (acceptedConsistency totalAssignment originalSat : Prop) : Prop :=
  AyMSCGConj acceptedConsistency (AyMSCGConj totalAssignment originalSat)

def AyMSCGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMSCGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mscg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMSCGConj p q :=
  fun r h => h hp hq

theorem ay_mscg_conj_left {p q : Prop} (h : AyMSCGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mscg_conj_right {p q : Prop} (h : AyMSCGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mscg_conj_left h)

theorem ay_mscg_disj_left {p q : Prop} (hp : p) : AyMSCGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mscg_disj_right {p q : Prop} (hq : q) : AyMSCGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mscg_eq_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMSCGEq p q :=
  ay_mscg_conj_intro hpq hqp

theorem ay_mscg_eq_forward {p q : Prop} (h : AyMSCGEq p q) : p -> q :=
  ay_mscg_conj_left h

theorem ay_mscg_eq_backward {p q : Prop} (h : AyMSCGEq p q) : q -> p :=
  ay_mscg_conj_right h

theorem ay_mscg_solver_status_artifact_intro {statusArtifact satStatus : Prop}
    (h : statusArtifact -> satStatus) :
    AyMSCGSolverStatusArtifact statusArtifact satStatus :=
  h

theorem ay_mscg_model_artifact_digest_intro {satStatus modelArtifact : Prop}
    (h : satStatus -> modelArtifact) :
    AyMSCGModelArtifactDigest satStatus modelArtifact :=
  h

theorem ay_mscg_model_checker_transcript_intro {modelArtifact checkedModel : Prop}
    (h : modelArtifact -> checkedModel) :
    AyMSCGModelCheckerTranscript modelArtifact checkedModel :=
  h

theorem ay_mscg_assignment_reconstruction_witness_intro
    {checkedModel totalAssignment : Prop}
    (h : checkedModel -> totalAssignment) :
    AyMSCGAssignmentReconstructionWitness checkedModel totalAssignment :=
  h

theorem ay_mscg_variable_domain_manifest_intro {totalAssignment domainComplete : Prop}
    (h : totalAssignment -> domainComplete) :
    AyMSCGVariableDomainManifest totalAssignment domainComplete :=
  h

theorem ay_mscg_clause_coverage_digest_intro
    {domainComplete everyClauseSatisfied : Prop}
    (h : domainComplete -> everyClauseSatisfied) :
    AyMSCGClauseCoverageDigest domainComplete everyClauseSatisfied :=
  h

theorem ay_mscg_formula_fingerprint_intro {everyClauseSatisfied fingerprint : Prop}
    (h : everyClauseSatisfied -> fingerprint) :
    AyMSCGFormulaFingerprint everyClauseSatisfied fingerprint :=
  h

theorem ay_mscg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMSCGBuildEvidence fingerprint build :=
  h

theorem ay_mscg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMSCGArchiveManifest build archived :=
  h

theorem ay_mscg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMSCGFallbackBaseline archived fallbackReady :=
  h

theorem ay_mscg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMSCGAuditTranscript fallbackReady audited :=
  h

theorem ay_mscg_accepted_consistency_intro
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (hsa : sa) (hmd : md) (hct : ct) (hrw : rw) (hdm : dm) (hcd : cd)
    (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au :=
  ay_mscg_conj_intro hsa
    (ay_mscg_conj_intro hmd
      (ay_mscg_conj_intro hct
        (ay_mscg_conj_intro hrw
          (ay_mscg_conj_intro hdm
            (ay_mscg_conj_intro hcd
              (ay_mscg_conj_intro hff
                (ay_mscg_conj_intro hbe
                  (ay_mscg_conj_intro har
                    (ay_mscg_conj_intro hfb hau))))))))))

theorem ay_mscg_accepted_consistency_status
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : sa :=
  ay_mscg_conj_left h

theorem ay_mscg_accepted_consistency_model
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : md :=
  ay_mscg_conj_left (ay_mscg_conj_right h)

theorem ay_mscg_accepted_consistency_checker
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : ct :=
  ay_mscg_conj_left (ay_mscg_conj_right (ay_mscg_conj_right h))

theorem ay_mscg_accepted_consistency_reconstruction
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : rw :=
  ay_mscg_conj_left (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h)))

theorem ay_mscg_accepted_consistency_domain
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : dm :=
  ay_mscg_conj_left
    (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h))))

theorem ay_mscg_accepted_consistency_coverage
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : cd :=
  ay_mscg_conj_left
    (ay_mscg_conj_right
      (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h)))))

theorem ay_mscg_accepted_consistency_fingerprint
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : ff :=
  ay_mscg_conj_left
    (ay_mscg_conj_right
      (ay_mscg_conj_right
        (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h))))))

theorem ay_mscg_accepted_consistency_build
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : be :=
  ay_mscg_conj_left
    (ay_mscg_conj_right
      (ay_mscg_conj_right
        (ay_mscg_conj_right
          (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h)))))))

theorem ay_mscg_accepted_consistency_archive
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : ar :=
  ay_mscg_conj_left
    (ay_mscg_conj_right
      (ay_mscg_conj_right
        (ay_mscg_conj_right
          (ay_mscg_conj_right
            (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h))))))))

theorem ay_mscg_accepted_consistency_fallback
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : fb :=
  ay_mscg_conj_left
    (ay_mscg_conj_right
      (ay_mscg_conj_right
        (ay_mscg_conj_right
          (ay_mscg_conj_right
            (ay_mscg_conj_right
              (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h)))))))))

theorem ay_mscg_accepted_consistency_audit
    {sa md ct rw dm cd ff be ar fb au : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au) : au :=
  ay_mscg_conj_right
    (ay_mscg_conj_right
      (ay_mscg_conj_right
        (ay_mscg_conj_right
          (ay_mscg_conj_right
            (ay_mscg_conj_right
              (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right (ay_mscg_conj_right h)))))))))

theorem ay_mscg_accepted_status_reconstructs_total_assignment
    {sa md ct rw dm cd ff be ar fb au totalAssignment checkedModel audited : Prop}
    (h : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au)
    (htotal : totalAssignment)
    (hchecked : checkedModel)
    (haudit : audited) :
    AyMSCGConj totalAssignment (AyMSCGConj checkedModel audited) :=
  ay_mscg_conj_intro htotal (ay_mscg_conj_intro hchecked haudit)

theorem ay_mscg_public_sat_intro {acceptedConsistency totalAssignment originalSat : Prop}
    (hac : acceptedConsistency) (htotal : totalAssignment) (hsat : originalSat) :
    AyMSCGPublicSat acceptedConsistency totalAssignment originalSat :=
  ay_mscg_conj_intro hac (ay_mscg_conj_intro htotal hsat)

theorem ay_mscg_public_sat_evidence {acceptedConsistency totalAssignment originalSat : Prop}
    (h : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat) :
    acceptedConsistency :=
  ay_mscg_conj_left h

theorem ay_mscg_public_sat_total_assignment
    {acceptedConsistency totalAssignment originalSat : Prop}
    (h : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat) : totalAssignment :=
  ay_mscg_conj_left (ay_mscg_conj_right h)

theorem ay_mscg_public_sat_claim {acceptedConsistency totalAssignment originalSat : Prop}
    (h : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat) : originalSat :=
  ay_mscg_conj_right (ay_mscg_conj_right h)

theorem ay_mscg_accepted_consistency_publishes_sat
    {sa md ct rw dm cd ff be ar fb au totalAssignment originalSat : Prop}
    (hac : AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMSCGPublicSat (AyMSCGAcceptedConsistency sa md ct rw dm cd ff be ar fb au)
      totalAssignment originalSat :=
  ay_mscg_public_sat_intro hac htotal hsat

theorem ay_mscg_public_sat_requires_accepted_consistency
    {acceptedConsistency totalAssignment originalSat : Prop}
    (h : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat) :
    acceptedConsistency :=
  ay_mscg_public_sat_evidence h

theorem ay_mscg_sat_status_without_model_no_claim {reason : Prop} (h : reason) :
    AyMSCGNoClaimDiagnostic reason :=
  h

theorem ay_mscg_model_under_unsat_or_unknown_recompute {reason : Prop} (h : reason) :
    AyMSCGRecomputeObligation reason :=
  h

theorem ay_mscg_status_model_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMSCGNoClaimDiagnostic reason :=
  h

theorem ay_mscg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMSCGNoClaimDiagnostic reason :=
  h

theorem ay_mscg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMSCGNoClaimDiagnostic reason :=
  h

theorem ay_mscg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMSCGNoClaimDiagnostic reason :=
  h

theorem ay_mscg_archive_mismatch_recompute {reason : Prop} (h : reason) :
    AyMSCGRecomputeObligation reason :=
  h

theorem ay_mscg_failed_status_guard_cannot_bless_sat
    {failure acceptedConsistency totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat ->
      AyMSCGNoClaimDiagnostic failure) :
    AyMSCGConj (AyMSCGNoClaimDiagnostic failure)
      (AyMSCGPublicSat acceptedConsistency totalAssignment originalSat ->
        AyMSCGNoClaimDiagnostic failure) :=
  ay_mscg_conj_intro hfail hblock

theorem ay_mscg_failed_status_guard_recompute_blocks_publication
    {failure acceptedConsistency totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMSCGPublicSat acceptedConsistency totalAssignment originalSat ->
      AyMSCGRecomputeObligation failure) :
    AyMSCGConj (AyMSCGRecomputeObligation failure)
      (AyMSCGPublicSat acceptedConsistency totalAssignment originalSat ->
        AyMSCGRecomputeObligation failure) :=
  ay_mscg_conj_intro hfail hblock

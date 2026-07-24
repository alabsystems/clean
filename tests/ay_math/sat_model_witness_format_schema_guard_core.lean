/-!
  SAT-COMP/ay model witness format/schema guard.

  This self-contained file records the abstract obligations required before a
  model witness artifact may be accepted as a public SAT certificate for the
  original formula.
-/

def AyMWSGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMWSGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMWSGEquisat (p q : Prop) : Prop :=
  AyMWSGConj (p -> q) (q -> p)

def AyMWSGFormatVersion (formatVersion schemaVersion : Prop) : Prop :=
  formatVersion -> schemaVersion

def AyMWSGVariableDomainManifest (schemaVersion domainComplete : Prop) : Prop :=
  schemaVersion -> domainComplete

def AyMWSGAssignmentCompletenessDigest (domainComplete totalAssignment : Prop) : Prop :=
  domainComplete -> totalAssignment

def AyMWSGCheckerTranscript (totalAssignment originalFormula : Prop) : Prop :=
  totalAssignment -> originalFormula

def AyMWSGFormulaFingerprint (originalFormula fingerprint : Prop) : Prop :=
  originalFormula -> fingerprint

def AyMWSGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMWSGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMWSGNoClaimFallback (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMWSGAcceptedSchema
    (formatVersion domainManifest completenessDigest checkerTranscript
     formulaFingerprint buildEvidence archiveManifest noClaimFallback : Prop) : Prop :=
  AyMWSGConj formatVersion
    (AyMWSGConj domainManifest
      (AyMWSGConj completenessDigest
        (AyMWSGConj checkerTranscript
          (AyMWSGConj formulaFingerprint
            (AyMWSGConj buildEvidence
              (AyMWSGConj archiveManifest noClaimFallback)))))))

def AyMWSGPublicSat (acceptedSchema totalAssignment originalSat : Prop) : Prop :=
  AyMWSGConj acceptedSchema (AyMWSGConj totalAssignment originalSat)

def AyMWSGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMWSGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mwsg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMWSGConj p q :=
  fun r h => h hp hq

theorem ay_mwsg_conj_left {p q : Prop} (h : AyMWSGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mwsg_conj_right {p q : Prop} (h : AyMWSGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mwsg_conj_left h)

theorem ay_mwsg_disj_left {p q : Prop} (hp : p) : AyMWSGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mwsg_disj_right {p q : Prop} (hq : q) : AyMWSGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mwsg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMWSGEquisat p q :=
  ay_mwsg_conj_intro hpq hqp

theorem ay_mwsg_equisat_forward {p q : Prop} (h : AyMWSGEquisat p q) : p -> q :=
  ay_mwsg_conj_left h

theorem ay_mwsg_equisat_backward {p q : Prop} (h : AyMWSGEquisat p q) : q -> p :=
  ay_mwsg_conj_right h

theorem ay_mwsg_format_version_intro {formatVersion schemaVersion : Prop}
    (h : formatVersion -> schemaVersion) : AyMWSGFormatVersion formatVersion schemaVersion :=
  h

theorem ay_mwsg_variable_domain_manifest_intro {schemaVersion domainComplete : Prop}
    (h : schemaVersion -> domainComplete) :
    AyMWSGVariableDomainManifest schemaVersion domainComplete :=
  h

theorem ay_mwsg_assignment_completeness_digest_intro
    {domainComplete totalAssignment : Prop}
    (h : domainComplete -> totalAssignment) :
    AyMWSGAssignmentCompletenessDigest domainComplete totalAssignment :=
  h

theorem ay_mwsg_checker_transcript_intro {totalAssignment originalFormula : Prop}
    (h : totalAssignment -> originalFormula) :
    AyMWSGCheckerTranscript totalAssignment originalFormula :=
  h

theorem ay_mwsg_formula_fingerprint_intro {originalFormula fingerprint : Prop}
    (h : originalFormula -> fingerprint) :
    AyMWSGFormulaFingerprint originalFormula fingerprint :=
  h

theorem ay_mwsg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMWSGBuildEvidence fingerprint build :=
  h

theorem ay_mwsg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMWSGArchiveManifest build archived :=
  h

theorem ay_mwsg_no_claim_fallback_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMWSGNoClaimFallback archived fallbackReady :=
  h

theorem ay_mwsg_accepted_schema_intro
    {fv dm cd ct ff be ar nf : Prop}
    (hfv : fv) (hdm : dm) (hcd : cd) (hct : ct) (hff : ff) (hbe : be)
    (har : ar) (hnf : nf) :
    AyMWSGAcceptedSchema fv dm cd ct ff be ar nf :=
  ay_mwsg_conj_intro hfv
    (ay_mwsg_conj_intro hdm
      (ay_mwsg_conj_intro hcd
        (ay_mwsg_conj_intro hct
          (ay_mwsg_conj_intro hff
            (ay_mwsg_conj_intro hbe
              (ay_mwsg_conj_intro har hnf)))))))

theorem ay_mwsg_accepted_schema_format_version
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : fv :=
  ay_mwsg_conj_left h

theorem ay_mwsg_accepted_schema_domain_manifest
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : dm :=
  ay_mwsg_conj_left (ay_mwsg_conj_right h)

theorem ay_mwsg_accepted_schema_completeness_digest
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : cd :=
  ay_mwsg_conj_left (ay_mwsg_conj_right (ay_mwsg_conj_right h))

theorem ay_mwsg_accepted_schema_checker
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : ct :=
  ay_mwsg_conj_left (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))

theorem ay_mwsg_accepted_schema_fingerprint
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : ff :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))

theorem ay_mwsg_accepted_schema_build
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : be :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))))

theorem ay_mwsg_accepted_schema_archive
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : ar :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))))

theorem ay_mwsg_accepted_schema_no_claim_fallback
    {fv dm cd ct ff be ar nf : Prop}
    (h : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf) : nf :=
  ay_mwsg_conj_right
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))))

theorem ay_mwsg_public_sat_intro {acceptedSchema totalAssignment originalSat : Prop}
    (has : acceptedSchema) (htotal : totalAssignment) (hsat : originalSat) :
    AyMWSGPublicSat acceptedSchema totalAssignment originalSat :=
  ay_mwsg_conj_intro has (ay_mwsg_conj_intro htotal hsat)

theorem ay_mwsg_public_sat_evidence {acceptedSchema totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat acceptedSchema totalAssignment originalSat) : acceptedSchema :=
  ay_mwsg_conj_left h

theorem ay_mwsg_public_sat_total_assignment
    {acceptedSchema totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat acceptedSchema totalAssignment originalSat) : totalAssignment :=
  ay_mwsg_conj_left (ay_mwsg_conj_right h)

theorem ay_mwsg_public_sat_claim {acceptedSchema totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat acceptedSchema totalAssignment originalSat) : originalSat :=
  ay_mwsg_conj_right (ay_mwsg_conj_right h)

theorem ay_mwsg_schema_reconstructs_total_assignment
    {fv dm cd ct ff be ar nf totalAssignment originalFormula archived : Prop}
    (has : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
    (htotal : totalAssignment)
    (horiginal : originalFormula)
    (harchive : archived) :
    AyMWSGConj totalAssignment (AyMWSGConj originalFormula archived) :=
  ay_mwsg_conj_intro htotal (ay_mwsg_conj_intro horiginal harchive)

theorem ay_mwsg_accepted_schema_publishes_sound_sat
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (has : AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat :=
  ay_mwsg_public_sat_intro has htotal hsat

theorem ay_mwsg_public_sat_requires_accepted_schema
    {acceptedSchema totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat acceptedSchema totalAssignment originalSat) : acceptedSchema :=
  ay_mwsg_public_sat_evidence h

theorem ay_mwsg_publication_requires_format_version
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : fv :=
  ay_mwsg_accepted_schema_format_version (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_domain_manifest
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : dm :=
  ay_mwsg_accepted_schema_domain_manifest (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_completeness_digest
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : cd :=
  ay_mwsg_accepted_schema_completeness_digest (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_checker
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : ct :=
  ay_mwsg_accepted_schema_checker (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_fingerprint
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : ff :=
  ay_mwsg_accepted_schema_fingerprint (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_build
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : be :=
  ay_mwsg_accepted_schema_build (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_archive
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : ar :=
  ay_mwsg_accepted_schema_archive (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_publication_requires_no_claim_fallback
    {fv dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyMWSGPublicSat (AyMWSGAcceptedSchema fv dm cd ct ff be ar nf)
      totalAssignment originalSat) : nf :=
  ay_mwsg_accepted_schema_no_claim_fallback (ay_mwsg_public_sat_requires_accepted_schema h)

theorem ay_mwsg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  h

theorem ay_mwsg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyMWSGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_mwsg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyMWSGRecomputeObligation reason :=
  h

theorem ay_mwsg_recompute_obligation_request {reason : Prop}
    (h : AyMWSGRecomputeObligation reason) : reason :=
  h

theorem ay_mwsg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_no_claim_diagnostic_intro h

theorem ay_mwsg_mismatch_recompute {reason : Prop} (h : reason) :
    AyMWSGRecomputeObligation reason :=
  ay_mwsg_recompute_obligation_intro h

theorem ay_mwsg_format_version_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_domain_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_completeness_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_fallback_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMWSGNoClaimDiagnostic reason :=
  ay_mwsg_mismatch_no_claim h

theorem ay_mwsg_failed_schema_cannot_bless_public_sat
    {failure acceptedSchema totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMWSGPublicSat acceptedSchema totalAssignment originalSat ->
      AyMWSGNoClaimDiagnostic failure) :
    AyMWSGConj (AyMWSGNoClaimDiagnostic failure)
      (AyMWSGPublicSat acceptedSchema totalAssignment originalSat ->
        AyMWSGNoClaimDiagnostic failure) :=
  ay_mwsg_conj_intro (ay_mwsg_no_claim_diagnostic_intro hfail) hblock

theorem ay_mwsg_failed_schema_recompute_blocks_publication
    {failure acceptedSchema totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMWSGPublicSat acceptedSchema totalAssignment originalSat ->
      AyMWSGRecomputeObligation failure) :
    AyMWSGConj (AyMWSGRecomputeObligation failure)
      (AyMWSGPublicSat acceptedSchema totalAssignment originalSat ->
        AyMWSGRecomputeObligation failure) :=
  ay_mwsg_conj_intro (ay_mwsg_recompute_obligation_intro hfail) hblock

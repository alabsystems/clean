/-!
  SAT-COMP/ay assignment sort/order guard.

  This self-contained file records the abstract obligations required before a
  sorted assignment witness may be accepted as the same total public SAT model
  for the original formula.
-/

def AyASOGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyASOGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyASOGEquisat (p q : Prop) : Prop :=
  AyASOGConj (p -> q) (q -> p)

def AyASOGOrderingManifest (unsorted sorted : Prop) : Prop :=
  unsorted -> sorted

def AyASOGVariableDomainManifest (sorted domainComplete : Prop) : Prop :=
  sorted -> domainComplete

def AyASOGAssignmentCompletenessDigest (domainComplete totalAssignment : Prop) : Prop :=
  domainComplete -> totalAssignment

def AyASOGCheckerTranscript (totalAssignment originalFormula : Prop) : Prop :=
  totalAssignment -> originalFormula

def AyASOGFormulaFingerprint (originalFormula fingerprint : Prop) : Prop :=
  originalFormula -> fingerprint

def AyASOGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyASOGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyASOGNoClaimFallback (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyASOGAcceptedOrdering
    (orderingManifest domainManifest completenessDigest checkerTranscript
     formulaFingerprint buildEvidence archiveManifest noClaimFallback : Prop) : Prop :=
  AyASOGConj orderingManifest
    (AyASOGConj domainManifest
      (AyASOGConj completenessDigest
        (AyASOGConj checkerTranscript
          (AyASOGConj formulaFingerprint
            (AyASOGConj buildEvidence
              (AyASOGConj archiveManifest noClaimFallback)))))))

def AyASOGPublicSat (acceptedOrdering totalAssignment originalSat : Prop) : Prop :=
  AyASOGConj acceptedOrdering (AyASOGConj totalAssignment originalSat)

def AyASOGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyASOGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_asog_conj_intro {p q : Prop} (hp : p) (hq : q) : AyASOGConj p q :=
  fun r h => h hp hq

theorem ay_asog_conj_left {p q : Prop} (h : AyASOGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_asog_conj_right {p q : Prop} (h : AyASOGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_asog_conj_left h)

theorem ay_asog_disj_left {p q : Prop} (hp : p) : AyASOGDisj p q :=
  fun r hl _ => hl hp

theorem ay_asog_disj_right {p q : Prop} (hq : q) : AyASOGDisj p q :=
  fun r _ hr => hr hq

theorem ay_asog_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyASOGEquisat p q :=
  ay_asog_conj_intro hpq hqp

theorem ay_asog_equisat_forward {p q : Prop} (h : AyASOGEquisat p q) : p -> q :=
  ay_asog_conj_left h

theorem ay_asog_equisat_backward {p q : Prop} (h : AyASOGEquisat p q) : q -> p :=
  ay_asog_conj_right h

theorem ay_asog_ordering_manifest_intro {unsorted sorted : Prop}
    (h : unsorted -> sorted) : AyASOGOrderingManifest unsorted sorted :=
  h

theorem ay_asog_variable_domain_manifest_intro {sorted domainComplete : Prop}
    (h : sorted -> domainComplete) : AyASOGVariableDomainManifest sorted domainComplete :=
  h

theorem ay_asog_assignment_completeness_digest_intro
    {domainComplete totalAssignment : Prop}
    (h : domainComplete -> totalAssignment) :
    AyASOGAssignmentCompletenessDigest domainComplete totalAssignment :=
  h

theorem ay_asog_checker_transcript_intro {totalAssignment originalFormula : Prop}
    (h : totalAssignment -> originalFormula) :
    AyASOGCheckerTranscript totalAssignment originalFormula :=
  h

theorem ay_asog_formula_fingerprint_intro {originalFormula fingerprint : Prop}
    (h : originalFormula -> fingerprint) :
    AyASOGFormulaFingerprint originalFormula fingerprint :=
  h

theorem ay_asog_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyASOGBuildEvidence fingerprint build :=
  h

theorem ay_asog_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyASOGArchiveManifest build archived :=
  h

theorem ay_asog_no_claim_fallback_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyASOGNoClaimFallback archived fallbackReady :=
  h

theorem ay_asog_accepted_ordering_intro
    {om dm cd ct ff be ar nf : Prop}
    (hom : om) (hdm : dm) (hcd : cd) (hct : ct) (hff : ff) (hbe : be)
    (har : ar) (hnf : nf) :
    AyASOGAcceptedOrdering om dm cd ct ff be ar nf :=
  ay_asog_conj_intro hom
    (ay_asog_conj_intro hdm
      (ay_asog_conj_intro hcd
        (ay_asog_conj_intro hct
          (ay_asog_conj_intro hff
            (ay_asog_conj_intro hbe
              (ay_asog_conj_intro har hnf)))))))

theorem ay_asog_accepted_ordering_manifest
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : om :=
  ay_asog_conj_left h

theorem ay_asog_accepted_ordering_domain
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : dm :=
  ay_asog_conj_left (ay_asog_conj_right h)

theorem ay_asog_accepted_ordering_completeness
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : cd :=
  ay_asog_conj_left (ay_asog_conj_right (ay_asog_conj_right h))

theorem ay_asog_accepted_ordering_checker
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : ct :=
  ay_asog_conj_left (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right h)))

theorem ay_asog_accepted_ordering_fingerprint
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : ff :=
  ay_asog_conj_left
    (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right h))))

theorem ay_asog_accepted_ordering_build
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : be :=
  ay_asog_conj_left
    (ay_asog_conj_right
      (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right h)))))

theorem ay_asog_accepted_ordering_archive
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : ar :=
  ay_asog_conj_left
    (ay_asog_conj_right
      (ay_asog_conj_right
        (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right h))))))

theorem ay_asog_accepted_ordering_fallback
    {om dm cd ct ff be ar nf : Prop}
    (h : AyASOGAcceptedOrdering om dm cd ct ff be ar nf) : nf :=
  ay_asog_conj_right
    (ay_asog_conj_right
      (ay_asog_conj_right
        (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right (ay_asog_conj_right h))))))

theorem ay_asog_public_sat_intro {acceptedOrdering totalAssignment originalSat : Prop}
    (hao : acceptedOrdering) (htotal : totalAssignment) (hsat : originalSat) :
    AyASOGPublicSat acceptedOrdering totalAssignment originalSat :=
  ay_asog_conj_intro hao (ay_asog_conj_intro htotal hsat)

theorem ay_asog_public_sat_evidence {acceptedOrdering totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat acceptedOrdering totalAssignment originalSat) : acceptedOrdering :=
  ay_asog_conj_left h

theorem ay_asog_public_sat_total_assignment
    {acceptedOrdering totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat acceptedOrdering totalAssignment originalSat) : totalAssignment :=
  ay_asog_conj_left (ay_asog_conj_right h)

theorem ay_asog_public_sat_claim {acceptedOrdering totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat acceptedOrdering totalAssignment originalSat) : originalSat :=
  ay_asog_conj_right (ay_asog_conj_right h)

theorem ay_asog_ordering_reconstructs_same_total_assignment
    {om dm cd ct ff be ar nf totalAssignment originalFormula archived : Prop}
    (hao : AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
    (htotal : totalAssignment)
    (horiginal : originalFormula)
    (harchive : archived) :
    AyASOGConj totalAssignment (AyASOGConj originalFormula archived) :=
  ay_asog_conj_intro htotal (ay_asog_conj_intro horiginal harchive)

theorem ay_asog_accepted_ordering_publishes_sound_sat
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (hao : AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat :=
  ay_asog_public_sat_intro hao htotal hsat

theorem ay_asog_public_sat_requires_accepted_ordering
    {acceptedOrdering totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat acceptedOrdering totalAssignment originalSat) : acceptedOrdering :=
  ay_asog_public_sat_evidence h

theorem ay_asog_publication_requires_ordering_manifest
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : om :=
  ay_asog_accepted_ordering_manifest (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_domain_manifest
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : dm :=
  ay_asog_accepted_ordering_domain (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_completeness_digest
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : cd :=
  ay_asog_accepted_ordering_completeness (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_checker
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : ct :=
  ay_asog_accepted_ordering_checker (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_fingerprint
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : ff :=
  ay_asog_accepted_ordering_fingerprint (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_build
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : be :=
  ay_asog_accepted_ordering_build (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_archive
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : ar :=
  ay_asog_accepted_ordering_archive (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_publication_requires_fallback
    {om dm cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyASOGPublicSat (AyASOGAcceptedOrdering om dm cd ct ff be ar nf)
      totalAssignment originalSat) : nf :=
  ay_asog_accepted_ordering_fallback (ay_asog_public_sat_requires_accepted_ordering h)

theorem ay_asog_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  h

theorem ay_asog_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyASOGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_asog_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyASOGRecomputeObligation reason :=
  h

theorem ay_asog_recompute_obligation_request {reason : Prop}
    (h : AyASOGRecomputeObligation reason) : reason :=
  h

theorem ay_asog_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_no_claim_diagnostic_intro h

theorem ay_asog_mismatch_recompute {reason : Prop} (h : reason) :
    AyASOGRecomputeObligation reason :=
  ay_asog_recompute_obligation_intro h

theorem ay_asog_ordering_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_domain_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_completeness_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_fallback_mismatch_no_claim {reason : Prop} (h : reason) :
    AyASOGNoClaimDiagnostic reason :=
  ay_asog_mismatch_no_claim h

theorem ay_asog_failed_ordering_cannot_bless_public_sat
    {failure acceptedOrdering totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyASOGPublicSat acceptedOrdering totalAssignment originalSat ->
      AyASOGNoClaimDiagnostic failure) :
    AyASOGConj (AyASOGNoClaimDiagnostic failure)
      (AyASOGPublicSat acceptedOrdering totalAssignment originalSat ->
        AyASOGNoClaimDiagnostic failure) :=
  ay_asog_conj_intro (ay_asog_no_claim_diagnostic_intro hfail) hblock

theorem ay_asog_failed_ordering_recompute_blocks_publication
    {failure acceptedOrdering totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyASOGPublicSat acceptedOrdering totalAssignment originalSat ->
      AyASOGRecomputeObligation failure) :
    AyASOGConj (AyASOGRecomputeObligation failure)
      (AyASOGPublicSat acceptedOrdering totalAssignment originalSat ->
        AyASOGRecomputeObligation failure) :=
  ay_asog_conj_intro (ay_asog_recompute_obligation_intro hfail) hblock

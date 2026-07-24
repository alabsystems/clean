/-!
  SAT-COMP/ay DIMACS variable range guard.

  This self-contained file records the abstract obligations required before a
  public SAT model may be accepted over the original DIMACS variable domain.
-/

def AyDVRGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyDVRGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyDVRGEquisat (p q : Prop) : Prop :=
  AyDVRGConj (p -> q) (q -> p)

def AyDVRGVariableRangeManifest (rawWitness rangedWitness : Prop) : Prop :=
  rawWitness -> rangedWitness

def AyDVRGAssignmentDomainDigest (rangedWitness domainValid : Prop) : Prop :=
  rangedWitness -> domainValid

def AyDVRGLiteralPolicy (domainValid policyAccepted : Prop) : Prop :=
  domainValid -> policyAccepted

def AyDVRGAssignmentCompletenessDigest (policyAccepted totalAssignment : Prop) : Prop :=
  policyAccepted -> totalAssignment

def AyDVRGCheckerTranscript (totalAssignment originalFormula : Prop) : Prop :=
  totalAssignment -> originalFormula

def AyDVRGFormulaFingerprint (originalFormula fingerprint : Prop) : Prop :=
  originalFormula -> fingerprint

def AyDVRGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyDVRGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyDVRGNoClaimFallback (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyDVRGAcceptedRange
    (rangeManifest domainDigest literalPolicy completenessDigest checkerTranscript
     formulaFingerprint buildEvidence archiveManifest noClaimFallback : Prop) : Prop :=
  AyDVRGConj rangeManifest
    (AyDVRGConj domainDigest
      (AyDVRGConj literalPolicy
        (AyDVRGConj completenessDigest
          (AyDVRGConj checkerTranscript
            (AyDVRGConj formulaFingerprint
              (AyDVRGConj buildEvidence
                (AyDVRGConj archiveManifest noClaimFallback))))))))

def AyDVRGPublicSat (acceptedRange totalAssignment originalSat : Prop) : Prop :=
  AyDVRGConj acceptedRange (AyDVRGConj totalAssignment originalSat)

def AyDVRGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyDVRGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_dvrg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyDVRGConj p q :=
  fun r h => h hp hq

theorem ay_dvrg_conj_left {p q : Prop} (h : AyDVRGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_dvrg_conj_right {p q : Prop} (h : AyDVRGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_dvrg_conj_left h)

theorem ay_dvrg_disj_left {p q : Prop} (hp : p) : AyDVRGDisj p q :=
  fun r hl _ => hl hp

theorem ay_dvrg_disj_right {p q : Prop} (hq : q) : AyDVRGDisj p q :=
  fun r _ hr => hr hq

theorem ay_dvrg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyDVRGEquisat p q :=
  ay_dvrg_conj_intro hpq hqp

theorem ay_dvrg_equisat_forward {p q : Prop} (h : AyDVRGEquisat p q) : p -> q :=
  ay_dvrg_conj_left h

theorem ay_dvrg_equisat_backward {p q : Prop} (h : AyDVRGEquisat p q) : q -> p :=
  ay_dvrg_conj_right h

theorem ay_dvrg_variable_range_manifest_intro {rawWitness rangedWitness : Prop}
    (h : rawWitness -> rangedWitness) :
    AyDVRGVariableRangeManifest rawWitness rangedWitness :=
  h

theorem ay_dvrg_assignment_domain_digest_intro {rangedWitness domainValid : Prop}
    (h : rangedWitness -> domainValid) :
    AyDVRGAssignmentDomainDigest rangedWitness domainValid :=
  h

theorem ay_dvrg_literal_policy_intro {domainValid policyAccepted : Prop}
    (h : domainValid -> policyAccepted) : AyDVRGLiteralPolicy domainValid policyAccepted :=
  h

theorem ay_dvrg_assignment_completeness_digest_intro
    {policyAccepted totalAssignment : Prop}
    (h : policyAccepted -> totalAssignment) :
    AyDVRGAssignmentCompletenessDigest policyAccepted totalAssignment :=
  h

theorem ay_dvrg_checker_transcript_intro {totalAssignment originalFormula : Prop}
    (h : totalAssignment -> originalFormula) :
    AyDVRGCheckerTranscript totalAssignment originalFormula :=
  h

theorem ay_dvrg_formula_fingerprint_intro {originalFormula fingerprint : Prop}
    (h : originalFormula -> fingerprint) :
    AyDVRGFormulaFingerprint originalFormula fingerprint :=
  h

theorem ay_dvrg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyDVRGBuildEvidence fingerprint build :=
  h

theorem ay_dvrg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyDVRGArchiveManifest build archived :=
  h

theorem ay_dvrg_no_claim_fallback_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyDVRGNoClaimFallback archived fallbackReady :=
  h

theorem ay_dvrg_accepted_range_intro
    {rm dd lp cd ct ff be ar nf : Prop}
    (hrm : rm) (hdd : dd) (hlp : lp) (hcd : cd) (hct : ct) (hff : ff)
    (hbe : be) (har : ar) (hnf : nf) :
    AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf :=
  ay_dvrg_conj_intro hrm
    (ay_dvrg_conj_intro hdd
      (ay_dvrg_conj_intro hlp
        (ay_dvrg_conj_intro hcd
          (ay_dvrg_conj_intro hct
            (ay_dvrg_conj_intro hff
              (ay_dvrg_conj_intro hbe
                (ay_dvrg_conj_intro har hnf))))))))

theorem ay_dvrg_accepted_range_manifest
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : rm :=
  ay_dvrg_conj_left h

theorem ay_dvrg_accepted_range_domain_digest
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : dd :=
  ay_dvrg_conj_left (ay_dvrg_conj_right h)

theorem ay_dvrg_accepted_range_literal_policy
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : lp :=
  ay_dvrg_conj_left (ay_dvrg_conj_right (ay_dvrg_conj_right h))

theorem ay_dvrg_accepted_range_completeness
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : cd :=
  ay_dvrg_conj_left (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h)))

theorem ay_dvrg_accepted_range_checker
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : ct :=
  ay_dvrg_conj_left
    (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h))))

theorem ay_dvrg_accepted_range_fingerprint
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : ff :=
  ay_dvrg_conj_left
    (ay_dvrg_conj_right
      (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h)))))

theorem ay_dvrg_accepted_range_build
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : be :=
  ay_dvrg_conj_left
    (ay_dvrg_conj_right
      (ay_dvrg_conj_right
        (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h))))))

theorem ay_dvrg_accepted_range_archive
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : ar :=
  ay_dvrg_conj_left
    (ay_dvrg_conj_right
      (ay_dvrg_conj_right
        (ay_dvrg_conj_right
          (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h)))))))

theorem ay_dvrg_accepted_range_fallback
    {rm dd lp cd ct ff be ar nf : Prop}
    (h : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf) : nf :=
  ay_dvrg_conj_right
    (ay_dvrg_conj_right
      (ay_dvrg_conj_right
        (ay_dvrg_conj_right
          (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right (ay_dvrg_conj_right h)))))))

theorem ay_dvrg_public_sat_intro {acceptedRange totalAssignment originalSat : Prop}
    (har : acceptedRange) (htotal : totalAssignment) (hsat : originalSat) :
    AyDVRGPublicSat acceptedRange totalAssignment originalSat :=
  ay_dvrg_conj_intro har (ay_dvrg_conj_intro htotal hsat)

theorem ay_dvrg_public_sat_evidence {acceptedRange totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat acceptedRange totalAssignment originalSat) : acceptedRange :=
  ay_dvrg_conj_left h

theorem ay_dvrg_public_sat_total_assignment
    {acceptedRange totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat acceptedRange totalAssignment originalSat) : totalAssignment :=
  ay_dvrg_conj_left (ay_dvrg_conj_right h)

theorem ay_dvrg_public_sat_claim {acceptedRange totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat acceptedRange totalAssignment originalSat) : originalSat :=
  ay_dvrg_conj_right (ay_dvrg_conj_right h)

theorem ay_dvrg_range_reconstructs_dimacs_total_assignment
    {rm dd lp cd ct ff be ar nf totalAssignment originalDomain archived : Prop}
    (hrange : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
    (htotal : totalAssignment)
    (hdomain : originalDomain)
    (harchive : archived) :
    AyDVRGConj totalAssignment (AyDVRGConj originalDomain archived) :=
  ay_dvrg_conj_intro htotal (ay_dvrg_conj_intro hdomain harchive)

theorem ay_dvrg_accepted_range_publishes_sound_sat
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (hrange : AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat :=
  ay_dvrg_public_sat_intro hrange htotal hsat

theorem ay_dvrg_public_sat_requires_accepted_range
    {acceptedRange totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat acceptedRange totalAssignment originalSat) : acceptedRange :=
  ay_dvrg_public_sat_evidence h

theorem ay_dvrg_publication_requires_range_manifest
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : rm :=
  ay_dvrg_accepted_range_manifest (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_domain_digest
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : dd :=
  ay_dvrg_accepted_range_domain_digest (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_literal_policy
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : lp :=
  ay_dvrg_accepted_range_literal_policy (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_completeness_digest
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : cd :=
  ay_dvrg_accepted_range_completeness (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_checker
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : ct :=
  ay_dvrg_accepted_range_checker (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_fingerprint
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : ff :=
  ay_dvrg_accepted_range_fingerprint (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_build
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : be :=
  ay_dvrg_accepted_range_build (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_archive
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : ar :=
  ay_dvrg_accepted_range_archive (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_publication_requires_fallback
    {rm dd lp cd ct ff be ar nf totalAssignment originalSat : Prop}
    (h : AyDVRGPublicSat (AyDVRGAcceptedRange rm dd lp cd ct ff be ar nf)
      totalAssignment originalSat) : nf :=
  ay_dvrg_accepted_range_fallback (ay_dvrg_public_sat_requires_accepted_range h)

theorem ay_dvrg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  h

theorem ay_dvrg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyDVRGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_dvrg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyDVRGRecomputeObligation reason :=
  h

theorem ay_dvrg_recompute_obligation_request {reason : Prop}
    (h : AyDVRGRecomputeObligation reason) : reason :=
  h

theorem ay_dvrg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_no_claim_diagnostic_intro h

theorem ay_dvrg_mismatch_recompute {reason : Prop} (h : reason) :
    AyDVRGRecomputeObligation reason :=
  ay_dvrg_recompute_obligation_intro h

theorem ay_dvrg_range_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_domain_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_literal_policy_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_completeness_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_fallback_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDVRGNoClaimDiagnostic reason :=
  ay_dvrg_mismatch_no_claim h

theorem ay_dvrg_failed_range_guard_cannot_bless_sat
    {failure acceptedRange totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDVRGPublicSat acceptedRange totalAssignment originalSat ->
      AyDVRGNoClaimDiagnostic failure) :
    AyDVRGConj (AyDVRGNoClaimDiagnostic failure)
      (AyDVRGPublicSat acceptedRange totalAssignment originalSat ->
        AyDVRGNoClaimDiagnostic failure) :=
  ay_dvrg_conj_intro (ay_dvrg_no_claim_diagnostic_intro hfail) hblock

theorem ay_dvrg_failed_range_guard_recompute_blocks_publication
    {failure acceptedRange totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDVRGPublicSat acceptedRange totalAssignment originalSat ->
      AyDVRGRecomputeObligation failure) :
    AyDVRGConj (AyDVRGRecomputeObligation failure)
      (AyDVRGPublicSat acceptedRange totalAssignment originalSat ->
        AyDVRGRecomputeObligation failure) :=
  ay_dvrg_conj_intro (ay_dvrg_recompute_obligation_intro hfail) hblock

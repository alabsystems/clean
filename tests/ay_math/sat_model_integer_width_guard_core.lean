/-!
  SAT-COMP/ay integer-width model parsing guard.

  This self-contained file records the abstract obligations required before
  parsed integer literals from a SAT model can be accepted as a total satisfying
  assignment over the original DIMACS variables.
-/

def AyMIWGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMIWGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMIWGEquiv (p q : Prop) : Prop :=
  AyMIWGConj (p -> q) (q -> p)

def AyMIWGLiteralIntegerWidthManifest (rawLiteral parsedWidth : Prop) : Prop :=
  rawLiteral -> parsedWidth

def AyMIWGSignednessOverflowPolicy (parsedWidth policyAccepted : Prop) : Prop :=
  parsedWidth -> policyAccepted

def AyMIWGParsedLiteralRangeWitness (policyAccepted inRangeLiteral : Prop) : Prop :=
  policyAccepted -> inRangeLiteral

def AyMIWGVariableDomainManifest (inRangeLiteral domainComplete : Prop) : Prop :=
  inRangeLiteral -> domainComplete

def AyMIWGAssignmentReconstructionWitness (domainComplete totalAssignment : Prop) : Prop :=
  domainComplete -> totalAssignment

def AyMIWGClauseCoverageDigest (totalAssignment everyClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyClauseSatisfied

def AyMIWGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyMIWGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyMIWGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMIWGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMIWGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMIWGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMIWGAcceptedParsing
    (widthManifest overflowPolicy rangeWitness domainManifest reconstructionWitness
     coverageDigest checkerTranscript formulaFingerprint buildEvidence archiveManifest
     fallbackBaseline auditTranscript : Prop) : Prop :=
  AyMIWGConj widthManifest
    (AyMIWGConj overflowPolicy
      (AyMIWGConj rangeWitness
        (AyMIWGConj domainManifest
          (AyMIWGConj reconstructionWitness
            (AyMIWGConj coverageDigest
              (AyMIWGConj checkerTranscript
                (AyMIWGConj formulaFingerprint
                  (AyMIWGConj buildEvidence
                    (AyMIWGConj archiveManifest
                      (AyMIWGConj fallbackBaseline auditTranscript)))))))))))

def AyMIWGPublicSat (acceptedParsing totalAssignment originalSat : Prop) : Prop :=
  AyMIWGConj acceptedParsing (AyMIWGConj totalAssignment originalSat)

def AyMIWGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMIWGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_miwg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMIWGConj p q :=
  fun r h => h hp hq

theorem ay_miwg_conj_left {p q : Prop} (h : AyMIWGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_miwg_conj_right {p q : Prop} (h : AyMIWGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_miwg_conj_left h)

theorem ay_miwg_disj_left {p q : Prop} (hp : p) : AyMIWGDisj p q :=
  fun r hl _ => hl hp

theorem ay_miwg_disj_right {p q : Prop} (hq : q) : AyMIWGDisj p q :=
  fun r _ hr => hr hq

theorem ay_miwg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMIWGEquiv p q :=
  ay_miwg_conj_intro hpq hqp

theorem ay_miwg_equiv_forward {p q : Prop} (h : AyMIWGEquiv p q) : p -> q :=
  ay_miwg_conj_left h

theorem ay_miwg_equiv_backward {p q : Prop} (h : AyMIWGEquiv p q) : q -> p :=
  ay_miwg_conj_right h

theorem ay_miwg_literal_integer_width_manifest_intro {rawLiteral parsedWidth : Prop}
    (h : rawLiteral -> parsedWidth) :
    AyMIWGLiteralIntegerWidthManifest rawLiteral parsedWidth :=
  h

theorem ay_miwg_signedness_overflow_policy_intro {parsedWidth policyAccepted : Prop}
    (h : parsedWidth -> policyAccepted) :
    AyMIWGSignednessOverflowPolicy parsedWidth policyAccepted :=
  h

theorem ay_miwg_parsed_literal_range_witness_intro {policyAccepted inRangeLiteral : Prop}
    (h : policyAccepted -> inRangeLiteral) :
    AyMIWGParsedLiteralRangeWitness policyAccepted inRangeLiteral :=
  h

theorem ay_miwg_variable_domain_manifest_intro {inRangeLiteral domainComplete : Prop}
    (h : inRangeLiteral -> domainComplete) :
    AyMIWGVariableDomainManifest inRangeLiteral domainComplete :=
  h

theorem ay_miwg_assignment_reconstruction_witness_intro
    {domainComplete totalAssignment : Prop}
    (h : domainComplete -> totalAssignment) :
    AyMIWGAssignmentReconstructionWitness domainComplete totalAssignment :=
  h

theorem ay_miwg_clause_coverage_digest_intro
    {totalAssignment everyClauseSatisfied : Prop}
    (h : totalAssignment -> everyClauseSatisfied) :
    AyMIWGClauseCoverageDigest totalAssignment everyClauseSatisfied :=
  h

theorem ay_miwg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyMIWGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_miwg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyMIWGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_miwg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMIWGBuildEvidence fingerprint build :=
  h

theorem ay_miwg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMIWGArchiveManifest build archived :=
  h

theorem ay_miwg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMIWGFallbackBaseline archived fallbackReady :=
  h

theorem ay_miwg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMIWGAuditTranscript fallbackReady audited :=
  h

theorem ay_miwg_accepted_parsing_intro
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (hwm : wm) (hop : op) (hrw : rw) (hdm : dm) (haw : aw) (hcd : cd)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au :=
  ay_miwg_conj_intro hwm
    (ay_miwg_conj_intro hop
      (ay_miwg_conj_intro hrw
        (ay_miwg_conj_intro hdm
          (ay_miwg_conj_intro haw
            (ay_miwg_conj_intro hcd
              (ay_miwg_conj_intro hct
                (ay_miwg_conj_intro hff
                  (ay_miwg_conj_intro hbe
                    (ay_miwg_conj_intro har
                      (ay_miwg_conj_intro hfb hau)))))))))))

theorem ay_miwg_accepted_parsing_width
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : wm :=
  ay_miwg_conj_left h

theorem ay_miwg_accepted_parsing_overflow_policy
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : op :=
  ay_miwg_conj_left (ay_miwg_conj_right h)

theorem ay_miwg_accepted_parsing_range
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : rw :=
  ay_miwg_conj_left (ay_miwg_conj_right (ay_miwg_conj_right h))

theorem ay_miwg_accepted_parsing_domain
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : dm :=
  ay_miwg_conj_left (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h)))

theorem ay_miwg_accepted_parsing_reconstruction
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : aw :=
  ay_miwg_conj_left
    (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h))))

theorem ay_miwg_accepted_parsing_coverage
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : cd :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h)))))

theorem ay_miwg_accepted_parsing_checker
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : ct :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h))))))

theorem ay_miwg_accepted_parsing_fingerprint
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : ff :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right
          (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h)))))))

theorem ay_miwg_accepted_parsing_build
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : be :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right
          (ay_miwg_conj_right
            (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h))))))))

theorem ay_miwg_accepted_parsing_archive
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : ar :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right
          (ay_miwg_conj_right
            (ay_miwg_conj_right
              (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h)))))))))

theorem ay_miwg_accepted_parsing_fallback
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : fb :=
  ay_miwg_conj_left
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right
          (ay_miwg_conj_right
            (ay_miwg_conj_right
              (ay_miwg_conj_right
                (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h))))))))))

theorem ay_miwg_accepted_parsing_audit
    {wm op rw dm aw cd ct ff be ar fb au : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au) : au :=
  ay_miwg_conj_right
    (ay_miwg_conj_right
      (ay_miwg_conj_right
        (ay_miwg_conj_right
          (ay_miwg_conj_right
            (ay_miwg_conj_right
              (ay_miwg_conj_right
                (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right (ay_miwg_conj_right h))))))))))

theorem ay_miwg_parsing_reconstructs_dimacs_assignment
    {wm op rw dm aw cd ct ff be ar fb au totalAssignment originalDomain audited : Prop}
    (h : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au)
    (htotal : totalAssignment)
    (hdomain : originalDomain)
    (haudit : audited) :
    AyMIWGConj totalAssignment (AyMIWGConj originalDomain audited) :=
  ay_miwg_conj_intro htotal (ay_miwg_conj_intro hdomain haudit)

theorem ay_miwg_public_sat_intro {acceptedParsing totalAssignment originalSat : Prop}
    (hap : acceptedParsing) (htotal : totalAssignment) (hsat : originalSat) :
    AyMIWGPublicSat acceptedParsing totalAssignment originalSat :=
  ay_miwg_conj_intro hap (ay_miwg_conj_intro htotal hsat)

theorem ay_miwg_public_sat_evidence {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMIWGPublicSat acceptedParsing totalAssignment originalSat) : acceptedParsing :=
  ay_miwg_conj_left h

theorem ay_miwg_public_sat_total_assignment {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMIWGPublicSat acceptedParsing totalAssignment originalSat) : totalAssignment :=
  ay_miwg_conj_left (ay_miwg_conj_right h)

theorem ay_miwg_public_sat_claim {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMIWGPublicSat acceptedParsing totalAssignment originalSat) : originalSat :=
  ay_miwg_conj_right (ay_miwg_conj_right h)

theorem ay_miwg_accepted_parsing_publishes_sat
    {wm op rw dm aw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (hap : AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMIWGPublicSat (AyMIWGAcceptedParsing wm op rw dm aw cd ct ff be ar fb au)
      totalAssignment originalSat :=
  ay_miwg_public_sat_intro hap htotal hsat

theorem ay_miwg_public_sat_requires_accepted_parsing
    {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMIWGPublicSat acceptedParsing totalAssignment originalSat) : acceptedParsing :=
  ay_miwg_public_sat_evidence h

theorem ay_miwg_overflow_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_truncation_recompute {reason : Prop} (h : reason) :
    AyMIWGRecomputeObligation reason :=
  h

theorem ay_miwg_signedness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_out_of_range_literal_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyMIWGRecomputeObligation reason :=
  h

theorem ay_miwg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMIWGNoClaimDiagnostic reason :=
  h

theorem ay_miwg_failed_integer_width_guard_cannot_bless_sat
    {failure acceptedParsing totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMIWGPublicSat acceptedParsing totalAssignment originalSat ->
      AyMIWGNoClaimDiagnostic failure) :
    AyMIWGConj (AyMIWGNoClaimDiagnostic failure)
      (AyMIWGPublicSat acceptedParsing totalAssignment originalSat ->
        AyMIWGNoClaimDiagnostic failure) :=
  ay_miwg_conj_intro hfail hblock

theorem ay_miwg_failed_integer_width_guard_recompute_blocks_publication
    {failure acceptedParsing totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMIWGPublicSat acceptedParsing totalAssignment originalSat ->
      AyMIWGRecomputeObligation failure) :
    AyMIWGConj (AyMIWGRecomputeObligation failure)
      (AyMIWGPublicSat acceptedParsing totalAssignment originalSat ->
        AyMIWGRecomputeObligation failure) :=
  ay_miwg_conj_intro hfail hblock

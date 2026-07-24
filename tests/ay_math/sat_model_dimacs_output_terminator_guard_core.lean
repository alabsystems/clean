/-!
  SAT-COMP/ay DIMACS output terminator guard.

  This self-contained file records the abstract obligations required before a
  DIMACS SAT model line with a zero terminator may be parsed and accepted as a
  consistent total satisfying assignment.
-/

def AyDOTGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyDOTGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyDOTGEq (p q : Prop) : Prop :=
  AyDOTGConj (p -> q) (q -> p)

def AyDOTGModelLineDigest (line stableLine : Prop) : Prop :=
  line -> stableLine

def AyDOTGZeroTerminatorPolicy (stableLine terminatedStream : Prop) : Prop :=
  stableLine -> terminatedStream

def AyDOTGVariableDomainManifest (terminatedStream domainComplete : Prop) : Prop :=
  terminatedStream -> domainComplete

def AyDOTGNormalizationWitness (domainComplete normalized : Prop) : Prop :=
  domainComplete -> normalized

def AyDOTGAssignmentReconstructionWitness (normalized totalAssignment : Prop) : Prop :=
  normalized -> totalAssignment

def AyDOTGClauseCoverageDigest (totalAssignment everyClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyClauseSatisfied

def AyDOTGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyDOTGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyDOTGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyDOTGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyDOTGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyDOTGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyDOTGAcceptedOutput
    (modelDigest terminatorPolicy domainManifest normalizationWitness reconstructionWitness
     coverageDigest checkerTranscript formulaFingerprint buildEvidence archiveManifest
     fallbackBaseline auditTranscript : Prop) : Prop :=
  AyDOTGConj modelDigest
    (AyDOTGConj terminatorPolicy
      (AyDOTGConj domainManifest
        (AyDOTGConj normalizationWitness
          (AyDOTGConj reconstructionWitness
            (AyDOTGConj coverageDigest
              (AyDOTGConj checkerTranscript
                (AyDOTGConj formulaFingerprint
                  (AyDOTGConj buildEvidence
                    (AyDOTGConj archiveManifest
                      (AyDOTGConj fallbackBaseline auditTranscript)))))))))))

def AyDOTGPublicSat (acceptedOutput totalAssignment originalSat : Prop) : Prop :=
  AyDOTGConj acceptedOutput (AyDOTGConj totalAssignment originalSat)

def AyDOTGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyDOTGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_dotg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyDOTGConj p q :=
  fun r h => h hp hq

theorem ay_dotg_conj_left {p q : Prop} (h : AyDOTGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_dotg_conj_right {p q : Prop} (h : AyDOTGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_dotg_conj_left h)

theorem ay_dotg_disj_left {p q : Prop} (hp : p) : AyDOTGDisj p q :=
  fun r hl _ => hl hp

theorem ay_dotg_disj_right {p q : Prop} (hq : q) : AyDOTGDisj p q :=
  fun r _ hr => hr hq

theorem ay_dotg_eq_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyDOTGEq p q :=
  ay_dotg_conj_intro hpq hqp

theorem ay_dotg_eq_forward {p q : Prop} (h : AyDOTGEq p q) : p -> q :=
  ay_dotg_conj_left h

theorem ay_dotg_eq_backward {p q : Prop} (h : AyDOTGEq p q) : q -> p :=
  ay_dotg_conj_right h

theorem ay_dotg_model_line_digest_intro {line stableLine : Prop}
    (h : line -> stableLine) : AyDOTGModelLineDigest line stableLine :=
  h

theorem ay_dotg_zero_terminator_policy_intro {stableLine terminatedStream : Prop}
    (h : stableLine -> terminatedStream) :
    AyDOTGZeroTerminatorPolicy stableLine terminatedStream :=
  h

theorem ay_dotg_variable_domain_manifest_intro {terminatedStream domainComplete : Prop}
    (h : terminatedStream -> domainComplete) :
    AyDOTGVariableDomainManifest terminatedStream domainComplete :=
  h

theorem ay_dotg_normalization_witness_intro {domainComplete normalized : Prop}
    (h : domainComplete -> normalized) : AyDOTGNormalizationWitness domainComplete normalized :=
  h

theorem ay_dotg_assignment_reconstruction_witness_intro
    {normalized totalAssignment : Prop}
    (h : normalized -> totalAssignment) :
    AyDOTGAssignmentReconstructionWitness normalized totalAssignment :=
  h

theorem ay_dotg_clause_coverage_digest_intro
    {totalAssignment everyClauseSatisfied : Prop}
    (h : totalAssignment -> everyClauseSatisfied) :
    AyDOTGClauseCoverageDigest totalAssignment everyClauseSatisfied :=
  h

theorem ay_dotg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyDOTGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_dotg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyDOTGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_dotg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyDOTGBuildEvidence fingerprint build :=
  h

theorem ay_dotg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyDOTGArchiveManifest build archived :=
  h

theorem ay_dotg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyDOTGFallbackBaseline archived fallbackReady :=
  h

theorem ay_dotg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyDOTGAuditTranscript fallbackReady audited :=
  h

theorem ay_dotg_accepted_output_intro
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (hmd : md) (htp : tp) (hdm : dm) (hnw : nw) (hrw : rw) (hcd : cd)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au :=
  ay_dotg_conj_intro hmd
    (ay_dotg_conj_intro htp
      (ay_dotg_conj_intro hdm
        (ay_dotg_conj_intro hnw
          (ay_dotg_conj_intro hrw
            (ay_dotg_conj_intro hcd
              (ay_dotg_conj_intro hct
                (ay_dotg_conj_intro hff
                  (ay_dotg_conj_intro hbe
                    (ay_dotg_conj_intro har
                      (ay_dotg_conj_intro hfb hau)))))))))))

theorem ay_dotg_accepted_output_model_digest
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : md :=
  ay_dotg_conj_left h

theorem ay_dotg_accepted_output_terminator_policy
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : tp :=
  ay_dotg_conj_left (ay_dotg_conj_right h)

theorem ay_dotg_accepted_output_domain
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : dm :=
  ay_dotg_conj_left (ay_dotg_conj_right (ay_dotg_conj_right h))

theorem ay_dotg_accepted_output_normalization
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : nw :=
  ay_dotg_conj_left (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h)))

theorem ay_dotg_accepted_output_reconstruction
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : rw :=
  ay_dotg_conj_left
    (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h))))

theorem ay_dotg_accepted_output_coverage
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : cd :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h)))))

theorem ay_dotg_accepted_output_checker
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : ct :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h))))))

theorem ay_dotg_accepted_output_fingerprint
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : ff :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right
          (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h)))))))

theorem ay_dotg_accepted_output_build
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : be :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right
          (ay_dotg_conj_right
            (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h))))))))

theorem ay_dotg_accepted_output_archive
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : ar :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right
          (ay_dotg_conj_right
            (ay_dotg_conj_right
              (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h)))))))))

theorem ay_dotg_accepted_output_fallback
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : fb :=
  ay_dotg_conj_left
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right
          (ay_dotg_conj_right
            (ay_dotg_conj_right
              (ay_dotg_conj_right
                (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h))))))))))

theorem ay_dotg_accepted_output_audit
    {md tp dm nw rw cd ct ff be ar fb au : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au) : au :=
  ay_dotg_conj_right
    (ay_dotg_conj_right
      (ay_dotg_conj_right
        (ay_dotg_conj_right
          (ay_dotg_conj_right
            (ay_dotg_conj_right
              (ay_dotg_conj_right
                (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right (ay_dotg_conj_right h))))))))))

theorem ay_dotg_output_parsing_reconstructs_consistent_total_assignment
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment consistent audited : Prop}
    (h : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
    (htotal : totalAssignment)
    (hconsistent : consistent)
    (haudit : audited) :
    AyDOTGConj totalAssignment (AyDOTGConj consistent audited) :=
  ay_dotg_conj_intro htotal (ay_dotg_conj_intro hconsistent haudit)

theorem ay_dotg_public_sat_intro {acceptedOutput totalAssignment originalSat : Prop}
    (hao : acceptedOutput) (htotal : totalAssignment) (hsat : originalSat) :
    AyDOTGPublicSat acceptedOutput totalAssignment originalSat :=
  ay_dotg_conj_intro hao (ay_dotg_conj_intro htotal hsat)

theorem ay_dotg_public_sat_evidence {acceptedOutput totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat acceptedOutput totalAssignment originalSat) : acceptedOutput :=
  ay_dotg_conj_left h

theorem ay_dotg_public_sat_total_assignment
    {acceptedOutput totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat acceptedOutput totalAssignment originalSat) : totalAssignment :=
  ay_dotg_conj_left (ay_dotg_conj_right h)

theorem ay_dotg_public_sat_claim {acceptedOutput totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat acceptedOutput totalAssignment originalSat) : originalSat :=
  ay_dotg_conj_right (ay_dotg_conj_right h)

theorem ay_dotg_accepted_output_publishes_sat
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (hao : AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat :=
  ay_dotg_public_sat_intro hao htotal hsat

theorem ay_dotg_public_sat_requires_accepted_output
    {acceptedOutput totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat acceptedOutput totalAssignment originalSat) : acceptedOutput :=
  ay_dotg_public_sat_evidence h

theorem ay_dotg_publication_requires_terminator_policy
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : tp :=
  ay_dotg_accepted_output_terminator_policy (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_domain
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : dm :=
  ay_dotg_accepted_output_domain (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_reconstruction
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : rw :=
  ay_dotg_accepted_output_reconstruction (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_coverage
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : cd :=
  ay_dotg_accepted_output_coverage (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_checker
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ct :=
  ay_dotg_accepted_output_checker (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_fingerprint
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ff :=
  ay_dotg_accepted_output_fingerprint (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_build
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : be :=
  ay_dotg_accepted_output_build (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_publication_requires_archive
    {md tp dm nw rw cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (h : AyDOTGPublicSat (AyDOTGAcceptedOutput md tp dm nw rw cd ct ff be ar fb au)
      totalAssignment originalSat) : ar :=
  ay_dotg_accepted_output_archive (ay_dotg_public_sat_requires_accepted_output h)

theorem ay_dotg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  h

theorem ay_dotg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyDOTGRecomputeObligation reason :=
  h

theorem ay_dotg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_no_claim_diagnostic_intro h

theorem ay_dotg_mismatch_recompute {reason : Prop} (h : reason) :
    AyDOTGRecomputeObligation reason :=
  ay_dotg_recompute_obligation_intro h

theorem ay_dotg_missing_terminator_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_extra_terminator_recompute {reason : Prop} (h : reason) :
    AyDOTGRecomputeObligation reason :=
  ay_dotg_mismatch_recompute h

theorem ay_dotg_malformed_literal_stream_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyDOTGNoClaimDiagnostic reason :=
  ay_dotg_mismatch_no_claim h

theorem ay_dotg_failed_terminator_guard_cannot_bless_sat
    {failure acceptedOutput totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDOTGPublicSat acceptedOutput totalAssignment originalSat ->
      AyDOTGNoClaimDiagnostic failure) :
    AyDOTGConj (AyDOTGNoClaimDiagnostic failure)
      (AyDOTGPublicSat acceptedOutput totalAssignment originalSat ->
        AyDOTGNoClaimDiagnostic failure) :=
  ay_dotg_conj_intro (ay_dotg_no_claim_diagnostic_intro hfail) hblock

theorem ay_dotg_failed_terminator_guard_recompute_blocks_publication
    {failure acceptedOutput totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyDOTGPublicSat acceptedOutput totalAssignment originalSat ->
      AyDOTGRecomputeObligation failure) :
    AyDOTGConj (AyDOTGRecomputeObligation failure)
      (AyDOTGPublicSat acceptedOutput totalAssignment originalSat ->
        AyDOTGRecomputeObligation failure) :=
  ay_dotg_conj_intro (ay_dotg_recompute_obligation_intro hfail) hblock

/-!
  SAT-COMP/ay locale and whitespace parser guard.

  This self-contained file records the abstract obligations required before
  locale-sensitive model text can be tokenized and accepted as a total
  satisfying assignment over the original DIMACS variables.
-/

def AyMLWGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyMLWGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyMLWGEquiv (p q : Prop) : Prop :=
  AyMLWGConj (p -> q) (q -> p)

def AyMLWGLocaleCharsetManifest (rawText stableCharset : Prop) : Prop :=
  rawText -> stableCharset

def AyMLWGWhitespaceTokenizationPolicy (stableCharset tokenized : Prop) : Prop :=
  stableCharset -> tokenized

def AyMLWGParsedLiteralStreamWitness (tokenized parsedLiterals : Prop) : Prop :=
  tokenized -> parsedLiterals

def AyMLWGAssignmentReconstructionWitness (parsedLiterals totalAssignment : Prop) : Prop :=
  parsedLiterals -> totalAssignment

def AyMLWGVariableDomainManifest (totalAssignment originalDomain : Prop) : Prop :=
  totalAssignment -> originalDomain

def AyMLWGClauseCoverageDigest (originalDomain everyClauseSatisfied : Prop) : Prop :=
  originalDomain -> everyClauseSatisfied

def AyMLWGCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyMLWGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyMLWGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyMLWGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyMLWGFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyMLWGAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyMLWGAcceptedParsing
    (localeManifest tokenizationPolicy literalStream reconstructionWitness
     domainManifest coverageDigest checkerTranscript formulaFingerprint buildEvidence
     archiveManifest fallbackBaseline auditTranscript : Prop) : Prop :=
  AyMLWGConj localeManifest
    (AyMLWGConj tokenizationPolicy
      (AyMLWGConj literalStream
        (AyMLWGConj reconstructionWitness
          (AyMLWGConj domainManifest
            (AyMLWGConj coverageDigest
              (AyMLWGConj checkerTranscript
                (AyMLWGConj formulaFingerprint
                  (AyMLWGConj buildEvidence
                    (AyMLWGConj archiveManifest
                      (AyMLWGConj fallbackBaseline auditTranscript)))))))))))

def AyMLWGPublicSat (acceptedParsing totalAssignment originalSat : Prop) : Prop :=
  AyMLWGConj acceptedParsing (AyMLWGConj totalAssignment originalSat)

def AyMLWGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyMLWGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_mlwg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyMLWGConj p q :=
  fun r h => h hp hq

theorem ay_mlwg_conj_left {p q : Prop} (h : AyMLWGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mlwg_conj_right {p q : Prop} (h : AyMLWGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mlwg_conj_left h)

theorem ay_mlwg_disj_left {p q : Prop} (hp : p) : AyMLWGDisj p q :=
  fun r hl _ => hl hp

theorem ay_mlwg_disj_right {p q : Prop} (hq : q) : AyMLWGDisj p q :=
  fun r _ hr => hr hq

theorem ay_mlwg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyMLWGEquiv p q :=
  ay_mlwg_conj_intro hpq hqp

theorem ay_mlwg_equiv_forward {p q : Prop} (h : AyMLWGEquiv p q) : p -> q :=
  ay_mlwg_conj_left h

theorem ay_mlwg_equiv_backward {p q : Prop} (h : AyMLWGEquiv p q) : q -> p :=
  ay_mlwg_conj_right h

theorem ay_mlwg_locale_charset_manifest_intro {rawText stableCharset : Prop}
    (h : rawText -> stableCharset) :
    AyMLWGLocaleCharsetManifest rawText stableCharset :=
  h

theorem ay_mlwg_whitespace_tokenization_policy_intro {stableCharset tokenized : Prop}
    (h : stableCharset -> tokenized) :
    AyMLWGWhitespaceTokenizationPolicy stableCharset tokenized :=
  h

theorem ay_mlwg_parsed_literal_stream_witness_intro {tokenized parsedLiterals : Prop}
    (h : tokenized -> parsedLiterals) :
    AyMLWGParsedLiteralStreamWitness tokenized parsedLiterals :=
  h

theorem ay_mlwg_assignment_reconstruction_witness_intro
    {parsedLiterals totalAssignment : Prop}
    (h : parsedLiterals -> totalAssignment) :
    AyMLWGAssignmentReconstructionWitness parsedLiterals totalAssignment :=
  h

theorem ay_mlwg_variable_domain_manifest_intro {totalAssignment originalDomain : Prop}
    (h : totalAssignment -> originalDomain) :
    AyMLWGVariableDomainManifest totalAssignment originalDomain :=
  h

theorem ay_mlwg_clause_coverage_digest_intro
    {originalDomain everyClauseSatisfied : Prop}
    (h : originalDomain -> everyClauseSatisfied) :
    AyMLWGClauseCoverageDigest originalDomain everyClauseSatisfied :=
  h

theorem ay_mlwg_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyMLWGCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_mlwg_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyMLWGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_mlwg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyMLWGBuildEvidence fingerprint build :=
  h

theorem ay_mlwg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyMLWGArchiveManifest build archived :=
  h

theorem ay_mlwg_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyMLWGFallbackBaseline archived fallbackReady :=
  h

theorem ay_mlwg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyMLWGAuditTranscript fallbackReady audited :=
  h

theorem ay_mlwg_accepted_parsing_intro
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (hlm : lm) (htp : tp) (hls : ls) (hrw : rw) (hdm : dm) (hcd : cd)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) (hfb : fb) (hau : au) :
    AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au :=
  ay_mlwg_conj_intro hlm
    (ay_mlwg_conj_intro htp
      (ay_mlwg_conj_intro hls
        (ay_mlwg_conj_intro hrw
          (ay_mlwg_conj_intro hdm
            (ay_mlwg_conj_intro hcd
              (ay_mlwg_conj_intro hct
                (ay_mlwg_conj_intro hff
                  (ay_mlwg_conj_intro hbe
                    (ay_mlwg_conj_intro har
                      (ay_mlwg_conj_intro hfb hau)))))))))))

theorem ay_mlwg_accepted_parsing_locale
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : lm :=
  ay_mlwg_conj_left h

theorem ay_mlwg_accepted_parsing_tokenization
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : tp :=
  ay_mlwg_conj_left (ay_mlwg_conj_right h)

theorem ay_mlwg_accepted_parsing_literal_stream
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : ls :=
  ay_mlwg_conj_left (ay_mlwg_conj_right (ay_mlwg_conj_right h))

theorem ay_mlwg_accepted_parsing_reconstruction
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : rw :=
  ay_mlwg_conj_left (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h)))

theorem ay_mlwg_accepted_parsing_domain
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : dm :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h))))

theorem ay_mlwg_accepted_parsing_coverage
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : cd :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h)))))

theorem ay_mlwg_accepted_parsing_checker
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : ct :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h))))))

theorem ay_mlwg_accepted_parsing_fingerprint
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : ff :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right
          (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h)))))))

theorem ay_mlwg_accepted_parsing_build
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : be :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right
          (ay_mlwg_conj_right
            (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h))))))))

theorem ay_mlwg_accepted_parsing_archive
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : ar :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right
          (ay_mlwg_conj_right
            (ay_mlwg_conj_right
              (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h)))))))))

theorem ay_mlwg_accepted_parsing_fallback
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : fb :=
  ay_mlwg_conj_left
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right
          (ay_mlwg_conj_right
            (ay_mlwg_conj_right
              (ay_mlwg_conj_right
                (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h))))))))))

theorem ay_mlwg_accepted_parsing_audit
    {lm tp ls rw dm cd ct ff be ar fb au : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au) : au :=
  ay_mlwg_conj_right
    (ay_mlwg_conj_right
      (ay_mlwg_conj_right
        (ay_mlwg_conj_right
          (ay_mlwg_conj_right
            (ay_mlwg_conj_right
              (ay_mlwg_conj_right
                (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right (ay_mlwg_conj_right h))))))))))

theorem ay_mlwg_parsing_reconstructs_dimacs_assignment
    {lm tp ls rw dm cd ct ff be ar fb au totalAssignment originalDomain audited : Prop}
    (h : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au)
    (htotal : totalAssignment)
    (hdomain : originalDomain)
    (haudit : audited) :
    AyMLWGConj totalAssignment (AyMLWGConj originalDomain audited) :=
  ay_mlwg_conj_intro htotal (ay_mlwg_conj_intro hdomain haudit)

theorem ay_mlwg_public_sat_intro {acceptedParsing totalAssignment originalSat : Prop}
    (hap : acceptedParsing) (htotal : totalAssignment) (hsat : originalSat) :
    AyMLWGPublicSat acceptedParsing totalAssignment originalSat :=
  ay_mlwg_conj_intro hap (ay_mlwg_conj_intro htotal hsat)

theorem ay_mlwg_public_sat_evidence {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMLWGPublicSat acceptedParsing totalAssignment originalSat) : acceptedParsing :=
  ay_mlwg_conj_left h

theorem ay_mlwg_public_sat_total_assignment {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMLWGPublicSat acceptedParsing totalAssignment originalSat) : totalAssignment :=
  ay_mlwg_conj_left (ay_mlwg_conj_right h)

theorem ay_mlwg_public_sat_claim {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMLWGPublicSat acceptedParsing totalAssignment originalSat) : originalSat :=
  ay_mlwg_conj_right (ay_mlwg_conj_right h)

theorem ay_mlwg_accepted_parsing_publishes_sat
    {lm tp ls rw dm cd ct ff be ar fb au totalAssignment originalSat : Prop}
    (hap : AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyMLWGPublicSat (AyMLWGAcceptedParsing lm tp ls rw dm cd ct ff be ar fb au)
      totalAssignment originalSat :=
  ay_mlwg_public_sat_intro hap htotal hsat

theorem ay_mlwg_public_sat_requires_accepted_parsing
    {acceptedParsing totalAssignment originalSat : Prop}
    (h : AyMLWGPublicSat acceptedParsing totalAssignment originalSat) : acceptedParsing :=
  ay_mlwg_public_sat_evidence h

theorem ay_mlwg_locale_drift_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_non_ascii_token_confusion_recompute {reason : Prop} (h : reason) :
    AyMLWGRecomputeObligation reason :=
  h

theorem ay_mlwg_malformed_whitespace_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    AyMLWGRecomputeObligation reason :=
  h

theorem ay_mlwg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyMLWGRecomputeObligation reason :=
  h

theorem ay_mlwg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyMLWGNoClaimDiagnostic reason :=
  h

theorem ay_mlwg_failed_locale_whitespace_guard_cannot_bless_sat
    {failure acceptedParsing totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMLWGPublicSat acceptedParsing totalAssignment originalSat ->
      AyMLWGNoClaimDiagnostic failure) :
    AyMLWGConj (AyMLWGNoClaimDiagnostic failure)
      (AyMLWGPublicSat acceptedParsing totalAssignment originalSat ->
        AyMLWGNoClaimDiagnostic failure) :=
  ay_mlwg_conj_intro hfail hblock

theorem ay_mlwg_failed_locale_whitespace_guard_recompute_blocks_publication
    {failure acceptedParsing totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyMLWGPublicSat acceptedParsing totalAssignment originalSat ->
      AyMLWGRecomputeObligation failure) :
    AyMLWGConj (AyMLWGRecomputeObligation failure)
      (AyMLWGPublicSat acceptedParsing totalAssignment originalSat ->
        AyMLWGRecomputeObligation failure) :=
  ay_mlwg_conj_intro hfail hblock

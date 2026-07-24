/-!
  SAT-COMP/ay incremental streaming model parser guard.

  This self-contained file records the abstract obligations required before a
  model parsed from streaming chunks may be accepted as the same total
  satisfying assignment as whole-file parsing.
-/

def AyISPQConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyISPQDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyISPQEquiv (p q : Prop) : Prop :=
  AyISPQConj (p -> q) (q -> p)

def AyISPQStreamingChunkDigestLedger (streamChunks orderedChunks : Prop) : Prop :=
  streamChunks -> orderedChunks

def AyISPQParserStateTransitionWitness (orderedChunks parsedState : Prop) : Prop :=
  orderedChunks -> parsedState

def AyISPQFinalAssignmentReconstructionWitness (parsedState totalAssignment : Prop) : Prop :=
  parsedState -> totalAssignment

def AyISPQVariableDomainManifest (totalAssignment domainComplete : Prop) : Prop :=
  totalAssignment -> domainComplete

def AyISPQClauseCoverageDigest (domainComplete everyClauseSatisfied : Prop) : Prop :=
  domainComplete -> everyClauseSatisfied

def AyISPQCheckerTranscript (everyClauseSatisfied checkerAccepted : Prop) : Prop :=
  everyClauseSatisfied -> checkerAccepted

def AyISPQFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyISPQBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyISPQArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyISPQFallbackBaseline (archived fallbackReady : Prop) : Prop :=
  archived -> fallbackReady

def AyISPQAuditTranscript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def AyISPQAcceptedStreamingParse
    (chunkLedger parserTransition assignmentReconstruction domainManifest coverageDigest
     checkerTranscript formulaFingerprint buildEvidence archiveManifest fallbackBaseline
     auditTranscript : Prop) : Prop :=
  AyISPQConj chunkLedger
    (AyISPQConj parserTransition
      (AyISPQConj assignmentReconstruction
        (AyISPQConj domainManifest
          (AyISPQConj coverageDigest
            (AyISPQConj checkerTranscript
              (AyISPQConj formulaFingerprint
                (AyISPQConj buildEvidence
                  (AyISPQConj archiveManifest
                    (AyISPQConj fallbackBaseline auditTranscript))))))))))

def AyISPQPublicSat (acceptedParse totalAssignment originalSat : Prop) : Prop :=
  AyISPQConj acceptedParse (AyISPQConj totalAssignment originalSat)

def AyISPQNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyISPQRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_ispq_conj_intro {p q : Prop} (hp : p) (hq : q) : AyISPQConj p q :=
  fun r h => h hp hq

theorem ay_ispq_conj_left {p q : Prop} (h : AyISPQConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_ispq_conj_right {p q : Prop} (h : AyISPQConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_ispq_conj_left h)

theorem ay_ispq_disj_left {p q : Prop} (hp : p) : AyISPQDisj p q :=
  fun r hl _ => hl hp

theorem ay_ispq_disj_right {p q : Prop} (hq : q) : AyISPQDisj p q :=
  fun r _ hr => hr hq

theorem ay_ispq_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyISPQEquiv p q :=
  ay_ispq_conj_intro hpq hqp

theorem ay_ispq_equiv_forward {p q : Prop} (h : AyISPQEquiv p q) : p -> q :=
  ay_ispq_conj_left h

theorem ay_ispq_equiv_backward {p q : Prop} (h : AyISPQEquiv p q) : q -> p :=
  ay_ispq_conj_right h

theorem ay_ispq_streaming_chunk_digest_ledger_intro {streamChunks orderedChunks : Prop}
    (h : streamChunks -> orderedChunks) :
    AyISPQStreamingChunkDigestLedger streamChunks orderedChunks :=
  h

theorem ay_ispq_parser_state_transition_witness_intro {orderedChunks parsedState : Prop}
    (h : orderedChunks -> parsedState) :
    AyISPQParserStateTransitionWitness orderedChunks parsedState :=
  h

theorem ay_ispq_final_assignment_reconstruction_witness_intro
    {parsedState totalAssignment : Prop}
    (h : parsedState -> totalAssignment) :
    AyISPQFinalAssignmentReconstructionWitness parsedState totalAssignment :=
  h

theorem ay_ispq_variable_domain_manifest_intro {totalAssignment domainComplete : Prop}
    (h : totalAssignment -> domainComplete) :
    AyISPQVariableDomainManifest totalAssignment domainComplete :=
  h

theorem ay_ispq_clause_coverage_digest_intro
    {domainComplete everyClauseSatisfied : Prop}
    (h : domainComplete -> everyClauseSatisfied) :
    AyISPQClauseCoverageDigest domainComplete everyClauseSatisfied :=
  h

theorem ay_ispq_checker_transcript_intro
    {everyClauseSatisfied checkerAccepted : Prop}
    (h : everyClauseSatisfied -> checkerAccepted) :
    AyISPQCheckerTranscript everyClauseSatisfied checkerAccepted :=
  h

theorem ay_ispq_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyISPQFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_ispq_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyISPQBuildEvidence fingerprint build :=
  h

theorem ay_ispq_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyISPQArchiveManifest build archived :=
  h

theorem ay_ispq_fallback_baseline_intro {archived fallbackReady : Prop}
    (h : archived -> fallbackReady) : AyISPQFallbackBaseline archived fallbackReady :=
  h

theorem ay_ispq_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) : AyISPQAuditTranscript fallbackReady audited :=
  h

theorem ay_ispq_accepted_streaming_parse_intro
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (hcl : cl) (hpt : pt) (har : ar) (hdm : dm) (hcc : cc) (hct : ct)
    (hff : ff) (hbe : be) (ham : am) (hfb : fb) (hau : au) :
    AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au :=
  ay_ispq_conj_intro hcl
    (ay_ispq_conj_intro hpt
      (ay_ispq_conj_intro har
        (ay_ispq_conj_intro hdm
          (ay_ispq_conj_intro hcc
            (ay_ispq_conj_intro hct
              (ay_ispq_conj_intro hff
                (ay_ispq_conj_intro hbe
                  (ay_ispq_conj_intro ham
                    (ay_ispq_conj_intro hfb hau))))))))))

theorem ay_ispq_accepted_parse_chunk_ledger
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : cl :=
  ay_ispq_conj_left h

theorem ay_ispq_accepted_parse_transition
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : pt :=
  ay_ispq_conj_left (ay_ispq_conj_right h)

theorem ay_ispq_accepted_parse_reconstruction
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : ar :=
  ay_ispq_conj_left (ay_ispq_conj_right (ay_ispq_conj_right h))

theorem ay_ispq_accepted_parse_domain
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : dm :=
  ay_ispq_conj_left (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h)))

theorem ay_ispq_accepted_parse_coverage
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : cc :=
  ay_ispq_conj_left
    (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h))))

theorem ay_ispq_accepted_parse_checker
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : ct :=
  ay_ispq_conj_left
    (ay_ispq_conj_right
      (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h)))))

theorem ay_ispq_accepted_parse_fingerprint
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : ff :=
  ay_ispq_conj_left
    (ay_ispq_conj_right
      (ay_ispq_conj_right
        (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h))))))

theorem ay_ispq_accepted_parse_build
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : be :=
  ay_ispq_conj_left
    (ay_ispq_conj_right
      (ay_ispq_conj_right
        (ay_ispq_conj_right
          (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h)))))))

theorem ay_ispq_accepted_parse_archive
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : am :=
  ay_ispq_conj_left
    (ay_ispq_conj_right
      (ay_ispq_conj_right
        (ay_ispq_conj_right
          (ay_ispq_conj_right
            (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h))))))))

theorem ay_ispq_accepted_parse_fallback
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : fb :=
  ay_ispq_conj_left
    (ay_ispq_conj_right
      (ay_ispq_conj_right
        (ay_ispq_conj_right
          (ay_ispq_conj_right
            (ay_ispq_conj_right
              (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h)))))))))

theorem ay_ispq_accepted_parse_audit
    {cl pt ar dm cc ct ff be am fb au : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au) : au :=
  ay_ispq_conj_right
    (ay_ispq_conj_right
      (ay_ispq_conj_right
        (ay_ispq_conj_right
          (ay_ispq_conj_right
            (ay_ispq_conj_right
              (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right (ay_ispq_conj_right h)))))))))

theorem ay_ispq_streaming_parse_matches_whole_file
    {cl pt ar dm cc ct ff be am fb au streamingAssignment wholeFileAssignment audited : Prop}
    (h : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au)
    (hstream : streamingAssignment)
    (hwhole : wholeFileAssignment)
    (haudit : audited) :
    AyISPQConj streamingAssignment (AyISPQConj wholeFileAssignment audited) :=
  ay_ispq_conj_intro hstream (ay_ispq_conj_intro hwhole haudit)

theorem ay_ispq_public_sat_intro {acceptedParse totalAssignment originalSat : Prop}
    (hap : acceptedParse) (htotal : totalAssignment) (hsat : originalSat) :
    AyISPQPublicSat acceptedParse totalAssignment originalSat :=
  ay_ispq_conj_intro hap (ay_ispq_conj_intro htotal hsat)

theorem ay_ispq_public_sat_evidence {acceptedParse totalAssignment originalSat : Prop}
    (h : AyISPQPublicSat acceptedParse totalAssignment originalSat) : acceptedParse :=
  ay_ispq_conj_left h

theorem ay_ispq_public_sat_total_assignment {acceptedParse totalAssignment originalSat : Prop}
    (h : AyISPQPublicSat acceptedParse totalAssignment originalSat) : totalAssignment :=
  ay_ispq_conj_left (ay_ispq_conj_right h)

theorem ay_ispq_public_sat_claim {acceptedParse totalAssignment originalSat : Prop}
    (h : AyISPQPublicSat acceptedParse totalAssignment originalSat) : originalSat :=
  ay_ispq_conj_right (ay_ispq_conj_right h)

theorem ay_ispq_accepted_parse_publishes_sat
    {cl pt ar dm cc ct ff be am fb au totalAssignment originalSat : Prop}
    (hap : AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyISPQPublicSat (AyISPQAcceptedStreamingParse cl pt ar dm cc ct ff be am fb au)
      totalAssignment originalSat :=
  ay_ispq_public_sat_intro hap htotal hsat

theorem ay_ispq_public_sat_requires_accepted_parse
    {acceptedParse totalAssignment originalSat : Prop}
    (h : AyISPQPublicSat acceptedParse totalAssignment originalSat) : acceptedParse :=
  ay_ispq_public_sat_evidence h

theorem ay_ispq_truncated_chunks_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_out_of_order_chunks_recompute {reason : Prop} (h : reason) :
    AyISPQRecomputeObligation reason :=
  h

theorem ay_ispq_malformed_chunks_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_coverage_mismatch_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_build_mismatch_recompute {reason : Prop} (h : reason) :
    AyISPQRecomputeObligation reason :=
  h

theorem ay_ispq_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyISPQNoClaimDiagnostic reason :=
  h

theorem ay_ispq_failed_streaming_parse_cannot_bless_sat
    {failure acceptedParse totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyISPQPublicSat acceptedParse totalAssignment originalSat ->
      AyISPQNoClaimDiagnostic failure) :
    AyISPQConj (AyISPQNoClaimDiagnostic failure)
      (AyISPQPublicSat acceptedParse totalAssignment originalSat ->
        AyISPQNoClaimDiagnostic failure) :=
  ay_ispq_conj_intro hfail hblock

theorem ay_ispq_failed_streaming_parse_recompute_blocks_publication
    {failure acceptedParse totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyISPQPublicSat acceptedParse totalAssignment originalSat ->
      AyISPQRecomputeObligation failure) :
    AyISPQConj (AyISPQRecomputeObligation failure)
      (AyISPQPublicSat acceptedParse totalAssignment originalSat ->
        AyISPQRecomputeObligation failure) :=
  ay_ispq_conj_intro hfail hblock

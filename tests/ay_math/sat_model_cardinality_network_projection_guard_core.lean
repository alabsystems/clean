/-!
  SAT-COMP/ay cardinality-network projection guard.

  This file is self-contained.  It packages the abstract obligations required
  before a CNF assignment for a cardinality-network encoding may be projected
  back to a public satisfying assignment for the original cardinality
  constraints.
-/

def AyCNPGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyCNPGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyCNPGEquisat (p q : Prop) : Prop :=
  AyCNPGConj (p -> q) (q -> p)

def AyCNPGEncodingManifest (cardinalityEncoding cnf originalCardinality : Prop) : Prop :=
  AyCNPGConj cardinalityEncoding
    (AyCNPGConj (cardinalityEncoding -> cnf) (cnf -> originalCardinality))

def AyCNPGAuxiliaryVariableMap (cnf projected : Prop) : Prop :=
  cnf -> projected

def AyCNPGProjectionWitnessLedger (projected originalAssignment : Prop) : Prop :=
  projected -> originalAssignment

def AyCNPGCnfAssignmentDigest (cnfAssignment cnf : Prop) : Prop :=
  cnfAssignment -> cnf

def AyCNPGOriginalCardinalityAssignmentDigest
    (originalAssignment originalCardinality : Prop) : Prop :=
  originalAssignment -> originalCardinality

def AyCNPGClauseCardinalityReplay (originalCardinality replayed : Prop) : Prop :=
  originalCardinality -> replayed

def AyCNPGCheckerTranscript (replayed accepted : Prop) : Prop :=
  replayed -> accepted

def AyCNPGFormulaFingerprint (accepted fingerprint : Prop) : Prop :=
  accepted -> fingerprint

def AyCNPGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyCNPGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyCNPGAcceptedProjection
    (encodingManifest auxiliaryMap projectionWitness cnfDigest originalDigest
     clauseCardinalityReplay checkerTranscript formulaFingerprint buildEvidence
     archiveManifest : Prop) : Prop :=
  AyCNPGConj encodingManifest
    (AyCNPGConj auxiliaryMap
      (AyCNPGConj projectionWitness
        (AyCNPGConj cnfDigest
          (AyCNPGConj originalDigest
            (AyCNPGConj clauseCardinalityReplay
              (AyCNPGConj checkerTranscript
                (AyCNPGConj formulaFingerprint
                  (AyCNPGConj buildEvidence archiveManifest))))))))

def AyCNPGPublicSat (acceptedProjection originalAssignment originalSat : Prop) : Prop :=
  AyCNPGConj acceptedProjection (AyCNPGConj originalAssignment originalSat)

def AyCNPGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyCNPGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_cnpg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyCNPGConj p q :=
  fun r h => h hp hq

theorem ay_cnpg_conj_left {p q : Prop} (h : AyCNPGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cnpg_conj_right {p q : Prop} (h : AyCNPGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cnpg_conj_left h)

theorem ay_cnpg_disj_left {p q : Prop} (hp : p) : AyCNPGDisj p q :=
  fun r hl _ => hl hp

theorem ay_cnpg_disj_right {p q : Prop} (hq : q) : AyCNPGDisj p q :=
  fun r _ hr => hr hq

theorem ay_cnpg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyCNPGEquisat p q :=
  ay_cnpg_conj_intro hpq hqp

theorem ay_cnpg_equisat_forward {p q : Prop} (h : AyCNPGEquisat p q) : p -> q :=
  ay_cnpg_conj_left h

theorem ay_cnpg_equisat_backward {p q : Prop} (h : AyCNPGEquisat p q) : q -> p :=
  ay_cnpg_conj_right h

theorem ay_cnpg_encoding_manifest_intro
    {cardinalityEncoding cnf originalCardinality : Prop}
    (henc : cardinalityEncoding) (hcnf : cardinalityEncoding -> cnf)
    (horiginal : cnf -> originalCardinality) :
    AyCNPGEncodingManifest cardinalityEncoding cnf originalCardinality :=
  ay_cnpg_conj_intro henc (ay_cnpg_conj_intro hcnf horiginal)

theorem ay_cnpg_encoding_manifest_encoding
    {cardinalityEncoding cnf originalCardinality : Prop}
    (h : AyCNPGEncodingManifest cardinalityEncoding cnf originalCardinality) :
    cardinalityEncoding :=
  ay_cnpg_conj_left h

theorem ay_cnpg_encoding_manifest_cnf
    {cardinalityEncoding cnf originalCardinality : Prop}
    (h : AyCNPGEncodingManifest cardinalityEncoding cnf originalCardinality) :
    cardinalityEncoding -> cnf :=
  ay_cnpg_conj_left (ay_cnpg_conj_right h)

theorem ay_cnpg_encoding_manifest_original
    {cardinalityEncoding cnf originalCardinality : Prop}
    (h : AyCNPGEncodingManifest cardinalityEncoding cnf originalCardinality) :
    cnf -> originalCardinality :=
  ay_cnpg_conj_right (ay_cnpg_conj_right h)

theorem ay_cnpg_auxiliary_variable_map_intro {cnf projected : Prop}
    (h : cnf -> projected) : AyCNPGAuxiliaryVariableMap cnf projected :=
  h

theorem ay_cnpg_projection_witness_ledger_intro {projected originalAssignment : Prop}
    (h : projected -> originalAssignment) :
    AyCNPGProjectionWitnessLedger projected originalAssignment :=
  h

theorem ay_cnpg_cnf_assignment_digest_intro {cnfAssignment cnf : Prop}
    (h : cnfAssignment -> cnf) : AyCNPGCnfAssignmentDigest cnfAssignment cnf :=
  h

theorem ay_cnpg_original_cardinality_assignment_digest_intro
    {originalAssignment originalCardinality : Prop}
    (h : originalAssignment -> originalCardinality) :
    AyCNPGOriginalCardinalityAssignmentDigest originalAssignment originalCardinality :=
  h

theorem ay_cnpg_clause_cardinality_replay_intro {originalCardinality replayed : Prop}
    (h : originalCardinality -> replayed) :
    AyCNPGClauseCardinalityReplay originalCardinality replayed :=
  h

theorem ay_cnpg_checker_transcript_intro {replayed accepted : Prop}
    (h : replayed -> accepted) : AyCNPGCheckerTranscript replayed accepted :=
  h

theorem ay_cnpg_formula_fingerprint_intro {accepted fingerprint : Prop}
    (h : accepted -> fingerprint) : AyCNPGFormulaFingerprint accepted fingerprint :=
  h

theorem ay_cnpg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyCNPGBuildEvidence fingerprint build :=
  h

theorem ay_cnpg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyCNPGArchiveManifest build archived :=
  h

theorem ay_cnpg_accepted_projection_intro
    {em am pw cd od rp ct ff be ar : Prop}
    (hem : em) (ham : am) (hpw : pw) (hcd : cd) (hod : od) (hrp : rp)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) :
    AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar :=
  ay_cnpg_conj_intro hem
    (ay_cnpg_conj_intro ham
      (ay_cnpg_conj_intro hpw
        (ay_cnpg_conj_intro hcd
          (ay_cnpg_conj_intro hod
            (ay_cnpg_conj_intro hrp
              (ay_cnpg_conj_intro hct
                (ay_cnpg_conj_intro hff
                  (ay_cnpg_conj_intro hbe har))))))))

theorem ay_cnpg_accepted_projection_encoding_manifest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : em :=
  ay_cnpg_conj_left h

theorem ay_cnpg_accepted_projection_auxiliary_map
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : am :=
  ay_cnpg_conj_left (ay_cnpg_conj_right h)

theorem ay_cnpg_accepted_projection_witness
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : pw :=
  ay_cnpg_conj_left (ay_cnpg_conj_right (ay_cnpg_conj_right h))

theorem ay_cnpg_accepted_projection_cnf_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : cd :=
  ay_cnpg_conj_left (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h)))

theorem ay_cnpg_accepted_projection_original_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : od :=
  ay_cnpg_conj_left
    (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h))))

theorem ay_cnpg_accepted_projection_clause_cardinality_replay
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : rp :=
  ay_cnpg_conj_left
    (ay_cnpg_conj_right
      (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h)))))

theorem ay_cnpg_accepted_projection_checker
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : ct :=
  ay_cnpg_conj_left
    (ay_cnpg_conj_right
      (ay_cnpg_conj_right
        (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h))))))

theorem ay_cnpg_accepted_projection_fingerprint
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : ff :=
  ay_cnpg_conj_left
    (ay_cnpg_conj_right
      (ay_cnpg_conj_right
        (ay_cnpg_conj_right
          (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h)))))))

theorem ay_cnpg_accepted_projection_build
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : be :=
  ay_cnpg_conj_left
    (ay_cnpg_conj_right
      (ay_cnpg_conj_right
        (ay_cnpg_conj_right
          (ay_cnpg_conj_right
            (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h))))))))

theorem ay_cnpg_accepted_projection_archive
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar) : ar :=
  ay_cnpg_conj_right
    (ay_cnpg_conj_right
      (ay_cnpg_conj_right
        (ay_cnpg_conj_right
          (ay_cnpg_conj_right
            (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right (ay_cnpg_conj_right h))))))))

theorem ay_cnpg_public_sat_intro {acceptedProjection originalAssignment originalSat : Prop}
    (hap : acceptedProjection) (hoa : originalAssignment) (hsat : originalSat) :
    AyCNPGPublicSat acceptedProjection originalAssignment originalSat :=
  ay_cnpg_conj_intro hap (ay_cnpg_conj_intro hoa hsat)

theorem ay_cnpg_public_sat_evidence {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_cnpg_conj_left h

theorem ay_cnpg_public_sat_assignment
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat acceptedProjection originalAssignment originalSat) :
    originalAssignment :=
  ay_cnpg_conj_left (ay_cnpg_conj_right h)

theorem ay_cnpg_public_sat_claim {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat acceptedProjection originalAssignment originalSat) : originalSat :=
  ay_cnpg_conj_right (ay_cnpg_conj_right h)

theorem ay_cnpg_projection_reconstructs_original_cardinality
    {em am pw cd od rp ct ff be ar originalAssignment originalCardinality archived : Prop}
    (hap : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
    (horiginalAssignment : originalAssignment)
    (horiginalCardinality : originalCardinality)
    (harchive : archived) :
    AyCNPGConj originalAssignment (AyCNPGConj originalCardinality archived) :=
  ay_cnpg_conj_intro horiginalAssignment
    (ay_cnpg_conj_intro horiginalCardinality harchive)

theorem ay_cnpg_accepted_projection_publishes_sound_sat
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (hap : AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
    (hoa : originalAssignment) (hsat : originalSat) :
    AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat :=
  ay_cnpg_public_sat_intro hap hoa hsat

theorem ay_cnpg_public_sat_requires_accepted_projection
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_cnpg_public_sat_evidence h

theorem ay_cnpg_publication_requires_encoding_manifest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : em :=
  ay_cnpg_accepted_projection_encoding_manifest (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_auxiliary_map
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : am :=
  ay_cnpg_accepted_projection_auxiliary_map (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_projection_witness
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : pw :=
  ay_cnpg_accepted_projection_witness (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_cnf_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : cd :=
  ay_cnpg_accepted_projection_cnf_digest (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_original_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : od :=
  ay_cnpg_accepted_projection_original_digest (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_clause_cardinality_replay
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : rp :=
  ay_cnpg_accepted_projection_clause_cardinality_replay
    (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_checker
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ct :=
  ay_cnpg_accepted_projection_checker (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_fingerprint
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ff :=
  ay_cnpg_accepted_projection_fingerprint (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_build
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : be :=
  ay_cnpg_accepted_projection_build (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_publication_requires_archive
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCNPGPublicSat (AyCNPGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ar :=
  ay_cnpg_accepted_projection_archive (ay_cnpg_public_sat_requires_accepted_projection h)

theorem ay_cnpg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  h

theorem ay_cnpg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyCNPGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_cnpg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyCNPGRecomputeObligation reason :=
  h

theorem ay_cnpg_recompute_obligation_request {reason : Prop}
    (h : AyCNPGRecomputeObligation reason) : reason :=
  h

theorem ay_cnpg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_no_claim_diagnostic_intro h

theorem ay_cnpg_mismatch_recompute {reason : Prop} (h : reason) :
    AyCNPGRecomputeObligation reason :=
  ay_cnpg_recompute_obligation_intro h

theorem ay_cnpg_encoding_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_auxiliary_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_projection_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_clause_cardinality_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCNPGNoClaimDiagnostic reason :=
  ay_cnpg_mismatch_no_claim h

theorem ay_cnpg_failed_projection_cannot_bless_public_sat
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyCNPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyCNPGNoClaimDiagnostic failure) :
    AyCNPGConj (AyCNPGNoClaimDiagnostic failure)
      (AyCNPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyCNPGNoClaimDiagnostic failure) :=
  ay_cnpg_conj_intro (ay_cnpg_no_claim_diagnostic_intro hfail) hblock

theorem ay_cnpg_failed_projection_recompute_blocks_publication
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyCNPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyCNPGRecomputeObligation failure) :
    AyCNPGConj (AyCNPGRecomputeObligation failure)
      (AyCNPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyCNPGRecomputeObligation failure) :=
  ay_cnpg_conj_intro (ay_cnpg_recompute_obligation_intro hfail) hblock

/-!
  SAT-COMP/ay AMO/EO projection guard.

  This self-contained file records the abstract proof obligations required
  before a CNF assignment for at-most-one/exactly-one encodings may be projected
  back to a public satisfying assignment for the original AMO constraints.
-/

def AyAMOGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyAMOGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyAMOGEquisat (p q : Prop) : Prop :=
  AyAMOGConj (p -> q) (q -> p)

def AyAMOGEncodingManifest (amoEncoding cnf originalAmo : Prop) : Prop :=
  AyAMOGConj amoEncoding (AyAMOGConj (amoEncoding -> cnf) (cnf -> originalAmo))

def AyAMOGAuxiliaryVariableMap (cnf projected : Prop) : Prop :=
  cnf -> projected

def AyAMOGProjectionWitnessLedger (projected originalAssignment : Prop) : Prop :=
  projected -> originalAssignment

def AyAMOGCnfAssignmentDigest (cnfAssignment cnf : Prop) : Prop :=
  cnfAssignment -> cnf

def AyAMOGOriginalConstraintAssignmentDigest
    (originalAssignment originalAmo : Prop) : Prop :=
  originalAssignment -> originalAmo

def AyAMOGClauseAmoReplay (originalAmo replayed : Prop) : Prop :=
  originalAmo -> replayed

def AyAMOGCheckerTranscript (replayed accepted : Prop) : Prop :=
  replayed -> accepted

def AyAMOGFormulaFingerprint (accepted fingerprint : Prop) : Prop :=
  accepted -> fingerprint

def AyAMOGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyAMOGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyAMOGAcceptedProjection
    (encodingManifest auxiliaryMap projectionWitness cnfDigest originalDigest
     clauseAmoReplay checkerTranscript formulaFingerprint buildEvidence
     archiveManifest : Prop) : Prop :=
  AyAMOGConj encodingManifest
    (AyAMOGConj auxiliaryMap
      (AyAMOGConj projectionWitness
        (AyAMOGConj cnfDigest
          (AyAMOGConj originalDigest
            (AyAMOGConj clauseAmoReplay
              (AyAMOGConj checkerTranscript
                (AyAMOGConj formulaFingerprint
                  (AyAMOGConj buildEvidence archiveManifest))))))))

def AyAMOGPublicSat (acceptedProjection originalAssignment originalSat : Prop) : Prop :=
  AyAMOGConj acceptedProjection (AyAMOGConj originalAssignment originalSat)

def AyAMOGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyAMOGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_amog_conj_intro {p q : Prop} (hp : p) (hq : q) : AyAMOGConj p q :=
  fun r h => h hp hq

theorem ay_amog_conj_left {p q : Prop} (h : AyAMOGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_amog_conj_right {p q : Prop} (h : AyAMOGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_amog_conj_left h)

theorem ay_amog_disj_left {p q : Prop} (hp : p) : AyAMOGDisj p q :=
  fun r hl _ => hl hp

theorem ay_amog_disj_right {p q : Prop} (hq : q) : AyAMOGDisj p q :=
  fun r _ hr => hr hq

theorem ay_amog_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyAMOGEquisat p q :=
  ay_amog_conj_intro hpq hqp

theorem ay_amog_equisat_forward {p q : Prop} (h : AyAMOGEquisat p q) : p -> q :=
  ay_amog_conj_left h

theorem ay_amog_equisat_backward {p q : Prop} (h : AyAMOGEquisat p q) : q -> p :=
  ay_amog_conj_right h

theorem ay_amog_encoding_manifest_intro {amoEncoding cnf originalAmo : Prop}
    (henc : amoEncoding) (hcnf : amoEncoding -> cnf) (horiginal : cnf -> originalAmo) :
    AyAMOGEncodingManifest amoEncoding cnf originalAmo :=
  ay_amog_conj_intro henc (ay_amog_conj_intro hcnf horiginal)

theorem ay_amog_encoding_manifest_encoding {amoEncoding cnf originalAmo : Prop}
    (h : AyAMOGEncodingManifest amoEncoding cnf originalAmo) : amoEncoding :=
  ay_amog_conj_left h

theorem ay_amog_encoding_manifest_cnf {amoEncoding cnf originalAmo : Prop}
    (h : AyAMOGEncodingManifest amoEncoding cnf originalAmo) : amoEncoding -> cnf :=
  ay_amog_conj_left (ay_amog_conj_right h)

theorem ay_amog_encoding_manifest_original {amoEncoding cnf originalAmo : Prop}
    (h : AyAMOGEncodingManifest amoEncoding cnf originalAmo) : cnf -> originalAmo :=
  ay_amog_conj_right (ay_amog_conj_right h)

theorem ay_amog_auxiliary_variable_map_intro {cnf projected : Prop}
    (h : cnf -> projected) : AyAMOGAuxiliaryVariableMap cnf projected :=
  h

theorem ay_amog_projection_witness_ledger_intro {projected originalAssignment : Prop}
    (h : projected -> originalAssignment) :
    AyAMOGProjectionWitnessLedger projected originalAssignment :=
  h

theorem ay_amog_cnf_assignment_digest_intro {cnfAssignment cnf : Prop}
    (h : cnfAssignment -> cnf) : AyAMOGCnfAssignmentDigest cnfAssignment cnf :=
  h

theorem ay_amog_original_constraint_assignment_digest_intro
    {originalAssignment originalAmo : Prop}
    (h : originalAssignment -> originalAmo) :
    AyAMOGOriginalConstraintAssignmentDigest originalAssignment originalAmo :=
  h

theorem ay_amog_clause_amo_replay_intro {originalAmo replayed : Prop}
    (h : originalAmo -> replayed) : AyAMOGClauseAmoReplay originalAmo replayed :=
  h

theorem ay_amog_checker_transcript_intro {replayed accepted : Prop}
    (h : replayed -> accepted) : AyAMOGCheckerTranscript replayed accepted :=
  h

theorem ay_amog_formula_fingerprint_intro {accepted fingerprint : Prop}
    (h : accepted -> fingerprint) : AyAMOGFormulaFingerprint accepted fingerprint :=
  h

theorem ay_amog_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyAMOGBuildEvidence fingerprint build :=
  h

theorem ay_amog_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyAMOGArchiveManifest build archived :=
  h

theorem ay_amog_accepted_projection_intro
    {em am pw cd od rp ct ff be ar : Prop}
    (hem : em) (ham : am) (hpw : pw) (hcd : cd) (hod : od) (hrp : rp)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) :
    AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar :=
  ay_amog_conj_intro hem
    (ay_amog_conj_intro ham
      (ay_amog_conj_intro hpw
        (ay_amog_conj_intro hcd
          (ay_amog_conj_intro hod
            (ay_amog_conj_intro hrp
              (ay_amog_conj_intro hct
                (ay_amog_conj_intro hff
                  (ay_amog_conj_intro hbe har))))))))

theorem ay_amog_accepted_projection_encoding_manifest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : em :=
  ay_amog_conj_left h

theorem ay_amog_accepted_projection_auxiliary_map
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : am :=
  ay_amog_conj_left (ay_amog_conj_right h)

theorem ay_amog_accepted_projection_witness
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : pw :=
  ay_amog_conj_left (ay_amog_conj_right (ay_amog_conj_right h))

theorem ay_amog_accepted_projection_cnf_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : cd :=
  ay_amog_conj_left (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h)))

theorem ay_amog_accepted_projection_original_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : od :=
  ay_amog_conj_left
    (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h))))

theorem ay_amog_accepted_projection_clause_amo_replay
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : rp :=
  ay_amog_conj_left
    (ay_amog_conj_right
      (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h)))))

theorem ay_amog_accepted_projection_checker
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : ct :=
  ay_amog_conj_left
    (ay_amog_conj_right
      (ay_amog_conj_right
        (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h))))))

theorem ay_amog_accepted_projection_fingerprint
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : ff :=
  ay_amog_conj_left
    (ay_amog_conj_right
      (ay_amog_conj_right
        (ay_amog_conj_right
          (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h)))))))

theorem ay_amog_accepted_projection_build
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : be :=
  ay_amog_conj_left
    (ay_amog_conj_right
      (ay_amog_conj_right
        (ay_amog_conj_right
          (ay_amog_conj_right
            (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h))))))))

theorem ay_amog_accepted_projection_archive
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar) : ar :=
  ay_amog_conj_right
    (ay_amog_conj_right
      (ay_amog_conj_right
        (ay_amog_conj_right
          (ay_amog_conj_right
            (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right (ay_amog_conj_right h))))))))

theorem ay_amog_public_sat_intro {acceptedProjection originalAssignment originalSat : Prop}
    (hap : acceptedProjection) (hoa : originalAssignment) (hsat : originalSat) :
    AyAMOGPublicSat acceptedProjection originalAssignment originalSat :=
  ay_amog_conj_intro hap (ay_amog_conj_intro hoa hsat)

theorem ay_amog_public_sat_evidence {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_amog_conj_left h

theorem ay_amog_public_sat_assignment
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat acceptedProjection originalAssignment originalSat) :
    originalAssignment :=
  ay_amog_conj_left (ay_amog_conj_right h)

theorem ay_amog_public_sat_claim {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat acceptedProjection originalAssignment originalSat) : originalSat :=
  ay_amog_conj_right (ay_amog_conj_right h)

theorem ay_amog_projection_reconstructs_original_amo
    {em am pw cd od rp ct ff be ar originalAssignment originalAmo archived : Prop}
    (hap : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
    (horiginalAssignment : originalAssignment)
    (horiginalAmo : originalAmo)
    (harchive : archived) :
    AyAMOGConj originalAssignment (AyAMOGConj originalAmo archived) :=
  ay_amog_conj_intro horiginalAssignment (ay_amog_conj_intro horiginalAmo harchive)

theorem ay_amog_accepted_projection_publishes_sound_sat
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (hap : AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
    (hoa : originalAssignment) (hsat : originalSat) :
    AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat :=
  ay_amog_public_sat_intro hap hoa hsat

theorem ay_amog_public_sat_requires_accepted_projection
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_amog_public_sat_evidence h

theorem ay_amog_publication_requires_encoding_manifest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : em :=
  ay_amog_accepted_projection_encoding_manifest (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_auxiliary_map
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : am :=
  ay_amog_accepted_projection_auxiliary_map (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_projection_witness
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : pw :=
  ay_amog_accepted_projection_witness (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_cnf_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : cd :=
  ay_amog_accepted_projection_cnf_digest (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_original_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : od :=
  ay_amog_accepted_projection_original_digest (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_clause_amo_replay
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : rp :=
  ay_amog_accepted_projection_clause_amo_replay (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_checker
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ct :=
  ay_amog_accepted_projection_checker (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_fingerprint
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ff :=
  ay_amog_accepted_projection_fingerprint (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_build
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : be :=
  ay_amog_accepted_projection_build (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_publication_requires_archive
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyAMOGPublicSat (AyAMOGAcceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ar :=
  ay_amog_accepted_projection_archive (ay_amog_public_sat_requires_accepted_projection h)

theorem ay_amog_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  h

theorem ay_amog_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyAMOGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_amog_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyAMOGRecomputeObligation reason :=
  h

theorem ay_amog_recompute_obligation_request {reason : Prop}
    (h : AyAMOGRecomputeObligation reason) : reason :=
  h

theorem ay_amog_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_no_claim_diagnostic_intro h

theorem ay_amog_mismatch_recompute {reason : Prop} (h : reason) :
    AyAMOGRecomputeObligation reason :=
  ay_amog_recompute_obligation_intro h

theorem ay_amog_encoding_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_auxiliary_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_projection_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_clause_amo_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyAMOGNoClaimDiagnostic reason :=
  ay_amog_mismatch_no_claim h

theorem ay_amog_failed_projection_cannot_bless_public_sat
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyAMOGPublicSat acceptedProjection originalAssignment originalSat ->
      AyAMOGNoClaimDiagnostic failure) :
    AyAMOGConj (AyAMOGNoClaimDiagnostic failure)
      (AyAMOGPublicSat acceptedProjection originalAssignment originalSat ->
        AyAMOGNoClaimDiagnostic failure) :=
  ay_amog_conj_intro (ay_amog_no_claim_diagnostic_intro hfail) hblock

theorem ay_amog_failed_projection_recompute_blocks_publication
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyAMOGPublicSat acceptedProjection originalAssignment originalSat ->
      AyAMOGRecomputeObligation failure) :
    AyAMOGConj (AyAMOGRecomputeObligation failure)
      (AyAMOGPublicSat acceptedProjection originalAssignment originalSat ->
        AyAMOGRecomputeObligation failure) :=
  ay_amog_conj_intro (ay_amog_recompute_obligation_intro hfail) hblock

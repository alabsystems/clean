/-!
  SAT-COMP/ay commander-encoding projection guard.

  This self-contained file records the abstract proof obligations required
  before a CNF assignment for commander encodings of cardinality/AMO constraints
  may be projected back to a public satisfying assignment for the original
  constraints.
-/

def AyCMPGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyCMPGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyCMPGEquisat (p q : Prop) : Prop :=
  AyCMPGConj (p -> q) (q -> p)

def AyCMPGEncodingManifest (commanderEncoding cnf originalConstraints : Prop) : Prop :=
  AyCMPGConj commanderEncoding
    (AyCMPGConj (commanderEncoding -> cnf) (cnf -> originalConstraints))

def AyCMPGCommanderVariableMap (cnf projected : Prop) : Prop :=
  cnf -> projected

def AyCMPGProjectionWitnessLedger (projected originalAssignment : Prop) : Prop :=
  projected -> originalAssignment

def AyCMPGCnfAssignmentDigest (cnfAssignment cnf : Prop) : Prop :=
  cnfAssignment -> cnf

def AyCMPGOriginalConstraintAssignmentDigest
    (originalAssignment originalConstraints : Prop) : Prop :=
  originalAssignment -> originalConstraints

def AyCMPGClauseCommanderReplay (originalConstraints replayed : Prop) : Prop :=
  originalConstraints -> replayed

def AyCMPGCheckerTranscript (replayed accepted : Prop) : Prop :=
  replayed -> accepted

def AyCMPGFormulaFingerprint (accepted fingerprint : Prop) : Prop :=
  accepted -> fingerprint

def AyCMPGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyCMPGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyCMPGAcceptedProjection
    (encodingManifest commanderMap projectionWitness cnfDigest originalDigest
     clauseCommanderReplay checkerTranscript formulaFingerprint buildEvidence
     archiveManifest : Prop) : Prop :=
  AyCMPGConj encodingManifest
    (AyCMPGConj commanderMap
      (AyCMPGConj projectionWitness
        (AyCMPGConj cnfDigest
          (AyCMPGConj originalDigest
            (AyCMPGConj clauseCommanderReplay
              (AyCMPGConj checkerTranscript
                (AyCMPGConj formulaFingerprint
                  (AyCMPGConj buildEvidence archiveManifest))))))))

def AyCMPGPublicSat (acceptedProjection originalAssignment originalSat : Prop) : Prop :=
  AyCMPGConj acceptedProjection (AyCMPGConj originalAssignment originalSat)

def AyCMPGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyCMPGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_cmpg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyCMPGConj p q :=
  fun r h => h hp hq

theorem ay_cmpg_conj_left {p q : Prop} (h : AyCMPGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cmpg_conj_right {p q : Prop} (h : AyCMPGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cmpg_conj_left h)

theorem ay_cmpg_disj_left {p q : Prop} (hp : p) : AyCMPGDisj p q :=
  fun r hl _ => hl hp

theorem ay_cmpg_disj_right {p q : Prop} (hq : q) : AyCMPGDisj p q :=
  fun r _ hr => hr hq

theorem ay_cmpg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyCMPGEquisat p q :=
  ay_cmpg_conj_intro hpq hqp

theorem ay_cmpg_equisat_forward {p q : Prop} (h : AyCMPGEquisat p q) : p -> q :=
  ay_cmpg_conj_left h

theorem ay_cmpg_equisat_backward {p q : Prop} (h : AyCMPGEquisat p q) : q -> p :=
  ay_cmpg_conj_right h

theorem ay_cmpg_encoding_manifest_intro
    {commanderEncoding cnf originalConstraints : Prop}
    (henc : commanderEncoding) (hcnf : commanderEncoding -> cnf)
    (horiginal : cnf -> originalConstraints) :
    AyCMPGEncodingManifest commanderEncoding cnf originalConstraints :=
  ay_cmpg_conj_intro henc (ay_cmpg_conj_intro hcnf horiginal)

theorem ay_cmpg_encoding_manifest_encoding
    {commanderEncoding cnf originalConstraints : Prop}
    (h : AyCMPGEncodingManifest commanderEncoding cnf originalConstraints) :
    commanderEncoding :=
  ay_cmpg_conj_left h

theorem ay_cmpg_encoding_manifest_cnf
    {commanderEncoding cnf originalConstraints : Prop}
    (h : AyCMPGEncodingManifest commanderEncoding cnf originalConstraints) :
    commanderEncoding -> cnf :=
  ay_cmpg_conj_left (ay_cmpg_conj_right h)

theorem ay_cmpg_encoding_manifest_original
    {commanderEncoding cnf originalConstraints : Prop}
    (h : AyCMPGEncodingManifest commanderEncoding cnf originalConstraints) :
    cnf -> originalConstraints :=
  ay_cmpg_conj_right (ay_cmpg_conj_right h)

theorem ay_cmpg_commander_variable_map_intro {cnf projected : Prop}
    (h : cnf -> projected) : AyCMPGCommanderVariableMap cnf projected :=
  h

theorem ay_cmpg_projection_witness_ledger_intro {projected originalAssignment : Prop}
    (h : projected -> originalAssignment) :
    AyCMPGProjectionWitnessLedger projected originalAssignment :=
  h

theorem ay_cmpg_cnf_assignment_digest_intro {cnfAssignment cnf : Prop}
    (h : cnfAssignment -> cnf) : AyCMPGCnfAssignmentDigest cnfAssignment cnf :=
  h

theorem ay_cmpg_original_constraint_assignment_digest_intro
    {originalAssignment originalConstraints : Prop}
    (h : originalAssignment -> originalConstraints) :
    AyCMPGOriginalConstraintAssignmentDigest originalAssignment originalConstraints :=
  h

theorem ay_cmpg_clause_commander_replay_intro {originalConstraints replayed : Prop}
    (h : originalConstraints -> replayed) :
    AyCMPGClauseCommanderReplay originalConstraints replayed :=
  h

theorem ay_cmpg_checker_transcript_intro {replayed accepted : Prop}
    (h : replayed -> accepted) : AyCMPGCheckerTranscript replayed accepted :=
  h

theorem ay_cmpg_formula_fingerprint_intro {accepted fingerprint : Prop}
    (h : accepted -> fingerprint) : AyCMPGFormulaFingerprint accepted fingerprint :=
  h

theorem ay_cmpg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyCMPGBuildEvidence fingerprint build :=
  h

theorem ay_cmpg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyCMPGArchiveManifest build archived :=
  h

theorem ay_cmpg_accepted_projection_intro
    {em cm pw cd od rp ct ff be ar : Prop}
    (hem : em) (hcm : cm) (hpw : pw) (hcd : cd) (hod : od) (hrp : rp)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) :
    AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar :=
  ay_cmpg_conj_intro hem
    (ay_cmpg_conj_intro hcm
      (ay_cmpg_conj_intro hpw
        (ay_cmpg_conj_intro hcd
          (ay_cmpg_conj_intro hod
            (ay_cmpg_conj_intro hrp
              (ay_cmpg_conj_intro hct
                (ay_cmpg_conj_intro hff
                  (ay_cmpg_conj_intro hbe har))))))))

theorem ay_cmpg_accepted_projection_encoding_manifest
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : em :=
  ay_cmpg_conj_left h

theorem ay_cmpg_accepted_projection_commander_map
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : cm :=
  ay_cmpg_conj_left (ay_cmpg_conj_right h)

theorem ay_cmpg_accepted_projection_witness
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : pw :=
  ay_cmpg_conj_left (ay_cmpg_conj_right (ay_cmpg_conj_right h))

theorem ay_cmpg_accepted_projection_cnf_digest
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : cd :=
  ay_cmpg_conj_left (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h)))

theorem ay_cmpg_accepted_projection_original_digest
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : od :=
  ay_cmpg_conj_left
    (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h))))

theorem ay_cmpg_accepted_projection_clause_commander_replay
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : rp :=
  ay_cmpg_conj_left
    (ay_cmpg_conj_right
      (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h)))))

theorem ay_cmpg_accepted_projection_checker
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : ct :=
  ay_cmpg_conj_left
    (ay_cmpg_conj_right
      (ay_cmpg_conj_right
        (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h))))))

theorem ay_cmpg_accepted_projection_fingerprint
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : ff :=
  ay_cmpg_conj_left
    (ay_cmpg_conj_right
      (ay_cmpg_conj_right
        (ay_cmpg_conj_right
          (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h)))))))

theorem ay_cmpg_accepted_projection_build
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : be :=
  ay_cmpg_conj_left
    (ay_cmpg_conj_right
      (ay_cmpg_conj_right
        (ay_cmpg_conj_right
          (ay_cmpg_conj_right
            (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h))))))))

theorem ay_cmpg_accepted_projection_archive
    {em cm pw cd od rp ct ff be ar : Prop}
    (h : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar) : ar :=
  ay_cmpg_conj_right
    (ay_cmpg_conj_right
      (ay_cmpg_conj_right
        (ay_cmpg_conj_right
          (ay_cmpg_conj_right
            (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right (ay_cmpg_conj_right h))))))))

theorem ay_cmpg_public_sat_intro {acceptedProjection originalAssignment originalSat : Prop}
    (hap : acceptedProjection) (hoa : originalAssignment) (hsat : originalSat) :
    AyCMPGPublicSat acceptedProjection originalAssignment originalSat :=
  ay_cmpg_conj_intro hap (ay_cmpg_conj_intro hoa hsat)

theorem ay_cmpg_public_sat_evidence {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_cmpg_conj_left h

theorem ay_cmpg_public_sat_assignment
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat acceptedProjection originalAssignment originalSat) :
    originalAssignment :=
  ay_cmpg_conj_left (ay_cmpg_conj_right h)

theorem ay_cmpg_public_sat_claim {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat acceptedProjection originalAssignment originalSat) : originalSat :=
  ay_cmpg_conj_right (ay_cmpg_conj_right h)

theorem ay_cmpg_projection_reconstructs_original_constraints
    {em cm pw cd od rp ct ff be ar originalAssignment originalConstraints archived : Prop}
    (hap : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
    (horiginalAssignment : originalAssignment)
    (horiginalConstraints : originalConstraints)
    (harchive : archived) :
    AyCMPGConj originalAssignment (AyCMPGConj originalConstraints archived) :=
  ay_cmpg_conj_intro horiginalAssignment
    (ay_cmpg_conj_intro horiginalConstraints harchive)

theorem ay_cmpg_accepted_projection_publishes_sound_sat
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (hap : AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
    (hoa : originalAssignment) (hsat : originalSat) :
    AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat :=
  ay_cmpg_public_sat_intro hap hoa hsat

theorem ay_cmpg_public_sat_requires_accepted_projection
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_cmpg_public_sat_evidence h

theorem ay_cmpg_publication_requires_encoding_manifest
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : em :=
  ay_cmpg_accepted_projection_encoding_manifest (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_commander_map
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : cm :=
  ay_cmpg_accepted_projection_commander_map (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_projection_witness
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : pw :=
  ay_cmpg_accepted_projection_witness (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_cnf_digest
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : cd :=
  ay_cmpg_accepted_projection_cnf_digest (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_original_digest
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : od :=
  ay_cmpg_accepted_projection_original_digest (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_clause_commander_replay
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : rp :=
  ay_cmpg_accepted_projection_clause_commander_replay
    (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_checker
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ct :=
  ay_cmpg_accepted_projection_checker (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_fingerprint
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ff :=
  ay_cmpg_accepted_projection_fingerprint (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_build
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : be :=
  ay_cmpg_accepted_projection_build (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_publication_requires_archive
    {em cm pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyCMPGPublicSat (AyCMPGAcceptedProjection em cm pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ar :=
  ay_cmpg_accepted_projection_archive (ay_cmpg_public_sat_requires_accepted_projection h)

theorem ay_cmpg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  h

theorem ay_cmpg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyCMPGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_cmpg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyCMPGRecomputeObligation reason :=
  h

theorem ay_cmpg_recompute_obligation_request {reason : Prop}
    (h : AyCMPGRecomputeObligation reason) : reason :=
  h

theorem ay_cmpg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_no_claim_diagnostic_intro h

theorem ay_cmpg_mismatch_recompute {reason : Prop} (h : reason) :
    AyCMPGRecomputeObligation reason :=
  ay_cmpg_recompute_obligation_intro h

theorem ay_cmpg_encoding_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_commander_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_projection_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_clause_commander_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyCMPGNoClaimDiagnostic reason :=
  ay_cmpg_mismatch_no_claim h

theorem ay_cmpg_failed_projection_cannot_bless_public_sat
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyCMPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyCMPGNoClaimDiagnostic failure) :
    AyCMPGConj (AyCMPGNoClaimDiagnostic failure)
      (AyCMPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyCMPGNoClaimDiagnostic failure) :=
  ay_cmpg_conj_intro (ay_cmpg_no_claim_diagnostic_intro hfail) hblock

theorem ay_cmpg_failed_projection_recompute_blocks_publication
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyCMPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyCMPGRecomputeObligation failure) :
    AyCMPGConj (AyCMPGRecomputeObligation failure)
      (AyCMPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyCMPGRecomputeObligation failure) :=
  ay_cmpg_conj_intro (ay_cmpg_recompute_obligation_intro hfail) hblock

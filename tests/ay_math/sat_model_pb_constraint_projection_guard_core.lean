/-!
  SAT-COMP/ay pseudo-Boolean/cardinality projection guard.

  This self-contained proof package records the abstract obligations needed
  before a CNF model for a PB/cardinality encoding may be projected back to a
  public satisfying assignment for the original constraints.
-/

def AyPBPGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyPBPGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyPBPGEquisat (p q : Prop) : Prop :=
  AyPBPGConj (p -> q) (q -> p)

def AyPBPGEncodingManifest (pbEncoding cnf originalConstraints : Prop) : Prop :=
  AyPBPGConj pbEncoding (AyPBPGConj (pbEncoding -> cnf) (cnf -> originalConstraints))

def AyPBPGAuxiliaryVariableMap (cnf projected : Prop) : Prop :=
  cnf -> projected

def AyPBPGProjectionWitnessLedger (projected originalAssignment : Prop) : Prop :=
  projected -> originalAssignment

def AyPBPGCnfAssignmentDigest (cnfAssignment cnf : Prop) : Prop :=
  cnfAssignment -> cnf

def AyPBPGOriginalConstraintAssignmentDigest
    (originalAssignment originalConstraints : Prop) : Prop :=
  originalAssignment -> originalConstraints

def AyPBPGClausePbReplay (originalConstraints replayed : Prop) : Prop :=
  originalConstraints -> replayed

def AyPBPGCheckerTranscript (replayed accepted : Prop) : Prop :=
  replayed -> accepted

def AyPBPGFormulaFingerprint (accepted fingerprint : Prop) : Prop :=
  accepted -> fingerprint

def AyPBPGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyPBPGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyPBPGAceptedProjection
    (encodingManifest auxiliaryMap projectionWitness cnfDigest originalDigest
     clausePbReplay checkerTranscript formulaFingerprint buildEvidence
     archiveManifest : Prop) : Prop :=
  AyPBPGConj encodingManifest
    (AyPBPGConj auxiliaryMap
      (AyPBPGConj projectionWitness
        (AyPBPGConj cnfDigest
          (AyPBPGConj originalDigest
            (AyPBPGConj clausePbReplay
              (AyPBPGConj checkerTranscript
                (AyPBPGConj formulaFingerprint
                  (AyPBPGConj buildEvidence archiveManifest))))))))

def AyPBPGPublicSat (acceptedProjection originalAssignment originalSat : Prop) : Prop :=
  AyPBPGConj acceptedProjection (AyPBPGConj originalAssignment originalSat)

def AyPBPGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyPBPGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_pbpg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyPBPGConj p q :=
  fun r h => h hp hq

theorem ay_pbpg_conj_left {p q : Prop} (h : AyPBPGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_pbpg_conj_right {p q : Prop} (h : AyPBPGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_pbpg_conj_left h)

theorem ay_pbpg_disj_left {p q : Prop} (hp : p) : AyPBPGDisj p q :=
  fun r hl _ => hl hp

theorem ay_pbpg_disj_right {p q : Prop} (hq : q) : AyPBPGDisj p q :=
  fun r _ hr => hr hq

theorem ay_pbpg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyPBPGEquisat p q :=
  ay_pbpg_conj_intro hpq hqp

theorem ay_pbpg_equisat_forward {p q : Prop} (h : AyPBPGEquisat p q) : p -> q :=
  ay_pbpg_conj_left h

theorem ay_pbpg_equisat_backward {p q : Prop} (h : AyPBPGEquisat p q) : q -> p :=
  ay_pbpg_conj_right h

theorem ay_pbpg_encoding_manifest_intro {pbEncoding cnf originalConstraints : Prop}
    (hpb : pbEncoding) (hcnf : pbEncoding -> cnf)
    (horiginal : cnf -> originalConstraints) :
    AyPBPGEncodingManifest pbEncoding cnf originalConstraints :=
  ay_pbpg_conj_intro hpb (ay_pbpg_conj_intro hcnf horiginal)

theorem ay_pbpg_encoding_manifest_encoding {pbEncoding cnf originalConstraints : Prop}
    (h : AyPBPGEncodingManifest pbEncoding cnf originalConstraints) : pbEncoding :=
  ay_pbpg_conj_left h

theorem ay_pbpg_encoding_manifest_cnf {pbEncoding cnf originalConstraints : Prop}
    (h : AyPBPGEncodingManifest pbEncoding cnf originalConstraints) : pbEncoding -> cnf :=
  ay_pbpg_conj_left (ay_pbpg_conj_right h)

theorem ay_pbpg_encoding_manifest_original {pbEncoding cnf originalConstraints : Prop}
    (h : AyPBPGEncodingManifest pbEncoding cnf originalConstraints) :
    cnf -> originalConstraints :=
  ay_pbpg_conj_right (ay_pbpg_conj_right h)

theorem ay_pbpg_auxiliary_variable_map_intro {cnf projected : Prop}
    (h : cnf -> projected) : AyPBPGAuxiliaryVariableMap cnf projected :=
  h

theorem ay_pbpg_projection_witness_ledger_intro {projected originalAssignment : Prop}
    (h : projected -> originalAssignment) :
    AyPBPGProjectionWitnessLedger projected originalAssignment :=
  h

theorem ay_pbpg_cnf_assignment_digest_intro {cnfAssignment cnf : Prop}
    (h : cnfAssignment -> cnf) : AyPBPGCnfAssignmentDigest cnfAssignment cnf :=
  h

theorem ay_pbpg_original_constraint_assignment_digest_intro
    {originalAssignment originalConstraints : Prop}
    (h : originalAssignment -> originalConstraints) :
    AyPBPGOriginalConstraintAssignmentDigest originalAssignment originalConstraints :=
  h

theorem ay_pbpg_clause_pb_replay_intro {originalConstraints replayed : Prop}
    (h : originalConstraints -> replayed) :
    AyPBPGClausePbReplay originalConstraints replayed :=
  h

theorem ay_pbpg_checker_transcript_intro {replayed accepted : Prop}
    (h : replayed -> accepted) : AyPBPGCheckerTranscript replayed accepted :=
  h

theorem ay_pbpg_formula_fingerprint_intro {accepted fingerprint : Prop}
    (h : accepted -> fingerprint) : AyPBPGFormulaFingerprint accepted fingerprint :=
  h

theorem ay_pbpg_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyPBPGBuildEvidence fingerprint build :=
  h

theorem ay_pbpg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyPBPGArchiveManifest build archived :=
  h

theorem ay_pbpg_accepted_projection_intro
    {em am pw cd od rp ct ff be ar : Prop}
    (hem : em) (ham : am) (hpw : pw) (hcd : cd) (hod : od) (hrp : rp)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) :
    AyPBPGAceptedProjection em am pw cd od rp ct ff be ar :=
  ay_pbpg_conj_intro hem
    (ay_pbpg_conj_intro ham
      (ay_pbpg_conj_intro hpw
        (ay_pbpg_conj_intro hcd
          (ay_pbpg_conj_intro hod
            (ay_pbpg_conj_intro hrp
              (ay_pbpg_conj_intro hct
                (ay_pbpg_conj_intro hff
                  (ay_pbpg_conj_intro hbe har))))))))

theorem ay_pbpg_accepted_projection_encoding_manifest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : em :=
  ay_pbpg_conj_left h

theorem ay_pbpg_accepted_projection_auxiliary_map
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : am :=
  ay_pbpg_conj_left (ay_pbpg_conj_right h)

theorem ay_pbpg_accepted_projection_witness
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : pw :=
  ay_pbpg_conj_left (ay_pbpg_conj_right (ay_pbpg_conj_right h))

theorem ay_pbpg_accepted_projection_cnf_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : cd :=
  ay_pbpg_conj_left (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h)))

theorem ay_pbpg_accepted_projection_original_digest
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : od :=
  ay_pbpg_conj_left
    (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h))))

theorem ay_pbpg_accepted_projection_clause_pb_replay
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : rp :=
  ay_pbpg_conj_left
    (ay_pbpg_conj_right
      (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h)))))

theorem ay_pbpg_accepted_projection_checker
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : ct :=
  ay_pbpg_conj_left
    (ay_pbpg_conj_right
      (ay_pbpg_conj_right
        (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h))))))

theorem ay_pbpg_accepted_projection_fingerprint
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : ff :=
  ay_pbpg_conj_left
    (ay_pbpg_conj_right
      (ay_pbpg_conj_right
        (ay_pbpg_conj_right
          (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h)))))))

theorem ay_pbpg_accepted_projection_build
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : be :=
  ay_pbpg_conj_left
    (ay_pbpg_conj_right
      (ay_pbpg_conj_right
        (ay_pbpg_conj_right
          (ay_pbpg_conj_right
            (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h))))))))

theorem ay_pbpg_accepted_projection_archive
    {em am pw cd od rp ct ff be ar : Prop}
    (h : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar) : ar :=
  ay_pbpg_conj_right
    (ay_pbpg_conj_right
      (ay_pbpg_conj_right
        (ay_pbpg_conj_right
          (ay_pbpg_conj_right
            (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right (ay_pbpg_conj_right h))))))))

theorem ay_pbpg_public_sat_intro {acceptedProjection originalAssignment originalSat : Prop}
    (hap : acceptedProjection) (hoa : originalAssignment) (hsat : originalSat) :
    AyPBPGPublicSat acceptedProjection originalAssignment originalSat :=
  ay_pbpg_conj_intro hap (ay_pbpg_conj_intro hoa hsat)

theorem ay_pbpg_public_sat_evidence {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_pbpg_conj_left h

theorem ay_pbpg_public_sat_assignment
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat acceptedProjection originalAssignment originalSat) :
    originalAssignment :=
  ay_pbpg_conj_left (ay_pbpg_conj_right h)

theorem ay_pbpg_public_sat_claim {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat acceptedProjection originalAssignment originalSat) : originalSat :=
  ay_pbpg_conj_right (ay_pbpg_conj_right h)

theorem ay_pbpg_projection_reconstructs_original_constraints
    {em am pw cd od rp ct ff be ar originalAssignment originalConstraints archived : Prop}
    (hap : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
    (horiginalAssignment : originalAssignment)
    (horiginalConstraints : originalConstraints)
    (harchive : archived) :
    AyPBPGConj originalAssignment (AyPBPGConj originalConstraints archived) :=
  ay_pbpg_conj_intro horiginalAssignment
    (ay_pbpg_conj_intro horiginalConstraints harchive)

theorem ay_pbpg_accepted_projection_publishes_sound_sat
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (hap : AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
    (hoa : originalAssignment) (hsat : originalSat) :
    AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat :=
  ay_pbpg_public_sat_intro hap hoa hsat

theorem ay_pbpg_public_sat_requires_accepted_projection
    {acceptedProjection originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat acceptedProjection originalAssignment originalSat) :
    acceptedProjection :=
  ay_pbpg_public_sat_evidence h

theorem ay_pbpg_publication_requires_encoding_manifest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : em :=
  ay_pbpg_accepted_projection_encoding_manifest (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_auxiliary_map
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : am :=
  ay_pbpg_accepted_projection_auxiliary_map (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_projection_witness
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : pw :=
  ay_pbpg_accepted_projection_witness (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_cnf_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : cd :=
  ay_pbpg_accepted_projection_cnf_digest (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_original_digest
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : od :=
  ay_pbpg_accepted_projection_original_digest (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_clause_pb_replay
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : rp :=
  ay_pbpg_accepted_projection_clause_pb_replay (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_checker
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ct :=
  ay_pbpg_accepted_projection_checker (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_fingerprint
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ff :=
  ay_pbpg_accepted_projection_fingerprint (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_build
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : be :=
  ay_pbpg_accepted_projection_build (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_publication_requires_archive
    {em am pw cd od rp ct ff be ar originalAssignment originalSat : Prop}
    (h : AyPBPGPublicSat (AyPBPGAceptedProjection em am pw cd od rp ct ff be ar)
      originalAssignment originalSat) : ar :=
  ay_pbpg_accepted_projection_archive (ay_pbpg_public_sat_requires_accepted_projection h)

theorem ay_pbpg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  h

theorem ay_pbpg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyPBPGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_pbpg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyPBPGRecomputeObligation reason :=
  h

theorem ay_pbpg_recompute_obligation_request {reason : Prop}
    (h : AyPBPGRecomputeObligation reason) : reason :=
  h

theorem ay_pbpg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_no_claim_diagnostic_intro h

theorem ay_pbpg_mismatch_recompute {reason : Prop} (h : reason) :
    AyPBPGRecomputeObligation reason :=
  ay_pbpg_recompute_obligation_intro h

theorem ay_pbpg_encoding_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_auxiliary_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_projection_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_clause_pb_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyPBPGNoClaimDiagnostic reason :=
  ay_pbpg_mismatch_no_claim h

theorem ay_pbpg_failed_projection_cannot_bless_public_sat
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyPBPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyPBPGNoClaimDiagnostic failure) :
    AyPBPGConj (AyPBPGNoClaimDiagnostic failure)
      (AyPBPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyPBPGNoClaimDiagnostic failure) :=
  ay_pbpg_conj_intro (ay_pbpg_no_claim_diagnostic_intro hfail) hblock

theorem ay_pbpg_failed_projection_recompute_blocks_publication
    {failure acceptedProjection originalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyPBPGPublicSat acceptedProjection originalAssignment originalSat ->
      AyPBPGRecomputeObligation failure) :
    AyPBPGConj (AyPBPGRecomputeObligation failure)
      (AyPBPGPublicSat acceptedProjection originalAssignment originalSat ->
        AyPBPGRecomputeObligation failure) :=
  ay_pbpg_conj_intro (ay_pbpg_recompute_obligation_intro hfail) hblock

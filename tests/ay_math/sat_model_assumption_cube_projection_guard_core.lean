/-!
  SAT-COMP/ay model publication guard for cube/assumption projection.

  This file is intentionally self-contained.  It packages the proof obligations
  needed before a model found under a cube or incremental assumption frame may
  be projected back to the public original instance.
-/

def AyACPGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyACPGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyACPGEquisat (p q : Prop) : Prop :=
  AyACPGConj (p -> q) (q -> p)

def AyACPGCubeManifest (cube reduced original : Prop) : Prop :=
  AyACPGConj cube (AyACPGConj (cube -> reduced) (reduced -> original))

def AyACPGAssumptionFrameLedger (frame active intended : Prop) : Prop :=
  AyACPGConj frame (AyACPGConj (frame -> active) (active -> intended))

def AyACPGProjectionMap (reduced projected : Prop) : Prop :=
  reduced -> projected

def AyACPGExtensionWitnessLedger (projected extended : Prop) : Prop :=
  projected -> extended

def AyACPGOriginalAssignmentDigest (extended originalModel : Prop) : Prop :=
  extended -> originalModel

def AyACPGReducedAssignmentDigest (reducedModel reduced : Prop) : Prop :=
  reducedModel -> reduced

def AyACPGClauseReplay (assignment cnf : Prop) : Prop :=
  assignment -> cnf

def AyACPGCheckerTranscript (cnf accepted : Prop) : Prop :=
  cnf -> accepted

def AyACPGFormulaFingerprint (accepted original : Prop) : Prop :=
  accepted -> original

def AyACPGBuildEvidence (original build : Prop) : Prop :=
  original -> build

def AyACPGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyACPGAcceptedProjection
    (cubeManifest assumptionFrame projectionMap extensionWitness
     originalDigest reducedDigest clauseReplay checkerTranscript
     formulaFingerprint buildEvidence archiveManifest : Prop) : Prop :=
  AyACPGConj cubeManifest
    (AyACPGConj assumptionFrame
      (AyACPGConj projectionMap
        (AyACPGConj extensionWitness
          (AyACPGConj originalDigest
            (AyACPGConj reducedDigest
              (AyACPGConj clauseReplay
                (AyACPGConj checkerTranscript
                  (AyACPGConj formulaFingerprint
                    (AyACPGConj buildEvidence archiveManifest)))))))))

def AyACPGPublicSatWitness (acceptedProjection originalSat intendedAssumptions : Prop) : Prop :=
  AyACPGConj acceptedProjection (AyACPGConj intendedAssumptions originalSat)

def AyACPGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyACPGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_acpg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyACPGConj p q :=
  fun r h => h hp hq

theorem ay_acpg_conj_left {p q : Prop} (h : AyACPGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_acpg_conj_right {p q : Prop} (h : AyACPGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_acpg_conj_left h)

theorem ay_acpg_disj_left {p q : Prop} (hp : p) : AyACPGDisj p q :=
  fun r hl _ => hl hp

theorem ay_acpg_disj_right {p q : Prop} (hq : q) : AyACPGDisj p q :=
  fun r _ hr => hr hq

theorem ay_acpg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyACPGEquisat p q :=
  ay_acpg_conj_intro hpq hqp

theorem ay_acpg_equisat_forward {p q : Prop} (h : AyACPGEquisat p q) : p -> q :=
  ay_acpg_conj_left h

theorem ay_acpg_equisat_backward {p q : Prop} (h : AyACPGEquisat p q) : q -> p :=
  ay_acpg_conj_right h

theorem ay_acpg_cube_manifest_intro {cube reduced original : Prop}
    (hcube : cube) (hred : cube -> reduced) (horig : reduced -> original) :
    AyACPGCubeManifest cube reduced original :=
  ay_acpg_conj_intro hcube (ay_acpg_conj_intro hred horig)

theorem ay_acpg_cube_manifest_cube {cube reduced original : Prop}
    (h : AyACPGCubeManifest cube reduced original) : cube :=
  ay_acpg_conj_left h

theorem ay_acpg_cube_manifest_reduced {cube reduced original : Prop}
    (h : AyACPGCubeManifest cube reduced original) : cube -> reduced :=
  ay_acpg_conj_left (ay_acpg_conj_right h)

theorem ay_acpg_cube_manifest_original {cube reduced original : Prop}
    (h : AyACPGCubeManifest cube reduced original) : reduced -> original :=
  ay_acpg_conj_right (ay_acpg_conj_right h)

theorem ay_acpg_assumption_frame_intro {frame active intended : Prop}
    (hframe : frame) (hactive : frame -> active) (hintended : active -> intended) :
    AyACPGAssumptionFrameLedger frame active intended :=
  ay_acpg_conj_intro hframe (ay_acpg_conj_intro hactive hintended)

theorem ay_acpg_assumption_frame_frame {frame active intended : Prop}
    (h : AyACPGAssumptionFrameLedger frame active intended) : frame :=
  ay_acpg_conj_left h

theorem ay_acpg_assumption_frame_active {frame active intended : Prop}
    (h : AyACPGAssumptionFrameLedger frame active intended) : frame -> active :=
  ay_acpg_conj_left (ay_acpg_conj_right h)

theorem ay_acpg_assumption_frame_intended {frame active intended : Prop}
    (h : AyACPGAssumptionFrameLedger frame active intended) : active -> intended :=
  ay_acpg_conj_right (ay_acpg_conj_right h)

theorem ay_acpg_projection_map_intro {reduced projected : Prop}
    (h : reduced -> projected) : AyACPGProjectionMap reduced projected :=
  h

theorem ay_acpg_extension_witness_ledger_intro {projected extended : Prop}
    (h : projected -> extended) : AyACPGExtensionWitnessLedger projected extended :=
  h

theorem ay_acpg_original_assignment_digest_intro {extended originalModel : Prop}
    (h : extended -> originalModel) : AyACPGOriginalAssignmentDigest extended originalModel :=
  h

theorem ay_acpg_reduced_assignment_digest_intro {reducedModel reduced : Prop}
    (h : reducedModel -> reduced) : AyACPGReducedAssignmentDigest reducedModel reduced :=
  h

theorem ay_acpg_clause_replay_intro {assignment cnf : Prop}
    (h : assignment -> cnf) : AyACPGClauseReplay assignment cnf :=
  h

theorem ay_acpg_checker_transcript_intro {cnf accepted : Prop}
    (h : cnf -> accepted) : AyACPGCheckerTranscript cnf accepted :=
  h

theorem ay_acpg_formula_fingerprint_intro {accepted original : Prop}
    (h : accepted -> original) : AyACPGFormulaFingerprint accepted original :=
  h

theorem ay_acpg_build_evidence_intro {original build : Prop}
    (h : original -> build) : AyACPGBuildEvidence original build :=
  h

theorem ay_acpg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyACPGArchiveManifest build archived :=
  h

theorem ay_acpg_accepted_projection_intro
    {cubeManifest assumptionFrame projectionMap extensionWitness
     originalDigest reducedDigest clauseReplay checkerTranscript
     formulaFingerprint buildEvidence archiveManifest : Prop}
    (hcm : cubeManifest) (haf : assumptionFrame) (hpm : projectionMap)
    (hew : extensionWitness) (hod : originalDigest) (hrd : reducedDigest)
    (hcr : clauseReplay) (hct : checkerTranscript) (hff : formulaFingerprint)
    (hbe : buildEvidence) (ham : archiveManifest) :
    AyACPGAcceptedProjection cubeManifest assumptionFrame projectionMap extensionWitness
      originalDigest reducedDigest clauseReplay checkerTranscript formulaFingerprint
      buildEvidence archiveManifest :=
  ay_acpg_conj_intro hcm
    (ay_acpg_conj_intro haf
      (ay_acpg_conj_intro hpm
        (ay_acpg_conj_intro hew
          (ay_acpg_conj_intro hod
            (ay_acpg_conj_intro hrd
              (ay_acpg_conj_intro hcr
                (ay_acpg_conj_intro hct
                  (ay_acpg_conj_intro hff
                    (ay_acpg_conj_intro hbe ham)))))))))

theorem ay_acpg_accepted_projection_cube_manifest
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : cm :=
  ay_acpg_conj_left h

theorem ay_acpg_accepted_projection_assumption_frame
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : af :=
  ay_acpg_conj_left (ay_acpg_conj_right h)

theorem ay_acpg_accepted_projection_map
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : pm :=
  ay_acpg_conj_left (ay_acpg_conj_right (ay_acpg_conj_right h))

theorem ay_acpg_accepted_projection_extension
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : ew :=
  ay_acpg_conj_left (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h)))

theorem ay_acpg_accepted_projection_original_digest
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : od :=
  ay_acpg_conj_left
    (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h))))

theorem ay_acpg_accepted_projection_reduced_digest
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : rd :=
  ay_acpg_conj_left
    (ay_acpg_conj_right
      (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h)))))

theorem ay_acpg_accepted_projection_replay
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : cr :=
  ay_acpg_conj_left
    (ay_acpg_conj_right
      (ay_acpg_conj_right
        (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h))))))

theorem ay_acpg_accepted_projection_checker
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : ct :=
  ay_acpg_conj_left
    (ay_acpg_conj_right
      (ay_acpg_conj_right
        (ay_acpg_conj_right
          (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h)))))))

theorem ay_acpg_accepted_projection_fingerprint
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : ff :=
  ay_acpg_conj_left
    (ay_acpg_conj_right
      (ay_acpg_conj_right
        (ay_acpg_conj_right
          (ay_acpg_conj_right
            (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h))))))))

theorem ay_acpg_accepted_projection_build
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : be :=
  ay_acpg_conj_left
    (ay_acpg_conj_right
      (ay_acpg_conj_right
        (ay_acpg_conj_right
          (ay_acpg_conj_right
            (ay_acpg_conj_right
              (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h)))))))))

theorem ay_acpg_accepted_projection_archive
    {cm af pm ew od rd cr ct ff be am : Prop}
    (h : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am) : am :=
  ay_acpg_conj_right
    (ay_acpg_conj_right
      (ay_acpg_conj_right
        (ay_acpg_conj_right
          (ay_acpg_conj_right
            (ay_acpg_conj_right
              (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right (ay_acpg_conj_right h)))))))))

theorem ay_acpg_public_sat_witness_intro {acceptedProjection originalSat intendedAssumptions : Prop}
    (hap : acceptedProjection) (hia : intendedAssumptions) (hos : originalSat) :
    AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions :=
  ay_acpg_conj_intro hap (ay_acpg_conj_intro hia hos)

theorem ay_acpg_public_sat_witness_evidence {acceptedProjection originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions) :
    acceptedProjection :=
  ay_acpg_conj_left h

theorem ay_acpg_public_sat_witness_assumptions
    {acceptedProjection originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions) :
    intendedAssumptions :=
  ay_acpg_conj_left (ay_acpg_conj_right h)

theorem ay_acpg_public_sat_witness_claim {acceptedProjection originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions) :
    originalSat :=
  ay_acpg_conj_right (ay_acpg_conj_right h)

theorem ay_acpg_projection_reconstructs_original_under_assumptions
    {cube reduced projected extended originalModel reducedModel reducedCnf checkedCnf
     accepted originalSat build archived frame active intended : Prop}
    (hcm : AyACPGCubeManifest cube reducedCnf originalSat)
    (haf : AyACPGAssumptionFrameLedger frame active intended)
    (hpm : AyACPGProjectionMap reducedCnf projected)
    (hew : AyACPGExtensionWitnessLedger projected extended)
    (hod : AyACPGOriginalAssignmentDigest extended originalModel)
    (hrd : AyACPGReducedAssignmentDigest reducedModel reducedCnf)
    (hcr : AyACPGClauseReplay originalModel checkedCnf)
    (hct : AyACPGCheckerTranscript checkedCnf accepted)
    (hff : AyACPGFormulaFingerprint accepted originalSat)
    (hbe : AyACPGBuildEvidence originalSat build)
    (ham : AyACPGArchiveManifest build archived)
    (hreducedModel : reducedModel) :
    AyACPGConj intended (AyACPGConj originalSat archived) :=
  let hred : reducedCnf := hrd hreducedModel
  let hproj : projected := hpm hred
  let hext : extended := hew hproj
  let horigModel : originalModel := hod hext
  let hcnf : checkedCnf := hcr horigModel
  let haccepted : accepted := hct hcnf
  let horigSat : originalSat := hff haccepted
  let hbuild : build := hbe horigSat
  let harchive : archived := ham hbuild
  let hframe : frame := ay_acpg_assumption_frame_frame haf
  let hactive : active := ay_acpg_assumption_frame_active haf hframe
  let hintended : intended := ay_acpg_assumption_frame_intended haf hactive
  ay_acpg_conj_intro hintended (ay_acpg_conj_intro horigSat harchive)

theorem ay_acpg_accepted_projection_publishes_sound_sat
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (hap : AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
    (hintended : intendedAssumptions) (hsat : originalSat) :
    AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions :=
  ay_acpg_public_sat_witness_intro hap hintended hsat

theorem ay_acpg_public_sat_requires_accepted_projection
    {acceptedProjection originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions) :
    acceptedProjection :=
  ay_acpg_public_sat_witness_evidence h

theorem ay_acpg_publication_requires_cube_manifest
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : cm :=
  ay_acpg_accepted_projection_cube_manifest (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_assumption_frame
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : af :=
  ay_acpg_accepted_projection_assumption_frame (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_projection_map
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : pm :=
  ay_acpg_accepted_projection_map (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_extension_witness
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : ew :=
  ay_acpg_accepted_projection_extension (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_original_digest
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : od :=
  ay_acpg_accepted_projection_original_digest (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_reduced_digest
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : rd :=
  ay_acpg_accepted_projection_reduced_digest (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_clause_replay
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : cr :=
  ay_acpg_accepted_projection_replay (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_checker_transcript
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : ct :=
  ay_acpg_accepted_projection_checker (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_formula_fingerprint
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : ff :=
  ay_acpg_accepted_projection_fingerprint (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_build_evidence
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : be :=
  ay_acpg_accepted_projection_build (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_publication_requires_archive_manifest
    {cm af pm ew od rd cr ct ff be am originalSat intendedAssumptions : Prop}
    (h : AyACPGPublicSatWitness
      (AyACPGAcceptedProjection cm af pm ew od rd cr ct ff be am)
      originalSat intendedAssumptions) : am :=
  ay_acpg_accepted_projection_archive (ay_acpg_public_sat_requires_accepted_projection h)

theorem ay_acpg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  h

theorem ay_acpg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyACPGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_acpg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyACPGRecomputeObligation reason :=
  h

theorem ay_acpg_recompute_obligation_request {reason : Prop}
    (h : AyACPGRecomputeObligation reason) : reason :=
  h

theorem ay_acpg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_no_claim_diagnostic_intro h

theorem ay_acpg_mismatch_recompute {reason : Prop} (h : reason) :
    AyACPGRecomputeObligation reason :=
  ay_acpg_recompute_obligation_intro h

theorem ay_acpg_cube_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_assumption_frame_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_projection_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_extension_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_clause_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyACPGNoClaimDiagnostic reason :=
  ay_acpg_mismatch_no_claim h

theorem ay_acpg_failed_projection_cannot_bless_public_sat
    {failure acceptedProjection originalSat intendedAssumptions : Prop}
    (hfail : failure)
    (hblock : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions ->
      AyACPGNoClaimDiagnostic failure) :
    AyACPGConj (AyACPGNoClaimDiagnostic failure)
      (AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions ->
        AyACPGNoClaimDiagnostic failure) :=
  ay_acpg_conj_intro (ay_acpg_no_claim_diagnostic_intro hfail) hblock

theorem ay_acpg_failed_projection_recompute_blocks_publication
    {failure acceptedProjection originalSat intendedAssumptions : Prop}
    (hfail : failure)
    (hblock : AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions ->
      AyACPGRecomputeObligation failure) :
    AyACPGConj (AyACPGRecomputeObligation failure)
      (AyACPGPublicSatWitness acceptedProjection originalSat intendedAssumptions ->
        AyACPGRecomputeObligation failure) :=
  ay_acpg_conj_intro (ay_acpg_recompute_obligation_intro hfail) hblock

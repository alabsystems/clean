/-!
  SAT-COMP/ay eliminated-XOR model extension guard.

  This self-contained package records the abstract proof obligations needed
  before a model produced after XOR/Gaussian preprocessing may be extended and
  published as a public SAT witness for the original formula.
-/

def AyXMEGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyXMEGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyXMEGEquisat (p q : Prop) : Prop :=
  AyXMEGConj (p -> q) (q -> p)

def AyXMEGXorEliminationManifest (xorSystem reduced original : Prop) : Prop :=
  AyXMEGConj xorSystem (AyXMEGConj (xorSystem -> reduced) (reduced -> original))

def AyXMEGAuxiliaryVariableMap (reduced projected : Prop) : Prop :=
  reduced -> projected

def AyXMEGExtensionWitnessLedger (projected total : Prop) : Prop :=
  projected -> total

def AyXMEGReducedAssignmentDigest (reducedAssignment reduced : Prop) : Prop :=
  reducedAssignment -> reduced

def AyXMEGOriginalAssignmentDigest (total originalAssignment : Prop) : Prop :=
  total -> originalAssignment

def AyXMEGClauseXorReplay (originalAssignment originalFormula : Prop) : Prop :=
  originalAssignment -> originalFormula

def AyXMEGCheckerTranscript (originalFormula accepted : Prop) : Prop :=
  originalFormula -> accepted

def AyXMEGFormulaFingerprint (accepted originalFingerprint : Prop) : Prop :=
  accepted -> originalFingerprint

def AyXMEGBuildEvidence (originalFingerprint build : Prop) : Prop :=
  originalFingerprint -> build

def AyXMEGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyXMEGAcceptedExtension
    (xorManifest auxiliaryMap extensionWitness reducedDigest originalDigest
     clauseXorReplay checkerTranscript formulaFingerprint buildEvidence
     archiveManifest : Prop) : Prop :=
  AyXMEGConj xorManifest
    (AyXMEGConj auxiliaryMap
      (AyXMEGConj extensionWitness
        (AyXMEGConj reducedDigest
          (AyXMEGConj originalDigest
            (AyXMEGConj clauseXorReplay
              (AyXMEGConj checkerTranscript
                (AyXMEGConj formulaFingerprint
                  (AyXMEGConj buildEvidence archiveManifest))))))))

def AyXMEGPublicSat (acceptedExtension totalAssignment originalSat : Prop) : Prop :=
  AyXMEGConj acceptedExtension (AyXMEGConj totalAssignment originalSat)

def AyXMEGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyXMEGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_xmeg_conj_intro {p q : Prop} (hp : p) (hq : q) : AyXMEGConj p q :=
  fun r h => h hp hq

theorem ay_xmeg_conj_left {p q : Prop} (h : AyXMEGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_xmeg_conj_right {p q : Prop} (h : AyXMEGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_xmeg_conj_left h)

theorem ay_xmeg_disj_left {p q : Prop} (hp : p) : AyXMEGDisj p q :=
  fun r hl _ => hl hp

theorem ay_xmeg_disj_right {p q : Prop} (hq : q) : AyXMEGDisj p q :=
  fun r _ hr => hr hq

theorem ay_xmeg_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyXMEGEquisat p q :=
  ay_xmeg_conj_intro hpq hqp

theorem ay_xmeg_equisat_forward {p q : Prop} (h : AyXMEGEquisat p q) : p -> q :=
  ay_xmeg_conj_left h

theorem ay_xmeg_equisat_backward {p q : Prop} (h : AyXMEGEquisat p q) : q -> p :=
  ay_xmeg_conj_right h

theorem ay_xmeg_xor_elimination_manifest_intro {xorSystem reduced original : Prop}
    (hxor : xorSystem) (hreduced : xorSystem -> reduced) (horiginal : reduced -> original) :
    AyXMEGXorEliminationManifest xorSystem reduced original :=
  ay_xmeg_conj_intro hxor (ay_xmeg_conj_intro hreduced horiginal)

theorem ay_xmeg_xor_elimination_manifest_system {xorSystem reduced original : Prop}
    (h : AyXMEGXorEliminationManifest xorSystem reduced original) : xorSystem :=
  ay_xmeg_conj_left h

theorem ay_xmeg_xor_elimination_manifest_reduced {xorSystem reduced original : Prop}
    (h : AyXMEGXorEliminationManifest xorSystem reduced original) : xorSystem -> reduced :=
  ay_xmeg_conj_left (ay_xmeg_conj_right h)

theorem ay_xmeg_xor_elimination_manifest_original {xorSystem reduced original : Prop}
    (h : AyXMEGXorEliminationManifest xorSystem reduced original) : reduced -> original :=
  ay_xmeg_conj_right (ay_xmeg_conj_right h)

theorem ay_xmeg_auxiliary_variable_map_intro {reduced projected : Prop}
    (h : reduced -> projected) : AyXMEGAuxiliaryVariableMap reduced projected :=
  h

theorem ay_xmeg_extension_witness_ledger_intro {projected total : Prop}
    (h : projected -> total) : AyXMEGExtensionWitnessLedger projected total :=
  h

theorem ay_xmeg_reduced_assignment_digest_intro {reducedAssignment reduced : Prop}
    (h : reducedAssignment -> reduced) :
    AyXMEGReducedAssignmentDigest reducedAssignment reduced :=
  h

theorem ay_xmeg_original_assignment_digest_intro {total originalAssignment : Prop}
    (h : total -> originalAssignment) :
    AyXMEGOriginalAssignmentDigest total originalAssignment :=
  h

theorem ay_xmeg_clause_xor_replay_intro {originalAssignment originalFormula : Prop}
    (h : originalAssignment -> originalFormula) :
    AyXMEGClauseXorReplay originalAssignment originalFormula :=
  h

theorem ay_xmeg_checker_transcript_intro {originalFormula accepted : Prop}
    (h : originalFormula -> accepted) : AyXMEGCheckerTranscript originalFormula accepted :=
  h

theorem ay_xmeg_formula_fingerprint_intro {accepted originalFingerprint : Prop}
    (h : accepted -> originalFingerprint) :
    AyXMEGFormulaFingerprint accepted originalFingerprint :=
  h

theorem ay_xmeg_build_evidence_intro {originalFingerprint build : Prop}
    (h : originalFingerprint -> build) : AyXMEGBuildEvidence originalFingerprint build :=
  h

theorem ay_xmeg_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyXMEGArchiveManifest build archived :=
  h

theorem ay_xmeg_accepted_extension_intro
    {xm am ew rd od rx ct ff be ar : Prop}
    (hxm : xm) (ham : am) (hew : ew) (hrd : rd) (hod : od) (hrx : rx)
    (hct : ct) (hff : ff) (hbe : be) (har : ar) :
    AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar :=
  ay_xmeg_conj_intro hxm
    (ay_xmeg_conj_intro ham
      (ay_xmeg_conj_intro hew
        (ay_xmeg_conj_intro hrd
          (ay_xmeg_conj_intro hod
            (ay_xmeg_conj_intro hrx
              (ay_xmeg_conj_intro hct
                (ay_xmeg_conj_intro hff
                  (ay_xmeg_conj_intro hbe har))))))))

theorem ay_xmeg_accepted_extension_xor_manifest
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : xm :=
  ay_xmeg_conj_left h

theorem ay_xmeg_accepted_extension_auxiliary_map
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : am :=
  ay_xmeg_conj_left (ay_xmeg_conj_right h)

theorem ay_xmeg_accepted_extension_witness
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : ew :=
  ay_xmeg_conj_left (ay_xmeg_conj_right (ay_xmeg_conj_right h))

theorem ay_xmeg_accepted_extension_reduced_digest
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : rd :=
  ay_xmeg_conj_left (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h)))

theorem ay_xmeg_accepted_extension_original_digest
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : od :=
  ay_xmeg_conj_left
    (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h))))

theorem ay_xmeg_accepted_extension_clause_xor_replay
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : rx :=
  ay_xmeg_conj_left
    (ay_xmeg_conj_right
      (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h)))))

theorem ay_xmeg_accepted_extension_checker
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : ct :=
  ay_xmeg_conj_left
    (ay_xmeg_conj_right
      (ay_xmeg_conj_right
        (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h))))))

theorem ay_xmeg_accepted_extension_fingerprint
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : ff :=
  ay_xmeg_conj_left
    (ay_xmeg_conj_right
      (ay_xmeg_conj_right
        (ay_xmeg_conj_right
          (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h)))))))

theorem ay_xmeg_accepted_extension_build
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : be :=
  ay_xmeg_conj_left
    (ay_xmeg_conj_right
      (ay_xmeg_conj_right
        (ay_xmeg_conj_right
          (ay_xmeg_conj_right
            (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h))))))))

theorem ay_xmeg_accepted_extension_archive
    {xm am ew rd od rx ct ff be ar : Prop}
    (h : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar) : ar :=
  ay_xmeg_conj_right
    (ay_xmeg_conj_right
      (ay_xmeg_conj_right
        (ay_xmeg_conj_right
          (ay_xmeg_conj_right
            (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right (ay_xmeg_conj_right h))))))))

theorem ay_xmeg_public_sat_intro {acceptedExtension totalAssignment originalSat : Prop}
    (hae : acceptedExtension) (htotal : totalAssignment) (hsat : originalSat) :
    AyXMEGPublicSat acceptedExtension totalAssignment originalSat :=
  ay_xmeg_conj_intro hae (ay_xmeg_conj_intro htotal hsat)

theorem ay_xmeg_public_sat_evidence {acceptedExtension totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat acceptedExtension totalAssignment originalSat) :
    acceptedExtension :=
  ay_xmeg_conj_left h

theorem ay_xmeg_public_sat_total_assignment
    {acceptedExtension totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat acceptedExtension totalAssignment originalSat) :
    totalAssignment :=
  ay_xmeg_conj_left (ay_xmeg_conj_right h)

theorem ay_xmeg_public_sat_claim {acceptedExtension totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat acceptedExtension totalAssignment originalSat) : originalSat :=
  ay_xmeg_conj_right (ay_xmeg_conj_right h)

theorem ay_xmeg_extension_reconstructs_total_original_assignment
    {xorSystem reduced projected total originalAssignment reducedAssignment originalFormula
     accepted originalFingerprint build archived : Prop}
    (hxm : AyXMEGXorEliminationManifest xorSystem reduced originalFormula)
    (ham : AyXMEGAuxiliaryVariableMap reduced projected)
    (hew : AyXMEGExtensionWitnessLedger projected total)
    (hrd : AyXMEGReducedAssignmentDigest reducedAssignment reduced)
    (hod : AyXMEGOriginalAssignmentDigest total originalAssignment)
    (hrx : AyXMEGClauseXorReplay originalAssignment originalFormula)
    (hct : AyXMEGCheckerTranscript originalFormula accepted)
    (hff : AyXMEGFormulaFingerprint accepted originalFingerprint)
    (hbe : AyXMEGBuildEvidence originalFingerprint build)
    (har : AyXMEGArchiveManifest build archived)
    (hreducedAssignment : reducedAssignment) :
    AyXMEGConj total (AyXMEGConj originalFormula archived) :=
  let hreduced : reduced := hrd hreducedAssignment
  let hprojected : projected := ham hreduced
  let htotal : total := hew hprojected
  let horiginalAssignment : originalAssignment := hod htotal
  let horiginalFormula : originalFormula := hrx horiginalAssignment
  let haccepted : accepted := hct horiginalFormula
  let hfingerprint : originalFingerprint := hff haccepted
  let hbuild : build := hbe hfingerprint
  let harchive : archived := har hbuild
  ay_xmeg_conj_intro htotal (ay_xmeg_conj_intro horiginalFormula harchive)

theorem ay_xmeg_accepted_extension_publishes_sound_sat
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (hae : AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat :=
  ay_xmeg_public_sat_intro hae htotal hsat

theorem ay_xmeg_public_sat_requires_accepted_extension
    {acceptedExtension totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat acceptedExtension totalAssignment originalSat) :
    acceptedExtension :=
  ay_xmeg_public_sat_evidence h

theorem ay_xmeg_publication_requires_xor_manifest
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : xm :=
  ay_xmeg_accepted_extension_xor_manifest (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_auxiliary_map
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : am :=
  ay_xmeg_accepted_extension_auxiliary_map (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_extension_witness
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : ew :=
  ay_xmeg_accepted_extension_witness (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_reduced_digest
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : rd :=
  ay_xmeg_accepted_extension_reduced_digest (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_original_digest
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : od :=
  ay_xmeg_accepted_extension_original_digest (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_clause_xor_replay
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : rx :=
  ay_xmeg_accepted_extension_clause_xor_replay (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_checker
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : ct :=
  ay_xmeg_accepted_extension_checker (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_fingerprint
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : ff :=
  ay_xmeg_accepted_extension_fingerprint (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_build
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : be :=
  ay_xmeg_accepted_extension_build (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_publication_requires_archive
    {xm am ew rd od rx ct ff be ar totalAssignment originalSat : Prop}
    (h : AyXMEGPublicSat (AyXMEGAcceptedExtension xm am ew rd od rx ct ff be ar)
      totalAssignment originalSat) : ar :=
  ay_xmeg_accepted_extension_archive (ay_xmeg_public_sat_requires_accepted_extension h)

theorem ay_xmeg_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  h

theorem ay_xmeg_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyXMEGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_xmeg_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyXMEGRecomputeObligation reason :=
  h

theorem ay_xmeg_recompute_obligation_request {reason : Prop}
    (h : AyXMEGRecomputeObligation reason) : reason :=
  h

theorem ay_xmeg_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_no_claim_diagnostic_intro h

theorem ay_xmeg_mismatch_recompute {reason : Prop} (h : reason) :
    AyXMEGRecomputeObligation reason :=
  ay_xmeg_recompute_obligation_intro h

theorem ay_xmeg_xor_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_auxiliary_map_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_extension_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_digest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_clause_xor_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyXMEGNoClaimDiagnostic reason :=
  ay_xmeg_mismatch_no_claim h

theorem ay_xmeg_failed_extension_cannot_bless_public_sat
    {failure acceptedExtension totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyXMEGPublicSat acceptedExtension totalAssignment originalSat ->
      AyXMEGNoClaimDiagnostic failure) :
    AyXMEGConj (AyXMEGNoClaimDiagnostic failure)
      (AyXMEGPublicSat acceptedExtension totalAssignment originalSat ->
        AyXMEGNoClaimDiagnostic failure) :=
  ay_xmeg_conj_intro (ay_xmeg_no_claim_diagnostic_intro hfail) hblock

theorem ay_xmeg_failed_extension_recompute_blocks_publication
    {failure acceptedExtension totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyXMEGPublicSat acceptedExtension totalAssignment originalSat ->
      AyXMEGRecomputeObligation failure) :
    AyXMEGConj (AyXMEGRecomputeObligation failure)
      (AyXMEGPublicSat acceptedExtension totalAssignment originalSat ->
        AyXMEGRecomputeObligation failure) :=
  ay_xmeg_conj_intro (ay_xmeg_recompute_obligation_intro hfail) hblock

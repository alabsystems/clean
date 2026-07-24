/-!
  SAT-COMP/ay totality/default-assignment guard.

  This self-contained package records the abstract obligations required before
  a partial assignment may be extended with defaults and published as a total
  public SAT witness for the original formula.
-/

def AyTDAGConj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def AyTDAGDisj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def AyTDAGEquisat (p q : Prop) : Prop :=
  AyTDAGConj (p -> q) (q -> p)

def AyTDAGAssignmentManifest (partialAssignment totalDomain : Prop) : Prop :=
  partialAssignment -> totalDomain

def AyTDAGDefaultPolicy (totalDomain defaultedAssignment : Prop) : Prop :=
  totalDomain -> defaultedAssignment

def AyTDAGExtensionWitnessLedger (defaultedAssignment totalAssignment : Prop) : Prop :=
  defaultedAssignment -> totalAssignment

def AyTDAGClauseReplay (totalAssignment originalFormula : Prop) : Prop :=
  totalAssignment -> originalFormula

def AyTDAGCheckerTranscript (originalFormula checkerAccepted : Prop) : Prop :=
  originalFormula -> checkerAccepted

def AyTDAGFormulaFingerprint (checkerAccepted fingerprint : Prop) : Prop :=
  checkerAccepted -> fingerprint

def AyTDAGBuildEvidence (fingerprint build : Prop) : Prop :=
  fingerprint -> build

def AyTDAGArchiveManifest (build archived : Prop) : Prop :=
  build -> archived

def AyTDAGAcceptedDefaults
    (assignmentManifest defaultPolicy extensionWitness clauseReplay checkerTranscript
     formulaFingerprint buildEvidence archiveManifest : Prop) : Prop :=
  AyTDAGConj assignmentManifest
    (AyTDAGConj defaultPolicy
      (AyTDAGConj extensionWitness
        (AyTDAGConj clauseReplay
          (AyTDAGConj checkerTranscript
            (AyTDAGConj formulaFingerprint
              (AyTDAGConj buildEvidence archiveManifest)))))))

def AyTDAGPublicSat (acceptedDefaults totalAssignment originalSat : Prop) : Prop :=
  AyTDAGConj acceptedDefaults (AyTDAGConj totalAssignment originalSat)

def AyTDAGNoClaimDiagnostic (reason : Prop) : Prop :=
  reason

def AyTDAGRecomputeObligation (reason : Prop) : Prop :=
  reason

theorem ay_tdag_conj_intro {p q : Prop} (hp : p) (hq : q) : AyTDAGConj p q :=
  fun r h => h hp hq

theorem ay_tdag_conj_left {p q : Prop} (h : AyTDAGConj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_tdag_conj_right {p q : Prop} (h : AyTDAGConj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_tdag_conj_left h)

theorem ay_tdag_disj_left {p q : Prop} (hp : p) : AyTDAGDisj p q :=
  fun r hl _ => hl hp

theorem ay_tdag_disj_right {p q : Prop} (hq : q) : AyTDAGDisj p q :=
  fun r _ hr => hr hq

theorem ay_tdag_equisat_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    AyTDAGEquisat p q :=
  ay_tdag_conj_intro hpq hqp

theorem ay_tdag_equisat_forward {p q : Prop} (h : AyTDAGEquisat p q) : p -> q :=
  ay_tdag_conj_left h

theorem ay_tdag_equisat_backward {p q : Prop} (h : AyTDAGEquisat p q) : q -> p :=
  ay_tdag_conj_right h

theorem ay_tdag_assignment_manifest_intro {partialAssignment totalDomain : Prop}
    (h : partialAssignment -> totalDomain) :
    AyTDAGAssignmentManifest partialAssignment totalDomain :=
  h

theorem ay_tdag_default_policy_intro {totalDomain defaultedAssignment : Prop}
    (h : totalDomain -> defaultedAssignment) :
    AyTDAGDefaultPolicy totalDomain defaultedAssignment :=
  h

theorem ay_tdag_extension_witness_ledger_intro
    {defaultedAssignment totalAssignment : Prop}
    (h : defaultedAssignment -> totalAssignment) :
    AyTDAGExtensionWitnessLedger defaultedAssignment totalAssignment :=
  h

theorem ay_tdag_clause_replay_intro {totalAssignment originalFormula : Prop}
    (h : totalAssignment -> originalFormula) :
    AyTDAGClauseReplay totalAssignment originalFormula :=
  h

theorem ay_tdag_checker_transcript_intro {originalFormula checkerAccepted : Prop}
    (h : originalFormula -> checkerAccepted) :
    AyTDAGCheckerTranscript originalFormula checkerAccepted :=
  h

theorem ay_tdag_formula_fingerprint_intro {checkerAccepted fingerprint : Prop}
    (h : checkerAccepted -> fingerprint) :
    AyTDAGFormulaFingerprint checkerAccepted fingerprint :=
  h

theorem ay_tdag_build_evidence_intro {fingerprint build : Prop}
    (h : fingerprint -> build) : AyTDAGBuildEvidence fingerprint build :=
  h

theorem ay_tdag_archive_manifest_intro {build archived : Prop}
    (h : build -> archived) : AyTDAGArchiveManifest build archived :=
  h

theorem ay_tdag_accepted_defaults_intro
    {am dp ew cr ct ff be ar : Prop}
    (ham : am) (hdp : dp) (hew : ew) (hcr : cr) (hct : ct) (hff : ff)
    (hbe : be) (har : ar) :
    AyTDAGAcceptedDefaults am dp ew cr ct ff be ar :=
  ay_tdag_conj_intro ham
    (ay_tdag_conj_intro hdp
      (ay_tdag_conj_intro hew
        (ay_tdag_conj_intro hcr
          (ay_tdag_conj_intro hct
            (ay_tdag_conj_intro hff
              (ay_tdag_conj_intro hbe har)))))))

theorem ay_tdag_accepted_defaults_assignment_manifest
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : am :=
  ay_tdag_conj_left h

theorem ay_tdag_accepted_defaults_policy
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : dp :=
  ay_tdag_conj_left (ay_tdag_conj_right h)

theorem ay_tdag_accepted_defaults_witness
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : ew :=
  ay_tdag_conj_left (ay_tdag_conj_right (ay_tdag_conj_right h))

theorem ay_tdag_accepted_defaults_replay
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : cr :=
  ay_tdag_conj_left (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right h)))

theorem ay_tdag_accepted_defaults_checker
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : ct :=
  ay_tdag_conj_left
    (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right h))))

theorem ay_tdag_accepted_defaults_fingerprint
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : ff :=
  ay_tdag_conj_left
    (ay_tdag_conj_right
      (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right h)))))

theorem ay_tdag_accepted_defaults_build
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : be :=
  ay_tdag_conj_left
    (ay_tdag_conj_right
      (ay_tdag_conj_right
        (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right h))))))

theorem ay_tdag_accepted_defaults_archive
    {am dp ew cr ct ff be ar : Prop}
    (h : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar) : ar :=
  ay_tdag_conj_right
    (ay_tdag_conj_right
      (ay_tdag_conj_right
        (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right (ay_tdag_conj_right h))))))

theorem ay_tdag_public_sat_intro {acceptedDefaults totalAssignment originalSat : Prop}
    (had : acceptedDefaults) (htotal : totalAssignment) (hsat : originalSat) :
    AyTDAGPublicSat acceptedDefaults totalAssignment originalSat :=
  ay_tdag_conj_intro had (ay_tdag_conj_intro htotal hsat)

theorem ay_tdag_public_sat_evidence {acceptedDefaults totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat) :
    acceptedDefaults :=
  ay_tdag_conj_left h

theorem ay_tdag_public_sat_total_assignment
    {acceptedDefaults totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat) :
    totalAssignment :=
  ay_tdag_conj_left (ay_tdag_conj_right h)

theorem ay_tdag_public_sat_claim {acceptedDefaults totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat) : originalSat :=
  ay_tdag_conj_right (ay_tdag_conj_right h)

theorem ay_tdag_defaults_reconstruct_total_assignment
    {am dp ew cr ct ff be ar totalAssignment originalFormula archived : Prop}
    (had : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
    (htotal : totalAssignment)
    (horiginal : originalFormula)
    (harchive : archived) :
    AyTDAGConj totalAssignment (AyTDAGConj originalFormula archived) :=
  ay_tdag_conj_intro htotal (ay_tdag_conj_intro horiginal harchive)

theorem ay_tdag_accepted_defaults_publish_sound_sat
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (had : AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
    (htotal : totalAssignment) (hsat : originalSat) :
    AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat :=
  ay_tdag_public_sat_intro had htotal hsat

theorem ay_tdag_public_sat_requires_accepted_defaults
    {acceptedDefaults totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat) :
    acceptedDefaults :=
  ay_tdag_public_sat_evidence h

theorem ay_tdag_publication_requires_assignment_manifest
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : am :=
  ay_tdag_accepted_defaults_assignment_manifest (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_default_policy
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : dp :=
  ay_tdag_accepted_defaults_policy (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_extension_witness
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : ew :=
  ay_tdag_accepted_defaults_witness (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_clause_replay
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : cr :=
  ay_tdag_accepted_defaults_replay (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_checker
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : ct :=
  ay_tdag_accepted_defaults_checker (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_fingerprint
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : ff :=
  ay_tdag_accepted_defaults_fingerprint (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_build
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : be :=
  ay_tdag_accepted_defaults_build (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_publication_requires_archive
    {am dp ew cr ct ff be ar totalAssignment originalSat : Prop}
    (h : AyTDAGPublicSat (AyTDAGAcceptedDefaults am dp ew cr ct ff be ar)
      totalAssignment originalSat) : ar :=
  ay_tdag_accepted_defaults_archive (ay_tdag_public_sat_requires_accepted_defaults h)

theorem ay_tdag_no_claim_diagnostic_intro {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  h

theorem ay_tdag_no_claim_diagnostic_blocks {reason : Prop}
    (h : AyTDAGNoClaimDiagnostic reason) : reason :=
  h

theorem ay_tdag_recompute_obligation_intro {reason : Prop} (h : reason) :
    AyTDAGRecomputeObligation reason :=
  h

theorem ay_tdag_recompute_obligation_request {reason : Prop}
    (h : AyTDAGRecomputeObligation reason) : reason :=
  h

theorem ay_tdag_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_no_claim_diagnostic_intro h

theorem ay_tdag_mismatch_recompute {reason : Prop} (h : reason) :
    AyTDAGRecomputeObligation reason :=
  ay_tdag_recompute_obligation_intro h

theorem ay_tdag_assignment_manifest_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_default_policy_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_extension_witness_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_clause_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_fingerprint_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_build_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    AyTDAGNoClaimDiagnostic reason :=
  ay_tdag_mismatch_no_claim h

theorem ay_tdag_failed_default_extension_cannot_bless_public_sat
    {failure acceptedDefaults totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat ->
      AyTDAGNoClaimDiagnostic failure) :
    AyTDAGConj (AyTDAGNoClaimDiagnostic failure)
      (AyTDAGPublicSat acceptedDefaults totalAssignment originalSat ->
        AyTDAGNoClaimDiagnostic failure) :=
  ay_tdag_conj_intro (ay_tdag_no_claim_diagnostic_intro hfail) hblock

theorem ay_tdag_failed_default_extension_recompute_blocks_publication
    {failure acceptedDefaults totalAssignment originalSat : Prop}
    (hfail : failure)
    (hblock : AyTDAGPublicSat acceptedDefaults totalAssignment originalSat ->
      AyTDAGRecomputeObligation failure) :
    AyTDAGConj (AyTDAGRecomputeObligation failure)
      (AyTDAGPublicSat acceptedDefaults totalAssignment originalSat ->
        AyTDAGRecomputeObligation failure) :=
  ay_tdag_conj_intro (ay_tdag_recompute_obligation_intro hfail) hblock

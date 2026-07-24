/-!
  SAT-COMP/ay UNSAT-label rejects assignment guard.

  This self-contained package models the obligations for rejecting stale or
  mixed SAT assignment artifacts attached to UNSAT/no-result solver labels.
-/

def ay_ulag_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_ulag_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_ulag_raw_solver_output_digest (rawOutput rawOk : Prop) : Prop :=
  rawOutput -> rawOk

def ay_ulag_status_parse_transcript (rawOk statusOk : Prop) : Prop :=
  rawOk -> statusOk

def ay_ulag_optional_assignment_artifact_digest
    (statusOk assignmentArtifactOk : Prop) : Prop :=
  statusOk -> assignmentArtifactOk

def ay_ulag_proof_artifact_digest_when_unsat
    (statusOk proofArtifactOk : Prop) : Prop :=
  statusOk -> proofArtifactOk

def ay_ulag_status_artifact_consistency_witness
    (assignmentArtifactOk proofArtifactOk consistencyOk : Prop) : Prop :=
  assignmentArtifactOk -> proofArtifactOk -> consistencyOk

def ay_ulag_checker_transcript (consistencyOk checkerOk : Prop) : Prop :=
  consistencyOk -> checkerOk

def ay_ulag_original_formula_fingerprint (checkerOk formulaOk : Prop) : Prop :=
  checkerOk -> formulaOk

def ay_ulag_solver_build_evidence (formulaOk buildOk : Prop) : Prop :=
  formulaOk -> buildOk

def ay_ulag_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_ulag_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_ulag_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_ulag_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_ulag_accepted_unsat
    (raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (raw -> status -> assignmentArtifact -> proofArtifact -> consistency -> checker ->
      formula -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_ulag_public_unsat
    (accepted proofArtifact checkerOk formulaOk validatorOk archiveOk audited : Prop) : Prop :=
  ay_ulag_conj accepted
    (ay_ulag_conj proofArtifact
      (ay_ulag_conj checkerOk
        (ay_ulag_conj formulaOk
          (ay_ulag_conj validatorOk (ay_ulag_conj archiveOk audited)))))

def ay_ulag_public_sat
    (accepted assignmentArtifact checkerOk formulaOk validatorOk archiveOk audited : Prop) :
    Prop :=
  ay_ulag_conj accepted
    (ay_ulag_conj assignmentArtifact
      (ay_ulag_conj checkerOk
        (ay_ulag_conj formulaOk
          (ay_ulag_conj validatorOk (ay_ulag_conj archiveOk audited)))))

def ay_ulag_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_ulag_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_ulag_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_ulag_conj p q :=
  fun r h => h hp hq

theorem ay_ulag_conj_left {p q : Prop} (h : ay_ulag_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_ulag_conj_right {p q : Prop} (h : ay_ulag_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_ulag_conj_left h)

theorem ay_ulag_disj_left {p q : Prop} (hp : p) : ay_ulag_disj p q :=
  fun r hl _ => hl hp

theorem ay_ulag_disj_right {p q : Prop} (hq : q) : ay_ulag_disj p q :=
  fun r _ hr => hr hq

theorem ay_ulag_raw_solver_output_digest_intro {rawOutput rawOk : Prop}
    (h : rawOutput -> rawOk) :
    ay_ulag_raw_solver_output_digest rawOutput rawOk :=
  h

theorem ay_ulag_status_parse_transcript_intro {rawOk statusOk : Prop}
    (h : rawOk -> statusOk) :
    ay_ulag_status_parse_transcript rawOk statusOk :=
  h

theorem ay_ulag_optional_assignment_artifact_digest_intro
    {statusOk assignmentArtifactOk : Prop}
    (h : statusOk -> assignmentArtifactOk) :
    ay_ulag_optional_assignment_artifact_digest statusOk assignmentArtifactOk :=
  h

theorem ay_ulag_proof_artifact_digest_when_unsat_intro
    {statusOk proofArtifactOk : Prop}
    (h : statusOk -> proofArtifactOk) :
    ay_ulag_proof_artifact_digest_when_unsat statusOk proofArtifactOk :=
  h

theorem ay_ulag_status_artifact_consistency_witness_intro
    {assignmentArtifactOk proofArtifactOk consistencyOk : Prop}
    (h : assignmentArtifactOk -> proofArtifactOk -> consistencyOk) :
    ay_ulag_status_artifact_consistency_witness assignmentArtifactOk proofArtifactOk
      consistencyOk :=
  h

theorem ay_ulag_checker_transcript_intro {consistencyOk checkerOk : Prop}
    (h : consistencyOk -> checkerOk) :
    ay_ulag_checker_transcript consistencyOk checkerOk :=
  h

theorem ay_ulag_original_formula_fingerprint_intro {checkerOk formulaOk : Prop}
    (h : checkerOk -> formulaOk) :
    ay_ulag_original_formula_fingerprint checkerOk formulaOk :=
  h

theorem ay_ulag_solver_build_evidence_intro {formulaOk buildOk : Prop}
    (h : formulaOk -> buildOk) :
    ay_ulag_solver_build_evidence formulaOk buildOk :=
  h

theorem ay_ulag_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_ulag_validator_gate buildOk validatorOk :=
  h

theorem ay_ulag_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_ulag_archive_manifest validatorOk archiveOk :=
  h

theorem ay_ulag_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_ulag_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_ulag_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_ulag_audit_transcript fallbackReady audited :=
  h

theorem ay_ulag_accepted_unsat_intro
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (hr : raw) (hs : status) (ha : assignmentArtifact) (hp : proofArtifact)
    (hc : consistency) (hchk : checker) (hf : formula) (hb : build) (hv : validator)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency checker
      formula build validator archive fallback audit :=
  fun r k => k hr hs ha hp hc hchk hf hb hv har hfb hau

theorem ay_ulag_accepted_unsat_assignment_artifact
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : assignmentArtifact :=
  h assignmentArtifact (fun _ _ ha _ _ _ _ _ _ _ _ _ => ha)

theorem ay_ulag_accepted_unsat_proof_artifact
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : proofArtifact :=
  h proofArtifact (fun _ _ _ hp _ _ _ _ _ _ _ _ => hp)

theorem ay_ulag_accepted_unsat_checker
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ hchk _ _ _ _ _ _ => hchk)

theorem ay_ulag_accepted_unsat_formula
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : formula :=
  h formula (fun _ _ _ _ _ _ hf _ _ _ _ _ => hf)

theorem ay_ulag_accepted_unsat_validator
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_ulag_accepted_unsat_archive
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_ulag_accepted_unsat_audit
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_ulag_public_unsat_intro
    {accepted proofArtifact checkerOk formulaOk validatorOk archiveOk audited : Prop}
    (ha : accepted) (hp : proofArtifact) (hc : checkerOk) (hf : formulaOk)
    (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_ulag_public_unsat accepted proofArtifact checkerOk formulaOk validatorOk archiveOk
      audited :=
  ay_ulag_conj_intro ha
    (ay_ulag_conj_intro hp
      (ay_ulag_conj_intro hc
        (ay_ulag_conj_intro hf
          (ay_ulag_conj_intro hv (ay_ulag_conj_intro har hau)))))

theorem ay_ulag_public_sat_intro
    {accepted assignmentArtifact checkerOk formulaOk validatorOk archiveOk audited : Prop}
    (ha : accepted) (hp : assignmentArtifact) (hc : checkerOk) (hf : formulaOk)
    (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_ulag_public_sat accepted assignmentArtifact checkerOk formulaOk validatorOk archiveOk
      audited :=
  ay_ulag_conj_intro ha
    (ay_ulag_conj_intro hp
      (ay_ulag_conj_intro hc
        (ay_ulag_conj_intro hf
          (ay_ulag_conj_intro hv (ay_ulag_conj_intro har hau)))))

theorem ay_ulag_unsat_publication_requires_proof_checker_evidence
    {raw status assignmentArtifact proofArtifact consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency
      checker formula build validator archive fallback audit) :
    ay_ulag_public_unsat
      (ay_ulag_accepted_unsat raw status assignmentArtifact proofArtifact consistency checker
        formula build validator archive fallback audit)
      proofArtifact checker formula validator archive audit :=
  ay_ulag_public_unsat_intro
    h
    (ay_ulag_accepted_unsat_proof_artifact h)
    (ay_ulag_accepted_unsat_checker h)
    (ay_ulag_accepted_unsat_formula h)
    (ay_ulag_accepted_unsat_validator h)
    (ay_ulag_accepted_unsat_archive h)
    (ay_ulag_accepted_unsat_audit h)

theorem ay_ulag_unsat_rejects_inconsistent_assignment_artifact
    {inconsistentAssignment nonPublicationEvidence : Prop}
    (reject : inconsistentAssignment -> nonPublicationEvidence)
    (h : inconsistentAssignment) : nonPublicationEvidence :=
  reject h

theorem ay_ulag_sat_assignment_under_unsat_label_no_claim_or_recompute
    {assignmentUnderUnsat noClaim recompute : Prop}
    (hn : assignmentUnderUnsat -> noClaim)
    (hr : assignmentUnderUnsat -> recompute)
    (ha : assignmentUnderUnsat) :
    ay_ulag_conj noClaim recompute :=
  ay_ulag_conj_intro (hn ha) (hr ha)

theorem ay_ulag_no_claim_intro {reason : Prop} (h : reason) :
    ay_ulag_no_claim_diagnostic reason :=
  h

theorem ay_ulag_recompute_intro {reason : Prop} (h : reason) :
    ay_ulag_recompute_obligation reason :=
  h

theorem ay_ulag_output_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_status_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_ulag_recompute_obligation mismatch :=
  ay_ulag_recompute_intro h

theorem ay_ulag_artifact_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_proof_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_ulag_recompute_obligation mismatch :=
  ay_ulag_recompute_intro h

theorem ay_ulag_checker_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_formula_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_ulag_recompute_obligation mismatch :=
  ay_ulag_recompute_intro h

theorem ay_ulag_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_ulag_recompute_obligation mismatch :=
  ay_ulag_recompute_intro h

theorem ay_ulag_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_ulag_no_claim_diagnostic mismatch :=
  ay_ulag_no_claim_intro h

theorem ay_ulag_failed_consistency_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_ulag_no_claim_diagnostic failure)
    (noBless : ay_ulag_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_ulag_failed_consistency_guard_cannot_bless_unsat_publication
    {failure publicUnsat : Prop}
    (fallback : failure -> ay_ulag_no_claim_diagnostic failure)
    (noBless : ay_ulag_no_claim_diagnostic failure -> publicUnsat -> failure)
    (hfailure : failure) (hpublic : publicUnsat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_ulag_failed_consistency_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_ulag_recompute_obligation failure)
    (hfailure : failure) :
    ay_ulag_recompute_obligation failure :=
  fallback hfailure

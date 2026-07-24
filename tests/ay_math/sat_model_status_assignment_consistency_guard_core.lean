/-!
  SAT-COMP/ay status/assignment consistency guard.

  This self-contained package models the SAT-only obligations for ensuring
  solver status labels, parsed assignments, and checker replay are coherent.
-/

def ay_sacg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_sacg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_sacg_raw_solver_output_digest (rawOutput rawOk : Prop) : Prop :=
  rawOutput -> rawOk

def ay_sacg_status_parse_transcript (rawOk statusOk : Prop) : Prop :=
  rawOk -> statusOk

def ay_sacg_assignment_artifact_digest (statusOk assignmentArtifactOk : Prop) : Prop :=
  statusOk -> assignmentArtifactOk

def ay_sacg_parser_version_digest (assignmentArtifactOk parserOk : Prop) : Prop :=
  assignmentArtifactOk -> parserOk

def ay_sacg_normalized_assignment_digest (parserOk normalizedAssignmentOk : Prop) : Prop :=
  parserOk -> normalizedAssignmentOk

def ay_sacg_original_formula_fingerprint
    (normalizedAssignmentOk formulaOk : Prop) : Prop :=
  normalizedAssignmentOk -> formulaOk

def ay_sacg_status_assignment_consistency_witness
    (formulaOk consistencyOk : Prop) : Prop :=
  formulaOk -> consistencyOk

def ay_sacg_clause_satisfaction_replay
    (consistencyOk originalClausesSatisfied : Prop) : Prop :=
  consistencyOk -> originalClausesSatisfied

def ay_sacg_solver_build_evidence
    (originalClausesSatisfied buildOk : Prop) : Prop :=
  originalClausesSatisfied -> buildOk

def ay_sacg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_sacg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_sacg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_sacg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_sacg_accepted_consistency
    (raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop) : Prop :=
  forall r : Prop,
    (raw -> status -> assignment -> parser -> normalized -> formula -> consistency ->
      replay -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_sacg_public_sat
    (accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_sacg_conj accepted
    (ay_sacg_conj satStatus
      (ay_sacg_conj normalizedAssignment
        (ay_sacg_conj originalClausesSatisfied
          (ay_sacg_conj validatorOk (ay_sacg_conj archiveOk audited)))))

def ay_sacg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_sacg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_sacg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_sacg_conj p q :=
  fun r h => h hp hq

theorem ay_sacg_conj_left {p q : Prop} (h : ay_sacg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_sacg_conj_right {p q : Prop} (h : ay_sacg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_sacg_conj_left h)

theorem ay_sacg_disj_left {p q : Prop} (hp : p) : ay_sacg_disj p q :=
  fun r hl _ => hl hp

theorem ay_sacg_disj_right {p q : Prop} (hq : q) : ay_sacg_disj p q :=
  fun r _ hr => hr hq

theorem ay_sacg_raw_solver_output_digest_intro {rawOutput rawOk : Prop}
    (h : rawOutput -> rawOk) :
    ay_sacg_raw_solver_output_digest rawOutput rawOk :=
  h

theorem ay_sacg_status_parse_transcript_intro {rawOk statusOk : Prop}
    (h : rawOk -> statusOk) :
    ay_sacg_status_parse_transcript rawOk statusOk :=
  h

theorem ay_sacg_assignment_artifact_digest_intro {statusOk assignmentArtifactOk : Prop}
    (h : statusOk -> assignmentArtifactOk) :
    ay_sacg_assignment_artifact_digest statusOk assignmentArtifactOk :=
  h

theorem ay_sacg_parser_version_digest_intro {assignmentArtifactOk parserOk : Prop}
    (h : assignmentArtifactOk -> parserOk) :
    ay_sacg_parser_version_digest assignmentArtifactOk parserOk :=
  h

theorem ay_sacg_normalized_assignment_digest_intro
    {parserOk normalizedAssignmentOk : Prop}
    (h : parserOk -> normalizedAssignmentOk) :
    ay_sacg_normalized_assignment_digest parserOk normalizedAssignmentOk :=
  h

theorem ay_sacg_original_formula_fingerprint_intro
    {normalizedAssignmentOk formulaOk : Prop}
    (h : normalizedAssignmentOk -> formulaOk) :
    ay_sacg_original_formula_fingerprint normalizedAssignmentOk formulaOk :=
  h

theorem ay_sacg_status_assignment_consistency_witness_intro
    {formulaOk consistencyOk : Prop}
    (h : formulaOk -> consistencyOk) :
    ay_sacg_status_assignment_consistency_witness formulaOk consistencyOk :=
  h

theorem ay_sacg_clause_satisfaction_replay_intro
    {consistencyOk originalClausesSatisfied : Prop}
    (h : consistencyOk -> originalClausesSatisfied) :
    ay_sacg_clause_satisfaction_replay consistencyOk originalClausesSatisfied :=
  h

theorem ay_sacg_solver_build_evidence_intro
    {originalClausesSatisfied buildOk : Prop}
    (h : originalClausesSatisfied -> buildOk) :
    ay_sacg_solver_build_evidence originalClausesSatisfied buildOk :=
  h

theorem ay_sacg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_sacg_validator_gate buildOk validatorOk :=
  h

theorem ay_sacg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_sacg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_sacg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_sacg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_sacg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_sacg_audit_transcript fallbackReady audited :=
  h

theorem ay_sacg_accepted_consistency_intro
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (hr : raw) (hs : status) (ha : assignment) (hp : parser) (hn : normalized)
    (hf : formula) (hc : consistency) (hreplay : replay) (hb : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit :=
  fun r k => k hr hs ha hp hn hf hc hreplay hb hv har hfb hau

theorem ay_sacg_accepted_consistency_status
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : status :=
  h status (fun _ hs _ _ _ _ _ _ _ _ _ _ _ => hs)

theorem ay_sacg_accepted_consistency_assignment
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : assignment :=
  h assignment (fun _ _ ha _ _ _ _ _ _ _ _ _ _ => ha)

theorem ay_sacg_accepted_consistency_parser
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : parser :=
  h parser (fun _ _ _ hp _ _ _ _ _ _ _ _ _ => hp)

theorem ay_sacg_accepted_consistency_normalized
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : normalized :=
  h normalized (fun _ _ _ _ hn _ _ _ _ _ _ _ _ => hn)

theorem ay_sacg_accepted_consistency_consistency
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : consistency :=
  h consistency (fun _ _ _ _ _ _ hc _ _ _ _ _ _ => hc)

theorem ay_sacg_accepted_consistency_replay
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_sacg_accepted_consistency_validator
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_sacg_accepted_consistency_archive
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_sacg_accepted_consistency_audit
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_sacg_public_sat_intro
    {accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (hs : satStatus) (hn : normalizedAssignment)
    (hr : originalClausesSatisfied) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_sacg_public_sat accepted satStatus normalizedAssignment originalClausesSatisfied
      validatorOk archiveOk audited :=
  ay_sacg_conj_intro ha
    (ay_sacg_conj_intro hs
      (ay_sacg_conj_intro hn
        (ay_sacg_conj_intro hr
          (ay_sacg_conj_intro hv (ay_sacg_conj_intro har hau)))))

theorem ay_sacg_public_sat_requires_status_guard
    {accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop}
    (h : ay_sacg_public_sat accepted satStatus normalizedAssignment
      originalClausesSatisfied validatorOk archiveOk audited) : accepted :=
  ay_sacg_conj_left h

theorem ay_sacg_public_sat_sat_status
    {accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop}
    (h : ay_sacg_public_sat accepted satStatus normalizedAssignment
      originalClausesSatisfied validatorOk archiveOk audited) : satStatus :=
  ay_sacg_conj_left (ay_sacg_conj_right h)

theorem ay_sacg_public_sat_normalized_assignment
    {accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop}
    (h : ay_sacg_public_sat accepted satStatus normalizedAssignment
      originalClausesSatisfied validatorOk archiveOk audited) : normalizedAssignment :=
  ay_sacg_conj_left (ay_sacg_conj_right (ay_sacg_conj_right h))

theorem ay_sacg_public_sat_original_clauses
    {accepted satStatus normalizedAssignment originalClausesSatisfied validatorOk archiveOk
     audited : Prop}
    (h : ay_sacg_public_sat accepted satStatus normalizedAssignment
      originalClausesSatisfied validatorOk archiveOk audited) : originalClausesSatisfied :=
  ay_sacg_conj_left
    (ay_sacg_conj_right (ay_sacg_conj_right (ay_sacg_conj_right h)))

theorem ay_sacg_accepted_sat_requires_status_and_assignment
    {raw status assignment parser normalized formula consistency replay build validator archive
     fallback audit : Prop}
    (h : ay_sacg_accepted_consistency raw status assignment parser normalized formula
      consistency replay build validator archive fallback audit) :
    ay_sacg_public_sat
      (ay_sacg_accepted_consistency raw status assignment parser normalized formula
        consistency replay build validator archive fallback audit)
      status normalized replay validator archive audit :=
  ay_sacg_public_sat_intro
    h
    (ay_sacg_accepted_consistency_status h)
    (ay_sacg_accepted_consistency_normalized h)
    (ay_sacg_accepted_consistency_replay h)
    (ay_sacg_accepted_consistency_validator h)
    (ay_sacg_accepted_consistency_archive h)
    (ay_sacg_accepted_consistency_audit h)

theorem ay_sacg_inconsistent_status_assignment_no_claim_or_recompute
    {inconsistent noClaim recompute : Prop}
    (hn : inconsistent -> noClaim)
    (hr : inconsistent -> recompute)
    (hi : inconsistent) :
    ay_sacg_conj noClaim recompute :=
  ay_sacg_conj_intro (hn hi) (hr hi)

theorem ay_sacg_no_claim_intro {reason : Prop} (h : reason) :
    ay_sacg_no_claim_diagnostic reason :=
  h

theorem ay_sacg_recompute_intro {reason : Prop} (h : reason) :
    ay_sacg_recompute_obligation reason :=
  h

theorem ay_sacg_output_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_status_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_sacg_recompute_obligation mismatch :=
  ay_sacg_recompute_intro h

theorem ay_sacg_assignment_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_parser_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_sacg_recompute_obligation mismatch :=
  ay_sacg_recompute_intro h

theorem ay_sacg_normalization_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_sacg_recompute_obligation mismatch :=
  ay_sacg_recompute_intro h

theorem ay_sacg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_sacg_recompute_obligation mismatch :=
  ay_sacg_recompute_intro h

theorem ay_sacg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_sacg_no_claim_diagnostic mismatch :=
  ay_sacg_no_claim_intro h

theorem ay_sacg_failed_status_assignment_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_sacg_no_claim_diagnostic failure)
    (noBless : ay_sacg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_sacg_failed_status_assignment_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_sacg_recompute_obligation failure)
    (hfailure : failure) :
    ay_sacg_recompute_obligation failure :=
  fallback hfailure

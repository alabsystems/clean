/-!
  SAT-COMP/ay multi-status output guard.

  This self-contained package models the obligations for choosing one coherent
  final solver status from output that may contain stale or repeated status
  lines.
-/

def ay_msog_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_msog_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_msog_raw_solver_output_digest (rawOutput rawOk : Prop) : Prop :=
  rawOutput -> rawOk

def ay_msog_status_line_sequence_transcript (rawOk statusSequenceOk : Prop) : Prop :=
  rawOk -> statusSequenceOk

def ay_msog_final_status_selection_rule (statusSequenceOk selectedStatusOk : Prop) : Prop :=
  statusSequenceOk -> selectedStatusOk

def ay_msog_stale_appended_output_ledger (selectedStatusOk staleLedgerOk : Prop) : Prop :=
  selectedStatusOk -> staleLedgerOk

def ay_msog_assignment_proof_artifact_digests
    (staleLedgerOk artifactDigestsOk : Prop) : Prop :=
  staleLedgerOk -> artifactDigestsOk

def ay_msog_status_artifact_consistency_witness
    (artifactDigestsOk consistencyOk : Prop) : Prop :=
  artifactDigestsOk -> consistencyOk

def ay_msog_checker_transcript (consistencyOk checkerOk : Prop) : Prop :=
  consistencyOk -> checkerOk

def ay_msog_original_formula_fingerprint (checkerOk formulaOk : Prop) : Prop :=
  checkerOk -> formulaOk

def ay_msog_solver_build_evidence (formulaOk buildOk : Prop) : Prop :=
  formulaOk -> buildOk

def ay_msog_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_msog_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_msog_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_msog_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_msog_accepted_selection
    (raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (raw -> sequence -> selected -> staleLedger -> artifacts -> consistency -> checker ->
      formula -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_msog_public_sat
    (accepted selectedStatus artifactEvidence checkerOk formulaOk validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_msog_conj accepted
    (ay_msog_conj selectedStatus
      (ay_msog_conj artifactEvidence
        (ay_msog_conj checkerOk
          (ay_msog_conj formulaOk
            (ay_msog_conj validatorOk (ay_msog_conj archiveOk audited))))))

def ay_msog_public_unsat
    (accepted selectedStatus artifactEvidence checkerOk formulaOk validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_msog_conj accepted
    (ay_msog_conj selectedStatus
      (ay_msog_conj artifactEvidence
        (ay_msog_conj checkerOk
          (ay_msog_conj formulaOk
            (ay_msog_conj validatorOk (ay_msog_conj archiveOk audited))))))

def ay_msog_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_msog_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_msog_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_msog_conj p q :=
  fun r h => h hp hq

theorem ay_msog_conj_left {p q : Prop} (h : ay_msog_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_msog_conj_right {p q : Prop} (h : ay_msog_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_msog_conj_left h)

theorem ay_msog_disj_left {p q : Prop} (hp : p) : ay_msog_disj p q :=
  fun r hl _ => hl hp

theorem ay_msog_disj_right {p q : Prop} (hq : q) : ay_msog_disj p q :=
  fun r _ hr => hr hq

theorem ay_msog_raw_solver_output_digest_intro {rawOutput rawOk : Prop}
    (h : rawOutput -> rawOk) :
    ay_msog_raw_solver_output_digest rawOutput rawOk :=
  h

theorem ay_msog_status_line_sequence_transcript_intro {rawOk statusSequenceOk : Prop}
    (h : rawOk -> statusSequenceOk) :
    ay_msog_status_line_sequence_transcript rawOk statusSequenceOk :=
  h

theorem ay_msog_final_status_selection_rule_intro
    {statusSequenceOk selectedStatusOk : Prop}
    (h : statusSequenceOk -> selectedStatusOk) :
    ay_msog_final_status_selection_rule statusSequenceOk selectedStatusOk :=
  h

theorem ay_msog_stale_appended_output_ledger_intro
    {selectedStatusOk staleLedgerOk : Prop}
    (h : selectedStatusOk -> staleLedgerOk) :
    ay_msog_stale_appended_output_ledger selectedStatusOk staleLedgerOk :=
  h

theorem ay_msog_assignment_proof_artifact_digests_intro
    {staleLedgerOk artifactDigestsOk : Prop}
    (h : staleLedgerOk -> artifactDigestsOk) :
    ay_msog_assignment_proof_artifact_digests staleLedgerOk artifactDigestsOk :=
  h

theorem ay_msog_status_artifact_consistency_witness_intro
    {artifactDigestsOk consistencyOk : Prop}
    (h : artifactDigestsOk -> consistencyOk) :
    ay_msog_status_artifact_consistency_witness artifactDigestsOk consistencyOk :=
  h

theorem ay_msog_checker_transcript_intro {consistencyOk checkerOk : Prop}
    (h : consistencyOk -> checkerOk) :
    ay_msog_checker_transcript consistencyOk checkerOk :=
  h

theorem ay_msog_original_formula_fingerprint_intro {checkerOk formulaOk : Prop}
    (h : checkerOk -> formulaOk) :
    ay_msog_original_formula_fingerprint checkerOk formulaOk :=
  h

theorem ay_msog_solver_build_evidence_intro {formulaOk buildOk : Prop}
    (h : formulaOk -> buildOk) :
    ay_msog_solver_build_evidence formulaOk buildOk :=
  h

theorem ay_msog_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_msog_validator_gate buildOk validatorOk :=
  h

theorem ay_msog_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_msog_archive_manifest validatorOk archiveOk :=
  h

theorem ay_msog_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_msog_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_msog_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_msog_audit_transcript fallbackReady audited :=
  h

theorem ay_msog_accepted_selection_intro
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (hr : raw) (hs : sequence) (hsel : selected) (hstale : staleLedger)
    (hart : artifacts) (hc : consistency) (hchk : checker) (hf : formula) (hb : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit :=
  fun r k => k hr hs hsel hstale hart hc hchk hf hb hv har hfb hau

theorem ay_msog_accepted_selection_selected
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : selected :=
  h selected (fun _ _ hsel _ _ _ _ _ _ _ _ _ _ => hsel)

theorem ay_msog_accepted_selection_artifacts
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : artifacts :=
  h artifacts (fun _ _ _ _ hart _ _ _ _ _ _ _ _ => hart)

theorem ay_msog_accepted_selection_checker
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ hchk _ _ _ _ _ _ => hchk)

theorem ay_msog_accepted_selection_formula
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : formula :=
  h formula (fun _ _ _ _ _ _ _ hf _ _ _ _ _ => hf)

theorem ay_msog_accepted_selection_validator
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_msog_accepted_selection_archive
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_msog_accepted_selection_audit
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_msog_public_sat_intro
    {accepted selectedStatus artifactEvidence checkerOk formulaOk validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (hs : selectedStatus) (hart : artifactEvidence) (hc : checkerOk)
    (hf : formulaOk) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_msog_public_sat accepted selectedStatus artifactEvidence checkerOk formulaOk
      validatorOk archiveOk audited :=
  ay_msog_conj_intro ha
    (ay_msog_conj_intro hs
      (ay_msog_conj_intro hart
        (ay_msog_conj_intro hc
          (ay_msog_conj_intro hf
            (ay_msog_conj_intro hv (ay_msog_conj_intro har hau))))))

theorem ay_msog_public_unsat_intro
    {accepted selectedStatus artifactEvidence checkerOk formulaOk validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (hs : selectedStatus) (hart : artifactEvidence) (hc : checkerOk)
    (hf : formulaOk) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_msog_public_unsat accepted selectedStatus artifactEvidence checkerOk formulaOk
      validatorOk archiveOk audited :=
  ay_msog_conj_intro ha
    (ay_msog_conj_intro hs
      (ay_msog_conj_intro hart
        (ay_msog_conj_intro hc
          (ay_msog_conj_intro hf
            (ay_msog_conj_intro hv (ay_msog_conj_intro har hau))))))

theorem ay_msog_accepted_publication_requires_unique_selected_status
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) :
    ay_msog_conj selected (ay_msog_conj artifacts checker) :=
  ay_msog_conj_intro
    (ay_msog_accepted_selection_selected h)
    (ay_msog_conj_intro
      (ay_msog_accepted_selection_artifacts h)
      (ay_msog_accepted_selection_checker h))

theorem ay_msog_accepted_selection_publishes_sat
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) :
    ay_msog_public_sat
      (ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
        checker formula build validator archive fallback audit)
      selected artifacts checker formula validator archive audit :=
  ay_msog_public_sat_intro
    h
    (ay_msog_accepted_selection_selected h)
    (ay_msog_accepted_selection_artifacts h)
    (ay_msog_accepted_selection_checker h)
    (ay_msog_accepted_selection_formula h)
    (ay_msog_accepted_selection_validator h)
    (ay_msog_accepted_selection_archive h)
    (ay_msog_accepted_selection_audit h)

theorem ay_msog_accepted_selection_publishes_unsat
    {raw sequence selected staleLedger artifacts consistency checker formula build validator
     archive fallback audit : Prop}
    (h : ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
      checker formula build validator archive fallback audit) :
    ay_msog_public_unsat
      (ay_msog_accepted_selection raw sequence selected staleLedger artifacts consistency
        checker formula build validator archive fallback audit)
      selected artifacts checker formula validator archive audit :=
  ay_msog_public_unsat_intro
    h
    (ay_msog_accepted_selection_selected h)
    (ay_msog_accepted_selection_artifacts h)
    (ay_msog_accepted_selection_checker h)
    (ay_msog_accepted_selection_formula h)
    (ay_msog_accepted_selection_validator h)
    (ay_msog_accepted_selection_archive h)
    (ay_msog_accepted_selection_audit h)

theorem ay_msog_status_conflict_no_claim_or_recompute
    {conflictingStatus noClaim recompute : Prop}
    (hn : conflictingStatus -> noClaim)
    (hr : conflictingStatus -> recompute)
    (hc : conflictingStatus) :
    ay_msog_conj noClaim recompute :=
  ay_msog_conj_intro (hn hc) (hr hc)

theorem ay_msog_no_claim_intro {reason : Prop} (h : reason) :
    ay_msog_no_claim_diagnostic reason :=
  h

theorem ay_msog_recompute_intro {reason : Prop} (h : reason) :
    ay_msog_recompute_obligation reason :=
  h

theorem ay_msog_output_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_status_sequence_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_msog_recompute_obligation mismatch :=
  ay_msog_recompute_intro h

theorem ay_msog_selection_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_artifact_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_msog_recompute_obligation mismatch :=
  ay_msog_recompute_intro h

theorem ay_msog_checker_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_formula_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_msog_recompute_obligation mismatch :=
  ay_msog_recompute_intro h

theorem ay_msog_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_msog_recompute_obligation mismatch :=
  ay_msog_recompute_intro h

theorem ay_msog_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_msog_no_claim_diagnostic mismatch :=
  ay_msog_no_claim_intro h

theorem ay_msog_failed_multi_status_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_msog_no_claim_diagnostic failure)
    (noBless : ay_msog_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_msog_failed_multi_status_guard_cannot_bless_unsat_publication
    {failure publicUnsat : Prop}
    (fallback : failure -> ay_msog_no_claim_diagnostic failure)
    (noBless : ay_msog_no_claim_diagnostic failure -> publicUnsat -> failure)
    (hfailure : failure) (hpublic : publicUnsat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_msog_failed_multi_status_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_msog_recompute_obligation failure)
    (hfailure : failure) :
    ay_msog_recompute_obligation failure :=
  fallback hfailure

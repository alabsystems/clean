/-!
  SAT-COMP/ay sparse-assignment index guard.

  This self-contained package models the SAT-only obligations for decoding
  sparse model witnesses that refer to a variable-index table.
-/

def ay_saig_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_saig_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_saig_original_formula_fingerprint
    (sparseWitness formulaOk : Prop) : Prop :=
  sparseWitness -> formulaOk

def ay_saig_sparse_assignment_digest (formulaOk sparseOk : Prop) : Prop :=
  formulaOk -> sparseOk

def ay_saig_variable_index_table_digest (sparseOk tableOk : Prop) : Prop :=
  sparseOk -> tableOk

def ay_saig_index_to_variable_map_witness (tableOk mapOk : Prop) : Prop :=
  tableOk -> mapOk

def ay_saig_default_completion_policy_manifest (mapOk defaultOk : Prop) : Prop :=
  mapOk -> defaultOk

def ay_saig_normalized_assignment_digest (defaultOk normalizedOk : Prop) : Prop :=
  defaultOk -> normalizedOk

def ay_saig_out_of_range_index_ledger (normalizedOk rangeLedgerOk : Prop) : Prop :=
  normalizedOk -> rangeLedgerOk

def ay_saig_clause_satisfaction_replay
    (rangeLedgerOk everyOriginalClauseSatisfied : Prop) : Prop :=
  rangeLedgerOk -> everyOriginalClauseSatisfied

def ay_saig_checker_transcript
    (everyOriginalClauseSatisfied checkerOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> checkerOk

def ay_saig_solver_build_evidence (checkerOk buildOk : Prop) : Prop :=
  checkerOk -> buildOk

def ay_saig_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_saig_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_saig_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_saig_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_saig_accepted_sparse_index
    (formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> sparse -> table -> indexMap -> defaultPolicy -> normalized ->
      rangeLedger -> replay -> checker -> build -> validator -> archive -> fallback ->
      audit -> r) -> r

def ay_saig_public_sat
    (accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop) : Prop :=
  ay_saig_conj accepted
    (ay_saig_conj normalizedAssignment
      (ay_saig_conj everyOriginalClauseSatisfied
        (ay_saig_conj tableOk
          (ay_saig_conj indexMapOk
            (ay_saig_conj rangeLedgerOk
              (ay_saig_conj checkerOk
                (ay_saig_conj validatorOk (ay_saig_conj archiveOk audited))))))))

def ay_saig_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_saig_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_saig_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_saig_conj p q :=
  fun r h => h hp hq

theorem ay_saig_conj_left {p q : Prop} (h : ay_saig_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_saig_conj_right {p q : Prop} (h : ay_saig_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_saig_conj_left h)

theorem ay_saig_disj_left {p q : Prop} (hp : p) : ay_saig_disj p q :=
  fun r hl _ => hl hp

theorem ay_saig_disj_right {p q : Prop} (hq : q) : ay_saig_disj p q :=
  fun r _ hr => hr hq

theorem ay_saig_original_formula_fingerprint_intro
    {sparseWitness formulaOk : Prop}
    (h : sparseWitness -> formulaOk) :
    ay_saig_original_formula_fingerprint sparseWitness formulaOk :=
  h

theorem ay_saig_sparse_assignment_digest_intro {formulaOk sparseOk : Prop}
    (h : formulaOk -> sparseOk) :
    ay_saig_sparse_assignment_digest formulaOk sparseOk :=
  h

theorem ay_saig_variable_index_table_digest_intro {sparseOk tableOk : Prop}
    (h : sparseOk -> tableOk) :
    ay_saig_variable_index_table_digest sparseOk tableOk :=
  h

theorem ay_saig_index_to_variable_map_witness_intro {tableOk mapOk : Prop}
    (h : tableOk -> mapOk) :
    ay_saig_index_to_variable_map_witness tableOk mapOk :=
  h

theorem ay_saig_default_completion_policy_manifest_intro
    {mapOk defaultOk : Prop}
    (h : mapOk -> defaultOk) :
    ay_saig_default_completion_policy_manifest mapOk defaultOk :=
  h

theorem ay_saig_normalized_assignment_digest_intro
    {defaultOk normalizedOk : Prop}
    (h : defaultOk -> normalizedOk) :
    ay_saig_normalized_assignment_digest defaultOk normalizedOk :=
  h

theorem ay_saig_out_of_range_index_ledger_intro
    {normalizedOk rangeLedgerOk : Prop}
    (h : normalizedOk -> rangeLedgerOk) :
    ay_saig_out_of_range_index_ledger normalizedOk rangeLedgerOk :=
  h

theorem ay_saig_clause_satisfaction_replay_intro
    {rangeLedgerOk everyOriginalClauseSatisfied : Prop}
    (h : rangeLedgerOk -> everyOriginalClauseSatisfied) :
    ay_saig_clause_satisfaction_replay rangeLedgerOk everyOriginalClauseSatisfied :=
  h

theorem ay_saig_checker_transcript_intro
    {everyOriginalClauseSatisfied checkerOk : Prop}
    (h : everyOriginalClauseSatisfied -> checkerOk) :
    ay_saig_checker_transcript everyOriginalClauseSatisfied checkerOk :=
  h

theorem ay_saig_solver_build_evidence_intro {checkerOk buildOk : Prop}
    (h : checkerOk -> buildOk) :
    ay_saig_solver_build_evidence checkerOk buildOk :=
  h

theorem ay_saig_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_saig_validator_gate buildOk validatorOk :=
  h

theorem ay_saig_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_saig_archive_manifest validatorOk archiveOk :=
  h

theorem ay_saig_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_saig_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_saig_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_saig_audit_transcript fallbackReady audited :=
  h

theorem ay_saig_accepted_sparse_index_intro
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (hf : formula) (hs : sparse) (ht : table) (hm : indexMap) (hd : defaultPolicy)
    (hn : normalized) (hrg : rangeLedger) (hr : replay) (hc : checker)
    (hb : build) (hv : validator) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit :=
  fun r k => k hf hs ht hm hd hn hrg hr hc hb hv ha hfb hau

theorem ay_saig_accepted_sparse_index_sparse
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    sparse :=
  h sparse (fun _ hs _ _ _ _ _ _ _ _ _ _ _ _ => hs)

theorem ay_saig_accepted_sparse_index_table
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    table :=
  h table (fun _ _ ht _ _ _ _ _ _ _ _ _ _ _ => ht)

theorem ay_saig_accepted_sparse_index_map
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    indexMap :=
  h indexMap (fun _ _ _ hm _ _ _ _ _ _ _ _ _ _ => hm)

theorem ay_saig_accepted_sparse_index_default_policy
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    defaultPolicy :=
  h defaultPolicy (fun _ _ _ _ hd _ _ _ _ _ _ _ _ _ => hd)

theorem ay_saig_accepted_sparse_index_normalized
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    normalized :=
  h normalized (fun _ _ _ _ _ hn _ _ _ _ _ _ _ _ => hn)

theorem ay_saig_accepted_sparse_index_range_ledger
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    rangeLedger :=
  h rangeLedger (fun _ _ _ _ _ _ hrg _ _ _ _ _ _ _ => hrg)

theorem ay_saig_accepted_sparse_index_replay
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    replay :=
  h replay (fun _ _ _ _ _ _ _ hr _ _ _ _ _ _ => hr)

theorem ay_saig_accepted_sparse_index_checker
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    checker :=
  h checker (fun _ _ _ _ _ _ _ _ hc _ _ _ _ _ => hc)

theorem ay_saig_accepted_sparse_index_validator
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_saig_accepted_sparse_index_archive
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ ha _ _ => ha)

theorem ay_saig_accepted_sparse_index_audit
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_saig_public_sat_intro
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hr : everyOriginalClauseSatisfied)
    (ht : tableOk) (hm : indexMapOk) (hrg : rangeLedgerOk) (hc : checkerOk)
    (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited :=
  ay_saig_conj_intro ha
    (ay_saig_conj_intro hn
      (ay_saig_conj_intro hr
        (ay_saig_conj_intro ht
          (ay_saig_conj_intro hm
            (ay_saig_conj_intro hrg
              (ay_saig_conj_intro hc
                (ay_saig_conj_intro hv
                  (ay_saig_conj_intro har hau))))))))

theorem ay_saig_public_sat_requires_sparse_index_guard
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    accepted :=
  ay_saig_conj_left h

theorem ay_saig_public_sat_normalized_assignment
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    normalizedAssignment :=
  ay_saig_conj_left (ay_saig_conj_right h)

theorem ay_saig_public_sat_original_clause_satisfaction
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    everyOriginalClauseSatisfied :=
  ay_saig_conj_left (ay_saig_conj_right (ay_saig_conj_right h))

theorem ay_saig_public_sat_index_table
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    tableOk :=
  ay_saig_conj_left
    (ay_saig_conj_right (ay_saig_conj_right (ay_saig_conj_right h)))

theorem ay_saig_public_sat_index_map
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    indexMapOk :=
  ay_saig_conj_left
    (ay_saig_conj_right
      (ay_saig_conj_right (ay_saig_conj_right (ay_saig_conj_right h))))

theorem ay_saig_public_sat_range_ledger
    {accepted normalizedAssignment everyOriginalClauseSatisfied tableOk indexMapOk
     rangeLedgerOk checkerOk validatorOk archiveOk audited : Prop}
    (h : ay_saig_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      tableOk indexMapOk rangeLedgerOk checkerOk validatorOk archiveOk audited) :
    rangeLedgerOk :=
  ay_saig_conj_left
    (ay_saig_conj_right
      (ay_saig_conj_right
        (ay_saig_conj_right (ay_saig_conj_right (ay_saig_conj_right h)))))

theorem ay_saig_accepted_sparse_indexes_publish_sat
    {formula sparse table indexMap defaultPolicy normalized rangeLedger replay checker
     build validator archive fallback audit : Prop}
    (h : ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
      normalized rangeLedger replay checker build validator archive fallback audit) :
    ay_saig_public_sat
      (ay_saig_accepted_sparse_index formula sparse table indexMap defaultPolicy
        normalized rangeLedger replay checker build validator archive fallback audit)
      normalized replay table indexMap rangeLedger checker validator archive audit :=
  ay_saig_public_sat_intro h
    (ay_saig_accepted_sparse_index_normalized h)
    (ay_saig_accepted_sparse_index_replay h)
    (ay_saig_accepted_sparse_index_table h)
    (ay_saig_accepted_sparse_index_map h)
    (ay_saig_accepted_sparse_index_range_ledger h)
    (ay_saig_accepted_sparse_index_checker h)
    (ay_saig_accepted_sparse_index_validator h)
    (ay_saig_accepted_sparse_index_archive h)
    (ay_saig_accepted_sparse_index_audit h)

theorem ay_saig_out_of_range_or_stale_index_forces_no_claim_or_recompute
    {outOfRangeIndex staleIndex noClaim recompute : Prop}
    (hbad : ay_saig_disj outOfRangeIndex staleIndex)
    (hrange : outOfRangeIndex -> noClaim)
    (hstale : staleIndex -> recompute) :
    ay_saig_disj (ay_saig_no_claim_diagnostic noClaim)
      (ay_saig_recompute_obligation recompute) :=
  hbad
    (ay_saig_disj (ay_saig_no_claim_diagnostic noClaim)
      (ay_saig_recompute_obligation recompute))
    (fun ho => ay_saig_disj_left (hrange ho))
    (fun hs => ay_saig_disj_right (hstale hs))

theorem ay_saig_no_claim_intro {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  h

theorem ay_saig_recompute_intro {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  h

theorem ay_saig_sparse_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_index_table_mismatch_recompute {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  ay_saig_recompute_intro h

theorem ay_saig_index_map_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_default_policy_mismatch_recompute {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  ay_saig_recompute_intro h

theorem ay_saig_normalization_mismatch_recompute {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  ay_saig_recompute_intro h

theorem ay_saig_replay_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_checker_mismatch_recompute {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  ay_saig_recompute_intro h

theorem ay_saig_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_saig_recompute_obligation reason :=
  ay_saig_recompute_intro h

theorem ay_saig_validator_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_saig_no_claim_diagnostic reason :=
  ay_saig_no_claim_intro h

theorem ay_saig_failed_sparse_index_guard_cannot_bless_sat_publication
    {failedGuard publicSat noClaim : Prop}
    (hf : failedGuard -> noClaim) (hfailed : failedGuard) :
    ay_saig_no_claim_diagnostic noClaim :=
  hf hfailed

theorem ay_saig_failed_sparse_index_guard_forces_recompute
    {failedGuard recompute : Prop}
    (hf : failedGuard -> recompute) (hfailed : failedGuard) :
    ay_saig_recompute_obligation recompute :=
  hf hfailed

/-!
  SAT-COMP/ay DIMACS variable-map guard.

  This self-contained package models the SAT-only obligations for interpreting
  an internal solver assignment through the original DIMACS variable map.
-/

def ay_vmg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_vmg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_vmg_equiv (p q : Prop) : Prop :=
  ay_vmg_conj (p -> q) (q -> p)

def ay_vmg_original_dimacs_fingerprint
    (assignmentArtifact originalFingerprintOk : Prop) : Prop :=
  assignmentArtifact -> originalFingerprintOk

def ay_vmg_internal_formula_fingerprint
    (originalFingerprintOk internalFingerprintOk : Prop) : Prop :=
  originalFingerprintOk -> internalFingerprintOk

def ay_vmg_variable_map_digest
    (internalFingerprintOk variableMapOk : Prop) : Prop :=
  internalFingerprintOk -> variableMapOk

def ay_vmg_inverse_map_witness (variableMapOk inverseMapOk : Prop) : Prop :=
  variableMapOk -> inverseMapOk

def ay_vmg_assignment_artifact_digest
    (inverseMapOk assignmentArtifactOk : Prop) : Prop :=
  inverseMapOk -> assignmentArtifactOk

def ay_vmg_mapped_assignment_replay
    (assignmentArtifactOk mappedAssignmentOk : Prop) : Prop :=
  assignmentArtifactOk -> mappedAssignmentOk

def ay_vmg_original_clause_satisfaction_replay
    (mappedAssignmentOk originalClausesSatisfied : Prop) : Prop :=
  mappedAssignmentOk -> originalClausesSatisfied

def ay_vmg_parser_transcript
    (originalClausesSatisfied parserOk : Prop) : Prop :=
  originalClausesSatisfied -> parserOk

def ay_vmg_solver_build_evidence (parserOk buildOk : Prop) : Prop :=
  parserOk -> buildOk

def ay_vmg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_vmg_fallback_no_claim_path (validatorOk fallbackReady : Prop) : Prop :=
  validatorOk -> fallbackReady

def ay_vmg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_vmg_accepted_variable_map
    (originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop) : Prop :=
  forall r : Prop,
    (originalFp -> internalFp -> mapDigest -> inverseMap -> assignmentArtifact ->
      mappedReplay -> originalReplay -> parser -> build -> validator -> fallback -> audit ->
      r) -> r

def ay_vmg_public_sat
    (accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop) : Prop :=
  ay_vmg_conj accepted
    (ay_vmg_conj originalDimacsAssignment
      (ay_vmg_conj inverseMapOk
        (ay_vmg_conj preservedAgreement
          (ay_vmg_conj originalClausesSatisfied
            (ay_vmg_conj validatorOk audited)))))

def ay_vmg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_vmg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_vmg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_vmg_conj p q :=
  fun r h => h hp hq

theorem ay_vmg_conj_left {p q : Prop} (h : ay_vmg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_vmg_conj_right {p q : Prop} (h : ay_vmg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_vmg_conj_left h)

theorem ay_vmg_disj_left {p q : Prop} (hp : p) : ay_vmg_disj p q :=
  fun r hl _ => hl hp

theorem ay_vmg_disj_right {p q : Prop} (hq : q) : ay_vmg_disj p q :=
  fun r _ hr => hr hq

theorem ay_vmg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_vmg_equiv p q :=
  ay_vmg_conj_intro hpq hqp

theorem ay_vmg_equiv_forward {p q : Prop} (h : ay_vmg_equiv p q) : p -> q :=
  ay_vmg_conj_left h

theorem ay_vmg_equiv_backward {p q : Prop} (h : ay_vmg_equiv p q) : q -> p :=
  ay_vmg_conj_right h

theorem ay_vmg_original_dimacs_fingerprint_intro
    {assignmentArtifact originalFingerprintOk : Prop}
    (h : assignmentArtifact -> originalFingerprintOk) :
    ay_vmg_original_dimacs_fingerprint assignmentArtifact originalFingerprintOk :=
  h

theorem ay_vmg_internal_formula_fingerprint_intro
    {originalFingerprintOk internalFingerprintOk : Prop}
    (h : originalFingerprintOk -> internalFingerprintOk) :
    ay_vmg_internal_formula_fingerprint originalFingerprintOk internalFingerprintOk :=
  h

theorem ay_vmg_variable_map_digest_intro
    {internalFingerprintOk variableMapOk : Prop}
    (h : internalFingerprintOk -> variableMapOk) :
    ay_vmg_variable_map_digest internalFingerprintOk variableMapOk :=
  h

theorem ay_vmg_inverse_map_witness_intro {variableMapOk inverseMapOk : Prop}
    (h : variableMapOk -> inverseMapOk) :
    ay_vmg_inverse_map_witness variableMapOk inverseMapOk :=
  h

theorem ay_vmg_assignment_artifact_digest_intro
    {inverseMapOk assignmentArtifactOk : Prop}
    (h : inverseMapOk -> assignmentArtifactOk) :
    ay_vmg_assignment_artifact_digest inverseMapOk assignmentArtifactOk :=
  h

theorem ay_vmg_mapped_assignment_replay_intro
    {assignmentArtifactOk mappedAssignmentOk : Prop}
    (h : assignmentArtifactOk -> mappedAssignmentOk) :
    ay_vmg_mapped_assignment_replay assignmentArtifactOk mappedAssignmentOk :=
  h

theorem ay_vmg_original_clause_satisfaction_replay_intro
    {mappedAssignmentOk originalClausesSatisfied : Prop}
    (h : mappedAssignmentOk -> originalClausesSatisfied) :
    ay_vmg_original_clause_satisfaction_replay mappedAssignmentOk
      originalClausesSatisfied :=
  h

theorem ay_vmg_parser_transcript_intro {originalClausesSatisfied parserOk : Prop}
    (h : originalClausesSatisfied -> parserOk) :
    ay_vmg_parser_transcript originalClausesSatisfied parserOk :=
  h

theorem ay_vmg_solver_build_evidence_intro {parserOk buildOk : Prop}
    (h : parserOk -> buildOk) :
    ay_vmg_solver_build_evidence parserOk buildOk :=
  h

theorem ay_vmg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_vmg_validator_gate buildOk validatorOk :=
  h

theorem ay_vmg_fallback_no_claim_path_intro {validatorOk fallbackReady : Prop}
    (h : validatorOk -> fallbackReady) :
    ay_vmg_fallback_no_claim_path validatorOk fallbackReady :=
  h

theorem ay_vmg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_vmg_audit_transcript fallbackReady audited :=
  h

theorem ay_vmg_accepted_variable_map_intro
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (hof : originalFp) (hif : internalFp) (hm : mapDigest) (hi : inverseMap)
    (ha : assignmentArtifact) (hmr : mappedReplay) (hor : originalReplay)
    (hp : parser) (hb : build) (hv : validator) (hfb : fallback) (hau : audit) :
    ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit :=
  fun r k => k hof hif hm hi ha hmr hor hp hb hv hfb hau

theorem ay_vmg_accepted_variable_map_original_fp
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    originalFp :=
  h originalFp (fun hof _ _ _ _ _ _ _ _ _ _ _ => hof)

theorem ay_vmg_accepted_variable_map_map_digest
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    mapDigest :=
  h mapDigest (fun _ _ hm _ _ _ _ _ _ _ _ _ => hm)

theorem ay_vmg_accepted_variable_map_inverse
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    inverseMap :=
  h inverseMap (fun _ _ _ hi _ _ _ _ _ _ _ _ => hi)

theorem ay_vmg_accepted_variable_map_assignment
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    assignmentArtifact :=
  h assignmentArtifact (fun _ _ _ _ ha _ _ _ _ _ _ _ => ha)

theorem ay_vmg_accepted_variable_map_mapped_replay
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    mappedReplay :=
  h mappedReplay (fun _ _ _ _ _ hmr _ _ _ _ _ _ => hmr)

theorem ay_vmg_accepted_variable_map_original_replay
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    originalReplay :=
  h originalReplay (fun _ _ _ _ _ _ hor _ _ _ _ _ => hor)

theorem ay_vmg_accepted_variable_map_parser
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    parser :=
  h parser (fun _ _ _ _ _ _ _ hp _ _ _ _ => hp)

theorem ay_vmg_accepted_variable_map_validator
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ => hv)

theorem ay_vmg_accepted_variable_map_audit
    {originalFp internalFp mapDigest inverseMap assignmentArtifact mappedReplay
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      assignmentArtifact mappedReplay originalReplay parser build validator fallback audit) :
    audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_vmg_public_sat_intro
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (ha : accepted) (hd : originalDimacsAssignment) (hi : inverseMapOk)
    (hp : preservedAgreement) (hc : originalClausesSatisfied) (hv : validatorOk)
    (hau : audited) :
    ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk preservedAgreement
      originalClausesSatisfied validatorOk audited :=
  ay_vmg_conj_intro ha
    (ay_vmg_conj_intro hd
      (ay_vmg_conj_intro hi
        (ay_vmg_conj_intro hp
          (ay_vmg_conj_intro hc (ay_vmg_conj_intro hv hau)))))

theorem ay_vmg_public_sat_requires_variable_map_guard
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) : accepted :=
  ay_vmg_conj_left h

theorem ay_vmg_public_sat_original_assignment
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) :
    originalDimacsAssignment :=
  ay_vmg_conj_left (ay_vmg_conj_right h)

theorem ay_vmg_public_sat_inverse_map
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) : inverseMapOk :=
  ay_vmg_conj_left (ay_vmg_conj_right (ay_vmg_conj_right h))

theorem ay_vmg_public_sat_preserved_agreement
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) : preservedAgreement :=
  ay_vmg_conj_left
    (ay_vmg_conj_right (ay_vmg_conj_right (ay_vmg_conj_right h)))

theorem ay_vmg_public_sat_original_clauses
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) :
    originalClausesSatisfied :=
  ay_vmg_conj_left
    (ay_vmg_conj_right
      (ay_vmg_conj_right (ay_vmg_conj_right (ay_vmg_conj_right h))))

theorem ay_vmg_accepted_variable_map_turns_internal_assignment_into_original_sat
    {originalFp internalFp mapDigest inverseMap originalAssignment preservedAgreement
     originalClausesSatisfied parser build validator fallback audit : Prop}
    (h : ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
      originalAssignment preservedAgreement originalClausesSatisfied parser build validator
      fallback audit) :
    ay_vmg_public_sat
      (ay_vmg_accepted_variable_map originalFp internalFp mapDigest inverseMap
        originalAssignment preservedAgreement originalClausesSatisfied parser build validator
        fallback audit)
      originalAssignment inverseMap preservedAgreement originalClausesSatisfied validator audit :=
  ay_vmg_public_sat_intro
    h
    (ay_vmg_accepted_variable_map_assignment h)
    (ay_vmg_accepted_variable_map_inverse h)
    (ay_vmg_accepted_variable_map_mapped_replay h)
    (ay_vmg_accepted_variable_map_original_replay h)
    (ay_vmg_accepted_variable_map_validator h)
    (ay_vmg_accepted_variable_map_audit h)

theorem ay_vmg_inverse_map_and_preserved_variables_required_for_publication
    {accepted originalDimacsAssignment inverseMapOk preservedAgreement
     originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_vmg_public_sat accepted originalDimacsAssignment inverseMapOk
      preservedAgreement originalClausesSatisfied validatorOk audited) :
    ay_vmg_conj inverseMapOk preservedAgreement :=
  ay_vmg_conj_intro
    (ay_vmg_public_sat_inverse_map h)
    (ay_vmg_public_sat_preserved_agreement h)

theorem ay_vmg_no_claim_intro {reason : Prop} (h : reason) :
    ay_vmg_no_claim_diagnostic reason :=
  h

theorem ay_vmg_recompute_intro {reason : Prop} (h : reason) :
    ay_vmg_recompute_obligation reason :=
  h

theorem ay_vmg_map_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_vmg_no_claim_diagnostic mismatch :=
  ay_vmg_no_claim_intro h

theorem ay_vmg_assignment_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_vmg_recompute_obligation mismatch :=
  ay_vmg_recompute_intro h

theorem ay_vmg_parser_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_vmg_no_claim_diagnostic mismatch :=
  ay_vmg_no_claim_intro h

theorem ay_vmg_replay_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_vmg_recompute_obligation mismatch :=
  ay_vmg_recompute_intro h

theorem ay_vmg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_vmg_recompute_obligation mismatch :=
  ay_vmg_recompute_intro h

theorem ay_vmg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_vmg_no_claim_diagnostic mismatch :=
  ay_vmg_no_claim_intro h

theorem ay_vmg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_vmg_no_claim_diagnostic mismatch :=
  ay_vmg_no_claim_intro h

theorem ay_vmg_failed_variable_map_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_vmg_no_claim_diagnostic failure)
    (noBless : ay_vmg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_vmg_failed_variable_map_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_vmg_recompute_obligation failure)
    (hfailure : failure) :
    ay_vmg_recompute_obligation failure :=
  fallback hfailure

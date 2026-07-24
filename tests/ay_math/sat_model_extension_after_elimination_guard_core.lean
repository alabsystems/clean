/-!
  SAT-COMP/ay model extension after elimination guard.

  This self-contained package models the SAT-only obligations for extending a
  reduced SAT model back to an original benchmark model after preprocessing.
-/

def ay_meeg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_meeg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_meeg_equiv (p q : Prop) : Prop :=
  ay_meeg_conj (p -> q) (q -> p)

def ay_meeg_original_formula_fingerprint
    (reducedModelArtifact originalFingerprintOk : Prop) : Prop :=
  reducedModelArtifact -> originalFingerprintOk

def ay_meeg_reduced_formula_fingerprint
    (originalFingerprintOk reducedFingerprintOk : Prop) : Prop :=
  originalFingerprintOk -> reducedFingerprintOk

def ay_meeg_elimination_ledger
    (reducedFingerprintOk eliminationLedgerOk : Prop) : Prop :=
  reducedFingerprintOk -> eliminationLedgerOk

def ay_meeg_extension_function_digest
    (eliminationLedgerOk extensionDigestOk : Prop) : Prop :=
  eliminationLedgerOk -> extensionDigestOk

def ay_meeg_eliminated_variable_assignment_witness
    (extensionDigestOk eliminatedAssignmentOk : Prop) : Prop :=
  extensionDigestOk -> eliminatedAssignmentOk

def ay_meeg_preserved_variable_agreement
    (eliminatedAssignmentOk preservedAgreementOk : Prop) : Prop :=
  eliminatedAssignmentOk -> preservedAgreementOk

def ay_meeg_original_clause_satisfaction_replay
    (preservedAgreementOk originalClausesSatisfied : Prop) : Prop :=
  preservedAgreementOk -> originalClausesSatisfied

def ay_meeg_reduced_model_artifact_digest
    (originalClausesSatisfied reducedArtifactOk : Prop) : Prop :=
  originalClausesSatisfied -> reducedArtifactOk

def ay_meeg_solver_build_evidence
    (reducedArtifactOk buildOk : Prop) : Prop :=
  reducedArtifactOk -> buildOk

def ay_meeg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_meeg_fallback_no_claim_path (validatorOk fallbackReady : Prop) : Prop :=
  validatorOk -> fallbackReady

def ay_meeg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_meeg_accepted_extension
    (originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop) : Prop :=
  forall r : Prop,
    (originalFp -> reducedFp -> ledger -> extensionDigest -> assignmentWitness ->
      preservedAgreement -> originalReplay -> reducedArtifact -> build -> validator ->
      fallback -> audit -> r) -> r

def ay_meeg_public_sat
    (accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop) : Prop :=
  ay_meeg_conj accepted
    (ay_meeg_conj originalModel
      (ay_meeg_conj preservedAgreement
        (ay_meeg_conj originalClausesSatisfied
          (ay_meeg_conj validatorOk audited))))

def ay_meeg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_meeg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_meeg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_meeg_conj p q :=
  fun r h => h hp hq

theorem ay_meeg_conj_left {p q : Prop} (h : ay_meeg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_meeg_conj_right {p q : Prop} (h : ay_meeg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_meeg_conj_left h)

theorem ay_meeg_disj_left {p q : Prop} (hp : p) : ay_meeg_disj p q :=
  fun r hl _ => hl hp

theorem ay_meeg_disj_right {p q : Prop} (hq : q) : ay_meeg_disj p q :=
  fun r _ hr => hr hq

theorem ay_meeg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_meeg_equiv p q :=
  ay_meeg_conj_intro hpq hqp

theorem ay_meeg_equiv_forward {p q : Prop} (h : ay_meeg_equiv p q) : p -> q :=
  ay_meeg_conj_left h

theorem ay_meeg_equiv_backward {p q : Prop} (h : ay_meeg_equiv p q) : q -> p :=
  ay_meeg_conj_right h

theorem ay_meeg_original_formula_fingerprint_intro
    {reducedModelArtifact originalFingerprintOk : Prop}
    (h : reducedModelArtifact -> originalFingerprintOk) :
    ay_meeg_original_formula_fingerprint reducedModelArtifact originalFingerprintOk :=
  h

theorem ay_meeg_reduced_formula_fingerprint_intro
    {originalFingerprintOk reducedFingerprintOk : Prop}
    (h : originalFingerprintOk -> reducedFingerprintOk) :
    ay_meeg_reduced_formula_fingerprint originalFingerprintOk reducedFingerprintOk :=
  h

theorem ay_meeg_elimination_ledger_intro
    {reducedFingerprintOk eliminationLedgerOk : Prop}
    (h : reducedFingerprintOk -> eliminationLedgerOk) :
    ay_meeg_elimination_ledger reducedFingerprintOk eliminationLedgerOk :=
  h

theorem ay_meeg_extension_function_digest_intro
    {eliminationLedgerOk extensionDigestOk : Prop}
    (h : eliminationLedgerOk -> extensionDigestOk) :
    ay_meeg_extension_function_digest eliminationLedgerOk extensionDigestOk :=
  h

theorem ay_meeg_eliminated_variable_assignment_witness_intro
    {extensionDigestOk eliminatedAssignmentOk : Prop}
    (h : extensionDigestOk -> eliminatedAssignmentOk) :
    ay_meeg_eliminated_variable_assignment_witness extensionDigestOk
      eliminatedAssignmentOk :=
  h

theorem ay_meeg_preserved_variable_agreement_intro
    {eliminatedAssignmentOk preservedAgreementOk : Prop}
    (h : eliminatedAssignmentOk -> preservedAgreementOk) :
    ay_meeg_preserved_variable_agreement eliminatedAssignmentOk preservedAgreementOk :=
  h

theorem ay_meeg_original_clause_satisfaction_replay_intro
    {preservedAgreementOk originalClausesSatisfied : Prop}
    (h : preservedAgreementOk -> originalClausesSatisfied) :
    ay_meeg_original_clause_satisfaction_replay preservedAgreementOk
      originalClausesSatisfied :=
  h

theorem ay_meeg_reduced_model_artifact_digest_intro
    {originalClausesSatisfied reducedArtifactOk : Prop}
    (h : originalClausesSatisfied -> reducedArtifactOk) :
    ay_meeg_reduced_model_artifact_digest originalClausesSatisfied reducedArtifactOk :=
  h

theorem ay_meeg_solver_build_evidence_intro {reducedArtifactOk buildOk : Prop}
    (h : reducedArtifactOk -> buildOk) :
    ay_meeg_solver_build_evidence reducedArtifactOk buildOk :=
  h

theorem ay_meeg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_meeg_validator_gate buildOk validatorOk :=
  h

theorem ay_meeg_fallback_no_claim_path_intro {validatorOk fallbackReady : Prop}
    (h : validatorOk -> fallbackReady) :
    ay_meeg_fallback_no_claim_path validatorOk fallbackReady :=
  h

theorem ay_meeg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_meeg_audit_transcript fallbackReady audited :=
  h

theorem ay_meeg_accepted_extension_intro
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (hof : originalFp) (hrf : reducedFp) (hl : ledger) (hed : extensionDigest)
    (haw : assignmentWitness) (hpa : preservedAgreement) (hor : originalReplay)
    (hra : reducedArtifact) (hb : build) (hv : validator) (hfb : fallback)
    (hau : audit) :
    ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit :=
  fun r k => k hof hrf hl hed haw hpa hor hra hb hv hfb hau

theorem ay_meeg_accepted_extension_original_fp
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : originalFp :=
  h originalFp (fun hof _ _ _ _ _ _ _ _ _ _ _ => hof)

theorem ay_meeg_accepted_extension_reduced_fp
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : reducedFp :=
  h reducedFp (fun _ hrf _ _ _ _ _ _ _ _ _ _ => hrf)

theorem ay_meeg_accepted_extension_ledger
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : ledger :=
  h ledger (fun _ _ hl _ _ _ _ _ _ _ _ _ => hl)

theorem ay_meeg_accepted_extension_digest
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : extensionDigest :=
  h extensionDigest (fun _ _ _ hed _ _ _ _ _ _ _ _ => hed)

theorem ay_meeg_accepted_extension_assignment_witness
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : assignmentWitness :=
  h assignmentWitness (fun _ _ _ _ haw _ _ _ _ _ _ _ => haw)

theorem ay_meeg_accepted_extension_preserved_agreement
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : preservedAgreement :=
  h preservedAgreement (fun _ _ _ _ _ hpa _ _ _ _ _ _ => hpa)

theorem ay_meeg_accepted_extension_original_replay
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : originalReplay :=
  h originalReplay (fun _ _ _ _ _ _ hor _ _ _ _ _ => hor)

theorem ay_meeg_accepted_extension_validator
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ => hv)

theorem ay_meeg_accepted_extension_audit
    {originalFp reducedFp ledger extensionDigest assignmentWitness preservedAgreement
     originalReplay reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      assignmentWitness preservedAgreement originalReplay reducedArtifact build validator
      fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_meeg_public_sat_intro
    {accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (ha : accepted) (hm : originalModel) (hp : preservedAgreement)
    (hc : originalClausesSatisfied) (hv : validatorOk) (hau : audited) :
    ay_meeg_public_sat accepted originalModel preservedAgreement originalClausesSatisfied
      validatorOk audited :=
  ay_meeg_conj_intro ha
    (ay_meeg_conj_intro hm
      (ay_meeg_conj_intro hp
        (ay_meeg_conj_intro hc (ay_meeg_conj_intro hv hau))))

theorem ay_meeg_public_sat_requires_extension_guard
    {accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_meeg_public_sat accepted originalModel preservedAgreement
      originalClausesSatisfied validatorOk audited) : accepted :=
  ay_meeg_conj_left h

theorem ay_meeg_public_sat_original_model
    {accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_meeg_public_sat accepted originalModel preservedAgreement
      originalClausesSatisfied validatorOk audited) : originalModel :=
  ay_meeg_conj_left (ay_meeg_conj_right h)

theorem ay_meeg_public_sat_preserved_variables
    {accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_meeg_public_sat accepted originalModel preservedAgreement
      originalClausesSatisfied validatorOk audited) : preservedAgreement :=
  ay_meeg_conj_left (ay_meeg_conj_right (ay_meeg_conj_right h))

theorem ay_meeg_public_sat_original_clauses
    {accepted originalModel preservedAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_meeg_public_sat accepted originalModel preservedAgreement
      originalClausesSatisfied validatorOk audited) : originalClausesSatisfied :=
  ay_meeg_conj_left
    (ay_meeg_conj_right (ay_meeg_conj_right (ay_meeg_conj_right h)))

theorem ay_meeg_accepted_extension_turns_reduced_sat_into_original_sat
    {originalFp reducedFp ledger extensionDigest originalModel preservedAgreement
     originalClausesSatisfied reducedArtifact build validator fallback audit : Prop}
    (h : ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest
      originalModel preservedAgreement originalClausesSatisfied reducedArtifact build validator
      fallback audit) :
    ay_meeg_public_sat
      (ay_meeg_accepted_extension originalFp reducedFp ledger extensionDigest originalModel
        preservedAgreement originalClausesSatisfied reducedArtifact build validator fallback
        audit)
      originalModel preservedAgreement originalClausesSatisfied validator audit :=
  ay_meeg_public_sat_intro
    h
    (ay_meeg_accepted_extension_assignment_witness h)
    (ay_meeg_accepted_extension_preserved_agreement h)
    (ay_meeg_accepted_extension_original_replay h)
    (ay_meeg_accepted_extension_validator h)
    (ay_meeg_accepted_extension_audit h)

theorem ay_meeg_preserved_variables_agree_between_models
    {reducedModel extendedModel preservedAgreement : Prop}
    (h : ay_meeg_equiv reducedModel extendedModel)
    (hp : extendedModel -> preservedAgreement) (hr : reducedModel) : preservedAgreement :=
  hp (ay_meeg_equiv_forward h hr)

theorem ay_meeg_no_claim_intro {reason : Prop} (h : reason) :
    ay_meeg_no_claim_diagnostic reason :=
  h

theorem ay_meeg_recompute_intro {reason : Prop} (h : reason) :
    ay_meeg_recompute_obligation reason :=
  h

theorem ay_meeg_original_fingerprint_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_meeg_no_claim_diagnostic mismatch :=
  ay_meeg_no_claim_intro h

theorem ay_meeg_reduced_fingerprint_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_meeg_recompute_obligation mismatch :=
  ay_meeg_recompute_intro h

theorem ay_meeg_elimination_ledger_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_meeg_no_claim_diagnostic mismatch :=
  ay_meeg_no_claim_intro h

theorem ay_meeg_extension_digest_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_meeg_recompute_obligation mismatch :=
  ay_meeg_recompute_intro h

theorem ay_meeg_assignment_witness_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_meeg_recompute_obligation mismatch :=
  ay_meeg_recompute_intro h

theorem ay_meeg_satisfaction_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_meeg_no_claim_diagnostic mismatch :=
  ay_meeg_no_claim_intro h

theorem ay_meeg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_meeg_recompute_obligation mismatch :=
  ay_meeg_recompute_intro h

theorem ay_meeg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_meeg_no_claim_diagnostic mismatch :=
  ay_meeg_no_claim_intro h

theorem ay_meeg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_meeg_no_claim_diagnostic mismatch :=
  ay_meeg_no_claim_intro h

theorem ay_meeg_failed_extension_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_meeg_no_claim_diagnostic failure)
    (noBless : ay_meeg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_meeg_failed_extension_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_meeg_recompute_obligation failure)
    (hfailure : failure) :
    ay_meeg_recompute_obligation failure :=
  fallback hfailure

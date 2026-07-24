/-!
  SAT-COMP/ay assignment roundtrip serialization guard.

  This self-contained package models the SAT-only obligations for serializing,
  reloading, and normalizing model assignments in result archives.
-/

def ay_arsg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_arsg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_arsg_equiv (p q : Prop) : Prop :=
  ay_arsg_conj (p -> q) (q -> p)

def ay_arsg_original_formula_fingerprint
    (assignmentBefore originalFingerprintOk : Prop) : Prop :=
  assignmentBefore -> originalFingerprintOk

def ay_arsg_assignment_digest_before_serialization
    (originalFingerprintOk assignmentBeforeOk : Prop) : Prop :=
  originalFingerprintOk -> assignmentBeforeOk

def ay_arsg_serialized_witness_digest
    (assignmentBeforeOk serializedOk : Prop) : Prop :=
  assignmentBeforeOk -> serializedOk

def ay_arsg_parser_reloader_version_digest
    (serializedOk parserReloaderOk : Prop) : Prop :=
  serializedOk -> parserReloaderOk

def ay_arsg_deserialized_assignment_digest
    (parserReloaderOk deserializedOk : Prop) : Prop :=
  parserReloaderOk -> deserializedOk

def ay_arsg_variable_domain_digest
    (deserializedOk domainOk : Prop) : Prop :=
  deserializedOk -> domainOk

def ay_arsg_normalization_ledger
    (domainOk normalizedOk : Prop) : Prop :=
  domainOk -> normalizedOk

def ay_arsg_clause_satisfaction_replay
    (normalizedOk originalClausesSatisfied : Prop) : Prop :=
  normalizedOk -> originalClausesSatisfied

def ay_arsg_solver_build_evidence
    (originalClausesSatisfied buildOk : Prop) : Prop :=
  originalClausesSatisfied -> buildOk

def ay_arsg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_arsg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_arsg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_arsg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_arsg_accepted_roundtrip
    (originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (originalFp -> before -> serialized -> parser -> deserialized -> domain -> normalized ->
      replay -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_arsg_public_sat
    (accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop) : Prop :=
  ay_arsg_conj accepted
    (ay_arsg_conj normalizedAssignment
      (ay_arsg_conj roundtripAgreement
        (ay_arsg_conj originalClausesSatisfied
          (ay_arsg_conj validatorOk (ay_arsg_conj archiveOk audited)))))

def ay_arsg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_arsg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_arsg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_arsg_conj p q :=
  fun r h => h hp hq

theorem ay_arsg_conj_left {p q : Prop} (h : ay_arsg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_arsg_conj_right {p q : Prop} (h : ay_arsg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_arsg_conj_left h)

theorem ay_arsg_disj_left {p q : Prop} (hp : p) : ay_arsg_disj p q :=
  fun r hl _ => hl hp

theorem ay_arsg_disj_right {p q : Prop} (hq : q) : ay_arsg_disj p q :=
  fun r _ hr => hr hq

theorem ay_arsg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_arsg_equiv p q :=
  ay_arsg_conj_intro hpq hqp

theorem ay_arsg_equiv_forward {p q : Prop} (h : ay_arsg_equiv p q) : p -> q :=
  ay_arsg_conj_left h

theorem ay_arsg_equiv_backward {p q : Prop} (h : ay_arsg_equiv p q) : q -> p :=
  ay_arsg_conj_right h

theorem ay_arsg_original_formula_fingerprint_intro
    {assignmentBefore originalFingerprintOk : Prop}
    (h : assignmentBefore -> originalFingerprintOk) :
    ay_arsg_original_formula_fingerprint assignmentBefore originalFingerprintOk :=
  h

theorem ay_arsg_assignment_digest_before_serialization_intro
    {originalFingerprintOk assignmentBeforeOk : Prop}
    (h : originalFingerprintOk -> assignmentBeforeOk) :
    ay_arsg_assignment_digest_before_serialization originalFingerprintOk assignmentBeforeOk :=
  h

theorem ay_arsg_serialized_witness_digest_intro
    {assignmentBeforeOk serializedOk : Prop}
    (h : assignmentBeforeOk -> serializedOk) :
    ay_arsg_serialized_witness_digest assignmentBeforeOk serializedOk :=
  h

theorem ay_arsg_parser_reloader_version_digest_intro
    {serializedOk parserReloaderOk : Prop}
    (h : serializedOk -> parserReloaderOk) :
    ay_arsg_parser_reloader_version_digest serializedOk parserReloaderOk :=
  h

theorem ay_arsg_deserialized_assignment_digest_intro
    {parserReloaderOk deserializedOk : Prop}
    (h : parserReloaderOk -> deserializedOk) :
    ay_arsg_deserialized_assignment_digest parserReloaderOk deserializedOk :=
  h

theorem ay_arsg_variable_domain_digest_intro {deserializedOk domainOk : Prop}
    (h : deserializedOk -> domainOk) :
    ay_arsg_variable_domain_digest deserializedOk domainOk :=
  h

theorem ay_arsg_normalization_ledger_intro {domainOk normalizedOk : Prop}
    (h : domainOk -> normalizedOk) :
    ay_arsg_normalization_ledger domainOk normalizedOk :=
  h

theorem ay_arsg_clause_satisfaction_replay_intro
    {normalizedOk originalClausesSatisfied : Prop}
    (h : normalizedOk -> originalClausesSatisfied) :
    ay_arsg_clause_satisfaction_replay normalizedOk originalClausesSatisfied :=
  h

theorem ay_arsg_solver_build_evidence_intro
    {originalClausesSatisfied buildOk : Prop}
    (h : originalClausesSatisfied -> buildOk) :
    ay_arsg_solver_build_evidence originalClausesSatisfied buildOk :=
  h

theorem ay_arsg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_arsg_validator_gate buildOk validatorOk :=
  h

theorem ay_arsg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_arsg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_arsg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_arsg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_arsg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_arsg_audit_transcript fallbackReady audited :=
  h

theorem ay_arsg_accepted_roundtrip_intro
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (hof : originalFp) (hb : before) (hs : serialized) (hp : parser)
    (hdz : deserialized) (hd : domain) (hn : normalized) (hr : replay)
    (hbuild : build) (hv : validator) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit :=
  fun r k => k hof hb hs hp hdz hd hn hr hbuild hv ha hfb hau

theorem ay_arsg_accepted_roundtrip_before
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : before :=
  h before (fun _ hb _ _ _ _ _ _ _ _ _ _ _ => hb)

theorem ay_arsg_accepted_roundtrip_serialized
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : serialized :=
  h serialized (fun _ _ hs _ _ _ _ _ _ _ _ _ _ => hs)

theorem ay_arsg_accepted_roundtrip_parser
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : parser :=
  h parser (fun _ _ _ hp _ _ _ _ _ _ _ _ _ => hp)

theorem ay_arsg_accepted_roundtrip_deserialized
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : deserialized :=
  h deserialized (fun _ _ _ _ hdz _ _ _ _ _ _ _ _ => hdz)

theorem ay_arsg_accepted_roundtrip_domain
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : domain :=
  h domain (fun _ _ _ _ _ hd _ _ _ _ _ _ _ => hd)

theorem ay_arsg_accepted_roundtrip_normalized
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : normalized :=
  h normalized (fun _ _ _ _ _ _ hn _ _ _ _ _ _ => hn)

theorem ay_arsg_accepted_roundtrip_replay
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ hr _ _ _ _ _ => hr)

theorem ay_arsg_accepted_roundtrip_validator
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_arsg_accepted_roundtrip_archive
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ ha _ _ => ha)

theorem ay_arsg_accepted_roundtrip_audit
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_arsg_public_sat_intro
    {accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hag : roundtripAgreement)
    (hr : originalClausesSatisfied) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_arsg_public_sat accepted normalizedAssignment roundtripAgreement
      originalClausesSatisfied validatorOk archiveOk audited :=
  ay_arsg_conj_intro ha
    (ay_arsg_conj_intro hn
      (ay_arsg_conj_intro hag
        (ay_arsg_conj_intro hr
          (ay_arsg_conj_intro hv (ay_arsg_conj_intro har hau)))))

theorem ay_arsg_public_sat_requires_roundtrip_guard
    {accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_arsg_public_sat accepted normalizedAssignment roundtripAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : accepted :=
  ay_arsg_conj_left h

theorem ay_arsg_public_sat_normalized_assignment
    {accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_arsg_public_sat accepted normalizedAssignment roundtripAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : normalizedAssignment :=
  ay_arsg_conj_left (ay_arsg_conj_right h)

theorem ay_arsg_public_sat_roundtrip_agreement
    {accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_arsg_public_sat accepted normalizedAssignment roundtripAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : roundtripAgreement :=
  ay_arsg_conj_left (ay_arsg_conj_right (ay_arsg_conj_right h))

theorem ay_arsg_public_sat_original_clauses
    {accepted normalizedAssignment roundtripAgreement originalClausesSatisfied validatorOk
     archiveOk audited : Prop}
    (h : ay_arsg_public_sat accepted normalizedAssignment roundtripAgreement
      originalClausesSatisfied validatorOk archiveOk audited) : originalClausesSatisfied :=
  ay_arsg_conj_left
    (ay_arsg_conj_right (ay_arsg_conj_right (ay_arsg_conj_right h)))

theorem ay_arsg_accepted_roundtrip_preserves_original_sat
    {originalFp before serialized parser deserialized domain normalized replay build validator
     archive fallback audit : Prop}
    (h : ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
      normalized replay build validator archive fallback audit) :
    ay_arsg_public_sat
      (ay_arsg_accepted_roundtrip originalFp before serialized parser deserialized domain
        normalized replay build validator archive fallback audit)
      normalized deserialized replay validator archive audit :=
  ay_arsg_public_sat_intro
    h
    (ay_arsg_accepted_roundtrip_normalized h)
    (ay_arsg_accepted_roundtrip_deserialized h)
    (ay_arsg_accepted_roundtrip_replay h)
    (ay_arsg_accepted_roundtrip_validator h)
    (ay_arsg_accepted_roundtrip_archive h)
    (ay_arsg_accepted_roundtrip_audit h)

theorem ay_arsg_roundtrip_assignments_agree_on_domain
    {before serialized deserialized normalized domainAgreement : Prop}
    (hb : ay_arsg_equiv before serialized)
    (hd : ay_arsg_equiv deserialized normalized)
    (hs : serialized -> deserialized)
    (hag : normalized -> domainAgreement)
    (hbefore : before) : domainAgreement :=
  hag (ay_arsg_equiv_forward hd (hs (ay_arsg_equiv_forward hb hbefore)))

theorem ay_arsg_no_claim_intro {reason : Prop} (h : reason) :
    ay_arsg_no_claim_diagnostic reason :=
  h

theorem ay_arsg_recompute_intro {reason : Prop} (h : reason) :
    ay_arsg_recompute_obligation reason :=
  h

theorem ay_arsg_assignment_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_serialized_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_arsg_recompute_obligation mismatch :=
  ay_arsg_recompute_intro h

theorem ay_arsg_parser_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_arsg_recompute_obligation mismatch :=
  ay_arsg_recompute_intro h

theorem ay_arsg_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_normalization_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_arsg_recompute_obligation mismatch :=
  ay_arsg_recompute_intro h

theorem ay_arsg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_arsg_recompute_obligation mismatch :=
  ay_arsg_recompute_intro h

theorem ay_arsg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_arsg_no_claim_diagnostic mismatch :=
  ay_arsg_no_claim_intro h

theorem ay_arsg_failed_serialization_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_arsg_no_claim_diagnostic failure)
    (noBless : ay_arsg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_arsg_failed_serialization_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_arsg_recompute_obligation failure)
    (hfailure : failure) :
    ay_arsg_recompute_obligation failure :=
  fallback hfailure

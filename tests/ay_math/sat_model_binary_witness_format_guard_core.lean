/-!
  SAT-COMP/ay binary model-witness format guard.

  This self-contained package models the SAT-only obligations for decoding
  compact binary witnesses before public SAT publication.
-/

def ay_bwfg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_bwfg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_bwfg_equiv (p q : Prop) : Prop :=
  ay_bwfg_conj (p -> q) (q -> p)

def ay_bwfg_original_formula_fingerprint
    (binaryWitness formulaOk : Prop) : Prop :=
  binaryWitness -> formulaOk

def ay_bwfg_binary_witness_digest (formulaOk binaryOk : Prop) : Prop :=
  formulaOk -> binaryOk

def ay_bwfg_decoder_version_digest (binaryOk decoderOk : Prop) : Prop :=
  binaryOk -> decoderOk

def ay_bwfg_byte_order_encoding_manifest (decoderOk encodingOk : Prop) : Prop :=
  decoderOk -> encodingOk

def ay_bwfg_decoded_assignment_digest (encodingOk decodedOk : Prop) : Prop :=
  encodingOk -> decodedOk

def ay_bwfg_variable_domain_digest (decodedOk domainOk : Prop) : Prop :=
  decodedOk -> domainOk

def ay_bwfg_normalization_ledger (domainOk normalizedOk : Prop) : Prop :=
  domainOk -> normalizedOk

def ay_bwfg_clause_satisfaction_replay
    (normalizedOk everyOriginalClauseSatisfied : Prop) : Prop :=
  normalizedOk -> everyOriginalClauseSatisfied

def ay_bwfg_checker_transcript
    (everyOriginalClauseSatisfied checkerOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> checkerOk

def ay_bwfg_solver_build_evidence (checkerOk buildOk : Prop) : Prop :=
  checkerOk -> buildOk

def ay_bwfg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_bwfg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_bwfg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_bwfg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_bwfg_accepted_binary_witness
    (formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> binary -> decoder -> encoding -> decoded -> domain -> normalized -> replay ->
      checker -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_bwfg_public_sat
    (accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_bwfg_conj accepted
    (ay_bwfg_conj normalizedAssignment
      (ay_bwfg_conj everyOriginalClauseSatisfied
        (ay_bwfg_conj checkerOk
          (ay_bwfg_conj validatorOk (ay_bwfg_conj archiveOk audited)))))

def ay_bwfg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_bwfg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_bwfg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_bwfg_conj p q :=
  fun r h => h hp hq

theorem ay_bwfg_conj_left {p q : Prop} (h : ay_bwfg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_bwfg_conj_right {p q : Prop} (h : ay_bwfg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_bwfg_conj_left h)

theorem ay_bwfg_disj_left {p q : Prop} (hp : p) : ay_bwfg_disj p q :=
  fun r hl _ => hl hp

theorem ay_bwfg_disj_right {p q : Prop} (hq : q) : ay_bwfg_disj p q :=
  fun r _ hr => hr hq

theorem ay_bwfg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_bwfg_equiv p q :=
  ay_bwfg_conj_intro hpq hqp

theorem ay_bwfg_equiv_forward {p q : Prop} (h : ay_bwfg_equiv p q) : p -> q :=
  ay_bwfg_conj_left h

theorem ay_bwfg_equiv_backward {p q : Prop} (h : ay_bwfg_equiv p q) : q -> p :=
  ay_bwfg_conj_right h

theorem ay_bwfg_original_formula_fingerprint_intro
    {binaryWitness formulaOk : Prop}
    (h : binaryWitness -> formulaOk) :
    ay_bwfg_original_formula_fingerprint binaryWitness formulaOk :=
  h

theorem ay_bwfg_binary_witness_digest_intro {formulaOk binaryOk : Prop}
    (h : formulaOk -> binaryOk) :
    ay_bwfg_binary_witness_digest formulaOk binaryOk :=
  h

theorem ay_bwfg_decoder_version_digest_intro {binaryOk decoderOk : Prop}
    (h : binaryOk -> decoderOk) :
    ay_bwfg_decoder_version_digest binaryOk decoderOk :=
  h

theorem ay_bwfg_byte_order_encoding_manifest_intro {decoderOk encodingOk : Prop}
    (h : decoderOk -> encodingOk) :
    ay_bwfg_byte_order_encoding_manifest decoderOk encodingOk :=
  h

theorem ay_bwfg_decoded_assignment_digest_intro {encodingOk decodedOk : Prop}
    (h : encodingOk -> decodedOk) :
    ay_bwfg_decoded_assignment_digest encodingOk decodedOk :=
  h

theorem ay_bwfg_variable_domain_digest_intro {decodedOk domainOk : Prop}
    (h : decodedOk -> domainOk) :
    ay_bwfg_variable_domain_digest decodedOk domainOk :=
  h

theorem ay_bwfg_normalization_ledger_intro {domainOk normalizedOk : Prop}
    (h : domainOk -> normalizedOk) :
    ay_bwfg_normalization_ledger domainOk normalizedOk :=
  h

theorem ay_bwfg_clause_satisfaction_replay_intro
    {normalizedOk everyOriginalClauseSatisfied : Prop}
    (h : normalizedOk -> everyOriginalClauseSatisfied) :
    ay_bwfg_clause_satisfaction_replay normalizedOk everyOriginalClauseSatisfied :=
  h

theorem ay_bwfg_checker_transcript_intro
    {everyOriginalClauseSatisfied checkerOk : Prop}
    (h : everyOriginalClauseSatisfied -> checkerOk) :
    ay_bwfg_checker_transcript everyOriginalClauseSatisfied checkerOk :=
  h

theorem ay_bwfg_solver_build_evidence_intro {checkerOk buildOk : Prop}
    (h : checkerOk -> buildOk) :
    ay_bwfg_solver_build_evidence checkerOk buildOk :=
  h

theorem ay_bwfg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_bwfg_validator_gate buildOk validatorOk :=
  h

theorem ay_bwfg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_bwfg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_bwfg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_bwfg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_bwfg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_bwfg_audit_transcript fallbackReady audited :=
  h

theorem ay_bwfg_accepted_binary_witness_intro
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (hf : formula) (hb : binary) (hdc : decoder) (he : encoding) (hdec : decoded)
    (hd : domain) (hn : normalized) (hr : replay) (hc : checker) (hbuild : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit :=
  fun r k => k hf hb hdc he hdec hd hn hr hc hbuild hv har hfb hau

theorem ay_bwfg_accepted_binary_witness_binary
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : binary :=
  h binary (fun _ hb _ _ _ _ _ _ _ _ _ _ _ _ => hb)

theorem ay_bwfg_accepted_binary_witness_decoder
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : decoder :=
  h decoder (fun _ _ hdc _ _ _ _ _ _ _ _ _ _ _ => hdc)

theorem ay_bwfg_accepted_binary_witness_encoding
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : encoding :=
  h encoding (fun _ _ _ he _ _ _ _ _ _ _ _ _ _ => he)

theorem ay_bwfg_accepted_binary_witness_decoded
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : decoded :=
  h decoded (fun _ _ _ _ hdec _ _ _ _ _ _ _ _ _ => hdec)

theorem ay_bwfg_accepted_binary_witness_domain
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : domain :=
  h domain (fun _ _ _ _ _ hd _ _ _ _ _ _ _ _ => hd)

theorem ay_bwfg_accepted_binary_witness_normalized
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : normalized :=
  h normalized (fun _ _ _ _ _ _ hn _ _ _ _ _ _ _ => hn)

theorem ay_bwfg_accepted_binary_witness_replay
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ hr _ _ _ _ _ _ => hr)

theorem ay_bwfg_accepted_binary_witness_checker
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ _ hc _ _ _ _ _ => hc)

theorem ay_bwfg_accepted_binary_witness_validator
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_bwfg_accepted_binary_witness_archive
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_bwfg_accepted_binary_witness_audit
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_bwfg_public_sat_intro
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hr : everyOriginalClauseSatisfied)
    (hc : checkerOk) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_bwfg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk
      validatorOk archiveOk audited :=
  ay_bwfg_conj_intro ha
    (ay_bwfg_conj_intro hn
      (ay_bwfg_conj_intro hr
        (ay_bwfg_conj_intro hc
          (ay_bwfg_conj_intro hv (ay_bwfg_conj_intro har hau)))))

theorem ay_bwfg_public_sat_requires_binary_guard
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_bwfg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : accepted :=
  ay_bwfg_conj_left h

theorem ay_bwfg_public_sat_normalized_assignment
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_bwfg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : normalizedAssignment :=
  ay_bwfg_conj_left (ay_bwfg_conj_right h)

theorem ay_bwfg_public_sat_original_clauses
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_bwfg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : everyOriginalClauseSatisfied :=
  ay_bwfg_conj_left (ay_bwfg_conj_right (ay_bwfg_conj_right h))

theorem ay_bwfg_accepted_binary_witness_publishes_sat
    {formula binary decoder encoding decoded domain normalized replay checker build validator
     archive fallback audit : Prop}
    (h : ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
      normalized replay checker build validator archive fallback audit) :
    ay_bwfg_public_sat
      (ay_bwfg_accepted_binary_witness formula binary decoder encoding decoded domain
        normalized replay checker build validator archive fallback audit)
      normalized replay checker validator archive audit :=
  ay_bwfg_public_sat_intro
    h
    (ay_bwfg_accepted_binary_witness_normalized h)
    (ay_bwfg_accepted_binary_witness_replay h)
    (ay_bwfg_accepted_binary_witness_checker h)
    (ay_bwfg_accepted_binary_witness_validator h)
    (ay_bwfg_accepted_binary_witness_archive h)
    (ay_bwfg_accepted_binary_witness_audit h)

theorem ay_bwfg_decoded_normalized_agree_with_original_domain
    {decoded normalized domainAgreement : Prop}
    (h : ay_bwfg_equiv decoded normalized)
    (hag : normalized -> domainAgreement)
    (hd : decoded) : domainAgreement :=
  hag (ay_bwfg_equiv_forward h hd)

theorem ay_bwfg_no_claim_intro {reason : Prop} (h : reason) :
    ay_bwfg_no_claim_diagnostic reason :=
  h

theorem ay_bwfg_recompute_intro {reason : Prop} (h : reason) :
    ay_bwfg_recompute_obligation reason :=
  h

theorem ay_bwfg_binary_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_decoder_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_bwfg_recompute_obligation mismatch :=
  ay_bwfg_recompute_intro h

theorem ay_bwfg_encoding_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_normalization_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_bwfg_recompute_obligation mismatch :=
  ay_bwfg_recompute_intro h

theorem ay_bwfg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_checker_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_bwfg_recompute_obligation mismatch :=
  ay_bwfg_recompute_intro h

theorem ay_bwfg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_bwfg_recompute_obligation mismatch :=
  ay_bwfg_recompute_intro h

theorem ay_bwfg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_bwfg_no_claim_diagnostic mismatch :=
  ay_bwfg_no_claim_intro h

theorem ay_bwfg_failed_binary_witness_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_bwfg_no_claim_diagnostic failure)
    (noBless : ay_bwfg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_bwfg_failed_binary_witness_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_bwfg_recompute_obligation failure)
    (hfailure : failure) :
    ay_bwfg_recompute_obligation failure :=
  fallback hfailure

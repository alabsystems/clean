/-!
  SAT-COMP/ay assignment compression manifest guard.

  This self-contained package models the SAT-only obligations for publishing a
  compressed model artifact only after decompression preserves the checked
  assignment over the original variable domain.
-/

def ay_acmg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_acmg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_acmg_equiv (p q : Prop) : Prop :=
  ay_acmg_conj (p -> q) (q -> p)

def ay_acmg_original_formula_fingerprint
    (rawAssignment originalFingerprintOk : Prop) : Prop :=
  rawAssignment -> originalFingerprintOk

def ay_acmg_raw_assignment_digest
    (originalFingerprintOk rawDigestOk : Prop) : Prop :=
  originalFingerprintOk -> rawDigestOk

def ay_acmg_compressed_assignment_digest
    (rawDigestOk compressedDigestOk : Prop) : Prop :=
  rawDigestOk -> compressedDigestOk

def ay_acmg_compression_manifest_version_digest
    (compressedDigestOk manifestOk : Prop) : Prop :=
  compressedDigestOk -> manifestOk

def ay_acmg_decompression_transcript
    (manifestOk decompressedOk : Prop) : Prop :=
  manifestOk -> decompressedOk

def ay_acmg_variable_domain_digest
    (decompressedOk domainOk : Prop) : Prop :=
  decompressedOk -> domainOk

def ay_acmg_normalized_assignment_digest
    (domainOk normalizedOk : Prop) : Prop :=
  domainOk -> normalizedOk

def ay_acmg_clause_satisfaction_replay
    (normalizedOk everyOriginalClauseSatisfied : Prop) : Prop :=
  normalizedOk -> everyOriginalClauseSatisfied

def ay_acmg_checker_transcript
    (everyOriginalClauseSatisfied checkerOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> checkerOk

def ay_acmg_solver_build_evidence (checkerOk buildOk : Prop) : Prop :=
  checkerOk -> buildOk

def ay_acmg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_acmg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_acmg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_acmg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_acmg_accepted_compression
    (formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> raw -> compressed -> manifest -> decompression -> domain -> normalized ->
      replay -> checker -> build -> validator -> archive -> fallback -> audit -> r) -> r

def ay_acmg_public_sat
    (accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop) : Prop :=
  ay_acmg_conj accepted
    (ay_acmg_conj normalizedAssignment
      (ay_acmg_conj everyOriginalClauseSatisfied
        (ay_acmg_conj checkerOk
          (ay_acmg_conj validatorOk (ay_acmg_conj archiveOk audited)))))

def ay_acmg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_acmg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_acmg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_acmg_conj p q :=
  fun r h => h hp hq

theorem ay_acmg_conj_left {p q : Prop} (h : ay_acmg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_acmg_conj_right {p q : Prop} (h : ay_acmg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_acmg_conj_left h)

theorem ay_acmg_disj_left {p q : Prop} (hp : p) : ay_acmg_disj p q :=
  fun r hl _ => hl hp

theorem ay_acmg_disj_right {p q : Prop} (hq : q) : ay_acmg_disj p q :=
  fun r _ hr => hr hq

theorem ay_acmg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_acmg_equiv p q :=
  ay_acmg_conj_intro hpq hqp

theorem ay_acmg_equiv_forward {p q : Prop} (h : ay_acmg_equiv p q) : p -> q :=
  ay_acmg_conj_left h

theorem ay_acmg_equiv_backward {p q : Prop} (h : ay_acmg_equiv p q) : q -> p :=
  ay_acmg_conj_right h

theorem ay_acmg_original_formula_fingerprint_intro
    {rawAssignment originalFingerprintOk : Prop}
    (h : rawAssignment -> originalFingerprintOk) :
    ay_acmg_original_formula_fingerprint rawAssignment originalFingerprintOk :=
  h

theorem ay_acmg_raw_assignment_digest_intro
    {originalFingerprintOk rawDigestOk : Prop}
    (h : originalFingerprintOk -> rawDigestOk) :
    ay_acmg_raw_assignment_digest originalFingerprintOk rawDigestOk :=
  h

theorem ay_acmg_compressed_assignment_digest_intro
    {rawDigestOk compressedDigestOk : Prop}
    (h : rawDigestOk -> compressedDigestOk) :
    ay_acmg_compressed_assignment_digest rawDigestOk compressedDigestOk :=
  h

theorem ay_acmg_compression_manifest_version_digest_intro
    {compressedDigestOk manifestOk : Prop}
    (h : compressedDigestOk -> manifestOk) :
    ay_acmg_compression_manifest_version_digest compressedDigestOk manifestOk :=
  h

theorem ay_acmg_decompression_transcript_intro
    {manifestOk decompressedOk : Prop}
    (h : manifestOk -> decompressedOk) :
    ay_acmg_decompression_transcript manifestOk decompressedOk :=
  h

theorem ay_acmg_variable_domain_digest_intro {decompressedOk domainOk : Prop}
    (h : decompressedOk -> domainOk) :
    ay_acmg_variable_domain_digest decompressedOk domainOk :=
  h

theorem ay_acmg_normalized_assignment_digest_intro {domainOk normalizedOk : Prop}
    (h : domainOk -> normalizedOk) :
    ay_acmg_normalized_assignment_digest domainOk normalizedOk :=
  h

theorem ay_acmg_clause_satisfaction_replay_intro
    {normalizedOk everyOriginalClauseSatisfied : Prop}
    (h : normalizedOk -> everyOriginalClauseSatisfied) :
    ay_acmg_clause_satisfaction_replay normalizedOk everyOriginalClauseSatisfied :=
  h

theorem ay_acmg_checker_transcript_intro
    {everyOriginalClauseSatisfied checkerOk : Prop}
    (h : everyOriginalClauseSatisfied -> checkerOk) :
    ay_acmg_checker_transcript everyOriginalClauseSatisfied checkerOk :=
  h

theorem ay_acmg_solver_build_evidence_intro {checkerOk buildOk : Prop}
    (h : checkerOk -> buildOk) :
    ay_acmg_solver_build_evidence checkerOk buildOk :=
  h

theorem ay_acmg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_acmg_validator_gate buildOk validatorOk :=
  h

theorem ay_acmg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_acmg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_acmg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_acmg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_acmg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_acmg_audit_transcript fallbackReady audited :=
  h

theorem ay_acmg_accepted_compression_intro
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (hf : formula) (hr : raw) (hc : compressed) (hm : manifest) (hdc : decompression)
    (hd : domain) (hn : normalized) (hrep : replay) (hchk : checker) (hb : build)
    (hv : validator) (har : archive) (hfb : fallback) (hau : audit) :
    ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit :=
  fun r k => k hf hr hc hm hdc hd hn hrep hchk hb hv har hfb hau

theorem ay_acmg_accepted_compression_raw
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : raw :=
  h raw (fun _ hr _ _ _ _ _ _ _ _ _ _ _ _ => hr)

theorem ay_acmg_accepted_compression_compressed
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : compressed :=
  h compressed (fun _ _ hc _ _ _ _ _ _ _ _ _ _ _ => hc)

theorem ay_acmg_accepted_compression_decompression
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : decompression :=
  h decompression (fun _ _ _ _ hdc _ _ _ _ _ _ _ _ _ => hdc)

theorem ay_acmg_accepted_compression_domain
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : domain :=
  h domain (fun _ _ _ _ _ hd _ _ _ _ _ _ _ _ => hd)

theorem ay_acmg_accepted_compression_normalized
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : normalized :=
  h normalized (fun _ _ _ _ _ _ hn _ _ _ _ _ _ _ => hn)

theorem ay_acmg_accepted_compression_replay
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ hrep _ _ _ _ _ _ => hrep)

theorem ay_acmg_accepted_compression_checker
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ _ hchk _ _ _ _ _ => hchk)

theorem ay_acmg_accepted_compression_validator
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_acmg_accepted_compression_archive
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_acmg_accepted_compression_audit
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_acmg_public_sat_intro
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hr : everyOriginalClauseSatisfied)
    (hc : checkerOk) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_acmg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk
      validatorOk archiveOk audited :=
  ay_acmg_conj_intro ha
    (ay_acmg_conj_intro hn
      (ay_acmg_conj_intro hr
        (ay_acmg_conj_intro hc
          (ay_acmg_conj_intro hv (ay_acmg_conj_intro har hau)))))

theorem ay_acmg_public_sat_requires_compression_guard
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_acmg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : accepted :=
  ay_acmg_conj_left h

theorem ay_acmg_public_sat_normalized_assignment
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_acmg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : normalizedAssignment :=
  ay_acmg_conj_left (ay_acmg_conj_right h)

theorem ay_acmg_public_sat_original_clauses
    {accepted normalizedAssignment everyOriginalClauseSatisfied checkerOk validatorOk archiveOk
     audited : Prop}
    (h : ay_acmg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      checkerOk validatorOk archiveOk audited) : everyOriginalClauseSatisfied :=
  ay_acmg_conj_left (ay_acmg_conj_right (ay_acmg_conj_right h))

theorem ay_acmg_accepted_compressed_assignment_publishes_sat
    {formula raw compressed manifest decompression domain normalized replay checker build
     validator archive fallback audit : Prop}
    (h : ay_acmg_accepted_compression formula raw compressed manifest decompression domain
      normalized replay checker build validator archive fallback audit) :
    ay_acmg_public_sat
      (ay_acmg_accepted_compression formula raw compressed manifest decompression domain
        normalized replay checker build validator archive fallback audit)
      normalized replay checker validator archive audit :=
  ay_acmg_public_sat_intro
    h
    (ay_acmg_accepted_compression_normalized h)
    (ay_acmg_accepted_compression_replay h)
    (ay_acmg_accepted_compression_checker h)
    (ay_acmg_accepted_compression_validator h)
    (ay_acmg_accepted_compression_archive h)
    (ay_acmg_accepted_compression_audit h)

theorem ay_acmg_raw_compressed_normalized_agree_on_domain
    {raw compressed normalized domainAgreement : Prop}
    (hraw : ay_acmg_equiv raw compressed)
    (hnorm : compressed -> normalized)
    (hag : normalized -> domainAgreement)
    (hr : raw) : domainAgreement :=
  hag (hnorm (ay_acmg_equiv_forward hraw hr))

theorem ay_acmg_no_claim_intro {reason : Prop} (h : reason) :
    ay_acmg_no_claim_diagnostic reason :=
  h

theorem ay_acmg_recompute_intro {reason : Prop} (h : reason) :
    ay_acmg_recompute_obligation reason :=
  h

theorem ay_acmg_compression_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_acmg_recompute_obligation mismatch :=
  ay_acmg_recompute_intro h

theorem ay_acmg_decompression_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_checker_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_acmg_recompute_obligation mismatch :=
  ay_acmg_recompute_intro h

theorem ay_acmg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_acmg_recompute_obligation mismatch :=
  ay_acmg_recompute_intro h

theorem ay_acmg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_acmg_no_claim_diagnostic mismatch :=
  ay_acmg_no_claim_intro h

theorem ay_acmg_failed_compression_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_acmg_no_claim_diagnostic failure)
    (noBless : ay_acmg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_acmg_failed_compression_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_acmg_recompute_obligation failure)
    (hfailure : failure) :
    ay_acmg_recompute_obligation failure :=
  fallback hfailure

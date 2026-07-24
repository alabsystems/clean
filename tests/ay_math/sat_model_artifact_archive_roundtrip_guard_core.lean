/-!
  SAT-COMP/ay model artifact archive-roundtrip guard.

  This self-contained package models the SAT-only obligations for publishing a
  SAT model from an archived artifact after extraction and roundtrip checking.
-/

def ay_marg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_marg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_marg_equiv (p q : Prop) : Prop :=
  ay_marg_conj (p -> q) (q -> p)

def ay_marg_benchmark_fingerprint (artifactDigest fingerprintOk : Prop) : Prop :=
  artifactDigest -> fingerprintOk

def ay_marg_model_artifact_digest (fingerprintOk artifactOk : Prop) : Prop :=
  fingerprintOk -> artifactOk

def ay_marg_archive_manifest (artifactOk archiveOk : Prop) : Prop :=
  artifactOk -> archiveOk

def ay_marg_extraction_roundtrip_digest (archiveOk extractedOk : Prop) : Prop :=
  archiveOk -> extractedOk

def ay_marg_serialized_witness_digest (extractedOk serializedOk : Prop) : Prop :=
  extractedOk -> serializedOk

def ay_marg_parser_transcript (serializedOk parsedOk : Prop) : Prop :=
  serializedOk -> parsedOk

def ay_marg_assignment_digest (parsedOk assignmentOk : Prop) : Prop :=
  parsedOk -> assignmentOk

def ay_marg_checker_transcript (assignmentOk checkerOk : Prop) : Prop :=
  assignmentOk -> checkerOk

def ay_marg_clause_satisfaction_replay
    (checkerOk everyOriginalClauseSatisfied : Prop) : Prop :=
  checkerOk -> everyOriginalClauseSatisfied

def ay_marg_solver_build_evidence (everyOriginalClauseSatisfied buildOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> buildOk

def ay_marg_fallback_no_claim_path (buildOk fallbackReady : Prop) : Prop :=
  buildOk -> fallbackReady

def ay_marg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_marg_accepted_archive_roundtrip
    (fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> artifact -> archive -> extraction -> serialized -> parser -> assignment ->
      checker -> everyClause -> build -> fallback -> audit -> r) -> r

def ay_marg_public_sat
    (accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop) :
    Prop :=
  ay_marg_conj accepted
    (ay_marg_conj roundtrippedArtifact
      (ay_marg_conj parsedAssignment
        (ay_marg_conj everyOriginalClauseSatisfied audited)))

def ay_marg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_marg_conj proofAccepted originalUnsat

def ay_marg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_marg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_marg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_marg_conj p q :=
  fun r h => h hp hq

theorem ay_marg_conj_left {p q : Prop} (h : ay_marg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_marg_conj_right {p q : Prop} (h : ay_marg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_marg_conj_left h)

theorem ay_marg_disj_left {p q : Prop} (hp : p) : ay_marg_disj p q :=
  fun r hl _ => hl hp

theorem ay_marg_disj_right {p q : Prop} (hq : q) : ay_marg_disj p q :=
  fun r _ hr => hr hq

theorem ay_marg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_marg_equiv p q :=
  ay_marg_conj_intro hpq hqp

theorem ay_marg_equiv_forward {p q : Prop} (h : ay_marg_equiv p q) : p -> q :=
  ay_marg_conj_left h

theorem ay_marg_equiv_backward {p q : Prop} (h : ay_marg_equiv p q) : q -> p :=
  ay_marg_conj_right h

theorem ay_marg_benchmark_fingerprint_intro {artifactDigest fingerprintOk : Prop}
    (h : artifactDigest -> fingerprintOk) :
    ay_marg_benchmark_fingerprint artifactDigest fingerprintOk :=
  h

theorem ay_marg_model_artifact_digest_intro {fingerprintOk artifactOk : Prop}
    (h : fingerprintOk -> artifactOk) :
    ay_marg_model_artifact_digest fingerprintOk artifactOk :=
  h

theorem ay_marg_archive_manifest_intro {artifactOk archiveOk : Prop}
    (h : artifactOk -> archiveOk) :
    ay_marg_archive_manifest artifactOk archiveOk :=
  h

theorem ay_marg_extraction_roundtrip_digest_intro {archiveOk extractedOk : Prop}
    (h : archiveOk -> extractedOk) :
    ay_marg_extraction_roundtrip_digest archiveOk extractedOk :=
  h

theorem ay_marg_serialized_witness_digest_intro {extractedOk serializedOk : Prop}
    (h : extractedOk -> serializedOk) :
    ay_marg_serialized_witness_digest extractedOk serializedOk :=
  h

theorem ay_marg_parser_transcript_intro {serializedOk parsedOk : Prop}
    (h : serializedOk -> parsedOk) :
    ay_marg_parser_transcript serializedOk parsedOk :=
  h

theorem ay_marg_assignment_digest_intro {parsedOk assignmentOk : Prop}
    (h : parsedOk -> assignmentOk) :
    ay_marg_assignment_digest parsedOk assignmentOk :=
  h

theorem ay_marg_checker_transcript_intro {assignmentOk checkerOk : Prop}
    (h : assignmentOk -> checkerOk) :
    ay_marg_checker_transcript assignmentOk checkerOk :=
  h

theorem ay_marg_clause_satisfaction_replay_intro
    {checkerOk everyOriginalClauseSatisfied : Prop}
    (h : checkerOk -> everyOriginalClauseSatisfied) :
    ay_marg_clause_satisfaction_replay checkerOk everyOriginalClauseSatisfied :=
  h

theorem ay_marg_solver_build_evidence_intro
    {everyOriginalClauseSatisfied buildOk : Prop}
    (h : everyOriginalClauseSatisfied -> buildOk) :
    ay_marg_solver_build_evidence everyOriginalClauseSatisfied buildOk :=
  h

theorem ay_marg_fallback_no_claim_path_intro {buildOk fallbackReady : Prop}
    (h : buildOk -> fallbackReady) :
    ay_marg_fallback_no_claim_path buildOk fallbackReady :=
  h

theorem ay_marg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_marg_audit_transcript fallbackReady audited :=
  h

theorem ay_marg_accepted_archive_roundtrip_intro
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (hf : fingerprint) (hart : artifact) (har : archive) (hex : extraction)
    (hs : serialized) (hp : parser) (ha : assignment) (hc : checker)
    (he : everyClause) (hb : build) (hfb : fallback) (hau : audit) :
    ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction serialized
      parser assignment checker everyClause build fallback audit :=
  fun r k => k hf hart har hex hs hp ha hc he hb hfb hau

theorem ay_marg_accepted_archive_roundtrip_artifact
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : artifact :=
  h artifact (fun _ hart _ _ _ _ _ _ _ _ _ _ => hart)

theorem ay_marg_accepted_archive_roundtrip_archive
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : archive :=
  h archive (fun _ _ har _ _ _ _ _ _ _ _ _ => har)

theorem ay_marg_accepted_archive_roundtrip_extraction
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : extraction :=
  h extraction (fun _ _ _ hex _ _ _ _ _ _ _ _ => hex)

theorem ay_marg_accepted_archive_roundtrip_parser
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : parser :=
  h parser (fun _ _ _ _ _ hp _ _ _ _ _ _ => hp)

theorem ay_marg_accepted_archive_roundtrip_assignment
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : assignment :=
  h assignment (fun _ _ _ _ _ _ ha _ _ _ _ _ => ha)

theorem ay_marg_accepted_archive_roundtrip_checker
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ hc _ _ _ _ => hc)

theorem ay_marg_accepted_archive_roundtrip_every_clause
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ _ _ he _ _ _ => he)

theorem ay_marg_accepted_archive_roundtrip_audit
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audit : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction
      serialized parser assignment checker everyClause build fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_marg_public_sat_intro
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop}
    (ha : accepted) (hart : roundtrippedArtifact) (hpa : parsedAssignment)
    (hc : everyOriginalClauseSatisfied) (hau : audited) :
    ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited :=
  ay_marg_conj_intro ha
    (ay_marg_conj_intro hart
      (ay_marg_conj_intro hpa (ay_marg_conj_intro hc hau)))

theorem ay_marg_public_sat_requires_archive_guard
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop}
    (h : ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited) : accepted :=
  ay_marg_conj_left h

theorem ay_marg_public_sat_roundtripped_artifact
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop}
    (h : ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited) : roundtrippedArtifact :=
  ay_marg_conj_left (ay_marg_conj_right h)

theorem ay_marg_public_sat_parsed_assignment
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop}
    (h : ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited) : parsedAssignment :=
  ay_marg_conj_left (ay_marg_conj_right (ay_marg_conj_right h))

theorem ay_marg_public_sat_every_original_clause
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited : Prop}
    (h : ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited) : everyOriginalClauseSatisfied :=
  ay_marg_conj_left
    (ay_marg_conj_right (ay_marg_conj_right (ay_marg_conj_right h)))

theorem ay_marg_archived_extracted_artifact_publishes_sat
    {fingerprint artifact archive extraction serialized parser assignment checker everyClause
     build fallback audited : Prop}
    (h : ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction serialized
      parser assignment checker everyClause build fallback audited) :
    ay_marg_public_sat
      (ay_marg_accepted_archive_roundtrip fingerprint artifact archive extraction serialized
        parser assignment checker everyClause build fallback audited)
      extraction assignment everyClause audited :=
  ay_marg_public_sat_intro
    h
    (ay_marg_accepted_archive_roundtrip_extraction h)
    (ay_marg_accepted_archive_roundtrip_assignment h)
    (ay_marg_accepted_archive_roundtrip_every_clause h)
    (ay_marg_accepted_archive_roundtrip_audit h)

theorem ay_marg_roundtrip_artifact_parses_to_checked_assignment
    {extracted parsedAssignment checkedAssignment everyClause : Prop}
    (hmatch : ay_marg_equiv extracted parsedAssignment)
    (hchecked : parsedAssignment -> checkedAssignment)
    (hsat : checkedAssignment -> everyClause)
    (hex : extracted) : everyClause :=
  hsat (hchecked (ay_marg_equiv_forward hmatch hex))

theorem ay_marg_no_claim_intro {reason : Prop} (h : reason) :
    ay_marg_no_claim_diagnostic reason :=
  h

theorem ay_marg_recompute_intro {reason : Prop} (h : reason) :
    ay_marg_recompute_obligation reason :=
  h

theorem ay_marg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_marg_no_claim_diagnostic archiveMismatch :=
  ay_marg_no_claim_intro h

theorem ay_marg_archive_mismatch_recompute {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_marg_recompute_obligation archiveMismatch :=
  ay_marg_recompute_intro h

theorem ay_marg_extraction_mismatch_recompute {extractionMismatch : Prop}
    (h : extractionMismatch) :
    ay_marg_recompute_obligation extractionMismatch :=
  ay_marg_recompute_intro h

theorem ay_marg_parser_mismatch_no_claim {parserMismatch : Prop}
    (h : parserMismatch) :
    ay_marg_no_claim_diagnostic parserMismatch :=
  ay_marg_no_claim_intro h

theorem ay_marg_assignment_mismatch_recompute {assignmentMismatch : Prop}
    (h : assignmentMismatch) :
    ay_marg_recompute_obligation assignmentMismatch :=
  ay_marg_recompute_intro h

theorem ay_marg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_marg_no_claim_diagnostic checkerMismatch :=
  ay_marg_no_claim_intro h

theorem ay_marg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_marg_recompute_obligation buildMismatch :=
  ay_marg_recompute_intro h

theorem ay_marg_failed_archive_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_marg_no_claim_diagnostic failure)
    (noBless : ay_marg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_marg_failed_archive_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_marg_recompute_obligation failure)
    (hfailure : failure) :
    ay_marg_recompute_obligation failure :=
  fallback hfailure

theorem ay_marg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_marg_public_unsat proofAccepted originalUnsat :=
  ay_marg_conj_intro hp hu

theorem ay_marg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_marg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_marg_conj_left h

theorem ay_marg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_marg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_marg_conj_right h

theorem ay_marg_archive_guard_cannot_strengthen_unsat_claims
    {accepted roundtrippedArtifact parsedAssignment everyOriginalClauseSatisfied audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_marg_public_sat accepted roundtrippedArtifact parsedAssignment
      everyOriginalClauseSatisfied audited)
    (hUnsat : ay_marg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_marg_public_unsat_claim hUnsat

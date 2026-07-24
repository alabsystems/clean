/-!
  SAT-COMP/ay model artifact-digest binding guard.

  This self-contained package models the SAT-only obligations for binding a
  public model artifact digest to the parsed assignment that was checked.
-/

def ay_madg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_madg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_madg_equiv (p q : Prop) : Prop :=
  ay_madg_conj (p -> q) (q -> p)

def ay_madg_benchmark_fingerprint (artifactDigest fingerprintOk : Prop) : Prop :=
  artifactDigest -> fingerprintOk

def ay_madg_model_artifact_digest (fingerprintOk artifactOk : Prop) : Prop :=
  fingerprintOk -> artifactOk

def ay_madg_serialized_witness_digest (artifactOk serializedOk : Prop) : Prop :=
  artifactOk -> serializedOk

def ay_madg_parser_transcript (serializedOk parsedAssignmentOk : Prop) : Prop :=
  serializedOk -> parsedAssignmentOk

def ay_madg_assignment_digest (parsedAssignmentOk assignmentOk : Prop) : Prop :=
  parsedAssignmentOk -> assignmentOk

def ay_madg_checker_transcript (assignmentOk checkerOk : Prop) : Prop :=
  assignmentOk -> checkerOk

def ay_madg_clause_satisfaction_replay (checkerOk everyOriginalClauseSatisfied : Prop) : Prop :=
  checkerOk -> everyOriginalClauseSatisfied

def ay_madg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_madg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_madg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_madg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_madg_accepted_artifact_binding
    (fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> artifact -> serialized -> parser -> assignment -> checker -> everyClause ->
      originalSat -> build -> archive -> fallback -> audit -> r) -> r

def ay_madg_public_sat
    (accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop) : Prop :=
  ay_madg_conj accepted
    (ay_madg_conj checkedArtifact
      (ay_madg_conj parsedAssignment
        (ay_madg_conj everyOriginalClauseSatisfied
          (ay_madg_conj originalSat audited))))

def ay_madg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_madg_conj proofAccepted originalUnsat

def ay_madg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_madg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_madg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_madg_conj p q :=
  fun r h => h hp hq

theorem ay_madg_conj_left {p q : Prop} (h : ay_madg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_madg_conj_right {p q : Prop} (h : ay_madg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_madg_conj_left h)

theorem ay_madg_disj_left {p q : Prop} (hp : p) : ay_madg_disj p q :=
  fun r hl _ => hl hp

theorem ay_madg_disj_right {p q : Prop} (hq : q) : ay_madg_disj p q :=
  fun r _ hr => hr hq

theorem ay_madg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_madg_equiv p q :=
  ay_madg_conj_intro hpq hqp

theorem ay_madg_equiv_forward {p q : Prop} (h : ay_madg_equiv p q) : p -> q :=
  ay_madg_conj_left h

theorem ay_madg_equiv_backward {p q : Prop} (h : ay_madg_equiv p q) : q -> p :=
  ay_madg_conj_right h

theorem ay_madg_benchmark_fingerprint_intro {artifactDigest fingerprintOk : Prop}
    (h : artifactDigest -> fingerprintOk) :
    ay_madg_benchmark_fingerprint artifactDigest fingerprintOk :=
  h

theorem ay_madg_model_artifact_digest_intro {fingerprintOk artifactOk : Prop}
    (h : fingerprintOk -> artifactOk) :
    ay_madg_model_artifact_digest fingerprintOk artifactOk :=
  h

theorem ay_madg_serialized_witness_digest_intro {artifactOk serializedOk : Prop}
    (h : artifactOk -> serializedOk) :
    ay_madg_serialized_witness_digest artifactOk serializedOk :=
  h

theorem ay_madg_parser_transcript_intro {serializedOk parsedAssignmentOk : Prop}
    (h : serializedOk -> parsedAssignmentOk) :
    ay_madg_parser_transcript serializedOk parsedAssignmentOk :=
  h

theorem ay_madg_assignment_digest_intro {parsedAssignmentOk assignmentOk : Prop}
    (h : parsedAssignmentOk -> assignmentOk) :
    ay_madg_assignment_digest parsedAssignmentOk assignmentOk :=
  h

theorem ay_madg_checker_transcript_intro {assignmentOk checkerOk : Prop}
    (h : assignmentOk -> checkerOk) :
    ay_madg_checker_transcript assignmentOk checkerOk :=
  h

theorem ay_madg_clause_satisfaction_replay_intro
    {checkerOk everyOriginalClauseSatisfied : Prop}
    (h : checkerOk -> everyOriginalClauseSatisfied) :
    ay_madg_clause_satisfaction_replay checkerOk everyOriginalClauseSatisfied :=
  h

theorem ay_madg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_madg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_madg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_madg_archive_manifest buildOk archiveOk :=
  h

theorem ay_madg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_madg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_madg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_madg_audit_transcript fallbackReady audited :=
  h

theorem ay_madg_accepted_artifact_binding_intro
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (hf : fingerprint) (ha : artifact) (hs : serialized) (hp : parser)
    (had : assignment) (hc : checker) (he : everyClause) (hos : originalSat)
    (hb : build) (har : archive) (hfb : fallback) (hau : audit) :
    ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit :=
  fun r k => k hf ha hs hp had hc he hos hb har hfb hau

theorem ay_madg_accepted_artifact_binding_artifact
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : artifact :=
  h artifact (fun _ ha _ _ _ _ _ _ _ _ _ _ => ha)

theorem ay_madg_accepted_artifact_binding_serialized
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : serialized :=
  h serialized (fun _ _ hs _ _ _ _ _ _ _ _ _ => hs)

theorem ay_madg_accepted_artifact_binding_parser
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : parser :=
  h parser (fun _ _ _ hp _ _ _ _ _ _ _ _ => hp)

theorem ay_madg_accepted_artifact_binding_assignment
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : assignment :=
  h assignment (fun _ _ _ _ had _ _ _ _ _ _ _ => had)

theorem ay_madg_accepted_artifact_binding_checker
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ hc _ _ _ _ _ _ => hc)

theorem ay_madg_accepted_artifact_binding_every_clause
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ he _ _ _ _ _ => he)

theorem ay_madg_accepted_artifact_binding_original_sat
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : originalSat :=
  h originalSat (fun _ _ _ _ _ _ _ hos _ _ _ _ => hos)

theorem ay_madg_accepted_artifact_binding_audit
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audit : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_madg_public_sat_intro
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (ha : accepted) (hart : checkedArtifact) (hassn : parsedAssignment)
    (hc : everyOriginalClauseSatisfied) (hs : originalSat) (hau : audited) :
    ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited :=
  ay_madg_conj_intro ha
    (ay_madg_conj_intro hart
      (ay_madg_conj_intro hassn
        (ay_madg_conj_intro hc (ay_madg_conj_intro hs hau))))

theorem ay_madg_public_sat_requires_artifact_guard
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : accepted :=
  ay_madg_conj_left h

theorem ay_madg_public_sat_checked_artifact
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : checkedArtifact :=
  ay_madg_conj_left (ay_madg_conj_right h)

theorem ay_madg_public_sat_parsed_assignment
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : parsedAssignment :=
  ay_madg_conj_left (ay_madg_conj_right (ay_madg_conj_right h))

theorem ay_madg_public_sat_every_original_clause
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : everyOriginalClauseSatisfied :=
  ay_madg_conj_left
    (ay_madg_conj_right (ay_madg_conj_right (ay_madg_conj_right h)))

theorem ay_madg_public_sat_original_formula
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : originalSat :=
  ay_madg_conj_left
    (ay_madg_conj_right
      (ay_madg_conj_right (ay_madg_conj_right (ay_madg_conj_right h))))

theorem ay_madg_public_sat_audit
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat
     audited : Prop}
    (h : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited) : audited :=
  ay_madg_conj_right
    (ay_madg_conj_right
      (ay_madg_conj_right (ay_madg_conj_right (ay_madg_conj_right h))))

theorem ay_madg_accepted_artifact_binding_publishes_sat
    {fingerprint artifact serialized parser assignment checker everyClause originalSat build
     archive fallback audited : Prop}
    (h : ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
      checker everyClause originalSat build archive fallback audited) :
    ay_madg_public_sat
      (ay_madg_accepted_artifact_binding fingerprint artifact serialized parser assignment
        checker everyClause originalSat build archive fallback audited)
      artifact assignment everyClause originalSat audited :=
  ay_madg_public_sat_intro
    h
    (ay_madg_accepted_artifact_binding_artifact h)
    (ay_madg_accepted_artifact_binding_assignment h)
    (ay_madg_accepted_artifact_binding_every_clause h)
    (ay_madg_accepted_artifact_binding_original_sat h)
    (ay_madg_accepted_artifact_binding_audit h)

theorem ay_madg_checked_artifact_matches_parsed_assignment
    {artifact parsedAssignment checkedAssignment originalSat : Prop}
    (hmatch : ay_madg_equiv artifact parsedAssignment)
    (hchecked : parsedAssignment -> checkedAssignment)
    (hsat : checkedAssignment -> originalSat)
    (ha : artifact) : originalSat :=
  hsat (hchecked (ay_madg_equiv_forward hmatch ha))

theorem ay_madg_no_claim_intro {reason : Prop} (h : reason) :
    ay_madg_no_claim_diagnostic reason :=
  h

theorem ay_madg_recompute_intro {reason : Prop} (h : reason) :
    ay_madg_recompute_obligation reason :=
  h

theorem ay_madg_artifact_mismatch_no_claim {artifactMismatch : Prop}
    (h : artifactMismatch) :
    ay_madg_no_claim_diagnostic artifactMismatch :=
  ay_madg_no_claim_intro h

theorem ay_madg_serialization_mismatch_recompute {serializationMismatch : Prop}
    (h : serializationMismatch) :
    ay_madg_recompute_obligation serializationMismatch :=
  ay_madg_recompute_intro h

theorem ay_madg_parser_mismatch_no_claim {parserMismatch : Prop}
    (h : parserMismatch) :
    ay_madg_no_claim_diagnostic parserMismatch :=
  ay_madg_no_claim_intro h

theorem ay_madg_assignment_mismatch_recompute {assignmentMismatch : Prop}
    (h : assignmentMismatch) :
    ay_madg_recompute_obligation assignmentMismatch :=
  ay_madg_recompute_intro h

theorem ay_madg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_madg_no_claim_diagnostic checkerMismatch :=
  ay_madg_no_claim_intro h

theorem ay_madg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_madg_recompute_obligation buildMismatch :=
  ay_madg_recompute_intro h

theorem ay_madg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_madg_no_claim_diagnostic archiveMismatch :=
  ay_madg_no_claim_intro h

theorem ay_madg_failed_artifact_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_madg_no_claim_diagnostic failure)
    (noBless : ay_madg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_madg_failed_artifact_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_madg_recompute_obligation failure)
    (hfailure : failure) :
    ay_madg_recompute_obligation failure :=
  fallback hfailure

theorem ay_madg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_madg_public_unsat proofAccepted originalUnsat :=
  ay_madg_conj_intro hp hu

theorem ay_madg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_madg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_madg_conj_left h

theorem ay_madg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_madg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_madg_conj_right h

theorem ay_madg_artifact_guard_cannot_strengthen_unsat_claims
    {accepted checkedArtifact parsedAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_madg_public_sat accepted checkedArtifact parsedAssignment
      everyOriginalClauseSatisfied originalSat audited)
    (hUnsat : ay_madg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_madg_public_unsat_claim hUnsat

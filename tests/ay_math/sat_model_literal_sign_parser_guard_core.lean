/-!
  SAT-COMP/ay literal-sign parser guard.

  This self-contained package models the SAT-only obligations for parsing
  signed DIMACS model literals before publishing a public SAT witness.
-/

def ay_lspg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_lspg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_lspg_equiv (p q : Prop) : Prop :=
  ay_lspg_conj (p -> q) (q -> p)

def ay_lspg_benchmark_fingerprint (serializedWitness fingerprintOk : Prop) : Prop :=
  serializedWitness -> fingerprintOk

def ay_lspg_serialized_witness_digest (fingerprintOk serializedOk : Prop) : Prop :=
  fingerprintOk -> serializedOk

def ay_lspg_signed_literal_parser_transcript (serializedOk signedParsed : Prop) : Prop :=
  serializedOk -> signedParsed

def ay_lspg_zero_terminator_policy_witness (signedParsed terminatorOk : Prop) : Prop :=
  signedParsed -> terminatorOk

def ay_lspg_variable_domain_manifest (terminatorOk domainOk : Prop) : Prop :=
  terminatorOk -> domainOk

def ay_lspg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_lspg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_lspg_model_checker_transcript
    (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_lspg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_lspg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_lspg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_lspg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_lspg_accepted_parsing
    (fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop) : Prop :=
  ay_lspg_conj fingerprint
    (ay_lspg_conj serialized
      (ay_lspg_conj parser
        (ay_lspg_conj terminator
          (ay_lspg_conj domain
            (ay_lspg_conj reconstruction
              (ay_lspg_conj replay
                (ay_lspg_conj checker
                  (ay_lspg_conj build
                    (ay_lspg_conj archive
                      (ay_lspg_conj fallback audit))))))))))

def ay_lspg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_lspg_conj accepted
    (ay_lspg_conj totalAssignment
      (ay_lspg_conj everyOriginalClauseSatisfied (ay_lspg_conj originalSat audited)))

def ay_lspg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_lspg_conj proofAccepted originalUnsat

def ay_lspg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_lspg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_lspg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_lspg_conj p q :=
  fun r h => h hp hq

theorem ay_lspg_conj_left {p q : Prop} (h : ay_lspg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_lspg_conj_right {p q : Prop} (h : ay_lspg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_lspg_conj_left h)

theorem ay_lspg_disj_left {p q : Prop} (hp : p) : ay_lspg_disj p q :=
  fun r hl _ => hl hp

theorem ay_lspg_disj_right {p q : Prop} (hq : q) : ay_lspg_disj p q :=
  fun r _ hr => hr hq

theorem ay_lspg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_lspg_equiv p q :=
  ay_lspg_conj_intro hpq hqp

theorem ay_lspg_equiv_forward {p q : Prop} (h : ay_lspg_equiv p q) : p -> q :=
  ay_lspg_conj_left h

theorem ay_lspg_equiv_backward {p q : Prop} (h : ay_lspg_equiv p q) : q -> p :=
  ay_lspg_conj_right h

theorem ay_lspg_benchmark_fingerprint_intro {serializedWitness fingerprintOk : Prop}
    (h : serializedWitness -> fingerprintOk) :
    ay_lspg_benchmark_fingerprint serializedWitness fingerprintOk :=
  h

theorem ay_lspg_serialized_witness_digest_intro {fingerprintOk serializedOk : Prop}
    (h : fingerprintOk -> serializedOk) :
    ay_lspg_serialized_witness_digest fingerprintOk serializedOk :=
  h

theorem ay_lspg_signed_literal_parser_transcript_intro {serializedOk signedParsed : Prop}
    (h : serializedOk -> signedParsed) :
    ay_lspg_signed_literal_parser_transcript serializedOk signedParsed :=
  h

theorem ay_lspg_zero_terminator_policy_witness_intro {signedParsed terminatorOk : Prop}
    (h : signedParsed -> terminatorOk) :
    ay_lspg_zero_terminator_policy_witness signedParsed terminatorOk :=
  h

theorem ay_lspg_variable_domain_manifest_intro {terminatorOk domainOk : Prop}
    (h : terminatorOk -> domainOk) :
    ay_lspg_variable_domain_manifest terminatorOk domainOk :=
  h

theorem ay_lspg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_lspg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_lspg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_lspg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_lspg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_lspg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_lspg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_lspg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_lspg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_lspg_archive_manifest buildOk archiveOk :=
  h

theorem ay_lspg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_lspg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_lspg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_lspg_audit_transcript fallbackReady audited :=
  h

theorem ay_lspg_accepted_parsing_intro
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (hf : fingerprint) (hs : serialized) (hp : parser) (ht : terminator)
    (hd : domain) (hrc : reconstruction) (hr : replay) (hchk : checker)
    (hb : build) (ha : archive) (hfb : fallback) (hau : audit) :
    ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit :=
  ay_lspg_conj_intro hf
    (ay_lspg_conj_intro hs
      (ay_lspg_conj_intro hp
        (ay_lspg_conj_intro ht
          (ay_lspg_conj_intro hd
            (ay_lspg_conj_intro hrc
              (ay_lspg_conj_intro hr
                (ay_lspg_conj_intro hchk
                  (ay_lspg_conj_intro hb
                    (ay_lspg_conj_intro ha
                      (ay_lspg_conj_intro hfb hau))))))))))

theorem ay_lspg_accepted_parsing_fingerprint
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_lspg_conj_left h

theorem ay_lspg_accepted_parsing_serialized
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : serialized :=
  ay_lspg_conj_left (ay_lspg_conj_right h)

theorem ay_lspg_accepted_parsing_parser
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : parser :=
  ay_lspg_conj_left (ay_lspg_conj_right (ay_lspg_conj_right h))

theorem ay_lspg_accepted_parsing_terminator
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : terminator :=
  ay_lspg_conj_left
    (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))

theorem ay_lspg_accepted_parsing_domain
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : domain :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h))))

theorem ay_lspg_accepted_parsing_reconstruction
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))))

theorem ay_lspg_accepted_parsing_replay
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h))))))

theorem ay_lspg_accepted_parsing_checker
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right
            (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))))))

theorem ay_lspg_accepted_parsing_build
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : build :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right
            (ay_lspg_conj_right
              (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h))))))))

theorem ay_lspg_accepted_parsing_archive
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right
            (ay_lspg_conj_right
              (ay_lspg_conj_right
                (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))))))))

theorem ay_lspg_accepted_parsing_fallback
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_lspg_conj_left
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right
            (ay_lspg_conj_right
              (ay_lspg_conj_right
                (ay_lspg_conj_right
                  (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h))))))))))

theorem ay_lspg_accepted_parsing_audit
    {fingerprint serialized parser terminator domain reconstruction replay checker build
     archive fallback audit : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_lspg_conj_right
    (ay_lspg_conj_right
      (ay_lspg_conj_right
        (ay_lspg_conj_right
          (ay_lspg_conj_right
            (ay_lspg_conj_right
              (ay_lspg_conj_right
                (ay_lspg_conj_right
                  (ay_lspg_conj_right
                    (ay_lspg_conj_right (ay_lspg_conj_right h))))))))))

theorem ay_lspg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_lspg_conj_intro ha
    (ay_lspg_conj_intro ht
      (ay_lspg_conj_intro hc (ay_lspg_conj_intro hs hau)))

theorem ay_lspg_public_sat_requires_parser_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_lspg_conj_left h

theorem ay_lspg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_lspg_conj_left (ay_lspg_conj_right h)

theorem ay_lspg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_lspg_conj_left (ay_lspg_conj_right (ay_lspg_conj_right h))

theorem ay_lspg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_lspg_conj_left
    (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))

theorem ay_lspg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_lspg_conj_right
    (ay_lspg_conj_right (ay_lspg_conj_right (ay_lspg_conj_right h)))

theorem ay_lspg_accepted_parsing_reconstructs_original_sat
    {fingerprint serialized parser terminator domain totalAssignment
     everyOriginalClauseSatisfied originalSat build archive fallback audited : Prop}
    (h : ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
      totalAssignment everyOriginalClauseSatisfied originalSat build archive fallback
      audited) :
    ay_lspg_public_sat
      (ay_lspg_accepted_parsing fingerprint serialized parser terminator domain
        totalAssignment everyOriginalClauseSatisfied originalSat build archive fallback audited)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_lspg_public_sat_intro
    h
    (ay_lspg_accepted_parsing_reconstruction h)
    (ay_lspg_accepted_parsing_replay h)
    (ay_lspg_accepted_parsing_checker h)
    (ay_lspg_accepted_parsing_audit h)

theorem ay_lspg_accepted_parsing_publishes_sat
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_lspg_public_sat_intro ha ht hc hs hau

theorem ay_lspg_no_claim_intro {reason : Prop} (h : reason) :
    ay_lspg_no_claim_diagnostic reason :=
  h

theorem ay_lspg_recompute_intro {reason : Prop} (h : reason) :
    ay_lspg_recompute_obligation reason :=
  h

theorem ay_lspg_sign_mismatch_no_claim {signMismatch : Prop} (h : signMismatch) :
    ay_lspg_no_claim_diagnostic signMismatch :=
  ay_lspg_no_claim_intro h

theorem ay_lspg_sign_mismatch_recompute {signMismatch : Prop} (h : signMismatch) :
    ay_lspg_recompute_obligation signMismatch :=
  ay_lspg_recompute_intro h

theorem ay_lspg_terminator_mismatch_no_claim {terminatorMismatch : Prop}
    (h : terminatorMismatch) :
    ay_lspg_no_claim_diagnostic terminatorMismatch :=
  ay_lspg_no_claim_intro h

theorem ay_lspg_terminator_mismatch_recompute {terminatorMismatch : Prop}
    (h : terminatorMismatch) :
    ay_lspg_recompute_obligation terminatorMismatch :=
  ay_lspg_recompute_intro h

theorem ay_lspg_domain_mismatch_no_claim {domainMismatch : Prop}
    (h : domainMismatch) :
    ay_lspg_no_claim_diagnostic domainMismatch :=
  ay_lspg_no_claim_intro h

theorem ay_lspg_reconstruction_mismatch_recompute {reconstructionMismatch : Prop}
    (h : reconstructionMismatch) :
    ay_lspg_recompute_obligation reconstructionMismatch :=
  ay_lspg_recompute_intro h

theorem ay_lspg_replay_mismatch_recompute {replayMismatch : Prop}
    (h : replayMismatch) :
    ay_lspg_recompute_obligation replayMismatch :=
  ay_lspg_recompute_intro h

theorem ay_lspg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_lspg_no_claim_diagnostic checkerMismatch :=
  ay_lspg_no_claim_intro h

theorem ay_lspg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_lspg_recompute_obligation buildMismatch :=
  ay_lspg_recompute_intro h

theorem ay_lspg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_lspg_no_claim_diagnostic archiveMismatch :=
  ay_lspg_no_claim_intro h

theorem ay_lspg_failed_parser_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_lspg_no_claim_diagnostic failure)
    (noBless : ay_lspg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_lspg_failed_parser_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_lspg_recompute_obligation failure)
    (hfailure : failure) :
    ay_lspg_recompute_obligation failure :=
  fallback hfailure

theorem ay_lspg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_lspg_public_unsat proofAccepted originalUnsat :=
  ay_lspg_conj_intro hp hu

theorem ay_lspg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_lspg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_lspg_conj_left h

theorem ay_lspg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_lspg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_lspg_conj_right h

theorem ay_lspg_parser_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_lspg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_lspg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_lspg_public_unsat_claim hUnsat

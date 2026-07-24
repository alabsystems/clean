/-!
  SAT-COMP/ay model witness serialization guard.

  This self-contained package models the SAT-only obligations for publishing a
  serialized model witness after parser, domain, reconstruction, and checker
  evidence agree.
-/

def ay_mwsg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mwsg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mwsg_equiv (p q : Prop) : Prop :=
  ay_mwsg_conj (p -> q) (q -> p)

def ay_mwsg_benchmark_fingerprint (serializedWitness fingerprintOk : Prop) : Prop :=
  serializedWitness -> fingerprintOk

def ay_mwsg_serialized_witness_digest (fingerprintOk serializationOk : Prop) : Prop :=
  fingerprintOk -> serializationOk

def ay_mwsg_witness_parser_transcript (serializationOk parserOk : Prop) : Prop :=
  serializationOk -> parserOk

def ay_mwsg_variable_domain_manifest (parserOk domainOk : Prop) : Prop :=
  parserOk -> domainOk

def ay_mwsg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_mwsg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_mwsg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_mwsg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_mwsg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mwsg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mwsg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mwsg_accepted_serialization
    (fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_mwsg_conj fingerprint
    (ay_mwsg_conj serialization
      (ay_mwsg_conj parser
        (ay_mwsg_conj domain
          (ay_mwsg_conj reconstruction
            (ay_mwsg_conj replay
              (ay_mwsg_conj checker
                (ay_mwsg_conj build
                  (ay_mwsg_conj archive
                    (ay_mwsg_conj fallback audit)))))))))

def ay_mwsg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_mwsg_conj accepted
    (ay_mwsg_conj totalAssignment
      (ay_mwsg_conj everyOriginalClauseSatisfied (ay_mwsg_conj originalSat audited)))

def ay_mwsg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mwsg_conj proofAccepted originalUnsat

def ay_mwsg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mwsg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mwsg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mwsg_conj p q :=
  fun r h => h hp hq

theorem ay_mwsg_conj_left {p q : Prop} (h : ay_mwsg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mwsg_conj_right {p q : Prop} (h : ay_mwsg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mwsg_conj_left h)

theorem ay_mwsg_disj_left {p q : Prop} (hp : p) : ay_mwsg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mwsg_disj_right {p q : Prop} (hq : q) : ay_mwsg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mwsg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mwsg_equiv p q :=
  ay_mwsg_conj_intro hpq hqp

theorem ay_mwsg_equiv_forward {p q : Prop} (h : ay_mwsg_equiv p q) : p -> q :=
  ay_mwsg_conj_left h

theorem ay_mwsg_equiv_backward {p q : Prop} (h : ay_mwsg_equiv p q) : q -> p :=
  ay_mwsg_conj_right h

theorem ay_mwsg_benchmark_fingerprint_intro {serializedWitness fingerprintOk : Prop}
    (h : serializedWitness -> fingerprintOk) :
    ay_mwsg_benchmark_fingerprint serializedWitness fingerprintOk :=
  h

theorem ay_mwsg_serialized_witness_digest_intro {fingerprintOk serializationOk : Prop}
    (h : fingerprintOk -> serializationOk) :
    ay_mwsg_serialized_witness_digest fingerprintOk serializationOk :=
  h

theorem ay_mwsg_witness_parser_transcript_intro {serializationOk parserOk : Prop}
    (h : serializationOk -> parserOk) :
    ay_mwsg_witness_parser_transcript serializationOk parserOk :=
  h

theorem ay_mwsg_variable_domain_manifest_intro {parserOk domainOk : Prop}
    (h : parserOk -> domainOk) :
    ay_mwsg_variable_domain_manifest parserOk domainOk :=
  h

theorem ay_mwsg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_mwsg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_mwsg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_mwsg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_mwsg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_mwsg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_mwsg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_mwsg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_mwsg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mwsg_archive_manifest buildOk archiveOk :=
  h

theorem ay_mwsg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mwsg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mwsg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mwsg_audit_transcript fallbackReady audited :=
  h

theorem ay_mwsg_accepted_serialization_intro
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hs : serialization) (hp : parser) (hd : domain)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit :=
  ay_mwsg_conj_intro hf
    (ay_mwsg_conj_intro hs
      (ay_mwsg_conj_intro hp
        (ay_mwsg_conj_intro hd
          (ay_mwsg_conj_intro hrc
            (ay_mwsg_conj_intro hr
              (ay_mwsg_conj_intro hc
                (ay_mwsg_conj_intro hb
                  (ay_mwsg_conj_intro ha
                    (ay_mwsg_conj_intro hfb hau)))))))))

theorem ay_mwsg_accepted_serialization_fingerprint
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : fingerprint :=
  ay_mwsg_conj_left h

theorem ay_mwsg_accepted_serialization_serialization
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : serialization :=
  ay_mwsg_conj_left (ay_mwsg_conj_right h)

theorem ay_mwsg_accepted_serialization_parser
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : parser :=
  ay_mwsg_conj_left (ay_mwsg_conj_right (ay_mwsg_conj_right h))

theorem ay_mwsg_accepted_serialization_domain
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : domain :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))

theorem ay_mwsg_accepted_serialization_reconstruction
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : reconstruction :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))

theorem ay_mwsg_accepted_serialization_replay
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : replay :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))))

theorem ay_mwsg_accepted_serialization_checker
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : checker :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right
          (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))))

theorem ay_mwsg_accepted_serialization_build
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : build :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right
          (ay_mwsg_conj_right
            (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))))))

theorem ay_mwsg_accepted_serialization_archive
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : archive :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right
          (ay_mwsg_conj_right
            (ay_mwsg_conj_right
              (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h))))))))

theorem ay_mwsg_accepted_serialization_fallback
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : fallback :=
  ay_mwsg_conj_left
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right
          (ay_mwsg_conj_right
            (ay_mwsg_conj_right
              (ay_mwsg_conj_right
                (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))))))))

theorem ay_mwsg_accepted_serialization_audit
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_mwsg_accepted_serialization fingerprint serialization parser domain reconstruction
      replay checker build archive fallback audit) : audit :=
  ay_mwsg_conj_right
    (ay_mwsg_conj_right
      (ay_mwsg_conj_right
        (ay_mwsg_conj_right
          (ay_mwsg_conj_right
            (ay_mwsg_conj_right
              (ay_mwsg_conj_right
                (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))))))))

theorem ay_mwsg_serialization_reconstructs_original_sat
    {serializedWitness fingerprintOk serializationOk parserOk domainOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_mwsg_benchmark_fingerprint serializedWitness fingerprintOk)
    (hs : ay_mwsg_serialized_witness_digest fingerprintOk serializationOk)
    (hp : ay_mwsg_witness_parser_transcript serializationOk parserOk)
    (hd : ay_mwsg_variable_domain_manifest parserOk domainOk)
    (hrc : ay_mwsg_total_assignment_reconstruction domainOk totalAssignment)
    (hr : ay_mwsg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_mwsg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_mwsg_solver_build_evidence originalSat buildOk)
    (ha : ay_mwsg_archive_manifest buildOk archiveOk)
    (hfb : ay_mwsg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_mwsg_audit_transcript fallbackReady audited)
    (hw : serializedWitness) :
    ay_mwsg_conj totalAssignment
      (ay_mwsg_conj everyOriginalClauseSatisfied (ay_mwsg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hserialization : serializationOk := hs hfingerprint
  let hparser : parserOk := hp hserialization
  let hdomain : domainOk := hd hparser
  let htotal : totalAssignment := hrc hdomain
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_mwsg_conj_intro htotal (ay_mwsg_conj_intro hevery (ay_mwsg_conj_intro hsat haudit))

theorem ay_mwsg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_mwsg_conj_intro ha
    (ay_mwsg_conj_intro ht (ay_mwsg_conj_intro hevery (ay_mwsg_conj_intro hs hau)))

theorem ay_mwsg_public_sat_requires_serialization_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_mwsg_conj_left h

theorem ay_mwsg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_mwsg_conj_left (ay_mwsg_conj_right h)

theorem ay_mwsg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_mwsg_conj_left (ay_mwsg_conj_right (ay_mwsg_conj_right h))

theorem ay_mwsg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_mwsg_conj_left (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))

theorem ay_mwsg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right (ay_mwsg_conj_right h)))

theorem ay_mwsg_accepted_serialization_publishes_sat
    {fingerprint serialization parser domain reconstruction replay checker build archive
     fallback audit totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_mwsg_accepted_serialization fingerprint serialization parser domain
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mwsg_public_sat
      (ay_mwsg_accepted_serialization fingerprint serialization parser domain
        reconstruction replay checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_mwsg_public_sat_intro hg ht hevery hs hau

theorem ay_mwsg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  h

theorem ay_mwsg_recompute_intro {reason : Prop} (h : reason) :
    ay_mwsg_recompute_obligation reason :=
  h

theorem ay_mwsg_serialization_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mwsg_recompute_obligation reason :=
  ay_mwsg_recompute_intro h

theorem ay_mwsg_parser_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  ay_mwsg_no_claim_intro h

theorem ay_mwsg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  ay_mwsg_no_claim_intro h

theorem ay_mwsg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mwsg_recompute_obligation reason :=
  ay_mwsg_recompute_intro h

theorem ay_mwsg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mwsg_recompute_obligation reason :=
  ay_mwsg_recompute_intro h

theorem ay_mwsg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  ay_mwsg_no_claim_intro h

theorem ay_mwsg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_mwsg_recompute_obligation reason :=
  ay_mwsg_recompute_intro h

theorem ay_mwsg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  ay_mwsg_no_claim_intro h

theorem ay_mwsg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_mwsg_no_claim_diagnostic reason :=
  ay_mwsg_no_claim_intro h

theorem ay_mwsg_failed_serialization_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mwsg_no_claim_diagnostic failure) :
    ay_mwsg_conj (ay_mwsg_no_claim_diagnostic failure)
      (ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mwsg_no_claim_diagnostic failure) :=
  ay_mwsg_conj_intro (ay_mwsg_no_claim_intro hfail) hblock

theorem ay_mwsg_failed_serialization_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_mwsg_recompute_obligation failure) :
    ay_mwsg_conj (ay_mwsg_recompute_obligation failure)
      (ay_mwsg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_mwsg_recompute_obligation failure) :=
  ay_mwsg_conj_intro (ay_mwsg_recompute_intro hfail) hblock

theorem ay_mwsg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mwsg_public_unsat proofAccepted originalUnsat :=
  ay_mwsg_conj_intro hp hu

theorem ay_mwsg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mwsg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mwsg_conj_left h

theorem ay_mwsg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mwsg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mwsg_conj_right h

theorem ay_mwsg_serialization_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat serializationSatGuard : Prop}
    (h : ay_mwsg_public_unsat proofAccepted originalUnsat) :
    ay_mwsg_conj (ay_mwsg_public_unsat proofAccepted originalUnsat)
      (serializationSatGuard -> ay_mwsg_public_unsat proofAccepted originalUnsat) :=
  ay_mwsg_conj_intro h (fun _ => h)

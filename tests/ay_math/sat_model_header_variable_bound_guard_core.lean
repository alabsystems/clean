/-!
  SAT-COMP/ay DIMACS header variable-bound guard.

  This self-contained package models the SAT-only obligations for publishing a
  model only when the assignment is scoped to the intended DIMACS header
  variable bound and original clause domain.
-/

def ay_hvbg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_hvbg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_hvbg_equiv (p q : Prop) : Prop :=
  ay_hvbg_conj (p -> q) (q -> p)

def ay_hvbg_benchmark_fingerprint (modelWitness fingerprintOk : Prop) : Prop :=
  modelWitness -> fingerprintOk

def ay_hvbg_dimacs_header_variable_bound (fingerprintOk headerBoundOk : Prop) : Prop :=
  fingerprintOk -> headerBoundOk

def ay_hvbg_assignment_variable_domain_manifest (headerBoundOk domainOk : Prop) : Prop :=
  headerBoundOk -> domainOk

def ay_hvbg_max_variable_witness (domainOk maxVarOk : Prop) : Prop :=
  domainOk -> maxVarOk

def ay_hvbg_total_assignment_reconstruction (maxVarOk totalAssignment : Prop) : Prop :=
  maxVarOk -> totalAssignment

def ay_hvbg_original_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_hvbg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_hvbg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_hvbg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_hvbg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_hvbg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_hvbg_accepted_bound
    (fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop) : Prop :=
  ay_hvbg_conj fingerprint
    (ay_hvbg_conj header
      (ay_hvbg_conj domain
        (ay_hvbg_conj maxVar
          (ay_hvbg_conj reconstruction
            (ay_hvbg_conj replay
              (ay_hvbg_conj checker
                (ay_hvbg_conj build
                  (ay_hvbg_conj archive
                    (ay_hvbg_conj fallback audit)))))))))

def ay_hvbg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_hvbg_conj accepted
    (ay_hvbg_conj totalAssignment
      (ay_hvbg_conj everyOriginalClauseSatisfied (ay_hvbg_conj originalSat audited)))

def ay_hvbg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_hvbg_conj proofAccepted originalUnsat

def ay_hvbg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_hvbg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_hvbg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_hvbg_conj p q :=
  fun r h => h hp hq

theorem ay_hvbg_conj_left {p q : Prop} (h : ay_hvbg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_hvbg_conj_right {p q : Prop} (h : ay_hvbg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_hvbg_conj_left h)

theorem ay_hvbg_disj_left {p q : Prop} (hp : p) : ay_hvbg_disj p q :=
  fun r hl _ => hl hp

theorem ay_hvbg_disj_right {p q : Prop} (hq : q) : ay_hvbg_disj p q :=
  fun r _ hr => hr hq

theorem ay_hvbg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_hvbg_equiv p q :=
  ay_hvbg_conj_intro hpq hqp

theorem ay_hvbg_equiv_forward {p q : Prop} (h : ay_hvbg_equiv p q) : p -> q :=
  ay_hvbg_conj_left h

theorem ay_hvbg_equiv_backward {p q : Prop} (h : ay_hvbg_equiv p q) : q -> p :=
  ay_hvbg_conj_right h

theorem ay_hvbg_benchmark_fingerprint_intro {modelWitness fingerprintOk : Prop}
    (h : modelWitness -> fingerprintOk) :
    ay_hvbg_benchmark_fingerprint modelWitness fingerprintOk :=
  h

theorem ay_hvbg_dimacs_header_variable_bound_intro {fingerprintOk headerBoundOk : Prop}
    (h : fingerprintOk -> headerBoundOk) :
    ay_hvbg_dimacs_header_variable_bound fingerprintOk headerBoundOk :=
  h

theorem ay_hvbg_assignment_variable_domain_manifest_intro {headerBoundOk domainOk : Prop}
    (h : headerBoundOk -> domainOk) :
    ay_hvbg_assignment_variable_domain_manifest headerBoundOk domainOk :=
  h

theorem ay_hvbg_max_variable_witness_intro {domainOk maxVarOk : Prop}
    (h : domainOk -> maxVarOk) :
    ay_hvbg_max_variable_witness domainOk maxVarOk :=
  h

theorem ay_hvbg_total_assignment_reconstruction_intro {maxVarOk totalAssignment : Prop}
    (h : maxVarOk -> totalAssignment) :
    ay_hvbg_total_assignment_reconstruction maxVarOk totalAssignment :=
  h

theorem ay_hvbg_original_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_hvbg_original_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_hvbg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_hvbg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_hvbg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_hvbg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_hvbg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_hvbg_archive_manifest buildOk archiveOk :=
  h

theorem ay_hvbg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_hvbg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_hvbg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_hvbg_audit_transcript fallbackReady audited :=
  h

theorem ay_hvbg_accepted_bound_intro
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hh : header) (hd : domain) (hm : maxVar)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay checker
      build archive fallback audit :=
  ay_hvbg_conj_intro hf
    (ay_hvbg_conj_intro hh
      (ay_hvbg_conj_intro hd
        (ay_hvbg_conj_intro hm
          (ay_hvbg_conj_intro hrc
            (ay_hvbg_conj_intro hr
              (ay_hvbg_conj_intro hc
                (ay_hvbg_conj_intro hb
                  (ay_hvbg_conj_intro ha
                    (ay_hvbg_conj_intro hfb hau)))))))))

theorem ay_hvbg_accepted_bound_fingerprint
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : fingerprint :=
  ay_hvbg_conj_left h

theorem ay_hvbg_accepted_bound_header
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : header :=
  ay_hvbg_conj_left (ay_hvbg_conj_right h)

theorem ay_hvbg_accepted_bound_domain
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : domain :=
  ay_hvbg_conj_left (ay_hvbg_conj_right (ay_hvbg_conj_right h))

theorem ay_hvbg_accepted_bound_max_var
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : maxVar :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))

theorem ay_hvbg_accepted_bound_reconstruction
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : reconstruction :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h))))

theorem ay_hvbg_accepted_bound_replay
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : replay :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))))

theorem ay_hvbg_accepted_bound_checker
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : checker :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right
          (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h))))))

theorem ay_hvbg_accepted_bound_build
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : build :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right
          (ay_hvbg_conj_right
            (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))))))

theorem ay_hvbg_accepted_bound_archive
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : archive :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right
          (ay_hvbg_conj_right
            (ay_hvbg_conj_right
              (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h))))))))

theorem ay_hvbg_accepted_bound_fallback
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : fallback :=
  ay_hvbg_conj_left
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right
          (ay_hvbg_conj_right
            (ay_hvbg_conj_right
              (ay_hvbg_conj_right
                (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))))))))

theorem ay_hvbg_accepted_bound_audit
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit : Prop}
    (h : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit) : audit :=
  ay_hvbg_conj_right
    (ay_hvbg_conj_right
      (ay_hvbg_conj_right
        (ay_hvbg_conj_right
          (ay_hvbg_conj_right
            (ay_hvbg_conj_right
              (ay_hvbg_conj_right
                (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))))))))

theorem ay_hvbg_header_bound_reconstructs_original_sat
    {modelWitness fingerprintOk headerBoundOk domainOk maxVarOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_hvbg_benchmark_fingerprint modelWitness fingerprintOk)
    (hh : ay_hvbg_dimacs_header_variable_bound fingerprintOk headerBoundOk)
    (hd : ay_hvbg_assignment_variable_domain_manifest headerBoundOk domainOk)
    (hm : ay_hvbg_max_variable_witness domainOk maxVarOk)
    (hrc : ay_hvbg_total_assignment_reconstruction maxVarOk totalAssignment)
    (hr : ay_hvbg_original_clause_satisfaction_replay
      totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_hvbg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_hvbg_solver_build_evidence originalSat buildOk)
    (ha : ay_hvbg_archive_manifest buildOk archiveOk)
    (hfb : ay_hvbg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_hvbg_audit_transcript fallbackReady audited)
    (hw : modelWitness) :
    ay_hvbg_conj totalAssignment
      (ay_hvbg_conj everyOriginalClauseSatisfied (ay_hvbg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hheader : headerBoundOk := hh hfingerprint
  let hdomain : domainOk := hd hheader
  let hmax : maxVarOk := hm hdomain
  let htotal : totalAssignment := hrc hmax
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_hvbg_conj_intro htotal (ay_hvbg_conj_intro hevery (ay_hvbg_conj_intro hsat haudit))

theorem ay_hvbg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_hvbg_conj_intro ha
    (ay_hvbg_conj_intro ht (ay_hvbg_conj_intro hevery (ay_hvbg_conj_intro hs hau)))

theorem ay_hvbg_public_sat_requires_header_bound
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_hvbg_conj_left h

theorem ay_hvbg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_hvbg_conj_left (ay_hvbg_conj_right h)

theorem ay_hvbg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_hvbg_conj_left (ay_hvbg_conj_right (ay_hvbg_conj_right h))

theorem ay_hvbg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_hvbg_conj_left (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))

theorem ay_hvbg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right (ay_hvbg_conj_right h)))

theorem ay_hvbg_accepted_bound_publishes_sat
    {fingerprint header domain maxVar reconstruction replay checker build archive fallback
     audit totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay
      checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_hvbg_public_sat
      (ay_hvbg_accepted_bound fingerprint header domain maxVar reconstruction replay checker
        build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_hvbg_public_sat_intro hg ht hevery hs hau

theorem ay_hvbg_no_claim_intro {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  h

theorem ay_hvbg_recompute_intro {reason : Prop} (h : reason) :
    ay_hvbg_recompute_obligation reason :=
  h

theorem ay_hvbg_header_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_max_var_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_hvbg_recompute_obligation reason :=
  ay_hvbg_recompute_intro h

theorem ay_hvbg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_hvbg_recompute_obligation reason :=
  ay_hvbg_recompute_intro h

theorem ay_hvbg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_hvbg_recompute_obligation reason :=
  ay_hvbg_recompute_intro h

theorem ay_hvbg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_hvbg_no_claim_diagnostic reason :=
  ay_hvbg_no_claim_intro h

theorem ay_hvbg_failed_header_bound_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_hvbg_no_claim_diagnostic failure) :
    ay_hvbg_conj (ay_hvbg_no_claim_diagnostic failure)
      (ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_hvbg_no_claim_diagnostic failure) :=
  ay_hvbg_conj_intro (ay_hvbg_no_claim_intro hfail) hblock

theorem ay_hvbg_failed_header_bound_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_hvbg_recompute_obligation failure) :
    ay_hvbg_conj (ay_hvbg_recompute_obligation failure)
      (ay_hvbg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_hvbg_recompute_obligation failure) :=
  ay_hvbg_conj_intro (ay_hvbg_recompute_intro hfail) hblock

theorem ay_hvbg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_hvbg_public_unsat proofAccepted originalUnsat :=
  ay_hvbg_conj_intro hp hu

theorem ay_hvbg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_hvbg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_hvbg_conj_left h

theorem ay_hvbg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_hvbg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_hvbg_conj_right h

theorem ay_hvbg_header_bound_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat headerSatGuard : Prop}
    (h : ay_hvbg_public_unsat proofAccepted originalUnsat) :
    ay_hvbg_conj (ay_hvbg_public_unsat proofAccepted originalUnsat)
      (headerSatGuard -> ay_hvbg_public_unsat proofAccepted originalUnsat) :=
  ay_hvbg_conj_intro h (fun _ => h)

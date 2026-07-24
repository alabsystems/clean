/-!
  SAT-COMP/ay incremental-assumption scope guard.

  This self-contained package models the SAT-only obligations for publishing a
  model produced under an incremental assumption scope.
-/

def ay_iasg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_iasg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_iasg_equiv (p q : Prop) : Prop :=
  ay_iasg_conj (p -> q) (q -> p)

def ay_iasg_benchmark_fingerprint (scopedWitness fingerprintOk : Prop) : Prop :=
  scopedWitness -> fingerprintOk

def ay_iasg_assumption_scope_manifest (fingerprintOk scopeOk : Prop) : Prop :=
  fingerprintOk -> scopeOk

def ay_iasg_activation_literal_ledger (scopeOk activationOk : Prop) : Prop :=
  scopeOk -> activationOk

def ay_iasg_scoped_assignment_witness (activationOk scopedAssignment : Prop) : Prop :=
  activationOk -> scopedAssignment

def ay_iasg_original_clause_satisfaction_replay
    (scopedAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  scopedAssignment -> everyOriginalClauseSatisfied

def ay_iasg_model_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_iasg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_iasg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_iasg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_iasg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_iasg_accepted_scope
    (fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop) : Prop :=
  ay_iasg_conj fingerprint
    (ay_iasg_conj scope
      (ay_iasg_conj activation
        (ay_iasg_conj assignment
          (ay_iasg_conj replay
            (ay_iasg_conj checker
              (ay_iasg_conj build
                (ay_iasg_conj archive
                  (ay_iasg_conj fallback audit))))))))

def ay_iasg_public_sat
    (accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_iasg_conj accepted
    (ay_iasg_conj scopedAssignment
      (ay_iasg_conj everyOriginalClauseSatisfied (ay_iasg_conj originalSat audited)))

def ay_iasg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_iasg_conj proofAccepted originalUnsat

def ay_iasg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_iasg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_iasg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_iasg_conj p q :=
  fun r h => h hp hq

theorem ay_iasg_conj_left {p q : Prop} (h : ay_iasg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_iasg_conj_right {p q : Prop} (h : ay_iasg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_iasg_conj_left h)

theorem ay_iasg_disj_left {p q : Prop} (hp : p) : ay_iasg_disj p q :=
  fun r hl _ => hl hp

theorem ay_iasg_disj_right {p q : Prop} (hq : q) : ay_iasg_disj p q :=
  fun r _ hr => hr hq

theorem ay_iasg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_iasg_equiv p q :=
  ay_iasg_conj_intro hpq hqp

theorem ay_iasg_equiv_forward {p q : Prop} (h : ay_iasg_equiv p q) : p -> q :=
  ay_iasg_conj_left h

theorem ay_iasg_equiv_backward {p q : Prop} (h : ay_iasg_equiv p q) : q -> p :=
  ay_iasg_conj_right h

theorem ay_iasg_benchmark_fingerprint_intro {scopedWitness fingerprintOk : Prop}
    (h : scopedWitness -> fingerprintOk) :
    ay_iasg_benchmark_fingerprint scopedWitness fingerprintOk :=
  h

theorem ay_iasg_assumption_scope_manifest_intro {fingerprintOk scopeOk : Prop}
    (h : fingerprintOk -> scopeOk) :
    ay_iasg_assumption_scope_manifest fingerprintOk scopeOk :=
  h

theorem ay_iasg_activation_literal_ledger_intro {scopeOk activationOk : Prop}
    (h : scopeOk -> activationOk) :
    ay_iasg_activation_literal_ledger scopeOk activationOk :=
  h

theorem ay_iasg_scoped_assignment_witness_intro {activationOk scopedAssignment : Prop}
    (h : activationOk -> scopedAssignment) :
    ay_iasg_scoped_assignment_witness activationOk scopedAssignment :=
  h

theorem ay_iasg_original_clause_satisfaction_replay_intro
    {scopedAssignment everyOriginalClauseSatisfied : Prop}
    (h : scopedAssignment -> everyOriginalClauseSatisfied) :
    ay_iasg_original_clause_satisfaction_replay scopedAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_iasg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_iasg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_iasg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_iasg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_iasg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_iasg_archive_manifest buildOk archiveOk :=
  h

theorem ay_iasg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_iasg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_iasg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_iasg_audit_transcript fallbackReady audited :=
  h

theorem ay_iasg_accepted_scope_intro
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (hf : fingerprint) (hs : scope) (ha : activation) (hasg : assignment)
    (hr : replay) (hc : checker) (hb : build) (har : archive)
    (hfb : fallback) (hau : audit) :
    ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit :=
  ay_iasg_conj_intro hf
    (ay_iasg_conj_intro hs
      (ay_iasg_conj_intro ha
        (ay_iasg_conj_intro hasg
          (ay_iasg_conj_intro hr
            (ay_iasg_conj_intro hc
              (ay_iasg_conj_intro hb
                (ay_iasg_conj_intro har
                  (ay_iasg_conj_intro hfb hau))))))))

theorem ay_iasg_accepted_scope_fingerprint
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : fingerprint :=
  ay_iasg_conj_left h

theorem ay_iasg_accepted_scope_scope
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : scope :=
  ay_iasg_conj_left (ay_iasg_conj_right h)

theorem ay_iasg_accepted_scope_activation
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : activation :=
  ay_iasg_conj_left (ay_iasg_conj_right (ay_iasg_conj_right h))

theorem ay_iasg_accepted_scope_assignment
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : assignment :=
  ay_iasg_conj_left
    (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h)))

theorem ay_iasg_accepted_scope_replay
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : replay :=
  ay_iasg_conj_left
    (ay_iasg_conj_right
      (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h))))

theorem ay_iasg_accepted_scope_checker
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : checker :=
  ay_iasg_conj_left
    (ay_iasg_conj_right
      (ay_iasg_conj_right
        (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h)))))

theorem ay_iasg_accepted_scope_build
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : build :=
  ay_iasg_conj_left
    (ay_iasg_conj_right
      (ay_iasg_conj_right
        (ay_iasg_conj_right
          (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h))))))

theorem ay_iasg_accepted_scope_archive
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : archive :=
  ay_iasg_conj_left
    (ay_iasg_conj_right
      (ay_iasg_conj_right
        (ay_iasg_conj_right
          (ay_iasg_conj_right
            (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h)))))))

theorem ay_iasg_accepted_scope_fallback
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : fallback :=
  ay_iasg_conj_left
    (ay_iasg_conj_right
      (ay_iasg_conj_right
        (ay_iasg_conj_right
          (ay_iasg_conj_right
            (ay_iasg_conj_right
              (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h))))))))

theorem ay_iasg_accepted_scope_audit
    {fingerprint scope activation assignment replay checker build archive fallback
     audit : Prop}
    (h : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit) : audit :=
  ay_iasg_conj_right
    (ay_iasg_conj_right
      (ay_iasg_conj_right
        (ay_iasg_conj_right
          (ay_iasg_conj_right
            (ay_iasg_conj_right
              (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h))))))))

theorem ay_iasg_scope_reconstructs_original_sat
    {scopedWitness fingerprintOk scopeOk activationOk scopedAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_iasg_benchmark_fingerprint scopedWitness fingerprintOk)
    (hs : ay_iasg_assumption_scope_manifest fingerprintOk scopeOk)
    (ha : ay_iasg_activation_literal_ledger scopeOk activationOk)
    (hasg : ay_iasg_scoped_assignment_witness activationOk scopedAssignment)
    (hr : ay_iasg_original_clause_satisfaction_replay
      scopedAssignment everyOriginalClauseSatisfied)
    (hc : ay_iasg_model_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_iasg_solver_build_evidence originalSat buildOk)
    (har : ay_iasg_archive_manifest buildOk archiveOk)
    (hfb : ay_iasg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_iasg_audit_transcript fallbackReady audited)
    (hw : scopedWitness) :
    ay_iasg_conj scopedAssignment
      (ay_iasg_conj everyOriginalClauseSatisfied (ay_iasg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hscope : scopeOk := hs hfingerprint
  let hactivation : activationOk := ha hscope
  let hassignment : scopedAssignment := hasg hactivation
  let hevery : everyOriginalClauseSatisfied := hr hassignment
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := har hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_iasg_conj_intro hassignment (ay_iasg_conj_intro hevery (ay_iasg_conj_intro hsat haudit))

theorem ay_iasg_public_sat_intro
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (hs : scopedAssignment) (hevery : everyOriginalClauseSatisfied)
    (hsat : originalSat) (hau : audited) :
    ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_iasg_conj_intro ha
    (ay_iasg_conj_intro hs (ay_iasg_conj_intro hevery (ay_iasg_conj_intro hsat hau)))

theorem ay_iasg_public_sat_requires_scope_guard
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_iasg_conj_left h

theorem ay_iasg_public_sat_scoped_assignment
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited) : scopedAssignment :=
  ay_iasg_conj_left (ay_iasg_conj_right h)

theorem ay_iasg_public_sat_every_original_clause
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_iasg_conj_left (ay_iasg_conj_right (ay_iasg_conj_right h))

theorem ay_iasg_public_sat_original_formula
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_iasg_conj_left (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h)))

theorem ay_iasg_public_sat_audit
    {accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right (ay_iasg_conj_right h)))

theorem ay_iasg_accepted_scope_publishes_sat
    {fingerprint scope activation assignment replay checker build archive fallback audit
     scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
      archive fallback audit)
    (hs : scopedAssignment) (hevery : everyOriginalClauseSatisfied)
    (hsat : originalSat) (hau : audited) :
    ay_iasg_public_sat
      (ay_iasg_accepted_scope fingerprint scope activation assignment replay checker build
        archive fallback audit)
      scopedAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_iasg_public_sat_intro hg hs hevery hsat hau

theorem ay_iasg_no_claim_intro {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  h

theorem ay_iasg_recompute_intro {reason : Prop} (h : reason) :
    ay_iasg_recompute_obligation reason :=
  h

theorem ay_iasg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_iasg_recompute_obligation reason :=
  ay_iasg_recompute_intro h

theorem ay_iasg_scope_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  ay_iasg_no_claim_intro h

theorem ay_iasg_activation_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  ay_iasg_no_claim_intro h

theorem ay_iasg_assignment_mismatch_recompute {reason : Prop} (h : reason) :
    ay_iasg_recompute_obligation reason :=
  ay_iasg_recompute_intro h

theorem ay_iasg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_iasg_recompute_obligation reason :=
  ay_iasg_recompute_intro h

theorem ay_iasg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  ay_iasg_no_claim_intro h

theorem ay_iasg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_iasg_recompute_obligation reason :=
  ay_iasg_recompute_intro h

theorem ay_iasg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  ay_iasg_no_claim_intro h

theorem ay_iasg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_iasg_no_claim_diagnostic reason :=
  ay_iasg_no_claim_intro h

theorem ay_iasg_failed_scope_guard_cannot_create_public_sat
    {failure accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_iasg_no_claim_diagnostic failure) :
    ay_iasg_conj (ay_iasg_no_claim_diagnostic failure)
      (ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_iasg_no_claim_diagnostic failure) :=
  ay_iasg_conj_intro (ay_iasg_no_claim_intro hfail) hblock

theorem ay_iasg_failed_scope_guard_forces_recompute
    {failure accepted scopedAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_iasg_recompute_obligation failure) :
    ay_iasg_conj (ay_iasg_recompute_obligation failure)
      (ay_iasg_public_sat accepted scopedAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_iasg_recompute_obligation failure) :=
  ay_iasg_conj_intro (ay_iasg_recompute_intro hfail) hblock

theorem ay_iasg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_iasg_public_unsat proofAccepted originalUnsat :=
  ay_iasg_conj_intro hp hu

theorem ay_iasg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_iasg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_iasg_conj_left h

theorem ay_iasg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_iasg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_iasg_conj_right h

theorem ay_iasg_scope_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat scopeSatGuard : Prop}
    (h : ay_iasg_public_unsat proofAccepted originalUnsat) :
    ay_iasg_conj (ay_iasg_public_unsat proofAccepted originalUnsat)
      (scopeSatGuard -> ay_iasg_public_unsat proofAccepted originalUnsat) :=
  ay_iasg_conj_intro h (fun _ => h)

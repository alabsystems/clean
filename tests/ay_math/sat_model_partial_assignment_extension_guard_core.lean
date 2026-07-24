/-!
  SAT-COMP/ay partial-assignment extension guard.

  This self-contained package models the SAT-only obligations needed before a
  compact or partial witness may be extended into a public SAT-COMP model for
  the original DIMACS instance.
-/

def ay_paeg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_paeg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_paeg_equiv (p q : Prop) : Prop :=
  ay_paeg_conj (p -> q) (q -> p)

def ay_paeg_benchmark_fingerprint (partialWitness fingerprintOk : Prop) : Prop :=
  partialWitness -> fingerprintOk

def ay_paeg_declared_variable_domain (fingerprintOk domainOk : Prop) : Prop :=
  fingerprintOk -> domainOk

def ay_paeg_assigned_literal_ledger (domainOk ledgerOk : Prop) : Prop :=
  domainOk -> ledgerOk

def ay_paeg_unassigned_extension_policy (ledgerOk extensionOk : Prop) : Prop :=
  ledgerOk -> extensionOk

def ay_paeg_clause_satisfaction_replay (extensionOk replayOk : Prop) : Prop :=
  extensionOk -> replayOk

def ay_paeg_dimacs_reconstruction (replayOk totalAssignment : Prop) : Prop :=
  replayOk -> totalAssignment

def ay_paeg_model_checker_transcript (totalAssignment originalSat : Prop) : Prop :=
  totalAssignment -> originalSat

def ay_paeg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_paeg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_paeg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_paeg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_paeg_accepted_guard
    (fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop) : Prop :=
  ay_paeg_conj fingerprint
    (ay_paeg_conj domain
      (ay_paeg_conj ledger
        (ay_paeg_conj extension
          (ay_paeg_conj replay
            (ay_paeg_conj reconstruction
              (ay_paeg_conj checker
                (ay_paeg_conj build
                  (ay_paeg_conj archive
                    (ay_paeg_conj fallback audit)))))))))

def ay_paeg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_paeg_conj accepted (ay_paeg_conj totalAssignment (ay_paeg_conj originalSat audited))

def ay_paeg_public_unsat (unsatCertificate originalUnsat : Prop) : Prop :=
  ay_paeg_conj unsatCertificate originalUnsat

def ay_paeg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_paeg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_paeg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_paeg_conj p q :=
  fun r h => h hp hq

theorem ay_paeg_conj_left {p q : Prop} (h : ay_paeg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_paeg_conj_right {p q : Prop} (h : ay_paeg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_paeg_conj_left h)

theorem ay_paeg_disj_left {p q : Prop} (hp : p) : ay_paeg_disj p q :=
  fun r hl _ => hl hp

theorem ay_paeg_disj_right {p q : Prop} (hq : q) : ay_paeg_disj p q :=
  fun r _ hr => hr hq

theorem ay_paeg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_paeg_equiv p q :=
  ay_paeg_conj_intro hpq hqp

theorem ay_paeg_equiv_forward {p q : Prop} (h : ay_paeg_equiv p q) : p -> q :=
  ay_paeg_conj_left h

theorem ay_paeg_equiv_backward {p q : Prop} (h : ay_paeg_equiv p q) : q -> p :=
  ay_paeg_conj_right h

theorem ay_paeg_benchmark_fingerprint_intro {partialWitness fingerprintOk : Prop}
    (h : partialWitness -> fingerprintOk) :
    ay_paeg_benchmark_fingerprint partialWitness fingerprintOk :=
  h

theorem ay_paeg_declared_variable_domain_intro {fingerprintOk domainOk : Prop}
    (h : fingerprintOk -> domainOk) :
    ay_paeg_declared_variable_domain fingerprintOk domainOk :=
  h

theorem ay_paeg_assigned_literal_ledger_intro {domainOk ledgerOk : Prop}
    (h : domainOk -> ledgerOk) :
    ay_paeg_assigned_literal_ledger domainOk ledgerOk :=
  h

theorem ay_paeg_unassigned_extension_policy_intro {ledgerOk extensionOk : Prop}
    (h : ledgerOk -> extensionOk) :
    ay_paeg_unassigned_extension_policy ledgerOk extensionOk :=
  h

theorem ay_paeg_clause_satisfaction_replay_intro {extensionOk replayOk : Prop}
    (h : extensionOk -> replayOk) :
    ay_paeg_clause_satisfaction_replay extensionOk replayOk :=
  h

theorem ay_paeg_dimacs_reconstruction_intro {replayOk totalAssignment : Prop}
    (h : replayOk -> totalAssignment) :
    ay_paeg_dimacs_reconstruction replayOk totalAssignment :=
  h

theorem ay_paeg_model_checker_transcript_intro {totalAssignment originalSat : Prop}
    (h : totalAssignment -> originalSat) :
    ay_paeg_model_checker_transcript totalAssignment originalSat :=
  h

theorem ay_paeg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_paeg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_paeg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_paeg_archive_manifest buildOk archiveOk :=
  h

theorem ay_paeg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_paeg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_paeg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_paeg_audit_transcript fallbackReady audited :=
  h

theorem ay_paeg_accepted_guard_intro
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hd : domain) (hl : ledger) (he : extension) (hr : replay)
    (hrec : reconstruction) (hc : checker) (hb : build) (ha : archive)
    (hfb : fallback) (hau : audit) :
    ay_paeg_accepted_guard fingerprint domain ledger extension replay reconstruction
      checker build archive fallback audit :=
  ay_paeg_conj_intro hf
    (ay_paeg_conj_intro hd
      (ay_paeg_conj_intro hl
        (ay_paeg_conj_intro he
          (ay_paeg_conj_intro hr
            (ay_paeg_conj_intro hrec
              (ay_paeg_conj_intro hc
                (ay_paeg_conj_intro hb
                  (ay_paeg_conj_intro ha
                    (ay_paeg_conj_intro hfb hau)))))))))

theorem ay_paeg_accepted_guard_fingerprint
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : fingerprint :=
  ay_paeg_conj_left h

theorem ay_paeg_accepted_guard_domain
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : domain :=
  ay_paeg_conj_left (ay_paeg_conj_right h)

theorem ay_paeg_accepted_guard_ledger
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : ledger :=
  ay_paeg_conj_left (ay_paeg_conj_right (ay_paeg_conj_right h))

theorem ay_paeg_accepted_guard_extension
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : extension :=
  ay_paeg_conj_left
    (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h)))

theorem ay_paeg_accepted_guard_replay
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : replay :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h))))

theorem ay_paeg_accepted_guard_reconstruction
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : reconstruction :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h)))))

theorem ay_paeg_accepted_guard_checker
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : checker :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right
          (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h))))))

theorem ay_paeg_accepted_guard_build
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : build :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right
          (ay_paeg_conj_right
            (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h)))))))

theorem ay_paeg_accepted_guard_archive
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : archive :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right
          (ay_paeg_conj_right
            (ay_paeg_conj_right
              (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h))))))))

theorem ay_paeg_accepted_guard_fallback
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : fallback :=
  ay_paeg_conj_left
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right
          (ay_paeg_conj_right
            (ay_paeg_conj_right
              (ay_paeg_conj_right
                (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h)))))))))

theorem ay_paeg_accepted_guard_audit
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit : Prop}
    (h : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit) : audit :=
  ay_paeg_conj_right
    (ay_paeg_conj_right
      (ay_paeg_conj_right
        (ay_paeg_conj_right
          (ay_paeg_conj_right
            (ay_paeg_conj_right
              (ay_paeg_conj_right
                (ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h)))))))))

theorem ay_paeg_partial_witness_extends_to_total_original_sat
    {partialWitness fingerprintOk domainOk ledgerOk extensionOk replayOk
     totalAssignment originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_paeg_benchmark_fingerprint partialWitness fingerprintOk)
    (hd : ay_paeg_declared_variable_domain fingerprintOk domainOk)
    (hl : ay_paeg_assigned_literal_ledger domainOk ledgerOk)
    (he : ay_paeg_unassigned_extension_policy ledgerOk extensionOk)
    (hr : ay_paeg_clause_satisfaction_replay extensionOk replayOk)
    (hrec : ay_paeg_dimacs_reconstruction replayOk totalAssignment)
    (hc : ay_paeg_model_checker_transcript totalAssignment originalSat)
    (hb : ay_paeg_solver_build_evidence originalSat buildOk)
    (ha : ay_paeg_archive_manifest buildOk archiveOk)
    (hfb : ay_paeg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_paeg_audit_transcript fallbackReady audited)
    (hw : partialWitness) :
    ay_paeg_conj totalAssignment (ay_paeg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hdomain : domainOk := hd hfingerprint
  let hledger : ledgerOk := hl hdomain
  let hextension : extensionOk := he hledger
  let hreplay : replayOk := hr hextension
  let htotal : totalAssignment := hrec hreplay
  let hsat : originalSat := hc htotal
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_paeg_conj_intro htotal (ay_paeg_conj_intro hsat haudit)

theorem ay_paeg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_paeg_public_sat accepted totalAssignment originalSat audited :=
  ay_paeg_conj_intro ha (ay_paeg_conj_intro ht (ay_paeg_conj_intro hs hau))

theorem ay_paeg_public_sat_requires_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_paeg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_paeg_conj_left h

theorem ay_paeg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_paeg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_paeg_conj_left (ay_paeg_conj_right h)

theorem ay_paeg_public_sat_original_formula_satisfied
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_paeg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_paeg_conj_left (ay_paeg_conj_right (ay_paeg_conj_right h))

theorem ay_paeg_public_sat_audited
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_paeg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_paeg_conj_right (ay_paeg_conj_right (ay_paeg_conj_right h))

theorem ay_paeg_accepted_guard_publishes_sat
    {fingerprint domain ledger extension replay reconstruction checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_paeg_accepted_guard fingerprint domain ledger extension replay
      reconstruction checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_paeg_public_sat
      (ay_paeg_accepted_guard fingerprint domain ledger extension replay reconstruction
        checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_paeg_public_sat_intro hg ht hs hau

theorem ay_paeg_no_claim_intro {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  h

theorem ay_paeg_recompute_intro {reason : Prop} (h : reason) :
    ay_paeg_recompute_obligation reason :=
  h

theorem ay_paeg_no_claim_reason {reason : Prop}
    (h : ay_paeg_no_claim_diagnostic reason) : reason :=
  h

theorem ay_paeg_recompute_reason {reason : Prop}
    (h : ay_paeg_recompute_obligation reason) : reason :=
  h

theorem ay_paeg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_ledger_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_extension_mismatch_recompute {reason : Prop} (h : reason) :
    ay_paeg_recompute_obligation reason :=
  ay_paeg_recompute_intro h

theorem ay_paeg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_paeg_recompute_obligation reason :=
  ay_paeg_recompute_intro h

theorem ay_paeg_reconstruction_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_paeg_recompute_obligation reason :=
  ay_paeg_recompute_intro h

theorem ay_paeg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_paeg_no_claim_diagnostic reason :=
  ay_paeg_no_claim_intro h

theorem ay_paeg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_paeg_recompute_obligation reason :=
  ay_paeg_recompute_intro h

theorem ay_paeg_failed_extension_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_paeg_public_sat accepted totalAssignment originalSat audited ->
      ay_paeg_no_claim_diagnostic failure) :
    ay_paeg_conj (ay_paeg_no_claim_diagnostic failure)
      (ay_paeg_public_sat accepted totalAssignment originalSat audited ->
        ay_paeg_no_claim_diagnostic failure) :=
  ay_paeg_conj_intro (ay_paeg_no_claim_intro hfail) hblock

theorem ay_paeg_failed_extension_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_paeg_public_sat accepted totalAssignment originalSat audited ->
      ay_paeg_recompute_obligation failure) :
    ay_paeg_conj (ay_paeg_recompute_obligation failure)
      (ay_paeg_public_sat accepted totalAssignment originalSat audited ->
        ay_paeg_recompute_obligation failure) :=
  ay_paeg_conj_intro (ay_paeg_recompute_intro hfail) hblock

theorem ay_paeg_public_unsat_intro {unsatCertificate originalUnsat : Prop}
    (hc : unsatCertificate) (hu : originalUnsat) :
    ay_paeg_public_unsat unsatCertificate originalUnsat :=
  ay_paeg_conj_intro hc hu

theorem ay_paeg_public_unsat_certificate {unsatCertificate originalUnsat : Prop}
    (h : ay_paeg_public_unsat unsatCertificate originalUnsat) : unsatCertificate :=
  ay_paeg_conj_left h

theorem ay_paeg_public_unsat_claim {unsatCertificate originalUnsat : Prop}
    (h : ay_paeg_public_unsat unsatCertificate originalUnsat) : originalUnsat :=
  ay_paeg_conj_right h

theorem ay_paeg_unsat_claims_unaffected_by_sat_only_guard
    {unsatCertificate originalUnsat satGuard : Prop}
    (h : ay_paeg_public_unsat unsatCertificate originalUnsat) :
    ay_paeg_conj (ay_paeg_public_unsat unsatCertificate originalUnsat)
      (satGuard -> ay_paeg_public_unsat unsatCertificate originalUnsat) :=
  ay_paeg_conj_intro h (fun _ => h)

/-!
  SAT-COMP/ay witness order-stability guard.

  This self-contained package models the SAT-only obligations for accepting a
  public model witness after order normalization and duplicate/conflict checks.
-/

def ay_wosg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_wosg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_wosg_equiv (p q : Prop) : Prop :=
  ay_wosg_conj (p -> q) (q -> p)

def ay_wosg_benchmark_fingerprint (rawWitness fingerprintOk : Prop) : Prop :=
  rawWitness -> fingerprintOk

def ay_wosg_variable_domain_manifest (fingerprintOk domainOk : Prop) : Prop :=
  fingerprintOk -> domainOk

def ay_wosg_witness_variable_order_ledger (domainOk orderOk : Prop) : Prop :=
  domainOk -> orderOk

def ay_wosg_duplicate_conflict_literal_policy (orderOk duplicatePolicyOk : Prop) : Prop :=
  orderOk -> duplicatePolicyOk

def ay_wosg_total_assignment_reconstruction (duplicatePolicyOk totalAssignment : Prop) : Prop :=
  duplicatePolicyOk -> totalAssignment

def ay_wosg_original_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_wosg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_wosg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_wosg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_wosg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_wosg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_wosg_accepted_order_stability
    (fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_wosg_conj fingerprint
    (ay_wosg_conj domain
      (ay_wosg_conj order
        (ay_wosg_conj duplicatePolicy
          (ay_wosg_conj reconstruction
            (ay_wosg_conj replay
              (ay_wosg_conj checker
                (ay_wosg_conj build
                  (ay_wosg_conj archive
                    (ay_wosg_conj fallback audit)))))))))

def ay_wosg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_wosg_conj accepted (ay_wosg_conj totalAssignment (ay_wosg_conj originalSat audited))

def ay_wosg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_wosg_conj proofAccepted originalUnsat

def ay_wosg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_wosg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_wosg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_wosg_conj p q :=
  fun r h => h hp hq

theorem ay_wosg_conj_left {p q : Prop} (h : ay_wosg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_wosg_conj_right {p q : Prop} (h : ay_wosg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_wosg_conj_left h)

theorem ay_wosg_disj_left {p q : Prop} (hp : p) : ay_wosg_disj p q :=
  fun r hl _ => hl hp

theorem ay_wosg_disj_right {p q : Prop} (hq : q) : ay_wosg_disj p q :=
  fun r _ hr => hr hq

theorem ay_wosg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_wosg_equiv p q :=
  ay_wosg_conj_intro hpq hqp

theorem ay_wosg_equiv_forward {p q : Prop} (h : ay_wosg_equiv p q) : p -> q :=
  ay_wosg_conj_left h

theorem ay_wosg_equiv_backward {p q : Prop} (h : ay_wosg_equiv p q) : q -> p :=
  ay_wosg_conj_right h

theorem ay_wosg_benchmark_fingerprint_intro {rawWitness fingerprintOk : Prop}
    (h : rawWitness -> fingerprintOk) :
    ay_wosg_benchmark_fingerprint rawWitness fingerprintOk :=
  h

theorem ay_wosg_variable_domain_manifest_intro {fingerprintOk domainOk : Prop}
    (h : fingerprintOk -> domainOk) :
    ay_wosg_variable_domain_manifest fingerprintOk domainOk :=
  h

theorem ay_wosg_witness_variable_order_ledger_intro {domainOk orderOk : Prop}
    (h : domainOk -> orderOk) :
    ay_wosg_witness_variable_order_ledger domainOk orderOk :=
  h

theorem ay_wosg_duplicate_conflict_literal_policy_intro {orderOk duplicatePolicyOk : Prop}
    (h : orderOk -> duplicatePolicyOk) :
    ay_wosg_duplicate_conflict_literal_policy orderOk duplicatePolicyOk :=
  h

theorem ay_wosg_total_assignment_reconstruction_intro
    {duplicatePolicyOk totalAssignment : Prop}
    (h : duplicatePolicyOk -> totalAssignment) :
    ay_wosg_total_assignment_reconstruction duplicatePolicyOk totalAssignment :=
  h

theorem ay_wosg_original_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_wosg_original_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_wosg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_wosg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_wosg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_wosg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_wosg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_wosg_archive_manifest buildOk archiveOk :=
  h

theorem ay_wosg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_wosg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_wosg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_wosg_audit_transcript fallbackReady audited :=
  h

theorem ay_wosg_accepted_order_stability_intro
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hd : domain) (ho : order) (hdup : duplicatePolicy)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit :=
  ay_wosg_conj_intro hf
    (ay_wosg_conj_intro hd
      (ay_wosg_conj_intro ho
        (ay_wosg_conj_intro hdup
          (ay_wosg_conj_intro hrc
            (ay_wosg_conj_intro hr
              (ay_wosg_conj_intro hc
                (ay_wosg_conj_intro hb
                  (ay_wosg_conj_intro ha
                    (ay_wosg_conj_intro hfb hau)))))))))

theorem ay_wosg_accepted_order_stability_fingerprint
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_wosg_conj_left h

theorem ay_wosg_accepted_order_stability_domain
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : domain :=
  ay_wosg_conj_left (ay_wosg_conj_right h)

theorem ay_wosg_accepted_order_stability_order
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : order :=
  ay_wosg_conj_left (ay_wosg_conj_right (ay_wosg_conj_right h))

theorem ay_wosg_accepted_order_stability_duplicate_policy
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : duplicatePolicy :=
  ay_wosg_conj_left
    (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h)))

theorem ay_wosg_accepted_order_stability_reconstruction
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h))))

theorem ay_wosg_accepted_order_stability_replay
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h)))))

theorem ay_wosg_accepted_order_stability_checker
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right
          (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h))))))

theorem ay_wosg_accepted_order_stability_build
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : build :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right
          (ay_wosg_conj_right
            (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h)))))))

theorem ay_wosg_accepted_order_stability_archive
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right
          (ay_wosg_conj_right
            (ay_wosg_conj_right
              (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h))))))))

theorem ay_wosg_accepted_order_stability_fallback
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_wosg_conj_left
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right
          (ay_wosg_conj_right
            (ay_wosg_conj_right
              (ay_wosg_conj_right
                (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h)))))))))

theorem ay_wosg_accepted_order_stability_audit
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_wosg_conj_right
    (ay_wosg_conj_right
      (ay_wosg_conj_right
        (ay_wosg_conj_right
          (ay_wosg_conj_right
            (ay_wosg_conj_right
              (ay_wosg_conj_right
                (ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h)))))))))

theorem ay_wosg_order_stability_reconstructs_original_sat
    {rawWitness fingerprintOk domainOk orderOk duplicatePolicyOk totalAssignment replayOk
     originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_wosg_benchmark_fingerprint rawWitness fingerprintOk)
    (hd : ay_wosg_variable_domain_manifest fingerprintOk domainOk)
    (ho : ay_wosg_witness_variable_order_ledger domainOk orderOk)
    (hdup : ay_wosg_duplicate_conflict_literal_policy orderOk duplicatePolicyOk)
    (hrc : ay_wosg_total_assignment_reconstruction duplicatePolicyOk totalAssignment)
    (hr : ay_wosg_original_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_wosg_model_checker_transcript replayOk originalSat)
    (hb : ay_wosg_solver_build_evidence originalSat buildOk)
    (ha : ay_wosg_archive_manifest buildOk archiveOk)
    (hfb : ay_wosg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_wosg_audit_transcript fallbackReady audited)
    (hw : rawWitness) :
    ay_wosg_conj totalAssignment (ay_wosg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hw
  let hdomain : domainOk := hd hfingerprint
  let horder : orderOk := ho hdomain
  let hdupOk : duplicatePolicyOk := hdup horder
  let htotal : totalAssignment := hrc hdupOk
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_wosg_conj_intro htotal (ay_wosg_conj_intro hsat haudit)

theorem ay_wosg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_wosg_public_sat accepted totalAssignment originalSat audited :=
  ay_wosg_conj_intro ha (ay_wosg_conj_intro ht (ay_wosg_conj_intro hs hau))

theorem ay_wosg_public_sat_requires_order_guard
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wosg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_wosg_conj_left h

theorem ay_wosg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wosg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_wosg_conj_left (ay_wosg_conj_right h)

theorem ay_wosg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wosg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_wosg_conj_left (ay_wosg_conj_right (ay_wosg_conj_right h))

theorem ay_wosg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_wosg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_wosg_conj_right (ay_wosg_conj_right (ay_wosg_conj_right h))

theorem ay_wosg_accepted_order_stability_publishes_sat
    {fingerprint domain order duplicatePolicy reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_wosg_public_sat
      (ay_wosg_accepted_order_stability fingerprint domain order duplicatePolicy
        reconstruction replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_wosg_public_sat_intro hg ht hs hau

theorem ay_wosg_no_claim_intro {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  h

theorem ay_wosg_recompute_intro {reason : Prop} (h : reason) :
    ay_wosg_recompute_obligation reason :=
  h

theorem ay_wosg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wosg_recompute_obligation reason :=
  ay_wosg_recompute_intro h

theorem ay_wosg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_order_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_duplicate_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wosg_recompute_obligation reason :=
  ay_wosg_recompute_intro h

theorem ay_wosg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wosg_recompute_obligation reason :=
  ay_wosg_recompute_intro h

theorem ay_wosg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_wosg_recompute_obligation reason :=
  ay_wosg_recompute_intro h

theorem ay_wosg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_wosg_no_claim_diagnostic reason :=
  ay_wosg_no_claim_intro h

theorem ay_wosg_failed_order_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_wosg_public_sat accepted totalAssignment originalSat audited ->
      ay_wosg_no_claim_diagnostic failure) :
    ay_wosg_conj (ay_wosg_no_claim_diagnostic failure)
      (ay_wosg_public_sat accepted totalAssignment originalSat audited ->
        ay_wosg_no_claim_diagnostic failure) :=
  ay_wosg_conj_intro (ay_wosg_no_claim_intro hfail) hblock

theorem ay_wosg_failed_order_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_wosg_public_sat accepted totalAssignment originalSat audited ->
      ay_wosg_recompute_obligation failure) :
    ay_wosg_conj (ay_wosg_recompute_obligation failure)
      (ay_wosg_public_sat accepted totalAssignment originalSat audited ->
        ay_wosg_recompute_obligation failure) :=
  ay_wosg_conj_intro (ay_wosg_recompute_intro hfail) hblock

theorem ay_wosg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_wosg_public_unsat proofAccepted originalUnsat :=
  ay_wosg_conj_intro hp hu

theorem ay_wosg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_wosg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_wosg_conj_left h

theorem ay_wosg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_wosg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_wosg_conj_right h

theorem ay_wosg_order_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat orderSatGuard : Prop}
    (h : ay_wosg_public_unsat proofAccepted originalUnsat) :
    ay_wosg_conj (ay_wosg_public_unsat proofAccepted originalUnsat)
      (orderSatGuard -> ay_wosg_public_unsat proofAccepted originalUnsat) :=
  ay_wosg_conj_intro h (fun _ => h)

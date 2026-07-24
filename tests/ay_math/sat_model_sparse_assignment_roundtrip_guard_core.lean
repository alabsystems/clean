/-!
  SAT-COMP/ay sparse assignment roundtrip guard.

  This self-contained package models the SAT-only obligations for publishing a
  sparse assignment after default-fill reconstruction and checker replay.
-/

def ay_sarg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_sarg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_sarg_equiv (p q : Prop) : Prop :=
  ay_sarg_conj (p -> q) (q -> p)

def ay_sarg_benchmark_fingerprint (sparseWitness fingerprintOk : Prop) : Prop :=
  sparseWitness -> fingerprintOk

def ay_sarg_sparse_witness_digest (fingerprintOk sparseDigestOk : Prop) : Prop :=
  fingerprintOk -> sparseDigestOk

def ay_sarg_default_fill_policy (sparseDigestOk defaultFillOk : Prop) : Prop :=
  sparseDigestOk -> defaultFillOk

def ay_sarg_variable_domain_manifest (defaultFillOk domainOk : Prop) : Prop :=
  defaultFillOk -> domainOk

def ay_sarg_reconstruction_witness (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_sarg_clause_satisfaction_replay
    (totalAssignment everyOriginalClauseSatisfied : Prop) : Prop :=
  totalAssignment -> everyOriginalClauseSatisfied

def ay_sarg_checker_transcript (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_sarg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_sarg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_sarg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_sarg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_sarg_accepted_sparse_roundtrip
    (fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_sarg_conj fingerprint
    (ay_sarg_conj sparseDigest
      (ay_sarg_conj defaultFill
        (ay_sarg_conj domain
          (ay_sarg_conj reconstruction
            (ay_sarg_conj replay
              (ay_sarg_conj checker
                (ay_sarg_conj build
                  (ay_sarg_conj archive
                    (ay_sarg_conj fallback audit)))))))))

def ay_sarg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_sarg_conj accepted
    (ay_sarg_conj totalAssignment
      (ay_sarg_conj everyOriginalClauseSatisfied (ay_sarg_conj originalSat audited)))

def ay_sarg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_sarg_conj proofAccepted originalUnsat

def ay_sarg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_sarg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_sarg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_sarg_conj p q :=
  fun r h => h hp hq

theorem ay_sarg_conj_left {p q : Prop} (h : ay_sarg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_sarg_conj_right {p q : Prop} (h : ay_sarg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_sarg_conj_left h)

theorem ay_sarg_disj_left {p q : Prop} (hp : p) : ay_sarg_disj p q :=
  fun r hl _ => hl hp

theorem ay_sarg_disj_right {p q : Prop} (hq : q) : ay_sarg_disj p q :=
  fun r _ hr => hr hq

theorem ay_sarg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_sarg_equiv p q :=
  ay_sarg_conj_intro hpq hqp

theorem ay_sarg_equiv_forward {p q : Prop} (h : ay_sarg_equiv p q) : p -> q :=
  ay_sarg_conj_left h

theorem ay_sarg_equiv_backward {p q : Prop} (h : ay_sarg_equiv p q) : q -> p :=
  ay_sarg_conj_right h

theorem ay_sarg_benchmark_fingerprint_intro {sparseWitness fingerprintOk : Prop}
    (h : sparseWitness -> fingerprintOk) :
    ay_sarg_benchmark_fingerprint sparseWitness fingerprintOk :=
  h

theorem ay_sarg_sparse_witness_digest_intro {fingerprintOk sparseDigestOk : Prop}
    (h : fingerprintOk -> sparseDigestOk) :
    ay_sarg_sparse_witness_digest fingerprintOk sparseDigestOk :=
  h

theorem ay_sarg_default_fill_policy_intro {sparseDigestOk defaultFillOk : Prop}
    (h : sparseDigestOk -> defaultFillOk) :
    ay_sarg_default_fill_policy sparseDigestOk defaultFillOk :=
  h

theorem ay_sarg_variable_domain_manifest_intro {defaultFillOk domainOk : Prop}
    (h : defaultFillOk -> domainOk) :
    ay_sarg_variable_domain_manifest defaultFillOk domainOk :=
  h

theorem ay_sarg_reconstruction_witness_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_sarg_reconstruction_witness domainOk totalAssignment :=
  h

theorem ay_sarg_clause_satisfaction_replay_intro
    {totalAssignment everyOriginalClauseSatisfied : Prop}
    (h : totalAssignment -> everyOriginalClauseSatisfied) :
    ay_sarg_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied :=
  h

theorem ay_sarg_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_sarg_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_sarg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_sarg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_sarg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_sarg_archive_manifest buildOk archiveOk :=
  h

theorem ay_sarg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_sarg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_sarg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_sarg_audit_transcript fallbackReady audited :=
  h

theorem ay_sarg_accepted_sparse_roundtrip_intro
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hsd : sparseDigest) (hdf : defaultFill) (hd : domain)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hb : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit :=
  ay_sarg_conj_intro hf
    (ay_sarg_conj_intro hsd
      (ay_sarg_conj_intro hdf
        (ay_sarg_conj_intro hd
          (ay_sarg_conj_intro hrc
            (ay_sarg_conj_intro hr
              (ay_sarg_conj_intro hc
                (ay_sarg_conj_intro hb
                  (ay_sarg_conj_intro ha
                    (ay_sarg_conj_intro hfb hau)))))))))

theorem ay_sarg_accepted_sparse_roundtrip_fingerprint
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : fingerprint :=
  ay_sarg_conj_left h

theorem ay_sarg_accepted_sparse_roundtrip_sparse_digest
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : sparseDigest :=
  ay_sarg_conj_left (ay_sarg_conj_right h)

theorem ay_sarg_accepted_sparse_roundtrip_default_fill
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : defaultFill :=
  ay_sarg_conj_left (ay_sarg_conj_right (ay_sarg_conj_right h))

theorem ay_sarg_accepted_sparse_roundtrip_domain
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : domain :=
  ay_sarg_conj_left
    (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))

theorem ay_sarg_accepted_sparse_roundtrip_reconstruction
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : reconstruction :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h))))

theorem ay_sarg_accepted_sparse_roundtrip_replay
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : replay :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))))

theorem ay_sarg_accepted_sparse_roundtrip_checker
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : checker :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right
          (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h))))))

theorem ay_sarg_accepted_sparse_roundtrip_build
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : build :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right
          (ay_sarg_conj_right
            (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))))))

theorem ay_sarg_accepted_sparse_roundtrip_archive
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : archive :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right
          (ay_sarg_conj_right
            (ay_sarg_conj_right
              (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h))))))))

theorem ay_sarg_accepted_sparse_roundtrip_fallback
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : fallback :=
  ay_sarg_conj_left
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right
          (ay_sarg_conj_right
            (ay_sarg_conj_right
              (ay_sarg_conj_right
                (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))))))))

theorem ay_sarg_accepted_sparse_roundtrip_audit
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit) : audit :=
  ay_sarg_conj_right
    (ay_sarg_conj_right
      (ay_sarg_conj_right
        (ay_sarg_conj_right
          (ay_sarg_conj_right
            (ay_sarg_conj_right
              (ay_sarg_conj_right
                (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))))))))

theorem ay_sarg_sparse_roundtrip_reconstructs_original_sat
    {sparseWitness fingerprintOk sparseDigestOk defaultFillOk domainOk totalAssignment
     everyOriginalClauseSatisfied originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_sarg_benchmark_fingerprint sparseWitness fingerprintOk)
    (hsd : ay_sarg_sparse_witness_digest fingerprintOk sparseDigestOk)
    (hdf : ay_sarg_default_fill_policy sparseDigestOk defaultFillOk)
    (hd : ay_sarg_variable_domain_manifest defaultFillOk domainOk)
    (hrc : ay_sarg_reconstruction_witness domainOk totalAssignment)
    (hr : ay_sarg_clause_satisfaction_replay totalAssignment everyOriginalClauseSatisfied)
    (hc : ay_sarg_checker_transcript everyOriginalClauseSatisfied originalSat)
    (hb : ay_sarg_solver_build_evidence originalSat buildOk)
    (ha : ay_sarg_archive_manifest buildOk archiveOk)
    (hfb : ay_sarg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_sarg_audit_transcript fallbackReady audited)
    (hw : sparseWitness) :
    ay_sarg_conj totalAssignment
      (ay_sarg_conj everyOriginalClauseSatisfied (ay_sarg_conj originalSat audited)) :=
  let hfingerprint : fingerprintOk := hf hw
  let hsparse : sparseDigestOk := hsd hfingerprint
  let hdefault : defaultFillOk := hdf hsparse
  let hdomain : domainOk := hd hdefault
  let htotal : totalAssignment := hrc hdomain
  let hevery : everyOriginalClauseSatisfied := hr htotal
  let hsat : originalSat := hc hevery
  let hbuild : buildOk := hb hsat
  let harchive : archiveOk := ha hbuild
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_sarg_conj_intro htotal (ay_sarg_conj_intro hevery (ay_sarg_conj_intro hsat haudit))

theorem ay_sarg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_sarg_conj_intro ha
    (ay_sarg_conj_intro ht (ay_sarg_conj_intro hevery (ay_sarg_conj_intro hs hau)))

theorem ay_sarg_public_sat_requires_sparse_roundtrip
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : accepted :=
  ay_sarg_conj_left h

theorem ay_sarg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : totalAssignment :=
  ay_sarg_conj_left (ay_sarg_conj_right h)

theorem ay_sarg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : everyOriginalClauseSatisfied :=
  ay_sarg_conj_left (ay_sarg_conj_right (ay_sarg_conj_right h))

theorem ay_sarg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : originalSat :=
  ay_sarg_conj_left (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))

theorem ay_sarg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited) : audited :=
  ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right (ay_sarg_conj_right h)))

theorem ay_sarg_accepted_sparse_roundtrip_publishes_sat
    {fingerprint sparseDigest defaultFill domain reconstruction replay checker build archive
     fallback audit totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hg : ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
      reconstruction replay checker build archive fallback audit)
    (ht : totalAssignment) (hevery : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_sarg_public_sat
      (ay_sarg_accepted_sparse_roundtrip fingerprint sparseDigest defaultFill domain
        reconstruction replay checker build archive fallback audit)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_sarg_public_sat_intro hg ht hevery hs hau

theorem ay_sarg_no_claim_intro {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  h

theorem ay_sarg_recompute_intro {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  h

theorem ay_sarg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  ay_sarg_recompute_intro h

theorem ay_sarg_sparse_digest_mismatch_recompute {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  ay_sarg_recompute_intro h

theorem ay_sarg_default_fill_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  ay_sarg_no_claim_intro h

theorem ay_sarg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  ay_sarg_no_claim_intro h

theorem ay_sarg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  ay_sarg_recompute_intro h

theorem ay_sarg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  ay_sarg_recompute_intro h

theorem ay_sarg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  ay_sarg_no_claim_intro h

theorem ay_sarg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_sarg_recompute_obligation reason :=
  ay_sarg_recompute_intro h

theorem ay_sarg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  ay_sarg_no_claim_intro h

theorem ay_sarg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_sarg_no_claim_diagnostic reason :=
  ay_sarg_no_claim_intro h

theorem ay_sarg_failed_sparse_roundtrip_guard_cannot_create_public_sat
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_sarg_no_claim_diagnostic failure) :
    ay_sarg_conj (ay_sarg_no_claim_diagnostic failure)
      (ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_sarg_no_claim_diagnostic failure) :=
  ay_sarg_conj_intro (ay_sarg_no_claim_intro hfail) hblock

theorem ay_sarg_failed_sparse_roundtrip_guard_forces_recompute
    {failure accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited -> ay_sarg_recompute_obligation failure) :
    ay_sarg_conj (ay_sarg_recompute_obligation failure)
      (ay_sarg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
        audited -> ay_sarg_recompute_obligation failure) :=
  ay_sarg_conj_intro (ay_sarg_recompute_intro hfail) hblock

theorem ay_sarg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_sarg_public_unsat proofAccepted originalUnsat :=
  ay_sarg_conj_intro hp hu

theorem ay_sarg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_sarg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_sarg_conj_left h

theorem ay_sarg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_sarg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_sarg_conj_right h

theorem ay_sarg_sparse_roundtrip_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat sparseRoundtripSatGuard : Prop}
    (h : ay_sarg_public_unsat proofAccepted originalUnsat) :
    ay_sarg_conj (ay_sarg_public_unsat proofAccepted originalUnsat)
      (sparseRoundtripSatGuard -> ay_sarg_public_unsat proofAccepted originalUnsat) :=
  ay_sarg_conj_intro h (fun _ => h)

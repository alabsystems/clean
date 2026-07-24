/-!
  SAT-COMP/ay DIMACS model roundtrip checksum guard.

  This self-contained package models the SAT-only obligations for publishing a
  DIMACS model file after writer, byte digest, parser roundtrip, and checker
  evidence agree.
-/

def ay_drcg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_drcg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_drcg_equiv (p q : Prop) : Prop :=
  ay_drcg_conj (p -> q) (q -> p)

def ay_drcg_benchmark_fingerprint (modelArtifact fingerprintOk : Prop) : Prop :=
  modelArtifact -> fingerprintOk

def ay_drcg_dimacs_writer_manifest (fingerprintOk writerOk : Prop) : Prop :=
  fingerprintOk -> writerOk

def ay_drcg_output_byte_digest (writerOk bytesOk : Prop) : Prop :=
  writerOk -> bytesOk

def ay_drcg_parser_roundtrip_witness (bytesOk parserOk : Prop) : Prop :=
  bytesOk -> parserOk

def ay_drcg_variable_domain_manifest (parserOk domainOk : Prop) : Prop :=
  parserOk -> domainOk

def ay_drcg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_drcg_clause_satisfaction_replay (totalAssignment replayOk : Prop) : Prop :=
  totalAssignment -> replayOk

def ay_drcg_model_checker_transcript (replayOk originalSat : Prop) : Prop :=
  replayOk -> originalSat

def ay_drcg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_drcg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_drcg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_drcg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_drcg_accepted_roundtrip
    (fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop) : Prop :=
  ay_drcg_conj fingerprint
    (ay_drcg_conj writer
      (ay_drcg_conj bytes
        (ay_drcg_conj parser
          (ay_drcg_conj domain
            (ay_drcg_conj reconstruction
              (ay_drcg_conj replay
                (ay_drcg_conj checker
                  (ay_drcg_conj build
                    (ay_drcg_conj archive
                      (ay_drcg_conj fallback audit))))))))))

def ay_drcg_public_sat (accepted totalAssignment originalSat audited : Prop) : Prop :=
  ay_drcg_conj accepted (ay_drcg_conj totalAssignment (ay_drcg_conj originalSat audited))

def ay_drcg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_drcg_conj proofAccepted originalUnsat

def ay_drcg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_drcg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_drcg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_drcg_conj p q :=
  fun r h => h hp hq

theorem ay_drcg_conj_left {p q : Prop} (h : ay_drcg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_drcg_conj_right {p q : Prop} (h : ay_drcg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_drcg_conj_left h)

theorem ay_drcg_disj_left {p q : Prop} (hp : p) : ay_drcg_disj p q :=
  fun r hl _ => hl hp

theorem ay_drcg_disj_right {p q : Prop} (hq : q) : ay_drcg_disj p q :=
  fun r _ hr => hr hq

theorem ay_drcg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_drcg_equiv p q :=
  ay_drcg_conj_intro hpq hqp

theorem ay_drcg_equiv_forward {p q : Prop} (h : ay_drcg_equiv p q) : p -> q :=
  ay_drcg_conj_left h

theorem ay_drcg_equiv_backward {p q : Prop} (h : ay_drcg_equiv p q) : q -> p :=
  ay_drcg_conj_right h

theorem ay_drcg_benchmark_fingerprint_intro {modelArtifact fingerprintOk : Prop}
    (h : modelArtifact -> fingerprintOk) :
    ay_drcg_benchmark_fingerprint modelArtifact fingerprintOk :=
  h

theorem ay_drcg_dimacs_writer_manifest_intro {fingerprintOk writerOk : Prop}
    (h : fingerprintOk -> writerOk) :
    ay_drcg_dimacs_writer_manifest fingerprintOk writerOk :=
  h

theorem ay_drcg_output_byte_digest_intro {writerOk bytesOk : Prop}
    (h : writerOk -> bytesOk) :
    ay_drcg_output_byte_digest writerOk bytesOk :=
  h

theorem ay_drcg_parser_roundtrip_witness_intro {bytesOk parserOk : Prop}
    (h : bytesOk -> parserOk) :
    ay_drcg_parser_roundtrip_witness bytesOk parserOk :=
  h

theorem ay_drcg_variable_domain_manifest_intro {parserOk domainOk : Prop}
    (h : parserOk -> domainOk) :
    ay_drcg_variable_domain_manifest parserOk domainOk :=
  h

theorem ay_drcg_total_assignment_reconstruction_intro {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_drcg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_drcg_clause_satisfaction_replay_intro {totalAssignment replayOk : Prop}
    (h : totalAssignment -> replayOk) :
    ay_drcg_clause_satisfaction_replay totalAssignment replayOk :=
  h

theorem ay_drcg_model_checker_transcript_intro {replayOk originalSat : Prop}
    (h : replayOk -> originalSat) :
    ay_drcg_model_checker_transcript replayOk originalSat :=
  h

theorem ay_drcg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_drcg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_drcg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_drcg_archive_manifest buildOk archiveOk :=
  h

theorem ay_drcg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_drcg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_drcg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_drcg_audit_transcript fallbackReady audited :=
  h

theorem ay_drcg_accepted_roundtrip_intro
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (hw : writer) (hb : bytes) (hp : parser) (hd : domain)
    (hrc : reconstruction) (hr : replay) (hc : checker) (hbuild : build)
    (ha : archive) (hfb : fallback) (hau : audit) :
    ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit :=
  ay_drcg_conj_intro hf
    (ay_drcg_conj_intro hw
      (ay_drcg_conj_intro hb
        (ay_drcg_conj_intro hp
          (ay_drcg_conj_intro hd
            (ay_drcg_conj_intro hrc
              (ay_drcg_conj_intro hr
                (ay_drcg_conj_intro hc
                  (ay_drcg_conj_intro hbuild
                    (ay_drcg_conj_intro ha
                      (ay_drcg_conj_intro hfb hau))))))))))

theorem ay_drcg_accepted_roundtrip_fingerprint
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : fingerprint :=
  ay_drcg_conj_left h

theorem ay_drcg_accepted_roundtrip_writer
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : writer :=
  ay_drcg_conj_left (ay_drcg_conj_right h)

theorem ay_drcg_accepted_roundtrip_bytes
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : bytes :=
  ay_drcg_conj_left (ay_drcg_conj_right (ay_drcg_conj_right h))

theorem ay_drcg_accepted_roundtrip_parser
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : parser :=
  ay_drcg_conj_left
    (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h)))

theorem ay_drcg_accepted_roundtrip_domain
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : domain :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))))

theorem ay_drcg_accepted_roundtrip_reconstruction
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : reconstruction :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h)))))

theorem ay_drcg_accepted_roundtrip_replay
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : replay :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))))))

theorem ay_drcg_accepted_roundtrip_checker
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : checker :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right
            (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h)))))))

theorem ay_drcg_accepted_roundtrip_build
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : build :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right
            (ay_drcg_conj_right
              (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))))))))

theorem ay_drcg_accepted_roundtrip_archive
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : archive :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right
            (ay_drcg_conj_right
              (ay_drcg_conj_right
                (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h)))))))))

theorem ay_drcg_accepted_roundtrip_fallback
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : fallback :=
  ay_drcg_conj_left
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right
            (ay_drcg_conj_right
              (ay_drcg_conj_right
                (ay_drcg_conj_right
                  (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))))))))))

theorem ay_drcg_accepted_roundtrip_audit
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit : Prop}
    (h : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit) : audit :=
  ay_drcg_conj_right
    (ay_drcg_conj_right
      (ay_drcg_conj_right
        (ay_drcg_conj_right
          (ay_drcg_conj_right
            (ay_drcg_conj_right
              (ay_drcg_conj_right
                (ay_drcg_conj_right
                  (ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))))))))))

theorem ay_drcg_roundtrip_reconstructs_original_sat
    {modelArtifact fingerprintOk writerOk bytesOk parserOk domainOk totalAssignment
     replayOk originalSat buildOk archiveOk fallbackReady audited : Prop}
    (hf : ay_drcg_benchmark_fingerprint modelArtifact fingerprintOk)
    (hw : ay_drcg_dimacs_writer_manifest fingerprintOk writerOk)
    (hb : ay_drcg_output_byte_digest writerOk bytesOk)
    (hp : ay_drcg_parser_roundtrip_witness bytesOk parserOk)
    (hd : ay_drcg_variable_domain_manifest parserOk domainOk)
    (hrc : ay_drcg_total_assignment_reconstruction domainOk totalAssignment)
    (hr : ay_drcg_clause_satisfaction_replay totalAssignment replayOk)
    (hc : ay_drcg_model_checker_transcript replayOk originalSat)
    (hbuild : ay_drcg_solver_build_evidence originalSat buildOk)
    (ha : ay_drcg_archive_manifest buildOk archiveOk)
    (hfb : ay_drcg_fallback_no_claim_path archiveOk fallbackReady)
    (hau : ay_drcg_audit_transcript fallbackReady audited)
    (hm : modelArtifact) :
    ay_drcg_conj totalAssignment (ay_drcg_conj originalSat audited) :=
  let hfingerprint : fingerprintOk := hf hm
  let hwriter : writerOk := hw hfingerprint
  let hbytes : bytesOk := hb hwriter
  let hparser : parserOk := hp hbytes
  let hdomain : domainOk := hd hparser
  let htotal : totalAssignment := hrc hdomain
  let hreplay : replayOk := hr htotal
  let hsat : originalSat := hc hreplay
  let hbuildOk : buildOk := hbuild hsat
  let harchive : archiveOk := ha hbuildOk
  let hfallback : fallbackReady := hfb harchive
  let haudit : audited := hau hfallback
  ay_drcg_conj_intro htotal (ay_drcg_conj_intro hsat haudit)

theorem ay_drcg_public_sat_intro {accepted totalAssignment originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_drcg_public_sat accepted totalAssignment originalSat audited :=
  ay_drcg_conj_intro ha (ay_drcg_conj_intro ht (ay_drcg_conj_intro hs hau))

theorem ay_drcg_public_sat_requires_roundtrip
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_drcg_public_sat accepted totalAssignment originalSat audited) : accepted :=
  ay_drcg_conj_left h

theorem ay_drcg_public_sat_total_assignment
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_drcg_public_sat accepted totalAssignment originalSat audited) : totalAssignment :=
  ay_drcg_conj_left (ay_drcg_conj_right h)

theorem ay_drcg_public_sat_original_formula
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_drcg_public_sat accepted totalAssignment originalSat audited) : originalSat :=
  ay_drcg_conj_left (ay_drcg_conj_right (ay_drcg_conj_right h))

theorem ay_drcg_public_sat_audit
    {accepted totalAssignment originalSat audited : Prop}
    (h : ay_drcg_public_sat accepted totalAssignment originalSat audited) : audited :=
  ay_drcg_conj_right (ay_drcg_conj_right (ay_drcg_conj_right h))

theorem ay_drcg_accepted_roundtrip_publishes_sat
    {fingerprint writer bytes parser domain reconstruction replay checker build archive
     fallback audit totalAssignment originalSat audited : Prop}
    (hg : ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
      replay checker build archive fallback audit)
    (ht : totalAssignment) (hs : originalSat) (hau : audited) :
    ay_drcg_public_sat
      (ay_drcg_accepted_roundtrip fingerprint writer bytes parser domain reconstruction
        replay checker build archive fallback audit)
      totalAssignment originalSat audited :=
  ay_drcg_public_sat_intro hg ht hs hau

theorem ay_drcg_no_claim_intro {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  h

theorem ay_drcg_recompute_intro {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  h

theorem ay_drcg_fingerprint_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_writer_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  ay_drcg_no_claim_intro h

theorem ay_drcg_bytes_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_parser_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_domain_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  ay_drcg_no_claim_intro h

theorem ay_drcg_reconstruction_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_replay_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_checker_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  ay_drcg_no_claim_intro h

theorem ay_drcg_build_mismatch_recompute {reason : Prop} (h : reason) :
    ay_drcg_recompute_obligation reason :=
  ay_drcg_recompute_intro h

theorem ay_drcg_archive_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  ay_drcg_no_claim_intro h

theorem ay_drcg_audit_mismatch_no_claim {reason : Prop} (h : reason) :
    ay_drcg_no_claim_diagnostic reason :=
  ay_drcg_no_claim_intro h

theorem ay_drcg_failed_roundtrip_guard_cannot_create_public_sat
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_drcg_public_sat accepted totalAssignment originalSat audited ->
      ay_drcg_no_claim_diagnostic failure) :
    ay_drcg_conj (ay_drcg_no_claim_diagnostic failure)
      (ay_drcg_public_sat accepted totalAssignment originalSat audited ->
        ay_drcg_no_claim_diagnostic failure) :=
  ay_drcg_conj_intro (ay_drcg_no_claim_intro hfail) hblock

theorem ay_drcg_failed_roundtrip_guard_forces_recompute
    {failure accepted totalAssignment originalSat audited : Prop}
    (hfail : failure)
    (hblock : ay_drcg_public_sat accepted totalAssignment originalSat audited ->
      ay_drcg_recompute_obligation failure) :
    ay_drcg_conj (ay_drcg_recompute_obligation failure)
      (ay_drcg_public_sat accepted totalAssignment originalSat audited ->
        ay_drcg_recompute_obligation failure) :=
  ay_drcg_conj_intro (ay_drcg_recompute_intro hfail) hblock

theorem ay_drcg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_drcg_public_unsat proofAccepted originalUnsat :=
  ay_drcg_conj_intro hp hu

theorem ay_drcg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_drcg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_drcg_conj_left h

theorem ay_drcg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_drcg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_drcg_conj_right h

theorem ay_drcg_roundtrip_guard_cannot_strengthen_unsat_claims
    {proofAccepted originalUnsat roundtripSatGuard : Prop}
    (h : ay_drcg_public_unsat proofAccepted originalUnsat) :
    ay_drcg_conj (ay_drcg_public_unsat proofAccepted originalUnsat)
      (roundtripSatGuard -> ay_drcg_public_unsat proofAccepted originalUnsat) :=
  ay_drcg_conj_intro h (fun _ => h)

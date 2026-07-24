-- DIMACS parser-version guard for sequential-main SAT-COMP validation.
-- Self-contained propositional contract for parser behavior changes and
-- parser transcript revalidation.

def ay_dpvg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dpvg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_dpvg_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_dpvg_conj left right :=
  fun result k => k hleft hright

theorem ay_dpvg_conj_left {left right : Prop} (h : ay_dpvg_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_dpvg_conj_right {left right : Prop} (h : ay_dpvg_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_dpvg_disj_left {left right : Prop} (hleft : left) :
    ay_dpvg_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_dpvg_disj_right {left right : Prop} (hright : right) :
    ay_dpvg_disj left right :=
  fun result _ kright => kright hright

def ay_dpvg_parser_contract
    (benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (benchmarkRawDigest ->
      parserVersionDigest ->
      parserFlagManifest ->
      parsedCnfDigest ->
      clauseVariableCountWitness ->
      parserTranscriptDigest ->
      parserCompatibilityOrFreshParse ->
      solverInputDigest ->
      resultBundleDigest ->
      checkerTranscriptDigest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_dpvg_parser_contract_intro
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (hraw : benchmarkRawDigest)
    (hversion : parserVersionDigest)
    (hflags : parserFlagManifest)
    (hparsed : parsedCnfDigest)
    (hcounts : clauseVariableCountWitness)
    (hparserTranscript : parserTranscriptDigest)
    (hcompatOrFresh : parserCompatibilityOrFreshParse)
    (hinput : solverInputDigest)
    (hresult : resultBundleDigest)
    (hchecker : checkerTranscriptDigest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
      parserFlagManifest parsedCnfDigest clauseVariableCountWitness
      parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
      resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
      auditTranscript :=
  fun result k =>
    k hraw hversion hflags hparsed hcounts hparserTranscript hcompatOrFresh
      hinput hresult hchecker hfallback haudit

theorem ay_dpvg_contract_raw_digest
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    benchmarkRawDigest :=
  h benchmarkRawDigest (fun hraw _ _ _ _ _ _ _ _ _ _ _ => hraw)

theorem ay_dpvg_contract_parser_version
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    parserVersionDigest :=
  h parserVersionDigest (fun _ hversion _ _ _ _ _ _ _ _ _ _ => hversion)

theorem ay_dpvg_contract_parser_flags
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    parserFlagManifest :=
  h parserFlagManifest (fun _ _ hflags _ _ _ _ _ _ _ _ _ => hflags)

theorem ay_dpvg_contract_parsed_cnf
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    parsedCnfDigest :=
  h parsedCnfDigest (fun _ _ _ hparsed _ _ _ _ _ _ _ _ => hparsed)

theorem ay_dpvg_contract_clause_variable_count
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    clauseVariableCountWitness :=
  h clauseVariableCountWitness (fun _ _ _ _ hcounts _ _ _ _ _ _ _ => hcounts)

theorem ay_dpvg_contract_parser_transcript
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    parserTranscriptDigest :=
  h parserTranscriptDigest
    (fun _ _ _ _ _ hparserTranscript _ _ _ _ _ _ => hparserTranscript)

theorem ay_dpvg_contract_compat_or_fresh_parse
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    parserCompatibilityOrFreshParse :=
  h parserCompatibilityOrFreshParse
    (fun _ _ _ _ _ _ hcompatOrFresh _ _ _ _ _ => hcompatOrFresh)

theorem ay_dpvg_contract_solver_input
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    solverInputDigest :=
  h solverInputDigest (fun _ _ _ _ _ _ _ hinput _ _ _ _ => hinput)

theorem ay_dpvg_contract_result_bundle
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    resultBundleDigest :=
  h resultBundleDigest (fun _ _ _ _ _ _ _ _ hresult _ _ _ => hresult)

theorem ay_dpvg_contract_checker_transcript
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    checkerTranscriptDigest :=
  h checkerTranscriptDigest (fun _ _ _ _ _ _ _ _ _ hchecker _ _ => hchecker)

theorem ay_dpvg_contract_fallback_path
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    fallbackRecomputeNoClaimPath :=
  h fallbackRecomputeNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_dpvg_contract_audit
    {benchmarkRawDigest parserVersionDigest parserFlagManifest parsedCnfDigest
      clauseVariableCountWitness parserTranscriptDigest
      parserCompatibilityOrFreshParse solverInputDigest resultBundleDigest
      checkerTranscriptDigest fallbackRecomputeNoClaimPath auditTranscript :
      Prop}
    (h :
      ay_dpvg_parser_contract benchmarkRawDigest parserVersionDigest
        parserFlagManifest parsedCnfDigest clauseVariableCountWitness
        parserTranscriptDigest parserCompatibilityOrFreshParse solverInputDigest
        resultBundleDigest checkerTranscriptDigest fallbackRecomputeNoClaimPath
        auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_dpvg_parse_upgrade_evidence
    (compatibilityEvidence freshParseEvidence : Prop) : Prop :=
  ay_dpvg_disj compatibilityEvidence freshParseEvidence

theorem ay_dpvg_parse_upgrade_evidence_from_compatibility
    {compatibilityEvidence freshParseEvidence : Prop}
    (h : compatibilityEvidence) :
    ay_dpvg_parse_upgrade_evidence compatibilityEvidence freshParseEvidence :=
  ay_dpvg_disj_left h

theorem ay_dpvg_parse_upgrade_evidence_from_fresh_parse
    {compatibilityEvidence freshParseEvidence : Prop}
    (h : freshParseEvidence) :
    ay_dpvg_parse_upgrade_evidence compatibilityEvidence freshParseEvidence :=
  ay_dpvg_disj_right h

def ay_dpvg_parser_checked_result
    (parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop) :
    Prop :=
  ay_dpvg_conj parserContract
    (ay_dpvg_conj parseUpgradeEvidence
      (ay_dpvg_conj resultBundleTiedToParse
        (ay_dpvg_conj checkerBackedBundle
          (ay_dpvg_conj resultKindMatches originalBenchmarkClaim))))

def ay_dpvg_sat_publication
    (parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedModel originalBenchmarkSat : Prop) : Prop :=
  ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
    resultBundleTiedToParse checkerBackedBundle checkedModel originalBenchmarkSat

def ay_dpvg_unsat_publication
    (parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedProof originalBenchmarkUnsat : Prop) : Prop :=
  ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
    resultBundleTiedToParse checkerBackedBundle checkedProof originalBenchmarkUnsat

theorem ay_dpvg_parser_checked_result_intro
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (hcontract : parserContract)
    (hparse : parseUpgradeEvidence)
    (hbundleParse : resultBundleTiedToParse)
    (hchecker : checkerBackedBundle)
    (hkind : resultKindMatches)
    (hclaim : originalBenchmarkClaim) :
    ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
      resultBundleTiedToParse checkerBackedBundle resultKindMatches
      originalBenchmarkClaim :=
  ay_dpvg_conj_intro hcontract
    (ay_dpvg_conj_intro hparse
      (ay_dpvg_conj_intro hbundleParse
        (ay_dpvg_conj_intro hchecker (ay_dpvg_conj_intro hkind hclaim))))

theorem ay_dpvg_sat_publication_intro
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedModel originalBenchmarkSat : Prop}
    (hcontract : parserContract)
    (hparse : parseUpgradeEvidence)
    (hbundleParse : resultBundleTiedToParse)
    (hchecker : checkerBackedBundle)
    (hmodel : checkedModel)
    (hsat : originalBenchmarkSat) :
    ay_dpvg_sat_publication parserContract parseUpgradeEvidence
      resultBundleTiedToParse checkerBackedBundle checkedModel
      originalBenchmarkSat :=
  ay_dpvg_parser_checked_result_intro hcontract hparse hbundleParse hchecker
    hmodel hsat

theorem ay_dpvg_unsat_publication_intro
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedProof originalBenchmarkUnsat : Prop}
    (hcontract : parserContract)
    (hparse : parseUpgradeEvidence)
    (hbundleParse : resultBundleTiedToParse)
    (hchecker : checkerBackedBundle)
    (hproof : checkedProof)
    (hunsat : originalBenchmarkUnsat) :
    ay_dpvg_unsat_publication parserContract parseUpgradeEvidence
      resultBundleTiedToParse checkerBackedBundle checkedProof
      originalBenchmarkUnsat :=
  ay_dpvg_parser_checked_result_intro hcontract hparse hbundleParse hchecker
    hproof hunsat

theorem ay_dpvg_result_requires_parser_contract
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    parserContract :=
  ay_dpvg_conj_left h

theorem ay_dpvg_result_requires_compat_or_fresh_parse
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    parseUpgradeEvidence :=
  ay_dpvg_conj_left (ay_dpvg_conj_right h)

theorem ay_dpvg_result_bundle_tied_to_parse
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    resultBundleTiedToParse :=
  ay_dpvg_conj_left (ay_dpvg_conj_right (ay_dpvg_conj_right h))

theorem ay_dpvg_result_requires_checker_backed_bundle
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    checkerBackedBundle :=
  ay_dpvg_conj_left
    (ay_dpvg_conj_right (ay_dpvg_conj_right (ay_dpvg_conj_right h)))

theorem ay_dpvg_result_kind_matches
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    resultKindMatches :=
  ay_dpvg_conj_left
    (ay_dpvg_conj_right
      (ay_dpvg_conj_right (ay_dpvg_conj_right (ay_dpvg_conj_right h))))

theorem ay_dpvg_result_original_claim
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_dpvg_conj_right
    (ay_dpvg_conj_right
      (ay_dpvg_conj_right (ay_dpvg_conj_right (ay_dpvg_conj_right h))))

theorem ay_dpvg_accepted_parser_change_requires_compat_or_fresh_parse
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    parseUpgradeEvidence :=
  ay_dpvg_result_requires_compat_or_fresh_parse h

theorem ay_dpvg_accepted_parser_change_tied_to_result_bundle
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_dpvg_parser_checked_result parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle resultKindMatches
        originalBenchmarkClaim) :
    resultBundleTiedToParse :=
  ay_dpvg_result_bundle_tied_to_parse h

theorem ay_dpvg_accepted_sat_preserves_soundness
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedModel originalBenchmarkSat : Prop}
    (h :
      ay_dpvg_sat_publication parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle checkedModel
        originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_dpvg_result_original_claim h

theorem ay_dpvg_accepted_unsat_preserves_soundness
    {parserContract parseUpgradeEvidence resultBundleTiedToParse
      checkerBackedBundle checkedProof originalBenchmarkUnsat : Prop}
    (h :
      ay_dpvg_unsat_publication parserContract parseUpgradeEvidence
        resultBundleTiedToParse checkerBackedBundle checkedProof
        originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_dpvg_result_original_claim h

def ay_dpvg_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_dpvg_conj diagnostic (ay_dpvg_conj recompute auditTranscript)

theorem ay_dpvg_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_dpvg_no_claim diagnostic recompute auditTranscript :=
  ay_dpvg_conj_intro hdiagnostic (ay_dpvg_conj_intro hrecompute haudit)

theorem ay_dpvg_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_dpvg_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_dpvg_conj_left h

theorem ay_dpvg_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_dpvg_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_dpvg_conj_left (ay_dpvg_conj_right h)

theorem ay_dpvg_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_dpvg_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_dpvg_conj_right (ay_dpvg_conj_right h)

def ay_dpvg_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_dpvg_no_claim diagnostic recompute auditTranscript

theorem ay_dpvg_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_dpvg_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_dpvg_parser_mismatch_forces_no_claim
    {parserMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : parserMismatch -> diagnostic)
    (hrecompute : parserMismatch -> recompute)
    (haudit : parserMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim parserMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_version_mismatch_forces_no_claim
    {versionMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : versionMismatch -> diagnostic)
    (hrecompute : versionMismatch -> recompute)
    (haudit : versionMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim versionMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_flag_mismatch_forces_no_claim
    {flagMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : flagMismatch -> diagnostic)
    (hrecompute : flagMismatch -> recompute)
    (haudit : flagMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim flagMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_raw_digest_mismatch_forces_no_claim
    {rawMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : rawMismatch -> diagnostic)
    (hrecompute : rawMismatch -> recompute)
    (haudit : rawMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim rawMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_parsed_digest_mismatch_forces_no_claim
    {parsedMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : parsedMismatch -> diagnostic)
    (hrecompute : parsedMismatch -> recompute)
    (haudit : parsedMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim parsedMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_count_mismatch_forces_no_claim
    {countMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : countMismatch -> diagnostic)
    (hrecompute : countMismatch -> recompute)
    (haudit : countMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim countMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_input_mismatch_forces_no_claim
    {inputMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : inputMismatch -> diagnostic)
    (hrecompute : inputMismatch -> recompute)
    (haudit : inputMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim inputMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_result_mismatch_forces_no_claim
    {resultMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : resultMismatch -> diagnostic)
    (hrecompute : resultMismatch -> recompute)
    (haudit : resultMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim resultMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_checker_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_dpvg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : auditMismatch -> diagnostic)
    (hrecompute : auditMismatch -> recompute)
    (haudit : auditMismatch -> auditTranscript) :
    ay_dpvg_mismatch_forces_no_claim auditMismatch diagnostic recompute
      auditTranscript :=
  ay_dpvg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_dpvg_stale_parser_transcript_only
    (benchmarkRawDigest parserVersionDigest parserFlagManifest
      parserTranscriptDigest solverInputDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkRawDigest ->
      parserVersionDigest ->
      parserFlagManifest ->
      parserTranscriptDigest ->
      solverInputDigest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_dpvg_stale_parser_transcript_only_intro
    {benchmarkRawDigest parserVersionDigest parserFlagManifest
      parserTranscriptDigest solverInputDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (hraw : benchmarkRawDigest)
    (hversion : parserVersionDigest)
    (hflags : parserFlagManifest)
    (htranscript : parserTranscriptDigest)
    (hinput : solverInputDigest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_dpvg_stale_parser_transcript_only benchmarkRawDigest
      parserVersionDigest parserFlagManifest parserTranscriptDigest
      solverInputDigest fallbackRecomputeNoClaimPath auditTranscript :=
  fun result k => k hraw hversion hflags htranscript hinput hfallback haudit

def ay_dpvg_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_dpvg_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_dpvg_stale_parser_transcript_alone_cannot_publish_sat
    {benchmarkRawDigest parserVersionDigest parserFlagManifest
      parserTranscriptDigest solverInputDigest fallbackRecomputeNoClaimPath
      auditTranscript noClaim publicSat : Prop}
    (h :
      ay_dpvg_stale_parser_transcript_only benchmarkRawDigest
        parserVersionDigest parserFlagManifest parserTranscriptDigest
        solverInputDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_dpvg_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_dpvg_stale_parser_transcript_alone_cannot_publish_unsat
    {benchmarkRawDigest parserVersionDigest parserFlagManifest
      parserTranscriptDigest solverInputDigest fallbackRecomputeNoClaimPath
      auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_dpvg_stale_parser_transcript_only benchmarkRawDigest
        parserVersionDigest parserFlagManifest parserTranscriptDigest
        solverInputDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_dpvg_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_dpvg_stale_parser_transcript_only_lacks_checker_bundle
    {benchmarkRawDigest parserVersionDigest parserFlagManifest
      parserTranscriptDigest solverInputDigest fallbackRecomputeNoClaimPath
      auditTranscript checkerBackedBundle noClaim : Prop}
    (h :
      ay_dpvg_stale_parser_transcript_only benchmarkRawDigest
        parserVersionDigest parserFlagManifest parserTranscriptDigest
        solverInputDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    checkerBackedBundle -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ hfallback _ => hnoClaim hfallback)

def ay_dpvg_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_dpvg_conj mismatch
    (ay_dpvg_conj quarantine
      (ay_dpvg_conj recompute (ay_dpvg_conj noClaim auditTranscript)))

theorem ay_dpvg_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_dpvg_conj_intro hmismatch
    (ay_dpvg_conj_intro hquarantine
      (ay_dpvg_conj_intro hrecompute (ay_dpvg_conj_intro hnoclaim haudit)))

theorem ay_dpvg_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    mismatch :=
  ay_dpvg_conj_left h

theorem ay_dpvg_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_dpvg_conj_left (ay_dpvg_conj_right (ay_dpvg_conj_right h))

theorem ay_dpvg_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    noClaim :=
  ay_dpvg_conj_left
    (ay_dpvg_conj_right (ay_dpvg_conj_right (ay_dpvg_conj_right h)))

theorem ay_dpvg_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    auditTranscript :=
  ay_dpvg_conj_right
    (ay_dpvg_conj_right (ay_dpvg_conj_right (ay_dpvg_conj_right h)))

theorem ay_dpvg_failed_parser_version_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_dpvg_blocks_sat noClaim publicSat :=
  fun _ => ay_dpvg_failed_guard_no_claim h

theorem ay_dpvg_failed_parser_version_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_dpvg_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_dpvg_failed_guard_no_claim h

theorem ay_dpvg_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_dpvg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_dpvg_failed_guard_recompute h

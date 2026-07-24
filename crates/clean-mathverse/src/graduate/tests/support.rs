// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// Shared fixtures: pilot env/baseline/request, Prop-level expression builders, forgery helpers, v2 definition fixtures, topo sort.

const IMP_SELF: &str = "GradPilot.imp_self";
const IMP_TRANS: &str = "GradPilot.imp_trans";
const BAD_AXIOM: &str = "GradPilot.bad_axiom";
const BAD_DEPENDENT: &str = "GradPilot.bad_dependent";
const UNCHECKED: &str = "GradPilot.unchecked";

fn bd() -> BinderInfo {
    BinderInfo::Default
}

/// `∀ (p : Prop), p → p` (a closed constructive Prop).
fn imp_self_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `fun (p : Prop) (h : p) => h`.
fn imp_self_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(bd(), Expr::bvar(0), Expr::bvar(0)),
    )
}

/// `∀ (p q r : Prop), (p → q) → (q → r) → p → r`.
fn imp_trans_type() -> Expr {
    let f_ty = Expr::pi(bd(), Expr::bvar(2), Expr::bvar(2)); // p → q
    let g_ty = Expr::pi(bd(), Expr::bvar(2), Expr::bvar(2)); // q → r
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(
                bd(),
                Expr::prop(),
                Expr::pi(
                    bd(),
                    f_ty,
                    Expr::pi(bd(), g_ty, Expr::pi(bd(), Expr::bvar(4), Expr::bvar(3))),
                ),
            ),
        ),
    )
}

/// `fun p q r f g x => g (f x)`.
fn imp_trans_value() -> Expr {
    let f_ty = Expr::pi(bd(), Expr::bvar(2), Expr::bvar(2));
    let g_ty = Expr::pi(bd(), Expr::bvar(2), Expr::bvar(2));
    let body = Expr::app(Expr::bvar(1), Expr::app(Expr::bvar(2), Expr::bvar(0)));
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(
                bd(),
                Expr::prop(),
                Expr::lam(
                    bd(),
                    f_ty,
                    Expr::lam(bd(), g_ty, Expr::lam(bd(), Expr::bvar(4), body)),
                ),
            ),
        ),
    )
}

/// `∀ (p q : Prop), p → p` — distinct statement reserved for the domain axiom.
fn bad_axiom_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(bd(), Expr::bvar(1), Expr::bvar(2)),
        ),
    )
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// Fixture environment built exclusively through the checked kernel path.
fn pilot_env() -> Environment {
    let mut env = Environment::new();
    env.add_decl(theorem(IMP_SELF, imp_self_type(), imp_self_value()))
        .expect("imp_self must kernel-check");
    env.add_decl(theorem(IMP_TRANS, imp_trans_type(), imp_trans_value()))
        .expect("imp_trans must kernel-check");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(BAD_AXIOM),
        level_params: vec![],
        type_: bad_axiom_type(),
    })
    .expect("bad_axiom must kernel-check as an axiom");
    env.add_decl(theorem(
        BAD_DEPENDENT,
        bad_axiom_type(),
        Expr::const_str(BAD_AXIOM),
    ))
    .expect("bad_dependent must kernel-check (it cites the axiom)");
    env
}

/// Baseline corpus: a 1-decl CleanNative shard containing `imp_self`.
fn pilot_baseline(dir: &Path) -> GraduationBaseline {
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("baseline export");
    let shard = dir.join("baseline.mathverse");
    builder.write_to_file(&shard).expect("write baseline shard");
    GraduationBaseline::load(dir).expect("load baseline")
}

fn pilot_request() -> GraduationRequest {
    GraduationRequest {
        project_name: "grad-pilot".to_string(),
        manifest_kind: "clean-math-project-v1".to_string(),
        manifest_digest: "blake3:fixture-manifest".to_string(),
        certificate_schema: Some("clean-math-certificate-v1".to_string()),
        certificate_cross_checks: Vec::new(),
        mathverse_release: "fixture".to_string(),
        on_duplicate: OnDuplicate::Reject,
        attempt_id: Some("pilot-0001".to_string()),
        replay_archive_sha256: Some(
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string(),
        ),
        engine: Some("pilot-harness".to_string()),
        seed: Some("0".to_string()),
        evidence_class: EvidenceClass::HarnessTranscribed,
        residual_risk: "fixture".to_string(),
        clean_commit: Some("fixture-commit".to_string()),
        shard_filename: None,
        decided_at_epoch_s: None,
        env_provenance: None,
        score_identity: false,
        score_defeq: false,
    }
}

fn names(list: &[&str]) -> Vec<Name> {
    list.iter().map(|n| Name::from_string(n)).collect()
}

fn run_pilot(out: &Path, baseline_dir: &Path) -> GraduationRecord {
    let env = pilot_env();
    let baseline = pilot_baseline(baseline_dir);
    graduate(
        &env,
        &names(&[IMP_SELF, IMP_TRANS, BAD_DEPENDENT]),
        &pilot_request(),
        &baseline,
        out,
    )
    .expect("graduation must not hit infrastructure errors")
}

fn entry<'a>(record: &'a GraduationRecord, name: &str) -> &'a super::record::GraduatedTheorem {
    record
        .theorems
        .iter()
        .find(|t| t.name == name)
        .unwrap_or_else(|| panic!("record must contain an entry for {name}"))
}

// ---------------------------------------------------------------------------
// Forgery helpers — shared by the coordinated two-file forgery tests
// ---------------------------------------------------------------------------

/// Self-consistent forged-record skeleton (empty audit tables; each test
/// fills in theorems / carried definitions / accepted lists).
fn forged_record_skeleton(schema: &str) -> GraduationRecord {
    GraduationRecord {
        schema: schema.to_string(),
        gate: GateInfo {
            gate_version: 2,
            clean_version: "forged".to_string(),
            clean_commit: "forged".to_string(),
            decided_at_epoch_s: 0,
            recheck_base: crate::graduate::record::default_recheck_base(),
        },
        project: ProjectInfo {
            name: "forged".to_string(),
            manifest_kind: "clean-math-project-v1".to_string(),
            manifest_digest: "blake3:forged".to_string(),
            certificate_schema: None,
        },
        corpus_pin: CorpusPin {
            mathverse_release: "forged".to_string(),
            manifest_digest: "blake3:forged".to_string(),
        },
        policy: PolicyInfo {
            min_trust: GRADUATION_MIN_TRUST.to_string(),
            on_duplicate: OnDuplicate::Reject,
        },
        theorems: Vec::new(),
        carried_definitions: Vec::new(),
        carried_inductives: Vec::new(),
        carried_theorems: Vec::new(),
        provenance: RunProvenance {
            attempt_id: None,
            replay_archive_sha256: None,
            engine: None,
            seed: None,
            evidence_class: EvidenceClass::AgentAttested,
            residual_risk: "forged".to_string(),
            env_provenance: None,
        },
        result: GraduationResult {
            accepted: Vec::new(),
            rejected: Vec::new(),
            shard_filename: "forged-graduated.mathverse".to_string(),
            shard_digest: String::new(),
        },
    }
}

/// A lying audit entry: claims KernelVerified / foundational-only acceptance
/// no matter what the declaration actually is.
fn forged_accepted_entry(
    name: &str,
    type_: &Expr,
    value: &Expr,
    carried: &[&str],
) -> GraduatedTheorem {
    GraduatedTheorem {
        name: name.to_string(),
        decl_kind: "theorem".to_string(),
        statement_hash: expr_canonical_digest(type_).expect("hash type"),
        proof_hash: expr_canonical_digest(value).expect("hash value"),
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified, // the lie
            value_typechecked: true,
            family_checked: false,
            checker: "forged".to_string(),
        },
        axiom_closure: AxiomClosure {
            foundational_only: true, // the lie
            domain_axioms: Vec::new(),
            axiom_profile_bits: 0,
        },
        novelty: NoveltyFacts {
            method: "name+statement-hash".to_string(),
            verdict: NoveltyVerdict::New,
            matched_name: None,
            match_kind: None,
        },
        accepted: true,
        reject_reason: None,
        carried_definitions: carried.iter().map(|s| (*s).to_string()).collect(),
        carried_inductives: Vec::new(),
        carried_theorems: Vec::new(),
        semantic_identity: None,
    }
}

/// Re-forge both digest bindings exactly the way the intake gate computes
/// them (binding note into every constant's provenance, then the shard
/// digest back into the record) and write the forged pair to disk.
fn forge_bindings_and_write(
    builder: &mut KernelShardBuilder,
    record: &mut GraduationRecord,
    constants: &[(u32, &str)],
    shard_path: &Path,
) {
    let note = record.provenance_note().expect("binding note");
    let mut sidecar = ProvenanceSidecar::new();
    for (idx, name) in constants {
        let prov = ProvenanceBuilder::new(name).note(&note).build();
        let (prov_idx, digest) = add_provenance(&mut sidecar, prov);
        builder
            .shard_writer_mut()
            .set_constant_provenance(*idx, prov_idx, digest);
    }
    builder
        .shard_writer_mut()
        .set_provenance(sidecar.to_bytes().expect("sidecar bytes"));
    builder
        .write_to_file(shard_path)
        .expect("write forged shard");
    record.result.shard_digest =
        super::record::blake3_digest(&std::fs::read(shard_path).expect("shard bytes"));
    record
        .write_to_file(&graduation_record_path(shard_path))
        .expect("write forged record");
}

// ---------------------------------------------------------------------------
// Legacy-schema fail-closed fixtures (cake-gate committed-artifact tests)
// ---------------------------------------------------------------------------
//
// The committed v1/v2 `clean-native-nnverify-graduated.mathverse` artifacts
// were retired from the git tree by the graduation-storage refactor (shards
// are no longer tracked; see `tests/no_graduation_mathverse_tracked.rs`). The
// two properties those tests pinned are regenerated here, fully in a tempdir
// with no tracked binary:
//
//   1. SCHEMA BACK-COMPAT — a record bearing the OLD `mathverse-graduation-v1`
//      / `-v2` schema string parses under the current schema types and the
//      cake gate accepts that schema.
//   2. FAIL-CLOSED REPLAY — a shard whose stored proof value does NOT
//      re-typecheck against its declared type (the historical artifacts could
//      not replay against the casesOn-corrected prelude) yields a
//      `KernelRejected` violation through the gate — never a silent pass.
//
// The record is otherwise self-consistent (the digest bindings are forged
// exactly as the intake computes them), so `verify_cake_shard` RUNS (returns
// `Ok`) and reports the single, intentional replay violation.

const LEGACY_THM: &str = "GradPilot.legacy_thm";

/// A proof value that cannot inhabit any of the Prop-level statements below:
/// `Prop : Sort 1`, so storing it as the value of a theorem of type
/// `imp_self_type()` / `uses_pid_type()` makes the kernel reject the replay.
fn nonreplaying_value() -> Expr {
    Expr::prop()
}

/// Build a genuine Cake shard + a self-consistent record bearing the given
/// LEGACY schema string, whose single accepted theorem fails the cake gate's
/// kernel replay (its stored value does not typecheck). When `with_definition`
/// is set, a real (value-correct) carried `PId` definition precedes the
/// theorem in the shard and is recorded in `carried_definitions` — the v2
/// shape — so only the theorem's replay fails. Returns the shard path; the
/// record sits beside it at `graduation_record_path`.
fn write_legacy_nonreplaying_graduation(
    dir: &Path,
    schema: &str,
    with_definition: bool,
) -> PathBuf {
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let mut constants: Vec<(u32, &str)> = Vec::new();
    let mut carried_definitions: Vec<CarriedDefinition> = Vec::new();

    if with_definition {
        let def_idx = builder
            .add_declaration(&definition(PID_DEF, pid_type(), pid_value()), &[])
            .expect("carried definition export");
        builder
            .shard_writer_mut()
            .set_constant_axiom_profile(def_idx, crate::types::AxiomProfile::NONE);
        constants.push((def_idx, PID_DEF));
        carried_definitions.push(CarriedDefinition {
            name: PID_DEF.to_string(),
            decl_kind: "definition".to_string(),
            statement_hash: expr_canonical_digest(&pid_type()).expect("hash PId type"),
            value_hash: expr_canonical_digest(&pid_value()).expect("hash PId value"),
            is_reducible: true,
            kernel: KernelFacts {
                verdict: KernelVerdict::KernelVerified,
                value_typechecked: true,
                family_checked: false,
                checker: "fixture".to_string(),
            },
            axiom_closure: AxiomClosure {
                foundational_only: true,
                domain_axioms: Vec::new(),
                axiom_profile_bits: 0,
            },
            required_by: vec![LEGACY_THM.to_string()],
        });
    }

    // The accepted theorem: a real Prop statement whose STORED value
    // (`Prop : Sort 1`) cannot inhabit it — replay must fail closed.
    let thm_type = imp_self_type();
    let thm_idx = builder
        .add_declaration(
            &theorem(LEGACY_THM, thm_type.clone(), nonreplaying_value()),
            &[],
        )
        .expect("theorem export (value deliberately mistyped)");
    builder
        .shard_writer_mut()
        .set_constant_axiom_profile(thm_idx, crate::types::AxiomProfile::NONE);
    constants.push((thm_idx, LEGACY_THM));
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(schema);
    record.gate.gate_version = if with_definition { 2 } else { 1 };
    record.carried_definitions = carried_definitions;
    record.theorems = vec![forged_accepted_entry(
        LEGACY_THM,
        &thm_type,
        &nonreplaying_value(),
        if with_definition { &[PID_DEF] } else { &[] },
    )];
    record.result.accepted = vec![LEGACY_THM.to_string()];

    let shard_path = dir.join("legacy-graduated.mathverse");
    forge_bindings_and_write(&mut builder, &mut record, &constants, &shard_path);
    shard_path
}

const PID_DEF: &str = "GradPilot.PId";
const USES_PID: &str = "GradPilot.uses_pid";

/// `PId : Prop → Prop`.
fn pid_type() -> Expr {
    Expr::pi(bd(), Expr::prop(), Expr::prop())
}

/// `fun (p : Prop) => p`.
fn pid_value() -> Expr {
    Expr::lam(bd(), Expr::prop(), Expr::bvar(0))
}

/// `∀ (p : Prop), PId p → p` — proving it forces the kernel to unfold the
/// carried definition (`PId p` ≡ `p` only by delta+beta).
fn uses_pid_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::app(Expr::const_str(PID_DEF), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    )
}

/// `fun (p : Prop) (h : PId p) => h`.
fn uses_pid_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::app(Expr::const_str(PID_DEF), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    )
}

fn definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    }
}

const PCOMP_DEF: &str = "GradPilot.PComp";
const USES_PCOMP: &str = "GradPilot.uses_pcomp";

/// `fun (p : Prop) => PId (PId p)` — a definition that depends on another
/// carried definition, forming a two-link chain.
fn pcomp_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::app(
            Expr::const_str(PID_DEF),
            Expr::app(Expr::const_str(PID_DEF), Expr::bvar(0)),
        ),
    )
}

/// `∀ (p : Prop), PComp p → p` — proving it forces delta through BOTH links.
fn uses_pcomp_type() -> Expr {
    Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::app(Expr::const_str(PCOMP_DEF), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    )
}

/// `fun (p : Prop) (h : PComp p) => h`.
fn uses_pcomp_value() -> Expr {
    Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::app(Expr::const_str(PCOMP_DEF), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    )
}

/// Topologically sort candidate theorems by their candidate-set reference
/// edges — the same derivation GRADUATION #1 used for its 277-name list,
/// extended (v3) to follow references THROUGH non-candidate constants: a
/// candidate that cites a co-candidate only inside a carried definition's
/// VALUE (e.g. `Rat.add_comm` → `Rat.add` → `Rat.Int.mulMulMulComm`) still
/// depends on it for gate resolution, so the eval order must respect it.
fn topo_sort_candidates(env: &Environment, mut names: Vec<Name>) -> Vec<Name> {
    names.sort_by_key(Name::to_string);
    let in_set: std::collections::HashSet<String> = names.iter().map(Name::to_string).collect();
    let refs_of = |name: &str| -> Vec<String> {
        let Some(info) = env.get_const(&Name::from_string(name)) else {
            return Vec::new();
        };
        let mut refs = super::intake::collect_constant_refs(&info.type_);
        if let Some(value) = &info.value {
            refs.extend(super::intake::collect_constant_refs(value));
        }
        let mut refs: Vec<String> = refs.into_iter().collect();
        refs.sort();
        refs
    };
    // Candidate-set dependency edges of one candidate, expanding through
    // every non-candidate constant transitively.
    let effective_edges = |name: &str| -> Vec<String> {
        let mut edges: Vec<String> = Vec::new();
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut queue: Vec<String> = refs_of(name);
        while let Some(dep) = queue.pop() {
            if !seen.insert(dep.clone()) {
                continue;
            }
            if in_set.contains(&dep) {
                if dep != name {
                    edges.push(dep);
                }
                continue;
            }
            queue.extend(refs_of(&dep));
        }
        edges.sort();
        edges.dedup();
        edges
    };
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut out: Vec<Name> = Vec::new();
    // Iterative DFS post-order (dependencies first).
    for root in &names {
        let mut stack: Vec<(Name, bool)> = vec![(root.clone(), false)];
        while let Some((name, expanded)) = stack.pop() {
            let key = name.to_string();
            if expanded {
                out.push(name);
                continue;
            }
            if !visited.insert(key.clone()) {
                continue;
            }
            stack.push((name.clone(), true));
            let refs: Vec<String> = effective_edges(&key)
                .into_iter()
                .filter(|r| !visited.contains(r))
                .collect();
            for r in refs {
                stack.push((Name::from_string(&r), false));
            }
        }
    }
    out
}

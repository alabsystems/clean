// Copyright 2026 Andrew Yates. Apache-2.0.
//! Original-source model proof qualification through the unchanged reference entry.
//! The manifest declares inputs and control goals, never proof authority.

use std::collections::{BTreeSet, HashSet};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{KernelEnvError, KernelTypeError, ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::semr_bool_body::{
    BoolBodyRefusal, BoolModuleSubject, BoolPacket, BoolSubject, UnboundBoolMathematicsContext,
};
use clean_olean::{load_module_with_deps, reference_base_closed};
use serde::Deserialize;

#[path = "../tests/support/installed_lean.rs"]
#[allow(dead_code)]
mod installed_lean;

const PINNED: &str = "leanprover/lean4:v4.30.0-rc2";
const AX0: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Source {
    module: String,
    path: PathBuf,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    proof: String,
    goal: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Subject {
    sources: Vec<Source>,
    module: String,
    roots: Vec<String>,
    positive: Vec<Case>,
    negative: Vec<Case>,
    #[serde(default)]
    bool_subject: Option<BoolRequest>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BoolRequest {
    bytes: PathBuf,
    function: u32,
    #[serde(default)]
    proof: Option<String>,
}

fn require(yes: bool, message: impl Into<String>) -> Result<()> {
    if yes {
        Ok(())
    } else {
        Err(message.into().into())
    }
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

// The same dependency walk as the maintained rm1_trust_sem regression.
fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        let walk = |e: &Expr, set: &mut HashSet<Name>| {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, set);
        };
        if let Some(c) = env.get_const(&name) {
            walk(&c.type_, &mut used);
            if let Some(value) = &c.value {
                walk(value, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&name) {
            walk(&i.type_, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&name) {
            walk(&c.type_, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&name) {
            walk(&r.type_, &mut used);
            used.insert(r.inductive_name.clone());
        }
        stack.extend(used.into_iter().filter(|u| !seen.contains(u)));
    }
    seen
}

fn module_path(module: &str) -> Result<PathBuf> {
    require(
        !module.is_empty()
            && module.split('.').all(|part| {
                !part.is_empty() && part.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            }),
        "invalid module name",
    )?;
    Ok(PathBuf::from(module.replace('.', "/")).with_extension("lean"))
}

fn audit_cones(
    env: &Environment,
    targets: &BTreeSet<Name>,
    admitted: Option<&BTreeSet<Name>>,
) -> Result<()> {
    for root in targets {
        for dependency in reach(env, root) {
            let name = dependency.to_string();
            require(
                ![
                    "sorryAx",
                    "Lean.ofReduceBool",
                    "Lean.ofReduceNat",
                    "Lean.trustCompiler",
                ]
                .contains(&name.as_str()),
                format!("{root} reaches escape {name}"),
            )?;
            if let Some(c) = env.get_const(&dependency) {
                require(
                    c.kind != ConstantKind::Axiom
                        || AX0.contains(&name.as_str())
                        || QUOT_FORMERS.contains(&name.as_str()),
                    format!("{root} reaches non-Ax0 axiom {name}"),
                )?;
                require(
                    c.kind != ConstantKind::Opaque
                        || (c.value.is_some()
                            && admitted.is_none_or(|names| names.contains(&dependency))),
                    format!("{root} reaches opaque computation {name} whose body is missing or was not replayed"),
                )?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::ConstantInfo;

    fn imported_metadata(kind: ConstantKind, body: bool) -> (Environment, BTreeSet<Name>) {
        let name = n("Counterfeit.imported");
        // Deliberately untrusted input metadata, never a kernel admission.
        let mut info = ConstantInfo::new(
            name.clone(),
            vec![],
            Expr::prop(),
            body.then(Expr::prop),
            false,
        );
        info.kind = kind;
        let mut env = Environment::for_lean_replay();
        env.add_constant_unchecked_for_test(info);
        (env, [name].into_iter().collect())
    }

    #[test]
    fn imported_axiom_with_value_is_still_refused() {
        let (env, roots) = imported_metadata(ConstantKind::Axiom, true);
        let error = audit_cones(&env, &roots, None).expect_err("a metadata value is not authority");
        assert!(error.to_string().contains("non-Ax0 axiom"));
    }

    #[test]
    fn bodyless_opaque_is_refused() {
        let (env, roots) = imported_metadata(ConstantKind::Opaque, false);
        let error =
            audit_cones(&env, &roots, None).expect_err("an opaque declaration needs a real body");
        assert!(error.to_string().contains("opaque computation"));
    }

    #[test]
    fn native_audit_cannot_authorize_an_ill_typed_definition() {
        let (env, roots) = imported_metadata(ConstantKind::Definition, true);
        audit_cones(&env, &roots, None).expect("the native walk is only an assumption audit");
        // An Err here is the entry refusing its own EMPTY starting base, never
        // this definition: a cone member's refusal lands in the report.
        let built = reference_base_closed(&env, &roots, &ClosedRecheckOptions::default())
            .expect("the empty reference entry must start before it can judge the subject");
        assert!(!built.report.passed(), "the original kernel must refuse");
    }

    #[test]
    fn opaque_metadata_body_does_not_replace_full_replay() {
        let (env, roots) = imported_metadata(ConstantKind::Opaque, true);
        audit_cones(&env, &roots, None).expect("the original entry must check this body");
        assert!(audit_cones(&env, &roots, Some(&BTreeSet::new())).is_err());
        // As above: an Err is the empty entry's own start-up refusal, not a verdict.
        let built = reference_base_closed(&env, &roots, &ClosedRecheckOptions::default())
            .expect("the empty reference entry must start before it can judge the subject");
        assert!(!built.report.passed(), "the original kernel must refuse");
    }
}

fn main() -> Result<()> {
    replay(None)
}

/// Qualification hook for the actual original untrusted Rust proof proposer.
/// The callback supplies only a term; it cannot supply the expected goal,
/// model environment, completion seal, evidence grade or acceptance decision.
pub fn replay_with_proposer(proposer: fn(&[u8], u32) -> Expr) -> Result<()> {
    replay(Some(proposer))
}

fn replay(proposer: Option<fn(&[u8], u32) -> Expr>) -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    require(
        args.len() == 1,
        "usage: model_reference_subject <subject.json>",
    )?;
    let request = Path::new(&args[0]).canonicalize()?;
    let bytes = std::fs::read(&request)?;
    let subject: Subject = serde_json::from_slice(&bytes)?;
    require(
        !subject.sources.is_empty()
            && !subject.roots.is_empty()
            && !subject.positive.is_empty()
            && !subject.negative.is_empty(),
        "sources, theorem roots, positive and negative cases must all be nonempty",
    )?;
    let lean = installed_lean::installed_lean(PINNED).ok_or("pinned Lean is unavailable")?;
    let bool_input = subject
        .bool_subject
        .as_ref()
        .map(|input| -> Result<_> {
            let path = if input.bytes.is_absolute() {
                input.bytes.clone()
            } else {
                request
                    .parent()
                    .ok_or("manifest has no parent")?
                    .join(&input.bytes)
            }
            .canonicalize()?;
            let bytes = std::fs::read(&path)?;
            require(!bytes.is_empty(), "typed Boolean subject bytes are empty")?;
            println!("SUBJECT_BYTES {} {}", path.display(), blake3::hash(&bytes));
            Ok((path, bytes))
        })
        .transpose()?;
    let replayer = std::env::current_exe()?.canonicalize()?;
    println!(
        "REPLAYER {} {}",
        replayer.display(),
        blake3::hash(&std::fs::read(&replayer)?)
    );
    println!(
        "ELABORATOR {} {}",
        lean.bin.display(),
        blake3::hash(&std::fs::read(&lean.bin)?)
    );
    let dir = tempfile::tempdir()?;
    let mut modules = BTreeSet::new();
    let mut paths = BTreeSet::new();
    let mut snapshots = Vec::new();
    for source in &subject.sources {
        require(
            modules.insert(source.module.clone()),
            "duplicate source module",
        )?;
        let original = if source.path.is_absolute() {
            source.path.clone()
        } else {
            request
                .parent()
                .ok_or("manifest has no parent")?
                .join(&source.path)
        }
        .canonicalize()?;
        require(
            paths.insert(original.clone()),
            "duplicate original source path",
        )?;
        let content = std::fs::read(&original)?;
        let relative = module_path(&source.module)?;
        let destination = dir.path().join(relative);
        std::fs::create_dir_all(destination.parent().ok_or("module has no parent")?)?;
        std::fs::write(&destination, &content)?;
        println!(
            "SOURCE {} {} {}",
            source.module,
            original.display(),
            blake3::hash(&content)
        );
        snapshots.push((original, content, destination));
    }
    require(
        modules.contains(&subject.module),
        "root module has no original source",
    )?;
    for (source, (_, _, path)) in subject.sources.iter().zip(&snapshots) {
        let output = Command::new(&lean.bin)
            .current_dir(dir.path())
            .env("LEAN_PATH", dir.path())
            .args(["--root", ".", "-o"])
            .arg(path.with_extension("olean"))
            .arg(path)
            .output()?;
        require(
            output.status.success(),
            format!(
                "compile {} failed: {}\n{}",
                source.module,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        )?;
    }
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(
        &mut env,
        &subject.module,
        &[dir.path().to_path_buf(), lean.lib.clone()],
    )?;
    let mut targets = BTreeSet::new();
    for root in &subject.roots {
        require(targets.insert(n(root)), "duplicate theorem root")?;
    }
    for case in subject.positive.iter().chain(&subject.negative) {
        targets.insert(n(&case.proof));
        targets.insert(n(&case.goal));
    }
    if let Some(input) = &subject.bool_subject {
        if let Some(proof) = &input.proof {
            targets.insert(n(proof));
        }
    }
    // Check original imported kinds as well as the independently reconstructed
    // environment. A metadata value must not disguise an authored axiom.
    audit_cones(&env, &targets, None)?;
    let built = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())?;
    require(
        built.report.passed() && built.entry_refusals.is_empty(),
        format!(
            "{}; refusals {:?}",
            built.report.verdict_sentence(),
            built.entry_refusals
        ),
    )?;
    require(
        targets.iter().all(|root| built.admitted.contains(root)),
        "a required root was not admitted",
    )?;
    let admitted_names = built.admitted.clone();
    let admitted = admitted_names.len();
    let mut kernel = built
        .into_kernel()
        .map_err(|report| report.verdict_sentence())?;
    require(
        kernel.theory_id() == TheoryId::LeanReferenceV1,
        "wrong reference theory",
    )?;
    // Opacity is valid mathematics when a real body passed the unchanged FULL
    // entry. It never supplies Rust/runtime implementation correspondence.
    audit_cones(kernel.environment(), &targets, Some(&admitted_names))?;
    for (index, (case, positive)) in subject
        .positive
        .iter()
        .map(|c| (c, true))
        .chain(subject.negative.iter().map(|c| (c, false)))
        .enumerate()
    {
        let proof = env
            .get_const(&n(&case.proof))
            .ok_or("proof constant missing")?;
        require(
            proof.level_params.is_empty(),
            "control proof has uninstantiated universes",
        )?;
        let value = proof.value.clone().ok_or("control proof has no body")?;
        let control = n(&format!("ModelReferenceControl.case_{index}"));
        require(
            kernel.environment().get_const(&control).is_none()
                && kernel.environment().get_inductive(&control).is_none()
                && kernel.environment().get_constructor(&control).is_none()
                && kernel.environment().get_recursor(&control).is_none(),
            "control name already exists in the subject",
        )?;
        let result = kernel.add_checked(Declaration::Theorem {
            name: control,
            level_params: vec![],
            type_: Expr::const_(n(&case.goal), vec![]),
            value,
        });
        if positive {
            result.map_err(|e| format!("original goal {} refused: {e:?}", case.goal))?;
        } else {
            require(
                matches!(
                    result,
                    Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                        source: KernelTypeError::TypeMismatch { .. },
                        ..
                    }))
                ),
                format!(
                    "false goal {} was not semantically refused: {result:?}",
                    case.goal
                ),
            )?;
        }
        println!(
            "CONTROL {} {} {}",
            if positive {
                "accepted"
            } else {
                "kernel-type-mismatch"
            },
            case.proof,
            case.goal
        );
    }
    if let (Some(input), Some((path, original))) = (&subject.bool_subject, &bool_input) {
        // A second original closed replay supplies the typed reader's PRIVATE
        // completion seal; controls above consumed the first into their kernel.
        let base = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())?;
        let context = UnboundBoolMathematicsContext::from_reference_base(base)?;
        context.check_model_source(&env)?;
        // This second association uses the already genuinely checked private
        // fixed source cache, not another replay per function.
        context.check_model_source(&env)?;
        let expected = BoolSubject {
            module: std::sync::Arc::new(BoolModuleSubject::new(std::sync::Arc::from(
                original.clone(),
            ))?),
            function: input.function,
        };
        let packet = BoolPacket {
            context: context.digest(),
            subject: expected.clone(),
            returned: match proposer {
                Some(propose) => propose(original, input.function),
                None => Expr::const_(
                    n(input
                        .proof
                        .as_deref()
                        .ok_or("typed subject needs a proof term producer")?),
                    vec![],
                ),
            },
        };
        let checked = context.check(&expected, &packet)?;
        require(
            checked.subject().module.bytes() == original.as_slice(),
            "checked bytes changed",
        )?;
        let mut wrong_context = packet.clone();
        wrong_context.context.0[0] ^= 1;
        require(
            matches!(
                context.check(&expected, &wrong_context),
                Err(BoolBodyRefusal::SubjectMismatch)
            ),
            "wrong context did not refuse specifically",
        )?;
        let mut wrong_function = expected.clone();
        wrong_function.function ^= 1;
        let mut wrong_packet = packet.clone();
        wrong_packet.subject = wrong_function.clone();
        require(
            matches!(
                context.check(&expected, &wrong_packet),
                Err(BoolBodyRefusal::SubjectMismatch)
            ),
            "wrong function packet did not refuse specifically",
        )?;
        require(
            bool_type_mismatch(context.check(&wrong_function, &wrong_packet)),
            "wrong native function goal did not reach actual kernel type mismatch",
        )?;
        let mut changed = original.clone();
        changed[0] ^= 1;
        let wrong_bytes = BoolSubject {
            module: std::sync::Arc::new(BoolModuleSubject::new(std::sync::Arc::from(changed))?),
            function: input.function,
        };
        wrong_packet.subject = wrong_bytes.clone();
        require(
            matches!(
                context.check(&expected, &wrong_packet),
                Err(BoolBodyRefusal::SubjectMismatch)
            ),
            "wrong byte packet did not refuse specifically",
        )?;
        require(
            bool_type_mismatch(context.check(&wrong_bytes, &wrong_packet)),
            "wrong native byte goal did not reach actual kernel type mismatch",
        )?;
        if proposer.is_some() {
            // Mutate the REAL original proposal's Boolean reflexivity premise
            // to a well-formed Nat equality. Parsing succeeds; the original
            // kernel must specifically refuse the carrier at application.
            let mut args: Vec<Expr> = packet
                .returned
                .get_app_args()
                .iter()
                .map(|e| (*e).clone())
                .collect();
            require(
                args.len() == 4,
                "original native proposal has unexpected control shape",
            )?;
            args[2] = Expr::apps(
                Expr::const_(
                    n("Eq.refl"),
                    vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                ),
                [Expr::const_(n("Nat"), vec![]), Expr::nat_lit(0)],
            );
            wrong_packet = packet.clone();
            wrong_packet.returned = Expr::apps(packet.returned.get_app_fn().clone(), args);
            require(
                bool_type_mismatch(context.check(&expected, &wrong_packet)),
                "wrong actual native premise carrier did not reach kernel type mismatch",
            )?;
            println!("TYPED_NATIVE_PROPOSER wrong_carrier=kernel-type-mismatch");
        }
        require(
            std::fs::read(path)? == *original,
            "actual Boolean subject changed during replay",
        )?;
        println!("TYPED_UNBOUND_BOOL positive=1 wrong_context=1 wrong_function_packet=1 wrong_function_goal=kernel-type-mismatch wrong_byte_packet=1 wrong_byte_goal=kernel-type-mismatch");
    }
    for (path, original, _) in snapshots {
        require(
            std::fs::read(&path)? == original,
            format!("original source changed: {}", path.display()),
        )?;
    }
    require(
        std::fs::read(&request)? == bytes,
        "subject manifest changed during replay",
    )?;
    println!(
        "MODEL_REFERENCE_REPLAY roots={} admitted={} positive={} negative={} manifest={}",
        subject.roots.len(),
        admitted,
        subject.positive.len(),
        subject.negative.len(),
        blake3::hash(&bytes)
    );
    Ok(())
}

fn bool_type_mismatch<T>(result: std::result::Result<T, BoolBodyRefusal>) -> bool {
    matches!(
        result,
        Err(BoolBodyRefusal::Proof(ReferenceRefusal::Kernel(
            KernelEnvError::TypeCheckFailed {
                source: KernelTypeError::TypeMismatch { .. },
                ..
            }
        )))
    )
}

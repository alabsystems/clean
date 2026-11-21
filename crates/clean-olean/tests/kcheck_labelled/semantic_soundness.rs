// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Partial C3 branches: origin-module census, independent fresh replay, exact
//! statement pins and an actual checked-proof/False pair for every own theorem.
//! Smaller-fuel hypotheses on induction steps remain explicit obligations.
//!
//! Each own declaration `d` has two pins in
//! `theories/kcheck_soundness/statement_pins.json`: `d`, its meaning digest
//! (`support/meaning_digest.rs`) over the package of the fixture family
//! `kcheck_soundness` (`cic_l`, `cic_l_model`, `kcheck_spec`,
//! `kcheck_labelled`, `kcheck_soundness`), which moves when anything its
//! statement or body reaches changes, the adopted checker included; and
//! `d::declaration`, the digest of its whole kernel record, proof included,
//! which these pins held before (so changing a theorem into a definition, or
//! a proof, still moves a pin). Re-pin with the command of `kcheck_labelled.rs`.
use super::*;
use clean_kernel::env::ConstantKind;

// Compile-time includes also expose every new theory input to the runner's
// existing @reach/include read-set discovery for this integration target.
const SOURCE_INPUTS: &[&str] = &[
    include_str!("../../../../theories/kcheck_soundness/ORDER"),
    include_str!("../../../../theories/kcheck_soundness/lakefile.toml"),
    include_str!("../../../../theories/kcheck_soundness/lean-toolchain"),
    include_str!("../../../../theories/kcheck_soundness/README.md"),
    include_str!("../../../../theories/kcheck_soundness/lake-manifest.json"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Scope.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Sort.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Constant.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Application.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Reduction.lean"),
    include_str!("../../../../theories/kcheck_soundness/KCheckSoundness/Spine.lean"),
];

// Freeze the complete declaration, including universes, kind and reducibility,
// so changing a theorem into a definition cannot silently drop a False pair.
fn pin_constant(declaration: &ConstantInfo) -> String {
    let bytes = bincode::serde::encode_to_vec(declaration, bincode::config::standard())
        .expect("serialize complete proof declaration");
    hex(&Sha256::digest(&bytes))
}

#[test]
fn partial_c3_branches_recheck_and_refuse_false() {
    assert!(SOURCE_INPUTS.iter().all(|source| !source.is_empty()));
    let stems: Vec<&str> = SOURCE_INPUTS[0]
        .lines()
        .filter(|line| !line.is_empty())
        .collect();
    assert_eq!(stems.len(), 7, "six proof modules plus their import root");
    assert_eq!(
        SOURCE_INPUTS.len(),
        stems.len() + 5,
        "every module joins the test read set"
    );
    let lib = require_pinned_lean_lib_path().expect("repository-pinned Lean");
    let compiled = compiled_fixture_dir("kcheck_soundness");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let binary_path = std::env::join_paths(paths).expect("binary path");
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", "KCheckSoundness"])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env("PATH", binary_path)
        .output()
        .expect("independent fresh Lean kernel replay");
    assert!(
        independent.status.success(),
        "Lean replay: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    load_module_with_deps(&mut loaded, "KCheckSoundness", &[compiled.clone(), lib])
        .expect("load source-built semantic proof package");
    let mut targets = BTreeSet::new();
    for stem in stems {
        let module = stem.replace('/', ".");
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .expect("own module name table");
        if stem == "KCheckSoundness" {
            assert!(
                artifact.names.is_empty(),
                "the root only imports proof modules"
            );
        } else {
            assert!(!artifact.names.is_empty(), "{module} declares no subjects");
        }
        for subject in artifact.names {
            assert!(
                loaded.get_const(&subject).is_some(),
                "missing own declaration {subject}"
            );
            assert!(
                !loaded.is_unsafe(&subject) && !loaded.is_partial(&subject),
                "unsafe/partial {subject}"
            );
            assert!(targets.insert(subject), "declaration counted twice");
        }
    }
    assert!(!targets.is_empty());
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("dependency-closed reference replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked
        .into_kernel()
        .expect("complete checked reference closure");
    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let package = Package::of_fixture(
        &compiled,
        "kcheck_soundness",
        &[
            "cic_l",
            "cic_l_model",
            "kcheck_spec",
            "kcheck_labelled",
            "kcheck_soundness",
        ],
    );
    let mut pins = BTreeMap::new();
    {
        let digests = MeaningDigests::new(kernel.environment(), &package);
        for subject in &targets {
            let declaration = loaded.get_const(subject).expect("own declaration");
            let meaning = digests
                .digest(subject)
                .unwrap_or_else(|error| panic!("{subject}: {error}"));
            assert!(pins.insert(subject.to_string(), meaning).is_none());
            assert!(pins
                .insert(format!("{subject}::declaration"), pin_constant(declaration))
                .is_none());
        }
        let roots: Vec<Name> = targets.iter().cloned().collect();
        eprintln!(
            "{}",
            digests
                .describe(&package, &roots)
                .unwrap_or_else(|error| panic!("{error}"))
        );
    }
    assert_eq!(
        pins.len(),
        2 * targets.len(),
        "two pins per own declaration"
    );
    let mut proofs = 0;
    for subject in &targets {
        let declaration = loaded.get_const(subject).expect("own declaration");
        let mut closure = kernel
            .environment()
            .axiom_deps(subject)
            .expect("axiom closure");
        closure.extend(
            kernel
                .environment()
                .foundational_axiom_deps(subject)
                .expect("foundations"),
        );
        let observed: BTreeSet<String> = closure.iter().map(ToString::to_string).collect();
        assert!(
            observed.is_subset(&allowed),
            "nonfoundational closure for {subject}: {observed:?}"
        );
        if declaration.kind != ConstantKind::Theorem {
            continue;
        }
        let value = declaration.value.clone().expect("real theorem proof body");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Soundness.Controls.positive_{proofs}")),
                level_params: declaration.level_params.clone(),
                type_: declaration.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|error| panic!("positive proof {subject}: {error:?}"));
        let forged = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Soundness.Controls.false_{proofs}")),
            level_params: declaration.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&forged),
            "{subject} at False must be refused: {forged:?}"
        );
        proofs += 1;
    }
    assert!(
        proofs >= 20,
        "the full current proof census must be exercised"
    );
    eprintln!(
        "C3_STATEMENT_PINS={}",
        serde_json::to_string(&pins).expect("pins JSON")
    );
    eprintln!(
        "partial C3: {} subjects, {proofs} positive/False pairs; both fresh kernels passed",
        targets.len()
    );
    let expected: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../../theories/kcheck_soundness/statement_pins.json"
    ))
    .expect("committed pins");
    if let Err(failure) = meaning_digest::check_pins(
        &pins,
        &expected,
        "theories/kcheck_soundness/statement_pins.json",
    ) {
        panic!("statement/body inventory changed; review actual proofs before minting: {failure}");
    }
}

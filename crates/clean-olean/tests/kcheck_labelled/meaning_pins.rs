// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The adopted checker's pins as meaning digests (plan unit E2's follow-up
//! part 2; `docs/DECISIONS.md`, "Pins bind meaning, part 2: the adopted
//! checker and the later packages"), the prefix rule they replace, and their
//! mutation controls.
//!
//! Every pin is the meaning digest (`support/meaning_digest.rs`) of a package
//! constant: a forged or contract statement's proposition definition, a
//! theorem (its statement only), or a checker, beta or per-token definition.
//! The definitions used to be pinned with every auxiliary constant declared
//! under their name (`<definition>.*`, the prefix rule), which missed what
//! they reach under another name: a helper such as `KCheck.splitFramesAux`
//! beside `KCheck.splitFrames`, a case such as `case_refl` that
//! `perTokenCases` lists, the inductive types and constructors the checker
//! matches on. A meaning digest reaches all of them. [`subsume_prefix_rule`]
//! shows that it also covers what the prefix rule covered: each auxiliary
//! under a pinned definition's name is in that definition's closure, or is
//! pinned under its own name (an equation lemma, a smart-unfolding copy or a
//! `match` splitter the definition never uses), so no constant the old pins
//! bound is left unpinned.
//!
//! [`mutation_controls`] then changes the package three ways and requires
//! exactly the pins whose closure reaches a changed constant (a theorem
//! changed only in its proof is not one) to move, among them the ones each
//! change must move, while the digests the pins used before ([`old_digest`])
//! do not see it:
//!
//! * (a) the body of `case_refl` swapped for the body of another accepted
//!   per-token case with a different verdict (a constant-level edit: the
//!   Lean source cannot express it, since `refl_accepted` states the verdict
//!   and would no longer compile): `perTokenCases` and `per_token_accepted`
//!   must move;
//! * (b) `KCheck.splitFramesAux`, reached from `KCheck.checker` and under no
//!   checker definition's name, refusing a frame that ends exactly at the end
//!   of the advice (`≤` to `<` in `KCheck/Token.lean`, compiled by the pinned
//!   Lean): `KCheck.checker` must move;
//! * (c) the constructor `KCheck.Token.stop` given a field (`stop (pad : Unit
//!   := ())` in `KCheck/Token.lean`, compiled by the pinned Lean): the checker
//!   pin must move.
//!
//! (b) and (c) load the package again with the mutated `KCheck.Token`
//! compiled into a scratch directory searched first; the other modules are
//! the fixture's own `.olean` files. All three compare with the environment
//! the loader built from the fixture.

use super::*;

use std::path::{Path, PathBuf};

use clean_kernel::ConstantKind;

/// What a pin hashed before the meaning digest, so the controls can show
/// what that missed.
pub(super) enum Old {
    /// A proposition definition's value, the stated proposition alone.
    Statement,
    /// A theorem's type alone.
    Theorem,
    /// A definition's type and value with those of each auxiliary declared
    /// under its name (`checker_digest`).
    Definition(Vec<Name>),
    /// A pin with no predecessor: an auxiliary pinned in its own right.
    New,
}

/// One pin: its key in `statement_pins.json`, the constant whose meaning
/// digest it holds, and what it hashed before.
pub(super) struct Pin {
    pub(super) key: String,
    pub(super) root: Name,
    pub(super) old: Old,
}

impl Pin {
    /// A forged or contract statement, keyed by its short name.
    pub(super) fn statement(key: &str, root: Name) -> Self {
        Self {
            key: key.to_owned(),
            root,
            old: Old::Statement,
        }
    }

    /// A theorem, keyed by its full name.
    pub(super) fn theorem(theorem: &str) -> Self {
        Self {
            key: theorem.to_owned(),
            root: name(theorem),
            old: Old::Theorem,
        }
    }

    /// An own theorem of the module-origin index, keyed by its unambiguous
    /// name and pinned by its statement before.
    pub(super) fn owned_theorem(subject: &Name) -> Self {
        Self {
            key: subject.to_unambiguous_string(),
            root: subject.clone(),
            old: Old::Theorem,
        }
    }

    /// An own definition of the module-origin index, keyed by its unambiguous
    /// name and pinned by its own type and value before.
    pub(super) fn owned_definition(subject: &Name) -> Self {
        Self {
            key: subject.to_unambiguous_string(),
            root: subject.clone(),
            old: Old::Definition(Vec::new()),
        }
    }

    /// A definition with the auxiliaries the prefix rule bound to it.
    pub(super) fn definition(definition: &str, auxiliaries: Vec<Name>) -> Self {
        Self {
            key: definition.to_owned(),
            root: name(definition),
            old: Old::Definition(auxiliaries),
        }
    }
}

fn statement_digest(statement: &Expr) -> String {
    let bytes = bincode::serde::encode_to_vec(statement, bincode::config::standard())
        .expect("serialize a statement");
    hex(&Sha256::digest(&bytes))
}

/// A constant's type and value, in that order, each length-prefixed.
fn feed_constant(hasher: &mut Sha256, constant: &ConstantInfo) {
    for part in std::iter::once(&constant.type_).chain(constant.value.as_ref()) {
        let bytes = bincode::serde::encode_to_vec(part, bincode::config::standard())
            .expect("serialize a checker part");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
}

/// The digest the checker, beta and per-token definitions were pinned by
/// until this change: type and value, then the name, type and value of each
/// auxiliary declared under the definition's name, in name order.
fn checker_digest(constant: &ConstantInfo, auxiliaries: &[(String, &ConstantInfo)]) -> String {
    let mut hasher = Sha256::new();
    feed_constant(&mut hasher, constant);
    for (auxiliary, info) in auxiliaries {
        hasher.update((auxiliary.len() as u64).to_le_bytes());
        hasher.update(auxiliary.as_bytes());
        feed_constant(&mut hasher, info);
    }
    hex(&hasher.finalize())
}

/// What `pin` hashed before the meaning digest, over `env`; `None` for a pin
/// that had no predecessor.
pub(super) fn old_digest(env: &Environment, pin: &Pin) -> Option<String> {
    let constant = |subject: &Name| {
        env.get_const(subject)
            .unwrap_or_else(|| panic!("{subject} is resident"))
    };
    match &pin.old {
        Old::Statement => Some(statement_digest(
            constant(&pin.root)
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{} is a proposition definition", pin.key)),
        )),
        Old::Theorem => Some(statement_digest(&constant(&pin.root).type_)),
        Old::Definition(auxiliaries) => {
            let auxiliaries: Vec<(String, &ConstantInfo)> = auxiliaries
                .iter()
                .map(|auxiliary| (auxiliary.to_string(), constant(auxiliary)))
                .collect();
            Some(checker_digest(constant(&pin.root), &auxiliaries))
        }
        Old::New => None,
    }
}

/// Every pin's meaning digest, keyed by the pin's key.
pub(super) fn measure(digests: &MeaningDigests<'_>, pins: &[Pin]) -> BTreeMap<String, String> {
    let mut measured = BTreeMap::new();
    for pin in pins {
        let digest = digests
            .digest(&pin.root)
            .unwrap_or_else(|error| panic!("{}: {error}", pin.key));
        assert!(
            measured.insert(pin.key.clone(), digest).is_none(),
            "{} is listed twice",
            pin.key
        );
    }
    measured
}

/// The prefix rule, subsumed: each auxiliary declared under a pinned
/// definition's name is in the definition's closure, so its meaning is in the
/// definition's digest, or it is appended to `pins` under its own name. The
/// body of each structurally recursive definition (`<definition>._f`) must be
/// in the closure, and the five members of the mutual block must have one.
/// Returns how many auxiliaries were pinned in their own right.
pub(super) fn subsume_prefix_rule(digests: &MeaningDigests<'_>, pins: &mut Vec<Pin>) -> usize {
    let mut keys: BTreeSet<String> = pins.iter().map(|pin| pin.key.clone()).collect();
    let mut own: Vec<Pin> = Vec::new();
    let (mut total, mut reached) = (0_usize, 0_usize);
    let mut bodies: BTreeSet<String> = BTreeSet::new();
    for pin in pins.iter() {
        let Old::Definition(auxiliaries) = &pin.old else {
            continue;
        };
        let closure = digests
            .closure(&pin.root)
            .unwrap_or_else(|error| panic!("{}: {error}", pin.key));
        let mut outside: Vec<String> = Vec::new();
        for auxiliary in auxiliaries {
            total += 1;
            let text = auxiliary.to_unambiguous_string();
            if closure.contains(auxiliary) {
                reached += 1;
                if text == format!("{}._f", pin.key) {
                    bodies.insert(pin.key.clone());
                }
                continue;
            }
            assert!(
                !text.ends_with("._f"),
                "{text}, the body of {}, is not in its closure",
                pin.key
            );
            if keys.insert(text.clone()) {
                own.push(Pin {
                    key: text.clone(),
                    root: auxiliary.clone(),
                    old: Old::New,
                });
            }
            outside.push(text);
        }
        eprintln!(
            "prefix-rule {}: {} auxiliaries, {} in its closure, pinned in their own right [{}]",
            pin.key,
            auxiliaries.len(),
            auxiliaries.len() - outside.len(),
            outside.join(", ")
        );
    }
    for member in [
        "KCheck.whnf",
        "KCheck.conv",
        "KCheck.inferAnn",
        "KCheck.check",
        "KCheck.walk",
    ] {
        assert!(
            bodies.contains(member),
            "the body of {member} ({member}._f) is not in its closure"
        );
    }
    let added = own.len();
    eprintln!(
        "prefix rule subsumed: {total} auxiliaries under pinned definitions' names, {reached} in \
         the definition's closure, {} pinned in their own right ({added} new keys)",
        total - reached
    );
    pins.extend(own);
    added
}

/// The verdict `KCheck.CheckerCases.<case>_accepted` states for the case.
fn stated_verdict(env: &Environment, case: &str) -> Expr {
    let theorem = name(&format!("KCheck.CheckerCases.{case}_accepted"));
    let statement = &env
        .get_const(&theorem)
        .unwrap_or_else(|| panic!("{theorem} is resident"))
        .type_;
    let args = statement.get_app_args();
    assert_eq!(args.len(), 3, "{theorem} states an equation");
    (*args[2]).clone()
}

/// The package constants whose kernel records differ between `base` and
/// `other` in what a meaning digest reads: a theorem by its statement (a
/// changed proof is no change of meaning), anything else by its whole record.
fn changed(base: &Environment, other: &Environment, package: &Package) -> BTreeSet<Name> {
    let constant_changed =
        |subject: &Name| match (base.get_const(subject), other.get_const(subject)) {
            (Some(before), Some(after))
                if before.kind == ConstantKind::Theorem && after.kind == ConstantKind::Theorem =>
            {
                before.type_ != after.type_ || before.level_params != after.level_params
            }
            (before, after) => before != after,
        };
    package
        .names()
        .iter()
        .filter(|subject| {
            constant_changed(subject)
                || base.get_inductive(subject) != other.get_inductive(subject)
                || base.get_constructor(subject) != other.get_constructor(subject)
                || base.get_recursor(subject) != other.get_recursor(subject)
        })
        .cloned()
        .collect()
}

/// The package loaded again with `KCheck/Token.lean` changed from `from` to
/// `to` and compiled by the pinned Lean into a scratch directory searched
/// before the fixture's.
fn load_with_token(label: &str, from: &str, to: &str, paths: &Paths<'_>) -> Environment {
    let source = include_str!("../../../../theories/kcheck_labelled/KCheck/Token.lean");
    assert_eq!(
        source.matches(from).count(),
        1,
        "mutation {label}: `{from}` occurs once in KCheck/Token.lean"
    );
    let root =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("kcheck_labelled_token_{label}"));
    if root.exists() {
        std::fs::remove_dir_all(&root).expect("clear the scratch directory");
    }
    std::fs::create_dir_all(root.join("KCheck")).expect("create the scratch directory");
    std::fs::write(root.join("KCheck/Token.lean"), source.replacen(from, to, 1))
        .expect("write the mutated source");
    let output = Command::new(paths.lean)
        .args([
            "--root",
            ".",
            "-o",
            "KCheck/Token.olean",
            "KCheck/Token.lean",
        ])
        .current_dir(&root)
        .env("LEAN_PATH", &root)
        .output()
        .expect("run the pinned Lean");
    assert!(
        output.status.success(),
        "mutation {label}: the pinned Lean refused the mutated KCheck/Token.lean: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(
        &mut env,
        ROOT,
        &[root, paths.compiled.to_path_buf(), paths.lib.to_path_buf()],
    )
    .unwrap_or_else(|error| panic!("mutation {label}: load: {error}"));
    env
}

/// Where the controls find the fixture, the Lean library and the pinned Lean.
pub(super) struct Paths<'a> {
    pub(super) compiled: &'a Path,
    pub(super) lib: &'a PathBuf,
    pub(super) lean: &'a Path,
}

/// The baseline every mutation is compared with.
struct Baseline<'a> {
    env: &'a Environment,
    package: &'a Package,
    pins: &'a [Pin],
    digests: BTreeMap<String, String>,
    closures: Vec<BTreeSet<Name>>,
}

impl Baseline<'_> {
    /// Requires the pins `env` moves to be exactly those whose baseline
    /// closure reaches a changed constant, `required` among them, and the old
    /// digests of `required` not to move. Returns the changed constants.
    fn compare(&self, label: &str, env: &Environment, required: &[&str]) -> BTreeSet<Name> {
        let changed = changed(self.env, env, self.package);
        assert!(!changed.is_empty(), "mutation {label} changed nothing");
        let after = measure(&MeaningDigests::new(env, self.package), self.pins);
        let moved: BTreeSet<&str> = self
            .pins
            .iter()
            .filter(|pin| self.digests[&pin.key] != after[&pin.key])
            .map(|pin| pin.key.as_str())
            .collect();
        let expected: BTreeSet<&str> = self
            .pins
            .iter()
            .zip(&self.closures)
            .filter(|(_, closure)| closure.iter().any(|reached| changed.contains(reached)))
            .map(|(pin, _)| pin.key.as_str())
            .collect();
        assert_eq!(
            moved, expected,
            "mutation {label}: the pins that moved are not those whose closure reaches a changed \
             constant ({changed:?})"
        );
        let mut old_moved = 0_usize;
        for pin in self.pins {
            let before = old_digest(self.env, pin);
            let now = old_digest(env, pin);
            if before.is_some() && before != now {
                old_moved += 1;
            }
            if required.contains(&pin.key.as_str()) {
                assert!(
                    moved.contains(pin.key.as_str()),
                    "mutation {label}: the pin of {} did not move",
                    pin.key
                );
                assert!(
                    before.is_some() && before == now,
                    "mutation {label}: the old digest of {} saw the change; the control shows \
                     nothing the old pins missed",
                    pin.key
                );
            }
        }
        eprintln!(
            "mutation {label}: {} package constants changed [{}]; {} of {} pins moved, exactly \
             those whose closure reaches one, including {required:?}; the old digests of those \
             did not move ({old_moved} old digests moved in all)",
            changed.len(),
            changed
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            moved.len(),
            self.pins.len()
        );
        changed
    }
}

/// The three mutation controls, over the environment the loader built from
/// the fixture (`loaded`).
pub(super) fn mutation_controls(
    loaded: &Environment,
    package: &Package,
    pins: &[Pin],
    paths: &Paths<'_>,
) {
    let digests = MeaningDigests::new(loaded, package);
    let closures: Vec<BTreeSet<Name>> = pins
        .iter()
        .map(|pin| {
            digests
                .closure(&pin.root)
                .unwrap_or_else(|error| panic!("{}: {error}", pin.key))
        })
        .collect();
    let baseline = Baseline {
        env: loaded,
        package,
        pins,
        digests: measure(&digests, pins),
        closures,
    };
    drop(digests);
    let reaches = |key: &str, subject: &str| {
        let position = pins
            .iter()
            .position(|pin| pin.key == key)
            .unwrap_or_else(|| panic!("{key} is pinned"));
        assert!(
            baseline.closures[position].contains(&name(subject)),
            "{subject} is not in the closure of {key}"
        );
    };
    let per_token_cases = "KCheck.CheckerCases.perTokenCases";
    reaches(per_token_cases, "KCheck.CheckerCases.case_refl");
    reaches(PER_TOKEN_THEOREM, "KCheck.CheckerCases.case_refl");
    reaches("KCheck.checker", "KCheck.splitFramesAux");
    reaches("KCheck.checker", "KCheck.Token.stop");

    // (a) `case_refl`'s body swapped for another accepted case's.
    let refl_verdict = stated_verdict(loaded, "refl");
    let donor = PER_TOKEN_CASES
        .iter()
        .skip(1)
        .find(|case| stated_verdict(loaded, case) != refl_verdict)
        .expect("an accepted per-token case with another verdict");
    let refl = name("KCheck.CheckerCases.case_refl");
    let mut swapped = loaded
        .get_const(&refl)
        .cloned()
        .expect("case_refl is resident");
    let donor_constant = loaded
        .get_const(&name(&format!("KCheck.CheckerCases.case_{donor}")))
        .expect("the donor case is resident");
    assert_eq!(swapped.type_, donor_constant.type_, "both are a DeclRun");
    assert_ne!(swapped.value, donor_constant.value, "the bodies differ");
    swapped.value = donor_constant.value.clone();
    let mut env = loaded.clone();
    env.add_constant_unchecked_for_test(swapped);
    let changed = baseline.compare(
        &format!("(a) case_refl := case_{donor}"),
        &env,
        &[per_token_cases, PER_TOKEN_THEOREM],
    );
    assert_eq!(
        changed,
        BTreeSet::from([refl]),
        "(a) changed case_refl only"
    );
    drop(env);

    // (b) and (c): `KCheck/Token.lean` changed and compiled by the pinned Lean.
    let token_names: BTreeSet<Name> = read_artifact(
        "KCheck.Token",
        &paths.compiled.join("KCheck/Token.olean"),
        ArtifactDepth::Names,
    )
    .expect("read KCheck.Token's names")
    .names
    .into_iter()
    .collect();
    let checker_prefixes: Vec<String> = CHECKER.iter().map(|d| format!("{d}.")).collect();

    let env = load_with_token(
        "b",
        "        if start + length ≤ bytes.size then\n",
        "        if start + length < bytes.size then\n",
        paths,
    );
    let changed = baseline.compare(
        "(b) splitFramesAux refuses a frame ending at the end",
        &env,
        &["KCheck.checker"],
    );
    assert!(
        changed.is_subset(&token_names),
        "(b) changed only KCheck.Token's constants"
    );
    assert!(
        changed
            .iter()
            .any(|subject| subject.to_string().starts_with("KCheck.splitFramesAux")),
        "(b) changed splitFramesAux"
    );
    for subject in &changed {
        let text = subject.to_string();
        assert!(
            !CHECKER.contains(&text.as_str())
                && !checker_prefixes
                    .iter()
                    .any(|prefix| text.starts_with(prefix)),
            "(b) changed {text}, which a checker definition's prefix rule covered"
        );
    }
    drop(env);

    let stop = name("KCheck.Token.stop");
    let env = load_with_token("c", "  | stop\n", "  | stop (pad : Unit := ())\n", paths);
    let fields = |env: &Environment| {
        env.get_constructor(&stop)
            .expect("KCheck.Token.stop is a constructor")
            .num_fields
    };
    assert_eq!(
        (fields(loaded), fields(&env)),
        (0, 1),
        "(c) KCheck.Token.stop gained a field"
    );
    let changed = baseline.compare(
        "(c) KCheck.Token.stop gains a field",
        &env,
        &["KCheck.checker"],
    );
    assert!(
        changed.contains(&stop) && changed.is_subset(&token_names),
        "(c) changed KCheck.Token.stop and only KCheck.Token's constants"
    );
}

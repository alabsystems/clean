// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module trust (report `reports/2026-09-24-module-trust.md`): a separately
//! built module's artifact is re-checked by the kernel before anything cites
//! it, not believed.
//!
//! Every attack here starts from a GENUINE artifact written by `clean lake
//! build` and rewrites it the way an attacker with write access to
//! `.lake/build` can: swap a declaration's stated type, flip its proof term,
//! replace its proof by `sorry`, turn it into an axiom, drop the module its
//! proof depends on, or swap its family's recursor rules. Each is shown to be
//! caught twice:
//!
//! * by [`ImportedConeGate::check`] directly over the loaded artifact, and
//! * by `clean lake build` of a dependent module, the path that would otherwise
//!   credit it (it exported such modules before the gate existed).
//!
//! Every attack test first asserts that the SAME citation passes against the
//! genuine artifact, so a refusal cannot come from a fixture that never
//! worked.

use clean_elab::ElabResult;
use clean_kernel::{ConstantKind, Environment, Expr, Name};
use clean_lake::{BuildContext, BuildResult, Workspace};
use clean_olean::payload::{decode_clean_payload, encode_clean_payload, CleanPayload};
use clean_olean::{ClosedRecheckRefusal, ImportedConeGate, ImportedConeVerdict, OleanExporter};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

const LIB: &str = "theorem K1Lib.zero_add' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun k => 0 + k = k) rfl (fun k ih => congrArg Nat.succ ih) n
";

const USE_TRUE: &str = "import K1Lib

theorem K1Use.ok (m : Nat) : 0 + (0 + m) = m :=
  Eq.trans (K1Lib.zero_add' (0 + m)) (K1Lib.zero_add' m)
";

const USE_FALSE: &str = "import K1Lib

theorem K1Use.bad : (0 : Nat) = 1 := K1Lib.zero_add' 0
";

fn write_project(dir: &Path, roots: &[&str], files: &[(&str, &str)]) {
    fs::create_dir_all(dir).expect("project dir");
    let roots = roots
        .iter()
        .map(|r| format!("\"{r}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(
        dir.join("lakefile.toml"),
        format!(
            "name = \"k1\"\ndefaultTargets = [\"K1\"]\n\n[[lean_lib]]\nname = \"K1\"\nroots = [{roots}]\n"
        ),
    )
    .expect("lakefile");
    for (module, source) in files {
        fs::write(dir.join(format!("{module}.lean")), source).expect("source");
    }
}

fn build(dir: &Path) -> BuildResult {
    let ws = Workspace::load(dir).expect("workspace");
    BuildContext::new(ws).build_all().expect("build runs")
}

fn lib_dir(dir: &Path) -> PathBuf {
    dir.join(".lake/build/lib")
}

fn olean(dir: &Path, module: &str) -> PathBuf {
    lib_dir(dir).join(format!("{module}.olean"))
}

/// Build a one-module library `K1Lib` from `source` and return its directory.
fn built_lib(root: &Path, tag: &str, source: &str) -> PathBuf {
    let dir = root.join(tag);
    write_project(&dir, &["K1Lib"], &[("K1Lib", source)]);
    let result = build(&dir);
    assert!(
        result.failed.is_empty() && result.built == vec!["K1Lib".to_string()],
        "{tag}: fixture library must build: {result:?}"
    );
    dir
}

fn read_payload(path: &Path) -> (Vec<u8>, CleanPayload) {
    let bytes = fs::read(path).expect("read artifact");
    let payload = decode_clean_payload(&bytes)
        .expect("decode")
        .expect("clean lake build writes a payload");
    (bytes, payload)
}

/// Replace the payload trailer of `bytes` and write the result to `out`,
/// dropping the `.olean.server` / `.olean.private` companions (their regions
/// are laid out after the original file's length).
fn write_payload(bytes: &[u8], payload: &CleanPayload, out: &Path) {
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut rewritten = bytes[..bytes.len() - trailer].to_vec();
    rewritten.extend(encode_clean_payload(payload).expect("encode"));
    fs::write(out, rewritten).expect("write tampered artifact");
    let _ = fs::remove_file(out.with_extension("olean.server"));
    let _ = fs::remove_file(out.with_extension("olean.private"));
}

fn tamper(dir: &Path, module: &str, edit: impl FnOnce(&mut CleanPayload)) {
    let path = olean(dir, module);
    let (bytes, mut payload) = read_payload(&path);
    edit(&mut payload);
    write_payload(&bytes, &payload, &path);
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn zero_add() -> Name {
    name("K1Lib.zero_add'")
}

/// The Lean world `clean lake build` selects for a module of a project under
/// the system temporary directory, where every project here is written: no
/// `lean-toolchain` above it, so the checkout's pin.
fn builder_world() -> clean_olean::SourceWorldDecision {
    clean_olean::source_world_for_file(&std::env::temp_dir().join("Builder.lean"), None)
        .expect("the builder's Lean world")
}

/// The environment `clean lake build` starts a module without `prelude` from
/// (genuine Init of its Lean world, as Lean's implicit `import Init`), and
/// the citation base it re-admits the module's cited closure over: the
/// world's reference-admitted foundations, never a post-Init snapshot.
fn builder_base() -> (Environment, ImportedConeGate) {
    static BASE: std::sync::OnceLock<(Environment, ImportedConeGate)> = std::sync::OnceLock::new();
    BASE.get_or_init(|| {
        use clean_elab::module_driver::{
            foundation_import_base, EnvironmentSetup, SourceModuleSetup,
        };
        let decision = builder_world();
        let mut setup = SourceModuleSetup::new(EnvironmentSetup::default(), &decision)
            .expect("the builder's backbone");
        let env = setup
            .initial_environment(&clean_parser::FileHeader::default())
            .expect("genuine Init");
        let gate = foundation_import_base(&decision).expect("the builder's citation base");
        (env, gate)
    })
    .clone()
}

/// Where `dir`'s artifacts' imports resolve: its build directory, then the
/// builder's world library, which holds the `Init` every artifact records.
fn load_paths(dir: &Path) -> Vec<PathBuf> {
    let mut paths = vec![lib_dir(dir)];
    paths.extend(clean_olean::search_paths_in_world(
        builder_world().imports().expect("an admitted world"),
    ));
    paths
}

/// The environment `clean lake build` builds before any import, the gate over
/// it, and then `module` loaded from `dir`'s build directory.
fn load(dir: &Path, module: &str) -> (Environment, ImportedConeGate) {
    let (mut env, gate) = builder_base();
    clean_olean::load_module_with_deps(&mut env, module, &load_paths(dir)).expect("load artifact");
    (env, gate)
}

fn gate(dir: &Path, module: &str, root: &Name) -> ImportedConeVerdict {
    let (env, mut gate) = load(dir, module);
    gate.check(&env, &BTreeSet::from([root.clone()]))
}

/// A proof term elaborated from source against the builder's base (used to
/// obtain a genuine `sorry` term, which the fixed builder refuses to export).
fn elaborated_proof(source: &str) -> Expr {
    let env = builder_base().0;
    let surface = clean_parser::parse_file(source).expect("parse");
    for decl in &surface {
        let result = clean_elab::ElabCtx::new(&env)
            .elab_decl(decl)
            .expect("elaborate");
        if let ElabResult::Theorem { proof, .. } = result {
            return proof;
        }
    }
    panic!("no theorem in {source}");
}

fn constant_mut<'a>(payload: &'a mut CleanPayload, n: &Name) -> &'a mut clean_kernel::ConstantInfo {
    payload
        .constants
        .iter_mut()
        .find(|c| &c.name == n)
        .expect("payload constant")
}

fn assert_refused(verdict: &ImportedConeVerdict, what: &str) {
    assert!(
        !verdict.passed(false),
        "{what}: the gate must refuse, got {verdict:#?}"
    );
}

/// Project with K1Lib (genuine) and a dependent K1Use; build it, tamper K1Lib's
/// artifact with `edit`, point K1Use at `use_source`, rebuild. Returns the
/// rebuild's result.
fn rebuild_dependent_after_tamper(
    root: &Path,
    tag: &str,
    use_source: &str,
    edit: impl FnOnce(&mut CleanPayload),
) -> BuildResult {
    let dir = root.join(tag);
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[("K1Lib", LIB), ("K1Use", USE_TRUE)],
    );
    let first = build(&dir);
    assert!(
        first.failed.is_empty(),
        "{tag}: genuine project must build: {first:?}"
    );
    tamper(&dir, "K1Lib", edit);
    restamp_trace(&dir, "K1Lib");
    fs::write(dir.join("K1Use.lean"), use_source).expect("rewrite dependent");
    build(&dir)
}

/// Re-derive `module`'s build trace over its (tampered) artifact, so the build
/// REUSES the tampered artifact instead of rebuilding it from source.
///
/// Without this a tampered artifact no longer reaches a dependent's build at
/// all: its bytes differ from what the trace records, so it is rebuilt first
/// (`tests/build_trace.rs`). A trace is a cache key, not a certificate, so the
/// attacker who rewrites both is the one the dependent's closure gate must
/// still stop, and these rows pin that it does.
fn restamp_trace(dir: &Path, module: &str) {
    let artifact = olean(dir, module);
    let trace = clean_lake::build_trace::trace_path(&artifact);
    let mut recorded: serde_json::Value =
        serde_json::from_slice(&fs::read(&trace).expect("trace")).expect("trace json");
    recorded["outputs"] = clean_lake::build_trace::digest_artifact_parts(&[
        artifact.clone(),
        artifact.with_extension("olean.server"),
        artifact.with_extension("olean.private"),
    ])
    .expect("digest")
    .into();
    fs::write(&trace, serde_json::to_vec(&recorded).expect("json")).expect("write trace");
}

// ── controls ────────────────────────────────────────────────────────────────

#[test]
fn the_genuine_artifact_re_admits_over_the_builders_base() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let verdict = gate(&dir, "K1Lib", &zero_add());
    assert!(verdict.passed(false), "{verdict:#?}");
    assert!(
        verdict
            .untrusted_in_cone
            .contains(&"K1Lib.zero_add'".to_string()),
        "the imported lemma is outside the base, so it must have been replayed: {verdict:#?}"
    );
    assert!(verdict.constants_admitted >= 1, "{verdict:#?}");
}

#[test]
fn a_genuine_dependent_builds_and_a_genuine_inductive_library_re_admits() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("proj");
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[("K1Lib", LIB), ("K1Use", USE_TRUE)],
    );
    let result = build(&dir);
    assert!(
        result.failed.is_empty() && result.built.len() == 2,
        "{result:?}"
    );

    let ind = built_lib(
        tmp.path(),
        "ind",
        "inductive K1Lib.Two where\n  | a : K1Lib.Two\n  | b : K1Lib.Two\n",
    );
    let verdict = gate(&ind, "K1Lib", &name("K1Lib.Two.rec"));
    assert!(verdict.passed(false), "{verdict:#?}");
    assert_eq!(verdict.families_replayed, 1, "{verdict:#?}");
}

#[test]
fn a_family_one_check_admitted_is_given_to_the_next() {
    // The replay holds the KERNEL's regenerated recursor, compared with the
    // imported one at admission. A second citation in the same run must not
    // re-compare bytes and report the family as a conflict (it did, measured
    // on Lean's `Std.Symm`, before admitted names were remembered).
    let tmp = tempfile::tempdir().expect("tmp");
    let ind = built_lib(
        tmp.path(),
        "ind",
        "inductive K1Lib.Two where\n  | a : K1Lib.Two\n  | b : K1Lib.Two\n",
    );
    // Re-spell the stored ι-rule as a beta-redex: definitionally equal to
    // what the kernel regenerates (so admission accepts it), never
    // syntactically equal (so only remembering the admission gives it later).
    tamper(&ind, "K1Lib", |p| {
        let r = p
            .recursors
            .iter_mut()
            .find(|r| r.name == name("K1Lib.Two.rec"))
            .expect("recursor");
        let nat = Expr::const_(name("Nat"), vec![]);
        let rhs = r.rules[0].rhs.clone();
        r.rules[0].rhs = Expr::app(
            Expr::lam(clean_kernel::BinderInfo::Default, nat, rhs),
            Expr::nat_lit(0),
        );
    });
    let (env, mut gate) = load(&ind, "K1Lib");
    let rec = BTreeSet::from([name("K1Lib.Two.rec")]);
    let first = gate.check(&env, &rec);
    assert!(
        first.passed(false) && first.families_replayed == 1,
        "{first:#?}"
    );
    let second = gate.check(&env, &rec);
    assert!(second.passed(false), "{second:#?}");
    assert_eq!(
        second.families_replayed, 0,
        "admitted once, given afterwards: {second:#?}"
    );
}

// ── the attack battery, at the gate ─────────────────────────────────────────

#[test]
fn swapping_a_stated_type_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let donor = built_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let (_, donor_payload) = read_payload(&olean(&donor, "K1Lib"));
    let false_type = donor_payload.constants[0].type_.clone();
    assert!(gate(&dir, "K1Lib", &zero_add()).passed(false));
    tamper(&dir, "K1Lib", |p| {
        constant_mut(p, &zero_add()).type_ = false_type
    });
    let verdict = gate(&dir, "K1Lib", &zero_add());
    assert_refused(&verdict, "type swap");
    assert!(matches!(
        verdict.refusals.first(),
        Some(ClosedRecheckRefusal::DeclarationRefused { name, .. }) if name == "K1Lib.zero_add'"
    ));
}

#[test]
fn flipping_a_proof_term_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let donor = built_lib(
        tmp.path(),
        "donor",
        "theorem K1Lib.zero_add' (n : Nat) : n = n := rfl\n",
    );
    let (_, donor_payload) = read_payload(&olean(&donor, "K1Lib"));
    let wrong_proof = donor_payload.constants[0].value.clone();
    assert!(gate(&dir, "K1Lib", &zero_add()).passed(false));
    tamper(&dir, "K1Lib", |p| {
        constant_mut(p, &zero_add()).value = wrong_proof
    });
    assert_refused(&gate(&dir, "K1Lib", &zero_add()), "proof flip");
}

#[test]
fn replacing_a_proof_by_sorry_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let sorry = elaborated_proof("theorem K1Lib.zero_add' (n : Nat) : 0 + n = n := sorry\n");
    assert!(gate(&dir, "K1Lib", &zero_add()).passed(false));
    tamper(&dir, "K1Lib", |p| {
        constant_mut(p, &zero_add()).value = Some(sorry)
    });
    let verdict = gate(&dir, "K1Lib", &zero_add());
    assert_refused(&verdict, "sorry proof");
    assert!(
        verdict
            .trust_markers
            .iter()
            .any(|m| m.starts_with("sorryAx")),
        "{verdict:#?}"
    );
    assert!(
        verdict.refusals.is_empty(),
        "a well-typed sorry re-admits; the marker is what refuses it"
    );
    // `--allow-sorry` may waive it, and only it.
    assert!(verdict.passed(true));
}

#[test]
fn turning_a_theorem_into_an_axiom_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let donor = built_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let (_, donor_payload) = read_payload(&olean(&donor, "K1Lib"));
    let axiom = donor_payload.constants[0].clone();
    assert_eq!(axiom.kind, ConstantKind::Axiom);
    assert!(gate(&dir, "K1Lib", &zero_add()).passed(false));
    tamper(&dir, "K1Lib", |p| *constant_mut(p, &zero_add()) = axiom);
    let verdict = gate(&dir, "K1Lib", &zero_add());
    assert_refused(&verdict, "theorem -> axiom");
    assert_eq!(verdict.imported_axioms, vec!["K1Lib.zero_add'".to_string()]);
    assert!(!verdict.passed(true), "--allow-sorry never waives an axiom");
}

#[test]
fn removing_a_dependency_module_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("dep");
    write_project(
        &dir,
        &["K1Base", "K1Lib"],
        &[
            (
                "K1Base",
                "theorem K1Base.helper (n : Nat) : 0 + n = n :=\n  Nat.rec (motive := fun k => 0 + k = k) rfl (fun k ih => congrArg Nat.succ ih) n\n",
            ),
            (
                "K1Lib",
                "import K1Base\n\ntheorem K1Lib.zero_add' (n : Nat) : 0 + n = n := K1Base.helper n\n",
            ),
        ],
    );
    assert!(build(&dir).failed.is_empty());
    assert!(gate(&dir, "K1Lib", &zero_add()).passed(false));
    // Re-export K1Lib with the same payload and NO imports: K1Base is never
    // loaded, so the proof's dependency is simply not there.
    let (_, payload) = read_payload(&olean(&dir, "K1Lib"));
    let rewritten = OleanExporter::export_with_payload(
        &[],
        &["K1Lib.zero_add'"],
        &[],
        clean_lake::CLEAN_OLEAN_GIT_HASH,
        &payload,
    )
    .expect("re-export");
    fs::write(olean(&dir, "K1Lib"), rewritten).expect("write");
    let verdict = gate(&dir, "K1Lib", &zero_add());
    assert_refused(&verdict, "dependency removed");
    assert!(
        verdict.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::AbsentFromEnvironment { name } if name == "K1Base.helper"
        )),
        "{verdict:#?}"
    );
}

#[test]
fn swapping_recursor_rules_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(
        tmp.path(),
        "ind",
        "inductive K1Lib.Two where\n  | a : K1Lib.Two\n  | b : K1Lib.Two\n",
    );
    let rec = name("K1Lib.Two.rec");
    assert!(gate(&dir, "K1Lib", &rec).passed(false));
    let honest_rules = {
        let (env, _) = load(&dir, "K1Lib");
        env.get_recursor(&rec)
            .expect("honest recursor")
            .rules
            .clone()
    };
    tamper(&dir, "K1Lib", |p| {
        let r = p
            .recursors
            .iter_mut()
            .find(|r| r.name == rec)
            .expect("recursor");
        let (a, b) = (r.rules[0].rhs.clone(), r.rules[1].rhs.clone());
        r.rules[0].rhs = b;
        r.rules[1].rhs = a;
    });
    // The import regenerates every recursor from its family (clean main's
    // `extend_recursors_structural`): the swapped record is refused and the
    // kernel's own rules are resident, so the swap is never believed. Either
    // the gate refuses (a rule mismatch), or the resident rules are exactly the
    // honest build's.
    let verdict = gate(&dir, "K1Lib", &rec);
    if verdict.passed(false) {
        let (env, _) = load(&dir, "K1Lib");
        let resident = env.get_recursor(&rec).expect("regenerated recursor");
        assert_eq!(
            resident.rules, honest_rules,
            "the swapped rules must not be resident: {verdict:#?}"
        );
    } else {
        assert!(
            verdict
                .refusals
                .iter()
                .any(|r| matches!(r, ClosedRecheckRefusal::RecursorRuleMismatch { .. })),
            "{verdict:#?}"
        );
    }
}

#[test]
fn an_imported_declaration_shadowing_a_native_reducer_name_keeps_its_own_meaning() {
    // A consumer whose base evaluates `K1Lib.double` BY NAME (a native
    // reducer registered for a name the base does not itself define — the
    // prelude does this for real names, Lean's `BitVec.ofFin` among them).
    // Until 2026-09-28 the gate refused the imported declaration outright
    // (`NativeReducerCollision`), because the kernel once fired a reducer on
    // the name alone and never consulted the imported value. Since the
    // kernel's native-fold authority (`clean-kernel/src/env/
    // native_fold_authority.rs`) a reducer fires only when its head's
    // δ-closure in the checking environment is a canonical definition, so the
    // declaration is admitted with ITS meaning, and the reducer's meaning is
    // available to nothing that cites it. Both halves are pinned below.
    use clean_kernel::env::{ConstantInfo, Reducibility, TrustedEnvExt};
    use clean_kernel::expr::{ExprKind, Literal};
    fn triple(args: &[&Expr]) -> Option<Expr> {
        match args {
            [arg] => match arg.kind() {
                ExprKind::Lit(Literal::Nat(v)) => v.to_u64().map(|v| Expr::nat_lit(3 * v)),
                _ => None,
            },
            _ => None,
        }
    }
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(
        tmp.path(),
        "shadow",
        "def K1Lib.double (n : Nat) : Nat := n + n
theorem K1Lib.four : K1Lib.double 2 = 4 := rfl
",
    );
    let double = name("K1Lib.double");
    let four = name("K1Lib.four");
    // Control: the same artifact over the builder's own base re-admits.
    assert!(gate(&dir, "K1Lib", &four).passed(false));

    let (mut env, _) = builder_base();
    env.register_native_reducer(double.clone(), triple);
    // The premise is real: this base's reducer says `K1Lib.double 2 = 6`.
    let reducer = env.get_native_reducer(&double).expect("registered");
    assert_eq!(reducer(&[&Expr::nat_lit(2)]), Some(Expr::nat_lit(6)));
    let mut gate = ImportedConeGate::new(&env);
    clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir)).expect("load");
    // A citation that holds only under the reducer's meaning, as a forged
    // artifact would carry it: `K1Lib.six : K1Lib.double 2 = 6 := rfl`.
    let nat = Expr::const_(name("Nat"), vec![]);
    let one = clean_kernel::Level::succ(clean_kernel::Level::zero());
    let six_ty = [
        nat.clone(),
        Expr::app(Expr::const_(double.clone(), vec![]), Expr::nat_lit(2)),
        Expr::nat_lit(6),
    ]
    .into_iter()
    .fold(Expr::const_(name("Eq"), vec![one.clone()]), Expr::app);
    let six_proof = [nat, Expr::nat_lit(6)]
        .into_iter()
        .fold(Expr::const_(name("Eq.refl"), vec![one]), Expr::app);
    let rejected = env.extend_constants_structural(std::iter::once(ConstantInfo {
        name: name("K1Lib.six"),
        level_params: vec![],
        type_: six_ty,
        value: Some(six_proof),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Theorem,
    }));
    assert!(rejected.is_empty(), "{rejected:?}");

    // The declaration's own meaning: admitted, with the citation true of it.
    let verdict = gate.check(&env, &BTreeSet::from([four.clone()]));
    assert!(verdict.passed(false), "{verdict:#?}");
    assert!(verdict
        .untrusted_in_cone
        .iter()
        .any(|m| m == "K1Lib.double"));
    // The reducer's meaning: refused by the kernel itself.
    let verdict = gate.check(&env, &BTreeSet::from([name("K1Lib.six")]));
    assert!(
        verdict.refusals.iter().any(|r| matches!(
            r,
            ClosedRecheckRefusal::DeclarationRefused { name, .. } if name == "K1Lib.six"
        )),
        "{verdict:#?}"
    );
}

// ── the build path that credited them ───────────────────────────────────────

#[test]
fn a_library_whose_theorem_is_sorry_does_not_build() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("sorry");
    write_project(
        &dir,
        &["K1Lib"],
        &[(
            "K1Lib",
            "theorem K1Lib.zero_add' (n : Nat) : 0 + n = n + 1 := sorry\n",
        )],
    );
    let result = build(&dir);
    assert!(result.built.is_empty(), "{result:?}");
    let (module, reason) = result.failed.first().expect("the module must fail");
    assert_eq!(module, "K1Lib");
    assert!(reason.contains("sorryAx"), "{reason}");
    assert!(!olean(&dir, "K1Lib").exists(), "nothing may be exported");
}

#[test]
fn a_dependent_citing_a_tampered_type_does_not_build() {
    let tmp = tempfile::tempdir().expect("tmp");
    let donor = built_lib(
        tmp.path(),
        "donor",
        "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n",
    );
    let (_, donor_payload) = read_payload(&olean(&donor, "K1Lib"));
    let false_type = donor_payload.constants[0].type_.clone();
    let result = rebuild_dependent_after_tamper(tmp.path(), "proj", USE_FALSE, |p| {
        constant_mut(p, &zero_add()).type_ = false_type;
    });
    let failure = result
        .failed
        .iter()
        .find(|(m, _)| m == "K1Use")
        .unwrap_or_else(|| panic!("K1Use.bad : 0 = 1 must not build: {result:?}"));
    assert!(
        failure.1.contains("cited closure not credited"),
        "{failure:?}"
    );
}

#[test]
fn a_dependent_citing_a_tampered_sorry_does_not_build() {
    let tmp = tempfile::tempdir().expect("tmp");
    let sorry = elaborated_proof("theorem K1Lib.zero_add' (n : Nat) : 0 + n = n := sorry\n");
    let result = rebuild_dependent_after_tamper(tmp.path(), "proj", USE_TRUE, |p| {
        constant_mut(p, &zero_add()).value = Some(sorry);
    });
    assert!(
        result
            .failed
            .iter()
            .any(|(m, e)| m == "K1Use" && e.contains("sorryAx")),
        "{result:?}"
    );
}

#[test]
fn a_dependent_citing_an_axiom_does_not_build_but_the_axiom_library_does() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("ax");
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[
            ("K1Lib", "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n"),
            ("K1Use", USE_FALSE),
        ],
    );
    let result = build(&dir);
    assert!(result.built.contains(&"K1Lib".to_string()), "{result:?}");
    assert!(
        result
            .failed
            .iter()
            .any(|(m, e)| m == "K1Use" && e.contains("imported axiom")),
        "{result:?}"
    );
}

// ── an axiom's NAME is no evidence (module-trust verification, 2026-09-25) ──

/// Every name `clean_kernel::is_foundational_axiom` accepts: exactly the
/// kernel's canonical axioms (`FOUNDATIONAL_AXIOMS`, `env/axiom_audit.rs`).
/// Before 2026-09-25 the gate exempted an imported axiom carrying a
/// whitelisted name, whatever its type, whenever the base did not already hold
/// it — `axiom proofIrrel : 0 = 1` in a dependency proved `0 = 1` in the
/// dependent, exit 0, "Build OK". Since 2026-09-28 the whitelist is these
/// seven names only (`proofIrrel`, `Eq.refl`, `WellFounded.fix`, `Char.decEq`
/// and `String.decEq` were never kernel axioms), the builder's base holds every
/// one of them, and the elaborator refuses to declare any of them.
const FOUNDATIONAL_NAMES: &[&str] = &[
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
];

#[test]
fn an_imported_axiom_carrying_a_foundational_name_is_refused() {
    let tmp = tempfile::tempdir().expect("tmp");
    let mut refused_at_elaboration = Vec::new();
    let mut refused_on_import = Vec::new();
    for (i, ax) in FOUNDATIONAL_NAMES.iter().enumerate() {
        assert!(
            clean_kernel::env::is_foundational_axiom(&name(ax)),
            "{ax} must be on the foundational list, or this row tests nothing"
        );

        // 1. From source: the library cannot declare the name at all, so
        //    nothing can cite a counterfeit through it.
        let dir = tmp.path().join(format!("fa{i}"));
        write_project(
            &dir,
            &["FaLib", "FaUse"],
            &[
                ("FaLib", &format!("axiom {ax} : (0 : Nat) = 1\n")),
                (
                    "FaUse",
                    &format!("import FaLib\n\ntheorem FaUse.bad : (0 : Nat) = 1 := {ax}\n"),
                ),
            ],
        );
        let result = build(&dir);
        let lib_failure = result
            .failed
            .iter()
            .find(|(m, _)| m == "FaLib")
            .unwrap_or_else(|| panic!("{ax}: the library declaring it must fail: {result:?}"));
        assert!(
            lib_failure.1.contains(&format!("`{ax}` is reserved")),
            "{ax}: refused as a reserved kernel name, not for another reason: {lib_failure:?}"
        );
        assert!(
            !result.built.iter().any(|m| m == "FaLib" || m == "FaUse"),
            "{ax}: {result:?}"
        );
        refused_at_elaboration.push(*ax);

        // 2. From a rewritten artifact: a genuine library's axiom renamed to
        //    the canonical name after the build (the only way left to put a
        //    counterfeit under it), with its trace restamped so a dependent
        //    reuses the rewritten bytes.
        let dir = tmp.path().join(format!("fa{i}-tampered"));
        write_project(
            &dir,
            &["FaLib", "FaUse"],
            &[
                ("FaLib", "axiom FaLib.stand : (0 : Nat) = 1\n"),
                (
                    "FaUse",
                    "import FaLib\n\ntheorem FaUse.ok : (0 : Nat) = 0 := rfl\n",
                ),
            ],
        );
        let first = build(&dir);
        assert!(first.failed.is_empty(), "{ax}: genuine fixture: {first:?}");
        tamper(&dir, "FaLib", |p| {
            constant_mut(p, &name("FaLib.stand")).name = name(ax);
        });
        restamp_trace(&dir, "FaLib");
        fs::write(
            dir.join("FaUse.lean"),
            format!("import FaLib\n\ntheorem FaUse.bad : (0 : Nat) = 1 := {ax}\n"),
        )
        .expect("rewrite dependent");
        let result = build(&dir);
        assert!(
            result.skipped.iter().any(|m| m == "FaLib"),
            "{ax}: the rewritten artifact must be REUSED, or this leg tests the source again: \
             {result:?}"
        );
        assert!(
            !result.built.iter().any(|m| m == "FaUse")
                && result.failed.iter().any(|(m, _)| m == "FaUse"),
            "{ax}: a dependent proving 0 = 1 from a counterfeit {ax} must not build: {result:?}"
        );
        // Why it cannot: the builder's base holds the kernel's own
        // declaration, and the counterfeit never enters the environment, in
        // one of two ways.
        // - A name genuine Init declares conflicts with Init's record, and the
        //   import is refused, as Lean refuses it.
        // - A name the base holds outside Init is kept, and the artifact's
        //   record is dropped (`filter_payload_dups`: base declarations are
        //   not artifacts). The citation then resolves to the canonical
        //   statement, and the gate over the name is given the base's
        //   declaration, never the artifact's.
        let (mut env, mut g) = builder_base();
        match clean_olean::load_module_with_deps(&mut env, "FaLib", &load_paths(&dir)) {
            Err(clean_olean::ImportError::ConflictingDeclaration { name: n, first }) => {
                assert_eq!(n, *ax, "{ax}: the conflict names the counterfeit");
                assert!(
                    first == "Init" || first.starts_with("Init."),
                    "{ax}: the first declaration is genuine Init's: {first}"
                );
                refused_on_import.push(*ax);
                continue;
            }
            Err(e) => panic!("{ax}: refused for another reason: {e}"),
            Ok(_) => {}
        }
        assert!(
            env.is_canonical_foundational_axiom(&name(ax)),
            "{ax}: after loading the rewritten artifact the name must still denote the \
             kernel's canonical declaration: {:?}",
            env.get_const(&name(ax))
        );
        assert!(
            env.non_canonical_ambient_declarations().is_empty(),
            "{ax}: {:?}",
            env.non_canonical_ambient_declarations()
        );
        let verdict = g.check(&env, &BTreeSet::from([name(ax)]));
        assert!(
            verdict.passed(false) && verdict.imported_axioms.is_empty(),
            "{ax}: the base's own declaration is given: {verdict:#?}"
        );
        refused_on_import.push(*ax);
    }
    // Not vacuous: every canonical name reached both refusals.
    assert_eq!(refused_at_elaboration, FOUNDATIONAL_NAMES);
    assert_eq!(refused_on_import, FOUNDATIONAL_NAMES);
}

#[test]
fn a_base_foundational_axiom_is_still_given() {
    // Control for the row above: a proof resting on the BASE's own `propext`
    // is credited, through an imported lemma.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("pe");
    write_project(
        &dir,
        &["PeLib", "PeUse"],
        &[
            (
                "PeLib",
                "theorem PeLib.iff_eq (a b : Prop) (h : a ↔ b) : a = b := propext h\n",
            ),
            (
                "PeUse",
                "import PeLib\n\ntheorem PeUse.t (a : Prop) : a = a := PeLib.iff_eq a a (Iff.intro id id)\n",
            ),
        ],
    );
    let result = build(&dir);
    assert!(
        result.failed.is_empty() && result.built.len() == 2,
        "{result:?}"
    );
    let verdict = gate(&dir, "PeLib", &name("PeLib.iff_eq"));
    assert!(verdict.passed(false), "{verdict:#?}");
}

// ── an upgraded base stub is not given (module-trust verification, 2026-09-25) ─

/// `(env, gate)` where `env` is the builder's base with the value-free stub
/// `Fact : Prop → Prop` upgraded — by the importer's own checked tier, as a
/// `.olean.private` or a Lean-built module does — to
/// `def Fact (p : Prop) : Prop := p → p`.
fn base_with_fact_upgraded() -> (Environment, ImportedConeGate) {
    use clean_kernel::env::TrustedEnvExt;
    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("io ops");
    // `Fact` is a stub of the opt-in stub theory since KR1 slice 1 (R132),
    // not of the default prelude: this base opts in.
    env.init_stub_theory().expect("stub theory");
    let gate = ImportedConeGate::new(&env);
    let stub = env
        .get_const(&name("Fact"))
        .expect("base holds Fact")
        .clone();
    assert!(
        stub.value.is_none(),
        "Fact must be a value-free stub in the base"
    );
    let value = {
        let surface =
            clean_parser::parse_file("def FactDef (p : Prop) : Prop := p → p\n").expect("parse");
        match clean_elab::ElabCtx::new(&env)
            .elab_decl(&surface[0])
            .expect("elaborate")
        {
            ElabResult::Definition { val, .. } => val,
            other => panic!("{other:?}"),
        }
    };
    // A plain (semireducible) definition record, as the importer converts one.
    let upgraded = clean_kernel::ConstantInfo::new(
        stub.name.clone(),
        stub.level_params.clone(),
        stub.type_.clone(),
        Some(value),
        false,
    );
    assert_eq!(upgraded.kind, ConstantKind::Definition);
    let (n, refused) = env.upgrade_axiom_stubs_checked(std::iter::once(upgraded));
    assert_eq!(
        n, 1,
        "the importer's checked tier accepts this upgrade: {refused:?}"
    );
    (env, gate)
}

/// Elaborate `source`'s one theorem against `env` and admit it through the
/// kernel's full check, as `clean check` / `clean lake build` do.
fn admit_theorem(env: &mut Environment, source: &str) -> Name {
    let surface = clean_parser::parse_file(source).expect("parse");
    let result = clean_elab::ElabCtx::new(env)
        .elab_decl(&surface[0])
        .expect("elaborate");
    let ElabResult::Theorem {
        name,
        universe_params,
        ty,
        proof,
        ..
    } = result
    else {
        panic!("{result:?}");
    };
    env.add_decl(clean_kernel::Declaration::Theorem {
        name: name.clone(),
        level_params: universe_params,
        type_: ty,
        value: proof,
    })
    .expect("the kernel admits it against the upgraded environment");
    name
}

#[test]
fn a_theorem_resting_on_an_upgraded_base_stub_is_refused() {
    let (mut env, mut gate) = base_with_fact_upgraded();
    // In the consumer's environment this is a kernel-checked proof of False:
    // `Fact False` unfolds to `False → False`, and the BASE's own axiom
    // `Fact.out : Fact p → p` then yields `False`.
    let bad = admit_theorem(
        &mut env,
        "theorem fact_false : False := @Fact.out False (fun x => x)\n",
    );
    let verdict = gate.check(&env, &BTreeSet::from([bad.clone()]));
    assert_refused(&verdict, "fact_false");
    assert!(
        verdict.untrusted_in_cone.contains(&"Fact".to_string()),
        "the upgraded stub must count as untrusted: {verdict:#?}"
    );
    assert!(
        verdict.refusals.iter().any(|r| r.subject() == "fact_false"),
        "the replay over the base must refuse the citing theorem itself: {verdict:#?}"
    );
}

#[test]
fn a_theorem_not_unfolding_an_upgraded_base_stub_is_still_credited() {
    // Control: the upgrade alone refuses nothing — a theorem that uses `Fact`
    // only as the base declares it re-admits over the base.
    let (mut env, mut gate) = base_with_fact_upgraded();
    let ok = admit_theorem(
        &mut env,
        "theorem fact_ok (p : Prop) (h : Fact p) : p := @Fact.out p h\n",
    );
    let verdict = gate.check(&env, &BTreeSet::from([ok]));
    assert!(verdict.passed(false), "{verdict:#?}");
}

// ── the reference verify-fresh compares against ─────────────────────────────

#[test]
fn a_fresh_build_reproduces_the_artifact_byte_for_byte_and_not_a_tampered_one() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", LIB);
    let on_disk = fs::read(olean(&dir, "K1Lib")).expect("artifact");
    let (result, fresh) = BuildContext::new(Workspace::load(&dir).expect("ws"))
        .build_fresh_artifacts(&["K1Lib".to_string()])
        .expect("fresh build");
    assert!(result.failed.is_empty(), "{result:?}");
    let fresh = fresh.get("K1Lib").expect("fresh artifact");
    assert_eq!(
        fresh.olean, on_disk,
        "clean lake build must be byte-reproducible"
    );
    assert_eq!(
        fs::read(olean(&dir, "K1Lib"))
            .expect("artifact still there")
            .len(),
        on_disk.len(),
        "a fresh build must not touch the project's own artifact"
    );
    let sorry = elaborated_proof("theorem K1Lib.zero_add' (n : Nat) : 0 + n = n := sorry\n");
    tamper(&dir, "K1Lib", |p| {
        constant_mut(p, &zero_add()).value = Some(sorry)
    });
    assert_ne!(
        fs::read(olean(&dir, "K1Lib")).expect("tampered"),
        fresh.olean
    );
}

#[path = "module_trust/metadata.rs"]
mod metadata;

#[path = "module_trust/real_artifacts.rs"]
mod real_artifacts;

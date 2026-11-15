// Keep the constellation-coordinated Clean pin atomic across the independently
// publishable crates and the standalone rustc frontend lock. "Frozen" below
// always means "frozen relative to the constants in THIS file" — the pin itself
// moves often and is meant to; see the `clean-kernel` note in
// crates/trust-ir/Cargo.toml for why the old "deliberately frozen baseline"
// wording was retired.
//
// Until 2026-08-19 this test was the ONLY mechanical enforcement of the Clean
// pin in the whole repository, because the root `[patch]` rewrote clean.git to
// `../clean` PATH deps, path deps emit no `source =` row, and a Clean move
// therefore produced a byte-identical root Cargo.lock that `--locked` could
// never fail on. That patch is gone (see the note in the workspace root
// Cargo.toml), so the root lock now records the revision and `--locked` is a
// second, independent check. This test remains the enforcement for the legs no
// lockfile covers: the two manifests and the `exclude`d frontend workspace.
// For that workspace it also asks Cargo whether the whole lock still RESOLVES
// (`frontend_lock_resolves_under_locked`), because a non-pin manifest
// change stales it too and nothing else here would notice.
//
// The patch's removal is itself an invariant now — `clean_pin_is_not_path_patched`
// below. Re-introducing it would restore the pin cycle it was deleted to cut:
// a path patch makes ambient working-tree bytes authoritative while Clean pins
// trust-ir back through the non-optional clean-reflect edge. The Clean commit
// every repo pins would then have to name the trust-ir commit that names it.
//
// Every assertion below appends PIN_MOVE_PROTOCOL, because whoever trips one
// has almost certainly just hand-edited a subset of the legs.
//
// The machine-readable leg table lives in `scripts/pin_rewrite.py`; the two
// must be updated together whenever a declaration is added or reshaped.

/// Appended to every assertion in this file. A partial pin move has shipped
/// three times; the recovery procedure has to be in the failure output, not in
/// a document the bumper was never going to open.
const PIN_MOVE_PROTOCOL: &str = r#"

================ DEPENDENCY PIN INCOHERENCE ================
A Clean/AY pin move is ATOMIC. Moving fewer than all of its legs
leaves main RED. Do not hand-edit — run the one correct action:

    scripts/bump-dep-pin.sh clean <40-hex-sha> [--clean-version X.Y.Z]
    scripts/bump-dep-pin.sh ay    <40-hex-sha> [--ay-version X.Y.Z]

When target Clean changes either package version, use the coordinated form:
    scripts/bump-dep-pin.sh clean-ay <clean-sha> <ay-sha> \
        --clean-version X.Y.Z --ay-version X.Y.Z

CLEAN legs:
  1. crates/trust-ir/Cargo.toml               clean-kernel            (1 rev)
  2. crates/trust-ir-build/Cargo.toml         kernel/mathverse/olean/verify (5 declarations)
  3. crates/trust-ir/tests/dependency_pin_coherence.rs  CLEAN_REVISION
  4. frontend/Cargo.lock  <-- SEPARATE WORKSPACE. frontend/ is `exclude`d
     from the root workspace, so it is INVISIBLE to --workspace. This is
     the leg that has been missed three times. Refresh:
       targo update --manifest-path frontend/Cargo.toml -p clean-kernel
  5. Cargo.lock (root) — since the root [patch] was deleted (2026-08-19)
     this DOES record the rev on every clean.git package, so `--locked`
     now fails on a partial move too.
     Refresh: targo metadata --format-version 1 --all-features >/dev/null
  6. (RETIRED) There is no ../clean working-tree leg any more. The root
     [patch] is gone, so cargo compiles clean.git AT THE PINNED REV and
     never the sibling's working tree. Do NOT "align" ../clean by
     checking it out at the pin, and do NOT chase ../clean's HEAD with a
     new pin: Clean pins trust-ir back (clean-reflect), so following its
     HEAD reopens the pin cycle this deletion cut. Cross-repo publication
     instead uses the ratified predecessor-epoch cut: backedges may retain
     immutable predecessor identities while successor repositories advance.
     The final epoch receipt, not raw five-workspace SHA equality, attests
     the exact cohort.

AY legs:
  1. crates/trust-ir-ay/Cargo.toml            ay + ay-proof          (2 revs)
  2. crates/trust-ir-ay/src/vc.rs             pub const AY_REV        (1 rev)
  3. crates/trust-ir-ay/src/bvblast.rs        BVBLAST_PROVER          (1 rev)
  4. crates/trust-ir/tests/dependency_pin_coherence.rs  AY_REVISION
  5. Cargo.lock (root) — 37 ay packages; refresh with the metadata line
  6. The selected Clean COMMIT's Cargo.toml pins ay too (7 declarations).
     The bumper reads that immutable commit before writing anything. If it
     disagrees, Cargo.lock carries two ay graphs and this guard fails.

VERIFY: scripts/run-targo.sh test -p trust-ir --test dependency_pin_coherence
        (standing gate 7 in scripts/ci_gates.sh; its exact toolchain-free
         mirror is scripts/pin_rewrite.py static-guard)
The compiled test is independent parity for the mandatory static mirror;
`check --workspace` alone still executes neither one.
============================================================
"#;

const CLEAN_REPOSITORY: &str = "https://github.com/alabsystems/clean.git";
// Leg 3. This constant had been left at 71449eaa across two Clean moves, so
// the clean half of this gate had been red (and therefore uninformative) the
// whole time. It is now the revision legs 1, 2, 4 and 5 actually carry, which
// is TrustIR's exact local Clean authority. The cross-repository graph is an
// SCC: predecessor backedges intentionally need not resolve this same commit.
// The final epoch receipt attests those predecessor/successor identities.
const CLEAN_REVISION: &str = "550ad0858df6a00c61a7cdabc7f37fa0bc975258";
const CLEAN_VERSION: &str = "0.9.0";
const AY_REPOSITORY: &str = "https://github.com/alabsystems/ay.git";
const AY_REVISION: &str = "add70f658ebe48a4d6a112a68a9d2866dab68970";
const AY_VERSION: &str = "0.27.0";

const TRUST_IR_MANIFEST: &str = include_str!("../Cargo.toml");
const TRUST_IR_AY_MANIFEST: &str = include_str!("../../trust-ir-ay/Cargo.toml");
const TRUST_IR_AY_VC: &str = include_str!("../../trust-ir-ay/src/vc.rs");
const TRUST_IR_AY_BVBLAST: &str = include_str!("../../trust-ir-ay/src/bvblast.rs");
const TRUST_IR_BUILD_MANIFEST: &str = include_str!("../../trust-ir-build/Cargo.toml");
const ROOT_MANIFEST: &str = include_str!("../../../Cargo.toml");
const ROOT_LOCK: &str = include_str!("../../../Cargo.lock");
const FRONTEND_LOCK: &str = include_str!("../../../frontend/Cargo.lock");

fn clean_dependency_lines(manifest: &str) -> Vec<&str> {
    manifest
        .lines()
        .map(str::trim)
        .filter(|line| {
            !line.starts_with('#') && line.starts_with("clean-") && line.contains(" = {")
        })
        .collect()
}

fn assert_exact_manifest_pins(manifest_name: &str, manifest: &str, expected_count: usize) {
    let lines = clean_dependency_lines(manifest);
    assert_eq!(
        lines.len(),
        expected_count,
        "{manifest_name} Clean dependency inventory changed; update this guard and every pin atomically: {lines:?}{PIN_MOVE_PROTOCOL}"
    );

    let exact_git = format!("git = \"{CLEAN_REPOSITORY}\"");
    let exact_rev = format!("rev = \"{CLEAN_REVISION}\"");
    let exact_version = format!("version = \"{CLEAN_VERSION}\"");
    for line in lines {
        assert!(
            line.contains(&exact_version),
            "{manifest_name} has a Clean dependency outside the frozen package version: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            line.contains(&exact_git),
            "{manifest_name} has a Clean dependency outside the canonical repository: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            line.contains(&exact_rev),
            "{manifest_name} has a Clean dependency outside the frozen revision: {line}{PIN_MOVE_PROTOCOL}"
        );
        assert!(
            !line.contains("branch =") && !line.contains("tag ="),
            "{manifest_name} must not add floating Clean selectors: {line}{PIN_MOVE_PROTOCOL}"
        );
    }
}

#[test]
fn clean_consumability_baseline_is_exact_and_atomic() {
    assert_exact_manifest_pins("crates/trust-ir/Cargo.toml", TRUST_IR_MANIFEST, 1);
    assert_exact_manifest_pins(
        "crates/trust-ir-build/Cargo.toml",
        TRUST_IR_BUILD_MANIFEST,
        5,
    );

    let clean_packages: Vec<&str> = FRONTEND_LOCK
        .split("[[package]]")
        .filter(|package| {
            package.lines().any(|line| {
                line.trim()
                    .strip_prefix("name = \"")
                    .is_some_and(|name| name.starts_with("clean-"))
            })
        })
        .collect();
    assert_eq!(
        clean_packages.len(),
        1,
        "frontend/Cargo.lock Clean package inventory changed; update this guard and every pin atomically{PIN_MOVE_PROTOCOL}"
    );
    let exact_version = format!("version = \"{CLEAN_VERSION}\"");
    assert!(
        clean_packages[0]
            .lines()
            .any(|line| line.trim() == exact_version),
        "frontend/Cargo.lock does not resolve Clean to the frozen package version{PIN_MOVE_PROTOCOL}"
    );

    let exact_source =
        format!("source = \"git+{CLEAN_REPOSITORY}?rev={CLEAN_REVISION}#{CLEAN_REVISION}\"");
    assert!(
        clean_packages[0]
            .lines()
            .any(|line| line.trim() == exact_source),
        "frontend/Cargo.lock does not resolve its Clean package to the exact frozen revision{PIN_MOVE_PROTOCOL}"
    );

    let clean_git_source = format!("git+{CLEAN_REPOSITORY}");
    let clean_source_rows: Vec<&str> = FRONTEND_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&clean_git_source))
        .collect();
    assert_eq!(
        clean_source_rows,
        vec![exact_source.as_str()],
        "frontend/Cargo.lock contains a floating or split Clean source{PIN_MOVE_PROTOCOL}"
    );
}

/// The workspace root must NOT redirect clean.git onto the `../clean` sibling.
///
/// A `[patch]` there is invisible to every consumer of trust-ir (Cargo only
/// honours `[patch]` in the workspace root it is building), so it bought
/// nothing but local convenience — while costing two things that matter:
/// the root Cargo.lock stopped recording the Clean revision at all, and
/// `ty-mcc-drift-guard` had to prove the patched declaration by requiring
/// `HEAD(../clean) == the declared rev`. Because Clean pins trust-ir back
/// through the non-optional clean-reflect edge, that requirement made the
/// five-repo pin set unsatisfiable: the Clean commit every repo names would
/// have had to name the trust-ir commit that names it. Keeping the patch out
/// is what keeps that set solvable.
///
/// Develop against a live sibling with an UNCOMMITTED override instead — a
/// gitignored `.cargo/config.toml` `[patch]`, or `paths = ["../clean"]`.
#[test]
fn clean_pin_is_not_path_patched() {
    let offending: Vec<&str> = ROOT_MANIFEST
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with('#'))
        .filter(|line| line.starts_with("[patch") && line.contains("clean.git"))
        .collect();
    assert!(
        offending.is_empty(),
        "the workspace root re-introduced a Clean path patch: {offending:?}\n\
         It cannot help any consumer (Cargo ignores [patch] outside the root being \
         built) and it reopens the trust-ir <-> clean pin cycle.{PIN_MOVE_PROTOCOL}"
    );

    // Leg 5, newly enforceable now that the patch is gone: every clean.git row
    // in the root lock must be the frozen revision, and there must be at least
    // one — a lock with no clean.git row means the patch is back.
    let exact_source =
        format!("source = \"git+{CLEAN_REPOSITORY}?rev={CLEAN_REVISION}#{CLEAN_REVISION}\"");
    let clean_git_source = format!("git+{CLEAN_REPOSITORY}");
    let clean_source_rows: Vec<&str> = ROOT_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&clean_git_source))
        .collect();
    assert!(
        !clean_source_rows.is_empty(),
        "root Cargo.lock records no clean.git source; the Clean dependency was \
         path-patched or dropped{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        clean_source_rows
            .iter()
            .all(|line| *line == exact_source.as_str()),
        "root Cargo.lock contains a stale or split Clean source: {clean_source_rows:?}{PIN_MOVE_PROTOCOL}"
    );
}

/// Appended to the frontend-lock resolution assertion below, beside
/// [`PIN_MOVE_PROTOCOL`]: that assertion also fires on a lock made stale by a
/// change that is NOT a pin move, and then this is the fix.
const FRONTEND_LOCK_REFRESH: &str = r#"

================ frontend/Cargo.lock DOES NOT RESOLVE ================
frontend/ is a SEPARATE workspace (`exclude`d from the root), so no
--workspace command ever resolves its lock. Any manifest change on its
path-dependency graph (crates/trust-ir, crates/trust-ir-build and their
own path dependencies) can make it stale, pin move or not.

If the lock is STALE ("cannot update the lock file ... --locked"),
refresh it (non-compiling; no verification claim) and commit the result:

    cd frontend && targo metadata --offline --format-version 1 >/dev/null

The diff should add or drop exactly the packages your manifest change
added or dropped. If it also moves unrelated versions, the offline cache
could not supply the locked ones: discard it and run the same command
without --offline.

If it failed for another reason, read Cargo's error above. The offline
query needs every package the lock names in the local cache; when it
cannot decide offline the test asks again WITH the network, so a
network error here means the cache is cold AND the registry or the
Clean git remote is unreachable. Warm the cache and re-run:

    targo fetch --locked --manifest-path frontend/Cargo.toml
=======================================================================
"#;

/// `frontend/Cargo.lock` must RESOLVE under `--locked`, not merely carry the
/// right Clean row.
///
/// `frontend/` is workspace-`exclude`d, so no `--workspace` command reads its
/// lock, and [`clean_consumability_baseline_is_exact_and_atomic`] reads only
/// its Clean rows. On 2026-09-25 a NON-pin change (`trust-ir-build` gained the
/// path dependency `trust-ir-laws`) left this lock stale, every `--locked`
/// frontend command failed, and no gate noticed until review. This asks Cargo
/// itself, through the non-compiling query `metadata --locked`, which fails
/// exactly when the lock would have to change to describe the current
/// manifests, whichever leg moved.
///
/// It runs the Cargo that is running this test (`CARGO`, which Cargo sets for
/// every test process). Under gate 7 that is `targo` itself (measured: a
/// `targo --unverified test` process sees `CARGO=<store>/bin/targo`, and targo
/// warns that a recursive `$CARGO` must select its own lane), so this runs
/// `targo metadata`: it compiles nothing, needs no lane, and establishes no
/// verification.
///
/// Network: the query runs `--offline` first. `metadata` needs every package
/// the lock names, for every platform, in the local cache, and building or
/// testing the root workspace does not put them there (the frontend lock pins
/// crates.io versions the root lock does not use). So when the offline query
/// cannot DECIDE (its error names `--offline` and is not the stale-lock error),
/// the same query runs once more with the network allowed, and that answer is
/// the verdict. Measured 2026-09-27 on a fresh `CARGO_HOME`: offline answers
/// "no matching package named `serde`"; the networked query downloads the
/// frontend's packages and passes; on a warm cache the networked query makes
/// no request (it passes behind an unreachable proxy). A stale lock fails
/// either way ("cannot update the lock file ... --locked"). Without a cache
/// and without the network this test FAILS (fail closed: the lock is then not
/// shown to resolve), and the message names the fetch that warms the cache.
#[test]
fn frontend_lock_resolves_under_locked() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    let manifest = format!("{root}/frontend/Cargo.toml");
    // Runtime, not `env!`: the Cargo running the test is the authority, and a
    // test binary run outside Cargo refuses rather than guessing one.
    let cargo = std::env::var_os("CARGO");
    let resolve = |offline: bool| -> (bool, String) {
        let Some(cargo) = cargo.as_ref() else {
            return (
                false,
                "CARGO is unset: run this through `scripts/run-targo.sh test -p trust-ir \
                 --test dependency_pin_coherence`, so the toolchain running the gate \
                 resolves the lock"
                    .to_owned(),
            );
        };
        let mut command = std::process::Command::new(cargo);
        command.args(["metadata", "--locked", "--format-version", "1"]);
        if offline {
            command.arg("--offline");
        }
        match command
            .arg("--manifest-path")
            .arg(&manifest)
            .current_dir(root)
            .stdout(std::process::Stdio::null())
            .output()
        {
            Ok(output) => (
                output.status.success(),
                String::from_utf8_lossy(&output.stderr).into_owned(),
            ),
            Err(error) => (false, format!("could not run CARGO: {error}")),
        }
    };
    let (offline_ok, offline_stderr) = resolve(true);
    if offline_ok {
        return;
    }
    // The stale-lock error's own help text names `--offline` too, so the
    // undecided case is "names --offline" MINUS "the lock would change".
    let stale = offline_stderr.contains("cannot update the lock file");
    let undecided_offline = !stale && offline_stderr.contains("--offline");
    let (success, stderr) = if undecided_offline {
        let (online_ok, online_stderr) = resolve(false);
        (
            online_ok,
            format!(
                "offline, Cargo could not decide:\n{offline_stderr}\n\
                 with the network allowed:\n{online_stderr}"
            ),
        )
    } else {
        (false, offline_stderr)
    };
    assert!(
        success,
        "`$CARGO metadata --locked [--offline] --format-version 1 --manifest-path \
         {manifest}` failed:\n{stderr}{FRONTEND_LOCK_REFRESH}{PIN_MOVE_PROTOCOL}"
    );
}

#[test]
fn ay_manifest_and_root_lock_are_exact_and_atomic() {
    // BOTH AY legs of the manifest. `ay` is the solver facade; `ay-proof` is the
    // bit-blast proof exporter, a DIRECT dependency because the facade does not
    // re-export `BvExpr` / `export_bv_blast_proof_expr`. They must move
    // together: a split rev puts two ay graphs in the lock, and the bv-blast
    // authority capability re-runs ay's blaster to bind a stored refutation to
    // a re-derived goal — so a rev drift between the two legs would compare a
    // proof produced by one blaster against a CNF derived by another.
    let ay_dependency_lines: Vec<&str> = TRUST_IR_AY_MANIFEST
        .lines()
        .map(str::trim)
        .filter(|line| {
            !line.starts_with('#')
                && (line.starts_with("ay = {") || line.starts_with("ay-proof = {"))
        })
        .collect();
    assert_eq!(
        ay_dependency_lines.len(),
        2,
        "trust-ir-ay AY dependency inventory changed; update this guard and every pin atomically{PIN_MOVE_PROTOCOL}"
    );
    let manifest_git = format!("git = \"{AY_REPOSITORY}\"");
    let manifest_rev = format!("rev = \"{AY_REVISION}\"");
    let manifest_version = format!("version = \"{AY_VERSION}\"");
    for line in &ay_dependency_lines {
        assert!(
            line.contains(&manifest_git)
                && line.contains(&manifest_rev)
                && line.contains(&manifest_version)
                && !line.contains("branch =")
                && !line.contains("tag ="),
            "trust-ir-ay must use the exact canonical AY authority: {line}{PIN_MOVE_PROTOCOL}"
        );
    }

    // One provenance leg no lockfile can catch: `AY_REV` is stamped
    // into every emitted verification bundle as solver provenance. A stale
    // value compiles, links, and silently misreports which solver replayed a
    // proof — there is no resolution step that could disagree with it.
    let exact_ay_rev = format!("pub const AY_REV: &str = \"{AY_REVISION}\";");
    assert!(
        TRUST_IR_AY_VC
            .lines()
            .any(|line| line.trim() == exact_ay_rev),
        "crates/trust-ir-ay/src/vc.rs AY_REV disagrees with the frozen AY revision; it stamps evidence provenance into every emitted bundle and a stale value silently misreports which solver replayed a proof{PIN_MOVE_PROTOCOL}"
    );
    let exact_bvblast_prover =
        format!("pub const BVBLAST_PROVER: &str = \"trust-ir-ay/bvblast@{AY_REVISION}\";");
    assert!(
        TRUST_IR_AY_BVBLAST
            .lines()
            .any(|line| line.trim() == exact_bvblast_prover),
        "crates/trust-ir-ay/src/bvblast.rs BVBLAST_PROVER disagrees with the frozen AY revision; it is the authority identity stamped into every stored bit-blast certificate{PIN_MOVE_PROTOCOL}"
    );

    let selector = format!("git+{AY_REPOSITORY}?rev={AY_REVISION}");
    let ay_git_source = format!("git+{AY_REPOSITORY}?rev=");
    let ay_selector_rows: Vec<&str> = ROOT_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(&ay_git_source))
        .collect();
    assert!(
        !ay_selector_rows.is_empty(),
        "root Cargo.lock must resolve the AY graph pulled through trust-ir-ay and Clean{PIN_MOVE_PROTOCOL}"
    );
    assert!(
        ay_selector_rows.iter().all(|line| line.contains(&selector)),
        "root Cargo.lock contains a stale or split AY selector: {ay_selector_rows:?}{PIN_MOVE_PROTOCOL}"
    );

    let exact_source = format!("source = \"{selector}#{AY_REVISION}\"");
    let ay_source_rows: Vec<&str> = ay_selector_rows
        .iter()
        .copied()
        .filter(|line| line.starts_with("source = "))
        .collect();
    assert!(
        !ay_source_rows.is_empty()
            && ay_source_rows
                .iter()
                .all(|line| *line == exact_source.as_str()),
        "root Cargo.lock does not resolve every AY package to the exact AY authority: {ay_source_rows:?}{PIN_MOVE_PROTOCOL}"
    );

    let ay_packages: Vec<&str> = ROOT_LOCK
        .split("[[package]]")
        .filter(|package| package.lines().any(|line| line.trim() == exact_source))
        .collect();
    assert_eq!(
        ay_packages.len(),
        ay_source_rows.len(),
        "root Cargo.lock AY package inventory disagrees with its exact source rows{PIN_MOVE_PROTOCOL}"
    );
    let exact_version = format!("version = \"{AY_VERSION}\"");
    assert!(
        ay_packages
            .iter()
            .all(|package| package.lines().any(|line| line.trim() == exact_version)),
        "root Cargo.lock resolves an AY package outside the frozen package version{PIN_MOVE_PROTOCOL}"
    );
}

/// The x86-64 vector-compare certificate ground names the AY that produced
/// every certificate (`trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`), and trust-cg's
/// certificate gate requires its own AY pin to equal it, while trust-cg's pin
/// transaction requires trust-ir to co-own trust-cg's AY. So an AY move here
/// that does not carry the rule would turn trust-cg's gate red at trust-cg's
/// next pin move, a red nothing runs per landing. This makes the move fail
/// HERE instead: re-certify the certificate cells under the new AY with
/// trust-cg's gate, then move the rule's `ay.rev`, `ay.version` and
/// `certifying_sha256` in the same commit as this pin
/// (`scripts/bump-dep-pin.sh` cannot move them: they are evidence, not a pin
/// leg). The revision AND the version are held, as `publish/transforms.sh` T1
/// holds them, because the rule's version is the one the rebuilt binary's
/// banner must report. What this cannot see is the re-certification itself:
/// the digests are evidence, not identity. Mirrored without a compiler by
/// `scripts/pin_rewrite.py static-guard` (its `GUARD_TEST_MIRRORS` row).
#[test]
fn x86_icmp_certificate_rule_names_the_pinned_ay() {
    let rule = trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE.ay;
    assert_eq!(
        (rule.rev, rule.version),
        (AY_REVISION, AY_VERSION),
        "CHC_X86_ICMP_CERTIFICATE_RULE.ay (rev, version) differs from the AY pin: re-certify \
         the x86-64 vector-compare certificate cells under the new AY (trust-cg \
         scripts/check_x86_icmp_certificates.py) and move the rule with the pin{PIN_MOVE_PROTOCOL}"
    );
}

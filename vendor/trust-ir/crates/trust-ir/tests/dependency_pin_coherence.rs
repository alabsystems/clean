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
  2. crates/trust-ir-build/Cargo.toml         kernel/mathverse/olean  (3 revs)
  3. crates/trust-ir/tests/dependency_pin_coherence.rs  CLEAN_REVISION
  4. frontend/Cargo.lock  <-- SEPARATE WORKSPACE. frontend/ is `exclude`d
     from the root workspace, so it is INVISIBLE to --workspace. This is
     the leg that has been missed three times. Refresh:
       cargo update --manifest-path frontend/Cargo.toml -p clean-kernel
  5. Cargo.lock (root) — since the root [patch] was deleted (2026-08-19)
     this DOES record the rev on every clean.git package, so `--locked`
     now fails on a partial move too.
     Refresh: cargo metadata --format-version 1 --all-features >/dev/null
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
const CLEAN_REVISION: &str = "84c9ae5e2017debb80f58e1f6fec4cdd8cf5487e";
const CLEAN_VERSION: &str = "0.4.0";
const AY_REPOSITORY: &str = "https://github.com/alabsystems/ay.git";
const AY_REVISION: &str = "09951c0e62934ccdec7525b0a08e37342d19aefb";
const AY_VERSION: &str = "0.15.0";

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
        3,
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

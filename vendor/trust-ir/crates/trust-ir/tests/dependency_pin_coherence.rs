// Keep the deliberately frozen Clean consumability baseline atomic across the
// independently publishable crates and the standalone rustc frontend lock.
//
// This test is the ONLY mechanical enforcement of the Clean pin in the whole
// repository: the root `[patch]` rewrites clean.git to `../clean` PATH deps,
// path deps emit no `source =` row, so a Clean move produces a byte-identical
// root Cargo.lock and `--locked` can never fail on it. Every assertion below
// therefore appends PIN_MOVE_PROTOCOL, because whoever trips one has almost
// certainly just hand-edited a subset of the legs.
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

    scripts/bump-dep-pin.sh clean <40-hex-sha>
    scripts/bump-dep-pin.sh ay    <40-hex-sha>

CLEAN legs:
  1. crates/trust-ir/Cargo.toml               clean-kernel            (1 rev)
  2. crates/trust-ir-build/Cargo.toml         kernel/mathverse/olean  (3 revs)
  3. crates/trust-ir/tests/dependency_pin_coherence.rs  CLEAN_REVISION
  4. frontend/Cargo.lock  <-- SEPARATE WORKSPACE. frontend/ is `exclude`d
     from the root workspace, so it is INVISIBLE to --workspace. This is
     the leg that has been missed three times. Refresh:
       cargo update --manifest-path frontend/Cargo.toml -p clean-kernel
  5. Cargo.lock (root) — normally byte-identical for a Clean move (the
     root [patch] redirects clean.git to ../clean, so no `source` line
     records the rev), but it DOES record the sibling's dependency graph.
     Refresh: cargo metadata --format-version 1 --all-features >/dev/null
  6. ../clean working tree MUST be checked out AT the rev — the [patch]
     is a PATH dep, so cargo compiles the sibling's WORKING TREE, not
     the pin:  git -C ../clean fetch && git -C ../clean checkout <sha>

AY legs:
  1. crates/trust-ir-ay/Cargo.toml            ay + ay-proof          (2 revs)
  2. crates/trust-ir-ay/src/vc.rs             pub const AY_REV        (1 rev)
  3. crates/trust-ir-ay/src/bvblast.rs        BVBLAST_PROVER          (1 rev)
  4. crates/trust-ir/tests/dependency_pin_coherence.rs  AY_REVISION
  5. Cargo.lock (root) — 37 ay packages; refresh with the metadata line
  6. ../clean/Cargo.toml PINS ay TOO (7 declarations). If it disagrees,
     the root lock carries TWO ay graphs (37 packages at each rev) and
     this guard fails. Move ../clean first; trust-ir cannot bump ay alone.

VERIFY: scripts/run-targo.sh test -p trust-ir --test dependency_pin_coherence
        (standing gate 7 in scripts/ci_gates.sh; the toolchain-free half is
         scripts/pin_rewrite.py census --dep clean|ay)
WHY IT KEEPS SLIPPING: this is a TEST. `check --workspace` — the natural
verification for a "pure pin bump" — CANNOT catch it.
============================================================
"#;

const CLEAN_REPOSITORY: &str = "https://github.com/alabsystems/clean.git";
const CLEAN_REVISION: &str = "71449eaa47957f90669ea40cf6ea270829044e20";
const CLEAN_VERSION: &str = "0.1.0";
const AY_REPOSITORY: &str = "https://github.com/alabsystems/ay.git";
const AY_REVISION: &str = "0c0538325fe2b0ed9542f7623124399d24df1312";
const AY_VERSION: &str = "0.10.0";

const TRUST_IR_MANIFEST: &str = include_str!("../Cargo.toml");
const TRUST_IR_AY_MANIFEST: &str = include_str!("../../trust-ir-ay/Cargo.toml");
const TRUST_IR_AY_VC: &str = include_str!("../../trust-ir-ay/src/vc.rs");
const TRUST_IR_AY_BVBLAST: &str = include_str!("../../trust-ir-ay/src/bvblast.rs");
const TRUST_IR_BUILD_MANIFEST: &str = include_str!("../../trust-ir-build/Cargo.toml");
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

    let clean_source_rows: Vec<&str> = FRONTEND_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("git+https://github.com/alabsystems/clean.git"))
        .collect();
    assert_eq!(
        clean_source_rows,
        vec![exact_source.as_str()],
        "frontend/Cargo.lock contains a floating or split Clean source{PIN_MOVE_PROTOCOL}"
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
    let ay_selector_rows: Vec<&str> = ROOT_LOCK
        .lines()
        .map(str::trim)
        .filter(|line| line.contains("git+https://github.com/alabsystems/ay.git?rev="))
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

/// AY leg 6 lives in ANOTHER repository. `../clean/Cargo.toml` declares the
/// same AY authority (7 declarations), and the root `[patch]` pulls Clean in by
/// path — so if the two disagree the root lock resolves two ay graphs and the
/// assertions above fail with a split selector. Checking it here names the
/// cause instead of leaving the bumper to infer it from a lockfile diff.
///
/// Deliberately a skip, not a failure, when the sibling is absent: a checkout
/// without `../clean` cannot build this workspace at all, so there is nothing
/// for this test to protect there.
#[test]
fn clean_sibling_agrees_with_the_frozen_ay_authority() {
    let sibling =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../clean/Cargo.toml");
    let Ok(manifest) = std::fs::read_to_string(&sibling) else {
        eprintln!(
            "SKIP: no Clean sibling manifest at {} — AY leg 6 unchecked",
            sibling.display()
        );
        return;
    };

    let selector = format!("git = \"{AY_REPOSITORY}\", rev = \"{AY_REVISION}\"");
    let disagreeing: Vec<&str> = manifest
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with('#') && line.contains(AY_REPOSITORY))
        .filter(|line| !line.contains(&selector))
        .collect();
    assert!(
        disagreeing.is_empty(),
        "../clean/Cargo.toml co-owns the AY pin and disagrees with it; the root Cargo.lock will carry two ay graphs and trust-ir cannot fix that alone: {disagreeing:?}{PIN_MOVE_PROTOCOL}"
    );
}

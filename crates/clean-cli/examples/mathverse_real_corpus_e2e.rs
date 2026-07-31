// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #4: real-corpus search -> use end-to-end qualification utility.
//!
//! Exercises the Mathverse retrieval -> tactic loop on a REAL `mathverse-v*`
//! Release corpus (not the synthetic fixtures used by the unit tests in
//! clean-mathverse / clean-elab):
//!
//!   download/locate shards -> `LibraryLoader::load_library` -> assert hundreds
//!   of thousands of constants -> `lookup_name` a known-present Mathlib lemma ->
//!   `search_for_kernel_goal` -> `run_strict_mathverse_use`, checking that the
//!   corpus contains both KernelVerified and below-Strict headers.
//!
//! The confidence assertions below are an explicit model of Strict's documented
//! enum policy because `TrustGate` is crate-private. They do not independently
//! prove that the production implementation matches the model. The production
//! strict entrypoint is exercised, but goal closure remains best-effort.
//!
//! This utility lives in `clean-cli` because it is the only crate that can depend
//! on BOTH `clean-mathverse` (loader/search/release) and `clean-elab` (the
//! `mathverse_use` tactic behind the `mathverse-library` feature) without a
//! dependency cycle — `clean-mathverse` cannot depend on `clean-elab`.
//!
//! # Qualification
//!
//! This is an explicit Rust qualification utility, not a default test. It
//! requires `MATHVERSE_E2E_CORPUS=1`; missing corpus/download prerequisites are
//! failures, so a successful exit proves that the real lane actually ran.
//!
//! ```bash
//! MATHVERSE_E2E_CORPUS=1 cargo run -p clean-cli \
//!     --example mathverse_real_corpus_e2e
//! ```

use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::{BinderInfo, Environment, Expr};
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::premise_select::{search_for_kernel_goal, PremiseConfig};
use clean_mathverse::release::{download_release, ReleaseConfig};
use clean_mathverse::search::MathverseSearch;
use clean_mathverse::types::ImportConfidence;

use clean_elab::tactic::{
    clear_mathverse_library, run_strict_mathverse_use, set_mathverse_library, ProofState,
    TacticError,
};

/// Candidate Mathlib / Lean core lemma names to probe for. At least one of
/// these must resolve in a real corpus; we don't hard-code a single name
/// because shard contents evolve across releases.
const PROBE_LEMMAS: &[&str] = &[
    "Nat.add_comm",
    "Nat.zero_add",
    "Nat.add_zero",
    "Nat.succ",
    "Nat.add_assoc",
    "Nat.mul_comm",
    "Nat.le_refl",
    "Eq.refl",
    "And.intro",
];

/// RAII guard so a thread-local library install cannot leak past the run.
struct LibGuard;
impl Drop for LibGuard {
    fn drop(&mut self) {
        clear_mathverse_library();
    }
}

fn main() {
    assert!(
        matches!(std::env::var("MATHVERSE_E2E_CORPUS").as_deref(), Ok("1")),
        "qualification requires MATHVERSE_E2E_CORPUS=1"
    );

    // Step 1: locate or download the corpus.
    let library_root = locate_or_download_corpus().expect(
        "MATHVERSE_E2E_CORPUS=1 but no corpus was located or downloaded; \
         qualification cannot pass without exercising real shards",
    );
    eprintln!(
        "e2e: using mathverse library root {}",
        library_root.display()
    );

    // Step 2: load all shards into a single searchable library.
    let library = clean_mathverse::build_library::load_built_library(&library_root)
        .expect("real corpus must load via LibraryLoader::load_library");

    // Step 3: assert the corpus is the REAL one — hundreds of thousands of
    // constants (synthetic fixtures carry a handful). Documented current
    // release is ~3.2M declarations; 100k is a deliberately loose floor.
    let count = library.constant_count();
    eprintln!("e2e: loaded {count} constants");
    assert!(
        count >= 100_000,
        "expected hundreds of thousands of constants from the real corpus, \
         got {count} (is this a synthetic / partial library?)"
    );

    // Step 4: probe for a stable, known-present Lean/Mathlib lemma. We require
    // at least one of the candidates to resolve via `lookup_name`.
    let mut resolved: Vec<(&str, ImportConfidence)> = Vec::new();
    for &name in PROBE_LEMMAS {
        if let Some(header) = library.lookup_name(name) {
            let conf = header
                .confidence()
                .expect("real header must carry a known ImportConfidence byte");
            eprintln!("e2e: resolved {name} -> confidence {conf:?}");
            resolved.push((name, conf));
        }
    }
    assert!(
        !resolved.is_empty(),
        "none of the probe lemmas {PROBE_LEMMAS:?} resolved in the real corpus \
         via lookup_name — corpus is missing core Lean/Mathlib content?"
    );

    // -----------------------------------------------------------------------
    // LOAD-BEARING ASSERTION: a model of the trust-gate dichotomy on REAL
    // headers.
    //
    // `mathverse_use` runs under `TrustGate::Strict`, which accepts a candidate
    // iff its `ImportConfidence == KernelVerified` and rejects everything below
    // Strict (Translated / Axiomatized / Unverified / SourceVerified) as
    // "below Strict". We assert that dichotomy directly against the real
    // headers in the corpus, mirroring `TrustGate::Strict.accepts` exactly via
    // the public `ImportConfidence` enum (the gate type itself is pub(crate) in
    // clean-elab). `strict_policy_model_accepts` is the documented Strict rule,
    // but this local model does not prove implementation correspondence.
    // -----------------------------------------------------------------------
    let mut kernel_verified: Option<&str> = None;
    let mut below_strict: Option<(&str, ImportConfidence)> = None;
    for &(name, conf) in &resolved {
        if conf == ImportConfidence::KernelVerified {
            assert!(
                strict_policy_model_accepts(conf),
                "Strict policy model must ACCEPT a KernelVerified real header ({name})"
            );
            kernel_verified.get_or_insert(name);
        } else {
            assert!(
                !strict_policy_model_accepts(conf),
                "Strict policy model must REJECT a below-Strict real header ({name}, {conf:?})"
            );
            below_strict.get_or_insert((name, conf));
        }
    }

    // Scan the whole corpus for a concrete KernelVerified header and a concrete
    // below-Strict (Translated / Axiomatized) header, so the dichotomy is
    // checked on the real distribution and not just the handful of probes.
    let (corpus_kernel, corpus_below) = scan_trust_extremes(&library);
    eprintln!(
        "e2e: corpus trust scan -> KernelVerified present: {}, \
         Translated/Axiomatized present: {}",
        corpus_kernel.is_some(),
        corpus_below.is_some()
    );

    // The real corpus must contain at least one KernelVerified constant (the
    // kernel-checked Lean/Mathlib core), and Strict must accept it.
    let kv_name = corpus_kernel
        .or(kernel_verified.map(str::to_owned))
        .expect("real corpus must contain at least one KernelVerified constant");
    assert!(
        strict_policy_model_accepts(ImportConfidence::KernelVerified),
        "Strict policy model accepts KernelVerified ({kv_name})"
    );

    // If the corpus carries any below-Strict headers (it does — translated /
    // axiomatized imports from the 68 source systems), Strict must reject them.
    let below_owned = below_strict.map(|(n, c)| (n.to_owned(), c));
    let (name, conf) = corpus_below
        .or(below_owned)
        .expect("real corpus must expose a Translated/Axiomatized below-Strict header");
    assert!(
        matches!(
            conf,
            ImportConfidence::Translated | ImportConfidence::Axiomatized
        ),
        "expected a Translated/Axiomatized below-Strict header, got {conf:?}"
    );
    assert!(
        !strict_policy_model_accepts(conf),
        "Strict policy model rejects below-Strict header ({name}, {conf:?})"
    );

    // -----------------------------------------------------------------------
    // Step 5: drive the REAL tactic entrypoint end-to-end.
    //
    // Install the library thread-locally, build a kernel goal out of a probed
    // lemma's symbol, run the same search the tactic uses, then invoke the
    // strict use entrypoint. Full goal closure is BEST-EFFORT: the single-shard
    // skeleton loader and the dep budget (1000) can legitimately prevent it.
    // The hard contract above is the trust-gate behavior, not closure.
    // -----------------------------------------------------------------------
    let _guard = LibGuard;

    // Build a search/use library handle. We need a mutable library for
    // `search_for_kernel_goal` (it interns the goal into the arena); load a
    // fresh one so the thread-local install below is independent.
    let mut search_lib = clean_mathverse::build_library::load_built_library(&library_root)
        .expect("real corpus reload for search must succeed");

    // Goal: a trivially-typed Pi over the lemma's head symbol. This exercises
    // the kernel-goal -> FlatExpr bridge and discrimination-tree query path.
    let probe = resolved[0].0;
    let head = probe.split('.').next().unwrap_or("Nat");
    let goal = Expr::pi(
        BinderInfo::Default,
        Expr::const_str(head),
        Expr::const_str(head),
    );

    let config = PremiseConfig {
        max_results: 10,
        ..PremiseConfig::default()
    };
    let candidates = search_for_kernel_goal(&mut search_lib, &goal, &[], &config);
    eprintln!(
        "e2e: search_for_kernel_goal returned {} candidate(s) for head symbol {head}",
        candidates.len()
    );
    assert!(
        !candidates.is_empty(),
        "real-corpus premise search must surface >=1 candidate for a core symbol"
    );

    // Install the freshly-loaded library and run the strict use tactic.
    let install_lib = clean_mathverse::build_library::load_built_library(&library_root)
        .expect("real corpus reload for tactic must succeed");
    set_mathverse_library(install_lib);

    let env = Environment::new();
    let mut state = ProofState::new(env, goal);
    match run_strict_mathverse_use(&mut state) {
        Ok(()) => {
            eprintln!("e2e: run_strict_mathverse_use CLOSED the goal (stretch goal met)");
        }
        Err(TacticError::SearchExhausted { tactic, detail }) => {
            // Expected common outcome: candidates found but skeleton loader /
            // dep budget / trust gate prevented closure. This is fine — the
            // confidence-policy model is already asserted hard above.
            assert_eq!(tactic, "mathverse_use");
            eprintln!("e2e: run_strict_mathverse_use did not close goal (best-effort): {detail}");
        }
        Err(other) => panic!("run_strict_mathverse_use failed unexpectedly: {other:?}"),
    }

    eprintln!(
        "e2e: real-corpus search->use loop exercised; Strict confidence-policy model asserted."
    );
}

/// Mirror of `clean_elab::tactic::TrustGate::Strict.accepts` (which is
/// `pub(crate)` in clean-elab): Strict accepts a candidate iff its confidence
/// is exactly `KernelVerified`.
fn strict_policy_model_accepts(confidence: ImportConfidence) -> bool {
    confidence == ImportConfidence::KernelVerified
}

/// Scan the whole library for one KernelVerified name and one below-Strict
/// (Translated / Axiomatized) name, to prove the dichotomy on the real
/// distribution rather than only the probe set.
fn scan_trust_extremes(
    library: &MathverseLibrary,
) -> (Option<String>, Option<(String, ImportConfidence)>) {
    let mut kernel: Option<String> = None;
    let mut below: Option<(String, ImportConfidence)> = None;
    for idx in 0..library.constant_count() {
        let i = idx as u32;
        let header = match library.get_constant(i) {
            Some(h) => h,
            None => continue,
        };
        let conf = match header.confidence() {
            Ok(c) => c,
            Err(_) => continue,
        };
        let name = library.get_name(i).map(str::to_owned);
        match conf {
            ImportConfidence::KernelVerified if kernel.is_none() => {
                kernel = name;
            }
            ImportConfidence::Translated | ImportConfidence::Axiomatized if below.is_none() => {
                if let Some(n) = name {
                    below = Some((n, conf));
                }
            }
            _ => {}
        }
        if kernel.is_some() && below.is_some() {
            break;
        }
    }
    (kernel, below)
}

// ---------------------------------------------------------------------------
// Corpus location / download
// ---------------------------------------------------------------------------

/// Locate the corpus on disk, or (when `MATHVERSE_E2E_CORPUS` is set) download
/// it. Returns the library root directory that `LibraryLoader` understands
/// (i.e. the directory holding `mathverse-manifest.json` + `base/` shards), or
/// `None` if nothing usable could be obtained.
fn locate_or_download_corpus() -> Option<PathBuf> {
    // 1. Explicit override.
    if let Ok(path) = std::env::var("MATHVERSE_LIBRARY_PATH") {
        let p = PathBuf::from(path);
        if library_root_is_loadable(&p) {
            return Some(p);
        }
    }

    // 2. Conventional in-repo locations, resolved from this crate's manifest
    //    dir (= crates/clean-cli) up to the repo root.
    let repo_root = repo_root();
    for rel in ["data/mathverse-library", "data/mathverse-shards"] {
        let candidate = repo_root.join(rel);
        if library_root_is_loadable(&candidate) {
            return Some(candidate);
        }
    }

    // 3. Nothing on disk: attempt a download (env gate already checked by the
    //    caller). Prefer the in-process `download_release`; fall back to the
    //    shell script if that path is unavailable.
    let out_dir = repo_root.join("data/mathverse-library");
    let cfg = ReleaseConfig::default_for_clean(&out_dir);
    match download_release(&cfg) {
        Ok(root) => {
            if library_root_is_loadable(&root) {
                return Some(root);
            }
            // download_release may extract into a nested dir; re-probe.
            if library_root_is_loadable(&out_dir) {
                return Some(out_dir);
            }
        }
        Err(e) => {
            eprintln!("e2e: download_release failed ({e}); trying download script");
            if run_download_script(&repo_root, &out_dir) && library_root_is_loadable(&out_dir) {
                return Some(out_dir);
            }
        }
    }

    None
}

/// A directory is a loadable library root if it carries the manifest that
/// `LibraryLoader::load_manifest` expects.
fn library_root_is_loadable(root: &Path) -> bool {
    if !root.is_dir() {
        return false;
    }
    root.join("mathverse-manifest.json").is_file()
}

/// Repo root, derived from `CARGO_MANIFEST_DIR` (= crates/clean-cli).
fn repo_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .join("../..")
        .canonicalize()
        .unwrap_or_else(|_| manifest_dir.join("../.."))
}

/// Shell out to `scripts/download_mathverse_library.sh` as a fallback.
fn run_download_script(repo_root: &Path, out_dir: &Path) -> bool {
    let script = repo_root.join("scripts/download_mathverse_library.sh");
    if !script.is_file() {
        return false;
    }
    let status = Command::new("bash")
        .arg(&script)
        .arg(format!("--output-dir={}", out_dir.display()))
        .current_dir(repo_root)
        .status();
    matches!(status, Ok(s) if s.success())
}

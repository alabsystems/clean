// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end proof that KERNEL-VERIFIED MATHLIB content can close a Clean goal.
//!
//! This is the acceptance probe for
//! [`docs/plans/MATHVERSE_USABLE_LIBRARY_2026-07-27.md`] brick 1.5: the first
//! demonstration that the whole chain actually works on real Mathlib —
//!
//! ```text
//!   Mathlib .olean
//!     -> clean mathverse stamp-verified --closure-root ... --parallel
//!     -> Basic.mathverse + kernel-verified.json
//!     -> load_built_library  (applies the manifest: SourceVerified -> KernelVerified)
//!     -> set_mathverse_library
//!     -> run_strict_mathverse_use   (TrustGate::Strict: confidence 0 only)
//!     -> goal CLOSED
//! ```
//!
//! # Why this differs from `mathverse_real_corpus_e2e`
//!
//! That utility builds a *synthetic* goal (`Pi(Const(head), Const(head))`) and
//! documents closure as explicitly BEST-EFFORT — it never asserts the goal is
//! actually closed. This one reconstructs a real KernelVerified constant's OWN
//! type out of the shard and uses that as the goal, so closure is a HARD
//! assertion. If this exits 0, Mathlib content genuinely discharged a Clean
//! proof obligation through the trust-gated path.
//!
//! # Scope — what this does NOT prove
//!
//! `mathverse_use` is registered `Nullary` and `mk_const` yields a BARE
//! constant, so `exact` only closes goals that unify with a lemma's WHOLE type.
//! This probe therefore demonstrates the *plumbing* (shard -> trust gate ->
//! add_decl -> close), not the project goal of citing a lemma BY NAME and
//! APPLYING it to arguments. That needs bricks 3-4 (level params + a
//! name-taking tactic with argument synthesis).
//!
//! # Usage
//!
//! ```bash
//! # 1. produce a kernel-verified Mathlib shard
//! clean mathverse stamp-verified \
//!     "$HOME/mathlib4/.lake/build/lib/lean/Mathlib/Logic/Basic.olean" \
//!     --out-dir /tmp/mathlib-stamped \
//!     --manifest /tmp/mathlib-stamped/kernel-verified.json \
//!     --closure-root "$HOME/mathlib4/.lake/build/lib/lean" --parallel --json
//!
//! # 2. prove a Clean goal with it
//! MATHVERSE_SHARD_DIR=/tmp/mathlib-stamped \
//!     cargo run -p clean-cli --example mathverse_mathlib_citation
//! ```
//!
//! Optional `MATHVERSE_PROBE_NAME=<constant>` pins the constant to cite;
//! otherwise the first `KernelVerified` theorem in the manifest is used.

use std::path::PathBuf;

use clean_elab::tactic::{
    run_strict_mathverse_use, set_mathverse_library, ProofState, TacticError,
};
use clean_kernel::Environment;
use clean_mathverse::build_library::load_built_library;
use clean_mathverse::search::MathverseSearch;
use clean_mathverse::shard_reconstruct::reconstruct_single_subdag_public;
use clean_mathverse::types::{DeclKind, ImportConfidence};

fn main() {
    let shard_dir: PathBuf = std::env::var("MATHVERSE_SHARD_DIR")
        .expect(
            "set MATHVERSE_SHARD_DIR to a directory produced by \
             `clean mathverse stamp-verified --out-dir <dir> --manifest <dir>/kernel-verified.json`",
        )
        .into();

    // The manifest is one of TWO ways a constant reaches `KernelVerified`:
    // `stamp-verified` also rewrites the shard BYTES destructively, so an
    // already-stamped shard needs no sidecar. Warn rather than assert, and let
    // the actual KernelVerified count below be the real gate.
    if !shard_dir.join("kernel-verified.json").is_file() {
        eprintln!(
            "citation: note — no kernel-verified.json in {}; relying on confidence \
             stamped directly in the shard bytes",
            shard_dir.display()
        );
    }

    // ---------------------------------------------------------------------
    // Step 1: load, and confirm the manifest upgrade actually happened.
    // ---------------------------------------------------------------------
    let library = load_built_library(&shard_dir).expect("stamped shard dir must load");

    let total = library.constant_count();
    let mut kv_names: Vec<String> = Vec::new();
    for idx in 0..(total as u32) {
        let Some(name) = library.get_name(idx) else {
            continue;
        };
        let name = name.to_string();
        if let Some(header) = library.lookup_name(&name) {
            // THEOREMS ONLY. `validate_dependency_loader_trust` requires the
            // selected candidate to be `DeclKind::Theorem`, and `exact` needs a
            // proof term. Picking the first KernelVerified constant of any kind
            // lands on things like `Fact.casesOn` (a recursor) or a definition,
            // which fail for a reason unrelated to what this probe measures.
            if header.confidence() == Ok(ImportConfidence::KernelVerified)
                && header.decl_kind() == Ok(DeclKind::Theorem)
            {
                kv_names.push(name);
            }
        }
    }

    eprintln!(
        "citation: loaded {} constant(s) from {}; {} KernelVerified",
        total,
        shard_dir.display(),
        kv_names.len()
    );
    assert!(
        !kv_names.is_empty(),
        "shard dir has 0 KernelVerified constants — TrustGate::Strict would admit nothing. \
         Did the kernel-verified.json manifest apply?"
    );

    // ---------------------------------------------------------------------
    // Step 2: choose the constant to cite and rebuild ITS OWN type as the goal.
    // ---------------------------------------------------------------------
    let probe = match std::env::var("MATHVERSE_PROBE_NAME") {
        Ok(n) => {
            assert!(
                kv_names.iter().any(|k| k == &n),
                "MATHVERSE_PROBE_NAME={n} is not KernelVerified in this shard dir"
            );
            n
        }
        Err(_) => kv_names[0].clone(),
    };

    let header = library
        .lookup_name(&probe)
        .expect("probe constant must resolve");
    assert_eq!(
        header.confidence(),
        Ok(ImportConfidence::KernelVerified),
        "probe must be KernelVerified for Strict to accept it"
    );

    // Must use the level-list-aware reconstruction, exactly as the tactic path
    // does. Building the goal with the no-arg helper drops every `Const`'s
    // universe arguments, so the goal and the candidate's own type disagree and
    // `exact` fails with a bogus shape mismatch that looks like a product defect.
    let goal = reconstruct_single_subdag_public(
        library.exprs(),
        library.levels(),
        library.strings(),
        library.level_lists(),
        header.type_idx,
    )
    .expect("probe constant's type must reconstruct out of the shard");

    eprintln!("citation: goal := type of `{probe}` (reconstructed from shard)");

    // ---------------------------------------------------------------------
    // Step 3: run the REAL strict tactic entrypoint against it.
    // ---------------------------------------------------------------------

    // Release the inspection copy BEFORE loading the one the tactic owns.
    // `set_mathverse_library` takes ownership, so a second load is unavoidable,
    // but holding both at once doubles peak residency — and each copy carries the
    // whole-arena reconstruct table built above. With a real Mathlib olean
    // preload (~170k-constant closure) on top, the two copies were enough to kill
    // the process with no message. `goal` is an owned `Expr` and does not borrow
    // the library, so dropping here is safe.
    drop(library);

    let install = load_built_library(&shard_dir).expect("reload for tactic install must succeed");
    set_mathverse_library(install);

    // `with_prelude`, NOT `Environment::new()`. A real proof session always has a
    // prelude, and it is load-bearing here: value-less declarations (Inductive /
    // Constructor / Recursor) can never be stamped `KernelVerified`, so a
    // closure containing `Eq`, `Eq.refl`, `And`, `Iff` … is only admissible
    // because those are already RESIDENT and the loader therefore never adds
    // them. An empty environment makes the lane unsatisfiable by construction
    // and tests nothing.
    let mut env = Environment::with_prelude();

    // OPTIONAL HYBRID PRELOAD.
    //
    // Value-less declarations (Inductive / Constructor / Recursor) can never be
    // stamped `KernelVerified` — `stamp-verified` stamps only names whose VALUE
    // the kernel accepted, and these have none — and the shard format stores no
    // `InductiveDecl`, so they cannot be replayed from a header either. Lean
    // CORE inductives (`Eq`, `Iff`, `And`) come free with the prelude, which is
    // why core-closure theorems already cite. Mathlib's own structures
    // (`Unique`, `Fact`, `CommMonoid`, …) do not.
    //
    // So supply them from the lane that already carries them: import the
    // module's `.olean` into this environment first. The theorem corpus is still
    // cited THROUGH Mathverse under `TrustGate::Strict`; the olean import only
    // provides the type infrastructure the shard format cannot express. With the
    // residency fix, those inductives are then satisfied by the ambient
    // environment instead of being demanded from the shard.
    //
    //   MATHVERSE_PRELOAD_OLEAN=Mathlib.Logic.Unique
    //   LEAN_PATH=<toolchain>/lib/lean  (and/or LEAN_PACKAGES_PATH)
    if let Ok(module) = std::env::var("MATHVERSE_PRELOAD_OLEAN") {
        let mut search_paths: Vec<PathBuf> = Vec::new();
        for var in ["LEAN_PATH", "LEAN_PACKAGES_PATH"] {
            if let Ok(v) = std::env::var(var) {
                for p in v.split(':').filter(|s| !s.is_empty()) {
                    search_paths.push(PathBuf::from(p));
                }
            }
        }
        assert!(
            !search_paths.is_empty(),
            "MATHVERSE_PRELOAD_OLEAN={module} needs LEAN_PATH and/or LEAN_PACKAGES_PATH"
        );
        // BOUNDED loader, matching what the real frontend uses
        // (`clean-elab/src/imports.rs` -> `load_module_with_deps_bounded` with
        // FRONTEND_OLEAN_IMPORT_MODULE_LIMIT). The unbounded
        // `load_module_with_deps` dies without a message on a real Mathlib module
        // — its closure is ~170k constants across thousands of modules.
        const MODULE_LIMIT: usize = 16_384;
        match clean_olean::load_module_with_deps_bounded(
            &mut env,
            &module,
            &search_paths,
            MODULE_LIMIT,
        ) {
            Ok(summaries) => {
                let loaded: usize = summaries.iter().map(|s| s.added_constants).sum();
                eprintln!("citation: preloaded `{module}` from .olean ({loaded} constants)");
            }
            Err(e) => panic!("preload of `{module}` failed: {e}"),
        }
    }

    let mut state = ProofState::new(env, goal);

    // BY-NAME path (MATHVERSE_BY_NAME=1): cite `probe` directly instead of
    // searching for it.
    //
    // This is the capability the nullary search cannot express. It is also a
    // much sharper probe: the goal IS `probe`'s own type, so a by-name citation
    // of `probe` MUST close it. The search path can legitimately miss simply
    // because premise selection ranked something else first — that outcome tells
    // us nothing about the shard lane, which is exactly why the search path's
    // TypeMismatch exits 2 rather than 1.
    if std::env::var("MATHVERSE_BY_NAME").is_ok() {
        return match clean_elab::tactic::run_mathverse_apply(&mut state, &probe) {
            Ok(()) => {
                eprintln!("citation: GOAL CLOSED by NAME via mathverse_apply (constant `{probe}`)")
            }
            Err(e) => {
                eprintln!(
                    "citation: BY-NAME citation of `{probe}` FAILED: {e:?}\n\
                     citation: the goal is this constant's own type, so a by-name citation must \
                     close it — this is a real defect, not a search miss."
                );
                std::process::exit(1);
            }
        };
    }

    match run_strict_mathverse_use(&mut state) {
        Ok(()) => {
            eprintln!(
                "citation: GOAL CLOSED by kernel-verified library content via \
                 TrustGate::Strict (constant `{probe}`)"
            );
        }
        Err(TacticError::SearchExhausted { tactic, detail }) => {
            // NOT an opaque failure: this is the measurement. The goal IS a
            // KernelVerified constant's own type, so a refusal here localizes a
            // structural blocker in the shard route rather than a bad probe.
            //
            // The blockers this probe originally enumerated (empty level-list
            // table; value-less inductives rejected by Strict; Definition/family
            // deps unreplayable) are all FIXED — see
            // docs/plans/MATHVERSE_USABLE_LIBRARY_2026-07-27.md §0.1. Listing
            // them here now would send the reader after settled ground, so what
            // follows is the CURRENT triage instead.
            eprintln!(
                "citation: NOT CLOSED ({tactic}).\n\
                 citation: detail: {detail}\n\
                 citation: the goal was literally `{probe}`'s own reconstructed type, so this is a \
                 blocker in the shard lane, not a probe mismatch. Current triage:\n\
                 citation:   * `below Strict` on an INDUCTIVE — the family replay did not install \
                 it. Re-run with CLEAN_FAMILY_DEBUG=1 to see whether the pre-pass found it \
                 pending, and CLEAN_WS16_DEBUG=<name> for the replay internals. Pending-but-no-WS16 \
                 means reconstruction failed before replay was reached.\n\
                 citation:   * `Unknown constant: X` — X is missing from the shard SET (coverage), \
                 or was registered out of order. Check whether X is declared anywhere:\n\
                 citation:       it is a coverage gap if no shard declares it; stamp the module \
                 that does.\n\
                 citation:   * `beyond reconstructable prefix` — a prefix-path reconstruction \
                 survived somewhere; it must use reconstruct_single_subdag_public."
            );
            std::process::exit(1);
        }
        Err(TacticError::TypeMismatch { .. }) => {
            // NOT a defect. `mathverse_use` is a nullary goal-directed SEARCH:
            // it applies whatever premise selection ranks first, and `exact`
            // rejects a candidate whose type does not unify with the goal. That
            // is the tactic working as designed on a goal it has no matching
            // lemma for — distinct from the structural refusals above, and it
            // must not be reported as one.
            eprintln!(
                "citation: NOT CLOSED — premise search returned a candidate whose type does not \
                 unify with the goal (`exact` TypeMismatch).\n\
                 citation: this is ordinary search behavior, NOT a shard-lane blocker: the \
                 dependency closure loaded and registered successfully. It means no ranked \
                 candidate proves `{probe}`, which for a nullary search tactic is expected unless \
                 the search happens to return the probe constant itself."
            );
            std::process::exit(2);
        }
        Err(other) => panic!("run_strict_mathverse_use failed unexpectedly: {other:?}"),
    }
}

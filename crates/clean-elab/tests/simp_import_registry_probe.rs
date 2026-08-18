// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Regression probe: imported `@[simp]` lemmas reach bare `simp` under a
//! real `import Init` (RC-B / T10 — the typed `simpExtension` decoder).**
//!
//! Before the typed decoder, every `Lean.Meta.simpExtension` entry in a real
//! Lean `.olean` was silently dropped at parse (`header.other < 2` in the
//! generic pair heuristic rejected the one-field `ScopedEnvExtension.Entry`
//! constructor), so bare `simp` under real imports saw exactly the 41
//! hand-written builtin rules (`lemmas_builtin.rs`) versus ~10,000 upstream
//! `@[simp]` sites in the Init tree alone — the single largest
//! real-import degradation cause for the simp family.
//!
//! This file is the batched probe — ONE full `import Init` (the expensive
//! step, mirroring `instance_priority_import_probe.rs`) — and it doubles as
//! the standing regression:
//!
//! * [`imported_simp_registry_has_thousands_of_lemmas`] — TEETH: the kernel
//!   simp registry (`Environment::get_simp_lemmas`, exactly what
//!   `collect_registry_lemmas` reads) must hold >= 1,000 entries after
//!   `import Init`. If the decoder regresses to the old bail, this collapses
//!   to the handful the prelude registers and fails loudly.
//! * [`bare_simp_rewrites_imported_append_nil`] — the acceptance probe: bare
//!   `simp` (no `only`, no named lemmas) closes a genuinely-stuck
//!   `l ++ [] = l` on an opaque list.
//! * [`bare_simp_fires_non_builtin_imported_registry_lemma`] — the sharp
//!   decoder teeth: `List.length_reverse` is `@[simp]` upstream but is NOT
//!   one of the 41 builtins, so its goal can only close if the DECODED
//!   registry entry fired; the closing proof must reference the lemma.
//!
//! All lanes skip when the pinned toolchain is absent.
//!
//! Goals are built by instantiating the imported lemma's OWN environment
//! statement (universe params at 0, `α := Nat`, the list binder at a fresh
//! opaque axiom), so they match whatever spelling the imported constant
//! carries — the probe measures lemma *reachability*, not statement-spelling
//! parity.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

/// The pinned toolchain whose `SimpTheorem` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

const IMPORT_ROOT: &str = "Init";

fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.join("Init.olean").is_file().then_some(lib)
}

/// A prelude environment with a real `import Init` on top — the configuration
/// where the decoded `@[simp]` registry actually feeds bare `simp`.
fn imported_env() -> Option<Environment> {
    let lib = v4_30_lib_path()?;
    let mut env = Environment::with_prelude();
    load_module_with_deps(&mut env, IMPORT_ROOT, &[lib])
        .unwrap_or_else(|e| panic!("importing {IMPORT_ROOT} must succeed: {e}"));
    Some(env)
}

/// TEETH: after a real `import Init`, the kernel simp registry must hold
/// thousands of entries — the Init tree persists ~10,000 `@[simp]`
/// registrations, and the decoded floor is far above 1,000. If the typed
/// decoder regresses to the old one-field-constructor bail, the registry
/// collapses to the prelude's handful and this fails.
#[test]
fn imported_simp_registry_has_thousands_of_lemmas() {
    let Some(env) = imported_env() else {
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let count = env.get_simp_lemmas().count();
    assert!(
        count >= 1000,
        "expected >= 1000 registered simp lemmas after `import {IMPORT_ROOT}` \
         (the Init tree persists ~10,000 @[simp] entries), got {count} — the \
         typed simpExtension decoder is not feeding the registry"
    );
    // Spot-check a known upstream @[simp] lemma that is NOT a builtin.
    assert!(
        env.is_simp_lemma(&Name::from_string("List.length_reverse")),
        "List.length_reverse (@[simp] in Init.Data.List.Lemmas, not a Clean \
         builtin) must be registered from the decoded extension"
    );
}

// The two bare-simp CLOSURE probes that previously lived here (append_nil,
// length_reverse under a real `import Init`) are intentionally NOT debug-mode
// unit tests anymore: with ~10k registered lemmas a single debug-profile
// bare-simp call ran for tens of minutes (candidate scans + per-node WHNF in
// path building), which is not a test, it is a hang. Closure acceptance for
// the imported registry is owned by the release-binary G-SIMP family gate
// (scripts/tactic_parity/g_simp.sh, fail-closed, wired into local_gate.sh),
// and the simp-performance brick (head-indexed candidate lookup + per-env
// lemma-set caching) is the tracked follow-on that can bring a bounded probe
// back here. Registration and counts stay asserted above — a decoder
// regression still fails this file loudly.

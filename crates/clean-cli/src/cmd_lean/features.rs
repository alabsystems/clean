// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lean`'s feature descriptor (`clean features`, `clean help lean`,
//! `docs/cli/lean.md`).

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// The `lean` front door.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["lean"],
    summary: "Run Clean with `lean`'s command line and Lean's semantics (Experimental)",
    description: "\
A front door for tools that invoke `lean`: `clean lean FILE` (or the `clean` binary invoked \
as `lean`, e.g. through a symlink) elaborates FILE through the same module driver `clean \
check` runs and prints every message the way `lean` does — `<file>:<line>:<col>: \
error|warning: <text>`, the bare output of `#eval` / `#check` / `#print` / `#print axioms`, \
or one JSON object per line under `--json` — and exits 1 exactly when an error was logged. \
Unlike `clean check`, which is a verification verdict, it does not fail a file for having no \
declaration or for an explicit `sorry` (that is Lean's warning, exit 0). It fails closed \
where Clean's outcome has no Lean counterpart: a synthetic `sorry` nobody reported, a proof \
resting on `trustedArith`/`trustedAy`, a kernel or re-validation failure, an exhausted \
per-declaration budget are errors.\n\n\
The command line is pinned Lean's, per release: the nearest `lean-toolchain` above the \
working directory (or `CLEAN_LEAN_VERSION`) picks Lean 4.8.0, 4.30.0-rc2 or 4.36.0; one that reads \
`clean`, as `clean lake new` and `clean lake init` write it, picks Clean's pin, as an absent \
`lean-toolchain` does; any other toolchain is refused by name. Honoured: FILE, `--stdin`, \
`--run FILE args…` (stable 4.36.0 reuses the environment that checked the file), `-D name=value` (G50's option table; \
`printMessageEndPos` is honoured here), `--json`, `-R/--root`, `-q`, `-E/--error=kind`, \
`--deps`, `--src-deps`, `--help`. Lean 4.30.0-rc2 and 4.36.0 also support `--deps-json`. `--version`, `-V` and `-g` report CLEAN's identity, never a \
Lean commit. In the Lean 4.36.0 dialect, `--print-prefix` and `--print-libdir` identify the selected SDK and `--features` reports optional compiler backends. The `-o` option writes Lean-format artifacts for checked axiom and \
theorem modules. Clean refuses source features that need native records it cannot yet write. \
Clean refuses `-i`, `-c`, `-b`, `--server`, `--worker`, \
`--plugin`, `--load-dynlib`, `--setup`, `-t`, `-M`, `-T`, `-j`, `-s`, `--profile`, and `--stats` \
by name and exits with status 1. \
`scripts/lean_front_door_diff.py` measures it byte for byte against pinned Lean.",
    category: Category::Dev,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean lean Main.lean",
            what: "elaborate Main.lean and print its messages exactly as `lean Main.lean` would",
        },
        Example {
            cmd: "clean lean --json -DautoImplicit=false Main.lean",
            what: "one JSON message per line, with an option set as Lake's `leanOptions` sets it",
        },
        Example {
            cmd: "clean lean --run Main.lean alpha beta",
            what: "elaborate Main.lean, then build and run its `main` with arguments",
        },
    ],
    see_also: &["check", "run"],
    references: &[
        Reference {
            kind: RefKind::Doc,
            label: "Decisions R74-R78",
            target: "docs/DECISIONS.md",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-cli",
            target: "clean-cli",
        },
    ],
    domain_root: Some("lean"),
    alternative_forms: &[],
    feature_gate: None,
}];

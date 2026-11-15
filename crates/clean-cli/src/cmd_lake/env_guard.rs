// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake env <cmd>` never hands a Lean toolchain program to whatever PATH
//! resolves (plan item `devsurface-lake-env-no-silent-lean`).
//!
//! `clean lake env lean F.lean` used to spawn the first `lean` on PATH: real
//! Lean through elan, or inside aterm a reroute to a stale Clean. Either way
//! the verdict it printed was not Clean's, and an agent reading it would
//! report "checked by Clean". The handoff refuses these programs by name
//! before anything is spawned, and each refusal names the Clean verb to use
//! instead. Two have a Clean counterpart under their own name: `lean` is
//! `clean lean` (decision R74's front door, which the `clean` binary also is
//! when invoked as `lean`), and `lake` is `clean lake`. Clean ships none of
//! the others. Clean installs no shim directory either, so nothing on the
//! child's PATH would reach Clean's `lean` by that name: answering `lake env
//! lean` with Clean's own front door is the item's open half, not this guard.
//!
//! The match is on the program's basename, wherever it lives, ASCII
//! case-insensitive (macOS resolves `LEAN` to a file named `lean`) and with an
//! `.exe` suffix ignored. Both `/` and `\` separate path components, so a
//! Windows-spelled path is caught too. A wrapper (`sh -c 'lean …'`, `env lean`,
//! `elan run …`) is not inspected: it names the program it runs explicitly.
//! Nor is a symlink or copy under another name: the guard keys on the name the
//! caller gave.
//!
//! The pinned toolchain's `bin/` also ships `leantar` (it packs and unpacks
//! `.ltar` build-cache archives and elaborates, checks and compiles nothing),
//! `cadical` (a SAT solver), and `clang`, `ld64.lld` and `llvm-ar` (the
//! bundled C toolchain). None of them runs Lean, so they are run as given.
//! The tests below classify every name in two recorded listings, the pinned
//! toolchain's `bin/` (v4.30.0-rc2) and elan 4.2.1's proxy directory; they
//! hold the first to the repository's `lean-toolchain`, and compare it with
//! that toolchain's installed `bin/` where it is installed.

/// A Lean toolchain program `clean lake env` refuses, and the Clean verb its
/// refusal names instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct LeanToolchainProgram {
    /// The basename, lower case, without an `.exe` suffix.
    pub(super) name: &'static str,
    /// What Clean has in the program's place, and the Clean verb to use
    /// instead.
    pub(super) instead: &'static str,
}

/// The programs in the pinned toolchain's `bin/` and in elan's proxy
/// directory that run Lean's frontend, kernel, compiler or package manager
/// (`lean`, `lake`, `leanchecker`, `leanc`, `leanir`, `leanmake`, `leanpkg`),
/// plus Lean's exporters (`leanexport`, `lean4export`). Each row says what
/// Clean has in that program's place: its own verb for `lean` and `lake`, and
/// for the rest that Clean ships none and the verb nearest to it.
pub(super) const LEAN_TOOLCHAIN_PROGRAMS: &[LeanToolchainProgram] = &[
    LeanToolchainProgram {
        name: "lean",
        instead: "Clean's own `lean` is `clean lean <FILE>`, with `lean`'s command line and exit \
                  rule; run it directly. It reads `LEAN_PATH` as `lean` does, and `clean lake \
                  env` with no command prints this workspace's.",
    },
    LeanToolchainProgram {
        name: "lake",
        instead: "Clean's own Lake is `clean lake <verb>`, for example `clean lake build`.",
    },
    LeanToolchainProgram {
        name: "leanchecker",
        instead: "Clean ships no `leanchecker`; use `clean olean replay <MODULE>` to re-check \
                  `.olean` files with Clean's kernel.",
    },
    LeanToolchainProgram {
        name: "leanexport",
        instead: "Clean ships no `leanexport` and writes no lean4export exports; `clean olean \
                  replay <MODULE>` re-checks the `.olean` files an export is made from, and \
                  `clean olean replay --from-export <FILE>` checks an export.",
    },
    LeanToolchainProgram {
        name: "lean4export",
        instead: "Clean ships no `lean4export` and writes no lean4export exports; `clean olean \
                  replay <MODULE>` re-checks the `.olean` files an export is made from, and \
                  `clean olean replay --from-export <FILE>` checks an export.",
    },
    LeanToolchainProgram {
        name: "leanc",
        instead: "Clean ships no `leanc`; use `clean run <FILE> --decl main` to compile, link and \
                  run a program with Clean.",
    },
    LeanToolchainProgram {
        name: "leanir",
        instead: "Clean ships no `leanir`; use `clean compile <FILE> --decl <NAME> --emit c` to \
                  emit C for a declaration with Clean, or `clean lake build` to build a \
                  package's modules.",
    },
    LeanToolchainProgram {
        name: "leanmake",
        instead: "Clean ships no `leanmake`; use `clean lake build`.",
    },
    LeanToolchainProgram {
        name: "leanpkg",
        instead: "Clean ships no `leanpkg`; use `clean lake <verb>`, for example `clean lake \
                  build`.",
    },
];

/// `clean lake env` was asked to run a Lean toolchain program.
#[derive(Debug, thiserror::Error)]
#[error(
    "clean lake env refuses to run `{given}`: `{}` is a Lean toolchain program, so it could \
     run real Lean or a stale reroute rather than Clean. {}",
    .program.name,
    .program.instead
)]
pub(super) struct LeanToolchainProgramRefused {
    /// The program as the caller spelled it.
    given: String,
    program: LeanToolchainProgram,
}

/// The Lean toolchain program `program` names, if it names one.
fn lean_toolchain_program(program: &str) -> Option<&'static LeanToolchainProgram> {
    let basename = program.rsplit(['/', '\\']).next().unwrap_or(program);
    let lower = basename.to_ascii_lowercase();
    let stem = lower.strip_suffix(".exe").unwrap_or(&lower);
    LEAN_TOOLCHAIN_PROGRAMS.iter().find(|p| p.name == stem)
}

/// Refuse `program` when it is a Lean toolchain program; called before
/// anything is spawned.
pub(super) fn refuse_lean_toolchain_program(
    program: &str,
) -> Result<(), LeanToolchainProgramRefused> {
    match lean_toolchain_program(program) {
        Some(found) => Err(LeanToolchainProgramRefused {
            given: program.to_string(),
            program: *found,
        }),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::{lean_toolchain_program, refuse_lean_toolchain_program, LEAN_TOOLCHAIN_PROGRAMS};

    #[test]
    fn test_lean_toolchain_program_matches_basename_case_and_exe_suffix() {
        for (spelling, name) in [
            ("lean", "lean"),
            ("LEAN", "lean"),
            ("Lean.exe", "lean"),
            ("/opt/elan/bin/lean", "lean"),
            ("./lake", "lake"),
            ("C:\\elan\\bin\\leanc.EXE", "leanc"),
            ("toolchain/bin/leanchecker", "leanchecker"),
            ("leanexport", "leanexport"),
            ("lean4export", "lean4export"),
            ("leanmake", "leanmake"),
            ("leanpkg", "leanpkg"),
            ("leanir", "leanir"),
            ("C:\\lean\\bin\\LEANIR.exe", "leanir"),
        ] {
            let found = lean_toolchain_program(spelling)
                .unwrap_or_else(|| panic!("`{spelling}` must be refused as `{name}`"));
            assert_eq!(found.name, name, "`{spelling}`");
        }
    }

    #[test]
    fn test_lean_toolchain_program_leaves_other_names_alone() {
        for spelling in [
            "lean4",
            "leaner",
            "clean",
            "elan",
            "sh",
            "/usr/bin/env",
            "lean.sh",
            "lean/",
            "",
        ] {
            assert_eq!(
                lean_toolchain_program(spelling),
                None,
                "`{spelling}` is not a Lean toolchain program"
            );
        }
    }

    /// The `lean` refusal names `clean lean`, the front door with `lean`'s
    /// command line (R74). It used to say Clean ships no `lean` and send the
    /// caller to `clean check`, a verdict that fails a file `lean` accepts
    /// (no declaration, an explicit `sorry`).
    #[test]
    fn test_refusal_names_the_program_and_the_clean_verb() {
        let err = refuse_lean_toolchain_program("/x/bin/LEAN").expect_err("lean is refused");
        assert_eq!(
            err.to_string(),
            "clean lake env refuses to run `/x/bin/LEAN`: `lean` is a Lean toolchain program, \
             so it could run real Lean or a stale reroute rather than Clean. Clean's own \
             `lean` is `clean lean <FILE>`, with `lean`'s command line and exit rule; run it \
             directly. It reads `LEAN_PATH` as `lean` does, and `clean lake env` with no \
             command prints this workspace's."
        );
        refuse_lean_toolchain_program("fake-tool").expect("an ordinary program is not refused");
    }

    /// A program Clean answers under its own name (`clean lean`, `clean
    /// lake`: a top-level verb of the clap tree the binary parses) is refused
    /// naming that verb, never as one Clean ships none of; every other row
    /// says Clean ships none. The shared refusal text used to say "Clean ships
    /// no `{name}` of its own yet" for all nine, `lean` and `lake` included.
    #[test]
    fn test_refusal_for_a_program_clean_has_a_verb_for_names_that_verb() {
        let command = <crate::cli_args::Cli as clap::CommandFactory>::command();
        let mut own = Vec::new();
        for program in LEAN_TOOLCHAIN_PROGRAMS {
            let message = refuse_lean_toolchain_program(program.name)
                .expect_err("a listed program is refused")
                .to_string();
            let ships_none = format!("Clean ships no `{}`", program.name);
            if command.find_subcommand(program.name).is_some() {
                own.push(program.name);
                assert!(
                    message.contains(&format!("`clean {} ", program.name)),
                    "`clean {}` exists, so its refusal must name it: {message}",
                    program.name
                );
                assert!(
                    !message.contains(&ships_none) && !message.contains("of its own yet"),
                    "`clean {}` exists, so its refusal must not say Clean has none: {message}",
                    program.name
                );
            } else {
                assert!(message.contains(&ships_none), "{message}");
            }
        }
        assert_eq!(own, ["lean", "lake"], "the programs Clean has a verb for");
    }

    /// A sample argument for each placeholder a refusal writes.
    fn sample_argument(placeholder: &str) -> &'static str {
        match placeholder {
            "<FILE>" => "Main.lean",
            "<MODULE>" => "Init",
            "<NAME>" => "main",
            "<verb>" => "build",
            other => panic!("a refusal writes the placeholder `{other}`: give it a sample here"),
        }
    }

    /// Every `clean …` command a refusal quotes parses with the clap tree the
    /// binary parses, its flags and their values included, so no refusal
    /// sends the caller to a verb or flag Clean does not have.
    #[test]
    fn test_every_clean_command_a_refusal_names_parses() {
        use clap::Parser;
        for program in LEAN_TOOLCHAIN_PROGRAMS {
            let mut quoted = 0;
            for span in program.instead.split('`').skip(1).step_by(2) {
                let Some(rest) = span.strip_prefix("clean ") else {
                    continue;
                };
                let argv: Vec<&str> = std::iter::once("clean")
                    .chain(rest.split_whitespace().map(|word| {
                        if word.starts_with('<') {
                            sample_argument(word)
                        } else {
                            word
                        }
                    }))
                    .collect();
                match crate::cli_args::Cli::try_parse_from(argv.iter().copied()) {
                    Ok(_) => {}
                    // `--help` and `--version` end the parse by printing, which
                    // clap reports as an error of these kinds.
                    Err(err)
                        if matches!(
                            err.kind(),
                            clap::error::ErrorKind::DisplayHelp
                                | clap::error::ErrorKind::DisplayVersion
                        ) => {}
                    Err(err) => panic!(
                        "the `{}` refusal names `{span}`, which `clean` does not parse as \
                         {argv:?}: {err}",
                        program.name
                    ),
                }
                quoted += 1;
            }
            assert!(
                quoted > 0,
                "the `{}` refusal quotes no `clean …` command",
                program.name
            );
        }
    }

    /// The toolchain whose `bin/` [`PINNED_TOOLCHAIN_BIN`] records: the
    /// repository's `lean-toolchain` when the listing was taken.
    const LISTED_TOOLCHAIN: &str = "leanprover/lean4:v4.30.0-rc2";

    /// What `ls` printed for [`LISTED_TOOLCHAIN`]'s `bin/` on 2026-10-25 on
    /// Apple-silicon macOS (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin`;
    /// v4.32.1 and v4.33.1 list the same eleven names). It is macOS's listing:
    /// `ld64.lld` is the Mach-O linker. A recorded copy, not a read of the
    /// directory: [`test_recorded_toolchain_listing_is_the_pin`] holds it to
    /// the pin everywhere, and on macOS, where the toolchain is installed,
    /// `test_recorded_toolchain_listing_is_its_installed_bin` holds it to the
    /// directory.
    const PINNED_TOOLCHAIN_BIN: &[&str] = &[
        "cadical",
        "clang",
        "lake",
        "ld64.lld",
        "lean",
        "leanc",
        "leanchecker",
        "leanir",
        "leanmake",
        "leantar",
        "llvm-ar",
    ];

    /// What `ls` printed for elan 4.2.1's proxy directory (`~/.elan/bin`) on
    /// 2026-10-25. A recorded copy, compared with no directory: the proxies a
    /// box has depend on the elan it runs.
    const ELAN_PROXY_DIR: &[&str] = &[
        "elan",
        "lake",
        "lean",
        "leanc",
        "leanchecker",
        "leanmake",
        "leanpkg",
    ];

    /// The programs in those two listings that `clean lake env` runs as given,
    /// each with the reason it is not a Lean toolchain program.
    const RUN_AS_GIVEN: &[(&str, &str)] = &[
        ("cadical", "a SAT solver; it runs no Lean"),
        ("clang", "the bundled C compiler; it runs no Lean"),
        ("ld64.lld", "the bundled linker; it runs no Lean"),
        ("llvm-ar", "the bundled archiver; it runs no Lean"),
        (
            "leantar",
            "packs and unpacks `.ltar` build-cache archives; it elaborates, checks and \
             compiles nothing and prints no verdict",
        ),
        (
            "elan",
            "the toolchain manager; `elan run <toolchain> <program>` names its toolchain \
             explicitly, like any other wrapper",
        ),
    ];

    /// Every name in the two recorded listings is refused or run as given
    /// with a reason. This reads the recorded copies, not the directories:
    /// the next test ties the first copy to the pin and to its installed
    /// `bin/`.
    #[test]
    fn test_recorded_listings_every_name_is_refused_or_run_as_given() {
        for name in PINNED_TOOLCHAIN_BIN.iter().chain(ELAN_PROXY_DIR) {
            let run_as_given = RUN_AS_GIVEN.iter().any(|(kept, _)| kept == name);
            match lean_toolchain_program(name) {
                Some(found) => {
                    assert!(
                        !run_as_given,
                        "`{name}` is both refused and listed as run as given"
                    );
                    assert_eq!(found.name, *name);
                }
                None => assert!(
                    run_as_given,
                    "`{name}` ships in a Lean toolchain or elan's proxy directory: refuse it \
                     or list it in RUN_AS_GIVEN with the reason it runs no Lean"
                ),
            }
        }
        for (name, reason) in RUN_AS_GIVEN {
            assert_eq!(
                lean_toolchain_program(name),
                None,
                "`{name}` is run as given: {reason}"
            );
            assert!(
                PINNED_TOOLCHAIN_BIN.contains(name) || ELAN_PROXY_DIR.contains(name),
                "`{name}` in RUN_AS_GIVEN must come from a listing"
            );
        }
    }

    /// The repository's `lean-toolchain` is the toolchain the listing was
    /// taken from, so a pin bump fails here until the listing is taken
    /// again.
    #[test]
    fn test_recorded_toolchain_listing_is_the_pin() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let pin = std::fs::read_to_string(root.join("lean-toolchain"))
            .expect("repository lean-toolchain");
        assert_eq!(
            pin.trim(),
            LISTED_TOOLCHAIN,
            "the pin moved: list the new toolchain's `bin/`, classify every new name in \
             LEAN_TOOLCHAIN_PROGRAMS or RUN_AS_GIVEN, then move LISTED_TOOLCHAIN"
        );
    }

    /// Where the pinned toolchain is installed, its `bin/` holds exactly the
    /// recorded names. The recorded listing was once checked against nothing,
    /// so a release whose `bin/` gained a Lean program passed while
    /// `clean lake env <new>` ran it. The listing is macOS's, so this test
    /// exists only there rather than passing vacuously elsewhere.
    #[cfg(target_os = "macos")]
    #[test]
    fn test_recorded_toolchain_listing_is_its_installed_bin() {
        let mut recorded = PINNED_TOOLCHAIN_BIN.to_vec();
        recorded.sort_unstable();
        match clean_olean::installed_lean_lib_path(LISTED_TOOLCHAIN) {
            Some(lib) => {
                let bin = lib
                    .parent()
                    .and_then(std::path::Path::parent)
                    .map(|toolchain| toolchain.join("bin"))
                    .unwrap_or_else(|| panic!("no toolchain directory above {}", lib.display()));
                let mut installed: Vec<String> = std::fs::read_dir(&bin)
                    .unwrap_or_else(|err| panic!("read {}: {err}", bin.display()))
                    .map(|entry| {
                        entry
                            .expect("a directory entry")
                            .file_name()
                            .into_string()
                            .expect("a UTF-8 program name")
                    })
                    .filter(|name| !name.starts_with('.'))
                    .collect();
                installed.sort_unstable();
                assert_eq!(
                    installed,
                    recorded,
                    "{} holds other programs than the recorded listing: classify each new name \
                     and record it",
                    bin.display()
                );
            }
            None => eprintln!(
                "note: {LISTED_TOOLCHAIN} is not installed here, so the recorded listing is held \
                 to the pin only"
            ),
        }
    }

    #[test]
    fn test_leanir_refusal_names_clean_compile() {
        let err = refuse_lean_toolchain_program("leanir").expect_err("leanir is refused");
        assert_eq!(
            err.to_string(),
            "clean lake env refuses to run `leanir`: `leanir` is a Lean toolchain program, so it \
             could run real Lean or a stale reroute rather than Clean. Clean ships no `leanir`; \
             use `clean compile <FILE> --decl <NAME> --emit c` to emit C for a declaration with \
             Clean, or `clean lake build` to build a package's modules."
        );
    }

    #[test]
    fn test_every_refusal_names_a_clean_verb() {
        for program in LEAN_TOOLCHAIN_PROGRAMS {
            assert!(
                program.instead.contains("`clean "),
                "the `{}` refusal must name a Clean verb: {}",
                program.name,
                program.instead
            );
            assert_eq!(program.name, program.name.to_ascii_lowercase());
        }
    }
}

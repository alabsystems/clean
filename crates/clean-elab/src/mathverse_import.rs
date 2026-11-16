// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `import Mathverse.<Corpus>[.<Constant>]` — Mathverse library content as
//! ordinary, ambient, kernel-checked declarations.
//!
//! # What this buys
//!
//! Before this, Mathverse content could only be reached through the
//! `mathverse_apply <name>` TACTIC, whose argument is a bare identifier
//! precisely because the constant is *not* in the environment — the tactic is
//! what loads it. So `mathverse_apply eq_or_ne` worked and `exact eq_or_ne x y`
//! did not, and neither did anything else that goes through ordinary name
//! resolution.
//!
//! An `import Mathverse.…` declaration installs the named constant and its full
//! transitive closure into the file's environment *before* any `ElabCtx` is
//! built for a later declaration. From that point the constant is resident, so
//! the elaborator's unmodified resolution path finds it and the name is usable
//! as a TERM. No hook was added to name resolution, and no cost was added to
//! the happy path: nothing in `elab_ident` changed.
//!
//! # Why the load must happen here
//!
//! `ElabCtx` holds `env: &'a Environment` — an IMMUTABLE borrow for its whole
//! lifetime (`infer/mod.rs`). Nothing inside term elaboration can install a
//! constant. `elaborate_decl_and_register_leaf` (`lib.rs`) owns
//! `&mut Environment` and does not construct the `ElabCtx` until later, so the
//! `SurfaceDecl::Import` arm is the natural, and nearly the only, place.
//!
//! # The gate
//!
//! Every constant enters through [`mathverse_load_named`], which is the loading
//! half of `mathverse_apply_named` with the goal-directed tail removed — the
//! same `synthesize_named_candidate` + `load_candidate_closure` pair. That
//! carries the whole existing chain unchanged: fabricated-stub discharge with
//! its fail-closed re-check, checked inductive-family replay,
//! `validate_dependency_loader_trust` (kind discriminator,
//! `validate_resident_type_agreement`, foundational-axiom restriction,
//! `accepts_dependency` over the FULL transitive closure), and checked
//! `Environment::add_decl`. There is no second loader and no weaker path.
//!
//! # Surface
//!
//! ```text
//! import Mathverse                             -- install the library, load nothing
//! import Mathverse.Mathlib                     -- install, note the corpus, load nothing
//! import Mathverse.Mathlib.eq_or_ne            -- load `eq_or_ne` from the Lean4 corpus
//! import Mathverse.Isabelle.Pure.prop_def      -- load `Pure.prop_def` from Isabelle
//! import Mathverse.Mathlib.eq_or_ne, Mathverse.Isabelle.Pure.prop_def
//! ```
//!
//! `set_option mathverse.trust "relaxed-foundational"` widens the gate from the
//! default `Strict`; `set_option mathverse.dir "<path>"` (or the
//! `CLEAN_MATHVERSE_DIR` environment variable) says where the shards live.
//!
//! Unlike the `.olean` lane, which warns and continues when a module resolves
//! to nothing, an armed-but-unsatisfiable `import Mathverse.…` is a LOUD error.
//! Reporting it quietly would present later as a bare `Unknown identifier`,
//! hiding a trust refusal behind a name-resolution message.

use crate::error::ElabError;
use clean_kernel::name::{Name, NameInner};
use clean_parser::SurfaceName;

/// Reserved first segment that routes an `import` at the Mathverse library
/// instead of the `.olean` search path.
pub(crate) const MATHVERSE_IMPORT_ROOT: &str = "Mathverse";

/// Option naming the shard directory, consulted only when no library has
/// already been installed on this thread.
#[cfg(feature = "mathverse-library")]
pub(crate) const MATHVERSE_DIR_OPTION: &str = "mathverse.dir";

/// Environment variable naming the shard directory. Mirrors the constant
/// `clean-server` already uses for premise search.
#[cfg(feature = "mathverse-library")]
pub(crate) const MATHVERSE_DIR_ENV: &str = "CLEAN_MATHVERSE_DIR";

/// Option selecting the trust gate. Default is `Strict`.
#[cfg(feature = "mathverse-library")]
pub(crate) const MATHVERSE_TRUST_OPTION: &str = "mathverse.trust";

/// Does this import path address the Mathverse library rather than a `.olean`
/// module?
///
/// Cheap and total: one walk to the root segment and one string comparison,
/// no allocation. Every ordinary import answers `false` here and is
/// dispatched exactly as before.
pub(crate) fn is_mathverse_path(path: &SurfaceName) -> bool {
    root_segment(path.name()) == Some(MATHVERSE_IMPORT_ROOT)
}

/// The outermost component of `name` when it is a string component.
fn root_segment(name: &Name) -> Option<&str> {
    let mut current = name;
    let mut root = None;
    loop {
        match current.inner() {
            NameInner::Anon => return root,
            NameInner::Str(parent, text) => {
                root = Some(&**text);
                current = parent;
            }
            NameInner::Num(parent, _) => {
                root = None;
                current = parent;
            }
        }
    }
}

/// The components of `name`, outermost first, each in its plain spelling.
#[cfg(any(feature = "mathverse-library", test))]
fn segments(name: &Name) -> Vec<String> {
    let mut out = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, text) => {
                out.push(text.to_string());
                current = parent;
            }
            NameInner::Num(parent, number) => {
                out.push(number.to_string());
                current = parent;
            }
        }
    }
    out.reverse();
    out
}

/// Split `Mathverse.<Corpus>.<A>.<B>` into the corpus tag and the dotted
/// constant name, if any.
///
/// Returns `(corpus_tag, Some(constant))`, `(corpus_tag, None)` for a bare
/// `import Mathverse.<Corpus>`, or `(None, None)` for a bare
/// `import Mathverse`.
#[cfg(any(feature = "mathverse-library", test))]
fn split_path(path: &SurfaceName) -> (Option<String>, Option<String>) {
    match segments(path.name()).as_slice() {
        [] | [_] => (None, None),
        [_, corpus] => (Some(corpus.clone()), None),
        [_, corpus, constant @ ..] => (Some(corpus.clone()), Some(constant.join("."))),
    }
}

#[cfg(feature = "mathverse-library")]
mod enabled {
    use super::{
        split_path, ElabError, SurfaceName, MATHVERSE_DIR_ENV, MATHVERSE_DIR_OPTION,
        MATHVERSE_TRUST_OPTION,
    };
    use crate::tactic::mathverse_use::{
        mathverse_constant_source_system, mathverse_library_installed, mathverse_load_named,
        set_mathverse_library, TrustGate,
    };
    use clean_mathverse::types::SourceSystem;

    /// Map a corpus tag written in an import path to the `SourceSystem` a
    /// loaded constant must actually carry.
    ///
    /// `Any` disables the check. An unrecognised tag is an error rather than a
    /// silent pass: a typo'd corpus would otherwise look like a working import
    /// that quietly checks nothing.
    fn corpus_source_system(tag: &str) -> Result<Option<SourceSystem>, ElabError> {
        match tag {
            "Mathlib" | "Lean4" | "Lean" => Ok(Some(SourceSystem::Lean4)),
            "Isabelle" | "HOL" => Ok(Some(SourceSystem::Isabelle)),
            "Coq" | "Rocq" => Ok(Some(SourceSystem::Coq)),
            "Metamath" => Ok(Some(SourceSystem::Metamath)),
            "Any" | "All" => Ok(None),
            other => Err(ElabError::MathverseImportFailed {
                name: format!("Mathverse.{other}"),
                detail: format!(
                    "unknown Mathverse corpus `{other}`; expected one of Mathlib, Lean4, \
                     Isabelle, Coq, Metamath, Any"
                ),
            }),
        }
    }

    /// Resolve the active trust gate from `set_option mathverse.trust "…"`.
    ///
    /// Default is `Strict` — the same gate `mathverse_apply` uses — so an
    /// import that says nothing about trust gets the strongest one. Widening it
    /// requires the user to write the option, which is the point.
    fn trust_gate_from_env(env: &clean_kernel::Environment) -> Result<TrustGate, ElabError> {
        let Some(Some(raw)) = env.get_option(MATHVERSE_TRUST_OPTION) else {
            return Ok(TrustGate::Strict);
        };
        match raw.trim().trim_matches('"') {
            "strict" | "Strict" => Ok(TrustGate::Strict),
            // `Relaxed` is DELIBERATELY NOT REACHABLE from source.
            //
            // It skips three checks that are guarded by
            // `matches!(trust_gate, Strict | RelaxedFoundational)`: the
            // shadowed-by-unchecked rule (whose own comment calls the thing it
            // stops "the exact failure this gate exists to prevent"), the KIND
            // discriminator (under `Relaxed` an axiom stub CAN pose as the
            // shard's inductive), and `validate_resident_type_agreement` (the
            // check that caught a citation resting on Clean's `Nat.succ_add`
            // while reporting Init's). It also drops `accepts_dependency` to
            // `KernelVerified || SourceVerified`.
            //
            // Before the import surface existed, `TrustGate::Relaxed` had NO
            // user-reachable surface anywhere in the workspace — `mathverse_apply`
            // is hardcoded to `Strict`. Exposing it here would have let one line
            // of ordinary Lean source turn those checks off, which is a bigger
            // hole than the feature is worth. Demonstrated: with the option set,
            // a deliberately type-substituted resident installs cleanly.
            //
            // `relaxed-foundational` remains available: it keeps all three
            // checks and only widens which AXIOMS may appear in the closure.
            "relaxed" | "Relaxed" => Err(ElabError::MathverseImportFailed {
                name: MATHVERSE_TRUST_OPTION.to_string(),
                detail: "trust gate `relaxed` is not available from source: it \
                         disables the resident type-agreement, kind and \
                         shadowed-by-unchecked checks. Use \"strict\" (the \
                         default) or \"relaxed-foundational\"."
                    .to_string(),
            }),
            "relaxed-foundational" | "foundational" | "RelaxedFoundational" => {
                Ok(TrustGate::RelaxedFoundational)
            }
            other => Err(ElabError::MathverseImportFailed {
                name: MATHVERSE_TRUST_OPTION.to_string(),
                detail: format!(
                    "unknown trust gate `{other}`; expected \"strict\", \"relaxed\" or \
                     \"relaxed-foundational\""
                ),
            }),
        }
    }

    /// Install a library from the configured shard directory if one is not
    /// already installed on this thread.
    ///
    /// A caller that has already called `set_mathverse_library` (a test, an
    /// embedder, a server that loaded shards at startup) keeps its library —
    /// re-loading would discard a deliberately-constructed one.
    fn ensure_library(env: &clean_kernel::Environment) -> Result<(), ElabError> {
        if mathverse_library_installed() {
            return Ok(());
        }
        let dir = match env.get_option(MATHVERSE_DIR_OPTION) {
            Some(Some(raw)) => raw.trim().trim_matches('"').to_string(),
            _ => {
                std::env::var(MATHVERSE_DIR_ENV).map_err(|_| ElabError::MathverseImportFailed {
                    name: "Mathverse".to_string(),
                    detail: format!(
                        "no Mathverse Library is installed and no shard directory is configured; \
                     set `{MATHVERSE_DIR_ENV}` or write `set_option {MATHVERSE_DIR_OPTION} \
                     \"<dir>\"` before the import"
                    ),
                })?
            }
        };
        // `load_built_library`, NOT `MathverseProvider::from_dir`: only the
        // former applies `kernel-verified.json`, which is what mints the
        // `KernelVerified` confidences `TrustGate::Strict` requires. Loading
        // through the provider would leave every header `SourceVerified` and
        // Strict would then admit nothing, presenting a trust configuration
        // mistake as "constant not found".
        let library =
            clean_mathverse::build_library::load_built_library(std::path::Path::new(dir.as_str()))
                .map_err(|e| ElabError::MathverseImportFailed {
                    name: "Mathverse".to_string(),
                    detail: format!("failed to load Mathverse shards from `{dir}`: {e}"),
                })?;
        set_mathverse_library(library);
        Ok(())
    }

    /// Install ONE library constant through the trust gate.
    ///
    /// THE single loader entry point for library content reached from source.
    /// Both surfaces call exactly this function:
    ///
    /// - eager `import Mathverse.<Corpus>.<Constant>` — [`process_mathverse_imports`]
    /// - lazy resolution after `import Mathverse.<Corpus>` — [`lazy_load_armed`]
    ///
    /// `expected` is the set of `SourceSystem`s the constant may come from; an
    /// EMPTY slice disables the provenance check (`Mathverse.Any`). The gate
    /// itself — `synthesize_named_candidate` + `load_candidate_closure`, with
    /// the kind discriminator, fabricated-stub discharge,
    /// `validate_resident_type_agreement`, the foundational-axiom restriction
    /// and `accepts_dependency` over the full transitive closure — is
    /// `mathverse_load_named`, untouched.
    pub(crate) fn load_gated_constant(
        env: &mut clean_kernel::Environment,
        name: &str,
        expected: &[SourceSystem],
        gate: TrustGate,
        surface: &str,
    ) -> Result<(), ElabError> {
        // Provenance check BEFORE the load: `import Mathverse.Isabelle.X` must
        // not quietly hand back a Lean4-sourced `X`. Done here so the mismatch
        // is reported as itself instead of as a later surprise.
        //
        // This matters more for lazy resolution than for the eager path: the
        // library's name index is global and last-writer-wins, so 41 names on
        // the shipped corpus (`List.append_assoc`, `Nat.le_trans`, …) resolve
        // to Isabelle even though a Lean4 declaration of the same name exists.
        // An `import Mathverse.Mathlib`-armed file must be told that, not
        // silently handed the Isabelle one.
        if !expected.is_empty() {
            match mathverse_constant_source_system(name) {
                Some(got) if expected.contains(&got) => {}
                Some(got) => {
                    let want = expected
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" or ");
                    return Err(ElabError::MathverseImportFailed {
                        name: name.to_string(),
                        detail: format!(
                            "requested from the {want} corpus but the installed library's \
                             `{name}` is from {got}"
                        ),
                    });
                }
                None => {
                    return Err(ElabError::MathverseImportFailed {
                        name: name.to_string(),
                        detail: format!(
                            "`{name}` is not in the installed Mathverse Library (or is hidden \
                             by the library's trust policy)"
                        ),
                    });
                }
            }
        }

        // THE GATE. Same candidate synthesis, same closure loader, same trust
        // chain as `mathverse_apply`.
        mathverse_load_named(env, name, gate, surface).map_err(|e| {
            ElabError::MathverseImportFailed {
                name: name.to_string(),
                detail: format!("{e}"),
            }
        })?;

        // Fail closed on a silent no-op. The loader only registers names it
        // finds absent; if for any reason the requested constant did not end
        // up resident, later declarations would report a bare
        // `Unknown identifier` and the trust story would be invisible.
        //
        // Lazy resolution additionally depends on this as its PROGRESS proof:
        // a granted request ends with the name resident, so the same name can
        // never be requested twice and the retry loop cannot spin.
        let kname = clean_kernel::name::Name::from_string(name);
        if env.get_const(&kname).is_none() && env.get_inductive(&kname).is_none() {
            return Err(ElabError::MathverseImportFailed {
                name: name.to_string(),
                detail: format!(
                    "the gated loader reported success but `{name}` is not resident in the \
                     environment"
                ),
            });
        }
        Ok(())
    }

    /// Honour a lazy [`ElabError::MathverseNameAvailable`] request from the
    /// decl driver.
    ///
    /// Reads the armed corpus list written by the corpus-level import arm and
    /// hands the name to the same [`load_gated_constant`] the eager path uses.
    /// A disarmed environment cannot get here (nothing mints the request), but
    /// it is checked anyway so the gate can never be reached without an
    /// explicit corpus-level import in the file.
    pub(crate) fn lazy_load_armed(
        env: &mut clean_kernel::Environment,
        name: &str,
    ) -> Result<(), ElabError> {
        let Some(tags) = crate::mathverse_lazy::armed_tags(
            env.get_option(crate::mathverse_lazy::MATHVERSE_ARMED_OPTION),
        ) else {
            return Err(ElabError::MathverseImportFailed {
                name: name.to_string(),
                detail: "no Mathverse corpus is armed in this file; write \
                         `import Mathverse.<Corpus>` before citing library names"
                    .to_string(),
            });
        };

        // An `Any`/`All` tag anywhere disables the provenance check, exactly as
        // `import Mathverse.Any.<name>` does on the eager path.
        let mut expected = Vec::with_capacity(tags.len());
        for tag in &tags {
            match corpus_source_system(tag)? {
                Some(system) => expected.push(system),
                None => {
                    expected.clear();
                    break;
                }
            }
        }

        let gate = trust_gate_from_env(env)?;
        load_gated_constant(env, name, &expected, gate, "import Mathverse (lazy)")
    }

    /// Handle every `Mathverse`-rooted path in one `import` declaration.
    pub(crate) fn process_mathverse_imports(
        env: &mut clean_kernel::Environment,
        paths: &[SurfaceName],
    ) -> Result<(), ElabError> {
        ensure_library(env)?;
        let gate = trust_gate_from_env(env)?;

        for path in paths {
            let (corpus, constant) = split_path(path);
            let expected = match corpus.as_deref() {
                Some(tag) => corpus_source_system(tag)?,
                None => None,
            };
            let Some(name) = constant else {
                // `import Mathverse` / `import Mathverse.Mathlib` — install the
                // library, name no constants, and ARM the corpus so any name in
                // it resolves on demand from here on (`mathverse_lazy`).
                //
                // Arming is an environment option, not the thread-local
                // library flag: it must travel with the file that asked for it,
                // so a file that never wrote `import Mathverse.…` keeps the
                // old `Unknown identifier` behaviour byte for byte even when an
                // embedder installed a library on this thread.
                let tag = corpus.as_deref().unwrap_or("Any");
                let armed = crate::mathverse_lazy::arm_tag(
                    env.get_option(crate::mathverse_lazy::MATHVERSE_ARMED_OPTION),
                    tag,
                );
                env.set_option(
                    crate::mathverse_lazy::MATHVERSE_ARMED_OPTION.to_string(),
                    Some(armed),
                );
                continue;
            };

            let expected = expected.map(|s| [s]);
            let expected: &[SourceSystem] = expected.as_ref().map_or(&[], |s| s.as_slice());
            load_gated_constant(env, &name, expected, gate, "import Mathverse")?;
        }
        Ok(())
    }
}

#[cfg(feature = "mathverse-library")]
pub(crate) use enabled::{lazy_load_armed, process_mathverse_imports};

/// Without the `mathverse-library` feature nothing can mint a lazy request
/// (`mathverse_lazy::library_offers` is a constant `false`), so this is
/// unreachable — but it must still say the same thing the eager path says.
#[cfg(not(feature = "mathverse-library"))]
pub(crate) fn lazy_load_armed(
    _env: &mut clean_kernel::Environment,
    name: &str,
) -> Result<(), ElabError> {
    Err(ElabError::MathverseImportFailed {
        name: name.to_string(),
        detail: "this build of Clean was compiled without the `mathverse-library` feature, so \
                 there is no Mathverse Library to import from"
            .to_string(),
    })
}

/// Without the `mathverse-library` feature there is no library to import from.
/// Say so, loudly — silently no-opping would leave every later use of a library
/// name reporting a bare `Unknown identifier`.
#[cfg(not(feature = "mathverse-library"))]
pub(crate) fn process_mathverse_imports(
    _env: &mut clean_kernel::Environment,
    paths: &[SurfaceName],
) -> Result<(), ElabError> {
    let named = paths
        .iter()
        .map(|p| p.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Err(ElabError::MathverseImportFailed {
        name: named,
        detail: "this build of Clean was compiled without the `mathverse-library` feature, so \
                 there is no Mathverse Library to import from"
            .to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::{is_mathverse_path, split_path};
    use clean_kernel::name::Name;
    use clean_parser::SurfaceName;

    fn path(dotted: &str) -> SurfaceName {
        SurfaceName::from_name(Name::from_string(dotted))
    }

    #[test]
    fn test_is_mathverse_path_only_matches_the_reserved_root() {
        assert!(is_mathverse_path(&path("Mathverse")));
        assert!(is_mathverse_path(&path("Mathverse.Mathlib")));
        // Ordinary imports must be untouched.
        assert!(!is_mathverse_path(&path("Mathlib.Logic.Basic")));
        assert!(!is_mathverse_path(&path("Init")));
        assert!(!is_mathverse_path(&SurfaceName::default()));
        // Not a prefix match: a real module could be called `MathverseFoo`.
        assert!(!is_mathverse_path(&path("MathverseFoo")));
        // Only the ROOT segment counts: `Foo.Mathverse` is an ordinary module.
        assert!(!is_mathverse_path(&path("Foo.Mathverse")));
    }

    #[test]
    fn test_split_path_separates_corpus_from_dotted_constant() {
        assert_eq!(split_path(&path("Mathverse")), (None, None));
        assert_eq!(
            split_path(&path("Mathverse.Mathlib")),
            (Some("Mathlib".to_string()), None)
        );
        assert_eq!(
            split_path(&path("Mathverse.Mathlib.eq_or_ne")),
            (Some("Mathlib".to_string()), Some("eq_or_ne".to_string()))
        );
        // A dotted constant name is rejoined, not truncated.
        assert_eq!(
            split_path(&path("Mathverse.Isabelle.Pure.prop_def")),
            (
                Some("Isabelle".to_string()),
                Some("Pure.prop_def".to_string())
            )
        );
    }
}

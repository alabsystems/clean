// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wire Coq translator output to the clean kernel [`Environment`].
//!
//! The [`verify_declarations`] function takes collected
//! [`TranslatedGlobalDecl`] values (from [`CoqBatchImporter::take_declarations`])
//! and feeds them to [`Environment::add_decl`] / [`Environment::add_inductive`],
//! tracking success/failure counts.

use crate::env::Environment;
use crate::name::Name;

use super::translate::TranslatedGlobalDecl;

/// Aggregate result of verifying translated Coq declarations against the kernel.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct VerifyStats {
    /// Declarations successfully added to the environment.
    pub verified: usize,
    /// Declarations that failed type-checking or registration.
    pub failed: usize,
}

/// Outcome of [`verify_declarations`]: the populated environment and stats.
#[derive(Debug)]
pub struct VerifyResult {
    /// The environment with all successfully added declarations.
    pub env: Environment,
    /// Verification statistics.
    pub stats: VerifyStats,
    /// Names of declarations that failed, paired with an error description.
    pub errors: Vec<(String, String)>,
}

/// Extract a human-readable name from a [`TranslatedGlobalDecl`].
fn decl_display_name(decl: &TranslatedGlobalDecl) -> String {
    match decl {
        TranslatedGlobalDecl::Constant(d) => {
            let name: &Name = match d {
                crate::Declaration::Definition { name, .. }
                | crate::Declaration::Axiom { name, .. }
                | crate::Declaration::Theorem { name, .. }
                | crate::Declaration::Opaque { name, .. } => name,
            };
            name.to_string()
        }
        TranslatedGlobalDecl::Inductive(ind) => {
            if let Some(first) = ind.types.first() {
                first.name.to_string()
            } else {
                "<empty inductive>".to_string()
            }
        }
    }
}

/// Verify a batch of translated Coq declarations by adding them to a fresh
/// Clean kernel [`Environment`].
///
/// For each [`TranslatedGlobalDecl::Constant`], calls [`Environment::add_decl`].
/// For each [`TranslatedGlobalDecl::Inductive`], calls [`Environment::add_inductive`].
///
/// Failures are logged (name + error) but do not abort processing of the
/// remaining declarations.
///
/// # Example
///
/// ```text
/// let mut importer = CoqBatchImporter::new();
/// importer.import_stdlib_types();
/// importer.import_sources_collecting(sources);
/// let decls = importer.take_declarations();
/// let result = verify_declarations(decls);
/// println!("verified {} / failed {}", result.stats.verified, result.stats.failed);
/// ```
pub fn verify_declarations(decls: Vec<TranslatedGlobalDecl>) -> VerifyResult {
    let mut env = Environment::new();
    verify_declarations_into(&mut env, decls)
}

/// Like [`verify_declarations`] but adds declarations into an existing
/// environment rather than creating a new one.
///
/// This is useful when the caller needs a pre-configured environment (e.g.,
/// one initialized with `Environment::with_prelude()`).
pub fn verify_declarations_into(
    env: &mut Environment,
    decls: Vec<TranslatedGlobalDecl>,
) -> VerifyResult {
    let mut stats = VerifyStats::default();
    let mut errors: Vec<(String, String)> = Vec::new();

    for decl in &decls {
        let name = decl_display_name(decl);
        match decl {
            TranslatedGlobalDecl::Constant(d) => match env.add_decl(d.clone()) {
                Ok(()) => stats.verified += 1,
                Err(e) => {
                    stats.failed += 1;
                    errors.push((name, e.to_string()));
                }
            },
            TranslatedGlobalDecl::Inductive(ind) => match env.add_inductive(ind.clone()) {
                Ok(()) => stats.verified += 1,
                Err(e) => {
                    stats.failed += 1;
                    errors.push((name, e.to_string()));
                }
            },
        }
    }

    // Take ownership of the env by swapping with a default.
    let final_env = std::mem::take(env);

    VerifyResult {
        env: final_env,
        stats,
        errors,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq_import::translate::TranslatedGlobalDecl;
    use crate::expr::Expr;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::name::Name;
    use crate::Declaration;

    #[test]
    fn verify_empty_vec_returns_zero_stats() {
        let result = verify_declarations(vec![]);
        assert_eq!(result.stats, VerifyStats::default());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn verify_single_axiom_succeeds() {
        let decl = TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string("coq_test_axiom"),
            level_params: vec![],
            type_: Expr::prop(),
        });
        let result = verify_declarations(vec![decl]);
        assert_eq!(result.stats.verified, 1);
        assert_eq!(result.stats.failed, 0);
        assert!(result
            .env
            .get_const(&Name::from_string("coq_test_axiom"))
            .is_some());
    }

    #[test]
    fn verify_duplicate_name_fails_gracefully() {
        let d1 = TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string("dup"),
            level_params: vec![],
            type_: Expr::prop(),
        });
        let d2 = d1.clone();
        let result = verify_declarations(vec![d1, d2]);
        assert_eq!(result.stats.verified, 1);
        assert_eq!(result.stats.failed, 1);
        assert_eq!(result.errors.len(), 1);
        assert!(result.errors[0].1.contains("Duplicate"));
    }

    #[test]
    fn verify_inductive_succeeds() {
        let ind = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("CoqUnit"),
                type_: Expr::sort(crate::level::Level::succ(crate::level::Level::zero())),
                constructors: vec![Constructor {
                    name: Name::from_string("CoqUnit.star"),
                    type_: Expr::const_(Name::from_string("CoqUnit"), vec![]),
                }],
            }],
        };
        let decl = TranslatedGlobalDecl::Inductive(ind);
        let result = verify_declarations(vec![decl]);
        assert_eq!(result.stats.verified, 1);
        assert_eq!(result.stats.failed, 0);
        assert!(result
            .env
            .get_inductive(&Name::from_string("CoqUnit"))
            .is_some());
    }

    #[test]
    fn verify_mixed_constants_and_inductives() {
        let axiom = TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string("coq_mix_axiom"),
            level_params: vec![],
            type_: Expr::prop(),
        });
        let ind = TranslatedGlobalDecl::Inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("CoqEmpty"),
                type_: Expr::sort(crate::level::Level::succ(crate::level::Level::zero())),
                constructors: vec![],
            }],
        });
        let result = verify_declarations(vec![axiom, ind]);
        assert_eq!(result.stats.verified, 2);
        assert_eq!(result.stats.failed, 0);
    }

    #[test]
    fn verify_into_preserves_existing_env_contents() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("preexisting"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();

        let decl = TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string("new_from_coq"),
            level_params: vec![],
            type_: Expr::prop(),
        });
        let result = verify_declarations_into(&mut env, vec![decl]);
        assert_eq!(result.stats.verified, 1);
        assert!(result
            .env
            .get_const(&Name::from_string("preexisting"))
            .is_some());
        assert!(result
            .env
            .get_const(&Name::from_string("new_from_coq"))
            .is_some());
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust source ingestion for `clean-rust-sem`.
//!
//! This module parses a supported subset of Rust source with `syn` and lowers
//! it into the existing semantic AST so the interpreter can run real `.rs`
//! programs without hand-built `Expr` trees.

mod captures;
mod desugar;
mod expr_closures;
mod expr_operators;
mod expr_paths;
mod exprs;
mod items;
mod literals;
mod macros;
mod parser;
mod patterns;
mod types;

use crate::eval::Interpreter;
use crate::expr::Item;
use crate::nll::NllResult;
use crate::proof_bundle::RustProofBundle;
use crate::vir_lowering::{LoweredProgram, VirLoweringError};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use thiserror::Error;

use parser::Parser;

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SourceError {
    #[error("failed to parse Rust source: {0}")]
    Parse(#[from] syn::Error),

    #[error("failed to read Rust source from {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("unsupported {context}: {detail}")]
    Unsupported {
        context: &'static str,
        detail: String,
    },

    #[error("invalid {context}: {detail}")]
    Invalid {
        context: &'static str,
        detail: String,
    },
}

#[derive(Debug, Clone)]
pub struct SourceProgram {
    items: Vec<Item>,
}

impl SourceProgram {
    pub fn parse(source: &str) -> Result<Self, SourceError> {
        let program = Parser::default().parse_source(source)?;
        program.validate_trait_impl_targets()?;
        program.validate_supertrait_obligations()?;
        Ok(program)
    }

    pub fn from_file(path: impl AsRef<Path>) -> Result<Self, SourceError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path).map_err(|source| SourceError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        Self::parse(&source)
    }

    pub fn items(&self) -> &[Item] {
        &self.items
    }

    pub fn run(&self, interpreter: &mut Interpreter) -> crate::expr::EvalResult {
        interpreter.run_program(&self.items, None)
    }

    /// Run the program with stacked-borrows aliasing checks enabled.
    pub fn run_with_aliasing_checks(&self) -> crate::expr::EvalResult {
        let mut interpreter = Interpreter::new().with_aliasing_checks(true);
        self.run(&mut interpreter)
    }

    /// Lower parsed semantic AST function bodies into VIR.
    pub fn lower_to_vir(&self) -> Result<LoweredProgram, VirLoweringError> {
        crate::vir_lowering::lower_items(&self.items)
    }

    /// Lower parsed semantic AST function bodies into VIR and run NLL on each one.
    pub fn check_borrows(&self) -> Result<BTreeMap<String, NllResult>, VirLoweringError> {
        Ok(self.lower_to_vir()?.check_borrows())
    }

    /// Build a Lean-facing ownership proof bundle from parsed Rust source.
    pub fn build_proof_bundle(&self) -> Result<RustProofBundle, VirLoweringError> {
        crate::proof_bundle::build_for_program(self)
    }

    /// Build a proof bundle via the `ProofBundleBuilder` pipeline.
    ///
    /// This is equivalent to `build_proof_bundle()` but uses the explicit
    /// builder API for clarity in the public interface.
    pub fn proof_obligations(&self) -> Result<RustProofBundle, VirLoweringError> {
        crate::proof_bundle_builder::ProofBundleBuilder::new().from_source(self)
    }

    /// Validate that every `impl Trait for Type` references a trait
    /// definition present in the source program.
    fn validate_trait_impl_targets(&self) -> Result<(), SourceError> {
        use std::collections::HashSet;

        let trait_names: HashSet<&str> = self
            .items
            .iter()
            .filter_map(|item| match item {
                Item::TraitDef(def) => Some(def.name.as_str()),
                _ => None,
            })
            .collect();

        for item in &self.items {
            if let Item::Impl {
                trait_name: Some(trait_name),
                ..
            } = item
            {
                if !trait_names.contains(trait_name.as_str()) {
                    return Err(SourceError::Invalid {
                        context: "impl",
                        detail: format!("trait impl references undefined trait `{trait_name}`"),
                    });
                }
            }
        }

        Ok(())
    }

    /// Validate that every `impl Trait for Type` satisfies the trait's
    /// supertrait obligations (i.e., `Type` also implements all supertraits).
    fn validate_supertrait_obligations(&self) -> Result<(), SourceError> {
        use std::collections::{HashMap, HashSet};

        // Collect trait defs with their supertraits
        let mut trait_supers: HashMap<&str, &[String]> = HashMap::new();
        for item in &self.items {
            if let Item::TraitDef(def) = item {
                trait_supers.insert(&def.name, &def.supertraits);
            }
        }

        // Collect all (trait_name, type_name) impl pairs
        let mut impl_pairs: HashSet<(&str, String)> = HashSet::new();
        for item in &self.items {
            if let Item::Impl {
                self_ty,
                trait_name: Some(trait_name),
                ..
            } = item
            {
                let type_name = self_ty.name().unwrap_or_else(|| "anonymous".to_string());
                impl_pairs.insert((trait_name, type_name));
            }
        }

        // Check supertrait obligations
        for item in &self.items {
            if let Item::Impl {
                self_ty,
                trait_name: Some(trait_name),
                ..
            } = item
            {
                if let Some(supers) = trait_supers.get(trait_name.as_str()) {
                    let type_name = self_ty.name().unwrap_or_else(|| "anonymous".to_string());
                    for super_trait in *supers {
                        if !impl_pairs.contains(&(super_trait.as_str(), type_name.clone())) {
                            return Err(SourceError::Invalid {
                                context: "impl",
                                detail: format!(
                                    "type `{type_name}` implements `{trait_name}` but \
                                     does not implement supertrait `{super_trait}`"
                                ),
                            });
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

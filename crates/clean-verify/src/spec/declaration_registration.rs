// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive and recursive declaration registration helpers for `Specification`.

use clean_elab::{elaborate_decl_and_register, ElabResult};
use clean_kernel::{Declaration, Expr, Level, Name, TypeChecker};
use clean_parser::parse_decl;
use std::collections::HashSet;

use super::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    /// Add an inductive type definition using the elaborator
    ///
    /// This registers a proper inductive type with its recursor (T.rec, T.casesOn)
    /// which enables structural recursion on the type.
    ///
    /// # Arguments
    /// * `source` - Lean-style inductive declaration source, e.g.:
    ///   ```text
    ///   inductive MyType : Type
    ///   | ctor1 : MyType
    ///   | ctor2 : Nat → MyType → MyType
    ///   ```
    /// * `description` - Human-readable description for tracking
    ///
    /// # Example
    ///
    /// ```text
    /// spec.add_inductive(r"inductive KExpr : Type
    /// | sort : Nat → KExpr
    /// | bvar : Nat → KExpr
    /// | app : KExpr → KExpr → KExpr
    /// | lam : KExpr → KExpr → KExpr
    /// | pi : KExpr → KExpr → KExpr", "Kernel expression type")?;
    /// ```
    pub fn add_inductive(&mut self, source: &str, description: &str) -> Result<(), SpecError> {
        let decl = parse_decl(source).map_err(|e| SpecError::ParseError(e.to_string()))?;
        let ind_name = source
            .split_whitespace()
            .skip_while(|w| *w != "inductive")
            .nth(1)
            .unwrap_or("<unknown>");
        let result = elaborate_decl_and_register(&mut self.env, &decl).map_err(|e| {
            SpecError::ElabError(format!("Failed to elaborate inductive {ind_name}: {e}"))
        })?;

        match result {
            ElabResult::Inductive {
                name,
                universe_params,
                ty,
                constructors,
                ..
            } => self.record_inductive_result(name, universe_params, ty, constructors, description),
            _ => Err(SpecError::TypeError(format!(
                "Expected Inductive result, got: {:?}",
                result
            ))),
        }
    }

    fn upper_camel_name(name: &str) -> String {
        let mut out = String::new();
        for part in name.split('_') {
            if part.is_empty() {
                continue;
            }
            let mut chars = part.chars();
            if let Some(first) = chars.next() {
                out.push(first.to_ascii_uppercase());
                out.extend(chars);
            }
        }
        if out.is_empty() {
            name.to_string()
        } else {
            out
        }
    }

    fn record_inductive_result(
        &mut self,
        name: Name,
        universe_params: Vec<Name>,
        ty: Expr,
        constructors: Vec<(Name, Expr)>,
        description: &str,
    ) -> Result<(), SpecError> {
        let alias_base = Self::alias_base_for(&name);
        self.register_inductive_alias(&name, &universe_params, &ty, &alias_base)?;
        self.record_inductive_type(&name, ty, description);
        self.record_inductive_recursor(&name);
        self.record_constructors(&name, &universe_params, &alias_base, constructors)?;
        Ok(())
    }

    fn alias_base_for(name: &Name) -> String {
        let name_str = name.to_string();
        if name_str
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_lowercase())
        {
            Self::upper_camel_name(&name_str)
        } else {
            String::new()
        }
    }

    fn register_inductive_alias(
        &mut self,
        name: &Name,
        universe_params: &[Name],
        ty: &Expr,
        alias_base: &str,
    ) -> Result<(), SpecError> {
        if alias_base.is_empty() {
            return Ok(());
        }

        let alias_name_id = Name::from_string(alias_base);
        if self.env.get_const(&alias_name_id).is_some() || self.definitions.contains_key(alias_base)
        {
            return Ok(());
        }

        let alias_levels: Vec<_> = universe_params.iter().cloned().map(Level::param).collect();
        let alias_value = Expr::const_(name.clone(), alias_levels);
        self.env
            .add_decl(Declaration::Definition {
                name: alias_name_id,
                level_params: universe_params.to_vec(),
                type_: ty.clone(),
                value: alias_value.clone(),
                is_reducible: false,
            })
            .map_err(|e| SpecError::TypeError(format!("add_decl alias: {e}")))?;

        let name_str = name.to_string();
        self.definitions.insert(
            alias_base.to_string(),
            SpecDefinition {
                name: alias_base.to_string(),
                type_src: format!("(alias of {name_str})"),
                value_src: Some(format!("(alias of {name_str})")),
                is_axiom: false,
                description: format!("Alias for {}", name_str),
                // PROOF STATUS: DerivedPending — alias has a definitional value
                // but has not been verified through the kernel promote pipeline.
                // Part of #3361.
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedPending,
                elaborated_type: Some(ty.clone()),
                elaborated_value: Some(alias_value),
                dependencies: None,
                axiom_deps: HashSet::new(),
            },
        );
        Ok(())
    }

    fn record_inductive_type(&mut self, name: &Name, ty: Expr, description: &str) {
        self.definitions.insert(
            name.to_string(),
            SpecDefinition {
                name: name.to_string(),
                type_src: "Type".to_string(),
                value_src: None,
                is_axiom: false,
                description: description.to_string(),
                // PROOF STATUS: DerivedPending — inductive type registration does not
                // go through the kernel promote pipeline. Part of #3361.
                category: AxiomCategory::FoundationalRule,
                proof_status: ProofStatus::DerivedPending,
                elaborated_type: Some(ty),
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            },
        );
    }

    fn record_inductive_recursor(&mut self, name: &Name) {
        let rec_name = Name::from_string(&format!("{}.rec", name));
        if let Some(rec_val) = self.env.get_recursor(&rec_name) {
            self.definitions.insert(
                rec_name.to_string(),
                SpecDefinition {
                    name: rec_name.to_string(),
                    type_src: format!("(recursor of {})", name),
                    value_src: None,
                    is_axiom: false,
                    description: format!("Recursor for {}, enables structural recursion", name),
                    // PROOF STATUS: DerivedPending — recursor registration does not
                    // go through the kernel promote pipeline. Part of #3361.
                    category: AxiomCategory::FoundationalRule,
                    proof_status: ProofStatus::DerivedPending,
                    elaborated_type: Some(rec_val.type_.clone()),
                    elaborated_value: None,
                    dependencies: None,
                    axiom_deps: HashSet::new(),
                },
            );
        }
    }

    fn record_constructors(
        &mut self,
        name: &Name,
        universe_params: &[Name],
        alias_base: &str,
        constructors: Vec<(Name, Expr)>,
    ) -> Result<(), SpecError> {
        for (ctor_name, ctor_ty) in constructors {
            self.record_constructor(name, &ctor_name, &ctor_ty);
            self.register_constructor_alias(universe_params, alias_base, &ctor_name, &ctor_ty)?;
        }
        Ok(())
    }

    fn record_constructor(&mut self, name: &Name, ctor_name: &Name, ctor_ty: &Expr) {
        self.definitions.insert(
            ctor_name.to_string(),
            SpecDefinition {
                name: ctor_name.to_string(),
                type_src: format!("(constructor of {})", name),
                value_src: None,
                is_axiom: false,
                description: format!("Constructor of {}", name),
                // PROOF STATUS: DerivedPending — constructor registration does not
                // go through the kernel promote pipeline. Part of #3361.
                category: AxiomCategory::FoundationalRule,
                proof_status: ProofStatus::DerivedPending,
                elaborated_type: Some(ctor_ty.clone()),
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            },
        );
    }

    fn register_constructor_alias(
        &mut self,
        universe_params: &[Name],
        alias_base: &str,
        ctor_name: &Name,
        ctor_ty: &Expr,
    ) -> Result<(), SpecError> {
        if alias_base.is_empty() {
            return Ok(());
        }

        let ctor_str = ctor_name.to_string();
        let ctor_short = ctor_str.rsplit('.').next().unwrap_or(&ctor_str);
        let alias_name = format!("{alias_base}.{ctor_short}");
        let alias_name_id = Name::from_string(&alias_name);
        if self.env.get_const(&alias_name_id).is_some()
            || self.definitions.contains_key(&alias_name)
        {
            return Ok(());
        }

        let alias_levels: Vec<_> = universe_params.iter().cloned().map(Level::param).collect();
        let alias_value = Expr::const_(ctor_name.clone(), alias_levels);
        let alias_decl = self.constructor_alias_decl(
            alias_name_id.clone(),
            universe_params,
            ctor_ty,
            &alias_value,
        );

        self.env
            .add_decl(alias_decl)
            .map_err(|e| SpecError::TypeError(format!("add_decl ctor alias: {e}")))?;

        self.definitions.insert(
            alias_name.clone(),
            SpecDefinition {
                name: alias_name,
                type_src: format!("(alias of {ctor_str})"),
                value_src: Some(format!("(alias of {ctor_str})")),
                is_axiom: false,
                description: format!("Alias for {}", ctor_str),
                // PROOF STATUS: DerivedPending — constructor alias has a
                // definitional value but has not been verified through the
                // kernel promote pipeline. Part of #3361.
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedPending,
                elaborated_type: Some(ctor_ty.clone()),
                elaborated_value: Some(alias_value),
                dependencies: None,
                axiom_deps: HashSet::new(),
            },
        );
        Ok(())
    }

    fn constructor_alias_decl(
        &self,
        alias_name_id: Name,
        universe_params: &[Name],
        ctor_ty: &Expr,
        alias_value: &Expr,
    ) -> Declaration {
        let alias_is_prop = {
            let tc = TypeChecker::with_mode(&self.env, self.env.mode());
            tc.infer_type(ctor_ty)
                .ok()
                .is_some_and(|sort| sort.is_prop())
        };

        if alias_is_prop {
            Declaration::Theorem {
                name: alias_name_id,
                level_params: universe_params.to_vec(),
                type_: ctor_ty.clone(),
                value: alias_value.clone(),
            }
        } else {
            Declaration::Definition {
                name: alias_name_id,
                level_params: universe_params.to_vec(),
                type_: ctor_ty.clone(),
                value: alias_value.clone(),
                is_reducible: false,
            }
        }
    }

    /// Add a recursive definition using the full elaborator (with structural recursion)
    ///
    /// This elaborates a `def` with match expressions and recursive calls,
    /// transforming them to recursor applications via structural recursion.
    ///
    /// # Arguments
    /// * `source` - Lean-style def declaration source, e.g.:
    ///   ```text
    ///   def add (n m : Nat) : Nat := match n with
    ///   | Nat.zero => m
    ///   | Nat.succ p => Nat.succ (add p m)
    ///   ```
    /// * `description` - Human-readable description for tracking
    pub fn add_recursive_def(&mut self, source: &str, description: &str) -> Result<(), SpecError> {
        let decl = parse_decl(source).map_err(|e| SpecError::ParseError(e.to_string()))?;

        let result = elaborate_decl_and_register(&mut self.env, &decl).map_err(|e| {
            SpecError::ElabError(format!("Failed to elaborate def ({description}): {e}"))
        })?;

        // Track the definition.
        match result {
            ElabResult::Definition { name, ty, val, .. } => {
                self.definitions.insert(
                    name.to_string(),
                    SpecDefinition {
                        name: name.to_string(),
                        type_src: source.to_string(),
                        value_src: Some(source.to_string()),
                        is_axiom: false,
                        description: description.to_string(),
                        // PROOF STATUS: DerivedPending — elaborated definition has
                        // a value but has not been verified through the kernel
                        // promote pipeline. Part of #3361.
                        category: AxiomCategory::DerivedLemma,
                        proof_status: ProofStatus::DerivedPending,
                        elaborated_type: Some(ty),
                        elaborated_value: Some(val),
                        dependencies: None,
                        axiom_deps: HashSet::new(),
                    },
                );
                Ok(())
            }
            ElabResult::Theorem {
                name, ty, proof, ..
            } => {
                // Some defs elaborate as theorems (when Prop result type).
                self.definitions.insert(
                    name.to_string(),
                    SpecDefinition {
                        name: name.to_string(),
                        type_src: source.to_string(),
                        value_src: Some(source.to_string()),
                        is_axiom: false,
                        description: description.to_string(),
                        // PROOF STATUS: DerivedPending — elaborated theorem has a
                        // proof term but has not been verified through the kernel
                        // promote pipeline. Part of #3361.
                        category: AxiomCategory::DerivedLemma,
                        proof_status: ProofStatus::DerivedPending,
                        elaborated_type: Some(ty),
                        elaborated_value: Some(proof),
                        dependencies: None,
                        axiom_deps: HashSet::new(),
                    },
                );
                Ok(())
            }
            _ => Err(SpecError::TypeError(format!(
                "Expected Definition result, got: {:?}",
                result
            ))),
        }
    }
}

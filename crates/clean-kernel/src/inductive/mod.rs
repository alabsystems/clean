// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive Types
//!
//! Validation and compilation of inductive type definitions.
//!
//! In Lean/CIC, inductive types are introduced with:
//! - A type former (the inductive type itself)
//! - Constructors that build inhabitants
//! - A recursor (eliminator) for case analysis and recursion
//!
//! # Example: Natural Numbers
//! ```text
//! inductive Nat : Type
//! | zero : Nat
//! | succ : Nat → Nat
//! ```
//!
//! Generates:
//! - `Nat : Type`
//! - `Nat.zero : Nat`
//! - `Nat.succ : Nat → Nat`
//! - `Nat.rec : {C : Nat → Sort u} → C Nat.zero → ((n : Nat) → C n → C (Nat.succ n)) → (n : Nat) → C n`

use crate::expr::{stack_safe, Expr, ExprKind, ExprVisitor, LevelVec, ZFCSetExpr};
use crate::name::Name;
use serde::{Deserialize, Serialize};

/// A constructor declaration for an inductive type
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Constructor {
    /// Name of the constructor (e.g., "Nat.zero")
    pub name: Name,
    /// Type of the constructor (must return the inductive type)
    pub type_: Expr,
}

/// A single inductive type declaration
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InductiveType {
    /// Name of the inductive type
    pub name: Name,
    /// Type of the inductive (e.g., Type, Type → Type, etc.)
    pub type_: Expr,
    /// Constructors
    pub constructors: Vec<Constructor>,
}

/// Declaration of one or more mutually inductive types
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InductiveDecl {
    /// Universe parameters
    pub level_params: Vec<Name>,
    /// Number of parameters (shared prefix in all types and constructors)
    pub num_params: u32,
    /// The inductive types (length > 1 for mutual inductives)
    pub types: Vec<InductiveType>,
}

/// Information stored in the environment about an inductive type
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InductiveVal {
    /// Name of the inductive type
    pub name: Name,
    /// Universe parameters
    pub level_params: Vec<Name>,
    /// Type of the inductive
    pub type_: Expr,
    /// Number of parameters
    pub num_params: u32,
    /// Number of indices (arguments after parameters)
    pub num_indices: u32,
    /// Names of all inductive types in mutual block
    pub all_names: Vec<Name>,
    /// Names of constructors
    pub constructor_names: Vec<Name>,
    /// Whether the type is recursive
    pub is_recursive: bool,
    /// Whether this is a reflexive inductive (contains inductive → inductive)
    pub is_reflexive: bool,
    /// Whether large elimination is allowed (eliminating into Type u for u > 0)
    pub is_large_elim: bool,
    /// Whether this is a nested inductive type (numNested > 0 in Lean 4)
    pub is_nested: bool,
}

/// Information stored in the environment about a constructor
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConstructorVal {
    /// Name of the constructor
    pub name: Name,
    /// Name of the inductive type this constructs
    pub inductive_name: Name,
    /// Universe parameters (same as inductive)
    pub level_params: Vec<Name>,
    /// Type of the constructor
    pub type_: Expr,
    /// Number of parameters
    pub num_params: u32,
    /// Number of fields (arguments after parameters)
    pub num_fields: u32,
    /// Index of this constructor in the inductive's constructor list
    pub constructor_idx: u32,
}

/// Information stored in the environment about a recursor
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RecursorVal {
    /// Name of the recursor (e.g., "Nat.rec")
    pub name: Name,
    /// Ordering of arguments relative to the major premise
    pub arg_order: RecursorArgOrder,
    /// Universe parameters (includes motive universe)
    pub level_params: Vec<Name>,
    /// Type of the recursor
    pub type_: Expr,
    /// Name of the inductive type
    pub inductive_name: Name,
    /// Number of parameters
    pub num_params: u32,
    /// Number of indices
    pub num_indices: u32,
    /// Number of motives (1 for simple inductives, n for mutual)
    pub num_motives: u32,
    /// Number of minor premises (one per constructor)
    pub num_minors: u32,
    /// Recursor rules (one per constructor)
    pub rules: Vec<RecursorRule>,
    /// Whether K-like reduction is used
    pub is_k: bool,
}

/// A recursor rule: how the recursor computes on a constructor
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RecursorRule {
    /// Constructor this rule applies to
    pub constructor_name: Name,
    /// Number of fields in the constructor
    pub num_fields: u32,
    /// Which fields are recursive (require induction hypothesis)
    /// Length equals num_fields; true means the field has type involving the inductive
    pub recursive_fields: Vec<bool>,
    /// The right-hand side of the rule
    /// `rec ... (ctor fields) = rhs[fields, recursive_results]`
    pub rhs: Expr,
}

impl RecursorVal {
    /// Validate metadata consistency between RecursorVal and its RecursorRules.
    ///
    /// Checks three invariants (#1394):
    /// 1. `num_params + num_indices` aligns with recursor type binder structure
    /// 2. Each `RecursorRule.num_fields` is consistent with `recursive_fields` length
    /// 3. The total recursor arity (params + motives + minors + indices + 1 major)
    ///    matches the type's Pi-binder count
    ///
    /// Returns Ok(()) if consistent, Err with a description of the mismatch.
    #[must_use = "the Result indicates whether recursor metadata is consistent"]
    pub fn validate_metadata(&self) -> Result<(), String> {
        let type_arity = count_pi_args(&self.type_);

        // Check 1: recursor type arity matches metadata sum
        // Total expected: params + motives + minors + indices + 1 (major)
        let expected_arity =
            self.num_params + self.num_motives + self.num_minors + self.num_indices + 1;
        if type_arity != expected_arity {
            return Err(format!(
                "{}: type has {} Pi-binders but metadata expects {} \
                 (params={} + motives={} + minors={} + indices={} + 1 major)",
                self.name,
                type_arity,
                expected_arity,
                self.num_params,
                self.num_motives,
                self.num_minors,
                self.num_indices,
            ));
        }

        // Check 2: each rule's recursive_fields length matches num_fields
        for rule in &self.rules {
            if !rule.recursive_fields.is_empty()
                && rule.recursive_fields.len() != rule.num_fields as usize
            {
                return Err(format!(
                    "{}: rule for {} has num_fields={} but recursive_fields length={}",
                    self.name,
                    rule.constructor_name,
                    rule.num_fields,
                    rule.recursive_fields.len(),
                ));
            }
        }

        Ok(())
    }

    /// The inductive type of the recursor's MAJOR premise, read off the
    /// recursor's own type (Lean's `RecursorVal.getMajorInduct`).
    ///
    /// For ordinary recursors this equals `inductive_name`, but for the aux
    /// recursors of nested inductives (`Trie.rec_1`, …) the major premise
    /// eliminates the CONTAINER (`Array _`, `List _`, `Prod _ _`, …) while
    /// `inductive_name` names the family head — reductions that dispatch on
    /// the major's type (struct-eta, K) must use this, not `inductive_name`.
    ///
    /// Returns `None` if the type has fewer Pi binders than the metadata
    /// promises or the major premise's type head is not a constant.
    #[must_use]
    pub fn major_induct(&self) -> Option<&Name> {
        let args_before_major = match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                self.num_params + self.num_motives + self.num_minors + self.num_indices
            }
            RecursorArgOrder::MajorAfterMotive => {
                self.num_params + self.num_motives + self.num_indices
            }
        };
        let mut current = &self.type_;
        for _ in 0..args_before_major {
            match &current.kind {
                ExprKind::Pi(_, _, body) => current = body,
                _ => return None,
            }
        }
        let ExprKind::Pi(_, major_domain, _) = &current.kind else {
            return None;
        };
        match &major_domain.get_app_fn().kind {
            ExprKind::Const(name, _) => Some(name),
            _ => None,
        }
    }
}

/// Where the major premise appears in the recursor argument list.
///
/// Lean-style recursors (rec/casesOn) put the major after minors and indices.
/// recOn variants move the major immediately after motives/indices so users can
/// supply the major premise earlier.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum RecursorArgOrder {
    /// Standard layout: params → motives → minors → indices → major
    MajorAfterMinors,
    /// recOn layout: params → motives → indices → major → minors
    MajorAfterMotive,
}

/// Errors during inductive type checking
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum InductiveError {
    /// Inductive declaration has no type definitions.
    #[error("Empty inductive declaration")]
    EmptyDecl,
    /// Inductive type has no constructors.
    #[error("No constructors for inductive type {0}")]
    NoConstructors(Name),
    /// Constructor has a type that is not well-formed.
    #[error("Constructor {0} has invalid type")]
    InvalidConstructorType(Name),
    /// Inductive type appears in a non-positive position (breaks soundness).
    #[error("Non-positive occurrence of {0} in {1}")]
    NonPositive(Name, Name),
    /// The type of the inductive type itself is invalid.
    #[error("Invalid inductive type: {0}")]
    InvalidType(String),
    /// Constructor's universe level doesn't match the type's universe.
    #[error("Universe level mismatch in constructor {0}")]
    UniverseMismatch(Name),
    /// Constructor's return type is not the inductive type being defined.
    #[error("Constructor {0} does not return the inductive type {1}")]
    ConstructorReturnType(Name, Name),
    /// Two constructors have the same name.
    #[error("Duplicate constructor name: {0}")]
    DuplicateConstructor(Name),
    /// The number of parameters doesn't match the type signature.
    #[error("Invalid number of parameters")]
    InvalidParams,
    /// Constructor return type parameter does not match declared parameter.
    ///
    /// The constructor's return type must apply the inductive type to exactly
    /// the declared parameters (as BVar references to the corresponding Pi binders).
    /// Lean 4 reference: kernel/inductive.cpp `is_valid_ind_app` lines 343-346.
    #[error(
        "Constructor {ctor_name} return type parameter at index {param_idx} does not match \
         declared parameter of {ind_name}"
    )]
    ConstructorParamMismatch {
        /// Name of the constructor with the mismatched parameter
        ctor_name: Name,
        /// Name of the inductive type being defined
        ind_name: Name,
        /// Zero-based index of the mismatched parameter
        param_idx: u32,
    },
    /// Constructor return type index argument mentions the inductive type.
    ///
    /// Index arguments (after parameters) in the constructor's return type must
    /// not contain occurrences of any inductive type in the mutual block.
    /// Lean 4 reference: kernel/inductive.cpp `is_valid_ind_app` lines 351-356
    /// (lean4#2125).
    #[error(
        "Constructor {ctor_name} return type index argument at position {index_pos} \
         mentions inductive type {ind_name}"
    )]
    IndexArgMentionsInductive {
        /// Name of the constructor with the problematic index argument
        ctor_name: Name,
        /// Name of the inductive type found in the index argument
        ind_name: Name,
        /// Zero-based position of the index argument (relative to first index)
        index_pos: u32,
    },
    /// A nested container occurrence instantiates the container's parameters
    /// with expressions referencing constructor-local binders (loose bvars
    /// below the field depth), not just the declaration's shared parameters.
    ///
    /// Lean rejects these identically with this exact message text
    /// (kernel/inductive.cpp lines 930-951); the message is kept verbatim for
    /// parity. See `designs/2026-07-02-parameterized-nested-inductives.md`
    /// §1.2(5).
    #[error("nested inductive datatypes parameters cannot contain local variables.")]
    NestedParamsContainLocals,
    /// Nested-inductive elimination exceeded the per-declaration
    /// auxiliary-type cap.
    ///
    /// Clean-only defensive bound guaranteeing fixpoint termination on
    /// mutually-nesting containers (Lean is unbounded); recorded in
    /// `docs/JUSTIFIED_EXCEPTIONS.md`. Deepest observed corpus chain ≈ 8.
    #[error("nested inductive elimination for {decl} exceeded the auxiliary-type cap ({limit})")]
    NestedAuxLimit {
        /// Name of the declaration whose elimination overflowed the cap
        decl: Name,
        /// The cap that was exceeded
        limit: usize,
    },
    /// A nested container occurrence supplies a universe-level list whose
    /// length differs from the container's declared level parameters.
    #[error(
        "nested occurrence of {container} supplies {got} universe levels, expected {expected}"
    )]
    NestedLevelArity {
        /// The container inductive at the occurrence head
        container: Name,
        /// Number of levels supplied at the occurrence
        got: usize,
        /// Number of level parameters the container declares
        expected: usize,
    },
    /// An internal invariant of nested-inductive elimination or restore was
    /// violated; the declaration is rolled back rather than registered.
    ///
    /// This is a tripwire for arithmetic/shape regressions (never expected on
    /// well-formed input); any occurrence is a bug in the elimination pass,
    /// not in the user's declaration.
    #[error("nested inductive restore invariant violated: {0}")]
    NestedRestoreInvariant(String),
    /// A constructor embeds a block-type occurrence that is not a valid
    /// inductive application: wrong arity, under/over-application, a
    /// non-block head over a block occurrence, or a head whose level list is
    /// not exactly the declaration's level parameters.
    ///
    /// Lean 4 reference: kernel/inductive.cpp `check_positivity` /
    /// `is_valid_ind_app` ("contains a non valid occurrence of the
    /// datatypes being declared"). Strict post-transform check ([R8]).
    #[error(
        "arg #{arg_idx} of constructor {ctor_name} contains a non valid occurrence \
         of the datatypes being declared (block of {ind_name})"
    )]
    InvalidInductiveOccurrence {
        /// Constructor carrying the invalid occurrence
        ctor_name: Name,
        /// First type of the declaration block (error anchor)
        ind_name: Name,
        /// Argument position associated with the failure (0 when the
        /// failure is not argument-specific)
        arg_idx: u32,
    },
}

/// Check if an inductive type occurs strictly positively in an expression.
///
/// Positivity is required for logical consistency. The rule is:
/// - An occurrence in a constructor's return type is positive
/// - An occurrence in the domain of a Pi is positive IFF the inductive doesn't
///   appear in a nested negative position within that domain
/// - Specifically: `I → R` is fine (I just appears directly)
/// - But `(I → X) → R` is NOT fine (I appears left of an arrow within the domain)
///
/// In practice, for a constructor like `succ : Nat → Nat`:
/// - The first Nat (domain) is checked with "strictly positive" rules
/// - The second Nat (codomain) is fine
///
/// The strictly positive check means: the inductive can appear, but not to the
/// left of any arrows within that subexpression.
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// REQUIRES: `inductive_name` is the inductive being checked
/// REQUIRES: `param_count` matches the inductive's parameter count (if used by callers)
///
/// ENSURES: `Ok(())` iff this checker finds no negative occurrences by its rules
/// ENSURES: `Err(NonPositive)` indicates a detected non-positive occurrence
#[must_use = "the Result indicates whether the constructor satisfies strict positivity"]
pub fn check_positivity(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    // For constructor types, we check the whole type with standard rules
    check_positivity_in_ctor_type(inductive_name, expr, param_count, all_ind_names)
}

/// Check positivity in a constructor type: (args) → I params indices
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// REQUIRES: `inductive_name` is the inductive being checked
/// REQUIRES: `param_count` matches the inductive's parameter count (if used by callers)
///
/// ENSURES: `Ok(())` iff this checker finds no negative occurrences by its rules
/// ENSURES: `Err(NonPositive)` indicates a detected non-positive occurrence
fn check_positivity_in_ctor_type(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    stack_safe(|| {
        check_positivity_in_ctor_type_impl(inductive_name, expr, param_count, all_ind_names)
    })
}

/// Implementation (called via stacker::maybe_grow)
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// REQUIRES: `inductive_name` is the inductive being checked
/// REQUIRES: `param_count` matches the inductive's parameter count (if used by callers)
/// REQUIRES: `all_ind_names` contains all inductive type names in the mutual block
///
/// ENSURES: `Ok(())` iff this checker finds no negative occurrences by its rules
/// ENSURES: `Err(NonPositive)` indicates a detected non-positive occurrence
fn check_positivity_in_ctor_type_impl(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    stack_safe(|| match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // In a constructor argument type, the inductive can appear
            // but must be "strictly positive" (not left of any arrow)
            check_strictly_positive_impl(inductive_name, domain, param_count, all_ind_names)?;
            check_positivity_in_ctor_type_impl(
                inductive_name,
                codomain,
                param_count,
                all_ind_names,
            )?;
            Ok(())
        }
        _ => {
            // Return type - any occurrence is fine (it should be the inductive itself)
            Ok(())
        }
    })
}

/// Check strict positivity: the inductive may appear, but not to the left of any arrow
///
/// Called internally from check_positivity_in_ctor_type_impl (within stack_safe context)
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// REQUIRES: `inductive_name` is the inductive being checked
/// REQUIRES: `_param_count` matches the inductive's parameter count (if used by callers)
/// REQUIRES: `all_ind_names` contains all inductive type names in the mutual block
///
/// ENSURES: `Ok(())` iff this checker finds no negative occurrences by its rules
/// ENSURES: `Err(NonPositive)` indicates a detected non-positive occurrence
fn check_strictly_positive_impl(
    inductive_name: &Name,
    expr: &Expr,
    _param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    stack_safe(|| match &expr.kind {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => Ok(()),

        ExprKind::Const(_name, _) => {
            // Direct occurrence of the inductive is fine
            Ok(())
        }

        ExprKind::App(f, a) => {
            // Check if head is the inductive type
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = &head.kind {
                if name == inductive_name {
                    // I applied to args - args must not mention ANY mutual
                    // inductive negatively (#2145). Lean 4's is_valid_ind_app
                    // uses has_ind_occ which checks against the full m_ind_cnsts.
                    let args = expr.get_app_args();
                    for arg in args {
                        for ind_name in all_ind_names {
                            check_no_negative_occurrence(ind_name, arg)?;
                        }
                    }
                    return Ok(());
                }
            }
            // General application: check both parts for strict positivity
            check_strictly_positive_impl(inductive_name, f, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, a, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Pi(_, domain, codomain) => {
            // This is the critical case: (A → B) appears in a constructor argument
            // The inductive CANNOT appear in A (that would be negative);
            // neither can any sibling mutual inductive (Wave 107). Lean 4's
            // `is_valid_ind_app`/`check_positivity` checks every mutual
            // name, not just the type currently being elaborated — without
            // this, `Tree.bad : (Forest → Bool) → Tree` is silently
            // accepted because the checker is invoked with
            // `inductive_name = Tree` while the offender is `Forest`.
            check_no_negative_occurrence(inductive_name, domain)?;
            for sibling in all_ind_names {
                if *sibling != inductive_name {
                    check_no_negative_occurrence(sibling, domain)?;
                }
            }
            // But it CAN appear in B (still positive, just nested)
            check_strictly_positive_impl(inductive_name, codomain, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Lam(_, ty, body) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Let(_, ty, val, body, _) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, val, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Proj(_, _, e) => {
            check_strictly_positive_impl(inductive_name, e, _param_count, all_ind_names)?;
            Ok(())
        }

        // MData is transparent - check the inner expression
        ExprKind::MData(_, inner) => {
            check_strictly_positive_impl(inductive_name, inner, _param_count, all_ind_names)
        }

        // Mode-specific extensions - conservative: check all subexpressions
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => Ok(()),
        ExprKind::CubicalPath { ty, left, right } => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, left, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, right, _param_count, all_ind_names)
        }
        ExprKind::CubicalPathLam { body } => {
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)
        }
        ExprKind::CubicalPathApp { path, arg } => {
            check_strictly_positive_impl(inductive_name, path, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, arg, _param_count, all_ind_names)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, phi, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, u, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, base, _param_count, all_ind_names)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, phi, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, base, _param_count, all_ind_names)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, r, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, s, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, base, _param_count, all_ind_names)
        }
        ExprKind::ZFCSet(set_expr) => {
            check_strictly_positive_zfc_set(inductive_name, set_expr, _param_count, all_ind_names)
        }
        ExprKind::ZFCMem { element, set } => {
            check_strictly_positive_impl(inductive_name, element, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, set, _param_count, all_ind_names)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            check_strictly_positive_impl(inductive_name, domain, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, pred, _param_count, all_ind_names)
        }
        // Impredicative mode extensions
        ExprKind::SProp => Ok(()),
        ExprKind::Squash(inner) => {
            check_strictly_positive_impl(inductive_name, inner, _param_count, all_ind_names)
        }
    })
}

/// Check strict positivity for ZFC set expressions.
///
/// Recursively checks all sub-expressions within the ZFCSetExpr for strict
/// positivity of the inductive type. Separation and Replacement predicates
/// are binding constructs, but the bound variable is a set element, not the
/// inductive type, so we check their bodies the same as non-binding positions.
fn check_strictly_positive_zfc_set(
    inductive_name: &Name,
    set_expr: &ZFCSetExpr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => Ok(()),
        ZFCSetExpr::Singleton(e)
        | ZFCSetExpr::Union(e)
        | ZFCSetExpr::PowerSet(e)
        | ZFCSetExpr::Choice(e) => {
            check_strictly_positive_impl(inductive_name, e, param_count, all_ind_names)
        }
        ZFCSetExpr::Pair(a, b) => {
            check_strictly_positive_impl(inductive_name, a, param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, b, param_count, all_ind_names)
        }
        ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
            check_strictly_positive_impl(inductive_name, set, param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, pred, param_count, all_ind_names)
        }
    }
}

/// Check that the inductive does not appear in a negative position
/// (i.e., the inductive should not appear in this expression at all in the domain of an arrow)
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// REQUIRES: `inductive_name` is the inductive being checked
///
/// ENSURES: `Ok(())` iff `expr` does not mention `inductive_name`
/// ENSURES: `Err(NonPositive)` indicates a detected occurrence of `inductive_name`
fn check_no_negative_occurrence(inductive_name: &Name, expr: &Expr) -> Result<(), InductiveError> {
    if mentions_name(expr, inductive_name) {
        Err(InductiveError::NonPositive(
            inductive_name.clone(),
            inductive_name.clone(),
        ))
    } else {
        Ok(())
    }
}

/// ExprVisitor that checks if an expression contains `Const(target, ..)`.
///
/// Uses ExprVisitor trait (#1824) — only `visit_const` is overridden; the trait
/// handles structural recursion over all ExprKind variants (including Cubical/ZFC).
struct MentionsNameVisitor<'a> {
    target: &'a Name,
}

impl ExprVisitor for MentionsNameVisitor<'_> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> bool {
        name == self.target
    }
}

/// Check if an expression mentions a name
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// ENSURES: Returns true iff `expr` contains `Const(name, ..)` anywhere
pub fn mentions_name(expr: &Expr, name: &Name) -> bool {
    MentionsNameVisitor { target: name }.visit_expr(expr)
}

/// Count the number of Pi types at the head of an expression
///
/// Uses iterative traversal to avoid stack overflow on deeply nested types.
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// ENSURES: Result is the number of leading `Pi` binders in `expr`
pub fn count_pi_args(expr: &Expr) -> u32 {
    let mut count = 0u32;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count = count.saturating_add(1);
        current = body;
    }
    count
}

/// Strip `n` Pi types from the front of an expression, returning the body
///
/// Uses iterative traversal to avoid stack overflow on deeply nested Pi types.
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// ENSURES: Returns the body after stripping up to `n` leading `Pi` binders
pub fn strip_pi(expr: &Expr, n: u32) -> &Expr {
    // Bounded for-loop: no decrement, so no underflow obligation. The previous
    // `remaining -= 1` was guarded by `while remaining > 0` (underflow was
    // unreachable) but left an unproven MIR Sub assert in the trusted core
    // (Trust ledger 2026-06-10, panic_boundary Overflow(Sub) @ inductive/mod.rs:627).
    let mut current = expr;
    for _ in 0..n {
        match &current.kind {
            ExprKind::Pi(_, _, body) => current = body,
            _ => break,
        }
    }
    current
}

/// Get the return type of a Pi-telescope (strip all Pi's)
///
/// Uses iterative traversal to avoid stack overflow on deeply nested Pi types.
///
/// # Contract
///
/// REQUIRES: `expr` is well-formed (no dangling BVars)
/// ENSURES: Returns the innermost non-Pi expression (the final return type)
/// ENSURES: If `expr` is not a Pi, returns `expr` unchanged
pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

/// Strip elaborator type-annotation gadgets from the head of a type.
///
/// Lean 4 kernel parity: `add_inductive_fn::mk_local_decl[_for]` wraps every
/// binder domain the inductive machinery collects (parameters, indices,
/// constructor fields) in `consume_type_annotations`
/// (`Lean.Expr.consumeTypeAnnotations`), so generated recursor/casesOn/recOn
/// types never contain `optParam` / `autoParam` / `outParam` /
/// `semiOutParam` applications even when the stored constructor type does
/// (e.g. `Lean.SourceInfo.synthetic`'s `canonical : Bool := false` field is
/// `optParam Bool Bool.false` in the constructor but plain `Bool` in
/// `Lean.SourceInfo.rec`'s minor premise). Without this, a Clean-regenerated
/// recursor type diverges from the `.olean`-imported one and the graduation
/// gate's carried-family member cross-check fail-closes.
///
/// Semantics mirror `consumeTypeAnnotations` exactly:
/// - `optParam α default` / `autoParam α tactic` (arity 2) → recurse on `α`
/// - `outParam α` / `semiOutParam α` (arity 1) → recurse on `α`
/// - anything else is returned unchanged.
pub fn consume_type_annotations(expr: &Expr) -> &Expr {
    let mut current = expr;
    loop {
        let ExprKind::App(f, last) = &current.kind else {
            return current;
        };
        // Exactly-arity-2 wrappers: `optParam α default` / `autoParam α tac`.
        if let ExprKind::App(f2, alpha) = &f.kind {
            if let ExprKind::Const(name, _) = &f2.kind {
                let s = name.to_string();
                if s == "optParam" || s == "autoParam" {
                    current = alpha;
                    continue;
                }
            }
        }
        // Exactly-arity-1 wrappers: `outParam α` / `semiOutParam α`.
        if let ExprKind::Const(name, _) = &f.kind {
            let s = name.to_string();
            if s == "outParam" || s == "semiOutParam" {
                current = last;
                continue;
            }
        }
        return current;
    }
}

/// Validate an inductive declaration
///
/// # Contract
///
/// REQUIRES: `decl` has at least one type (non-empty `types` field)
/// REQUIRES: All expressions in constructors are well-formed
/// ENSURES: `Ok(())` if all constructors satisfy positivity and return the correct type
/// ENSURES: `Err(EmptyDecl)` if `decl.types` is empty
/// ENSURES: `Err(NonPositive)` if any constructor violates strict positivity
/// ENSURES: `Err(ConstructorReturnType)` if a constructor doesn't return its inductive type
#[must_use = "the Result indicates whether the inductive declaration is well-formed"]
pub fn validate_inductive(decl: &InductiveDecl) -> Result<(), InductiveError> {
    if decl.types.is_empty() {
        return Err(InductiveError::EmptyDecl);
    }

    // Collect all inductive type names for mutual positivity checking (#2135).
    // For mutual inductives, each constructor must be checked against ALL type
    // names in the block, not just its own. Otherwise a sibling type can appear
    // in a non-positive position (e.g., (B → Nat) → A) without being detected.
    let all_names: Vec<&Name> = decl.types.iter().map(|t| &t.name).collect();

    // Check each inductive type
    for ind_type in &decl.types {
        for ctor in &ind_type.constructors {
            // Check positivity against all names in the mutual block.
            for name in &all_names {
                check_positivity(name, &ctor.type_, decl.num_params, &all_names)?;
            }

            // Validate the constructor's return type application:
            // head must be the inductive, params must match, indices must be clean.
            validate_ctor_return_type(ctor, ind_type, decl, &all_names)?;
        }
    }

    Ok(())
}

/// Validate a constructor's return type application (head, params, and indices).
///
/// Lean 4 reference: kernel/inductive.cpp `is_valid_ind_app`.
///
/// Checks:
/// 1. The return type head is `Const(ind_type.name, _)` (lines 339-341)
/// 2. Parameter arguments match declared params as BVars (lines 343-346)
/// 3. Index arguments do not mention any inductive in the mutual block
///    (lines 351-356, lean4#2125, #3243)
fn validate_ctor_return_type(
    ctor: &Constructor,
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    all_names: &[&Name],
) -> Result<(), InductiveError> {
    let return_type = get_return_type(&ctor.type_);

    // HIT path constructor (Cubical mode): the return type is a `CubicalPath`
    // whose line `ty : I → Sort` targets the inductive, with endpoints that are
    // bare *point* constructors of the same type (e.g. S¹'s
    // `loop : Path (λ_:I. S¹) base base`). These are validated and accepted by a
    // dedicated path, then the Const-only param/index checks below are skipped
    // (a path constructor has no applied params/indices in its return head).
    if let ExprKind::CubicalPath { ty, left, right } = &return_type.kind {
        return validate_path_ctor_return_type(ctor, ind_type, decl, ty, left, right);
    }

    let head = return_type.get_app_fn();

    // Check 1: constructor returns the correct inductive type
    match &head.kind {
        ExprKind::Const(name, _) if name == &ind_type.name => {}
        _ => {
            return Err(InductiveError::ConstructorReturnType(
                ctor.name.clone(),
                ind_type.name.clone(),
            ));
        }
    }

    let args = return_type.get_app_args();

    // Check 2: parameter arguments match declared params as BVars.
    // Each a_i (for i < num_params) must be BVar(total_binders - 1 - i).
    if decl.num_params > 0 {
        let total_binders = count_pi_args(&ctor.type_);
        for i in 0..decl.num_params {
            let param_ok = if total_binders > i {
                let expected_bvar = total_binders - 1 - i;
                args.get(i as usize).is_some_and(
                    |arg| matches!(&arg.kind, ExprKind::BVar(idx) if *idx == expected_bvar),
                )
            } else {
                false
            };
            if !param_ok {
                return Err(InductiveError::ConstructorParamMismatch {
                    ctor_name: ctor.name.clone(),
                    ind_name: ind_type.name.clone(),
                    param_idx: i,
                });
            }
        }
    }

    // Check 3: index arguments must not mention any inductive in the mutual
    // block. Lean 4 reference: kernel/inductive.cpp lines 351-356 (lean4#2125).
    let num_params = decl.num_params as usize;
    for (idx_pos, idx_arg) in args.iter().skip(num_params).enumerate() {
        for ind_name in all_names {
            if mentions_name(idx_arg, ind_name) {
                return Err(InductiveError::IndexArgMentionsInductive {
                    ctor_name: ctor.name.clone(),
                    ind_name: (*ind_name).clone(),
                    index_pos: idx_pos as u32,
                });
            }
        }
    }

    Ok(())
}

/// Recognize the **propositional-truncation** HIT shape `∥_∥ : Sort s → Sort s`
/// — the SECOND known-sound HIT (alongside S¹). The shape is *exactly*:
///
/// ```text
/// inductive Trunc (A : Sort s) : Sort s
/// | in     : A → Trunc A                                  -- point constructor
/// | squash : (x y : Trunc A) → Path (λ _:I. Trunc A) x y  -- propositional squash
/// ```
///
/// i.e. a single non-mutual type with **one parameter `A`**, **no indices**, and
/// **two constructors**: a point constructor taking a single `A`-field, and a
/// *path* constructor (`squash`) with two `Trunc A` fields whose path runs
/// between them (making `Trunc A` a proposition).
///
/// Recognized purely by SHAPE (not by name) and deliberately TIGHT — nothing
/// outside this exact shape passes, so the HIT gate is never opened to arbitrary
/// inductives. Used to (a) admit `squash` through
/// [`validate_path_ctor_return_type`] and (b) gate generation of the sound
/// prop-restricted recursor (`build_truncation_recursor`).
pub(crate) fn is_prop_truncation_shape(decl: &InductiveDecl) -> bool {
    // Single non-mutual type, exactly one parameter.
    if decl.types.len() != 1 || decl.num_params != 1 {
        return false;
    }
    let ind = &decl.types[0];
    let ind_name = &ind.name;

    // Type former: `Π (A : Sort _). Sort _` (one binder, Sort domain & body).
    let ExprKind::Pi(_, a_dom, a_cod) = &ind.type_.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) || !matches!(a_cod.kind, ExprKind::Sort(_)) {
        return false;
    }

    if ind.constructors.len() != 2 {
        return false;
    }
    is_truncation_point_ctor(&ind.constructors[0].type_, ind_name)
        && is_truncation_squash_ctor(&ind.constructors[1].type_, ind_name)
}

/// `expr == App(Const(ind_name), BVar(bvar))` — the inductive applied to a single
/// de-Bruijn variable (its parameter at the given depth).
fn is_ind_applied_to_bvar(expr: &Expr, ind_name: &Name, bvar: u32) -> bool {
    if let ExprKind::App(f, a) = &expr.kind {
        if let (ExprKind::Const(n, _), ExprKind::BVar(k)) = (&f.kind, &a.kind) {
            return n == ind_name && *k == bvar;
        }
    }
    false
}

/// Point-constructor shape `Π (A : Sort _). Π (_ : A). Ind A` (one parameter, one
/// `A`-typed field, returning the inductive applied to the parameter).
fn is_truncation_point_ctor(ty: &Expr, ind_name: &Name) -> bool {
    // Π (A : Sort _).
    let ExprKind::Pi(_, a_dom, after_a) = &ty.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) {
        return false;
    }
    // Π (_ : A).   A is the parameter = BVar(0) at this depth.
    let ExprKind::Pi(_, field_dom, ret) = &after_a.kind else {
        return false;
    };
    if !matches!(field_dom.kind, ExprKind::BVar(0)) {
        return false;
    }
    // Return: `Ind A` = `App(Ind, BVar1)` (A under the field binder is BVar1).
    is_ind_applied_to_bvar(ret, ind_name, 1)
}

/// Squash-constructor shape
/// `Π (A : Sort _). Π (x : Ind A). Π (y : Ind A). Path (λ _:I. Ind A) x y`
/// (one parameter, two `Ind A` fields, a homogeneous path running between them).
fn is_truncation_squash_ctor(ty: &Expr, ind_name: &Name) -> bool {
    // Π (A : Sort _).
    let ExprKind::Pi(_, a_dom, after_a) = &ty.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) {
        return false;
    }
    // Π (x : Ind A).   Ind applied to BVar0 (parameter A at depth [A]).
    let ExprKind::Pi(_, x_dom, after_x) = &after_a.kind else {
        return false;
    };
    if !is_ind_applied_to_bvar(x_dom, ind_name, 0) {
        return false;
    }
    // Π (y : Ind A).   Ind applied to BVar1 (parameter A at depth [A, x]).
    let ExprKind::Pi(_, y_dom, ret) = &after_x.kind else {
        return false;
    };
    if !is_ind_applied_to_bvar(y_dom, ind_name, 1) {
        return false;
    }
    // Return: `Path (λ _:I. Ind A) x y` with x = BVar1, y = BVar0 at depth [A,x,y].
    let ExprKind::CubicalPath {
        ty: line,
        left,
        right,
    } = &ret.kind
    else {
        return false;
    };
    let ExprKind::Lam(_, lam_dom, lam_body) = &line.kind else {
        return false;
    };
    if !matches!(lam_dom.kind, ExprKind::CubicalInterval) {
        return false;
    }
    // Line body: `Ind A` with A = BVar3 (depth [A, x, y, _i]).
    if !is_ind_applied_to_bvar(lam_body, ind_name, 3) {
        return false;
    }
    matches!(left.kind, ExprKind::BVar(1)) && matches!(right.kind, ExprKind::BVar(0))
}

/// Recognize the **suspension** HIT shape `Susp : Sort s → Sort s` — the THIRD
/// known-sound HIT (after S¹ and propositional truncation). It generalizes the
/// HIT schema past S¹/truncation to a path constructor that is a *family*
/// (`merid : A → north ≡ south`). The shape is *exactly*:
///
/// ```text
/// inductive Susp (A : Sort s) : Sort s
/// | north : Susp A                                              -- point ctor
/// | south : Susp A                                              -- point ctor
/// | merid : (a : A) → Path (λ _:I. Susp A) (north A) (south A)  -- path FAMILY
/// ```
///
/// i.e. a single non-mutual type with **one parameter `A`**, **no indices**, and
/// **three constructors**: two nullary point constructors (`north`/`south`,
/// returning `Susp A`) and a *path* constructor (`merid`) taking ONE `A`-field
/// whose path runs between `north A` and `south A`. Unlike S¹'s `loop` (no
/// field) and truncation's `squash` (path between two *fields* of the type),
/// `merid`'s endpoints are the *point constructors* applied to the parameter and
/// it carries an `A`-field, making the path a family indexed by `a : A`.
///
/// Recognized purely by SHAPE (not by name) and deliberately TIGHT — nothing
/// outside this exact shape passes, so the HIT gate is never opened to arbitrary
/// inductives. Used to (a) admit `merid` through
/// [`validate_path_ctor_return_type`] and (b) gate generation of the sound
/// dependent recursor (`build_suspension_recursor`). The gate and the recursor
/// builder are kept in lockstep — a `merid` ctor is accepted iff a correct
/// recursor is generated.
pub(crate) fn is_suspension_shape(decl: &InductiveDecl) -> bool {
    // Single non-mutual type, exactly one parameter.
    if decl.types.len() != 1 || decl.num_params != 1 {
        return false;
    }
    let ind = &decl.types[0];
    let ind_name = &ind.name;

    // Type former: `Π (A : Sort _). Sort _` (one binder, Sort domain & body).
    let ExprKind::Pi(_, a_dom, a_cod) = &ind.type_.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) || !matches!(a_cod.kind, ExprKind::Sort(_)) {
        return false;
    }

    if ind.constructors.len() != 3 {
        return false;
    }
    let north = &ind.constructors[0];
    let south = &ind.constructors[1];
    let merid = &ind.constructors[2];
    is_suspension_point_ctor(&north.type_, ind_name)
        && is_suspension_point_ctor(&south.type_, ind_name)
        && is_suspension_merid_ctor(&merid.type_, ind_name, &north.name, &south.name)
}

/// Suspension point-constructor shape `Π (A : Sort _). Ind A` (one parameter,
/// NO fields, returning the inductive applied to the parameter). This is both
/// `north` and `south`.
fn is_suspension_point_ctor(ty: &Expr, ind_name: &Name) -> bool {
    // Π (A : Sort _).
    let ExprKind::Pi(_, a_dom, ret) = &ty.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) {
        return false;
    }
    // Return: `Ind A` = `App(Ind, BVar0)` (A at depth [A]).
    is_ind_applied_to_bvar(ret, ind_name, 0)
}

/// Suspension `merid`-constructor shape
/// `Π (A : Sort _). Π (a : A). Path (λ _:I. Ind A) (north A) (south A)`
/// (one parameter, one `A`-field, a homogeneous path running between the two
/// point constructors applied to the parameter).
fn is_suspension_merid_ctor(
    ty: &Expr,
    ind_name: &Name,
    north_name: &Name,
    south_name: &Name,
) -> bool {
    // Π (A : Sort _).
    let ExprKind::Pi(_, a_dom, after_a) = &ty.kind else {
        return false;
    };
    if !matches!(a_dom.kind, ExprKind::Sort(_)) {
        return false;
    }
    // Π (a : A).   A is the parameter = BVar(0) at depth [A].
    let ExprKind::Pi(_, field_dom, ret) = &after_a.kind else {
        return false;
    };
    if !matches!(field_dom.kind, ExprKind::BVar(0)) {
        return false;
    }
    // Return: `Path (λ _:I. Ind A) (north A) (south A)` at depth [A, a].
    let ExprKind::CubicalPath {
        ty: line,
        left,
        right,
    } = &ret.kind
    else {
        return false;
    };
    // Line: `λ _:I. Ind A` with A = BVar2 at depth [A, a, _i].
    let ExprKind::Lam(_, lam_dom, lam_body) = &line.kind else {
        return false;
    };
    if !matches!(lam_dom.kind, ExprKind::CubicalInterval) {
        return false;
    }
    if !is_ind_applied_to_bvar(lam_body, ind_name, 2) {
        return false;
    }
    // Endpoints: `north A` and `south A` with A = BVar1 at depth [A, a].
    // (`is_ind_applied_to_bvar` checks `App(Const(name), BVar(k))` for any name.)
    is_ind_applied_to_bvar(left, north_name, 1) && is_ind_applied_to_bvar(right, south_name, 1)
}

/// Validate a Higher-Inductive-Type *path* constructor's return type.
///
/// Accepts exactly three SHAPE-RESTRICTED, known-sound HIT path constructors:
///
/// 1. **S¹'s `loop`** — `c : Path (λ (_:I). I_app) ep_left ep_right` where the
///    line is `λ (_:I). <head = Const(ind)>` (targets the inductive being
///    defined), each endpoint is a **bare point constructor** of the same
///    inductive type declared strictly *before* this path constructor, the
///    constructor has **no leading Pi fields**, and the inductive has **no
///    parameters and no indices**.
///
/// 2. **Propositional truncation's `squash`** — the second known-sound HIT
///    ([`is_prop_truncation_shape`]). Accepted *only* when the whole declaration
///    is the recognized prop-truncation shape and this constructor is its squash
///    constructor; recursor generation special-cases the same shape, so the gate
///    and the recursor stay in lockstep.
///
/// 3. **Suspension's `merid`** — the third known-sound HIT
///    ([`is_suspension_shape`]), a path *family* `merid : A → north ≡ south`.
///    Accepted *only* when the whole declaration is the recognized suspension
///    shape and this constructor is its merid constructor; `build_suspension_recursor`
///    special-cases the same shape, so the gate and the recursor stay in lockstep.
///
/// These restrictions keep recursor generation sound and total. Anything outside
/// these three shapes is rejected here, so a wrong recursor is never generated
/// for an unsupported HIT.
fn validate_path_ctor_return_type(
    ctor: &Constructor,
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    line: &Expr,
    left: &Expr,
    right: &Expr,
) -> Result<(), InductiveError> {
    let bad = || InductiveError::ConstructorReturnType(ctor.name.clone(), ind_type.name.clone());

    // Suspension `merid` (the third known-sound HIT). The full shape is checked
    // by `is_suspension_shape`; here we only confirm this ctor is the recognized
    // merid constructor (the 3rd ctor of the recognized suspension shape).
    if is_suspension_shape(decl)
        && ind_type
            .constructors
            .get(2)
            .is_some_and(|c| c.name == ctor.name)
    {
        return Ok(());
    }

    // Prop-truncation `squash` (the second known-sound HIT). The full shape is
    // checked by `is_prop_truncation_shape`; here we only confirm this ctor is
    // the recognized squash constructor (the 2nd ctor of the recognized shape).
    if is_prop_truncation_shape(decl)
        && ind_type
            .constructors
            .get(1)
            .is_some_and(|c| c.name == ctor.name)
    {
        return Ok(());
    }

    // The inductive must have no parameters and no indices (S¹ scope).
    if decl.num_params != 0 || count_pi_args(&ind_type.type_) != 0 {
        return Err(bad());
    }
    // The path constructor must have no leading Pi fields: its type is directly
    // the `CubicalPath`.
    if count_pi_args(&ctor.type_) != 0 {
        return Err(bad());
    }

    // The line must be `λ (_:I). body` whose body head targets this inductive.
    let ExprKind::Lam(_, _, body) = &line.kind else {
        return Err(bad());
    };
    match &body.get_app_fn().kind {
        ExprKind::Const(name, _) if name == &ind_type.name => {}
        _ => return Err(bad()),
    }

    // Locate this path constructor's position in the constructor list.
    let Some(self_idx) = ind_type
        .constructors
        .iter()
        .position(|c| c.name == ctor.name)
    else {
        return Err(bad());
    };

    // Each endpoint must be a bare point constructor declared earlier.
    for ep in [left, right] {
        validate_path_endpoint(ep, ind_type, self_idx)?;
    }
    Ok(())
}

/// Validate a single endpoint of a path constructor (see
/// [`validate_path_ctor_return_type`]).
///
/// Requires the endpoint to be a bare `Const(c)` (no applied arguments) naming a
/// *point* constructor `c` of `ind_type` whose own constructor index is `<
/// self_idx`.
fn validate_path_endpoint(
    ep: &Expr,
    ind_type: &InductiveType,
    self_idx: usize,
) -> Result<(), InductiveError> {
    let bad = || {
        InductiveError::ConstructorReturnType(
            ind_type
                .constructors
                .get(self_idx)
                .map_or_else(|| ind_type.name.clone(), |c| c.name.clone()),
            ind_type.name.clone(),
        )
    };
    // Bare constant (no applied args).
    if !ep.get_app_args().is_empty() {
        return Err(bad());
    }
    let ExprKind::Const(c, _) = &ep.kind else {
        return Err(bad());
    };
    // Must name a constructor of this inductive, declared earlier than self.
    let Some(ep_idx) = ind_type.constructors.iter().position(|cc| &cc.name == c) else {
        return Err(bad());
    };
    if ep_idx >= self_idx {
        return Err(bad());
    }
    // The endpoint constructor must itself be a *point* constructor (not a path).
    let ep_ctor = &ind_type.constructors[ep_idx];
    if matches!(
        get_return_type(&ep_ctor.type_).kind,
        ExprKind::CubicalPath { .. }
    ) {
        return Err(bad());
    }
    Ok(())
}

/// Check if an inductive type is recursive
///
/// An inductive is recursive if any constructor has an argument mentioning any
/// type in the mutual inductive block. For non-mutual inductives, pass a
/// single-element slice with just the inductive's own name.
///
/// Lean 4 reference: `inductive.cpp:265-286` checks all `m_ind_cnsts`.
///
/// # Contract
///
/// REQUIRES: `all_ind_names` contains the names of ALL types in the mutual block
/// REQUIRES: `constructors` contains all constructors for this inductive type
/// ENSURES: Returns `true` iff any constructor argument type mentions any name in `all_ind_names`
/// ENSURES: Returns `false` for non-recursive types like `Unit` or `Bool`
pub(crate) fn is_recursive(all_ind_names: &[Name], constructors: &[Constructor]) -> bool {
    constructors
        .iter()
        .any(|ctor| mentions_any_name_in_args(&ctor.type_, all_ind_names))
}

/// Check if an inductive type is reflexive
///
/// A reflexive inductive is one where any type in the mutual block appears in
/// the domain of a function type in a constructor argument. For non-mutual
/// inductives, pass a single-element slice with just the inductive's own name.
///
/// Lean 4 reference: `inductive.cpp:294-309` checks all `m_ind_cnsts`.
///
/// Example: W-types (well-founded trees)
/// ```text
/// inductive W (A : Type) (B : A → Type) : Type
/// | sup : (a : A) → (B a → W A B) → W A B
/// ```
/// Here `W A B` appears in the domain of `B a → W A B`, making it reflexive.
///
/// Contrast with Nat which is recursive but NOT reflexive:
/// ```text
/// inductive Nat : Type
/// | succ : Nat → Nat
/// ```
/// Nat appears directly as an argument, not in a function domain.
///
/// # Contract
///
/// REQUIRES: `all_ind_names` contains the names of ALL types in the mutual block
/// REQUIRES: `constructors` contains all constructors for this inductive type
/// ENSURES: Returns `true` iff any name in `all_ind_names` appears in a function-typed argument domain
/// ENSURES: Reflexivity implies recursivity (if reflexive, then also recursive)
pub(crate) fn is_reflexive(all_ind_names: &[Name], constructors: &[Constructor]) -> bool {
    constructors
        .iter()
        .any(|ctor| has_reflexive_occurrence(&ctor.type_, all_ind_names))
}

/// Check if an expression has a reflexive occurrence of any name in the mutual block
///
/// A reflexive occurrence is when any mutual block name appears in the domain of a
/// function type that is itself an argument to a constructor.
///
/// Uses stack_safe for stack overflow protection on deeply nested Pi types.
fn has_reflexive_occurrence(expr: &Expr, names: &[Name]) -> bool {
    stack_safe(|| has_reflexive_occurrence_impl(expr, names))
}

/// Implementation of has_reflexive_occurrence (called via stack_safe)
fn has_reflexive_occurrence_impl(expr: &Expr, names: &[Name]) -> bool {
    match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // Check if this domain is a function type where any mutual block name appears
            // somewhere in that function type (making this a reflexive argument)
            if is_function_mentioning_any_name(domain, names) {
                return true;
            }
            // Continue checking in the codomain
            has_reflexive_occurrence_impl(codomain, names)
        }
        _ => false, // Return type doesn't matter
    }
}

/// Check if expr is a function type (Pi) that mentions any name in `names`
/// This detects reflexive arguments like `(B a → W A B)` where W appears in the codomain
fn is_function_mentioning_any_name(expr: &Expr, names: &[Name]) -> bool {
    match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // This is a function type - check if any name appears anywhere in it
            mentions_any_name(domain, names) || mentions_any_name(codomain, names)
        }
        _ => false, // Not a function type
    }
}

/// Check if an expression mentions any of the given names anywhere
fn mentions_any_name(expr: &Expr, names: &[Name]) -> bool {
    names.iter().any(|name| mentions_name(expr, name))
}

/// Check if an expression mentions any of the given names in its argument types
/// (Pi domains), not the return type.
///
/// Uses stack_safe for stack overflow protection on deeply nested Pi types.
fn mentions_any_name_in_args(expr: &Expr, names: &[Name]) -> bool {
    stack_safe(|| mentions_any_name_in_args_impl(expr, names))
}

/// Implementation of mentions_any_name_in_args (called via stack_safe)
fn mentions_any_name_in_args_impl(expr: &Expr, names: &[Name]) -> bool {
    match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            mentions_any_name(domain, names) || mentions_any_name_in_args_impl(codomain, names)
        }
        _ => false, // Return type doesn't count
    }
}

/// Check if large elimination is allowed
///
/// Large elimination (eliminating into Type u for u > 0) is allowed when:
/// - The inductive is not in Prop (always)
/// - The inductive is in Prop with 0 constructors (e.g., `False`)
/// - The inductive is in Prop with 1 constructor where all non-param fields
///   are either in Prop or appear as index arguments (singleton elimination)
///
/// # Contract
///
/// REQUIRES: `env` contains the inductive type and its constructors as registered constants
/// REQUIRES: `inductive_type` is the type signature of the inductive (e.g., `Type u` or `Prop`)
/// REQUIRES: `constructors` contains all constructors for this inductive
/// REQUIRES: `num_params` matches the inductive's parameter count
/// REQUIRES: `num_mutual_types` is the number of types in the mutual inductive block (1 for non-mutual)
/// ENSURES: Returns `true` if the inductive supports elimination into large universes
/// ENSURES: Returns `false` for `Nonempty`-like Prop inductives with non-Prop fields
/// ENSURES: Returns `false` for mutual Prop predicates (Lean 4 inductive.cpp:486-489)
/// ENSURES: Returns `true` for any Type-valued inductive (always allows large elim)
pub fn allows_large_elim(
    env: &crate::Environment,
    inductive_type: &Expr,
    constructors: &[Constructor],
    num_params: u32,
    num_types: usize,
) -> bool {
    !crate::env::elim_analysis::elim_only_at_universe_zero(
        env,
        inductive_type,
        constructors,
        num_params,
        num_types,
    )
}

mod strict;
pub(crate) use strict::validate_inductive_strict;

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod kani_proofs;

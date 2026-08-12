// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration result types and helper functions.
//!
//! Extracted from `infer/mod.rs` to reduce file size. Contains:
//! - `RecursiveDefContext` — recursive definition elaboration state
//! - `DerivedInstance` — auto-derived type class instances
//! - `ClassRegistration` — class registration metadata
//! - `ElabResult` — elaboration output variants
//! - Binder info conversion helpers

use crate::commands::{CheckResult, EvalResult, PrintResult};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId};
use clean_parser::{DeclModifiers, SurfaceBinderInfo, SurfaceExpr};
use std::collections::HashMap;

/// Metadata for a parameter after the decreasing argument in a recursive
/// definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct RecursiveExtraParam {
    /// Binder name as it appears in the local context.
    pub name: String,
    /// Original binder visibility, needed when rebuilding IH/motive binders.
    pub binder_info: BinderInfo,
}

/// Context for recursive definition elaboration (#378)
#[derive(Clone, Debug)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(super) struct RecursiveDefContext {
    /// Name of the function being defined
    pub func_name: String,
    /// Position of the decreasing argument (0-indexed)
    pub decreasing_arg_pos: usize,
    /// Name of the decreasing argument
    pub decreasing_arg_name: String,
    /// Inductive type name of the decreasing argument
    pub inductive_type_name: Option<Name>,
    /// Free variable for the inductive hypothesis (set when elaborating match arms)
    pub ih_fvar: Option<FVarId>,
    /// Type of the IH (set when elaborating match arms)
    pub ih_type: Option<Expr>,
    /// Mapping from pattern variable names to their IH fvars (#381)
    /// Used to replace recursive calls with the appropriate IH.
    /// Key is the variable name bound in the pattern, value is the IH fvar for that variable.
    pub ih_map: HashMap<String, FVarId>,
    /// Fully-qualified names of *sibling* mutual functions whose calls also
    /// rewrite to induction hypotheses (Track AA: a nested-mutual fold fuses
    /// `Tree.size`/`Tree.sizeList` into one `Tree.rec` application, so inside a
    /// minor body BOTH `Tree.size t` and `Tree.sizeList rest` must be recognized
    /// as recursive self-calls — each resolving to the IH bound for its argument
    /// variable). Empty for ordinary single-function recursion, leaving the
    /// existing `matches_call_name` behavior byte-for-byte unchanged.
    pub sibling_names: Vec<String>,
    /// Parameters AFTER the decreasing argument (#1386).
    /// These get folded into the recursor motive so IHs can handle varying
    /// parameter values in recursive calls (e.g., `Nat.succ cutoff` vs `cutoff`).
    pub extra_params: Vec<RecursiveExtraParam>,
    /// Well-founded measure expression from `termination_by` (#1132).
    /// Stored for future well-founded recursion compilation via `WellFounded.fix`.
    /// None for structural recursion or when no measure is provided.
    pub wf_measure: Option<Box<SurfaceExpr>>,
}

impl RecursiveDefContext {
    /// Short (final-segment) name of the function being defined, e.g.
    /// `bitWidth` for `TrustIr.Ty.bitWidth`.
    pub fn short_name(&self) -> &str {
        self.func_name
            .rsplit_once('.')
            .map(|(_, tail)| tail)
            .unwrap_or(self.func_name.as_str())
    }

    /// Does `candidate` name this recursive function?
    ///
    /// `func_name` is the fully qualified declaration name (e.g.
    /// `TrustIr.Ty.bitWidth`). A self-call may be spelled with the full
    /// qualified path, or with a namespace-relative prefix shorter than the
    /// enclosing namespace (`Ty.bitWidth` inside `namespace TrustIr`), so a
    /// candidate matches when it equals the full name or is a dotted *suffix*
    /// of it. The bare short name alone does not match here — that case is
    /// handled separately at call sites where the receiver type is known.
    pub fn matches_call_name(&self, candidate: &str) -> bool {
        let cand = candidate.strip_prefix("_root_.").unwrap_or(candidate);
        if Self::name_matches(cand, &self.func_name) {
            return true;
        }
        // Track AA: a fused nested-mutual fold also recognizes its sibling
        // function names as recursive self-calls (each resolves to the IH bound
        // for its argument variable, via `ih_map`).
        self.sibling_names
            .iter()
            .any(|sib| Self::name_matches(cand, sib))
    }

    /// Does the (already `_root_.`-stripped) `cand` denote the function whose
    /// fully qualified name is `full`? Matches an exact spelling, a dotted
    /// suffix of `full`, or (for a namespace-relative prefix like `Ty.bitWidth`
    /// inside `namespace TrustIr`) a dotted prefix of `full`. A bare short name
    /// alone does not match — that case is handled at call sites where the
    /// receiver type is known.
    fn name_matches(cand: &str, full: &str) -> bool {
        if cand == full || cand.ends_with(&format!(".{full}")) {
            return true;
        }
        cand.contains('.') && full.ends_with(&format!(".{cand}"))
    }
}

/// A derived instance generated from a `deriving` clause
#[derive(Debug, Clone)]
pub struct DerivedInstance {
    /// Instance name (e.g., "instReprPoint")
    pub name: Name,
    /// Class name (e.g., "Repr")
    pub class_name: Name,
    /// Instance type (e.g., Repr Point)
    pub ty: Expr,
    /// Instance value
    pub val: Expr,
    /// Priority (default: 1000 — [`crate::instances::DEFAULT_PRIORITY`])
    pub priority: u32,
    /// Universe level parameters used by this instance's type and value.
    ///
    /// Derive handlers call `mk_const` which generates fresh universe params
    /// (e.g., `u_0`, `u_1`) for universe-polymorphic constants. These params
    /// must be declared in the instance's `level_params` when registering.
    /// For concrete types with no type parameters, this may still be non-empty
    /// because the instance references universe-polymorphic constants like
    /// `DecidableEq.{u}`.  Fixes #3393.
    pub level_params: Vec<Name>,
}

/// Collect all `Level::Param` names referenced in an expression.
///
/// Traverses Sort levels and Const level arguments to find all universe
/// parameter names used. Returns a deduplicated, order-preserving list.
/// Used to compute `DerivedInstance::level_params` from the instance's
/// type and value expressions.  Part of #3393.
pub fn collect_level_params(exprs: &[&Expr]) -> Vec<Name> {
    use clean_kernel::ExprKind;
    use std::collections::HashSet;

    let mut seen = HashSet::new();
    let mut result = Vec::new();
    let mut expr_stack: Vec<&Expr> = exprs.to_vec();

    while let Some(curr) = expr_stack.pop() {
        match curr.kind() {
            ExprKind::Sort(l) => collect_level_params_from_level(l, &mut seen, &mut result),
            ExprKind::Const(_, levels) => {
                for l in levels {
                    collect_level_params_from_level(l, &mut seen, &mut result);
                }
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                expr_stack.push(a);
                expr_stack.push(f);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                expr_stack.push(body);
                expr_stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                expr_stack.push(body);
                expr_stack.push(val);
                expr_stack.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                expr_stack.push(inner);
            }
            _ => {}
        }
    }

    result
}

/// Helper: collect Level::Param names from a level expression.
fn collect_level_params_from_level(
    level: &clean_kernel::Level,
    seen: &mut std::collections::HashSet<Name>,
    result: &mut Vec<Name>,
) {
    use clean_kernel::Level;

    let mut stack = vec![level];
    while let Some(l) = stack.pop() {
        match l {
            Level::Zero => {}
            Level::Param(n) => {
                if seen.insert(n.clone()) {
                    result.push(n.clone());
                }
            }
            Level::Succ(inner) => stack.push(inner),
            Level::Max(a, b) | Level::IMax(a, b) => {
                stack.push(b);
                stack.push(a);
            }
        }
    }
}

/// Information needed to register a class with the kernel
#[derive(Debug, Clone)]
pub struct ClassRegistration {
    /// Number of parameters the class takes
    pub num_params: usize,
    /// Indices of "output parameters" (can be inferred from other params)
    pub out_params: Vec<usize>,
    /// Indices of "semi-output parameters"
    pub semi_out_params: Vec<usize>,
}

// Note: Recursor information is provided by the kernel's RecursorVal type.
// See clean_kernel::RecursorVal after calling env.add_inductive().

/// A user-written hole (`_`) and the type the elaborator expected at it.
///
/// Recorded after a declaration finishes elaborating by snapshotting the
/// metavariables tagged with a source span (see [`MetaVar::span`]). The
/// expected type is the metavariable's `ty`, instantiated as far as the final
/// metavariable assignments allow. For an unsolved hole type the type is
/// reported as-is — that is precisely the expected type to show at the hole.
///
/// IDE-surface only: this carries no proof term and never affects what is
/// added to the kernel.
///
/// [`MetaVar::span`]: crate::unify::MetaVar::span
#[derive(Debug, Clone)]
pub struct HoleContext {
    /// Source span of the `_` hole in the original declaration text.
    pub span: clean_parser::Span,
    /// Expected type at the hole, instantiated with the final metavariable
    /// assignments (an unsolved type is reported as-is).
    pub expected_type: Expr,
    /// Local bindings in scope when the hole was elaborated, as
    /// `(name, type)` pairs in binder order. Each type is instantiated with the
    /// final metavariable assignments. May be empty when no locals were in
    /// scope (e.g. a top-level body hole).
    pub local_bindings: Vec<(String, Expr)>,
}

/// Result of elaboration
#[derive(Debug)]
pub enum ElabResult {
    Definition {
        name: Name,
        universe_params: Vec<Name>,
        ty: Expr,
        val: Expr,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    Theorem {
        name: Name,
        universe_params: Vec<Name>,
        ty: Expr,
        proof: Expr,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    Axiom {
        name: Name,
        universe_params: Vec<Name>,
        ty: Expr,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    /// Opaque declaration: type is known, body is hidden from the kernel.
    ///
    /// `opaque name : ty := val` elaborates with both type and value.
    /// `opaque name : ty` elaborates with type only (val is None) and is
    /// registered as an axiom since the kernel has no val-less opaque form.
    Opaque {
        name: Name,
        universe_params: Vec<Name>,
        ty: Expr,
        val: Option<Expr>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    /// Inductive type declaration (multiple constructors)
    ///
    /// E.g.:
    /// ```text
    /// inductive List (α : Type) : Type
    /// | nil : List α
    /// | cons : α → List α → List α
    /// ```
    Inductive {
        /// Inductive type name
        name: Name,
        /// Universe parameters
        universe_params: Vec<Name>,
        /// Number of parameters
        num_params: u32,
        /// Inductive type
        ty: Expr,
        /// Constructors: (name, type)
        constructors: Vec<(Name, Expr)>,
        /// Derived type class instances
        derived_instances: Vec<DerivedInstance>,
        /// Explicit `deriving DeepInduction` marker: registration must run
        /// the deep-induction generator LOUDLY (declines are errors).
        wants_deep_induction: bool,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
        // Note: Recursors (rec, casesOn) are generated by the kernel during add_inductive
        // and can be queried via env.get_recursor("Type.rec") or env.get_recursor("Type.casesOn")
    },
    /// Mutual inductive family: two or more inductive types declared together
    /// inside a `mutual … end` block whose constructors may reference each
    /// other (e.g. `Even`/`Odd`).
    ///
    /// Unlike a run of independent `Inductive` results, the whole family must be
    /// registered in a SINGLE `add_inductive` call so cross-references between
    /// the types resolve and the kernel can build the mutual recursors. The
    /// payload is the fully-elaborated kernel declaration; registration passes
    /// it to `env.add_inductive` verbatim, so the kernel re-checks positivity
    /// and every constructor type.
    MutualInductive {
        /// The combined kernel declaration (all types + constructors).
        decl: clean_kernel::InductiveDecl,
        /// Per-type derived type-class instances (from `deriving` clauses).
        derived_instances: Vec<DerivedInstance>,
        /// Declaration modifiers (private, protected, noncomputable, etc.).
        modifiers: DeclModifiers,
    },
    /// Structure declaration (single-constructor inductive with named fields)
    Structure {
        /// Structure name
        name: Name,
        /// Universe parameters
        universe_params: Vec<Name>,
        /// Number of parameters
        num_params: u32,
        /// Structure type
        ty: Expr,
        /// Constructor name
        ctor_name: Name,
        /// Constructor type (includes parameters and fields)
        ctor_ty: Expr,
        /// Field names (in order)
        field_names: Vec<Name>,
        /// In-file field defaults (`field : Type := value`) as (field name,
        /// elaborated default value). Only closed defaults are recorded; these
        /// are registered so that a structure literal omitting the field fills
        /// it with this value (kernel-re-checked). Empty when no field has a
        /// default.
        field_defaults: Vec<(Name, Expr)>,
        /// Projection functions: (name, type, value) for each field
        /// E.g., for `structure Point where x : Nat  y : Nat`:
        /// - Point.x : Point → Nat, λ s => s.0
        /// - Point.y : Point → Nat, λ s => s.1
        projections: Vec<(Name, Expr, Expr)>,
        /// Shared named-argument binder row for every projection of this
        /// structure: the structure's own binders in declaration order, then
        /// the receiver binder `self` (inst-implicit for a class, explicit for
        /// a structure). Recorded via `set_param_infos` at registration so
        /// `Struct.field (α := T)` named-argument calls resolve instead of
        /// hitting the no-recorded-binder-names descope (B92).
        projection_param_infos: Vec<(String, BinderInfo)>,
        /// Parent subobject fields from an `extends` clause, as
        /// `(toParent_field_name, parent_struct_name)` in constructor order.
        /// Mirrors Lean's subobject layout (`src/Lean/Elab/Structure.lean`):
        /// each parent is embedded as a constructor field `toParent : Parent`,
        /// not flattened. Empty for a structure without `extends`. Registered as
        /// elaborator-only metadata so anonymous-constructor flattening and
        /// structure-literal parent assembly can reconstruct the subobject.
        parents: Vec<(Name, Name)>,
        /// Derived type class instances
        /// E.g., for `deriving Repr, BEq`, contains generated instance definitions
        derived_instances: Vec<DerivedInstance>,
        /// If this is a class declaration (from `class` rather than `structure`)
        /// Contains the class registration info
        class_info: Option<ClassRegistration>,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    /// Type class instance declaration
    ///
    /// An instance provides an implementation of a type class for specific types.
    /// E.g., `instance : Add Nat where add := Nat.add`
    Instance {
        /// Instance name (auto-generated if not provided)
        name: Name,
        /// Universe parameters
        universe_params: Vec<Name>,
        /// The class name this instance implements
        class_name: Name,
        /// The instance type (e.g., `Add Nat`)
        ty: Expr,
        /// The instance value (structure constructor applied to field values)
        val: Expr,
        /// Instance priority (higher = tried first)
        priority: u32,
        /// Declaration modifiers (private, protected, noncomputable, etc.)
        modifiers: DeclModifiers,
    },
    /// An `example` declaration: fully elaborated and kernel-checked, then
    /// DISCARDED — never registered into the environment (B02,
    /// GAP_SWEEP_2026-07-09).
    ///
    /// Lean ground truth: lean4 `src/Lean/Elab/Declaration.lean`
    /// (`elabExample` elaborates the anonymous definition through the same
    /// def-elab pipeline as a named `def`/`theorem` — fully checked — and the
    /// result is inaccessible afterwards). Mirroring that, this variant
    /// carries the elaborated type and value so checkers can count and
    /// re-validate the example as one checked unit, while registration
    /// treats it as a no-op. Before B02 the `Example` arm returned
    /// [`ElabResult::Skipped`], so `clean check` on an example-only file
    /// reported "Checked 0 declarations … 0 passed" with exit 0 — vacuous
    /// success on unverified-looking (actually verified but uncounted,
    /// invisible) content.
    Example {
        /// Elaborated (possibly inferred) type of the example.
        ty: Expr,
        /// Elaborated proof/value term (already kernel-checked against `ty`).
        val: Expr,
    },
    Command(CommandOutput),
    /// Multiple declarations from a namespace or section block
    Multiple(Vec<ElabResult>),
    /// A single inner declaration (e.g. a member of a `namespace`/`section`/
    /// `mutual` block) whose elaboration or kernel check failed.
    ///
    /// Previously a sibling failure inside such a block was propagated with `?`,
    /// which aborted the entire block and dropped every *good* sibling from the
    /// pass/fail tally (the namespace-ABORT bug). Collecting failures as an
    /// explicit `Failed` leaf instead lets the block register and count each
    /// successful inner decl while still recording — and counting — each failure.
    ///
    /// This leaf is NOT registered into the kernel: it represents a declaration
    /// that already failed elaboration/registration. It exists solely so the
    /// checker can attribute one counted failure per failing inner decl with an
    /// accurate span and diagnostic, exactly as a top-level decl failure would.
    Failed {
        /// Best-effort name of the failing inner declaration (for reporting).
        name: String,
        /// The inner surface declaration, retained so the checker can produce a
        /// span-accurate structured failure (the same one a top-level failure
        /// would yield).
        decl: Box<clean_parser::SurfaceDecl>,
        /// The elaboration error that caused this inner decl to fail.
        error: Box<crate::error::ElabError>,
    },
    Skipped,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CommandOutput {
    Check(CheckResult),
    Eval(EvalResult),
    Print(PrintResult),
}

impl ElabResult {
    /// Return the elaborated declaration name when one exists.
    #[must_use]
    pub fn declaration_name(&self) -> Option<&Name> {
        match self {
            Self::Definition { name, .. }
            | Self::Theorem { name, .. }
            | Self::Axiom { name, .. }
            | Self::Opaque { name, .. }
            | Self::Inductive { name, .. }
            | Self::Structure { name, .. }
            | Self::Instance { name, .. } => Some(name),
            // A mutual inductive family has several names; report the first
            // type's name as the representative for the block.
            Self::MutualInductive { decl, .. } => decl.types.first().map(|t| &t.name),
            Self::Multiple(results) => results.iter().find_map(|r| r.declaration_name()),
            // `Failed` carries only a best-effort *string* name (the inner decl
            // never produced a kernel `Name`), so there is no `&Name` to return.
            // `Example` is anonymous by construction (Lean discards it).
            Self::Command(_) | Self::Skipped | Self::Failed { .. } | Self::Example { .. } => None,
        }
    }

    /// Collect every leaf declaration result, flattening any nested
    /// [`Self::Multiple`] blocks produced by `namespace`/`section`/`mutual`.
    ///
    /// Only genuine declaration leaves (those carrying a declaration name, e.g.
    /// `Definition`, `Theorem`, `Inductive`, …) are returned; administrative
    /// `Command`/`Skipped` results are dropped. This lets `clean check` count and
    /// report each declaration inside a namespace block individually instead of
    /// collapsing the whole block into one uncounted unit.
    pub fn leaf_decls<'a>(&'a self, out: &mut Vec<&'a ElabResult>) {
        match self {
            Self::Multiple(results) => {
                for r in results {
                    r.leaf_decls(out);
                }
            }
            Self::Command(_) | Self::Skipped => {}
            // `Failed` is a genuine declaration leaf: it represents one inner
            // decl that was checked and failed. It must be counted as one
            // checked unit (and reported as a failure), so surface it here.
            // Every other variant is a concrete declaration leaf as well.
            _ => out.push(self),
        }
    }

    /// Return the declared type for declaration kinds that elaborate one.
    #[must_use]
    pub fn declaration_type(&self) -> Option<&Expr> {
        match self {
            Self::Definition { ty, .. }
            | Self::Theorem { ty, .. }
            | Self::Axiom { ty, .. }
            | Self::Opaque { ty, .. }
            | Self::Inductive { ty, .. }
            | Self::Structure { ty, .. }
            | Self::Instance { ty, .. } => Some(ty),
            Self::Example { ty, .. } => Some(ty),
            Self::MutualInductive { decl, .. } => decl.types.first().map(|t| &t.type_),
            Self::Multiple(results) => results.iter().find_map(|r| r.declaration_type()),
            Self::Command(_) | Self::Skipped | Self::Failed { .. } => None,
        }
    }

    /// Returns `(type, value)` for declarations that have both.
    #[must_use]
    pub fn type_value_pair(&self) -> Option<(&Expr, &Expr)> {
        match self {
            Self::Definition { ty, val, .. } => Some((ty, val)),
            Self::Theorem { ty, proof, .. } => Some((ty, proof)),
            Self::Instance { ty, val, .. } => Some((ty, val)),
            Self::Example { ty, val } => Some((ty, val)),
            Self::Opaque {
                ty, val: Some(val), ..
            } => Some((ty, val)),
            Self::Multiple(results) => results.iter().find_map(|r| r.type_value_pair()),
            Self::Axiom { .. }
            | Self::Opaque { val: None, .. }
            | Self::Inductive { .. }
            | Self::MutualInductive { .. }
            | Self::Structure { .. }
            | Self::Command(_)
            | Self::Skipped
            | Self::Failed { .. } => None,
        }
    }

    /// Whether this elaboration result is a theorem declaration.
    #[must_use]
    pub fn is_theorem(&self) -> bool {
        matches!(self, Self::Theorem { .. })
    }
}

pub(crate) fn convert_binder_info(info: SurfaceBinderInfo) -> BinderInfo {
    match info {
        SurfaceBinderInfo::Explicit => BinderInfo::Default,
        SurfaceBinderInfo::Implicit => BinderInfo::Implicit,
        SurfaceBinderInfo::StrictImplicit => BinderInfo::StrictImplicit,
        SurfaceBinderInfo::Instance => BinderInfo::InstImplicit,
    }
}

/// Check if a surface expression is an outParam wrapper
pub(in crate::infer) fn is_out_param_type(expr: &SurfaceExpr) -> bool {
    matches!(expr, SurfaceExpr::OutParam(_, _))
}

/// Check if a surface expression is a semiOutParam wrapper
pub(in crate::infer) fn is_semi_out_param_type(expr: &SurfaceExpr) -> bool {
    matches!(expr, SurfaceExpr::SemiOutParam(_, _))
}

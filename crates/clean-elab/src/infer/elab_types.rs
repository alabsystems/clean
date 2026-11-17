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
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId};
use clean_parser::{DeclModifiers, SurfaceBinderInfo, SurfaceExpr, SurfaceName};
use std::collections::HashMap;

/// An original declaration binder, captured before match-arm shadowing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct RecursiveParam {
    /// Binder name as it appears in the local context.
    pub name: SurfaceName,
    /// Original binder visibility, needed when rebuilding IH/motive binders.
    pub binder_info: BinderInfo,
    /// Captured by the recursive binding, rather than supplied at its calls.
    /// Includes autos introduced by captured section-variable domains.
    pub(super) captured_section: bool,
    pub(super) fvar: FVarId,
    pub(super) type_: Expr,
}

/// Context for recursive definition elaboration (#378)
#[derive(Clone, Debug)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(super) struct RecursiveDefContext {
    /// Name of the function being defined
    pub func_name: SurfaceName,
    /// Position among the recursive binding's own explicit arguments.
    /// Captured section parameters are omitted at internal call sites.
    pub decreasing_arg_pos: usize,
    /// Name of the decreasing argument
    pub decreasing_arg_name: SurfaceName,
    /// Inductive type name of the decreasing argument
    pub inductive_type_name: Option<Name>,
    /// Free variable for the inductive hypothesis (set when elaborating match arms)
    pub ih_fvar: Option<FVarId>,
    /// Type of the IH (set when elaborating match arms)
    pub ih_type: Option<Expr>,
    /// Recursive constructor-field FVar identity to its IH. Names alone are
    /// insufficient: a same-named local may shadow a pattern variable.
    pub ih_map: HashMap<FVarId, FVarId>,
    /// Fully-qualified names of *sibling* mutual functions whose calls also
    /// rewrite to induction hypotheses (Track AA: a nested-mutual fold fuses
    /// `Tree.size`/`Tree.sizeList` into one `Tree.rec` application, so inside a
    /// minor body BOTH `Tree.size t` and `Tree.sizeList rest` must be recognized
    /// as recursive self-calls — each resolving to the IH bound for its argument
    /// variable). Empty for ordinary single-function recursion, leaving the
    /// existing `matches_call_name` behavior byte-for-byte unchanged.
    pub sibling_names: Vec<SurfaceName>,
    /// Actual member types elaborated before entering constructor-arm scope.
    pub(super) sibling_types: Vec<(SurfaceName, Expr)>,
    /// Original typed declaration telescope, in binder order.
    pub(super) parameters: Vec<RecursiveParam>,
    /// Binder indices generalized in the current recursive match's motive.
    /// This includes movable prefix parameters, not just the suffix. Prefix
    /// dependencies of the scrutinee type remain fixed recursor parameters.
    pub(super) generalized_params: Vec<usize>,
    /// Original binders supplied as variable indices to an indexed recursor.
    /// Their values vary with the structural child; they are not fixed params
    /// or additional IH arguments.
    pub(super) index_params: Vec<usize>,
    /// Well-founded measure expression from `termination_by` (#1132).
    /// Stored for future well-founded recursion compilation via `WellFounded.fix`.
    /// None for structural recursion or when no measure is provided.
    pub wf_measure: Option<Box<SurfaceExpr>>,
    /// For a `let rec`/`where` helper: the first free-variable id allocated
    /// inside the helper. A local of the helper's own bare name bound before
    /// it (an id below this floor, such as a sibling `where` helper `go`
    /// while a `let rec go` inside another helper elaborates) is shadowed by
    /// the helper, as Lean's `let rec` binds its name over its own body. A
    /// local bound inside the helper (one of its parameters, a pattern
    /// variable) still shadows the helper. `None` for a top-level `def`.
    pub(super) outer_locals_floor: Option<u64>,
}

impl RecursiveDefContext {
    /// Short (final-segment) name of the function being defined, e.g.
    /// `bitWidth` for `TrustIr.Ty.bitWidth`.
    pub(super) fn short_name(&self) -> SurfaceName {
        self.func_name.last_component()
    }

    /// Does an already RESOLVED canonical name denote a recursive member?
    /// Surface spellings must first use the ordinary namespace search with the
    /// pending members included; a dotted suffix is not an identity proof.
    pub(super) fn matches_call_name(&self, candidate: &SurfaceName) -> bool {
        candidate.name() == self.func_name.name()
            || self
                .sibling_names
                .iter()
                .any(|name| candidate.name() == name.name())
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
pub(crate) fn collect_level_params(exprs: &[&Expr]) -> Vec<Name> {
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
    /// `(identity, name, type)` triples in binder order. Each type is instantiated
    /// with the final metavariable assignments. Identities let the renderer
    /// resolve dependent types and distinguish shadowed binders. May be empty
    /// when no locals were in scope (e.g. a top-level body hole).
    pub local_bindings: Vec<(FVarId, String, Expr)>,
}

impl HoleContext {
    /// Render the actual expected type and hypotheses in their captured local
    /// context, using the same identity-aware formatter as tactic goals.
    #[must_use]
    pub fn render(&self) -> (String, Vec<(String, String)>) {
        let config = crate::tactic::display::ExprFormatter::default().with_local_names(
            self.local_bindings
                .iter()
                .map(|(fvar, name, _)| (*fvar, name.clone())),
        );
        let bindings = self
            .local_bindings
            .iter()
            .map(|(fvar, name, ty)| {
                let name = config
                    .local_names
                    .get(fvar)
                    .cloned()
                    .unwrap_or_else(|| name.clone());
                (name, config.format(ty))
            })
            .collect();
        (config.format(&self.expected_type), bindings)
    }
}

/// Result of elaboration
#[derive(Debug)]
pub enum ElabResult {
    /// The enclosed declaration registered successfully. Source diagnostics
    /// (for example compilation errors) do not revoke that registration.
    /// This remains one checked declaration, not an unregistered `Failed` leaf.
    Diagnosed {
        result: Box<ElabResult>,
        diagnostics: Vec<crate::source_diagnostics::SourceDiagnostic>,
    },
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
        /// Explicit `deriving ContainerMap` marker: registration must run the
        /// `C.map` generator LOUDLY (declines are errors), exactly like
        /// `wants_deep_induction`.
        wants_container_map: bool,
        /// Explicit `deriving ContainerRel` marker: same contract for the
        /// `C.rel` relational lifting.
        ///
        /// That is now THREE kernel-side derive booleans travelling together.
        /// A fourth should collapse them into one set rather than adding
        /// another field and another destructuring site.
        wants_container_rel: bool,
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
        projection_param_infos: Vec<(SurfaceName, BinderInfo)>,
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
    /// `#reduce e` (`crate::reduce_command`): Clean's rendering of the term
    /// Lean's `Meta.reduce` returns unchanged, which is not Lean's text.
    Reduce(crate::reduce_command::ReduceResult),
    Print(PrintResult),
    /// `#print axioms c`: Lean 4.8.0's axiom census of each constant `c`
    /// resolved to (`crate::print_axioms`).
    PrintAxioms(crate::print_axioms::PrintAxiomsResult),
    /// A `#guard_msgs` whose expectation matched and whose command declared
    /// nothing (`crate::guard_msgs`). It is a checked assertion, not an
    /// administrative command: the checkers count it as one passing unit
    /// ([`ElabResult::checked_leaves`]).
    GuardMsgs(crate::guard_msgs::GuardMsgsResult),
}

impl ElabResult {
    /// Source errors attached to this result, including nested blocks.
    /// These do not imply that the enclosed kernel declarations were rejected.
    #[must_use]
    pub fn source_error_message(&self) -> Option<String> {
        let messages: Vec<String> = match self {
            Self::Diagnosed {
                result,
                diagnostics,
            } => result
                .source_error_message()
                .into_iter()
                .chain(diagnostics.iter().map(|d| d.error.to_string()))
                .collect(),
            Self::Multiple(results) => results
                .iter()
                .filter_map(Self::source_error_message)
                .collect(),
            _ => Vec::new(),
        };
        (!messages.is_empty()).then(|| messages.join("\n"))
    }

    /// Consume source diagnostics after a successful `#guard_msgs` comparison.
    /// The actual declarations and their registered values remain intact.
    pub(crate) fn without_source_diagnostics(self) -> Self {
        match self {
            Self::Diagnosed { result, .. } => result.without_source_diagnostics(),
            Self::Multiple(results) => Self::Multiple(
                results
                    .into_iter()
                    .map(Self::without_source_diagnostics)
                    .collect(),
            ),
            other => other,
        }
    }

    /// Every name a checked declaration's verdict rests on: the declaration's own
    /// registered names, and every constant its elaborated type/value/constructor
    /// terms mention. An `example` is never registered, so its terms are the only
    /// way to reach its cone.
    #[must_use]
    pub fn cited_roots(&self, env: &clean_kernel::Environment) -> std::collections::BTreeSet<Name> {
        let mut refs: std::collections::HashSet<Name> = std::collections::HashSet::new();
        let mut names: Vec<&Name> = Vec::new();
        // A DAG walk: a term whose subterms are shared (a match's copied
        // right-hand side, G15/G76) can be a tree far larger than its distinct
        // nodes.
        let mut add = |e: &Expr| e.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
        match self {
            Self::Definition { name, ty, val, .. } | Self::Instance { name, ty, val, .. } => {
                names.push(name);
                add(ty);
                add(val);
            }
            Self::Theorem {
                name, ty, proof, ..
            } => {
                names.push(name);
                add(ty);
                add(proof);
            }
            Self::Axiom { name, ty, .. } => {
                names.push(name);
                add(ty);
            }
            Self::Opaque { name, ty, val, .. } => {
                names.push(name);
                add(ty);
                if let Some(val) = val {
                    add(val);
                }
            }
            Self::Inductive {
                name,
                ty,
                constructors,
                ..
            } => {
                names.push(name);
                add(ty);
                for (ctor, ctor_ty) in constructors {
                    names.push(ctor);
                    add(ctor_ty);
                }
            }
            Self::MutualInductive { decl, .. } => {
                for ty in &decl.types {
                    names.push(&ty.name);
                    add(&ty.type_);
                    for ctor in &ty.constructors {
                        names.push(&ctor.name);
                        add(&ctor.type_);
                    }
                }
            }
            Self::Structure {
                name,
                ty,
                ctor_name,
                ctor_ty,
                projections,
                field_defaults,
                ..
            } => {
                names.push(name);
                names.push(ctor_name);
                add(ty);
                add(ctor_ty);
                for (proj, proj_ty, proj_val) in projections {
                    names.push(proj);
                    add(proj_ty);
                    add(proj_val);
                }
                for (_, default) in field_defaults {
                    add(default);
                }
            }
            Self::Example { ty, val, .. } => {
                add(ty);
                add(val);
            }
            Self::Multiple(_) | Self::Command(_) | Self::Skipped | Self::Failed { .. } => {}
            Self::Diagnosed { result, .. } => return result.cited_roots(env),
        }
        let mut roots: std::collections::BTreeSet<Name> = refs.into_iter().collect();
        for name in names {
            if env.get_const(name).is_some() {
                roots.insert(name.clone());
            }
        }
        roots
    }

    /// Return the elaborated declaration name when one exists — for a
    /// declaration that lifted `where` / `let rec` helpers, the declaration's
    /// own name, never a helper's ([`Self::primary_leaf`]).
    #[must_use]
    pub fn declaration_name(&self) -> Option<&Name> {
        match self {
            Self::Diagnosed { result, .. } => result.declaration_name(),
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
            Self::Multiple(results) => match Self::lifted_helpers_parent(results) {
                Some(parent) => parent.declaration_name(),
                None => results.iter().find_map(|r| r.declaration_name()),
            },
            // `Failed` carries only a best-effort *string* name (the inner decl
            // never produced a kernel `Name`), so there is no `&Name` to return.
            // `Example` is anonymous by construction (Lean discards it).
            Self::Command(_) | Self::Skipped | Self::Failed { .. } | Self::Example { .. } => None,
        }
    }

    /// The declaration a result for ONE source declaration is about: itself
    /// for a single declaration; for `parent` with the auxiliaries it lifted
    /// — `Multiple([parent.go…, parent])`, auxiliaries first so they register
    /// first (`crate::infer::let_rec_lift`, and the course-of-values
    /// `parent.cov`) — the parent; for a type with failed `deriving` classes
    /// beside it — `Multiple([T, Failed…])` — the type. `None` for any other
    /// block (a `namespace` or `mutual` block is about no one declaration)
    /// and for a result that declares nothing.
    ///
    /// Callers that ask about "the declaration" (its parameter names, its
    /// editor info, its staged header) read this rather than matching a lone
    /// `Definition`, which a declaration with a helper is not.
    #[must_use]
    pub fn primary_leaf(&self) -> Option<&ElabResult> {
        match self {
            Self::Diagnosed { result, .. } => result.primary_leaf(),
            Self::Multiple(results) => {
                if let Some(parent) = Self::lifted_helpers_parent(results) {
                    return Some(parent);
                }
                let (first, rest) = results.split_first()?;
                let only_failed_beside = !rest.is_empty()
                    && rest.iter().all(|r| matches!(r, Self::Failed { .. }))
                    && !matches!(first, Self::Multiple(_));
                if only_failed_beside {
                    first.primary_leaf()
                } else {
                    None
                }
            }
            Self::Command(_) | Self::Skipped | Self::Failed { .. } | Self::Example { .. } => None,
            _ => Some(self),
        }
    }

    /// The parent of `[parent.go…, parent]`: the last result, when it is a
    /// single named declaration and every result before it is a declaration
    /// strictly under its name — the shape `let_rec_lift` builds, and only it
    /// (a `namespace` block's members are siblings, never under one another).
    fn lifted_helpers_parent(results: &[ElabResult]) -> Option<&ElabResult> {
        let (last, helpers) = results.split_last()?;
        if helpers.is_empty() || matches!(last, Self::Multiple(_)) {
            return None;
        }
        let parent = last.declaration_name()?;
        helpers
            .iter()
            .all(|helper| {
                !matches!(helper, Self::Multiple(_))
                    && helper.declaration_name().is_some_and(|name| {
                        name != parent && crate::namespace::name_has_prefix(name, parent)
                    })
            })
            .then_some(last)
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

    /// Refuse a [`Self::Multiple`] that still holds declaration leaves.
    ///
    /// THE K5 VACUOUS PASS, PINNED WHERE IT HAPPENED (2026-09-17). A `namespace` /
    /// `section` / `mutual` block elaborates to one `Multiple` holding its members.
    /// Answering "this is administrative, skip it" for such a block does not skip a
    /// command — it skips every declaration inside it, silently, and the run then
    /// reports `0 checked, 0 failed, pass`. `clean project check` did exactly that
    /// on a 1,580-declaration package and did not refuse a deliberate type error
    /// inside a namespace (`reports/2026-09-17-clean-authority-project-check-vacuous.md`).
    ///
    /// Every caller that validates one declaration at a time must flatten with
    /// [`Self::leaf_decls`] first. This turns the mistake into a loud failure
    /// instead of a green run. A block that really holds nothing — an empty
    /// namespace, or one holding only `#command` / `set_option` — is genuinely
    /// administrative and returns `None`.
    #[must_use]
    pub fn unflattened_block_refusal(&self) -> Option<String> {
        if !matches!(self, Self::Multiple(_)) {
            return None;
        }
        let mut leaves: Vec<&ElabResult> = Vec::new();
        self.leaf_decls(&mut leaves);
        (!leaves.is_empty()).then(|| {
            format!(
                "internal: a namespace/section/mutual block holding {} declaration(s) reached the \
                 single-declaration checker unflattened; it must be flattened with `leaf_decls` so \
                 every member is checked",
                leaves.len()
            )
        })
    }

    /// [`Self::leaf_decls`] plus every passing `#guard_msgs` that declared
    /// nothing ([`CommandOutput::GuardMsgs`]): the units a CHECKER counts.
    ///
    /// A `#guard_msgs` is an assertion, so a file of nothing but passing
    /// `#guard_msgs in #print axioms c` audits checked something; reporting it
    /// as `nothing_checked` would misstate the run. It is kept out of
    /// `leaf_decls` because that one's callers hand every leaf to read-only
    /// kernel validation, and a message comparison has no term to re-check.
    pub fn checked_leaves<'a>(&'a self, out: &mut Vec<&'a ElabResult>) {
        match self {
            Self::Multiple(results) => {
                for r in results {
                    r.checked_leaves(out);
                }
            }
            Self::Command(CommandOutput::GuardMsgs(_)) => out.push(self),
            Self::Command(_) | Self::Skipped => {}
            _ => out.push(self),
        }
    }

    /// Whether this is a checked assertion command — a passing `#guard_msgs`
    /// that declared nothing — rather than an administrative one. Checkers
    /// count it as one passing unit (see [`Self::checked_leaves`]).
    #[must_use]
    pub fn is_checked_command(&self) -> bool {
        matches!(self, Self::Command(CommandOutput::GuardMsgs(_)))
    }

    /// Return the declared type for declaration kinds that elaborate one.
    #[must_use]
    pub(crate) fn declaration_type(&self) -> Option<&Expr> {
        match self {
            Self::Diagnosed { result, .. } => result.declaration_type(),
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

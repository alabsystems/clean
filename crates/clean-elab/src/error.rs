// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration error types.

use crate::agent_diagnostics::AgentDiagnostic;
use crate::tactic::TacticError;
use clean_kernel::Name;

/// Errors that can occur during elaboration.
///
/// Elaboration converts surface syntax to kernel terms, performing type inference,
/// implicit argument insertion, and macro expansion. These errors indicate
/// semantic problems that prevent successful elaboration.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ElabError {
    /// An internal elaborator scope/state invariant was violated.
    ///
    /// This is a compiler defect, not unsupported source syntax.  Keep it as a
    /// typed error so malformed or adversarial input cannot turn a recoverable
    /// elaboration failure into a process panic.
    #[error("Internal elaboration invariant violated: {0}")]
    InternalInvariant(String),
    /// Type mismatch between expected and actual types.
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },
    /// A finalized declaration still contains unresolved variables — either
    /// metavariable-tagged FVars (an implicit argument no unification could
    /// ever constrain: phantom section binders, an untyped alias desugar, a
    /// failed instance synthesis fallback) or a genuine local FVar that
    /// escaped abstraction (e.g. a dropped section variable). Fail-closed
    /// here: without this guard both classes reach the kernel and die as an
    /// opaque "contains free variables".
    #[error("{decl_kind} {name}: elaboration left unresolved variables ({detail})")]
    ResidualFreeVariables {
        /// Declaration kind ("def", "theorem", "instance").
        decl_kind: String,
        /// Declaration name as registered.
        name: String,
        /// Classified id list: which are unsolved metas vs escaped locals.
        detail: String,
    },
    /// Reference to an identifier that is not in scope.
    #[error("Unknown identifier: {0}")]
    UnknownIdent(String),
    /// Reference to an identifier that is not in scope, with nearest theorem names.
    #[error(
        "Unknown identifier: {name}; nearest theorem names: {}",
        suggestions.join(", ")
    )]
    UnknownIdentWithSuggestions {
        /// Unresolved identifier.
        name: String,
        /// Nearest theorem names in the current environment.
        suggestions: Vec<String>,
    },
    /// A bare identifier matches a `protected` declaration in an opened
    /// namespace: a simple `open` does not shorten protected names (Lean
    /// `ResolveName.lean` skips them in `OpenDecl.simple` resolution), so the
    /// fix is the qualified name (gap sweep B13, namespaces_scoping/p16).
    #[error(
        "Unknown identifier: {name} (`{qualified}` is protected — \
         `open {namespace_}` does not shorten it; use `{qualified}`)"
    )]
    ProtectedIdent {
        /// The bare identifier as written.
        name: String,
        /// The protected declaration it would have matched.
        qualified: String,
        /// The opened namespace containing the protected declaration.
        namespace_: String,
    },
    /// Type inference failed to determine a type.
    #[error("Cannot infer type")]
    CannotInfer,
    /// Projection applied to an expression that is not a structure.
    #[error("Invalid projection target: {0}")]
    InvalidProjectionTarget(String),
    /// Structure field does not exist.
    #[error(
        "Unknown projection field {field} on structure {struct_name}; nearest fields: {}",
        suggestions.join(", ")
    )]
    UnknownProjectionField {
        struct_name: Name,
        field: String,
        suggestions: Vec<String>,
    },
    /// Structure literal provided a field that the target structure does not have.
    #[error(
        "Unknown structure field {field} on {struct_name}; nearest fields: {}",
        suggestions.join(", ")
    )]
    UnknownStructureField {
        /// Target structure.
        struct_name: Name,
        /// Provided field name.
        field: String,
        /// Nearest declared field names.
        suggestions: Vec<String>,
    },
    /// Structure literal omitted one or more required fields.
    #[error("Missing field(s) for {struct_name}: {}", fields.join(", "))]
    MissingStructureFields {
        /// Target structure.
        struct_name: Name,
        /// Missing fields.
        fields: Vec<String>,
    },
    /// Structure literal field value failed against the expected field type.
    #[error("Field {struct_name}.{field} has type {actual}, expected {expected}")]
    StructureFieldTypeMismatch {
        /// Target structure.
        struct_name: Name,
        /// Field being elaborated.
        field: String,
        /// Expected field type.
        expected: String,
        /// Actual field type or elaboration failure summary.
        actual: String,
    },
    /// Field index exceeds the number of fields in the structure.
    #[error("Projection index {idx} out of bounds for {struct_name} (fields: {field_count})")]
    ProjectionIndexOutOfBounds {
        struct_name: Name,
        idx: u32,
        field_count: u32,
    },
    /// Type-class instance synthesis failed for a required goal.
    ///
    /// Introduced for the strict lean4-core monad gate (Brick B07,
    /// GAP_SWEEP_2026-07-09 OVER_ACCEPT-01): mirrors real Lean's
    /// "failed to synthesize Monad List" rejection for `do`-blocks over
    /// monads that Lean core provides no instance for.
    #[error("failed to synthesize instance {class_name} for goal {goal}")]
    FailedToSynthesize {
        /// The class whose instance could not be synthesized.
        class_name: Name,
        /// Rendered synthesis goal (e.g. `Monad List`).
        goal: String,
    },
    /// A Mathlib-only surface construct was used under the strict
    /// `--prelude lean4-core` lane, where Lean 4 core rejects it (usually at
    /// parse time). Introduced for `Type*` (GAP_SWEEP_2026-07-09 universes/p09),
    /// paralleling the B07 strict monad-instance gate: real-Lean parity means a
    /// LOUD reject rather than a silent fresh-universe accept.
    #[error("`{syntax}` is Mathlib-only and rejected under --prelude lean4-core: {hint}")]
    Lean4CoreOnlySyntax {
        /// The rejected surface syntax, e.g. `Type*`.
        syntax: &'static str,
        /// Guidance on the core-compatible spelling, e.g. `use \`Type _\` or \`Type u\``.
        hint: &'static str,
    },
    /// Kernel rejected a declaration during full type checking.
    #[error("Kernel check failed for {name}: {detail}")]
    KernelCheckFailed { name: Name, detail: String },
    /// Environment registration failed after elaboration produced a declaration.
    #[error("Kernel registration failed during {operation}: {detail}")]
    KernelRegistrationFailed { operation: String, detail: String },
    /// Feature is recognized but not yet implemented.
    #[error("Not implemented: {0}")]
    NotImplemented(String),
    /// Surface syntax failed to parse.
    #[error("Parse error: {0}")]
    ParseError(String),
    /// Macro expansion encountered an error.
    #[error("Macro expansion failed: {0}")]
    MacroError(String),
    /// Anonymous constructor `⟨⟩` used without an expected type to infer from.
    #[error("Anonymous constructor ⟨⟩ requires expected type, but none found")]
    AnonymousCtorNoExpectedType,
    /// Anonymous constructor `⟨⟩` used with a non-inductive expected type.
    #[error("Anonymous constructor ⟨⟩ expected inductive type, got {0}")]
    AnonymousCtorNotInductive(String),
    /// Anonymous constructor `⟨⟩` used with a multi-constructor inductive type.
    #[error(
        "Anonymous constructor ⟨⟩ requires single-constructor type, but {0} has {1} constructors"
    )]
    AnonymousCtorNotSingleCtor(Name, usize),
    /// Reference to a structure that is not defined.
    #[error("Unknown structure: {name}")]
    UnknownStruct { name: String },
    /// Feature is not supported by the elaborator.
    #[error("Unsupported feature: {feature}")]
    Unsupported { feature: String },
    /// Function applied to more arguments than its type allows.
    #[error("Too many arguments: function type {func_type} is not a function type, but {remaining_args} argument(s) remain")]
    TooManyArguments {
        func_type: String,
        remaining_args: usize,
    },
    /// Term-level `▸` (subst) elaboration failed: non-equality equation,
    /// neither equality side occurs where required, or the inferred motive is
    /// not type-correct. Mirrors Lean's `elabSubst` "invalid `▸` notation"
    /// errors — always loud; the motive is never guessed.
    #[error("invalid `▸` notation: {detail}")]
    InvalidSubst {
        /// Human-readable description of which `elabSubst` step failed.
        detail: String,
    },
    /// The `xs[i]` bounds obligation could not be discharged by the
    /// `get_elem_tactic` analog (Brick 4). Mirrors Lean's `get_elem_tactic`
    /// "failed to prove index is valid" diagnostic — always loud; the proof
    /// hole is never left as a metavariable and never filled with `sorry`.
    #[error("failed to prove index is valid (get_elem_tactic analog tried {tried}), goal: {goal}; provide the proof explicitly with `xs[i]'h`, or use `xs[i]!` / `xs[i]?`")]
    GetElemValidUnproved {
        /// The pinned `valid xs i` proof obligation.
        goal: String,
        /// The tactic chain that was attempted.
        tried: String,
    },
    /// Match arm body type does not match the motive inferred from the first arm.
    #[error("Match arm {arm_index} has type {actual}, but match motive expects {expected}")]
    MatchArmTypeMismatch {
        arm_index: usize,
        expected: String,
        actual: String,
    },
    /// Constructor pattern uses the wrong number of field patterns.
    #[error(
        "{context}: constructor {ctor_name} expects {expected} field pattern(s), got {actual}"
    )]
    ConstructorPatternArityMismatch {
        context: String,
        ctor_name: String,
        expected: usize,
        actual: usize,
    },
    /// A tactic failed during tactic block elaboration.
    #[error("Tactic failed: {0}")]
    TacticFailed(#[source] TacticError),
    /// A user metaprogram (term/tactic elaborator body) raised a custom error via
    /// `throwError "msg"` (or an alias). The `message` is the literal string the
    /// user passed. This is a plain typed diagnostic: it closes no goal, accepts
    /// no term, and fabricates nothing — it only makes elaboration FAIL with
    /// exactly the user's message.
    #[error("{message}")]
    UserThrowError { message: String },
    /// Post-hoc proof type check failed: the assembled proof term's type
    /// does not match the expected goal type. This is the hard gate at
    /// the tactic elaboration boundary (Phase 2 of #2154/#2201).
    #[error("Proof type mismatch: expected {expected}, got {actual}")]
    ProofTypeMismatch { expected: String, actual: String },
    /// Type class instance synthesis failed for a fully-determined goal
    /// (B06, GAP_SWEEP_2026-07-09).
    ///
    /// Raised when an instance-implicit argument's goal type is GROUND (no
    /// remaining metavariables — later unification cannot change it) and no
    /// registered or local instance inhabits it. Before B06 the unassigned
    /// instance metavariable leaked into the declaration and surfaced far
    /// from the cause as the kernel's "Declaration contains free variables"
    /// rejection. Lean ground truth: "failed to synthesize <goal>"
    /// (lean4 `src/Lean/Meta/SynthInstance.lean`, `synthInstance` failure).
    #[error("failed to synthesize instance `{goal}`")]
    FailedToSynthesizeInstance {
        /// Rendered instance goal (e.g. `Hm Int`).
        goal: String,
    },
    /// Universe instance `.{{u, v}}` applied to a non-constant expression.
    #[error("Universe instance applied to non-constant expression")]
    UniverseInstNotConst,
    /// Universe instance `.{{...}}` count does not match the constant's
    /// number of universe parameters.
    #[error("Universe level count mismatch for {name}: expected {expected}, got {actual}")]
    UniverseLevelMismatch {
        name: String,
        expected: usize,
        actual: usize,
    },
    /// Named-argument binding failed (B01, GAP_SWEEP_2026-07-09).
    ///
    /// A named argument `(name := v)` must bind the binder with that exact
    /// name — never a positional slot. Unknown names, double-filled binders,
    /// and function heads whose binder names are unavailable are all LOUD
    /// errors: before B01 these fell back to *silent positional binding*, so
    /// `Point.mk (y := 2) (x := 1)` elaborated as `Point.mk 2 1` and the
    /// kernel certified the swapped fields.
    /// Lean ground truth: lean4 `src/Lean/Elab/App.lean` (`ElabAppArgs`:
    /// named args bind by binder name; positional args fill the remaining
    /// explicit binders in order).
    #[error("invalid named argument `({name} := …)` for `{func}`: {reason}")]
    NamedArgBindingFailed {
        /// Function head the named argument was applied to.
        func: String,
        /// The named argument's name.
        name: String,
        /// Why binding failed (unknown name / already bound / binder names
        /// unavailable for this head).
        reason: String,
    },
    /// A `where`-clause / `let rec` local definition has a shape the
    /// elaborator cannot lower to a real kernel value. Always loud: the
    /// pre-2026-07 behavior silently registered the enclosing declaration
    /// with a synthetic `sorry` placeholder value (audit d04,
    /// docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md); that fallback is
    /// eliminated — an unsupported shape now fails the whole declaration.
    #[error("unsupported `where`/`let rec` local definition `{name}`: {shape}")]
    WhereLetRecUnsupported {
        /// Name of the local helper definition.
        name: String,
        /// Description of the unsupported shape.
        shape: String,
    },
    /// A `match h : e with …` (annotated discriminant, Lean
    /// `Lean/Parser/Term.lean:275 matchDiscr` / `Lean/Elab/Match.lean:67`)
    /// combined with a match sub-shape the equality-hypothesis lowering does
    /// not support yet (audit d01, docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md).
    /// Always a LOUD failure of the whole declaration — the hypothesis is
    /// never silently dropped and never discharged with `sorry`.
    #[error("unsupported `match {hyp} : …` shape: {shape}")]
    MatchDiscrHypUnsupported {
        /// The discriminant-hypothesis name (`h` in `match h : e with`).
        hyp: String,
        /// Description of the unsupported sub-shape.
        shape: String,
    },
}

/// Domain-prefixed alias for collision-free imports.
///
/// Use `ElabElabError` when importing from multiple crates with `ElabError` types.
pub type ElabElabError = ElabError;

impl From<TacticError> for ElabError {
    fn from(err: TacticError) -> Self {
        Self::TacticFailed(err)
    }
}

impl ElabError {
    /// Return machine-readable diagnostics attached to this elaboration error.
    #[must_use]
    pub fn agent_diagnostics(&self) -> Vec<AgentDiagnostic> {
        match self {
            Self::UnknownIdentWithSuggestions { name, suggestions } => {
                let mut diag = AgentDiagnostic::error(
                    "ident.nearest_theorems",
                    format!("unknown identifier `{name}`"),
                )
                .with_fact("identifier", name.clone());
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("nearest theorem `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            Self::UnknownProjectionField {
                struct_name,
                field,
                suggestions,
            } => {
                let mut diag = AgentDiagnostic::error(
                    "structure.unknown_projection_field",
                    format!("unknown projection field `{field}` in `{struct_name}`"),
                )
                .with_facts([
                    ("structure", struct_name.to_string()),
                    ("field", field.clone()),
                    ("context", "projection".to_owned()),
                ]);
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("replace `{field}` with `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            Self::UnknownStructureField {
                struct_name,
                field,
                suggestions,
            } => {
                let mut diag = AgentDiagnostic::error(
                    "structure.unknown_field",
                    format!("unknown field `{field}` in `{struct_name}`"),
                )
                .with_facts([
                    ("structure", struct_name.to_string()),
                    ("field", field.clone()),
                ]);
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("replace `{field}` with `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            Self::MissingStructureFields {
                struct_name,
                fields,
            } => vec![AgentDiagnostic::error(
                "structure.missing_fields",
                format!("missing required field(s) for `{struct_name}`"),
            )
            .with_facts([
                ("structure", struct_name.to_string()),
                ("fields", fields.join(",")),
            ])],
            Self::StructureFieldTypeMismatch {
                struct_name,
                field,
                expected,
                actual,
            } => vec![AgentDiagnostic::error(
                "structure.field_type_mismatch",
                format!("field `{struct_name}.{field}` has the wrong type"),
            )
            .with_facts([
                ("structure", struct_name.to_string()),
                ("field", field.clone()),
                ("expected", expected.clone()),
                ("actual", actual.clone()),
            ])],
            Self::TacticFailed(err) => err.agent_diagnostics(),
            _ => Vec::new(),
        }
    }
}

impl From<crate::options_registry::OptionError> for ElabError {
    /// Map a command-level `set_option` validation failure onto a loud
    /// elaboration error (gap sweep B21). An unknown option becomes an
    /// unknown-identifier error; a wrong-typed value becomes a type mismatch.
    fn from(err: crate::options_registry::OptionError) -> Self {
        use crate::options_registry::OptionError;
        match err {
            OptionError::UnknownOption { name } => {
                ElabError::UnknownIdent(format!("unknown option '{name}'"))
            }
            OptionError::TypeMismatch {
                name,
                expected,
                actual,
            } => ElabError::TypeMismatch {
                expected: format!("{expected} (option '{name}')"),
                actual: actual.to_string(),
            },
        }
    }
}

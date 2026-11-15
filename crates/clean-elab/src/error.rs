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
    /// A do block requires a type constructor application into Type.
    #[error("invalid `do` notation, expected type is not a monad application\n  {type_}\nUse `Id.run do` for pure code")]
    InvalidDoExpectedType { type_: String },
    /// A declaration in a do sequence shadows a still-active mutable local.
    #[error("mutable variable `{name}` cannot be shadowed")]
    MutableVariableShadowing { name: String },
    /// A surface command cannot use another source world's semantics.
    #[error("source world refused: {0}")]
    SourceWorld(String),
    /// A declaration or forall binder uses `[...]` for a non-class type.
    #[error("invalid binder annotation, type is not a class instance: {type_}")]
    InvalidInstanceBinder { type_: String },
    /// An explicit local-instance parameter cannot be recovered by resolution.
    #[error("invalid parametric local instance, parameter with type {type_} does not have forward dependencies")]
    InvalidParametricLocalInstance { type_: String },
    /// An internal elaborator scope/state invariant was violated.
    ///
    /// This is a compiler defect, not unsupported source syntax.  Keep it as a
    /// typed error so malformed or adversarial input cannot turn a recoverable
    /// elaboration failure into a process panic.
    #[error("Internal elaboration invariant violated: {0}")]
    InternalInvariant(String),
    /// Type mismatch between expected and actual types. A private constant
    /// is shown by its user name, as Lean 4.8.0 prints it (G21).
    #[error(
        "Type mismatch: expected {}, got {}",
        crate::private_names::user_facing_text(expected),
        crate::private_names::user_facing_text(actual)
    )]
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
    /// A finalized declaration left an INSTANCE-SYNTHESIS goal unfilled.
    ///
    /// The same failure `ResidualFreeVariables` used to report as
    /// `unsolved metavariables ?[7]`. The metavariable id names nothing a
    /// reader can act on — it is an allocation counter, and the SAME id
    /// appears for unrelated programs — while the goal that failed to
    /// synthesize is still in hand at the reporting site (`MetaVar.ty`).
    ///
    /// Distinct from [`Self::FailedToSynthesizeInstance`], which fires
    /// EAGERLY inside the argument loop when the goal is already ground.
    /// This one fires at declaration close, which is where the two measured
    /// evasions of that eager check land: a goal that is still open when the
    /// loop settles, and the B104 homogeneous-retry, which deliberately
    /// un-grounds the goal the eager check requires to be ground. At decl
    /// close "no later unification will run" is a fact rather than a guess.
    ///
    /// The message states only what is derivable: the goal, and the candidate
    /// list the search actually had. It never claims the goal is
    /// unsatisfiable in principle.
    #[error("{decl_kind} {name}: failed to synthesize instance `{goal}`\n{detail}")]
    UnsynthesizedInstanceGoal {
        /// Declaration kind ("def", "theorem", "instance").
        decl_kind: String,
        /// Declaration name as registered.
        name: String,
        /// Rendered instance goal, e.g. `HMod UInt64 UInt64 UInt64`.
        goal: String,
        /// Candidate list plus the options a reader can take.
        detail: String,
    },
    /// The declaration spent its whole automation work budget
    /// (`clean check --automation-budget`), and failed after it did.
    ///
    /// Clean's analogue of Lean's `throwMaxHeartbeat` "(deterministic)
    /// timeout …, maximum number of heartbeats … has been reached"
    /// (`Lean.Core.checkMaxHeartbeatsCore`, `src/lean/Lean/CoreM.lean`). Once
    /// the budget is spent every automation call of the declaration gives up
    /// (`clean-auto`'s `work_budget.rs`), so `underlying` — the error the
    /// declaration then failed with — is what the script could do without
    /// automation, not evidence that the goal is out of reach. It is kept in
    /// the message verbatim so the failure stays classifiable by what the
    /// script was doing.
    #[error(
        "(deterministic) automation budget exhausted: the declaration spent all {limit} \
         units of its automation work budget (exhausted in `{site}`); raise it with \
         `--automation-budget <n>`, or 0 for unlimited. It then failed with: {underlying}"
    )]
    AutomationBudgetExhausted {
        /// The per-declaration limit, in automation work units.
        limit: u64,
        /// The automation site whose charge found the budget spent.
        site: String,
        /// The error the declaration failed with after the budget ran out.
        underlying: Box<ElabError>,
    },
    /// Reference to an identifier that is not in scope, whose "nearest
    /// theorem names" have NOT been computed.
    ///
    /// Computing them is a Levenshtein scan over every accessible theorem in
    /// the environment, and most unknown-identifier errors are never reported:
    /// they are raised on SPECULATIVE paths that catch them and try something
    /// else — a pattern name tried as a constructor before it is bound as a
    /// variable (`elab_match/name_classification.rs`), a dotted name's prefix
    /// tried as a receiver before the qualified constant
    /// (`infer/elab_proj.rs`). Measured by the performance audit
    /// (`reports/lean4-replacement-audit-2026-09-24/performance.json`) at
    /// 4-15% of `Mathlib/Logic/Basic.lean`'s elaboration, under exactly those
    /// two callers. So the scan runs only for the error that is REPORTED:
    /// [`ElabError::with_ident_suggestions`] turns this into
    /// [`ElabError::UnknownIdentWithSuggestions`] (or [`ElabError::UnknownIdent`]
    /// when nothing is near) at the declaration boundary, with the namespace
    /// the identifier was written in, which decides what is accessible.
    /// Unmaterialized, it renders exactly as [`ElabError::UnknownIdent`].
    #[error("Unknown identifier: {name}")]
    UnknownIdentDeferred {
        /// Unresolved identifier.
        name: String,
        /// The namespace the identifier was written in (private names are
        /// suggested only inside their own namespace).
        namespace_prefix: Name,
        /// What to report instead when nothing is near `name`. Upstream's
        /// dotted-name fallback (`infer/elab_proj.rs`) forwards the QUALIFIED
        /// name only when it carries suggestions and otherwise reports the
        /// base-name error; whether suggestions exist is decided only when the
        /// error is reported, so the base error rides along until then.
        fallback: Option<Box<ElabError>>,
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
    /// Dot notation `recv.field` whose target did not resolve, on a receiver
    /// whose type has no nameable head after normalisation.
    ///
    /// This is the NAMED form of what used to surface as
    /// `NotImplemented("cannot extract type name from <raw Expr dump>")` at
    /// the dot-notation site (`infer/elab_proj.rs`) — 44 of the 497 failures
    /// in the 2026-08-25 five-file Mathlib-source measurement, the second
    /// largest single-mechanism class on that frontier
    /// (`docs/analysis/frontier-next-class-2026-08-25.md` §5). The old message
    /// deleted the identifier that failed to resolve and printed the
    /// receiver's `whnf`'d type instead, which is why the class could not be
    /// triaged from the artifact at all.
    ///
    /// It is a MISSING NAME, not a missing feature. `get_type_name`
    /// (`infer/elab_match/helpers.rs`) normalises before reading the head, so
    /// a `def`-based alias (`Function.Surjective f` → `∀ b, ∃ a, f a = b`) or
    /// a projection stuck on an opaque instance variable (`a ≤ b` →
    /// `Proj(LE, 0, Proj(Preorder, 0, …))`) loses its head there. But the
    /// un-reduced head has ALREADY been tried by the Track-UU pre-whnf lookup
    /// earlier in the same function, so when this is raised the named
    /// identifier is known not to resolve — which is what makes naming it
    /// honest rather than speculative. Measured on this box: four probes whose
    /// dot target DOES resolve, in exactly these receiver shapes, all pass
    /// (`tests/fixtures/source_frontier/p01,p04,p07,p13`).
    ///
    /// Message shape is load-bearing twice over. `Unknown identifier:` leads
    /// so the source-elab classifier
    /// (`scripts/srcelab_classify.py`, first-match-wins) files these under
    /// `unknown identifier` rather than `not implemented (elaborator NYI)`,
    /// and so the name survives the 400-char truncation of `per_error_class`.
    /// `dot notation` then keeps them separable from the pre-existing
    /// unknown-identifier population in the same report.
    #[error(
        "Unknown identifier: {name}; dot notation `.{field}` on a receiver of type \
         `{receiver}`, whose head does not name a type after reduction ({normalized_head})"
    )]
    UnresolvedDotTarget {
        /// The identifier that failed to resolve: `<Head>.<field>` when the
        /// receiver type's un-reduced head is a constant, else the bare field.
        name: String,
        /// The field written after the dot.
        field: String,
        /// The receiver's type as inferred, BEFORE normalisation.
        receiver: String,
        /// Compact shape of the receiver type's head after normalisation —
        /// the discriminator between this class's sub-shapes (`Pi` for the
        /// unfolded-alias face, `Proj(S, i)` for the stuck-projection face).
        normalized_head: String,
    },
    /// The unresolved identifier IS the name of the declaration being
    /// elaborated, so this is a RECURSIVE definition whose form no recursion
    /// lowering accepted — not a missing name and not a typo.
    ///
    /// Nothing about what elaborates changes when this fires: it is raised at
    /// the point where resolution has ALREADY failed, in place of the
    /// name-distance suggestion list, whose nearest-theorem answer for a
    /// self-reference (`gcd` → `Quotient.ind`) is actively misleading. Clean
    /// lowers exactly two recursion shapes today — structural recursion
    /// through the inductive type's recursor (`infer/structural/`) and
    /// well-founded recursion with a `termination_by` measure naming ONE
    /// parameter (`infer/wf_recursion/`, limits in `wf_recursion/mod.rs`;
    /// the signature may be wider than the measure) — so the refusal states
    /// that boundary and the ways across it rather than guessing at a
    /// spelling.
    #[error(
        "`{name}` is the name being defined: a self-reference in a def body is \
         a recursive definition, not a missing name. Recursive definitions are \
         supported for structural recursion (match/equation form on a \
         structurally decreasing parameter) and for well-founded recursion \
         whose `termination_by` measure names ONE parameter; the form of \
         `{decl}` ({params} parameter(s); neither lowering applied: {detail}) is \
         outside today's fragment.\n  \
         help: ways forward, in order of preference — (1) restate `{decl}` \
         structurally: match on one parameter and recurse on its immediate \
         sub-term, which lowers through that type's recursor and needs no \
         termination argument at all; (2) give `{decl}` a `termination_by \
         <parameter>` naming the ONE parameter that shrinks — the signature \
         may stay as wide as it is, the other parameters are threaded through \
         unchanged, but the measure itself must name a single parameter (a \
         lexicographic measure is not lowered yet); (3) if `{decl}` is only \
         needed to STATE something, write it in proof position — a signature \
         plus the equations you rely on, each disclosed by name — where no \
         emitted body is required."
    )]
    RecursionOutsideFragment {
        /// The unresolved identifier, exactly as written at the use site.
        name: String,
        /// The declaration being elaborated, whose own name this is.
        decl: String,
        /// Its explicit parameter count, after equation-form normalization.
        params: usize,
        /// Which recursion form was met and why no lowering takes it: the
        /// decreasing parameter the structural lowering tried and what the
        /// unresolved call passes there, or that no parameter was found.
        detail: String,
    },
    /// The unresolved identifier matches a declaration in the SAME batch that
    /// contributed no forward-resolvable header, so header-first checking had
    /// nothing to resolve the reference against.
    ///
    /// This is a report about the SIBLING, not about the use site: the name is
    /// not a typo, and the nearest-theorem list is noise. See
    /// [`crate::module_batch`] for why a declaration can be in a batch and
    /// still stage no signature.
    #[error(
        "Unknown identifier: {name} — it matches `{sibling}`, declared in this \
         same batch, but `{sibling}` has no forward-resolvable header \
         ({reason}), so a declaration written before it cannot refer to it.\n  \
         note: header-first checking resolves forward references out of the \
         signature index; a declaration whose own signature never reached that \
         index contributes no entry to it. There is nothing to fix at this use \
         site.\n  \
         help: ways forward, in order of preference — (1) repair `{sibling}`: \
         its own refusal in this batch says what its signature needs, and \
         every reference to it resolves once that signature elaborates; (2) \
         write `{sibling}`'s result type explicitly if it is being inferred \
         from its body; (3) move `{sibling}` above this declaration, making \
         the reference backward — that restores source-order resolution and \
         needs no header at all."
    )]
    SameBatchHeaderUnavailable {
        /// The unresolved identifier, exactly as written at the use site.
        name: String,
        /// The same-batch declaration it names.
        sibling: String,
        /// Why that declaration staged no header.
        reason: &'static str,
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
    /// A structure-instance pattern named the same field slot twice.
    ///
    /// Lean rejects a repeated `structInstField` the same way; accepting one
    /// would silently drop a user-written pattern.
    #[error("Duplicate field {field} in a `{{ … }}` pattern for {struct_name}")]
    DuplicateStructureField {
        /// Target structure.
        struct_name: Name,
        /// The repeated field name.
        field: String,
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
    /// Kernel rejected a declaration during full type checking. The detail's
    /// private constants are shown by their user names, as Lean 4.8.0 prints
    /// them (G21).
    #[error(
        "Kernel check failed for {name}: {}",
        crate::private_names::user_facing_text(detail)
    )]
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
    /// Attribute name has no modeled or explicitly recognized handler.
    #[error("Unknown attribute `[{name}]`")]
    UnknownAttribute { name: String },

    /// Compiler simplification accepts only bare constant replacement equalities.
    #[error("invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported.")]
    InvalidCsimpTheorem { name: Name },
    /// A class attribute targets a value-bearing declaration.
    #[error(
        "invalid 'class', declaration '{name}' must be inductive datatype, structure, or constant"
    )]
    InvalidClassAttribute { name: Name },
    /// A class is registered twice.
    #[error("class has already been declared '{name}'")]
    ClassAlreadyDeclared { name: Name },
    /// A regular class parameter depends on an output parameter.
    #[error(
        "invalid class, parameter #{parameter} depends on `outParam`, but it is not an `outParam`"
    )]
    InvalidClassOutParam { parameter: usize },
    /// Feature is not supported by the elaborator.
    #[error("Unsupported feature: {feature}")]
    Unsupported { feature: String },
    /// An `@[implemented_by f]` use pinned Lean rejects, displayed in Lean's
    /// text (`crate::implemented_by`). `target` is `f` as written, or as
    /// resolved once it resolved.
    #[error("{}", crate::implemented_by::render(decl, target, defect))]
    InvalidImplementedBy {
        decl: Name,
        target: String,
        defect: crate::implemented_by::ImplementedByDefect,
    },
    /// `attribute [attr] decl` for a parametric attribute (`extern`) on a
    /// declaration this run did not add (`crate::declared_here`): Lean's
    /// `ParametricAttribute.add` refuses it with this text.
    #[error(
        "Cannot add attribute `[{attribute}]` to declaration `{decl}` because it is in an \
         imported module"
    )]
    AttributeOnImportedDeclaration { attribute: &'static str, decl: Name },
    /// One class of a `deriving` clause failed for a type that itself
    /// elaborated. Lean adds the type before it runs any deriving handler, so
    /// this is an error about the clause, never about the type: the type is
    /// registered and this error is reported beside it as its own failed leaf
    /// (`crate::infer::deriving_log`). Displays as the handler's own error.
    #[error("{error}")]
    DerivingHandlerFailed {
        /// The class as the clause names it.
        class: String,
        /// The type the clause belongs to.
        type_name: String,
        /// Why the handler failed.
        error: Box<ElabError>,
    },
    /// A built-in `deriving` handler refused a type that Lean 4.8.0's
    /// handler refuses too, with Lean's message (`failed to generate
    /// 'Inhabited' instance for 'T'`, `Lean/Elab/Deriving/Inhabited.lean`).
    #[error("{message}")]
    DerivingRefused {
        /// Lean's message.
        message: String,
    },
    /// A declaration of a name Lean 4.8.0 core already declares
    /// (`crate::lean_core_names`), whether or not Clean's prelude models it:
    /// Lean refuses it, so Clean does too.
    #[error("`{name}` has already been declared (Lean 4.8.0 core)")]
    DeclaredInLeanCore { name: String },
    /// Lean 4.8.0's `checkNotAlreadyDeclared`
    /// (`Lean/Elab/DeclModifiers.lean:17-40`) where a `private` name is
    /// involved: a private and a public declaration of one user-facing name in
    /// one module, or two private ones. With module-local private names (G21)
    /// the two no longer collide in the kernel, so the rule is Lean's and the
    /// message is Lean's text (`private declaration 'z' …`, `a private
    /// declaration 'x' …`, `a non-private declaration 'y' has already been
    /// declared`).
    #[error("{message}")]
    PrivateNameAlreadyDeclared {
        /// Lean's message, with the user-facing name.
        message: String,
    },
    /// A structure field, or the constructor behind `⟨...⟩` / `{...}`
    /// notation, that is `private` to ANOTHER module (G21 B3). Lean 4.8.0
    /// refuses each from an importer (`Lean/Elab/App.lean` `resolveLValAux`,
    /// `BuiltinNotation.lean` `elabAnonymousConstructor`, `StructInst.lean`):
    /// "field 'x' from structure '_private.M.0.S' is private", "invalid ⟨...⟩
    /// notation, constructor for `_private.M.0.S` is marked as private",
    /// "invalid {...} notation, constructor for `_private.M.0.S` is marked as
    /// private" — the text is Lean's, with the raw kernel name it prints.
    #[error("{message}")]
    PrivateFromImportedModule {
        /// Lean's message.
        message: String,
    },
    /// A source declaration whose name is reserved for a kernel-owned axiom —
    /// a foundational axiom (`propext`, `Quot.sound`, `Classical.choice`, the
    /// `Quot` primitives) or a trust marker (`sorry`, `sorryAx`,
    /// `trustedArith`, `trustedAy`) — structurally or by printed form
    /// (`clean_kernel::is_reserved_ambient_axiom_name`). Only the kernel's own
    /// declaration may carry such a name; `«Quot.sound»` is a different
    /// one-component name that prints exactly like `Quot.sound`.
    #[error(
        "`{name}` is reserved: it is or prints as `{printed}`, a kernel-owned axiom or trust \
         marker, and only the kernel's own declaration may carry that name"
    )]
    ReservedKernelName {
        /// The declared name, rendered unambiguously (`«»` around a component
        /// that contains a dot).
        name: String,
        /// The name as every report would print it.
        printed: String,
    },
    /// An `import` could not be resolved, or its loader refused to continue.
    /// A refused partial load must not be replaced by another resolution path.
    ///
    /// FAIL-CLOSED ON PURPOSE. The elaborator used to fabricate a prelude here
    /// and return `Ok(())`, so every declaration in such a file was checked
    /// against something the source never asked for and the run still reported
    /// `N passed, 0 failed`. A verdict minted that way says nothing, which is
    /// strictly worse than no verdict — see [`crate::imports::ImportPolicy`].
    #[error(
        "unresolved import `{module}`: {reason}\n  \
         The module was not loaded successfully. For an absent module, \
         `--permissive-imports` can substitute a hand-written stand-in \
         (the resulting verdict is not a verification claim). It cannot \
         override resource, integrity, or Lean-world refusals."
    )]
    UnresolvedImport {
        /// The module name exactly as written in the `import` statement.
        module: String,
        /// Why resolution failed: the `.olean` loader's own error, or the
        /// absence of any search path to look in.
        reason: String,
    },
    /// Function applied to more arguments than its type allows.
    #[error("Too many arguments: function type {func_type} is not a function type, but {remaining_args} argument(s) remain")]
    TooManyArguments {
        func_type: String,
        remaining_args: usize,
    },
    /// An identifier that did not resolve in a SIGNATURE position, which
    /// auto-bound-implicit insertion swallowed into a fresh binder, and which
    /// then had arguments applied to it.
    ///
    /// This is the NAMED form of what used to surface as
    /// `TooManyArguments { func_type: "Sort(Param(u_0))", … }` — the third
    /// mask of the 2026-08-25 five-file Mathlib-source measurement, 17 entries
    /// and the row `Mathlib/Order/Basic.lean` was pinned to expose
    /// (`docs/analysis/frontier-next-class-2026-08-25.md` §2.6, §7.5). The old
    /// message printed the arity and the auto-bound head's `Sort` type and
    /// DELETED the identifier, which is why the class could not be triaged
    /// from the artifact — the same defect stage 0 repaired for the
    /// dot-notation face in [`Self::UnresolvedDotTarget`].
    ///
    /// It is a MISSING NAME, not an arity error. Auto-implicit binding runs
    /// only in declaration headers (`infer/auto_implicit.rs`
    /// `with_term_body_scope`; the same identifier in a VALUE position is
    /// already a loud `unknown identifier`, pinned by
    /// `tests/fixtures/source_frontier/p14`), and it fires only where name
    /// resolution has ALREADY failed — every local, constant, alias, namespace
    /// and projection lookup is tried first
    /// (`infer/elab_core.rs`, `elab_ident_or_auto_implicit`). So when this is
    /// raised the named identifier is known not to resolve, which is what
    /// makes naming it honest rather than speculative. Lean reports the same
    /// program the same way (`function expected at nosuchpred`); Clean's
    /// message names the auto-binding as well, because that — not the arity —
    /// is what the user has to undo.
    ///
    /// Raised ONLY where `TooManyArguments` was already raised and only when
    /// the application head is a free variable this declaration's auto-implicit
    /// table introduced, so no declaration's verdict can move: a failure stays
    /// a failure with the same span, and a genuine over-application of a
    /// user-written binder keeps the untouched `TooManyArguments` message
    /// (pinned by `tests/fixtures/source_frontier/p30`).
    ///
    /// Message shape is load-bearing twice over, exactly as for
    /// [`Self::UnresolvedDotTarget`]. `Unknown identifier:` leads so the
    /// source-elab classifier (`scripts/srcelab_classify.py`, first-match-wins)
    /// files these under `unknown identifier` instead of the residual `other`
    /// bucket, and so the name survives `per_error_class`'s 400-char
    /// truncation. `auto-bound implicit` then keeps them separable from both
    /// the pre-existing unknown-identifier population and the `dot notation`
    /// population in the same report.
    #[error(
        "Unknown identifier: {name}; auto-bound implicit of type `{func_type}` in a \
         signature position, then applied to {remaining_args} argument(s) it cannot \
         take. Define `{name}`, or `set_option autoImplicit false` so an unresolved \
         name in a signature is a hard error"
    )]
    AutoBoundHeadOverApplied {
        /// The identifier auto-implicit swallowed, as written in the source.
        name: String,
        /// The auto-bound head's type, PRETTY-PRINTED (`Sort ?u_0`) rather than
        /// dumped — unlike [`Self::TooManyArguments`], whose `{func_type:?}`
        /// spelling is kept byte-stable for every head this variant does not
        /// claim. The dump of a fresh universe mint is ~70 characters of
        /// `Name { depth, suffix, lean4_hash }` that would push the actionable
        /// tail of this message past `per_error_class`'s 400-char truncation.
        func_type: String,
        /// Arguments still applied when the head's type ran out of binders.
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
    /// **Attribution wrapper**: a tactic block failed with a diagnostic that
    /// did not name the tactic responsible.
    ///
    /// Brick T0 of `docs/plans/TACTICS_TO_100_2026-07-29.md` closed the
    /// *silent* class (a construct that produced no diagnostic at all). This
    /// closes the neighbouring one: `unsolved goals: tactic block has 1
    /// unsolved goal(s)`, `TypeMismatch`, `UnknownIdentWithSuggestions` and
    /// friends fail loudly but carry no tactic, so a reader cannot tell
    /// whether `omega` ran and gave up or was never reached — the tactic is
    /// *effectively* hidden. Measured on `origin/main` at 2026-08-09,
    /// **88 of 373** census probes failed this way
    /// (`data/silent_tactic_census.json`, verdict `unnamed`).
    ///
    /// Added at the `by`-block boundary only, and only when the underlying
    /// diagnostic does not already name the dispatching tactic. Every error
    /// that already carries a `tactic:` field is returned unchanged, and the
    /// wrapper is transparent to `TacticError::from_elab_error`, so no
    /// combinator (`first`, `try`, `all_goals`) sees a different error than
    /// before. This changes the *message*, never the verdict.
    #[error("{source} [raised under tactic {chain} at source bytes {span_start}..{span_end}]")]
    InTactic {
        /// Source spelling of the innermost tactic in scope when the failure
        /// was raised (`arg`, not the registry key `conv_arg`).
        tactic: String,
        /// The nesting chain, outermost → innermost, e.g. ``` `conv` > `lhs` ```.
        chain: String,
        /// Start byte offset of that tactic in the source file.
        span_start: usize,
        /// End byte offset (exclusive).
        span_end: usize,
        /// The original diagnostic, structurally unmodified.
        #[source]
        source: Box<ElabError>,
    },
    /// A user metaprogram (term/tactic elaborator body) raised a custom error via
    /// `throwError "msg"` (or an alias). The `message` is the literal string the
    /// user passed. This is a plain typed diagnostic: it closes no goal, accepts
    /// no term, and fabricates nothing — it only makes elaboration FAIL with
    /// exactly the user's message.
    #[error("{message}")]
    UserThrowError { message: String },
    /// A Lean testing or audit command (`#guard`, `#print axioms`,
    /// `#guard_msgs`) failed. `message` is the error Lean logs for the same
    /// failure, verbatim where Clean can produce Lean's text (`unknown
    /// constant 'c'`, the `#guard_msgs` mismatch report), because a
    /// surrounding `#guard_msgs` compares exactly this text.
    #[error("{message}")]
    CommandFailed { message: String },
    /// A `#reduce` outside the class in which Clean knows what pinned Lean's
    /// `Meta.reduce` does, or whose output a `#guard_msgs` would compare
    /// (`crate::reduce_command`). It is Clean's own refusal, not a message of
    /// Lean's, so no `#guard_msgs` consumes it.
    #[error("`#reduce` refused: {reason}")]
    ReduceUnmodeled { reason: String },
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
    #[error("failed to synthesize instance `{goal}`{detail}")]
    FailedToSynthesizeInstance {
        /// Rendered instance goal (e.g. `Hm Int`).
        goal: String,
        /// The candidate list and the reader's options, already prefixed with
        /// its own newline, or EMPTY when the site has no `ElabCtx` to build it
        /// from or the goal is not a class application.
        ///
        /// The bare form of this error was the whole message for essentially
        /// every real instance failure: the rich explanation existed, was
        /// reachable, and lost a race. `ensure_no_residual_fvars` builds it at
        /// declaration CLOSE, but an ordinary synthesis failure aborts the body
        /// long before close — so on a pinned Mathlib slice the rich text fired
        /// 0 times against 497 bare ones. Replacing the proofs with `sorry` (so
        /// the argument loop never runs) took it to 3, which is what identified
        /// the race rather than a dead path. The detail is built HERE now,
        /// where the failure actually happens.
        detail: String,
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
    /// A declaration wrote an explicit `.{...}` universe list and its VALUE left an
    /// undetermined universe level that neither its type nor the list names (U2 rung 4,
    /// 2026-08-25; Lean's rule since 2026-10-19, `docs/DECISIONS.md` R93). Lean generalizes
    /// a level its TYPE leaves into an appended parameter (`levelMVarToParamTypesPreDecls`,
    /// `sortDeclLevelParams`) and refuses a value-only one ("contains universe level
    /// metavariables"). Only a WRITTEN list counts: file-scope `universe u` names are
    /// subtracted (`ElabCtx::set_file_universe_params`), and a declaration with no list
    /// still generalizes every leftover (`docs/FRONTEND_CLASS_LEDGER.md` (164), open half).
    #[error("{detail}")]
    ExplicitUniverseListClosed {
        /// Which levels leaked, which list they leaked out of, and the two
        /// ways forward. Keep it SINGLE-LINE. (It used to be single-line
        /// because `clean check` rendered a top-level declaration's failure
        /// through `{:?}`, which escapes newlines; since 2026-08-27 that
        /// reporter renders Display in both of its paths
        /// — `cmd_core.rs::elaboration_error_diagnostic` — so a newline here
        /// would now really break the line, and one error would stop being
        /// one terminal row.)
        detail: String,
    },
    /// A declaration WROTE a universe name inside the reserved metavariable
    /// namespace (`crate::level_mint::MINT_PREFIX`, 2026-08-26b).
    ///
    /// Universe metavariables are spelled `?u_N` precisely so that a level
    /// the elaborator mints and a level a declaration writes can never be the
    /// same `Level::Param(Name)`. `?` is not an identifier-start character, so
    /// the level grammar has no production for such a name — but a guillemet
    /// identifier (`Sort «?u_0»`) bypasses the lexer's identifier rules and
    /// would otherwise reach the namespace anyway. This variant is that door,
    /// shut: it is what makes "the surface cannot produce a mint name" a
    /// checked property instead of a lexer accident.
    #[error("{detail}")]
    ReservedUniverseName {
        /// The offending name, why the space is reserved, and what to write
        /// instead. Keep it SINGLE-LINE, for the reason spelled out on
        /// [`Self::ExplicitUniverseListClosed`]'s `detail`.
        detail: String,
    },
    /// A universe name that is neither declared (`universe u`, `.{u}`) nor
    /// auto-boundable: `autoImplicit` is off, or the name fails Lean's
    /// `isValidAutoBoundLevelName` (under `relaxedAutoImplicit false`, an
    /// ASCII-lowercase letter plus digits / subscripts / `_` / `'`). Lean's
    /// message, from `Lean/Elab/Level.lean` `elabLevel`.
    #[error("unknown universe level `{name}`")]
    UnknownUniverseLevel {
        /// The universe name as written.
        name: String,
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
    /// A `where` / `let rec` helper lifts to a name that is already declared,
    /// or that a second helper of the same declaration also lifts to. Lean
    /// 4.8.0 refuses both (`checkNotAlreadyDeclared` in `Lean/Elab/LetRec.lean`;
    /// pinned: `'foo.go' has already been declared`, also for two identical
    /// helpers), so Clean does too (`crate::infer::let_rec_lift`).
    #[error("`{name}` has already been declared (a `where`/`let rec` helper lifts to it)")]
    LetRecAuxAlreadyDeclared {
        /// The auxiliary declaration name.
        name: String,
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
    /// A `match` alternative (or equation) that no value selects: every value
    /// it matches is matched by an earlier alternative. Lean 4.8.0 refuses the
    /// match ("redundant alternative", `reportMatcherResultErrors` in
    /// `src/Lean/Elab/Match.lean`); accepting it would admit a program Lean
    /// rejects and silently drop the alternative's body (decision D2).
    #[error("redundant alternative: {detail}")]
    RedundantAlternative {
        /// Which alternative, of which match, and why it is unreachable.
        detail: String,
    },
    /// A `do` block that Lean 4.8.0's `do` elaborator refuses
    /// (`src/Lean/Elab/Do.lean`), reported with Lean's own message: a
    /// `(← e)` lifted over a binder (`expandLiftMethodAux`), a `return` /
    /// `break` / `continue` that is not the last element of its sequence
    /// (`checkLastElem`). Accepting either would admit a program Lean
    /// rejects (decision D2).
    #[error("{message}")]
    DoNotation {
        /// Lean's message.
        message: String,
    },
    /// Two members of a `mutual` block carry well-founded `termination_by` measures of different
    /// types. Lean packs the block into ONE well-founded relation and refuses it with this message
    /// (`checkCodomains`, `Lean/Elab/PreDefinition/WF/Rel.lean`); Clean's structural lowering
    /// would ignore the measures and accept it (`infer/elab_mutual_measures.rs`).
    #[error(
        "The termination measures of mutually recursive functions must have the same return \
         type, but the termination measure of {first} has type\n  {first_ty}\nwhile the \
         termination measure of {other} has type\n  {other_ty}\nTry using `sizeOf` explicitly"
    )]
    MutualMeasureTypeMismatch {
        /// The block's first member with a measure.
        first: String,
        /// Its measure's type.
        first_ty: String,
        /// The member whose measure type differs.
        other: String,
        /// That measure's type.
        other_ty: String,
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

#[path = "error_diagnostics.rs"]
mod diagnostics;

#[path = "error_ident_suggestions.rs"]
mod ident_suggestions;

impl ElabError {
    /// Strip any [`ElabError::InTactic`] attribution wrappers, and the
    /// [`ElabError::DerivingHandlerFailed`] wrapper a logged `deriving`
    /// failure travels in.
    ///
    /// Attribution is presentation, not classification: every site that
    /// *categorises* an error (failure trackers, blocking-reason tables, the
    /// reverse `ElabError → TacticError` boundary) must look through the
    /// wrapper so the category it reports is exactly the one it reported
    /// before attribution existed.
    #[must_use]
    pub fn innermost(&self) -> &ElabError {
        match self {
            Self::InTactic { source, .. } => source.innermost(),
            // A logged `deriving` failure names the class it came from; WHAT
            // failed is the handler's own error.
            Self::DerivingHandlerFailed { error, .. } => error.innermost(),
            other => other,
        }
    }

    /// The identifier an unknown-identifier error names, whichever form it
    /// takes: raised plain, still deferred inside the elaborator
    /// ([`ElabError::UnknownIdentDeferred`]), or materialized with suggestions
    /// at the reporting boundary. A site that asks "is this an unknown
    /// identifier, and which?" asks this rather than matching one form, so
    /// the deferral of the "did you mean" scan never changes what it sees.
    #[must_use]
    #[cfg(test)]
    pub(crate) fn unknown_ident_name(&self) -> Option<&str> {
        match self {
            Self::UnknownIdent(name)
            | Self::UnknownIdentDeferred { name, .. }
            | Self::UnknownIdentWithSuggestions { name, .. } => Some(name),
            _ => None,
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

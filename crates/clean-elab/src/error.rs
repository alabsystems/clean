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
         `{decl}` ({params} parameter(s); neither lowering applied) is outside \
         today's fragment.\n  \
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
    /// An `import` named a module that resolves to nothing real: no `.olean`
    /// was loadable for it, no intra-project `.lean` source was elaborated for
    /// it this run, and Clean declares no hand-written prelude under that name.
    ///
    /// FAIL-CLOSED ON PURPOSE. The elaborator used to fabricate a prelude here
    /// and return `Ok(())`, so every declaration in such a file was checked
    /// against something the source never asked for and the run still reported
    /// `N passed, 0 failed`. A verdict minted that way says nothing, which is
    /// strictly worse than no verdict — see [`crate::imports::ImportPolicy`].
    #[error(
        "unresolved import `{module}`: {reason}\n  \
         nothing real provides this module, so nothing in this file can be \
         checked against it.\n  \
         Pass `--permissive-imports` to substitute a hand-written stand-in and \
         continue (the resulting verdict is not a verification claim)."
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
    /// A declaration wrote an EXPLICIT `.{...}` universe list and elaboration
    /// still left an undetermined universe level that the list does not name
    /// (U2 rung-4 explicitness channel, 2026-08-25).
    ///
    /// Lean treats an explicit list as EXHAUSTIVE
    /// (`Lean.sortDeclLevelParams`): when `allUserLevelNames` is non-empty,
    /// a used level outside it is an error, never an extra parameter. Clean
    /// used to APPEND the leftovers instead, so `def leak.{u} (A : Type u)
    /// (a : A) := fun (B : Type _) (b : B) => b` registered with arity TWO
    /// while its author declared one — the declaration's universe signature
    /// silently disagreed with its source, and only a use site
    /// (`@leak.{0}` → `UniverseLevelMismatch { expected: 2, actual: 1 }`)
    /// ever reported it, at a distance and blaming the caller.
    ///
    /// Scoped precisely to declarations that WROTE a list: `universe u` at
    /// file scope is folded into the same parameter vector by
    /// [`crate::preprocess_decl_with_context`] and does NOT close anything,
    /// so the explicit set is derived by subtracting the file-scope names
    /// (`ElabCtx::set_file_universe_params`). A declaration with no written
    /// list keeps auto-generalizing exactly as before.
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

#[path = "error_diagnostics.rs"]
mod diagnostics;

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

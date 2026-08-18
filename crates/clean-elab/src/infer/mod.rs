// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type inference with metavariables
//!
//! Converts surface syntax to kernel expressions with:
//! - Named to de Bruijn conversion
//! - Metavariable creation for holes and implicit arguments
//! - Type inference
//! - Implicit argument insertion

mod auto_implicit;
mod certification;
mod coercion;
mod course_of_values;
mod derive;
mod elab_app;
mod elab_app_support;
mod elab_attributes;
mod elab_calc;
mod elab_canonicalize;
mod elab_core;
mod elab_ctx;
mod elab_do;
mod elab_do_actions;
mod elab_do_bind;
mod elab_do_compat;
mod elab_do_control;
mod elab_do_for;
mod elab_do_for_handlers;
mod elab_do_for_post;
mod elab_do_handlers;
mod elab_do_monad;
mod elab_do_mut;
mod elab_do_prod;
mod elab_do_stack;
mod elab_getelem;
mod elab_monad_materialize;
mod elab_pattern_lambda;
mod elab_subst;
mod elab_universe_inst;
use elab_do::DoMonadInfo;
mod elab_decl_value;
mod elab_def_body;
mod elab_do_if;
mod elab_do_match;
mod elab_do_match_ctor_order;
mod elab_do_match_q_pattern;
mod elab_do_try;
mod elab_expected;
mod elab_inductive;
mod elab_init;
mod elab_instance;
mod elab_match;
mod elab_mutual;
mod elab_proj;
mod elab_struct_lit;
mod elab_structure;
mod elab_tactic;
mod elab_tactic_compound;
mod elab_types;
mod elab_variable;
pub(crate) mod elaborate_decl;
mod equation_dep_family;
mod instance;
mod meta_builtin;
mod meta_control_flow;
mod meta_query;
mod q_pattern;
mod quotation;
mod structural;
mod synth_order;
// `pub(crate)` so the macro-expansion path (`macro_integration::computed_body`)
// can reuse the shared `throwError`/`s!"…"` recognition + interpolation
// rendering (`as_throw_error_message_in`, `is_throw_error_call`) when surfacing a
// `throwError` raised inside a computed `macro_rules` body. The module's items
// are individually `pub(crate)` only where that reuse requires it.
pub(crate) mod user_tactic;
pub(crate) mod user_term;
mod wf_recursion;
pub(in crate::infer) use elab_types::{is_out_param_type, is_semi_out_param_type};
// `pub(crate)`: `register::register_param_names` (B01) converts surface binder
// kinds when recording named-argument parameter info.
pub(crate) use elab_types::collect_level_params;
pub(crate) use elab_types::convert_binder_info;
pub use elab_types::{ClassRegistration, CommandOutput, DerivedInstance, ElabResult, HoleContext};
use elab_types::{RecursiveDefContext, RecursiveExtraParam};

use crate::instances::InstanceTable;
use crate::macro_integration::{expand_surface_macros, syntax_to_surface, MacroCtx};
use crate::stack_safe;
use crate::tactic::TacticRegistry;
use crate::term_elab_registry::TermElabRegistry;
use crate::unify::{
    MetaId, MetaState, OwnedMetaScopeCloseError, OwnedMetaScopeToken, Unifier, UnifyResult,
};
use crate::ElabError;
#[cfg(test)]
use clean_kernel::cert::ProofCert;
use clean_kernel::env::{Reducibility, SimpPriority as KernelSimpPriority};
use clean_kernel::name::Name;
use clean_kernel::{
    BigNat, BinderData, BinderInfo, Environment, Expr, ExprKind, FVarId, Level, Literal,
    LocalContext, TcCaches, TypeChecker,
};
use clean_macro::quotation::parse_quotation;
use clean_parser::{
    AesopAttr, DoCatchClause, DoElem, DoMatchArm, LevelExpr, Projection, SurfaceArg, SurfaceBinder,
    SurfaceBinderInfo, SurfaceExpr, SurfaceLit, SurfacePattern, UniverseExpr,
};
use std::cell::RefCell;
use std::collections::HashMap;

/// Elaboration context
pub struct ElabCtx<'a> {
    /// The kernel environment
    env: &'a Environment,
    /// Local bindings: name -> (fvar_id, type)
    locals: Vec<(String, FVarId, Expr)>,
    /// Values of let-bound locals: fvar_id -> value. A local in `locals` that
    /// also appears here is a *local definition* (`let x : T := v`) rather than
    /// an opaque hypothesis: its value is body-visible / zeta-reducible. The
    /// ProofState → ElabCtx bridge (`eval_tactic`) records `LocalDecl.value`
    /// here so a subsequent term elaboration (e.g. `have h : x = v := rfl`) can
    /// unfold `x` to `v` during definitional-equality checking. `build_local_ctx`
    /// consults this map and emits `push_let_with_id` (instead of `push_with_id`)
    /// for these fvars. Cleared in lock-step with `locals` by `pop_local`.
    local_let_values: HashMap<FVarId, Expr>,
    /// Active synthetic names used to thread helper-generated `if let`
    /// scrutinees through recursive elaboration without macro expansion.
    shared_if_let_scrutinees: Vec<String>,
    /// Universe parameter names
    universe_params: Vec<String>,
    /// Metavariable state (for unification)
    pub(crate) metas: MetaState,
    /// Next fresh free variable id
    next_fvar: u64,
    /// Next fresh universe parameter id
    next_universe: u64,
    /// Instance table for type class resolution
    instances: InstanceTable,
    /// Local instance-implicit binders for nested instance resolution
    /// Stack of (fvar_id, type) pairs for local `[inst : T]` binders.
    /// These are searched during instance resolution before global instances.
    local_instances: Vec<(FVarId, Expr)>,
    /// Instances hidden from resolution for this declaration: `local
    /// instance`s whose declaring section/namespace block has ended. Injected
    /// per declaration from `FileContext` (B99); empty by default, so
    /// resolution is unchanged when no `local instance` has gone out of
    /// scope.
    hidden_instances: std::collections::HashSet<Name>,
    /// `scoped instance` → declaring namespace. A candidate in this map is
    /// only visible while its namespace is the current namespace (or an
    /// ancestor of it) or appears in `namespace_state.open_namespaces()` —
    /// checked at resolution time so `open Foo in def …` activates it.
    /// Injected per declaration from `FileContext` (B99).
    scoped_instances: HashMap<Name, Name>,
    /// `@[default_instance]` table: class → (instance, priority) in
    /// declaration order. Drives open-metavariable defaulting in
    /// `resolve_instance_candidates` (Lean's default-instance mechanism).
    /// Injected per declaration from `FileContext` (B99).
    default_instances: HashMap<Name, Vec<(Name, u32)>>,
    /// Cache for instance resolution (tabled resolution)
    /// Maps normalized goal types to resolved instance expressions.
    /// This avoids re-resolving the same instance multiple times.
    instance_cache: HashMap<String, Expr>,
    /// TypeChecker caches reused across whnf/is_def_eq/infer_type calls (#1852).
    /// Avoids discarding memoized WHNF, def_eq, and equiv results between
    /// elaboration operations. Uses RefCell for interior mutability since
    /// whnf/is_def_eq take &self.
    tc_caches: RefCell<TcCaches>,
    /// Read-only authentication verdicts for executable recursor side-table
    /// packets. `ElabCtx` holds an immutable environment borrow for its entire
    /// lifetime, so a name's packet cannot change while this cache is live.
    /// Subject-reduction validation is intentionally stronger than an ordinary
    /// type lookup and must not be repeated for every match arm.
    recursor_auth_cache: RefCell<HashMap<Name, Result<(), String>>>,
    /// Canonical-wrapper authentication verdicts for imported plain-definition
    /// `casesOn` constants. Kept separate from recursor packets because the
    /// imported name has no recursor-registry row of its own.
    cases_on_auth_cache: RefCell<HashMap<Name, Result<(), String>>>,
    /// Macro expansion context (built-ins + user-registered macro_rules)
    macro_ctx: MacroCtx,
    /// Registry for extensible tactic dispatch (Named variant)
    tactic_registry: TacticRegistry,
    /// Registry for extensible term elaboration dispatch.
    /// Consulted before the hardcoded match in `elaborate()`.
    /// User-registered handlers at higher priority override builtins.
    term_elab_registry: TermElabRegistry,
    /// User-defined term elaborators from `elab "kw" e:term : term => <body>`,
    /// keyed by keyword. Consulted in `elaborate()` when a post-expansion
    /// `App(Ident(kw), args)` / `Ident(kw)` head matches a registered keyword:
    /// the call-site arguments are bound to the pattern variables, substituted
    /// into the body, and the body is re-elaborated through the normal pipeline.
    user_term_elabs: HashMap<String, user_term::UserTermElab>,
    /// Metaprogram value channel: bound names mapped to already-elaborated kernel
    /// `Expr` values. Populated while a value-channel term-elaborator body (e.g.
    /// `let t := inferType e; t`) is being interpreted, and consulted by
    /// `elab_ident` so a later reference to the bound name splices the stored
    /// `Expr` directly (no surface round-trip). Cleared per body, so a binding
    /// never leaks into an unrelated elaboration. See [`meta_query`].
    meta_value_bindings: HashMap<String, Expr>,
    /// Collected aesop attributes during elaboration
    /// Callers should retrieve these via `take_aesop_attrs()` and register them
    collected_aesop_attrs: Vec<(Name, AesopAttr)>,
    /// Collected simp lemma attributes (name, priority)
    collected_simp_attrs: Vec<(Name, KernelSimpPriority)>,
    /// Collected reducibility attributes (name, level)
    collected_reducibility: Vec<(Name, Reducibility)>,
    /// Collected extern bindings (decl_name, extern_name)
    collected_extern: Vec<(Name, String)>,
    /// Collected export bindings (decl_name, export_name)
    collected_export: Vec<(Name, String)>,
    /// Collected deprecations (name, message)
    collected_deprecated: Vec<(Name, Option<String>)>,
    /// Collected inline hints
    collected_inline: Vec<Name>,
    /// Collected noinline hints
    collected_noinline: Vec<Name>,
    /// Collected always_inline hints
    collected_always_inline: Vec<Name>,
    /// Collected specialize hints
    collected_specialize: Vec<Name>,
    /// Collected csimp lemmas
    collected_csimp: Vec<Name>,
    /// Collected congr lemmas
    collected_congr: Vec<Name>,
    /// Collected ext lemmas
    collected_ext: Vec<Name>,
    /// Collected refl lemmas
    collected_refl: Vec<Name>,
    /// Collected symm lemmas
    collected_symm: Vec<Name>,
    /// Collected macro_inline hints
    collected_macro_inline: Vec<Name>,
    /// Collected inline_if_reduce hints
    collected_inline_if_reduce: Vec<Name>,
    /// Collected nospecialize hints
    collected_nospecialize: Vec<Name>,
    /// Collected @[implemented_by] bindings (decl_name, impl_name)
    collected_implemented_by: Vec<(Name, String)>,
    /// Collected @[coe] coercion registrations
    collected_coe: Vec<Name>,
    /// Collected @[match_pattern] registrations
    collected_match_pattern: Vec<Name>,
    /// Collected @[init] registrations
    collected_init: Vec<Name>,
    /// Collected @[default_instance] registrations (name, priority)
    collected_default_instance: Vec<(Name, u32)>,
    /// Collected `attribute [instance]` / `@[instance N]` registrations
    /// (name, priority): turn an existing definition into a type class
    /// instance (B06; Lean `src/Lean/Meta/Instances.lean`, `addInstance`).
    collected_instance_attrs: Vec<(Name, u32)>,
    /// Collected @[derive_handler] registrations.
    collected_derive_handler: Vec<Name>,
    /// Collected file-scope attribute removals (decl name, attribute name)
    collected_attribute_removals: Vec<(Name, String)>,
    /// Auto-implicit type parameters discovered during elaboration (#164)
    /// Each entry is (name, fvar_id, type) where type is typically a fresh Sort metavar
    auto_implicits: Vec<(String, FVarId, Expr)>,
    /// O(1) lookup for active auto-implicit binders by source name.
    /// `auto_implicits` remains the canonical ordered packet representation.
    auto_implicit_lookup: HashMap<String, FVarId>,
    /// Whether we're in a declaration context where auto-implicits are allowed (#164)
    /// When false, unknown identifiers error rather than becoming auto-implicits
    in_decl_context: bool,
    /// Whether we're elaborating a declaration's VALUE (def body, theorem
    /// proof, instance field value) rather than its SIGNATURE (binder types,
    /// result type, ctor/field types). Lean enables auto-bound implicits only
    /// around declaration *headers* (`Lean/Elab/MutualDef.lean` `elabHeaders`
    /// runs under `withAutoBoundImplicit`; `Lean/Elab/Term.lean`
    /// `elabTermAux`/`mkAutoBoundImplicit` consults that flag) — an unknown
    /// identifier in a term/value position is always a loud
    /// "unknown identifier" error, never an auto-implicit (gap sweep B03).
    in_term_body: bool,
    /// `variable` binders accumulated from enclosing `section` BLOCKS being
    /// elaborated by [`elaborate_decl::ElabCtx::elab_section`]. Prepended as
    /// real binders to inner value declarations (Lean
    /// `Lean/Elab/Command.lean` `elabVariable` + section-variable inclusion in
    /// `Lean/Elab/MutualDef.lean`), mirroring what `FileContext`/`preprocess`
    /// does for top-level marker-form `variable` commands. Before B03 these
    /// references only worked by falling through to body auto-implicits —
    /// removing body auto-bind required making the binders real.
    section_binder_stack: Vec<SurfaceBinder>,
    /// Expected type for bidirectional type checking (#172)
    /// Used by anonymous constructor syntax `⟨...⟩` to determine which structure to construct.
    /// Set when elaborating definition bodies with type annotations.
    current_expected_type: Option<Expr>,
    /// Recursive definition context (#378)
    /// When set, we're elaborating a recursive definition and recursive calls
    /// should be replaced with the inductive hypothesis.
    /// Contains: (function_name, decreasing_arg_position, decreasing_arg_name, ih_fvar)
    recursive_def_ctx: Option<RecursiveDefContext>,
    /// Explicit argument mode (#1231)
    /// When true, implicit arguments are not automatically inserted.
    /// Set when elaborating expressions under the @ marker.
    explicit_mode: bool,
    /// One-shot binop% heterogeneous-fallback flag (B104). Set by
    /// `elab_app_binop_hetero_fallback` immediately before its retry call and
    /// CONSUMED (reset to false) at `elab_app_inner` entry, so exactly the
    /// retried application skips the homogeneous slot pinning while nested
    /// sub-elaborations behave normally. Mirrors Lean's `binop%`
    /// try-homogeneous-then-heterogeneous behavior; the fallback only fires on
    /// paths where elaboration already FAILED, so homogeneous elaborations are
    /// byte-identical.
    suppress_binop_homogenize: bool,
    /// Cached monad info for do-block elaboration (#1814).
    /// Set once at the start of `elab_do` and reused by all `mk_bind_app` /
    /// `mk_pure_app` calls within the same do-block, matching Lean 4's
    /// `MonadInfo { m, u, v }` pattern from `Do/Basic.lean:26-38`.
    do_monad_info: Option<DoMonadInfo>,
    /// Control flow effects detected by the pre-pass (#1818 Phase 3).
    /// Set at the start of `elab_do` after `expand_all_nested_actions`.
    /// Used by Phase 4 (ControlStack) to wrap the base monad in transformers.
    do_control_info: Option<elab_do_control::ControlInfo>,
    /// Control stack built from ControlInfo (#1818 Phase 4B).
    /// Contains the transformer layer stack and saved base indices for
    /// generating break/continue/return expressions at the correct depth.
    do_control_stack: Option<elab_do_stack::ControlStack>,
    /// The wrapped monad `m'` when a ControlStack is active (#1818 Phase 4C).
    /// When transformers are applied, bind/pure inside the do-block must use the
    /// wrapped monad (e.g., `ContinueT (BreakT (StateT σ (ExceptT ρ m)))`)
    /// instead of the base monad `m`. The base monad is preserved in `do_monad_info`
    /// for ControlStack operations that generate control flow at specific layers.
    do_wrapped_monad: Option<Expr>,
    /// Loop context for for/while/repeat elaboration (#1818 Phase 4C).
    /// When inside a for-loop body, break/continue generate ForInStep.done/yield
    /// directly instead of OptionT.fail. This matches Lean 4 BuiltinDo/For.lean
    /// where the loop handler consumes break/continue (ControlInfo strips them).
    do_loop_ctx: Option<DoLoopContext>,
    /// Names declared `let mut` in the current do-block (B08).
    /// Populated at the start of `elab_do`; a `Reassign` of a name NOT in this
    /// set is a hard "cannot reassign immutable variable" error (Lean parity).
    do_mut_vars: Vec<String>,
    /// True when the current do-block is being elaborated via the pure
    /// functional state-threading lane (B08 — `docs/plans/GAP_SWEEP_2026-07-09.md`).
    /// In this lane `mut` reassignment desugars to `let`-shadowing and
    /// `if`-without-`else`/early-return-guards thread state as ordinary terms
    /// (no `StateT`/`ExceptT` transformer stack), so the emitted term
    /// kernel-checks and computes. Set by `elab_do` only for blocks whose
    /// control flow is expressible purely (no `for`/`while`/`break`/`continue`).
    do_pure_state: bool,
    /// Pending universe level assignments discovered by the level_eq callback
    /// during kernel type checking. The callback writes here (via RefCell for
    /// interior mutability since kernel calls go through `&self` methods).
    /// Committed to MetaState at `&mut self` boundaries via
    /// `commit_pending_level_assigns()`.
    pending_level_assigns: RefCell<Vec<(Name, Level)>>,
    namespace_state: crate::namespace::NamespaceState,
    /// Current namespace prefix for qualifying declaration names.
    namespace_prefix: String,
    /// Local option overrides for section-scoped `set_option` commands.
    ///
    /// When `set_option` appears inside a section or namespace block,
    /// the option is stored here and scoped to the block. Lookups check
    /// this map first, then fall back to `env.get_option()`.
    local_options: HashMap<String, Option<String>>,
    /// Dependent-match motive body for the match currently being lowered.
    ///
    /// When a `match` is elaborated under an expected type that genuinely
    /// *depends on the scrutinee* (e.g. `def f (b : T) : Choose b := match b
    /// with …`), the motive is not a constant `fun _ : T => R` — it is the
    /// dependent `fun (x : T) => R[scrutinee := x]`. This field holds the
    /// abstracted body `R[scrutinee := BVar(0)]` (with the scrutinee fvar
    /// replaced by `BVar(0)`), so each arm can recover its own expected type
    /// `R[scrutinee := ctorᵢ fields]` by instantiating the body at the arm's
    /// constructor value. `None` when the motive is constant. Saved/restored
    /// around each match so nested matches do not leak motives.
    match_dependent_motive: Option<Expr>,
    /// Number of index binders preceding the major-premise binder in
    /// [`Self::match_dependent_motive`].
    ///
    /// For a *non-indexed* dependent match the body is under a single binder
    /// (the scrutinee, `BVar(0)`) and this is `0`, so per-arm specialization is
    /// `body.instantiate(ctorᵢ)` exactly as before. For a **dependent-return
    /// match over an indexed family** — e.g. `def rebuild (n) (v : IVec n) :
    /// IVec n := match v with …` — the motive is generalized over both the
    /// scrutinee *and* its index(es): `fun (idx₀ … idx_{k-1}) (major) =>
    /// R[indices := idx BVars][scrutinee := major]`. The stored body then lives
    /// under `k + 1` binders (`BVar(0)` = major, `BVar(k)` = idx₀) and this
    /// holds `k`. Per-arm specialization instantiates all `k + 1` binders with
    /// the constructor's own index values + ctor value, so each branch's
    /// expected type is `motive idx(ctorᵢ)… (ctorᵢ fields…)`.
    match_dependent_motive_indices: usize,
    /// When an *index-discriminating* motive is in force for the current match,
    /// the universe level `u` of the `PUnit.{u}` returned at the impossible
    /// indices. `None` when no discriminating motive is active (the common case).
    ///
    /// Set by `elab_match` when a single-index GADT match legitimately omits an
    /// index-impossible constructor whose branch type has no closed inhabitant
    /// (e.g. `Vec.head : Vec α (succ n) → α`, where the omitted `nil` branch
    /// would need an `α`). The motive then returns `branch_ty` at the scrutinee's
    /// index-constructor head and `PUnit.{u}` at every other head, so the omitted
    /// branch's minor is the trivially-inhabited `PUnit.unit.{u}` — a SOUND,
    /// sorry-free discharge (the kernel re-checks the lowered term). Saved/restored
    /// around each match like the dependent-motive fields.
    match_index_discriminating_punit: Option<Level>,
    /// Auxiliary-constructor arm source for a fused nested-mutual fold (Track AA).
    ///
    /// When a `mutual` block of the shape `{ T.f : T -> R, T.g : C T -> R }` is
    /// fused into ONE `T.rec` application, `T.f`'s arms supply the *primary*
    /// minors (leaf/node) while `T.g`'s arms supply the *auxiliary* minors
    /// (nil/cons of the synthesized `T._C` mirror). This field carries `T.g`'s
    /// arms so the nested-recursor minor builder fills the auxiliary minors with
    /// the REAL fold body instead of the degenerate `try_default_value_of_type`
    /// (which yields `Nat.zero` and makes `T.size` over a multi-element node
    /// return 0). `None` for ordinary single-function recursion, leaving that
    /// path's default-fill behavior byte-for-byte unchanged. Saved/restored
    /// around the fused def's elaboration so it never leaks into nested matches.
    nested_mutual_aux_arms: Option<NestedMutualAuxArms>,
    /// Names of user-written *named* synthetic holes (`?name`), keyed by the
    /// metavariable each hole lowered to. Populated by [`Self::elab_hole`] when a
    /// [`SurfaceExpr::NamedHole`] is elaborated; read back by
    /// `elaborate_refine_term` to tag the pending goal so `case name => …` can
    /// select it. Anonymous holes (`_`, `?`, `?_`) never insert an entry, so a
    /// refine goal from an anonymous hole stays untagged (`tag: None`).
    /// Informational only: it never affects elaboration outside the refine
    /// bridge's goal-tag lookup.
    hole_names: HashMap<MetaId, String>,
}

/// The auxiliary-arm source for a fused nested-mutual fold (Track AA).
///
/// See [`ElabCtx::nested_mutual_aux_arms`]. The arms are matched against the
/// auxiliary mirror type's constructors by *short name* — `nil` ↔ a `[]` /
/// `List.nil` pattern, `cons` ↔ a `_ :: _` / `List.cons` pattern — so the real
/// `T.g` body (e.g. `Tree.size t + Tree.sizeList rest`) fills the `T._List.cons`
/// minor, with each field's induction hypothesis wired exactly as the primary
/// minors are.
#[derive(Clone, Debug)]
pub(super) struct NestedMutualAuxArms {
    /// Short name of the auxiliary container, e.g. `List` (the `C` in `C T`).
    /// The mirror aux inductive is `<Parent>._<container>` (e.g. `Tree._List`).
    pub container_short: String,
    /// The sibling function's arms (e.g. `Tree.sizeList`'s `[] => 0` /
    /// `t :: rest => …`).
    pub arms: Vec<clean_parser::SurfaceMatchArm>,
    /// Fully-qualified names of the sibling mutual functions (e.g.
    /// `["Tree.sizeList"]`). Copied into the fused def's `RecursiveDefContext`
    /// by `setup_recursion` so a sibling self-call inside a minor body
    /// (`Tree.sizeList rest`) is recognized as recursive and rewritten to its IH.
    pub sibling_func_names: Vec<String>,
}

/// Context for elaborating the body of a for/while/repeat loop (#1818 Phase 4C).
///
/// Lean 4 (BuiltinDo/For.lean) handles break/continue/return inside loops
/// by mapping them to ForInStep.done/ForInStep.yield with the current
/// accumulator state. The ControlStack's BreakT/ContinueT layers are only
/// used when break/continue must tunnel through non-algebraic combinators
/// (e.g., tryCatch inside the loop body).
///
/// When `DoLoopContext` is active:
/// - `break` → `Pure.pure (ForInStep.done σ_value)`
/// - `continue` → `Pure.pure (ForInStep.yield σ_value)`
/// - Fall-through → `Pure.pure (ForInStep.yield σ_value)`
pub(crate) struct DoLoopContext {
    /// The accumulator type σ (product of mutable variable types, or PUnit).
    pub(crate) sigma: Expr,
    /// FVarId of the accumulator parameter in the loop body lambda.
    pub(crate) acc_fvar: FVarId,
    /// Universe level for ForInStep (same as DoMonadInfo.u).
    pub(crate) u_level: Level,
    /// Mutable variables threaded through the accumulator.
    /// Each entry is (name, fvar_id, type) where fvar_id refers to the
    /// destructured projection from the accumulator (set at iteration start).
    /// Empty when accumulator is just PUnit (no mutable vars in loop body).
    pub(crate) mut_vars: Vec<(String, FVarId, Expr)>,
    /// Return type ρ when early return is tunneled through the accumulator.
    /// When Some(ρ), the accumulator includes an `Option ρ` component:
    /// - `return e` → `ForInStep.done (Some e, mutVars)`
    /// - break/continue → `ForInStep.done/yield (None, mutVars)`
    ///
    /// After the loop, the Option is case-split to propagate the return.
    /// Reference: Lean 4 BuiltinDo/For.lean:96-110 (`useLoopMutVars`).
    pub(crate) return_type: Option<Expr>,
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a surface expression in *checking mode* against an expected
    /// kernel type.
    ///
    /// Public wrapper over the internal [`Self::elaborate_with_expected_type`].
    /// Unlike [`Self::elaborate`] (pure inference), this propagates
    /// `expected_ty` into elaboration so that, in particular, universe-level
    /// unification ties the term's binder universes to the expected type's
    /// universe parameters. This is what a value must do to share universe
    /// parameters with its declared type (a bare `elaborate` freshens the
    /// term's universes independently, so the two can diverge in name).
    pub fn elaborate_with_type(
        &mut self,
        surface: &SurfaceExpr,
        expected_ty: Expr,
    ) -> Result<Expr, ElabError> {
        self.elaborate_with_expected_type(surface, Some(expected_ty))
    }

    /// Elaborate a surface expression to a kernel expression
    ///
    /// # REQUIRES
    /// - `surface` is a valid surface expression from the parser
    ///
    /// # ENSURES
    /// - On success, returns kernel `Expr` with de Bruijn indices
    /// - Named bindings are converted to de Bruijn indices
    /// - Macros are expanded before elaboration
    /// - Type inference inserts implicit arguments
    pub fn elaborate(&mut self, surface: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Commit any pending level assignments from previous kernel callbacks
        // before starting a new elaboration step.
        self.commit_pending_level_assigns();

        // Unwrap a parenthesized control-flow / binder node *before* the
        // macro-expansion-bypass checks below. Parentheses are pure syntactic
        // grouping and must never change elaboration semantics, but the bypass
        // checks match the bare variant (`If`, `Match`, `Lambda`, …) only — a
        // `Paren(If …)` would otherwise fall through to whole-expression macro
        // expansion, which rewrites the inner `If` into an `ite` *application*.
        // That loses both the `Bool.rec` routing (so a `Bool` condition lands
        // in `ite`'s `c : Prop` slot) AND the expected-type propagation into the
        // branches (so `id8 (if b then 1 else 0) : UInt8` defaults the branch
        // literals to `Nat`). Re-entering `elaborate` on the inner node — with
        // `current_expected_type` untouched — routes it straight to its dedicated
        // elaborator, exactly as the bare form already is. Inner is still
        // macro-expanded individually by that re-entry, so nested macros are
        // unaffected. Scoped to the variants that have a pre-macro bypass so all
        // other parenthesized expressions keep their existing (post-expansion)
        // handling at the `Paren` arm below.
        if let SurfaceExpr::Paren(_, inner) = surface {
            // A parenthesized ascription carrying a `by`-block / `calc` / `do`
            // (the `(by tac : T)` inline-proof idiom) must be unwrapped here too:
            // the parser yields `Paren(Ascription(ByTactic …, T))`, and letting
            // the whole `Paren` blob reach `expand_macros` collapses the nested
            // `ByTactic` into `ByTactic([])` (its children are discarded by the
            // syntax roundtrip). Re-entering `elaborate` on the inner ascription
            // routes it straight to the retry-sensitive `Ascription` bypass
            // below, which hands the by-block its ascribed type as the expected
            // goal — matching the bare-`by`-block-as-body behavior. Scoped by
            // `contains_retry_sensitive_surface` so an ordinary `(h : p)` keeps
            // its existing post-expansion handling at the `Paren` arm below.
            if let SurfaceExpr::Ascription(_, asc_expr, _) = inner.as_ref() {
                if Self::contains_retry_sensitive_surface(asc_expr) {
                    return self.elaborate(inner);
                }
            }
            // A bare parenthesized `by`-block / `calc`-block in subterm position
            // (`(by exact 2) + 3`, `def n : Nat := (by exact 2)`) must unwrap
            // here for the same reason as the `Paren(Ascription(by …))` case
            // above: letting `Paren(ByTactic …)` reach `expand_macros` collapses
            // the nested `ByTactic` into `ByTactic([])` (the syntax roundtrip
            // discards its tactic children — see the `ByTactic` bypass below), so
            // the tactic block runs ZERO tactics and the goal is left unsolved
            // (`UnsolvedGoals ⊢ Nat`). Re-entering `elaborate` on the inner block
            // — with `current_expected_type` untouched — routes it straight to
            // the dedicated `elab_by_tactic`/`elab_calc` path with the surrounding
            // expected type as its goal, exactly as a bare (unparenthesized) `by`
            // block already is.
            if matches!(
                inner.as_ref(),
                SurfaceExpr::If(..)
                    | SurfaceExpr::IfLet(..)
                    | SurfaceExpr::IfDecidable(..)
                    | SurfaceExpr::Match(..)
                    | SurfaceExpr::PatternMatchLambda(..)
                    | SurfaceExpr::Lambda(..)
                    // `Paren(Let …)` must re-enter `elaborate` too: a bare `Let`
                    // has its own bypass (below), but a PARENTHESIZED one —
                    // `(let x := match e with …; body) : T`, the shape a
                    // `theorem : (let … ) = v := rfl` LHS takes — otherwise falls
                    // through to `expand_macros`, which collapses the let value's
                    // nested `match` (leaking a motive FVar). Routing to
                    // `elab_let`/`elab_let_rec`/`elaborate_let_q_pattern` keeps the
                    // value/body intact, exactly like the bare-`Let` bypass.
                    | SurfaceExpr::Let(..)
                    | SurfaceExpr::LetRec(..)
                    | SurfaceExpr::LetPattern(..)
                    | SurfaceExpr::Do(..)
                    | SurfaceExpr::ByTactic(..)
                    | SurfaceExpr::CalcBlock(..)
            ) {
                return self.elaborate(inner);
            }
            // A parenthesized APPLICATION (or a further-parenthesized block) that
            // transitively carries a `by`/`calc`/`do` block — e.g. the argument
            // `(some (by exact 7))` in `some (some (by exact 7))` is parsed as
            // `Paren(App(some, [by exact 7]))`, and a doubly-parenthesized block
            // `((by exact 7))` as `Paren(Paren(ByTactic …))`. Neither the
            // bare-variant unwrap above nor the `App` retry-sensitive bypass below
            // matches a `Paren(App …)` / `Paren(Paren …)`, so it would fall through
            // to `expand_macros`, which collapses the nested `ByTactic` into
            // `ByTactic([])` and DROPS the tactics — the block then runs zero
            // tactics and leaves the (now correctly-typed) goal unsolved
            // (`UnsolvedGoals ⊢ Nat`). Parentheses are pure syntactic grouping, so
            // re-entering `elaborate` on the inner node — with
            // `current_expected_type` untouched — routes it straight to the `App`
            // retry-sensitive bypass (or the inner `Paren(ByTactic)` unwrap),
            // keeping the tactic children intact. Scoped to nodes that actually
            // contain a retry-sensitive block so ordinary `(f x)` / `((e))` keep
            // their existing post-expansion handling at the `Paren` arm below.
            if matches!(
                inner.as_ref(),
                SurfaceExpr::App(..) | SurfaceExpr::Paren(..)
            ) && Self::contains_retry_sensitive_surface(inner)
            {
                return self.elaborate(inner);
            }
        }

        // Do-notation has a dedicated elaboration path that handles its own
        // desugaring. Skip macro expansion for Do blocks to avoid the macro
        // system converting them into raw identifiers (e.g., `return e` → `pure e`)
        // that would require additional name resolution infrastructure.
        if let SurfaceExpr::Do(_, elems) = surface {
            return self.elab_do(elems);
        }

        // ByTactic and CalcBlock have dedicated elaboration paths. Skip macro
        // expansion because surface_to_syntax discards their children (tactics/
        // steps) into empty opaque nodes. While syntax_to_surface now preserves
        // the variant type (Part of #2060), the content is irrecoverably lost.
        // Fix for #2211.
        if let SurfaceExpr::ByTactic(_, tactics) = surface {
            return self.elab_by_tactic(tactics);
        }
        if let SurfaceExpr::CalcBlock(_, steps) = surface {
            return self.elab_calc(steps);
        }
        if let SurfaceExpr::IfLet(_, pat, scrutinee, then_br, else_br) = surface {
            return self.elab_if_let(pat, scrutinee, then_br, else_br);
        }
        // Bypass macro expansion for pattern lambdas and matches.
        //
        // The built-in single-arm match macro rewrites `match e with | p => b`
        // through a hygienic lambda application. The syntax roundtrip used by
        // `expand_macros` loses that scoped gensym bookkeeping, which can leak
        // bogus identifiers like `_x_1` and turn qualified constructor patterns
        // into lambda binders. Elaborating the original surface nodes directly
        // keeps nested macros in subterms reachable without corrupting patterns.
        if let SurfaceExpr::PatternMatchLambda(_, binders, body) = surface {
            return self.elab_pattern_lambda(binders, body);
        }
        if let SurfaceExpr::Match(_, hyp, scrutinee, arms) = surface {
            return self.elab_match(hyp.as_deref(), scrutinee, arms);
        }
        // Holes carry their source span, which the macro syntax roundtrip
        // (`surface → syntax → surface`) discards (resetting it to a dummy
        // `(0, 0)`). A `_` has nothing to expand, so elaborate it directly to
        // preserve the span for IDE hole contexts (`$/lean/plainTermGoal`).
        // A `?name` named hole also bypasses expansion here: the roundtrip would
        // discard the name too, and `elab_hole` needs it to tag the refine goal.
        if let SurfaceExpr::Hole(span) = surface {
            return Ok(self.elab_hole(*span, None));
        }
        if let SurfaceExpr::NamedHole(span, name) = surface {
            return Ok(self.elab_hole(*span, Some(name)));
        }
        // Bypass macro expansion for if-then-else, exactly like Match/IfLet/
        // PatternMatchLambda above. The `surface → syntax → surface` macro
        // roundtrip rewrites a structured `If` into an `ite` *application*, which
        // then elaborates via `elab_app` and passes the condition straight into
        // `ite`'s `c : Prop` slot — rejecting a `Bool` condition ("expected
        // Sort(Zero), got Bool"). `elab_if` handles Bool conditions (via Bool.rec)
        // and Prop conditions (via ite) directly, so route `If` there.
        if let SurfaceExpr::If(_, cond, then_br, else_br) = surface {
            return self.elab_if(cond, then_br, else_br);
        }
        // `if h : c then … else …` (dependent-if / `IfDecidable`), for the same
        // reason as the plain `If` above and `Match`/`IfLet`. Without a standalone
        // bypass the `surface → syntax → expand → surface` roundtrip collapses the
        // structured node and mangles a nested `match`/`if` in either branch (e.g.
        // `if h : c then (match e with …) else …` — the match loses its scoped
        // gensym bookkeeping and leaks a motive FVar). `elab_if_decidable`
        // re-enters `elaborate` on both branches, so a nested block hits its own
        // bypass intact. (The plain `If` bypass never matches this variant.)
        if let SurfaceExpr::IfDecidable(_, witness_name, prop, then_br, else_br) = surface {
            return self.elab_if_decidable(witness_name, prop, then_br, else_br);
        }
        // Bypass whole-expression macro expansion for `Lambda`/`Pi` binders, for
        // the same reason as `If`/`Match` above: the `surface → syntax → expand
        // → surface` roundtrip rewrites a *nested* `If` inside the body into an
        // `ite` application, so a `fun id' => if (b : Bool) … ` body loses the
        // `Bool.rec` routing and the `Bool` condition lands in `ite`'s `c : Prop`
        // slot ("expected Sort(Zero), got Bool"). `elab_lambda`/`elab_pi`
        // re-enter `elaborate` for each binder type and the body, so every
        // sub-node (including a nested `If`, which then hits its own bypass
        // above) is still macro-expanded individually — the body just is not
        // collapsed as one blob. Mirrors the existing `PatternMatchLambda`
        // bypass, which already routes binder+body straight to its elaborator.
        if let SurfaceExpr::Lambda(_, binders, body) = surface {
            return self.elab_lambda(binders, body);
        }
        if let SurfaceExpr::Pi(_, binders, body) = surface {
            return self.elab_pi(binders, body);
        }
        // Bypass whole-expression macro expansion for `let`/`let rec`/`let pattern`,
        // for the same reason as `If`/`Match`/`Lambda`/`Pi` above. The `surface →
        // syntax → expand → surface` roundtrip collapses a structured `If` *inside
        // the let body* (most commonly a `match` arm whose body is
        // `if … then .ok … else .error …`) into an `ite` *application*: the
        // condition lands in `ite`'s `c : Prop` slot and the anonymous
        // constructors `.ok`/`.error` become bare application arguments with no
        // expected type, so they fail to resolve ("UnknownIdent `.error`"). This
        // is the pervasive `let m := …; match … | … => if … then .error … else
        // .ok …` shape in trust-ir's `Semantics/{Arith,Cast,Compare}.lean`.
        // `elab_let`/`elab_let_rec`/`elaborate_let_q_pattern` re-enter `elaborate` for the
        // bound value and the body, so every sub-node (the inner `match`, which
        // hits its own bypass above, and that match's arm `If`s) is still
        // macro-expanded individually — the let body just is not collapsed as one
        // blob. Mirrors the `Lambda`/`Pi` bypass exactly. (Track KL)
        if let SurfaceExpr::Let(_, binder, val, body) = surface {
            return self.elab_let(binder, val, body);
        }
        if let SurfaceExpr::LetRec(_, binder, val, body) = surface {
            return self.elab_let_rec(binder, val, body);
        }
        if let SurfaceExpr::LetPattern(_, pattern, scrutinee, fallback, body) = surface {
            return self.elaborate_let_q_pattern(pattern, scrutinee, fallback, body);
        }

        // Bypass whole-expression macro expansion for term-level `open X in
        // <term>`. The `surface → syntax → expand → surface` roundtrip has no
        // faithful `openIn` node, so it collapses the construct to an opaque
        // `Ident("openIn")` and the namespace path is lost. `elab_open_in`
        // opens the namespaces, then re-enters `elaborate` on the sub-term
        // (which macro-expands it individually), and pops the scope. Mirrors
        // the `Let`/`Lambda`/`Pi` bypasses above.
        if let SurfaceExpr::OpenIn {
            paths,
            scoped,
            body,
            ..
        } = surface
        {
            return self.elab_open_in(paths, *scoped, body);
        }

        // Bypass whole-expression macro expansion for a type ascription
        // `(e : T)` whose ascribed term contains a `by`-block / `calc` / `do`
        // (or explicit `sorry`) — the `(by tac : T)` inline-proof idiom. Same
        // reason as `If`/`Match`/`Lambda`/`Let`/anonymousCtor above: the
        // `surface → syntax → expand → surface` roundtrip discards the children
        // of a nested `ByTactic`/`CalcBlock` into empty opaque nodes (see the
        // `ByTactic` bypass above), so `(by exact h : p)` reaches
        // `elab_ascription` with the inner block collapsed to `ByTactic([])`.
        // The zero-tactic block then leaves the goal unsolved (auto-`sorry`) or
        // assembles a mis-universed identity-lambda wrapper the kernel rejects
        // (`Sort(Succ Zero)` vs `Sort(Zero)`). `elab_ascription` re-enters
        // `elaborate`/`elaborate_with_expected_type` on both the ascribed term
        // and the type, so every sub-node — including the `by …` block, which
        // then hits its own bypass above with the ascribed type as its expected
        // goal — is still macro-expanded individually, just not collapsed as one
        // blob. Scoped by `contains_retry_sensitive_surface` so ordinary
        // ascriptions (`(h : p)`) keep their existing post-expansion handling
        // verbatim at the `Ascription` arm below.
        if let SurfaceExpr::Ascription(_, expr, ty) = surface {
            if Self::contains_retry_sensitive_surface(expr) {
                return self.elab_ascription(expr, ty);
            }
        }

        // Bypass whole-expression macro expansion for the anonymous constructor
        // `⟨…⟩` (parsed as `App(Ident("anonymousCtor"), args)`), for the same
        // reason as `If`/`Match`/`Lambda`/`Let` above. The `surface → syntax →
        // expand → surface` roundtrip discards the children of a *nested*
        // `ByTactic`/`CalcBlock` component into empty opaque nodes (see the
        // `ByTactic` bypass above): a `⟨1, by omega⟩` would reach
        // `elab_anonymous_ctor` with the second component collapsed to
        // `ByTactic([])`, so the tactic block runs zero tactics and the goal is
        // left unsolved. Routing the anonymous constructor straight to `elab_app`
        // keeps each component intact; `elab_anonymous_ctor` re-enters
        // `elaborate` per component (via `elaborate_with_expected_type`), so every
        // sub-node — including a `by …` block, which then hits its own bypass
        // above — is still macro-expanded individually, just not collapsed as one
        // blob. Mirrors the `Lambda`/`Pi`/`Let` bypass exactly. (#172 + #2211)
        if let SurfaceExpr::App(_, func, args) = surface {
            // A fully-applied lambda with UNTYPED binders, e.g. `(· + ·) x y`
            // (a `·`-section desugars to `fun __cdot_0 __cdot_1 => …`) or a
            // hand-written `(fun a b => a + b) x y`. Applied as an application
            // HEAD, an untyped binder's type is still a metavar when the body
            // elaborates, so a body that uses the binder type-dependently — an
            // arithmetic `a + b` (whose `HAdd`/`Add` instance resolves the OPEN
            // carrier to a `UInt64` default before the arguments pin it), or a
            // binder used as a FUNCTION head (`mp ha`, which fails
            // `TooManyArguments` on a metavar-typed head) — mis-elaborates:
            // `(· + ·) p.1 p.2` with `p : Nat × Nat` fails "expected UInt64, got
            // Nat" (bare-literal `(· + ·) 3 4` and ascribed `((· + ·) : Nat → Nat
            // → Nat) …` work because the types are already pinned). Rewrite the
            // fully-applied form to a `let`-chain binding each binder to its
            // argument, so the argument pins the binder's type BEFORE the body is
            // elaborated (beta ≡ let for these non-dependent binders — every
            // binder is untyped, so none names another's type; `add_decl`
            // re-checks the result). Only the fully-applied, all-untyped-binder
            // form; a typed binder (`fun (a : T) => …`) already pins its own type
            // and is left as an ordinary β-redex.
            if let SurfaceExpr::Lambda(_, binders, body) = Self::unwrap_surface_parens(func) {
                if !binders.is_empty()
                    && args.len() == binders.len()
                    && binders.iter().all(|b| b.ty.is_none())
                {
                    let mut rewritten = (**body).clone();
                    for (binder, arg) in binders.iter().zip(args.iter()).rev() {
                        rewritten = SurfaceExpr::Let(
                            func.span(),
                            binder.clone(),
                            Box::new(arg.expr.clone()),
                            Box::new(rewritten),
                        );
                    }
                    return self.elaborate(&rewritten);
                }
            }
            // A prelude combinator (`∘`/`Function.comp`, `flip`, `Function.const`)
            // APPLIED to arguments. Clean has none of these consts — each desugars
            // to a defeq lambda in `elaborate_surface_inner`, but only for its BARE
            // form. The parser nests an applied combinator as
            // `App(App(comb, [inner…]), [outer…])`; the desugared lambda then serves
            // as an application HEAD, which trips unannotated-binder inference and
            // yields a spurious type mismatch. Rewrite the whole nested form to the
            // beta-reduced surface term directly (all types pinned by the operands,
            // no intermediate lambda); chained/curried forms recompose through
            // re-elaboration. The bare combinator (no outer application) keeps its
            // lambda desugar. Mirrors the beta≡let rewrite below.
            //   `(f ∘ g) x rest…`            ⇝ `f (g x) rest…`
            //   `(flip g) a b rest…`         ⇝ `g b a rest…`
            //   `(Function.const β a) x rest…` ⇝ `a rest…`   (const ignores `x`)
            if !args.is_empty() {
                if let SurfaceExpr::App(_, inner_func, inner_args) =
                    Self::unwrap_surface_parens(func)
                {
                    let sp = func.span();
                    let apply_rest = |head: SurfaceExpr, rest: &[SurfaceArg]| {
                        if rest.is_empty() {
                            head
                        } else {
                            SurfaceExpr::App(sp, Box::new(head), rest.to_vec())
                        }
                    };
                    let reduced: Option<SurfaceExpr> =
                        match Self::func_qualified_name(inner_func).as_deref() {
                            Some("Function.comp") if inner_args.len() == 2 => {
                                let g_x = SurfaceExpr::App(
                                    sp,
                                    Box::new(inner_args[1].expr.clone()),
                                    vec![SurfaceArg::positional(args[0].expr.clone())],
                                );
                                let f_g_x = SurfaceExpr::App(
                                    sp,
                                    Box::new(inner_args[0].expr.clone()),
                                    vec![SurfaceArg::positional(g_x)],
                                );
                                Some(apply_rest(f_g_x, &args[1..]))
                            }
                            Some("flip") if inner_args.len() == 1 && args.len() >= 2 => {
                                let g_b_a = SurfaceExpr::App(
                                    sp,
                                    Box::new(inner_args[0].expr.clone()),
                                    vec![
                                        SurfaceArg::positional(args[1].expr.clone()),
                                        SurfaceArg::positional(args[0].expr.clone()),
                                    ],
                                );
                                Some(apply_rest(g_b_a, &args[2..]))
                            }
                            Some("Function.const") if inner_args.len() == 2 => {
                                Some(apply_rest(inner_args[1].expr.clone(), &args[1..]))
                            }
                            _ => None,
                        };
                    if let Some(applied) = reduced {
                        return self.elaborate(&applied);
                    }
                }
            }
            // `(fun p => match p with …) a` with an UNANNOTATED binder whose body
            // directly matches ON that binder: `p`'s type is a fresh metavar when
            // `elab_app` elaborates the lambda body, so the match cannot determine
            // `p`'s constructor and fails. Rewrite the beta-redex to `let p := a;
            // match p with …` — the argument pins `p`'s type before the body is
            // elaborated (beta ≡ let for a non-dependent binder; `add_decl`
            // re-checks the result). Narrowly scoped: a single unannotated binder,
            // a single argument, and a `Match` body whose scrutinee IS the binder —
            // exactly the failing shape. An annotated binder (`fun (p : T) => …`)
            // and a non-`match` body already elaborate correctly, so they are left
            // untouched.
            if let SurfaceExpr::Lambda(_, binders, body) = Self::unwrap_surface_parens(func) {
                if binders.len() == 1 && binders[0].ty.is_none() && args.len() == 1 {
                    if let SurfaceExpr::Match(_, _, scrut, _) = Self::unwrap_surface_parens(body) {
                        if matches!(
                            Self::unwrap_surface_parens(scrut),
                            SurfaceExpr::Ident(_, n) if *n == binders[0].name
                        ) {
                            let let_expr = SurfaceExpr::Let(
                                func.span(),
                                binders[0].clone(),
                                Box::new(args[0].expr.clone()),
                                Box::new((**body).clone()),
                            );
                            return self.elaborate(&let_expr);
                        }
                    }
                }
            }
            if matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "anonymousCtor") {
                return self.elab_app(func, args);
            }
            // Bypass whole-application macro expansion when a positional argument
            // carries a `by`-block / `calc` / `do` (or explicit `sorry`) — most
            // commonly the `(by tac : T)` inline-proof idiom in an operator or
            // ordinary-call argument position (`(by exact g : Nat) + 1` desugars
            // to `App(Ident "HAdd.hAdd", [(by … : Nat), 1])`). The `surface →
            // syntax → expand → surface` roundtrip on the whole application would
            // collapse the nested `ByTactic` into `ByTactic([])` (its children are
            // discarded), so the tactic block runs zero tactics and the goal is
            // left unsolved. Routing straight to `elab_app` keeps each argument
            // intact; `elab_app` re-elaborates every argument via
            // `elaborate_with_expected_type`, so the retry-sensitive argument hits
            // the `Ascription`/`ByTactic` bypasses above (macro-expanded
            // individually), just not collapsed as one blob. Mirrors the
            // `anonymousCtor` bypass. Restricted to a plain `Ident`/`Proj` head
            // (the desugared-operator and ordinary-call shapes) so a genuinely
            // macro-headed application keeps its existing whole-expression
            // expansion; and only fires when an argument is actually
            // retry-sensitive, so ordinary applications are unaffected.
            if matches!(
                func.as_ref(),
                SurfaceExpr::Ident(..) | SurfaceExpr::Proj(..)
            ) && args
                .iter()
                .any(|arg| Self::contains_retry_sensitive_surface(&arg.expr))
            {
                return self.elab_app(func, args);
            }
            // A retry-sensitive HEAD — most commonly an inline applied lambda
            // whose body is a `match`/`by`/`do` block: `(fun p => match p with
            // …) x`. The head carries a nested match that the `surface → syntax →
            // expand → surface` roundtrip would mangle (the match loses its scoped
            // gensym bookkeeping and its pattern binders get rebound at the wrong
            // constructor positions — e.g. a `(a, b)` tuple pattern's `a`/`b` end
            // up typed `Sort u` instead of the field values, so `a + b` fails
            // `HAdd Sort …`). The Ident/Proj-head cases above never match such a
            // head (a `Paren(Lambda …)`), so route it to `elab_app`, which
            // elaborates the head via `elaborate` — hitting the head's own
            // `Paren`/`Lambda`/`Match` bypass with the match intact. Mirrors the
            // retry-sensitive-argument case; fires only when the head is actually
            // retry-sensitive, so ordinary applications are unaffected.
            if Self::contains_retry_sensitive_surface(func) {
                return self.elab_app(func, args);
            }
        }

        // Bypass whole-expression macro expansion for a record/structure literal
        // `{ f := … }` whose field value (or `with`-base) carries a `by`-block /
        // `calc` / `do` (or explicit `sorry`). The `surface → syntax → expand →
        // surface` roundtrip collapses a nested `ByTactic` field value into
        // `ByTactic([])` (its tactic children discarded — see the `ByTactic`
        // bypass above), so `{ n := by exact 5 }` reaches `elab_struct_lit` with
        // the field's tactic block empty: it runs ZERO tactics and leaves the
        // field goal unsolved (`UnsolvedGoals ⊢ Nat`). Routing straight to
        // `elab_struct_lit` keeps each field intact; it re-elaborates every field
        // value via `elaborate_with_expected_type`, so a retry-sensitive field
        // hits the `Ascription`/`ByTactic` bypasses above (macro-expanded
        // individually), just not collapsed as one blob. Mirrors the
        // `anonymousCtor`/`App` bypass; fires only when a field/base is actually
        // retry-sensitive, so ordinary record literals keep their existing
        // post-expansion handling verbatim.
        if let SurfaceExpr::StructLit {
            struct_type,
            base,
            fields,
            ..
        } = surface
        {
            if fields
                .iter()
                .any(|f| Self::contains_retry_sensitive_surface(&f.val))
                || base
                    .as_deref()
                    .is_some_and(Self::contains_retry_sensitive_surface)
            {
                return self.elab_struct_lit(struct_type, base, fields);
            }
        }

        // A field projection `e.field` whose BASE carries a `match`/`by`/`do`
        // block — `(⟨match e with …, y⟩ : T).1`. `Proj` is not otherwise bypassed,
        // so the whole `Proj(…)` reaches `expand_macros`, which mangles the nested
        // match (it leaks a motive FVar, so the projected value's type is a loose
        // fvar and `.1` fails `TooManyArguments FVar(..)`). Route to `elab_proj`,
        // which elaborates the base via `elaborate` — hitting the base's own
        // `Ascription`/`anonymousCtor`/`Match` bypass with the block intact.
        // Mirrors the App-head/argument bypasses; fires only when the base is
        // actually retry-sensitive, so ordinary projections are unaffected.
        if let SurfaceExpr::Proj(_, base, proj) = surface {
            if Self::contains_retry_sensitive_surface(base) {
                return self.elab_proj(base, proj);
            }
        }

        let expanded = self.expand_macros(surface)?;

        // Phase 5: user-defined term elaborators (`elab "kw" e:term : term => b`).
        // A keyword in term position parses as an ordinary identifier, so a call
        // `kw e` arrives here as `App(Ident("kw"), [e])` (or bare `Ident("kw")`
        // when nullary). If the head matches a registered keyword and the arity
        // matches, bind the call-site arguments to the pattern variables,
        // substitute them into the body surface AST, and re-elaborate the
        // substituted body through this same pipeline. Soundness: the body is
        // elaborated and kernel-checked exactly like any other term — no bypass.
        if !self.user_term_elabs.is_empty() {
            if let Some((kw, args)) =
                user_term::match_user_term_call(&expanded, &self.user_term_elabs)
            {
                // Clone the entry out so the immutable borrow on `self` ends
                // before the recursive `elaborate(&mut self, ...)` call.
                if let Some(entry) = self.user_term_elabs.get(kw).cloned() {
                    if let Some(substituted) = user_term::build_substituted_body(&entry, &args) {
                        // A supported `throwError "msg"` body raises the user's
                        // custom error as a typed diagnostic: it produces no term
                        // and fabricates nothing — it only makes elaboration FAIL
                        // with exactly the user's message.
                        if let Some(message) = user_tactic::as_throw_error_message(&substituted) {
                            return Err(ElabError::UserThrowError { message });
                        }
                        // Value channel / query evaluator: a body in the
                        // value-channel shape (`inferType e`, or `let t :=
                        // inferType e; t`) computes a kernel `Expr` value from the
                        // elaboration state, which has no surface form to rewrite
                        // back into. It is evaluated here (queries read from the
                        // kernel-checked elaboration state; bound values splice as
                        // already-elaborated `Expr`s). A non-query body returns
                        // `None` and falls through to the constructor evaluator.
                        if let Some(result) = self.eval_meta_query_body(&substituted) {
                            return result;
                        }
                        // Computed control flow: a body `if <cond> then <a> else
                        // <b>` whose condition whnf-reduces to a concrete
                        // `Bool.true`/`Bool.false` is a metaprogram-time decision —
                        // elaborate only the selected branch (kernel-checked by the
                        // normal pipeline). A condition that does NOT reduce to a
                        // concrete Bool (stuck / symbolic / non-Bool) returns `None`
                        // and falls through to the ordinary `elab_if` path below, so
                        // it fails honestly (or builds the runtime `ite`) rather
                        // than guessing a branch.
                        if let Some(result) = self.eval_meta_if_body(&substituted) {
                            return result;
                        }
                        // Value-constructor evaluator: if the (substituted) body is
                        // written in `MetaM`/`TermElabM` constructor style
                        // (`mkConst`/`mkApp`/`Expr.const`/`Expr.app`), rewrite those
                        // builtin calls into the equivalent ordinary surface
                        // expression first. The rewrite is purely syntactic; the
                        // result is elaborated and kernel-checked by this same
                        // pipeline, so an unknown name or ill-typed application
                        // fails honestly — no kernel bypass.
                        let body = meta_builtin::rewrite_meta_builtins(&substituted)
                            .unwrap_or(substituted);
                        return self.elaborate(&body);
                    }
                }
            }
        }

        // Phase A: Try user-registered term elaborators before the hardcoded
        // match. Extract the handler (clone the Arc) to avoid holding a borrow
        // on term_elab_registry while passing &mut self to the handler.
        let kind = surface_expr_kind_name(&expanded);
        let user_handler = self.term_elab_registry.get_user_handler(kind);
        if let Some(handler) = user_handler {
            let expected = self.current_expected_type.clone();
            match (handler)(&expanded, expected.as_ref(), self) {
                Ok(expr) => {
                    self.commit_pending_level_assigns();
                    return Ok(expr);
                }
                Err(ElabError::NotImplemented(_)) => {
                    // Fall through to hardcoded dispatch
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }

        let result = stack_safe(|| self.elaborate_surface_inner(&expanded));

        // Commit level assignments discovered during this elaboration step
        self.commit_pending_level_assigns();

        result
    }

    /// Inner hardcoded dispatch for surface expression elaboration.
    ///
    /// Factored out from `elaborate()` so that the term elab registry can be
    /// consulted first, and this serves as the fallback. Each arm here
    /// corresponds to a builtin `SurfaceExpr` variant handler.
    /// The fully-qualified name a function-head surface expr denotes, unifying
    /// the flat-ident form (`Ident("Function.comp")`, e.g. the `∘` operator's
    /// output) with the projection form a literal qualified name parses to
    /// (`Function.const` ⇒ `Proj(Ident("Function"), Named("const"))`). Lets the
    /// prelude-combinator desugars (`∘`/`flip`/`Function.const`) recognize their
    /// head however it was written. `None` for a non-name head.
    fn func_qualified_name(e: &SurfaceExpr) -> Option<String> {
        match e {
            SurfaceExpr::Ident(_, n) => Some(n.clone()),
            SurfaceExpr::Proj(_, base, Projection::Named(field)) => match base.as_ref() {
                SurfaceExpr::Ident(_, ns) => Some(format!("{ns}.{field}")),
                _ => None,
            },
            _ => None,
        }
    }

    fn elaborate_surface_inner(&mut self, expanded: &SurfaceExpr) -> Result<Expr, ElabError> {
        match expanded {
            SurfaceExpr::Ident(_, name) if name == "sorry" => self.elab_explicit_sorry(),

            SurfaceExpr::Ident(_, name) if name == "inferInstance" => self.elab_infer_instance(),

            SurfaceExpr::Ident(_, name) => self.elab_ident(name),

            SurfaceExpr::SyntheticSorry(_) => self.elab_synthetic_sorry(),

            SurfaceExpr::Universe(_, univ) => self.elab_universe(univ),

            // A bare negative numeric literal `-n` (`App(Neg.neg, [literal])`)
            // with no contextual expected type defaults to `Int`, not `Nat`:
            // `Nat` has no `Neg`, so `def x := -5` / `#check -5` must land at
            // `Int` (Lean's behavior). Re-elaborating with `Int` as the expected
            // type propagates it to the literal and resolves `Neg Int`. Guarded
            // to a single bare `Nat`-literal argument with no expected type, so
            // `(-5 : Float)`, `-x`, and type-pinned contexts are untouched.
            SurfaceExpr::App(_, func, args)
                if self.current_expected_type.is_none()
                    && args.len() == 1
                    && matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "Neg.neg")
                    && matches!(
                        args[0].expr,
                        SurfaceExpr::Lit(_, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_))
                    ) =>
            {
                let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
                self.elaborate_with_expected_type(expanded, Some(int_ty))
            }

            // `f ∘ g` (parsed as `App(Function.comp, [f, g])`). Clean's prelude
            // has no `Function.comp`, so desugar to the definitionally-equal
            // `fun x => f (g x)` — the value `Function.comp` unfolds to. A
            // correct, kernel-checkable composed function; the expected type (if
            // any) flows into the lambda so an unannotated binder is inferred.
            SurfaceExpr::App(sp, func, args)
                if args.len() == 2
                    && Self::func_qualified_name(func).as_deref() == Some("Function.comp") =>
            {
                let sp = *sp;
                let x = SurfaceExpr::Ident(sp, "_comp_x".to_string());
                let g_x = SurfaceExpr::App(
                    sp,
                    Box::new(args[1].expr.clone()),
                    vec![SurfaceArg::positional(x)],
                );
                let f_g_x = SurfaceExpr::App(
                    sp,
                    Box::new(args[0].expr.clone()),
                    vec![SurfaceArg::positional(g_x)],
                );
                let lam = SurfaceExpr::Lambda(
                    sp,
                    vec![SurfaceBinder::new(
                        "_comp_x".to_string(),
                        None,
                        SurfaceBinderInfo::Explicit,
                    )],
                    Box::new(f_g_x),
                );
                self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
            }

            // `flip g` (`Function.flip`) — absent from Clean's prelude. Desugar
            // to the defeq `fun a b => g b a`. Guarded to the single-argument
            // form (the combinator itself); further application composes via the
            // resulting lambda.
            SurfaceExpr::App(sp, func, args)
                if args.len() == 1
                    && Self::func_qualified_name(func).as_deref() == Some("flip") =>
            {
                let sp = *sp;
                let a = SurfaceExpr::Ident(sp, "_flip_a".to_string());
                let b = SurfaceExpr::Ident(sp, "_flip_b".to_string());
                let body = SurfaceExpr::App(
                    sp,
                    Box::new(args[0].expr.clone()),
                    vec![SurfaceArg::positional(b), SurfaceArg::positional(a)],
                );
                let lam = SurfaceExpr::Lambda(
                    sp,
                    vec![
                        SurfaceBinder::new(
                            "_flip_a".to_string(),
                            None,
                            SurfaceBinderInfo::Explicit,
                        ),
                        SurfaceBinder::new(
                            "_flip_b".to_string(),
                            None,
                            SurfaceBinderInfo::Explicit,
                        ),
                    ],
                    Box::new(body),
                );
                self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
            }

            // `Function.const β a` — absent from Clean's prelude. Desugar to the
            // defeq `fun _ : β => a` (the constant function ignoring a `β`); the
            // partial `Function.const β` becomes `fun a (_ : β) => a`.
            SurfaceExpr::App(sp, func, args)
                if (args.len() == 1 || args.len() == 2)
                    && Self::func_qualified_name(func).as_deref() == Some("Function.const") =>
            {
                let sp = *sp;
                let beta = args[0].expr.clone();
                let lam = if args.len() == 2 {
                    // `fun (_ : β) => a`
                    SurfaceExpr::Lambda(
                        sp,
                        vec![SurfaceBinder::new(
                            "_const_ignored".to_string(),
                            Some(beta),
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(args[1].expr.clone()),
                    )
                } else {
                    // partial: `fun a (_ : β) => a`
                    SurfaceExpr::Lambda(
                        sp,
                        vec![
                            SurfaceBinder::new(
                                "_const_a".to_string(),
                                None,
                                SurfaceBinderInfo::Explicit,
                            ),
                            SurfaceBinder::new(
                                "_const_ignored".to_string(),
                                Some(beta),
                                SurfaceBinderInfo::Explicit,
                            ),
                        ],
                        Box::new(SurfaceExpr::Ident(sp, "_const_a".to_string())),
                    )
                };
                self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
            }

            // `Function.uncurry g` — absent from the prelude. Desugar to the
            // defeq `fun p => g p.fst p.snd`. When APPLIED to its pair (and any
            // further arguments) — `Function.uncurry g p rest…`, the fully-applied
            // form the parser flattens — reduce directly to `g p.fst p.snd rest…`
            // instead of applying the desugared lambda as a head (which would trip
            // unannotated-binder inference, as for the comp/flip/const applied
            // forms). Bare `Function.uncurry g` keeps the lambda.
            SurfaceExpr::App(sp, func, args)
                if !args.is_empty()
                    && Self::func_qualified_name(func).as_deref() == Some("Function.uncurry") =>
            {
                let sp = *sp;
                if args.len() == 1 {
                    let p = SurfaceExpr::Ident(sp, "_uncurry_p".to_string());
                    let fst = SurfaceExpr::Proj(
                        sp,
                        Box::new(p.clone()),
                        Projection::Named("fst".to_string()),
                    );
                    let snd =
                        SurfaceExpr::Proj(sp, Box::new(p), Projection::Named("snd".to_string()));
                    let body = SurfaceExpr::App(
                        sp,
                        Box::new(args[0].expr.clone()),
                        vec![SurfaceArg::positional(fst), SurfaceArg::positional(snd)],
                    );
                    let lam = SurfaceExpr::Lambda(
                        sp,
                        vec![SurfaceBinder::new(
                            "_uncurry_p".to_string(),
                            None,
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(body),
                    );
                    self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
                } else {
                    // `Function.uncurry g p rest…` ⇝ `g p.fst p.snd rest…`.
                    let p = args[1].expr.clone();
                    let fst = SurfaceExpr::Proj(
                        sp,
                        Box::new(p.clone()),
                        Projection::Named("fst".to_string()),
                    );
                    let snd =
                        SurfaceExpr::Proj(sp, Box::new(p), Projection::Named("snd".to_string()));
                    let g_app = SurfaceExpr::App(
                        sp,
                        Box::new(args[0].expr.clone()),
                        vec![SurfaceArg::positional(fst), SurfaceArg::positional(snd)],
                    );
                    let applied = if args.len() > 2 {
                        SurfaceExpr::App(sp, Box::new(g_app), args[2..].to_vec())
                    } else {
                        g_app
                    };
                    self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
                }
            }

            // `Function.curry g` — absent from the prelude. Desugar to the defeq
            // `fun a b => g ⟨a, b⟩`. Applied forms (the parser flattens the spine):
            // `Function.curry g a b rest…` ⇝ `g ⟨a, b⟩ rest…` (fully applied,
            // built directly); `Function.curry g a` ⇝ `fun b => g ⟨a, b⟩` (partial).
            SurfaceExpr::App(sp, func, args)
                if !args.is_empty()
                    && Self::func_qualified_name(func).as_deref() == Some("Function.curry") =>
            {
                let sp = *sp;
                let mk_pair = |x: SurfaceExpr, y: SurfaceExpr| {
                    SurfaceExpr::App(
                        sp,
                        Box::new(SurfaceExpr::Ident(sp, "anonymousCtor".to_string())),
                        vec![SurfaceArg::positional(x), SurfaceArg::positional(y)],
                    )
                };
                if args.len() >= 3 {
                    // `g ⟨a, b⟩ rest…`
                    let pair = mk_pair(args[1].expr.clone(), args[2].expr.clone());
                    let g_app = SurfaceExpr::App(
                        sp,
                        Box::new(args[0].expr.clone()),
                        vec![SurfaceArg::positional(pair)],
                    );
                    let applied = if args.len() > 3 {
                        SurfaceExpr::App(sp, Box::new(g_app), args[3..].to_vec())
                    } else {
                        g_app
                    };
                    self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
                } else if args.len() == 2 {
                    // partial: `fun b => g ⟨a, b⟩`
                    let b_id = SurfaceExpr::Ident(sp, "_curry_b".to_string());
                    let pair = mk_pair(args[1].expr.clone(), b_id);
                    let body = SurfaceExpr::App(
                        sp,
                        Box::new(args[0].expr.clone()),
                        vec![SurfaceArg::positional(pair)],
                    );
                    let lam = SurfaceExpr::Lambda(
                        sp,
                        vec![SurfaceBinder::new(
                            "_curry_b".to_string(),
                            None,
                            SurfaceBinderInfo::Explicit,
                        )],
                        Box::new(body),
                    );
                    self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
                } else {
                    // `fun a b => g ⟨a, b⟩`
                    let a = SurfaceExpr::Ident(sp, "_curry_a".to_string());
                    let b = SurfaceExpr::Ident(sp, "_curry_b".to_string());
                    let pair = mk_pair(a, b);
                    let body = SurfaceExpr::App(
                        sp,
                        Box::new(args[0].expr.clone()),
                        vec![SurfaceArg::positional(pair)],
                    );
                    let lam = SurfaceExpr::Lambda(
                        sp,
                        vec![
                            SurfaceBinder::new(
                                "_curry_a".to_string(),
                                None,
                                SurfaceBinderInfo::Explicit,
                            ),
                            SurfaceBinder::new(
                                "_curry_b".to_string(),
                                None,
                                SurfaceBinderInfo::Explicit,
                            ),
                        ],
                        Box::new(body),
                    );
                    self.elaborate_with_expected_type(&lam, self.current_expected_type.clone())
                }
            }

            // `And.elim f h` — absent from Clean's prelude. Lean's
            // `And.elim {a b c} (f : a → b → c) (h : a ∧ b) : c := f h.left
            // h.right`. A bare `And.elim` reaches here as `Proj(And, elim)` and
            // (with `And` a type, not a value) fails "cannot extract type name".
            // Desugar the applied form directly to `f h.left h.right` — both
            // projections are registered (`And.left`/`And.right`) and reduce, so
            // the kernel re-checks a closed term; no new constant or trust.
            SurfaceExpr::App(sp, func, args)
                if args.len() >= 2
                    && Self::func_qualified_name(func).as_deref() == Some("And.elim") =>
            {
                let sp = *sp;
                let h = args[1].expr.clone();
                let h_left = SurfaceExpr::Proj(
                    sp,
                    Box::new(h.clone()),
                    Projection::Named("left".to_string()),
                );
                let h_right =
                    SurfaceExpr::Proj(sp, Box::new(h), Projection::Named("right".to_string()));
                let f_app = SurfaceExpr::App(
                    sp,
                    Box::new(args[0].expr.clone()),
                    vec![
                        SurfaceArg::positional(h_left),
                        SurfaceArg::positional(h_right),
                    ],
                );
                let applied = if args.len() > 2 {
                    SurfaceExpr::App(sp, Box::new(f_app), args[2..].to_vec())
                } else {
                    f_app
                };
                self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
            }

            // `Iff.elim f h` — absent from Clean's prelude. Lean's
            // `Iff.elim {a b c} (f : (a → b) → (b → a) → c) (h : a ↔ b) : c :=
            // f h.mp h.mpr`. A bare `Iff.elim` reaches here as `Proj(Iff, elim)`
            // and fails "cannot extract type name". `Iff.mp`/`Iff.mpr` are
            // registered, so desugar the applied form to `f h.mp h.mpr` (mirrors
            // `And.elim`); the kernel re-checks the closed term.
            SurfaceExpr::App(sp, func, args)
                if args.len() >= 2
                    && Self::func_qualified_name(func).as_deref() == Some("Iff.elim") =>
            {
                let sp = *sp;
                let h = args[1].expr.clone();
                let h_mp =
                    SurfaceExpr::Proj(sp, Box::new(h.clone()), Projection::Named("mp".to_string()));
                let h_mpr =
                    SurfaceExpr::Proj(sp, Box::new(h), Projection::Named("mpr".to_string()));
                let f_app = SurfaceExpr::App(
                    sp,
                    Box::new(args[0].expr.clone()),
                    vec![SurfaceArg::positional(h_mp), SurfaceArg::positional(h_mpr)],
                );
                let applied = if args.len() > 2 {
                    SurfaceExpr::App(sp, Box::new(f_app), args[2..].to_vec())
                } else {
                    f_app
                };
                self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
            }

            // `Or.elim h f g` — absent from Clean's prelude. Lean's
            // `Or.elim {a b c} (h : a ∨ b) (f : a → c) (g : b → c) : c`. Desugar
            // the applied form to `match h with | Or.inl x => f x | Or.inr x =>
            // g x` — the case analysis clean's match elaborator already discharges
            // for an `Or` (Prop) scrutinee; the kernel re-checks the assembled
            // recursor term. No new constant or trust.
            SurfaceExpr::App(sp, func, args)
                if args.len() >= 3
                    && Self::func_qualified_name(func).as_deref() == Some("Or.elim") =>
            {
                let sp = *sp;
                let x = SurfaceExpr::Ident(sp, "__or_elim_x".to_string());
                let inl_body = SurfaceExpr::App(
                    sp,
                    Box::new(args[1].expr.clone()),
                    vec![SurfaceArg::positional(x.clone())],
                );
                let inr_body = SurfaceExpr::App(
                    sp,
                    Box::new(args[2].expr.clone()),
                    vec![SurfaceArg::positional(x)],
                );
                let arms = vec![
                    clean_parser::SurfaceMatchArm {
                        span: clean_parser::Span::dummy(),
                        pattern: SurfacePattern::Ctor(
                            "Or.inl".to_string(),
                            vec![SurfacePattern::Var("__or_elim_x".to_string())],
                        ),
                        body: inl_body,
                    },
                    clean_parser::SurfaceMatchArm {
                        span: clean_parser::Span::dummy(),
                        pattern: SurfacePattern::Ctor(
                            "Or.inr".to_string(),
                            vec![SurfacePattern::Var("__or_elim_x".to_string())],
                        ),
                        body: inr_body,
                    },
                ];
                let m = SurfaceExpr::Match(sp, None, Box::new(args[0].expr.clone()), arms);
                let applied = if args.len() > 3 {
                    SurfaceExpr::App(sp, Box::new(m), args[3..].to_vec())
                } else {
                    m
                };
                self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
            }

            // `Not.elim h ha` — absent from Clean's prelude. Lean's
            // `Not.elim {a : Prop} (H1 : ¬a) (H2 : a) : C := absurd H2 H1`.
            // `absurd` is registered, so desugar the applied form to `absurd ha
            // h` (note the swapped order: `absurd : a → ¬a → C`).
            SurfaceExpr::App(sp, func, args)
                if args.len() >= 2
                    && Self::func_qualified_name(func).as_deref() == Some("Not.elim") =>
            {
                let sp = *sp;
                let absurd_app = SurfaceExpr::App(
                    sp,
                    Box::new(SurfaceExpr::Ident(sp, "absurd".to_string())),
                    vec![
                        SurfaceArg::positional(args[1].expr.clone()),
                        SurfaceArg::positional(args[0].expr.clone()),
                    ],
                );
                let applied = if args.len() > 2 {
                    SurfaceExpr::App(sp, Box::new(absurd_app), args[2..].to_vec())
                } else {
                    absurd_app
                };
                self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
            }

            // `Sum.elim f g s` — absent from Clean's prelude. Lean's
            // `Sum.elim {α β γ} (f : α → γ) (g : β → γ) (s : α ⊕ β) : γ` (the
            // scrutinee is the THIRD/last argument, unlike `Or.elim`). Desugar to
            // `match s with | Sum.inl a => f a | Sum.inr b => g b` — the match
            // elaborator discharges the `Sum` recursor; the kernel re-checks.
            SurfaceExpr::App(sp, func, args)
                if args.len() >= 3
                    && Self::func_qualified_name(func).as_deref() == Some("Sum.elim") =>
            {
                let sp = *sp;
                let x = SurfaceExpr::Ident(sp, "__sum_elim_x".to_string());
                let inl_body = SurfaceExpr::App(
                    sp,
                    Box::new(args[0].expr.clone()),
                    vec![SurfaceArg::positional(x.clone())],
                );
                let inr_body = SurfaceExpr::App(
                    sp,
                    Box::new(args[1].expr.clone()),
                    vec![SurfaceArg::positional(x)],
                );
                let arms = vec![
                    clean_parser::SurfaceMatchArm {
                        span: clean_parser::Span::dummy(),
                        pattern: SurfacePattern::Ctor(
                            "Sum.inl".to_string(),
                            vec![SurfacePattern::Var("__sum_elim_x".to_string())],
                        ),
                        body: inl_body,
                    },
                    clean_parser::SurfaceMatchArm {
                        span: clean_parser::Span::dummy(),
                        pattern: SurfacePattern::Ctor(
                            "Sum.inr".to_string(),
                            vec![SurfacePattern::Var("__sum_elim_x".to_string())],
                        ),
                        body: inr_body,
                    },
                ];
                let m = SurfaceExpr::Match(sp, None, Box::new(args[2].expr.clone()), arms);
                let applied = if args.len() > 3 {
                    SurfaceExpr::App(sp, Box::new(m), args[3..].to_vec())
                } else {
                    m
                };
                self.elaborate_with_expected_type(&applied, self.current_expected_type.clone())
            }

            // `nomatch e` — Lean's sugar for an arm-less match on an
            // uninhabited scrutinee. The parser produces `App(Ident("nomatch"),
            // [e])` (there is no `nomatch` in scope, so it never collides with a
            // real function). Desugar to an empty `Match`, which the empty-match
            // eliminator ([`Self::elab_empty_match`]) discharges via the
            // scrutinee type's zero-minor recursor. Multi-discriminant
            // `nomatch e₁ e₂` is not this shape — it falls through to `elab_app`
            // and fails loud on the unknown `nomatch` head.
            SurfaceExpr::App(sp, func, args)
                if args.len() == 1
                    && Self::func_qualified_name(func).as_deref() == Some("nomatch") =>
            {
                let empty_match =
                    SurfaceExpr::Match(*sp, None, Box::new(args[0].expr.clone()), Vec::new());
                self.elaborate_with_expected_type(&empty_match, self.current_expected_type.clone())
            }

            // `↑e` — Lean's prefix coercion. The lexer maps `↑`/`⇑` to
            // `Ident("↑")`, so `↑n` parses as `App(Ident("↑"), [n])`. Elaborate
            // `e` at its natural type, then coerce it to the expected type via
            // the standard `Coe`-instance machinery. Without an expected type (or
            // when no coercion is needed) the value is returned unchanged. A
            // wrong coercion still fails loud in the kernel re-check.
            SurfaceExpr::App(_, func, args)
                if args.len() == 1
                    && matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "↑") =>
            {
                let inner = self.elaborate_with_expected_type(&args[0].expr, None)?;
                if let Some(expected) = self.current_expected_type.clone() {
                    let expected = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&expected));
                    let from_ty = self.infer_type(&inner)?;
                    if let Some(coerced) = self.try_coerce(&inner, &from_ty, &expected) {
                        return Ok(coerced);
                    }
                }
                Ok(inner)
            }

            SurfaceExpr::App(_, func, args) => self.elab_app(func, args),

            // Pattern-matching lambda is elaborated the same way as regular lambda
            SurfaceExpr::Lambda(_, binders, body) => self.elab_lambda(binders, body),
            SurfaceExpr::PatternMatchLambda(_, binders, body) => {
                self.elab_pattern_lambda(binders, body)
            }

            SurfaceExpr::Pi(_, binders, body) => self.elab_pi(binders, body),

            SurfaceExpr::Arrow(_, from, to) => {
                let from_expr = self.elaborate(from)?;
                let to_expr = self.elaborate(to)?;
                let _ = self.ensure_type_expr(&from_expr)?;
                let _ = self.ensure_type_expr(&to_expr)?;
                Ok(Expr::arrow(from_expr, to_expr))
            }

            SurfaceExpr::Let(_, binder, val, body) => self.elab_let(binder, val, body),

            SurfaceExpr::Lit(_, lit) => match lit {
                SurfaceLit::Nat(n) => {
                    let n = BigNat::from_u64(*n);
                    if let Some(expected_ty) = self.current_expected_type.clone() {
                        Ok(self.elab_nat_literal_with_expected(&n, &expected_ty))
                    } else {
                        self.elab_nat_literal(&n)
                    }
                }
                // Arbitrary-precision `Nat` literal (>= 2^64). Same elaboration
                // path as the small case; the exact multi-limb value flows
                // straight through to the kernel `Literal::Nat(BigNat)`.
                SurfaceLit::BigNat(n) => {
                    if let Some(expected_ty) = self.current_expected_type.clone() {
                        Ok(self.elab_nat_literal_with_expected(n, &expected_ty))
                    } else {
                        self.elab_nat_literal(n)
                    }
                }
                SurfaceLit::String(s) => Ok(Expr::str_lit(s)),
                SurfaceLit::Char(c) => Ok(self.elab_char_literal(*c)),
                // Floating-point literals lower through the `OfScientific`
                // typeclass: `@OfScientific.ofScientific α inst m s e`. With an
                // expected type we resolve its instance; otherwise we default to
                // the prelude `Float` type (mirroring the `Nat` arm above).
                SurfaceLit::Float(s) => {
                    if let Some(expected_ty) = self.current_expected_type.clone() {
                        self.elab_float_literal_with_expected(s, &expected_ty)
                    } else {
                        self.elab_float_literal(s)
                    }
                }
            },

            SurfaceExpr::Paren(_, inner) => self.elaborate(inner),

            SurfaceExpr::Hole(span) => {
                // Create a fresh metavariable. Tag the hole metavariable with
                // its source span so IDE surfaces (e.g. `$/lean/plainTermGoal`)
                // can recover the expected type the elaborator demands at the
                // hole. The expected type is `ty_meta`, captured as the hole
                // metavariable's `ty` (instantiated as far as it is solved when
                // hole contexts are later snapshotted).
                Ok(self.elab_hole(*span, None))
            }

            // A named synthetic hole (`?name`) elaborates identically to an
            // anonymous hole — a fresh metavariable — but also records the name
            // so `refine` can tag the produced goal with it. This arm is a
            // fallback; `elaborate()` normally intercepts `NamedHole` before
            // macro expansion (which would discard the name).
            SurfaceExpr::NamedHole(span, name) => Ok(self.elab_hole(*span, Some(name))),

            SurfaceExpr::Ascription(_, expr, ty) => self.elab_ascription(expr, ty),

            SurfaceExpr::If(_, cond, then_br, else_br) => self.elab_if(cond, then_br, else_br),

            SurfaceExpr::Match(_, hyp, scrutinee, arms) => {
                self.elab_match(hyp.as_deref(), scrutinee, arms)
            }

            SurfaceExpr::OutParam(_, inner) => {
                // outParam is just a marker for type class parameters
                // During normal elaboration, we just elaborate the inner type
                self.elaborate(inner)
            }

            SurfaceExpr::SemiOutParam(_, inner) => {
                // semiOutParam is also just a marker for type class parameters
                // During normal elaboration, we just elaborate the inner type
                self.elaborate(inner)
            }

            SurfaceExpr::Proj(_, expr, proj) => self.elab_proj(expr, proj),

            SurfaceExpr::UniverseInst(_, expr, levels) => self.elab_universe_inst(expr, levels),

            SurfaceExpr::NamedArg(_, name, value) => {
                // Named argument: (name := expr)
                // This should typically appear inside an App, but if it appears standalone,
                // we just elaborate the value and ignore the name for now
                // The elaborator should handle named args in the App case
                let _ = name; // Name is used when this appears as an argument
                self.elaborate(value)
            }

            SurfaceExpr::SyntaxQuote(_, content) => self.elab_syntax_quote(content),

            SurfaceExpr::Explicit(_, inner) => self.elab_explicit(inner),

            SurfaceExpr::LetRec(_, binder, val, body) => self.elab_let_rec(binder, val, body),

            SurfaceExpr::IfLet(_, pat, scrutinee, then_br, else_br) => {
                self.elab_if_let(pat, scrutinee, then_br, else_br)
            }

            SurfaceExpr::IfDecidable(_, witness_name, prop, then_br, else_br) => {
                self.elab_if_decidable(witness_name, prop, then_br, else_br)
            }

            SurfaceExpr::LetPattern(_, pattern, scrutinee, fallback, body) => {
                self.elaborate_let_q_pattern(pattern, scrutinee, fallback, body)
            }

            SurfaceExpr::QQuotation {
                kind,
                inner,
                type_annot,
                ..
            } => self.elaborate_q_quotation(*kind, inner, type_annot.as_ref().map(|t| t.as_ref())),

            SurfaceExpr::QAntiquot { span, .. } => Err(ElabError::NotImplemented(format!(
                "antiquotation outside q(...) context at {:?}",
                span
            ))),

            SurfaceExpr::StructLit {
                struct_type,
                base,
                fields,
                ..
            } => self.elab_struct_lit(struct_type, base, fields),

            SurfaceExpr::Do(_, elems) => self.elab_do(elems),

            SurfaceExpr::ByTactic(_, tactics) => self.elab_by_tactic(tactics),

            SurfaceExpr::CalcBlock(_, steps) => self.elab_calc(steps),

            SurfaceExpr::LiftMethod(_, _) => Err(ElabError::Unsupported {
                feature: "nested action (`<-` / `←`) outside a do block".into(),
            }),

            SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
                crate::string_interpolation::elaborate_interpolation(self, *kind, parts)
            }

            // Term-level `open X in <term>`. Normally reached via the early
            // bypass in `elaborate` (before macro expansion); this arm handles
            // any residual path that reaches the inner dispatch directly.
            SurfaceExpr::OpenIn {
                paths,
                scoped,
                body,
                ..
            } => self.elab_open_in(paths, *scoped, body),
        }
    }

    /// Elaborate a term-level `open X in <term>` / `open scoped X in <term>`.
    ///
    /// SOUNDNESS (elaboration-completeness fix): this mirrors the
    /// declaration-level `SurfaceDecl::Open` handler (`elaborate_decl.rs`).
    /// Opening a namespace only affects name/instance *resolution* for the
    /// sub-term — it adds short-name aliases to `namespace_state`, which is
    /// pushed as a fresh scope and popped immediately after `body` is
    /// elaborated. The body is still fully elaborated and kernel-checked
    /// through the normal `elaborate` path; no kernel/TCB code is touched, and
    /// the opened names cannot leak past this sub-term. Previously
    /// `open_expr_body` desugared to `App(Ident("open"), …)`, discarding the
    /// namespace and leaving `open` to fail as an unknown identifier.
    ///
    /// For `scoped` we also `process_open`: Mathlib's
    /// `open scoped Classical in Decidable.…` relies on the namespace being
    /// available for name/instance resolution of the sub-term.
    fn elab_open_in(
        &mut self,
        paths: &[clean_parser::OpenPath],
        scoped: bool,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        self.namespace_state.push_scope();
        let open_result =
            crate::namespace::process_open(self.env, paths, &mut self.namespace_state).map_err(
                |e| ElabError::Unsupported {
                    feature: e.to_string(),
                },
            );
        // `scoped` currently opens the namespace identically (name / instance
        // resolution); the flag is retained for fidelity and future
        // scoped-only (notation / scoped-instance) handling.
        let _ = scoped;
        // Elaborate the body in CHECKING mode against the expected type currently
        // in scope, not plain synthesis. Lean elaborates `open X in e` against the
        // same expected type the `open … in` expression is checked against, and it
        // matters: for `theorem t : T := open scoped Classical in Decidable.foo`,
        // the body head `Decidable.foo {a b} [Decidable a]` only pins its implicit
        // Props `a`/`b` from the expected type `T`. Synthesising the body first
        // (the old `self.elaborate(body)`) left `a`/`b` as open metavars, so
        // instance search for `Decidable ?a` unified `?a` against the conclusion of
        // the first matching olean `Decidable` instance it scanned (a spurious
        // Bool-deceq garbage), producing a wrong-typed term. Threading the expected
        // type pins `a`/`b` before instance synthesis runs.
        let expected = self.current_expected_type.clone();
        let result = open_result.and_then(|()| self.elaborate_with_expected_type(body, expected));
        self.namespace_state.pop_scope();
        result
    }
}

/// Map a `SurfaceExpr` variant to its syntax kind name for registry lookup.
///
/// Each variant corresponds to a string key in the `TermElabRegistry`. The
/// naming convention follows Lean 4's syntax node kinds (lowercase, camelCase).
pub(crate) fn surface_expr_kind_name(expr: &SurfaceExpr) -> &'static str {
    match expr {
        SurfaceExpr::Ident(..) => "ident",
        SurfaceExpr::SyntheticSorry(..) => "syntheticSorry",
        SurfaceExpr::Universe(..) => "universe",
        SurfaceExpr::App(..) => "app",
        SurfaceExpr::Lambda(..) => "lambda",
        SurfaceExpr::PatternMatchLambda(..) => "patternMatchLambda",
        SurfaceExpr::Pi(..) => "pi",
        SurfaceExpr::Arrow(..) => "arrow",
        SurfaceExpr::Let(..) => "let",
        SurfaceExpr::LetRec(..) => "letRec",
        SurfaceExpr::LetPattern(..) => "letPattern",
        SurfaceExpr::Lit(..) => "lit",
        SurfaceExpr::Paren(..) => "paren",
        SurfaceExpr::Hole(..) => "hole",
        SurfaceExpr::NamedHole(..) => "hole",
        SurfaceExpr::Ascription(..) => "ascription",
        SurfaceExpr::OutParam(..) => "outParam",
        SurfaceExpr::SemiOutParam(..) => "semiOutParam",
        SurfaceExpr::If(..) => "if",
        SurfaceExpr::IfLet(..) => "ifLet",
        SurfaceExpr::IfDecidable(..) => "ifDecidable",
        SurfaceExpr::Match(..) => "match",
        SurfaceExpr::Proj(..) => "proj",
        SurfaceExpr::UniverseInst(..) => "universeInst",
        SurfaceExpr::NamedArg(..) => "namedArg",
        SurfaceExpr::SyntaxQuote(..) => "syntaxQuote",
        SurfaceExpr::QQuotation { .. } => "qQuotation",
        SurfaceExpr::QAntiquot { .. } => "qAntiquot",
        SurfaceExpr::Explicit(..) => "explicit",
        SurfaceExpr::StructLit { .. } => "structLit",
        SurfaceExpr::ByTactic(..) => "byTactic",
        SurfaceExpr::CalcBlock(..) => "calcBlock",
        SurfaceExpr::Do(..) => "do",
        SurfaceExpr::LiftMethod(..) => "liftMethod",
        SurfaceExpr::InterpolatedStr { .. } => "interpolatedStr",
        SurfaceExpr::OpenIn { .. } => "openIn",
    }
}

#[cfg(test)]
mod tests;

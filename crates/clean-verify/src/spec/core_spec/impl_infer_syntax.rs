// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Layer-1 OPERATIONAL SYNTAX for the deployed kernel's release inference body
//! (job C1 / migration step M2 of
//! `designs/2026-07-29-unified-implinfer-relation.md`).
//!
//! This module registers the syntax `ImplInfer` (the next stage) ranges over —
//! and nothing else. It is **purely additive**: `KExpr` is untouched, so none of
//! the 781 in-tree `KExpr.rec` sites move. That is the measured reason the
//! design refuses to add `KExpr.fvar` (116 declaration units carrying a
//! `KExpr.rec` term would need a 10th minor across 38 files).
//!
//! # What is modelled, and against what
//!
//! Layer 1 is the code, warts included. Every declaration below transcribes a
//! concrete production data structure or operation:
//!
//! | spec name | production source |
//! |---|---|
//! | `BinderInfo` / `Multiplicity` / `BinderData` | `clean-kernel/src/expr/types.rs:26,53,121` |
//! | `ImplLit` | `expr::Literal` (`Nat` and `String`; `KExpr.lit` is Nat-only) |
//! | `ImplExpr` | the release `ExprKind` image of `infer_type_fast_inner` |
//! | `LocalDecl` / `LCtx` | `tc/local_context.rs:32-58` (`decls`, `index_by_id`, `next_id`) |
//! | `ImplConstInfo` | the `env.get_const(name)` record the `Const` arm reads |
//! | `impl_instantiate` | `Expr::instantiate` (de Bruijn, shifting) |
//! | `impl_open` | `TypeChecker::open_bvar` (`tc/eta.rs:197` = `instantiate (FVar id)`) |
//! | `impl_abstract_fvar` | `Expr::abstract_fvar` (`expr/subst.rs:1137`) |
//! | `impl_subst_fvar` | `Expr::subst_fvar` (`expr/subst.rs:1162`) — NO binder-depth dependence, verified at source (`FVarSubst`, `:431-435`) |
//! | `impl_inst_levels` | `instantiate_level_params_direct` (`expr/subst.rs:1198`) |
//!
//! `ImplExpr` carries `fvar` because the deployed body does: `Lam`/`Pi`/`Let`
//! mint a fresh `FVarId`, open `BVar(0)` to it, infer, then abstract back
//! (`tc/infer.rs:533-548`). The metatheory (`KExpr`) stays de Bruijn.
//!
//! # Freshness is numeric, not cofinite
//!
//! `LocalContext` carries `next_id: u64` and asserts an id is never reused
//! (`local_context.rs:82-89`). `LCtx` is a snoc-list of `LocalDecl` carrying the
//! `FVarId` explicitly, and `ImplInfer` threads `next_id` as in/out indices — so
//! freshness is decidable arithmetic and the equivariance obligation collapses
//! to ONE renaming lemma instead of recurring at every binder.
//!
//! # Registration order is load-bearing
//!
//! Definitions are registered eagerly, so each name must exist before its first
//! use: types -> projections -> lift -> instantiate -> open -> abstract ->
//! subst_fvar -> the constant-environment layer.
//!
//! ZERO new axioms: every declaration is an `add_inductive` (Inductive /
//! Constructor / Recursor — census-neutral) or a valued `add_recursive_def`.

use crate::spec::error::SpecError;
use crate::Specification;

impl Specification {
    /// M2: the layer-1 operational syntax + its substitution calculus + the
    /// constant-environment record the release `Const` arm reads.
    pub(super) fn add_impl_infer_syntax(&mut self) -> Result<(), SpecError> {
        self.add_impl_syntax_types()?;
        self.add_impl_syntax_subst()?;
        self.add_impl_syntax_const_env()?;
        Ok(())
    }

    /// The inductive types + their projections + local-context lookup.
    fn add_impl_syntax_types(&mut self) -> Result<(), SpecError> {
        // ================================================================
        // Binder annotations — carried through inference, never inspected.
        // ================================================================
        // The release Lam/Pi arms thread `*bi` from the input node into the
        // context entry AND the reconstructed Pi (`tc/infer.rs:533,544-548`).
        // Modelling it as an opaque payload is what makes that threading
        // checkable; erasing it would silently permit a binder-info-losing
        // implementation to satisfy the relation.
        self.add_inductive(
            r"inductive BinderInfo : Type
| default : BinderInfo
| implicit : BinderInfo
| strictImplicit : BinderInfo
| instImplicit : BinderInfo",
            "Binder visibility, transcribing clean-kernel BinderInfo \
             (expr/types.rs:26-36): default | implicit | strictImplicit | instImplicit.",
        )?;

        self.add_inductive(
            r"inductive Multiplicity : Type
| zero : Multiplicity
| one : Multiplicity
| many : Multiplicity",
            "QTT resource multiplicity, transcribing clean-kernel Multiplicity \
             (expr/types.rs:53-62): zero (erased) | one (linear) | many (unrestricted).",
        )?;

        self.add_inductive(
            r"inductive BinderData : Type
| mk : BinderInfo -> Multiplicity -> BinderData",
            "Binder annotation record, transcribing clean-kernel BinderData \
             (expr/types.rs:121-126): { info : BinderInfo, mult : Multiplicity }. \
             Carried by ImplExpr.lam / ImplExpr.pi and by every LocalDecl, exactly \
             as the release Lam arm threads `*bi` into ctx_push and back into the \
             reconstructed Pi (tc/infer.rs:533,544-548).",
        )?;

        // ================================================================
        // Literals — BOTH kernel cases (KExpr.lit is Nat-only).
        // ================================================================
        // `expr::Literal` is Nat | String. The spec's `Name` already encodes
        // strings as interned Nat ids (`Name.str : Name -> Nat -> Name`), so
        // `strVal` carries the same interned id. HONEST RESIDUAL: the string
        // BYTES are not modelled — only the identity of the interned symbol,
        // which is all the Lit arm observes (it returns a fixed constant and
        // performs ZERO environment validation, tc/infer.rs:647-650).
        self.add_inductive(
            r"inductive ImplLit : Type
| natVal : Nat -> ImplLit
| strVal : Nat -> ImplLit",
            "Kernel literal payload (expr::Literal): natVal for Literal::Nat, strVal \
             for Literal::String (carrying the interned symbol id — the spec's Name \
             encodes strings the same way). The reflected KExpr.lit is Nat-ONLY, so \
             this is strictly wider and is one reason the layer-1 syntax is separate.",
        )?;

        // ================================================================
        // ImplExpr — the release ExprKind image, 10 constructors.
        // ================================================================
        // Generated from the arms `infer_type_fast_inner` dispatches on
        // (tc/infer.rs:349-663). It covers exactly the CORE arms: the 13
        // mode-gated extension constructors are absent by construction (they
        // cannot be inferred in the default Constructive mode — proved as a side
        // lemma in `impl_infer_mode_gate`), and `Proj` is EXCLUDED OUTRIGHT
        // (tc/infer.rs:651): its arm calls `is_prop` -> `infer_type_infer_only`,
        // a mode switch INSIDE the arm, plus a `proj_type_cache` keyed on a
        // rebuilt node and a constructor-telescope walk (infer_proj.rs:243-341:
        // cache_projection_field_types_non_prop / walk_prop_telescope_to_idx /
        // cache_projection_field_types_prop).
        //
        // Coverage, not rounded up: 10 of 24 release dispatch arms carry a rule
        // (9 constructors + the `bvar` REFUTATION); 13 more are discharged by the
        // mode-gate side lemma; 1 (`Proj`) is excluded. 23 of 24.
        self.add_inductive(
            r"inductive ImplExpr : Type
| bvar : Nat -> ImplExpr
| fvar : Nat -> ImplExpr
| sort : Level -> ImplExpr
| const : Name -> ListType Level -> ImplExpr
| app : ImplExpr -> ImplExpr -> ImplExpr
| lam : BinderData -> ImplExpr -> ImplExpr -> ImplExpr
| pi : BinderData -> ImplExpr -> ImplExpr -> ImplExpr
| let_ : Name -> ImplExpr -> ImplExpr -> ImplExpr -> ImplExpr
| lit : ImplLit -> ImplExpr
| mdata : ImplExpr -> ImplExpr",
            "Layer-1 operational syntax: the release ExprKind image of \
             infer_type_fast_inner (tc/infer.rs:349-663), 10 constructors. Unlike \
             KExpr it carries `fvar` (the deployed body opens binders to fresh \
             FVarIds), binder data on lam/pi, a name on let_, BOTH literal cases, \
             and mdata. PURELY ADDITIVE: KExpr is untouched, so no existing \
             KExpr.rec proof term moves. ZERO new axioms.",
        )?;

        // ================================================================
        // The local context — LocalContext, literally.
        // ================================================================
        self.add_inductive(
            r"inductive LocalDecl : Type
| mk : Nat -> ImplExpr -> OptionType ImplExpr -> BinderData -> LocalDecl",
            "One local-context entry, transcribing clean-kernel LocalDecl \
             (tc/local_context.rs:32-43): the FVarId, the type, the OPTIONAL value \
             (`some` exactly for let-bindings, `push_let` at :109), and the binder \
             data. The user-facing `name` field is deliberately omitted: no release \
             inference arm reads it.",
        )?;

        self.add_inductive(
            r"inductive LCtx : Type
| nil : LCtx
| snoc : LCtx -> LocalDecl -> LCtx",
            "Local context as a snoc-list of LocalDecl, transcribing \
             LocalContext.decls (a Vec pushed/popped as a stack, \
             tc/local_context.rs:48). Lookup is BY FVarId (production keys an \
             index_by_id map, :50), not by position — see lctx_lookup.",
        )?;

        // local_decl_* : the four field projections.
        self.add_recursive_def(
            r"def local_decl_id (d : LocalDecl) : Nat := match d with
| LocalDecl.mk x ty v bd => x",
            "FVarId of a local declaration (LocalDecl.id).",
        )?;
        self.add_recursive_def(
            r"def local_decl_type (d : LocalDecl) : ImplExpr := match d with
| LocalDecl.mk x ty v bd => ty",
            "Type of a local declaration (LocalDecl.type_).",
        )?;
        self.add_recursive_def(
            r"def local_decl_value (d : LocalDecl) : OptionType ImplExpr := match d with
| LocalDecl.mk x ty v bd => v",
            "Value of a local declaration (LocalDecl.value) — `some` exactly for \
             let-bindings.",
        )?;
        self.add_recursive_def(
            r"def local_decl_bi (d : LocalDecl) : BinderData := match d with
| LocalDecl.mk x ty v bd => bd",
            "Binder data of a local declaration (LocalDecl.bi).",
        )?;

        // lctx_lookup: `LocalContext::get(id)` — by FVarId, most recent first.
        // Production reads a HashMap keyed on FVarId; ids are unique by the
        // never-reuse assertion (:82-89), so the most-recent-first scan of the
        // snoc-list agrees with the map on every reachable context. Returns the
        // stored type UNLIFTED — the release FVar arm does `.map(|d|
        // d.type_.clone())` with no de Bruijn adjustment (tc/infer.rs:351-359).
        self.add_recursive_def(
            r"def lctx_lookup (g : LCtx) : Nat -> OptionType ImplExpr := LCtx.rec (fun (_ : LCtx) => Nat -> OptionType ImplExpr) (fun (_ : Nat) => OptionType.none ImplExpr) (fun (rest : LCtx) (d : LocalDecl) (ih : Nat -> OptionType ImplExpr) => fun (x : Nat) => Bool.rec (fun (_ : Bool) => OptionType ImplExpr) (ih x) (OptionType.some ImplExpr (local_decl_type d)) (nat_eqb (local_decl_id d) x)) g",
            "Local-context lookup BY FVarId (LocalContext::get, tc/local_context.rs). \
             Scans the snoc-list most-recent-first; agrees with production's \
             index_by_id HashMap because push asserts ids are never reused \
             (:82-89). Returns the stored type UNLIFTED — the deployed FVar arm \
             applies no lift, unlike KernelInfers.bvar / TypingCtxConv.var.",
        )?;

        // lctx_fresh: `x >= next_id`. Decidable arithmetic, no cofinite sets.
        self.add_recursive_def(
            r"def lctx_fresh (next_id : Nat) (x : Nat) : Bool := nat_is_zero (Nat.sub next_id x)",
            "Numeric freshness: an FVarId x is fresh for a context whose counter is \
             next_id exactly when x >= next_id (truncated subtraction is zero). \
             Models LocalContext.next_id (tc/local_context.rs:57, incremented at \
             :81/:111 and never rewound), which is what lets ImplInfer thread \
             next_id as in/out indices and AVOID cofinite quantification entirely.",
        )?;

        Ok(())
    }

    /// The de Bruijn substitution calculus over `ImplExpr`, in dependency
    /// order: lift -> instantiate -> open -> abstract -> subst_fvar.
    fn add_impl_syntax_subst(&mut self) -> Result<(), SpecError> {
        // Mirrors the KExpr versions (expr_model.rs) constructor-for-constructor;
        // the extra ImplExpr shapes (fvar, mdata, binder-data-carrying lam/pi,
        // named let_, wider lit) are added and the metatheory copies stay put.
        self.add_recursive_def(
            r"def impl_lift_bvar_at (idx : Nat) (cutoff : Nat) (amount : Nat) : ImplExpr := Nat.rec (fun (_ : Nat) => ImplExpr) (ImplExpr.bvar (Nat.add idx amount)) (fun (k : Nat) (r : ImplExpr) => ImplExpr.bvar idx) (Nat.sub cutoff idx)",
            "Compute a lifted bvar on ImplExpr: at idx >= cutoff add amount, else \
             keep. Mirrors lift_bvar_at on KExpr.",
        )?;
        self.add_recursive_def(
            r"def impl_lift_at (e : ImplExpr) (cutoff : Nat) (amount : Nat) : ImplExpr := match e with
| ImplExpr.bvar i => impl_lift_bvar_at i cutoff amount
| ImplExpr.fvar y => ImplExpr.fvar y
| ImplExpr.sort l => ImplExpr.sort l
| ImplExpr.const nm us => ImplExpr.const nm us
| ImplExpr.app f a => ImplExpr.app (impl_lift_at f cutoff amount) (impl_lift_at a cutoff amount)
| ImplExpr.lam bd ty b => ImplExpr.lam bd (impl_lift_at ty cutoff amount) (impl_lift_at b (Nat.succ cutoff) amount)
| ImplExpr.pi bd ty b => ImplExpr.pi bd (impl_lift_at ty cutoff amount) (impl_lift_at b (Nat.succ cutoff) amount)
| ImplExpr.let_ nm ty v b => ImplExpr.let_ nm (impl_lift_at ty cutoff amount) (impl_lift_at v cutoff amount) (impl_lift_at b (Nat.succ cutoff) amount)
| ImplExpr.lit lt => ImplExpr.lit lt
| ImplExpr.mdata inner => ImplExpr.mdata (impl_lift_at inner cutoff amount)",
            "Lift bound variables >= cutoff by amount on ImplExpr. Mirrors lift_at \
             on KExpr; fvar is a LEAF (free variables are never lifted — that is \
             the point of the locally-nameless crossing the deployed body performs).",
        )?;

        self.add_recursive_def(
            r"def impl_inst_bvar_geq (idx : Nat) (depth : Nat) (val : ImplExpr) : ImplExpr := Nat.rec (fun (_ : Nat) => ImplExpr) (impl_lift_at val Nat.zero depth) (fun (k : Nat) (r : ImplExpr) => ImplExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) (Nat.sub idx depth)",
            "Helper: at idx == depth substitute the lifted value; at idx > depth \
             decrement. Mirrors instantiate_bvar_geq on KExpr.",
        )?;
        self.add_recursive_def(
            r"def impl_inst_bvar_at (idx : Nat) (depth : Nat) (val : ImplExpr) : ImplExpr := Nat.rec (fun (_ : Nat) => ImplExpr) (impl_inst_bvar_geq idx depth val) (fun (k : Nat) (r : ImplExpr) => ImplExpr.bvar idx) (Nat.sub depth idx)",
            "Helper: three-way comparison idx vs depth for bvar substitution. \
             Mirrors instantiate_bvar_at on KExpr.",
        )?;
        self.add_recursive_def(
            r"def impl_instantiate_at (body : ImplExpr) (val : ImplExpr) (depth : Nat) : ImplExpr := match body with
| ImplExpr.bvar i => impl_inst_bvar_at i depth val
| ImplExpr.fvar y => ImplExpr.fvar y
| ImplExpr.sort l => ImplExpr.sort l
| ImplExpr.const nm us => ImplExpr.const nm us
| ImplExpr.app f a => ImplExpr.app (impl_instantiate_at f val depth) (impl_instantiate_at a val depth)
| ImplExpr.lam bd ty b => ImplExpr.lam bd (impl_instantiate_at ty val depth) (impl_instantiate_at b val (Nat.succ depth))
| ImplExpr.pi bd ty b => ImplExpr.pi bd (impl_instantiate_at ty val depth) (impl_instantiate_at b val (Nat.succ depth))
| ImplExpr.let_ nm ty v b => ImplExpr.let_ nm (impl_instantiate_at ty val depth) (impl_instantiate_at v val depth) (impl_instantiate_at b val (Nat.succ depth))
| ImplExpr.lit lt => ImplExpr.lit lt
| ImplExpr.mdata inner => ImplExpr.mdata (impl_instantiate_at inner val depth)",
            "Substitute val for BVar(depth), incrementing depth under each binder. \
             The ImplExpr counterpart of instantiate_at; mdata recurses \
             transparently (the deployed MData arm is a passthrough, \
             tc/infer.rs:658-663).",
        )?;
        self.add_recursive_def(
            r"def impl_instantiate (body : ImplExpr) (val : ImplExpr) : ImplExpr := impl_instantiate_at body val Nat.zero",
            "Expr::instantiate on ImplExpr: substitute val for BVar(0). This is the \
             operation the release App arm applies to the Pi codomain \
             (`result_type.instantiate(a)`, tc/infer.rs:490).",
        )?;

        // impl_open: production's open_bvar is LITERALLY instantiate(FVar id)
        // (tc/eta.rs:197-199) — so it is defined that way here, not re-derived.
        self.add_recursive_def(
            r"def impl_open (body : ImplExpr) (x : Nat) : ImplExpr := impl_instantiate body (ImplExpr.fvar x)",
            "TypeChecker::open_bvar (tc/eta.rs:197-199), which is defined at source \
             as `e.instantiate(&Expr::from_kind(ExprKind::FVar(id)))` — reproduced \
             here as exactly that composition, not as an independent traversal.",
        )?;

        // impl_abstract_at / impl_abstract_fvar: Expr::abstract_fvar.
        // Production SHIFTS existing bvars >= depth up by one — the new binder
        // slots in underneath them (Abstractor::fold_bvar_opt, expr/subst.rs:399-409;
        // ENSURES "All BVar(i) referring to enclosing binders become BVar(i+1)",
        // :1131-1132). A bvar-as-leaf model is unfaithful on open terms.
        self.add_recursive_def(
            r"def impl_abstract_bvar (idx : Nat) (depth : Nat) : ImplExpr := Nat.rec (fun (_ : Nat) => ImplExpr) (ImplExpr.bvar (Nat.succ idx)) (fun (k : Nat) (_ : ImplExpr) => ImplExpr.bvar idx) (Nat.sub depth idx)",
            "Bvar case of impl_abstract_at: idx >= depth (Nat.sub depth idx = 0) \
             shifts up by one for the new binder, idx < depth is kept — \
             Abstractor::fold_bvar_opt (expr/subst.rs:399-409).",
        )?;
        self.add_recursive_def(
            r"def impl_abstract_at (e : ImplExpr) (x : Nat) (depth : Nat) : ImplExpr := match e with
| ImplExpr.bvar i => impl_abstract_bvar i depth
| ImplExpr.fvar y => Bool.rec (fun (_ : Bool) => ImplExpr) (ImplExpr.fvar y) (ImplExpr.bvar depth) (nat_eqb y x)
| ImplExpr.sort l => ImplExpr.sort l
| ImplExpr.const nm us => ImplExpr.const nm us
| ImplExpr.app f a => ImplExpr.app (impl_abstract_at f x depth) (impl_abstract_at a x depth)
| ImplExpr.lam bd ty b => ImplExpr.lam bd (impl_abstract_at ty x depth) (impl_abstract_at b x (Nat.succ depth))
| ImplExpr.pi bd ty b => ImplExpr.pi bd (impl_abstract_at ty x depth) (impl_abstract_at b x (Nat.succ depth))
| ImplExpr.let_ nm ty v b => ImplExpr.let_ nm (impl_abstract_at ty x depth) (impl_abstract_at v x depth) (impl_abstract_at b x (Nat.succ depth))
| ImplExpr.lit lt => ImplExpr.lit lt
| ImplExpr.mdata inner => ImplExpr.mdata (impl_abstract_at inner x depth)",
            "Expr::abstract_fvar_at (expr/subst.rs:1141): replace FVar(x) by \
             BVar(depth) and shift existing BVar(i), i >= depth, up by one \
             (Abstractor::fold_bvar_opt, :399-409), incrementing depth under \
             each binder. The inverse of impl_open, and the operation the \
             release Lam arm applies to the inferred body type before \
             rebuilding the Pi (tc/infer.rs:543).",
        )?;
        self.add_recursive_def(
            r"def impl_abstract_fvar (e : ImplExpr) (x : Nat) : ImplExpr := impl_abstract_at e x Nat.zero",
            "Expr::abstract_fvar (expr/subst.rs:1137-1139): abstract_fvar_at at \
             depth 0.",
        )?;

        // impl_subst_fvar: Expr::subst_fvar — NO binder-depth dependence. The
        // production folder `FVarSubst` states this at source (expr/subst.rs:431-435,
        // "FVarSubst has no binder-depth dependence"), and the contract says
        // "Bound variable structure is preserved (no shifting needed, unlike
        // instantiate)" (:1157). This is the zeta the release Let arm applies.
        self.add_recursive_def(
            r"def impl_subst_fvar (e : ImplExpr) (x : Nat) (v : ImplExpr) : ImplExpr := match e with
| ImplExpr.bvar i => ImplExpr.bvar i
| ImplExpr.fvar y => Bool.rec (fun (_ : Bool) => ImplExpr) (ImplExpr.fvar y) v (nat_eqb y x)
| ImplExpr.sort l => ImplExpr.sort l
| ImplExpr.const nm us => ImplExpr.const nm us
| ImplExpr.app f a => ImplExpr.app (impl_subst_fvar f x v) (impl_subst_fvar a x v)
| ImplExpr.lam bd ty b => ImplExpr.lam bd (impl_subst_fvar ty x v) (impl_subst_fvar b x v)
| ImplExpr.pi bd ty b => ImplExpr.pi bd (impl_subst_fvar ty x v) (impl_subst_fvar b x v)
| ImplExpr.let_ nm ty w b => ImplExpr.let_ nm (impl_subst_fvar ty x v) (impl_subst_fvar w x v) (impl_subst_fvar b x v)
| ImplExpr.lit lt => ImplExpr.lit lt
| ImplExpr.mdata inner => ImplExpr.mdata (impl_subst_fvar inner x v)",
            "Expr::subst_fvar (expr/subst.rs:1162): replace every FVar(x) by v with \
             NO depth tracking and NO shifting — verified at source (the FVarSubst \
             folder is depth-independent, :431-435; the contract states bound \
             structure is preserved, :1157). This is the ZETA the release Let arm \
             applies directly to the inferred body type (tc/infer.rs:645), NOT an \
             abstract+instantiate round trip and NOT `instantiate`.",
        )?;

        Ok(())
    }

    /// The constant-environment record the release `Const` arm reads, and the
    /// five operations it performs on it.
    ///
    /// `KernelInferAccepts.const` models **zero** of these five (its only field
    /// is the guarded conclusion `has_type (const n us) T`, which
    /// `const_untypable` refutes in valid states). That gap is the single
    /// clearest measured reason this relation exists.
    fn add_impl_syntax_const_env(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive ImplConstInfo : Type
| mk : ListType Name -> ImplExpr -> Bool -> Bool -> ImplConstInfo",
            "What the release Const arm reads about a constant \
             (tc/infer.rs:379-418), bundled into one record: the declared \
             level_params and the type (both genuine ConstantInfo fields, \
             env/types.rs:235-256), plus the is_unsafe / is_partial verdicts. \
             NOTE those last two are NOT ConstantInfo fields — they are \
             Environment name-set queries (env/registries.rs:888 and :878). \
             They are bundled here because the arm consults them per-constant at \
             exactly this point, and because the deployed gates are \
             `!allow_unsafe && is_unsafe` / `!allow_partial && is_partial` \
             (tc/infer.rs:401,404) — so an ImplConstInfo with both false pins \
             BOTH the constant's status and the checker's allow_* config.",
        )?;
        self.add_recursive_def(
            r"def impl_const_lps (ci : ImplConstInfo) : ListType Name := match ci with
| ImplConstInfo.mk lps ty u p => lps",
            "ConstantInfo.level_params.",
        )?;
        self.add_recursive_def(
            r"def impl_const_type (ci : ImplConstInfo) : ImplExpr := match ci with
| ImplConstInfo.mk lps ty u p => ty",
            "ConstantInfo.type_.",
        )?;
        self.add_recursive_def(
            r"def impl_const_unsafe (ci : ImplConstInfo) : Bool := match ci with
| ImplConstInfo.mk lps ty u p => u",
            "Environment::is_unsafe for this constant (env/registries.rs:888), as the \
             release arm consults it at tc/infer.rs:401 under !allow_unsafe.",
        )?;
        self.add_recursive_def(
            r"def impl_const_partial (ci : ImplConstInfo) : Bool := match ci with
| ImplConstInfo.mk lps ty u p => p",
            "Environment::is_partial for this constant (env/registries.rs:878), as the \
             release arm consults it at tc/infer.rs:404 under !allow_partial.",
        )?;

        // List lengths, monomorphic (the level-arity check at tc/infer.rs:383).
        self.add_recursive_def(
            r"def name_list_len (xs : ListType Name) : Nat := ListType.rec Name (fun (_ : ListType Name) => Nat) Nat.zero (fun (y : Name) (rest : ListType Name) (ih : Nat) => Nat.succ ih) xs",
            "Length of a Name list — the `info.level_params.len()` side of the \
             release Const arm's arity check (tc/infer.rs:383).",
        )?;
        self.add_recursive_def(
            r"def level_list_len (xs : ListType Level) : Nat := ListType.rec Level (fun (_ : ListType Level) => Nat) Nat.zero (fun (u : Level) (rest : ListType Level) (ih : Nat) => Nat.succ ih) xs",
            "Length of a Level list — the `levels.len()` side of the release Const \
             arm's arity check (tc/infer.rs:383).",
        )?;

        // The declared-level-param discipline: every `Level::Param` mentioned by
        // an admitted declaration must appear in its declared `level_params`.
        //
        // IMPORTANT ATTRIBUTION CORRECTION (measured at HEAD). An earlier version
        // of this comment said `check_level` enforces this "on EVERY path a
        // declaration is admitted through". That is FALSE about `check_level`:
        // `TypeChecker::check_level` short-circuits to `Ok(())` unless
        // `self.level_params` is `Some` (`tc/infer.rs:892-894`), and nothing on
        // the declaration-admission path ever sets it — so the calls the release
        // Sort and Const arms make (`:366-368`, `:396-399`) are no-ops in the
        // modelled configuration.
        //
        // The OBLIGATION nevertheless does hold for every admitted declaration —
        // it is just discharged one level up, by `find_undef_level_param` over
        // both the type and the value in `add_decl` step (4)
        // (`env/decl_add.rs:520-534`), before any type checking runs. So
        // `level_params_ok` is a faithful model of a real admission-path check;
        // it simply models `decl_add`'s check, not `infer`'s. The `sort` and
        // `const` rules carry it as a premise for that reason.
        self.add_recursive_def(
            r"def name_list_mem (xs : ListType Name) (n : Name) : Bool := ListType.rec Name (fun (_ : ListType Name) => Bool) Bool.false (fun (y : Name) (rest : ListType Name) (ih : Bool) => Bool.or (name_eqb y n) ih) xs",
            "Membership of a Name in a Name list (Bool-valued, decidable).",
        )?;
        self.add_recursive_def(
            r"def level_params_ok (lps : ListType Name) (l : Level) : Bool := match l with
| Level.zero => Bool.true
| Level.succ u => level_params_ok lps u
| Level.max u v => Bool.and (level_params_ok lps u) (level_params_ok lps v)
| Level.imax u v => Bool.and (level_params_ok lps u) (level_params_ok lps v)
| Level.param n => name_list_mem lps n",
            "The declared-level-param discipline: every Level::Param occurring in \
             the level must appear in the declaration's declared level_params \
             (Lean 4 parity with type_checker.cpp:63-73). ATTRIBUTION, measured: \
             this models add_decl step (4)'s find_undef_level_param over the type \
             and the value (env/decl_add.rs:520-534), which runs on every \
             admission before any type checking. It does NOT model \
             TypeChecker::check_level, whose calls in the release Sort and Const \
             arms (tc/infer.rs:366-368, :396-399) are NO-OPS in the modelled \
             configuration: check_level returns Ok(()) unless \
             TypeChecker::level_params is Some (tc/infer.rs:892-894), and nothing \
             on the admission path sets it.",
        )?;
        self.add_recursive_def(
            r"def impl_levels_ok (lps : ListType Name) (us : ListType Level) : Bool := ListType.rec Level (fun (_ : ListType Level) => Bool) Bool.true (fun (u : Level) (rest : ListType Level) (ih : Bool) => Bool.and (level_params_ok lps u) ih) us",
            "The declared-level-param discipline applied to every level in a const \
             node's universe-instantiation list. The release Const arm's loop \
             (`for l in levels { self.check_level(l)? }`, tc/infer.rs:397-399) is \
             the shape being modelled; as above, the check that actually bites on \
             the admission path is decl_add's find_undef_level_param, which \
             traverses the whole declaration — const nodes' level lists included.",
        )?;

        // instantiate_level_params_direct: positional name->level substitution.
        // Written with explicit recursors (not nested `match`) because it walks
        // TWO lists in lockstep.
        self.add_recursive_def(
            r"def level_lookup (lps : ListType Name) : ListType Level -> Name -> OptionType Level := ListType.rec Name (fun (_ : ListType Name) => ListType Level -> Name -> OptionType Level) (fun (us : ListType Level) (n : Name) => OptionType.none Level) (fun (p : Name) (rest : ListType Name) (ih : ListType Level -> Name -> OptionType Level) => fun (us : ListType Level) (n : Name) => ListType.rec Level (fun (_ : ListType Level) => OptionType Level) (OptionType.none Level) (fun (u : Level) (urest : ListType Level) (r : OptionType Level) => Bool.rec (fun (_ : Bool) => OptionType Level) (ih urest n) (OptionType.some Level u) (name_eqb p n)) us) lps",
            "Positional level-parameter lookup: walk the declared params and the \
             supplied levels in lockstep (the `zip` in \
             instantiate_level_params_direct, expr/subst.rs:1198). Unequal lengths \
             yield none — matching the source's explicitly panic-free behaviour for \
             any relative lengths; the Const arm has already CHECKED the lengths \
             equal before this runs.",
        )?;
        self.add_recursive_def(
            r"def level_subst (lps : ListType Name) (us : ListType Level) (l : Level) : Level := match l with
| Level.zero => Level.zero
| Level.succ u => Level.succ (level_subst lps us u)
| Level.max u v => Level.max (level_subst lps us u) (level_subst lps us v)
| Level.imax u v => Level.imax (level_subst lps us u) (level_subst lps us v)
| Level.param n => OptionType.rec Level (fun (_ : OptionType Level) => Level) (Level.param n) (fun (u : Level) => u) (level_lookup lps us n)",
            "Level-parameter substitution: replace each Level.param bound by the \
             declaration with the supplied level, leaving unbound params alone \
             (Expr::instantiate_level_params contract, expr/subst.rs:1180-1184).",
        )?;
        self.add_recursive_def(
            r"def impl_inst_levels_list (lps : ListType Name) (us : ListType Level) (vs : ListType Level) : ListType Level := ListType.rec Level (fun (_ : ListType Level) => ListType Level) (ListType.nil Level) (fun (v : Level) (rest : ListType Level) (ih : ListType Level) => ListType.cons Level (level_subst lps us v) ih) vs",
            "Map level_subst over a const node's universe-instantiation list — the \
             ListType Level half of impl_inst_levels.",
        )?;
        self.add_recursive_def(
            r"def impl_inst_levels (lps : ListType Name) (us : ListType Level) (e : ImplExpr) : ImplExpr := match e with
| ImplExpr.bvar i => ImplExpr.bvar i
| ImplExpr.fvar y => ImplExpr.fvar y
| ImplExpr.sort l => ImplExpr.sort (level_subst lps us l)
| ImplExpr.const nm vs => ImplExpr.const nm (impl_inst_levels_list lps us vs)
| ImplExpr.app f a => ImplExpr.app (impl_inst_levels lps us f) (impl_inst_levels lps us a)
| ImplExpr.lam bd ty b => ImplExpr.lam bd (impl_inst_levels lps us ty) (impl_inst_levels lps us b)
| ImplExpr.pi bd ty b => ImplExpr.pi bd (impl_inst_levels lps us ty) (impl_inst_levels lps us b)
| ImplExpr.let_ nm ty v b => ImplExpr.let_ nm (impl_inst_levels lps us ty) (impl_inst_levels lps us v) (impl_inst_levels lps us b)
| ImplExpr.lit lt => ImplExpr.lit lt
| ImplExpr.mdata inner => ImplExpr.mdata (impl_inst_levels lps us inner)",
            "Expr::instantiate_level_params_direct (expr/subst.rs:1198): rewrite \
             every level in the expression under the declaration's \
             level_params -> levels substitution. Expression STRUCTURE is preserved \
             — only levels change (the source contract, :1183). This is the result \
             the release Const arm returns (tc/infer.rs:416-418).",
        )?;

        Ok(())
    }
}

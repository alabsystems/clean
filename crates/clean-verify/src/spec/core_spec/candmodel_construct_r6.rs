// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R6 of the candidate-model construction ladder — the SYNTACTIC rung: a real
//! context-indexed typing judgment `SynTy : ListType KExpr -> KExpr -> KExpr ->
//! Type` whose rules mention NO `candInterp`, the closing-substitution
//! interface `SubstOK`, the Tait fundamental theorem `synTy_fundamental` over
//! it, and the UNCONDITIONAL capstones `synTy_sn_subst` / `synTy_sn` /
//! `synTy_sn_closed`.
//!
//! R5 landed `fragTy_sn : FragTy T e -> whnf_acc e` unconditionally but with
//! two stated limits: `FragTy` is a SEMANTIC-PREMISE judgment (its app/lam
//! rules mention `candInterp`), and `candInterp`'s Pi clause is NON-DEPENDENT.
//! R6 closes the first (A below) and proves the precise obstruction to the
//! second (B below).
//!
//! ## A — the syntactic judgment and its fundamental theorem
//!
//! `SynTy` is the ordinary shape, transcribed against the landed
//! `TypingCtx` (`dependent_sn_richmodel.rs:108`) rather than invented:
//!
//! - `var` by `ctx_lookup G i = some T` — the de Bruijn lookup, no lifting
//!   (see the SIMPLE-TYPE note below for why the `lift_at A 0 (i+1)` of
//!   `TypingCtx.var` is absent and what that costs),
//! - `sort` : `sort n : sort (succ n)`,
//! - `app` : `f : pi A B`, `a : A` give `app f a : B`,
//! - `lam` : `b : B` in `cons A G` gives `lam A b : pi A B`.
//!
//! The fundamental theorem is the `Models`/`fundamental_general` tower of the
//! `CandModel` development (`dependent_sn_richmodel.rs:3283/4052) re-run
//! against R5's `candInterp`: `SubstOK s G` replaces `Models tenv M s G`,
//! `candInterp_var`/`candInterp_sort_mem`/`candInterp_app`/`candInterp_lam`
//! replace the `red_var`/`red_sort`/`pi_elim`/`redAbstraction` LAW
//! PROJECTIONS. The difference is the whole point: there the laws are fields
//! of the hypothesis `M : CandModel tenv`; here every one of them is a landed
//! R5 theorem, so
//!
//! ```text
//! synTy_fundamental : SynTy G e T -> forall s, SubstOK s G -> candInterp T (psubst s e)
//! synTy_sn_subst    : SynTy G e T -> forall s, SubstOK s G -> whnf_acc (psubst s e)
//! synTy_sn          : SynTy G e T -> whnf_acc e
//! synTy_sn_closed   : SynTy nil e T -> whnf_acc e
//! ```
//!
//! carry **NO premise of any kind** — no `CandModel`, no `RecEnvClosed`, no
//! `DefEnvClosed`, no acyclicity. A shape guard pins that (`test_..._shape_
//! guards` (5)), exactly as R5 guarded `fragTy_sn`'s premise-freedom.
//! `synTy_sn` follows from `synTy_sn_subst` at `s := idsubst`, which models
//! EVERY context (`substOK_idsubst`, via `candInterp_var`) — so the capstone
//! is not restricted to closed terms and `synTy_sn_closed` is a one-line
//! corollary rather than the theorem. `synTy_fundamental_typesubst` is the
//! `candInterp (psubst s T) (psubst s e)` spelling, under `SimpleTy T`.
//!
//! ## The two side conditions, and WHY they are in the RULE
//!
//! Two premises of `SynTy` are not in the textbook rule. Both are purely
//! syntactic (`SimpleTy`, `betaStar`, `psubst`, `up`, `SynTy` — no
//! `candInterp`), and both are there so that the FUNDAMENTAL THEOREM AND THE
//! CAPSTONE stay unconditional:
//!
//! 1. **`SimpleTy A` on the lam rule.** `SimpleTy` is the syntactic class of
//!    types built from `sort` and `pi` only. It buys two facts,
//!    `simpleTy_psubst` (`psubst s T = T` for every `s` — simple types are
//!    closed, so substitution is inert) and `simpleTy_whnfAcc` (via the landed
//!    `whnfAcc_sort` / `whnfAcc_pi`). The first is what makes R5's
//!    NON-DEPENDENT Pi clause exactly right rather than approximately right:
//!    on a closed codomain `instantiate B a = B`, so the dependent and
//!    non-dependent readings COINCIDE, and no `psubst_instantiate` reshaping
//!    is needed anywhere in the tower (contrast `fundamental_app`, which needs
//!    one). This is the honest scope of A: it is the SIMPLE-type fragment of
//!    the dependent judgment, and its capstone says nothing about types whose
//!    codomains genuinely depend on the argument.
//!
//! 2. **Development closure on the lam rule.** The recursive premise is
//!    `forall (s : Nat -> KExpr) (b2 : KExpr), betaStar (psubst (up s) b) b2
//!    -> SynTy (cons A G) b2 B` — the body's typing, at EVERY substitution
//!    instance and closed under beta-development. This is the load-bearing
//!    design decision of the rung, and it is a hoisted premise, not a
//!    convenience:
//!
//!    R5's `candInterp_lam` (R1's Tait engine `candExpHF_beta`) demands the
//!    DEVELOPMENT FAMILY `forall b2, betaStar b' b2 -> forall a, candInterp A a
//!    -> candInterp B (instantiate b2 a)` at the SUBSTITUTED body
//!    `b' = psubst (up s) b`. Deriving that family from a single-contractum IH
//!    needs the substitution-step transport `beta_reduces b' b2 ->
//!    beta_reduces (instantiate b' a) (instantiate b2 a)`; the only spec-side
//!    transport is R2's `betaRed_inst_transport`, and it CARRIES
//!    `RecEnvClosed (red_rec the_red_env)` (its iota arm goes through
//!    `iota_subst_commutes`). The same wall stands one step further out: the
//!    obvious alternative — get SN of the body and `SubstOK (cons A G) (up s)`
//!    from a renaming IH — needs `candInterp T e -> candInterp T (lift_at e 0
//!    1)`, whose base case `whnf_acc e -> whnf_acc (lift_at e 0 1)` is a
//!    lift-step transport, blocked by the same iota arm (`RecEnvLiftClosed`).
//!    The discharges of both (`the_red_env_rec_closed_via_checker_b2`,
//!    `the_red_env_rec_lift_closed_via_checker_b2`) live in
//!    `add_the_red_env_faithful_discharge`, which registers AFTER the whole
//!    candmodel ladder — so at this stage position neither is available, and
//!    R5's standing rule (do not import a closedness premise to buy a prettier
//!    engine spelling) forbids carrying them on the capstone. Hoisting the
//!    consequence into the RULE keeps the capstone premise-free and puts the
//!    cost exactly where it is honest: in what `SynTy` derives.
//!
//!    Note what the premise still gives for free: at `b2 := psubst (up s) b`
//!    with `betaStar.refl` it IS the ordinary "body is typed in the extended
//!    context, at every substitution instance", and its IH at
//!    `s2 := idsubst` yields `whnf_acc (psubst (up s) b)` through
//!    `candInterp_cr1` — so the lam arm needs NO separate SN-of-body premise.
//!    `r6_lam_body_acc_necessary` records that the obligation itself is real
//!    (a lam over `r5_omegaV` self-loops, so it is not SN), and
//!    `r6_substBody_beta_inert` + `r6_substBody_image` +
//!    `r6_subst_creates_redex` record why the premise must be stated over
//!    `psubst` instances: `app (bvar 0) (bvar 0)` takes NO beta step at all
//!    (R5's `r5_bvarApp_no_beta`), yet its image under the closing
//!    substitution `scons (lam (sort 0) (bvar 0)) idsubst` IS a beta redex
//!    that fires. A premise quantified over developments of `b` alone would
//!    therefore be strictly weaker and would not feed the engine.
//!
//! ## B — the dependent Pi clause: OBSTRUCTION PROVED, not attempted
//!
//! The dependent clause would be `candInterp (pi A B) := PiSet (candInterp A)
//! (fun a => candInterp (instantiate B a))`. `r6_dependent_pi_self_argument` +
//! `r6_dependent_pi_self_reachable` settle it mechanically at `A := sort 0`,
//! `B := bvar 0`:
//!
//! - `instantiate (bvar 0) a = a` for EVERY `a` (`r6_dependent_pi_arg_
//!   unbounded`) — the recursive call's argument is not a subterm of
//!   `pi A B`, it is an arbitrary `KExpr`;
//! - taking `a := pi (sort 0) (bvar 0)` — the very type being defined — the
//!   clause's recursive call is `candInterp (pi (sort 0) (bvar 0))`, i.e. a
//!   call to the function AT ITS OWN ARGUMENT
//!   (`r6_dependent_pi_self_argument`);
//! - and that `a` is REACHABLE, not hypothetical: `r6_dependent_pi_self_
//!   reachable` states membership AT the recursive-call argument,
//!   `candInterp (sort 0) (instantiate (bvar 0) (pi (sort 0) (bvar 0)))` —
//!   `candInterp (sort 0)` is the top candidate `whnf_acc`, and
//!   `whnf_acc (pi (sort 0) (bvar 0))` holds (`whnfAcc_pi` on `whnfAcc_sort`
//!   and `cand_var_witness`), so `a` genuinely inhabits the domain candidate
//!   that `PiSet` quantifies over.
//!
//! So the dependent clause is not merely non-structural in `KExpr`: it is
//! non-terminating on any recursion whose measure is the TYPE, because the
//! recursive call returns to the same type. No `KExpr.rec`, and no
//! well-founded recursion on any measure of `pi A B`, defines it. The corpus
//! route is the shape/denotation split (`stratified-sn/solution/Stratified/
//! Shapes.lean` — `Sk` / `VD` / `Val`, and `CCUShape.lean`'s `cval`), where
//! the recursion is on the SHAPE `Sk`, which decreases even when the type does
//! not. That is design rungs R4+R5 of
//! `designs/2026-08-23-spec-candmodel-port.md` §5 (60-90 constants, 16-30
//! cycles) and is NOT portable inside this rung; per the ladder's standing
//! rule the obstruction is registered instead of ground against.
//!
//! ## Honesty notes (read before quoting)
//!
//! - **Nothing here discharges `M : CandModel tenv`.** `synTy_sn` is SN for
//!   `SynTy`, NOT for `TypingCtx`, and must never be described as advancing
//!   `whnf_terminates_well_typed_dependent` (design §6.2; the wh3-loop
//!   retraction is the precedent for that overclaim). `SynTy` is strictly
//!   narrower than `TypingCtx`: no `const` rule, no `let_` rule, no `pi`
//!   formation rule, simple types only, and the two lam side conditions above.
//! - **The judgment is not total, and neither is the type class.**
//!   `synTy_not_total` : `r5_omegaLam` — a strongly normalizing term — is NOT
//!   `SynTy`-derivable at `pi (sort 0) (sort 0)` in ANY context, because the
//!   fundamental theorem would place it in the interpretation that R5's
//!   `candInterp_pi_not_total` excludes. `simpleTy_not_total` : `bvar 0` is
//!   not a `SimpleTy`. These are the `micro_has_type` total-predicate trap
//!   guards; no automated gate performs this discrimination (the axiom census
//!   counts axioms, and a judgment is value-full and census-invisible).
//! - **The positive witness goes THROUGH the capstone.** `synTy_sn_witness`
//!   derives `whnf_acc (app (lam (sort 0) (bvar 0)) (bvar 0))` as
//!   `synTy_sn` applied to `synTy_app_witness` — i.e. through `SynTy.lam`,
//!   `SynTy.app`, the fundamental theorem, the Tait engine `candExpHF_beta`
//!   inside `candInterp_lam`, and `candInterp_cr1`. The redex differs from
//!   R1's `candExp_beta_base_witness` term and from R5's `fragTy_sn_witness`
//!   term (the annotation is `sort 0`, not `bvar 0`).
//! - **Recursor conventions are taken from a landed consumer, not guessed.**
//!   `SynTy.app` has TWO recursive premises, so the minor-premise binder order
//!   is convention-dependent; `fundamental_general`
//!   (`dependent_sn_richmodel.rs:4052`) consumes `TypingCtx.rec` — a judgment
//!   of exactly this shape — with ALL FIELDS FIRST, THEN ALL IHs, in
//!   constructor order. R6 follows that and pins it in the shape guard.
//! - **The uniform leading `(G : ListType KExpr)` is safe here for a stated
//!   reason.** `fixedIndicesToParams` promotes a leading index only when it is
//!   the SAME in every constructor conclusion AND in every recursive premise;
//!   `SynTy.lam`'s premise concludes at `ListType.cons KExpr A G`, so the
//!   first index is not fixed and no promotion fires — the same reason
//!   `TypingCtx` keeps its 3-ary index motive. Pinned by the shape guard.
//! - **Prop/Type discipline, and the `AndType` slot trap MEASURED on this
//!   rung.** `Eq` is Prop; `candInterp T`, `SynTy`, `SimpleTy`, `SubstOK` and
//!   `whnf_acc` are Type. Every `(C : Type)` CPS eliminator
//!   (`option_none_ne_some_type`, `r5_bvarApp_no_beta`) is instantiated only
//!   at Type-valued goals; the `SimpleTy` no-confusion discriminator lands in
//!   `Empty` directly (its goal IS `Empty`), so no `Empty.rec` detour is
//!   needed. The new lesson, paid for by one 6-minute cycle: **`AndType
//!   (A : Type) (B : Type) : Type` is `Type 0`-in, and the kernel is
//!   non-cumulative**, so a slot may hold NEITHER a Prop (`Eq KExpr x y` —
//!   *"expected Sort(Succ(Zero)), got universe level conflict: 1 vs 0"*) NOR a
//!   `Type 1` term (anything quantifying over `(C : Type)`, e.g.
//!   `r5_bvarApp_no_beta`'s own type). Both mistakes were made here; the fix
//!   is to specialize the CPS eliminator at `Empty` and to register the
//!   equation as its own constant, and shape guard (8b) now refuses either
//!   shape. Note this is invisible to `cargo check`, to the parser harness AND
//!   to the paren/binder guards — it surfaces only in the heavy elaboration.
//!
//! ## Census
//!
//! ZERO new axioms: every constant is value-bearing (two genuine inductives
//! via `add_inductive`, one plain def via `add_recursive_def`, theorems via
//! `add_definition` with kernel `add_decl` checking). Census-neutral.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// ==== R6 SOURCES BEGIN (pure string builders; every source in this region is ====
// ==== pre-validated through the stable-toolchain clean-parser harness).      ====

/// `bvar 0` — the canonical irreducible neutral.
const V0: &str = "(KExpr.bvar Nat.zero)";
/// `sort 0`, the fragment's base simple type.
const S0: &str = "(KExpr.sort Level.zero)";
/// The non-dependent function type `pi (sort 0) (sort 0)`.
const PI00: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero))";
/// The fragment's identity function, annotated at the base type.
const IDLAM0: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The one-entry context `[sort 0]`.
const CTX1: &str = "(@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))";
/// The witness redex `app (lam (sort 0) (bvar 0)) (bvar 0)`.
const REDEX: &str =
    "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))";
/// R5's self-application body `app (bvar 0) (bvar 0)` — proved beta-inert
/// there by `r5_bvarApp_no_beta`.
const SELF_BODY: &str = "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))";
/// The self-referential Pi `pi (sort 0) (bvar 0)` of the B obstruction.
const SELF_PI: &str = "(KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))";
/// The looping lambda `lam (sort 0) r5_omegaV` of the body-SN necessity guard.
const LOOP_LAM: &str = "(KExpr.lam (KExpr.sort Level.zero) r5_omegaV)";

// ================================================================
// Group A — SimpleTy: the syntactic simple-type class, its psubst-inertness
// and its strong normalization.
// ================================================================

pub(super) const SRC_SIMPLE_TY: &str = "inductive SimpleTy : KExpr -> Type\n| base : forall (n : Level), SimpleTy (KExpr.sort n)\n| arrow : forall (A : KExpr) (B : KExpr), SimpleTy A -> SimpleTy B -> SimpleTy (KExpr.pi A B)";

pub(super) const TY_SIMPLETY_PSUBST: &str =
    "forall (T : KExpr), SimpleTy T -> forall (s : Nat -> KExpr), @Eq KExpr (psubst s T) T";

pub(super) const VAL_SIMPLETY_PSUBST: &str = "fun (T : KExpr) (h : SimpleTy T) => @SimpleTy.rec (fun (qT : KExpr) (_ : SimpleTy qT) => forall (qs : Nat -> KExpr), @Eq KExpr (psubst qs qT) qT) (fun (qn : Level) (qs : Nat -> KExpr) => psubst_sort qs qn) (fun (qA : KExpr) (qB : KExpr) (_qhA : SimpleTy qA) (_qhB : SimpleTy qB) (qihA : forall (qs : Nat -> KExpr), @Eq KExpr (psubst qs qA) qA) (qihB : forall (qs : Nat -> KExpr), @Eq KExpr (psubst qs qB) qB) (qs : Nat -> KExpr) => @Eq.trans KExpr (psubst qs (KExpr.pi qA qB)) (KExpr.pi (psubst qs qA) (psubst (up qs) qB)) (KExpr.pi qA qB) (psubst_pi qs qA qB) (@Eq.trans KExpr (KExpr.pi (psubst qs qA) (psubst (up qs) qB)) (KExpr.pi qA (psubst (up qs) qB)) (KExpr.pi qA qB) (@Eq.cong KExpr KExpr (fun (qw : KExpr) => KExpr.pi qw (psubst (up qs) qB)) (psubst qs qA) qA (qihA qs)) (@Eq.cong KExpr KExpr (fun (qw : KExpr) => KExpr.pi qA qw) (psubst (up qs) qB) qB (qihB (up qs))))) T h";

pub(super) const TY_SIMPLETY_WHNFACC: &str = "forall (T : KExpr), SimpleTy T -> whnf_acc T";

pub(super) const VAL_SIMPLETY_WHNFACC: &str = "fun (T : KExpr) (h : SimpleTy T) => @SimpleTy.rec (fun (qT : KExpr) (_ : SimpleTy qT) => whnf_acc qT) (fun (qn : Level) => whnfAcc_sort qn) (fun (qA : KExpr) (qB : KExpr) (_qhA : SimpleTy qA) (_qhB : SimpleTy qB) (qihA : whnf_acc qA) (qihB : whnf_acc qB) => whnfAcc_pi qA qB qihA qihB) T h";

/// Inline `KExpr.rec` discriminator into `Type`: the `bvar` constructor maps
/// to `Empty`, every other constructor to `Nat` (the R2/R5 `kexpr_discr`
/// idiom, reproduced here rather than imported because R5 keeps it private).
fn kexpr_discr_bvar() -> String {
    "(@KExpr.rec (fun (_ : KExpr) => Type) (fun (_ : Level) => Nat) (fun (_ : Nat) => Empty) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : ListType Level) => Nat) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) (fun (_ : Nat) => Nat))".to_string()
}

pub(super) fn ty_simplety_not_total() -> String {
    format!("SimpleTy {V0} -> Empty")
}

pub(super) fn val_simplety_not_total() -> String {
    let d = kexpr_discr_bvar();
    format!(
        "fun (h : SimpleTy {V0}) => @SimpleTy.rec (fun (qT : KExpr) (_ : SimpleTy qT) => @Eq KExpr qT {V0} -> Empty) (fun (qn : Level) (qeq : @Eq KExpr (KExpr.sort qn) {V0}) => @Eq.substType KExpr {d} (KExpr.sort qn) {V0} qeq Nat.zero) (fun (qA : KExpr) (qB : KExpr) (_qhA : SimpleTy qA) (_qhB : SimpleTy qB) (_qihA : @Eq KExpr qA {V0} -> Empty) (_qihB : @Eq KExpr qB {V0} -> Empty) (qeq : @Eq KExpr (KExpr.pi qA qB) {V0}) => @Eq.substType KExpr {d} (KExpr.pi qA qB) {V0} qeq Nat.zero) {V0} h (@Eq.refl KExpr {V0})"
    )
}

/// The premise-satisfiability witness: `SimpleTy` is INHABITED, at the
/// fragment's own function type and through BOTH constructors. `SimpleTy` is a
/// hypothesis of `SynTy.lam` and of `synTy_fundamental_typesubst`, and a
/// constructor is not evidence that anything can build one — the gate excludes
/// constructors from the supply side for exactly that reason.
pub(super) fn ty_simplety_arrow_witness() -> String {
    format!("SimpleTy {PI00}")
}

pub(super) fn val_simplety_arrow_witness() -> String {
    format!("SimpleTy.arrow {S0} {S0} (SimpleTy.base Level.zero) (SimpleTy.base Level.zero)")
}

// ================================================================
// Group B — closing substitutions: the SubstOK interface and its three
// builders (nil / idsubst / extend).
// ================================================================

pub(super) const SRC_SUBST_OK: &str = "def SubstOK (s : Nat -> KExpr) (G : ListType KExpr) : Type := forall (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> candInterp A (s i)";

pub(super) const TY_SUBSTOK_NIL: &str =
    "forall (s : Nat -> KExpr), SubstOK s (@ListType.nil KExpr)";

pub(super) const VAL_SUBSTOK_NIL: &str = "fun (s : Nat -> KExpr) (i : Nat) (A : KExpr) (hget : @Eq (OptionType KExpr) (ctx_lookup (@ListType.nil KExpr) i) (@OptionType.some KExpr A)) => option_none_ne_some_type KExpr A (candInterp A (s i)) hget";

pub(super) const TY_SUBSTOK_IDSUBST: &str = "forall (G : ListType KExpr), SubstOK idsubst G";

pub(super) const VAL_SUBSTOK_IDSUBST: &str = "fun (G : ListType KExpr) (i : Nat) (A : KExpr) (_hget : @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A)) => candInterp_var A i";

pub(super) const TY_SUBSTOK_EXTEND: &str = "forall (s : Nat -> KExpr) (G : ListType KExpr) (A : KExpr) (a : KExpr), candInterp A a -> SubstOK s G -> SubstOK (scons a s) (@ListType.cons KExpr A G)";

pub(super) const VAL_SUBSTOK_EXTEND: &str = "fun (s : Nat -> KExpr) (G : ListType KExpr) (A : KExpr) (a : KExpr) (ha : candInterp A a) (hs : SubstOK s G) (i : Nat) (A2 : KExpr) (hget : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) i) (@OptionType.some KExpr A2)) => @Nat.rec (fun (qi : Nat) => @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) qi) (@OptionType.some KExpr A2) -> candInterp A2 (scons a s qi)) (fun (qh0 : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) Nat.zero) (@OptionType.some KExpr A2)) => @Eq.substType KExpr (fun (qw : KExpr) => candInterp qw a) A A2 (option_some_inj KExpr A A2 qh0) ha) (fun (qk : Nat) (_qih : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) qk) (@OptionType.some KExpr A2) -> candInterp A2 (scons a s qk)) (qhk : @Eq (OptionType KExpr) (ctx_lookup (@ListType.cons KExpr A G) (Nat.succ qk)) (@OptionType.some KExpr A2)) => hs qk A2 qhk) i hget";

// ================================================================
// Group C — the SYNTACTIC judgment.
// ================================================================

/// The lam rule's development-closure premise, spelled once so the inductive
/// source, the recursor minor and the shape guard cannot drift apart.
const LAM_DEV_PREMISE: &str = "forall (s : Nat -> KExpr) (b2 : KExpr), betaStar (psubst (up s) b) b2 -> SynTy (@ListType.cons KExpr A G) b2 B";

pub(super) fn src_syn_ty() -> String {
    format!(
        "inductive SynTy : ListType KExpr -> KExpr -> KExpr -> Type\n\
         | var : forall (G : ListType KExpr) (i : Nat) (T : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr T) -> SynTy G (KExpr.bvar i) T\n\
         | sort : forall (G : ListType KExpr) (n : Level), SynTy G (KExpr.sort n) (KExpr.sort (Level.succ n))\n\
         | app : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr), SynTy G f (KExpr.pi A B) -> SynTy G a A -> SynTy G (KExpr.app f a) B\n\
         | lam : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (b : KExpr), SimpleTy A -> ({LAM_DEV_PREMISE}) -> SynTy G (KExpr.lam A b) (KExpr.pi A B)"
    )
}

// ================================================================
// Group D — the fundamental theorem and the capstones.
// ================================================================

pub(super) const TY_SYNTY_FUNDAMENTAL: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp T (psubst s e)";

pub(super) fn val_synty_fundamental() -> String {
    let motive = "(fun (qG : ListType KExpr) (qe : KExpr) (qT : KExpr) (_ : SynTy qG qe qT) => forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qT (psubst qs qe))";
    // var: the SubstOK lookup IS the goal (psubst qs (bvar qi) reduces to qs qi).
    let m_var = "(fun (qG : ListType KExpr) (qi : Nat) (qT : KExpr) (qhget : @Eq (OptionType KExpr) (ctx_lookup qG qi) (@OptionType.some KExpr qT)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => qhs qi qT qhget)";
    // sort: red_sort at the interpretation, with the landed SN of sorts.
    let m_sort = "(fun (qG : ListType KExpr) (qn : Level) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => candInterp_sort_mem (Level.succ qn) (KExpr.sort qn) (whnfAcc_sort qn))";
    // app: pi_elim at the interpretation on the two IHs. No psubst_instantiate
    // reshaping is needed, because the codomain is NOT instantiated (the
    // non-dependent clause) — that is what the SimpleTy discipline buys.
    let m_app = "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qf : KExpr) (qa : KExpr) (_qhf : SynTy qG qf (KExpr.pi qA qB)) (_qha : SynTy qG qa qA) (qihf : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp (KExpr.pi qA qB) (psubst qs qf)) (qiha : forall (qs : Nat -> KExpr), SubstOK qs qG -> candInterp qA (psubst qs qa)) (qs : Nat -> KExpr) (qhs : SubstOK qs qG) => candInterp_app qA qB (psubst qs qf) (psubst qs qa) (qihf qs qhs) (qiha qs qhs))";
    // lam: the substantive case.
    let ih_ty = "forall (qs0 : Nat -> KExpr) (qb2 : KExpr), betaStar (psubst (up qs0) qb) qb2 -> forall (qs2 : Nat -> KExpr), SubstOK qs2 (@ListType.cons KExpr qA qG) -> candInterp qB (psubst qs2 qb2)";
    let dev_ty = "forall (qs0 : Nat -> KExpr) (qb2 : KExpr), betaStar (psubst (up qs0) qb) qb2 -> SynTy (@ListType.cons KExpr qA qG) qb2 qB";
    // whnf_acc of the substituted annotation, through SimpleTy.
    let hty = "(@Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) qA (psubst qs qA) (@Eq.symm KExpr (psubst qs qA) qA (simpleTy_psubst qA qhA qs)) (simpleTy_whnfAcc qA qhA))";
    // whnf_acc of the substituted BODY, from the development IH at the
    // reflexive development and the identity substitution — so no separate
    // SN-of-body premise is carried by the rule.
    let hb = "(candInterp_cr1 qB (psubst (up qs) qb) (@Eq.substType KExpr (fun (qw : KExpr) => candInterp qB qw) (psubst idsubst (psubst (up qs) qb)) (psubst (up qs) qb) (psubst_id (psubst (up qs) qb)) (qih qs (psubst (up qs) qb) (betaStar.refl (psubst (up qs) qb)) idsubst (substOK_idsubst (@ListType.cons KExpr qA qG)))))";
    // The Tait engine's development family, from the IH at scons a idsubst,
    // reshaped by instantiate_eq_psubst.
    let hfam = "(fun (qb2 : KExpr) (qstar : betaStar (psubst (up qs) qb) qb2) (qa : KExpr) (qha : candInterp qA qa) => @Eq.substType KExpr (fun (qw : KExpr) => candInterp qB qw) (psubst (scons qa idsubst) qb2) (instantiate qb2 qa) (@Eq.symm KExpr (instantiate qb2 qa) (psubst (scons qa idsubst) qb2) (instantiate_eq_psubst qb2 qa)) (qih qs qb2 qstar (scons qa idsubst) (substOK_extend idsubst qG qA qa qha (substOK_idsubst qG))))";
    let m_lam = format!(
        "(fun (qG : ListType KExpr) (qA : KExpr) (qB : KExpr) (qb : KExpr) (qhA : SimpleTy qA) (_qhdev : {dev_ty}) (qih : {ih_ty}) (qs : Nat -> KExpr) (_qhs : SubstOK qs qG) => candInterp_lam qA qB (psubst qs qA) (psubst (up qs) qb) {hty} {hb} {hfam})"
    );
    format!(
        "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) => @SynTy.rec {motive} {m_var} {m_sort} {m_app} {m_lam} G e T h"
    )
}

pub(super) const TY_SYNTY_SN_SUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> forall (s : Nat -> KExpr), SubstOK s G -> whnf_acc (psubst s e)";

pub(super) const VAL_SYNTY_SN_SUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) (s : Nat -> KExpr) (hs : SubstOK s G) => candInterp_cr1 T (psubst s e) (synTy_fundamental G e T h s hs)";

pub(super) const TY_SYNTY_SN: &str =
    "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> whnf_acc e";

pub(super) const VAL_SYNTY_SN: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) => @Eq.substType KExpr (fun (qw : KExpr) => whnf_acc qw) (psubst idsubst e) e (psubst_id e) (synTy_sn_subst G e T h idsubst (substOK_idsubst G))";

pub(super) const TY_SYNTY_SN_CLOSED: &str =
    "forall (e : KExpr) (T : KExpr), SynTy (@ListType.nil KExpr) e T -> whnf_acc e";

pub(super) const VAL_SYNTY_SN_CLOSED: &str = "fun (e : KExpr) (T : KExpr) (h : SynTy (@ListType.nil KExpr) e T) => synTy_sn (@ListType.nil KExpr) e T h";

pub(super) const TY_SYNTY_FUNDAMENTAL_TYPESUBST: &str = "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), SynTy G e T -> SimpleTy T -> forall (s : Nat -> KExpr), SubstOK s G -> candInterp (psubst s T) (psubst s e)";

pub(super) const VAL_SYNTY_FUNDAMENTAL_TYPESUBST: &str = "fun (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : SynTy G e T) (hT : SimpleTy T) (s : Nat -> KExpr) (hs : SubstOK s G) => @Eq.substType KExpr (fun (qw : KExpr) => candInterp qw (psubst s e)) T (psubst s T) (@Eq.symm KExpr (psubst s T) T (simpleTy_psubst T hT s)) (synTy_fundamental G e T h s hs)";

// ================================================================
// Group E — the discriminating witnesses and the necessity guards.
// ================================================================

pub(super) fn ty_synty_id() -> String {
    format!("forall (G : ListType KExpr), SynTy G {IDLAM0} {PI00}")
}

pub(super) fn val_synty_id() -> String {
    format!(
        "fun (G : ListType KExpr) => SynTy.lam G {S0} {S0} {V0} (SimpleTy.base Level.zero) (fun (qs : Nat -> KExpr) (qb2 : KExpr) (qstar : betaStar (psubst (up qs) {V0}) qb2) => @Eq.substType KExpr (fun (qw : KExpr) => SynTy (@ListType.cons KExpr {S0} G) qw {S0}) {V0} qb2 (@Eq.symm KExpr qb2 {V0} (betaStar_bvar_collapse Nat.zero qb2 qstar)) (SynTy.var (@ListType.cons KExpr {S0} G) Nat.zero {S0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S0}))))"
    )
}

pub(super) fn ty_synty_sort_witness() -> String {
    format!("SynTy (@ListType.nil KExpr) {S0} (KExpr.sort (Level.succ Level.zero))")
}

pub(super) const VAL_SYNTY_SORT_WITNESS: &str = "SynTy.sort (@ListType.nil KExpr) Level.zero";

pub(super) fn ty_synty_app_witness() -> String {
    format!("SynTy {CTX1} {REDEX} {S0}")
}

pub(super) fn val_synty_app_witness() -> String {
    format!(
        "SynTy.app {CTX1} {S0} {S0} {IDLAM0} {V0} (synTy_id {CTX1}) (SynTy.var {CTX1} Nat.zero {S0} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {S0})))"
    )
}

pub(super) fn ty_synty_sn_witness() -> String {
    format!("whnf_acc {REDEX}")
}

pub(super) fn val_synty_sn_witness() -> String {
    format!("synTy_sn {CTX1} {REDEX} {S0} synTy_app_witness")
}

pub(super) fn ty_synty_not_total() -> String {
    format!("forall (G : ListType KExpr), SynTy G r5_omegaLam {PI00} -> Empty")
}

pub(super) fn val_synty_not_total() -> String {
    format!(
        "fun (G : ListType KExpr) (h : SynTy G r5_omegaLam {PI00}) => candInterp_pi_not_total (@Eq.substType KExpr (fun (qw : KExpr) => candInterp {PI00} qw) (psubst idsubst r5_omegaLam) r5_omegaLam (psubst_id r5_omegaLam) (synTy_fundamental G r5_omegaLam {PI00} h idsubst (substOK_idsubst G)))"
    )
}

pub(super) fn ty_r6_lam_body_acc_necessary() -> String {
    format!("AndType (whnf_step {LOOP_LAM} {LOOP_LAM}) (whnf_acc {LOOP_LAM} -> Empty)")
}

pub(super) fn val_r6_lam_body_acc_necessary() -> String {
    let step = format!(
        "(whnf_step.beta {LOOP_LAM} {LOOP_LAM} (beta_reduces.lam_body {S0} r5_omegaV r5_omegaV (beta_reduces.beta {V0} {SELF_BODY} r5_omegaLam)))"
    );
    format!(
        "@AndType.intro (whnf_step {LOOP_LAM} {LOOP_LAM}) (whnf_acc {LOOP_LAM} -> Empty) {step} (selfLoop_not_whnfAcc {LOOP_LAM} {step})"
    )
}

/// The substituted image of `app (bvar 0) (bvar 0)` under
/// `scons (lam (sort 0) (bvar 0)) idsubst`.
const SUBST_IMAGE: &str = "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)))";

/// The beta-inertness face, `Empty`-specialized. R5's `r5_bvarApp_no_beta` is
/// `forall g2 (C : Type), beta_reduces .. g2 -> C`, which lives in `Type 1`
/// (it quantifies over `C : Type`) and therefore cannot sit in an `AndType`
/// slot — `AndType (A : Type) (B : Type)` is `Type 0`-in / `Type`-out. The
/// specialization to `Empty` is `Type`-valued and says the same thing at the
/// only instance this guard needs.
pub(super) fn ty_r6_substbody_beta_inert() -> String {
    format!("forall (g2 : KExpr), beta_reduces {SELF_BODY} g2 -> Empty")
}

pub(super) fn val_r6_substbody_beta_inert() -> String {
    format!("fun (g2 : KExpr) (hb : beta_reduces {SELF_BODY} g2) => r5_bvarApp_no_beta g2 Empty hb")
}

pub(super) fn ty_r6_substbody_image() -> String {
    format!("@Eq KExpr (psubst (scons {IDLAM0} idsubst) {SELF_BODY}) {SUBST_IMAGE}")
}

pub(super) fn val_r6_substbody_image() -> String {
    format!("@Eq.refl KExpr {SUBST_IMAGE}")
}

pub(super) fn ty_r6_subst_creates_redex() -> String {
    let inert = format!("(forall (g2 : KExpr), beta_reduces {SELF_BODY} g2 -> Empty)");
    let fires = format!("(beta_reduces {SUBST_IMAGE} (instantiate {V0} {IDLAM0}))");
    format!("AndType {inert} {fires}")
}

pub(super) fn val_r6_subst_creates_redex() -> String {
    let inert = format!("(forall (g2 : KExpr), beta_reduces {SELF_BODY} g2 -> Empty)");
    let fires = format!("(beta_reduces {SUBST_IMAGE} (instantiate {V0} {IDLAM0}))");
    format!(
        "@AndType.intro {inert} {fires} r6_substBody_beta_inert (beta_reduces.beta {S0} {V0} {IDLAM0})"
    )
}

pub(super) fn ty_r6_dependent_pi_arg_unbounded() -> String {
    format!("forall (a : KExpr), @Eq KExpr (instantiate {V0} a) a")
}

pub(super) const VAL_R6_DEPENDENT_PI_ARG_UNBOUNDED: &str = "cand_inst_bvar0";

pub(super) fn ty_r6_dependent_pi_self_argument() -> String {
    format!("@Eq KExpr (instantiate {V0} {SELF_PI}) {SELF_PI}")
}

pub(super) fn val_r6_dependent_pi_self_argument() -> String {
    format!("cand_inst_bvar0 {SELF_PI}")
}

/// Reachability, stated AT the recursive-call argument itself
/// (`instantiate (bvar 0) (pi (sort 0) (bvar 0))`) rather than as an
/// `AndType` with the equation — the equation is an `Eq`, i.e. Prop, and the
/// kernel is non-cumulative, so it cannot inhabit an `AndType` slot.
pub(super) fn ty_r6_dependent_pi_self_reachable() -> String {
    format!("candInterp {S0} (instantiate {V0} {SELF_PI})")
}

pub(super) fn val_r6_dependent_pi_self_reachable() -> String {
    format!(
        "@Eq.substType KExpr (fun (qw : KExpr) => candInterp {S0} qw) {SELF_PI} (instantiate {V0} {SELF_PI}) (@Eq.symm KExpr (instantiate {V0} {SELF_PI}) {SELF_PI} (cand_inst_bvar0 {SELF_PI})) (candInterp_sort_mem Level.zero {SELF_PI} (whnfAcc_pi {S0} {V0} (whnfAcc_sort Level.zero) cand_var_witness))"
    )
}

// ==== R6 SOURCES END ====

/// Register one value-bearing theorem (R5's helper, verbatim: a free function
/// rather than a closure over `&mut self`, because the stage interleaves
/// `add_definition` with `add_recursive_def` / `add_inductive` calls).
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    /// Register the R6 simple-type class, the syntactic judgment `SynTy`, the
    /// closing-substitution interface `SubstOK`, the fundamental theorem, the
    /// unconditional SN capstones, the discriminating witnesses and the two
    /// registered obstructions.
    ///
    /// MUST be registered AFTER `add_candmodel_construct_r0..r5` (the
    /// candidate interface, `betaStar` + `betaStar_bvar_collapse` +
    /// `cand_inst_bvar0` + `selfLoop_not_whnfAcc`, `r5_bvarApp_no_beta` +
    /// `r5_omegaLam`/`r5_omegaV`, and the whole `candInterp` layer),
    /// `add_dependent_sn_richmodel` (`ctx_lookup`, `psubst`/`up`/`scons`/
    /// `idsubst`, `psubst_sort`/`psubst_pi`/`psubst_id`,
    /// `instantiate_eq_psubst`, `option_some_inj`, `whnfAcc_sort`,
    /// `whnfAcc_pi`), `add_whnf_reduction` (`beta_reduces`, `whnf_step`,
    /// `whnf_acc`), `add_expr_model` (`KExpr`, `Level`, `instantiate`) and
    /// `add_par_reduces_c` (`option_none_ne_some_type`).
    ///
    /// The tower is the `Models` / `fundamental_*` / `fundamental_general`
    /// development of `dependent_sn_richmodel.rs` re-run against R5's
    /// `candInterp` instead of against the `CandModel` hypothesis `M`; see the
    /// module docs for the two hoisted lam side conditions, why they are in
    /// the RULE rather than on the theorem, and the proved obstruction to the
    /// dependent Pi clause.
    pub(super) fn add_candmodel_construct_r6(&mut self) -> Result<(), SpecError> {
        // --- Group A: the simple-type class ---
        self.add_inductive(
            SRC_SIMPLE_TY,
            "SimpleTy T — the SYNTACTIC class of simple types over reflected KExpr: sorts, and \
             pis of simple types. Two constructors, no indices beyond T, and the two conclusions \
             are at DIFFERENT formers (sort n vs pi A B), so the single index is not fixed and \
             fixedIndicesToParams cannot promote it. Its whole job is to make R5's NON-DEPENDENT \
             Pi clause exactly right instead of approximately right: a simple type is closed, so \
             psubst is inert on it (simpleTy_psubst) AND instantiate is inert on it, which is \
             precisely the condition under which candInterp (pi A B) := PiSet (candInterp A) (fun \
             _ => candInterp B) agrees with the dependent reading. Not total: simpleTy_not_total. \
             ZERO new axioms.",
        )?;
        add_thm(
            self,
            "simpleTy_psubst",
            TY_SIMPLETY_PSUBST.to_string(),
            VAL_SIMPLETY_PSUBST.to_string(),
            &[
                "SimpleTy.rec",
                "psubst_sort",
                "psubst_pi",
                "Eq.trans",
                "Eq.cong",
            ],
            "SIMPLE TYPES ARE SUBSTITUTION-INERT: SimpleTy T gives psubst s T = T for EVERY s. Two \
             arms of SimpleTy.rec with the substitution universally quantified INSIDE the motive \
             (the pi arm consumes its codomain IH at `up s`, not at `s`): the sort arm is \
             psubst_sort, the pi arm is psubst_pi followed by two Eq.cong steps along the two \
             IHs. This is the one fact that removes every psubst_instantiate reshaping from the \
             fundamental tower below — contrast fundamental_app, whose dependent codomain needs \
             one. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "simpleTy_whnfAcc",
            TY_SIMPLETY_WHNFACC.to_string(),
            VAL_SIMPLETY_WHNFACC.to_string(),
            &["SimpleTy.rec", "whnfAcc_sort", "whnfAcc_pi"],
            "Every simple type is strongly normalizing for the spec's full env-fixed whnf_step: \
             two arms of SimpleTy.rec discharged by the landed whnfAcc_sort and whnfAcc_pi. This \
             is what supplies candInterp_lam's annotation premise in the lam case, so the lam \
             rule needs no whnf_acc premise on its domain. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "simpleTy_not_total",
            ty_simplety_not_total(),
            val_simplety_not_total(),
            &["SimpleTy.rec", "KExpr.rec", "Eq.substType"],
            "NON-DEGENERACY of the type class: bvar 0 is NOT a SimpleTy. SimpleTy.rec with the \
             no-confusion motive `T = bvar 0 -> Empty`, each arm transporting the R2/R5 \
             kexpr_discr discriminator (bvar to Empty, every other former to Nat) along the false \
             equation — the goal IS Empty, so no Empty.rec detour is needed. Without this the \
             SimpleTy premises of SynTy could be vacuous decoration. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "simpleTy_arrow_witness",
            ty_simplety_arrow_witness(),
            val_simplety_arrow_witness(),
            &["SimpleTy.arrow", "SimpleTy.base"],
            "PREMISE-SATISFIABILITY WITNESS, and the other half of simpleTy_not_total: SimpleTy \
             IS INHABITED, at pi (sort 0) (sort 0) — the fragment's own function type, the one \
             synTy_id concludes at — and through BOTH constructors (arrow over two bases). \
             SimpleTy is assumed as a hypothesis by SynTy.lam and by \
             synTy_fundamental_typesubst, and until this was registered nothing in the spec \
             CONCLUDED it: the premise-satisfiability gate deliberately excludes constructors \
             from the supply side, because a constructor builds P only if something can supply \
             its fields, and a type class nothing inhabits makes every rule that demands it \
             unusable while leaving the axiom census, the domain-axiom count and the \
             DerivedProved debt all green. Zero axiom_deps.",
        )?;

        // --- Group B: closing substitutions ---
        self.add_recursive_def(
            SRC_SUBST_OK,
            "SubstOK s G — s is a CLOSING SUBSTITUTION for the context G: every context entry \
             i : A is mapped to a term inhabiting that type's interpretation. The R5-interpretation \
             analogue of the CandModel-parameterised Models tenv M s G \
             (dependent_sn_richmodel.rs:3283), with two simplifications the simple-type discipline \
             licenses: no lift_at bookkeeping on the looked-up type (a simple type is closed, so \
             lift_at A 0 (i+1) = A) and no psubst on it either. Type-valued plain def.",
        )?;
        add_thm(
            self,
            "substOK_nil",
            TY_SUBSTOK_NIL.to_string(),
            VAL_SUBSTOK_NIL.to_string(),
            &["SubstOK", "ctx_lookup", "option_none_ne_some_type"],
            "Every substitution closes the EMPTY context, vacuously: ctx_lookup nil i REDUCES to \
             none, so the lookup hypothesis is none = some A and option_none_ne_some_type \
             eliminates it into the Type-valued goal candInterp A (s i). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "substOK_idsubst",
            TY_SUBSTOK_IDSUBST.to_string(),
            VAL_SUBSTOK_IDSUBST.to_string(),
            &["SubstOK", "candInterp_var", "idsubst"],
            "THE IDENTITY SUBSTITUTION CLOSES EVERY CONTEXT (corpus/guide models_idsubst): \
             idsubst i reduces to bvar i, and every variable inhabits every type's interpretation \
             by R5's candInterp_var, so the context's contents are irrelevant. This is why the \
             capstone synTy_sn holds at an ARBITRARY context and synTy_sn_closed is a corollary \
             rather than the theorem — and it is also what discharges the body's SN inside the \
             fundamental theorem's lam arm. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "substOK_extend",
            TY_SUBSTOK_EXTEND.to_string(),
            VAL_SUBSTOK_EXTEND.to_string(),
            &[
                "SubstOK",
                "Nat.rec",
                "ctx_lookup",
                "scons",
                "option_some_inj",
                "Eq.substType",
            ],
            "Extending a closing substitution by a member of the new type closes the extended \
             context (guide models_extend, without its lift_at/psubst_cancel bookkeeping — simple \
             types make both inert). Nat.rec on the looked-up index: at zero, ctx_lookup (cons A \
             G) 0 reduces to some A and scons a s 0 to a, so option_some_inj transports the given \
             membership along A = A2; at succ k both sides reduce to the tail (ctx_lookup G k, s \
             k) and the tail hypothesis applies unchanged. Zero axiom_deps.",
        )?;

        // --- Group C: the syntactic judgment ---
        self.add_inductive(
            &src_syn_ty(),
            "SynTy G e T — THE SYNTACTIC TYPING JUDGMENT of the R6 fragment: e has type T in \
             context G. Four rules in the ORDINARY shapes, transcribed against the landed \
             TypingCtx (dependent_sn_richmodel.rs:108) — var by ctx_lookup, sort at the successor \
             universe, app by pi-elimination, lam by pi-introduction in the extended context — and \
             CRUCIALLY mentioning NO candInterp anywhere, which is exactly what R5's FragTy could \
             not claim. Two premises are not in the textbook rule, both purely syntactic and both \
             on the lam rule: (1) SimpleTy A, which makes the non-dependent interpretation of the \
             conclusion type exact; (2) the DEVELOPMENT-CLOSURE premise `forall s b2, betaStar \
             (psubst (up s) b) b2 -> SynTy (cons A G) b2 B`, i.e. the body is typed at every \
             substitution instance AND at every beta-development of it. Premise (2) is the \
             hoisted form of the two facts the Tait engine needs and that are BLOCKED at this \
             stage position — substitution transport for beta_reduces (R2's \
             betaRed_inst_transport carries RecEnvClosed (red_rec the_red_env)) and lift transport \
             for whnf_acc (RecEnvLiftClosed) — whose checker discharges register only in \
             add_the_red_env_faithful_discharge, after the whole candmodel ladder. Hoisting it \
             into the RULE is what keeps synTy_fundamental and the capstones premise-FREE. \
             Strict positivity: the recursive occurrence is the CONCLUSION of premise (2), and \
             premise (2) is the LAST field of its constructor. No fixedIndicesToParams promotion: \
             the leading (G : ListType KExpr) is uniform across the four conclusions but premise \
             (2) concludes at ListType.cons KExpr A G, so the first index is not fixed — the same \
             reason TypingCtx keeps its 3-ary index motive. SCOPE: strictly narrower than \
             TypingCtx (no const, no let_, no pi formation, simple types only, plus the two lam \
             side conditions); nothing about it advances M : CandModel tenv. Not total: \
             synTy_not_total. ZERO new axioms.",
        )?;

        // --- Group D: the fundamental theorem and the capstones ---
        add_thm(
            self,
            "synTy_fundamental",
            TY_SYNTY_FUNDAMENTAL.to_string(),
            val_synty_fundamental(),
            &[
                "SynTy.rec",
                "SubstOK",
                "candInterp_sort_mem",
                "candInterp_app",
                "candInterp_lam",
                "candInterp_cr1",
                "simpleTy_psubst",
                "simpleTy_whnfAcc",
                "substOK_idsubst",
                "substOK_extend",
                "instantiate_eq_psubst",
                "psubst_id",
                "betaStar.refl",
                "whnfAcc_sort",
                "Eq.substType",
            ],
            "THE FUNDAMENTAL THEOREM over closing substitutions: every SynTy-derivable term \
             inhabits its type's interpretation at every closing substitution. One SynTy.rec with \
             a full four-binder motive; this is fundamental_general \
             (dependent_sn_richmodel.rs:4052) re-run with candInterp in place of cm_Red tenv M and \
             R5's landed THEOREMS in place of the CandModel LAW PROJECTIONS — which is the entire \
             point: there the laws are fields of the hypothesis M, here every one of them is \
             proved. Arms: var is the SubstOK lookup itself (psubst s (bvar i) reduces to s i); \
             sort is candInterp_sort_mem on whnfAcc_sort; app is candInterp_app on the two IHs \
             with NO psubst_instantiate reshaping (the codomain is not instantiated — the \
             non-dependent clause, made exact by SimpleTy); lam is candInterp_lam, whose \
             annotation premise comes from simpleTy_whnfAcc transported along simpleTy_psubst, \
             whose BODY-SN premise comes from the development IH at the reflexive development and \
             idsubst (so the rule carries no whnf_acc premise), and whose development FAMILY comes \
             from the development IH at scons a idsubst reshaped by instantiate_eq_psubst. Carries \
             NO premise: no CandModel, no RecEnvClosed, no DefEnvClosed. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sn_subst",
            TY_SYNTY_SN_SUBST.to_string(),
            VAL_SYNTY_SN_SUBST.to_string(),
            &["synTy_fundamental", "candInterp_cr1"],
            "SN OF EVERY CLOSING INSTANCE: SynTy G e T implies whnf_acc (psubst s e) for every s \
             that closes G — the fundamental theorem composed with R5's cr1 projection. This is \
             the content R5's fragTy_sn had no analogue for: it says nothing about substitution. \
             UNCONDITIONAL. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sn",
            TY_SYNTY_SN.to_string(),
            VAL_SYNTY_SN.to_string(),
            &["synTy_sn_subst", "substOK_idsubst", "psubst_id"],
            "THE R6 CAPSTONE — UNCONDITIONAL strong normalization for the syntactic judgment: \
             SynTy G e T implies whnf_acc e, at an ARBITRARY context, for the spec's FULL \
             env-fixed one-step reduction (beta, zeta, iota at red_rec the_red_env with full \
             congruence, and delta at red_def the_red_env). Instantiate synTy_sn_subst at \
             idsubst — which closes every context by substOK_idsubst — and cancel the substitution \
             with psubst_id. NO carried premise of any kind: no CandModel, no RecEnvClosed, no \
             DefEnvClosed, no acyclicity (pinned by the premise-freedom shape guard). HONESTY: \
             this is SN for SynTy, NOT for TypingCtx — it neither discharges nor advances the M : \
             CandModel tenv hypothesis of whnf_terminates_well_typed_dependent, and must never be \
             described as doing so (design §6.2). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sn_closed",
            TY_SYNTY_SN_CLOSED.to_string(),
            VAL_SYNTY_SN_CLOSED.to_string(),
            &["synTy_sn"],
            "The closed-term corollary: SynTy nil e T implies whnf_acc e. A one-line \
             specialization of synTy_sn, which already holds at every context — recorded \
             separately because the closed case is the one the ladder's statement of work names. \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_fundamental_typesubst",
            TY_SYNTY_FUNDAMENTAL_TYPESUBST.to_string(),
            VAL_SYNTY_FUNDAMENTAL_TYPESUBST.to_string(),
            &["synTy_fundamental", "simpleTy_psubst", "Eq.substType"],
            "The fundamental theorem in the SUBSTITUTED-TYPE spelling candInterp (psubst s T) \
             (psubst s e), obtained from synTy_fundamental by transporting along simpleTy_psubst \
             under a SimpleTy T premise. Registered because that is the shape the guide's tower \
             uses (fundamental_general concludes at cm_Red (psubst s T) (psubst s e)); the \
             unsubstituted form is the primitive one here precisely because simple types are \
             substitution-inert. Zero axiom_deps.",
        )?;

        // --- Group E: witnesses and necessity guards ---
        add_thm(
            self,
            "synTy_id",
            ty_synty_id(),
            val_synty_id(),
            &[
                "SynTy.lam",
                "SynTy.var",
                "SimpleTy.base",
                "betaStar_bvar_collapse",
                "Eq.substType",
            ],
            "The fragment's identity function is SYNTACTICALLY typed, in every context: lam (sort \
             0) (bvar 0) : pi (sort 0) (sort 0). The lam rule's development-closure premise is \
             discharged for EVERY substitution s because psubst (up s) (bvar 0) REDUCES to bvar 0 \
             (up is scons (bvar 0) …), after which R1's betaStar_bvar_collapse collapses every \
             development back to bvar 0 and the var rule applies with ctx_lookup (cons (sort 0) G) \
             0 = some (sort 0) by Eq.refl. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sort_witness",
            ty_synty_sort_witness(),
            VAL_SYNTY_SORT_WITNESS.to_string(),
            &["SynTy.sort"],
            "sort 0 : sort 1 in the empty context — the judgment's non-vacuity at its simplest \
             rule, a pure constructor application with no computation. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_app_witness",
            ty_synty_app_witness(),
            val_synty_app_witness(),
            &["SynTy.app", "SynTy.var", "synTy_id"],
            "A genuine BETA REDEX inside the syntactic judgment: app (lam (sort 0) (bvar 0)) (bvar \
             0) : sort 0 in the one-entry context [sort 0], by the pi-elim rule at the identity \
             function and the context variable. Distinct from R1's candExp_beta_base_witness term \
             and from R5's fragTy_sn_witness term (the annotation here is sort 0, not bvar 0). \
             Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_sn_witness",
            ty_synty_sn_witness(),
            val_synty_sn_witness(),
            &["synTy_sn", "synTy_app_witness"],
            "THE POSITIVE WITNESS, obtained THROUGH the capstone: whnf_acc of a beta redex, \
             derived as synTy_sn applied to synTy_app_witness — i.e. through SynTy.lam, SynTy.app, \
             the fundamental theorem, the Tait engine candExpHF_beta inside candInterp_lam, and \
             the cr1 projection. Not by a direct whnf_acc.intro. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "synTy_not_total",
            ty_synty_not_total(),
            val_synty_not_total(),
            &[
                "synTy_fundamental",
                "substOK_idsubst",
                "psubst_id",
                "candInterp_pi_not_total",
            ],
            "THE NON-DEGENERACY GUARD (design §6.1; the micro_has_type total-predicate trap): \
             r5_omegaLam — a STRONGLY NORMALIZING term — is NOT SynTy-derivable at pi (sort 0) \
             (sort 0), in ANY context. The fundamental theorem at idsubst would place it in \
             candInterp (pi (sort 0) (sort 0)), which R5's candInterp_pi_not_total refutes. So the \
             judgment is not the total relation and, since the excluded term IS whnf_acc, not a \
             disguised restatement of strong normalization either. No automated gate performs this \
             discrimination: the axiom census counts axioms and a judgment is value-full. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_lam_body_acc_necessary",
            ty_r6_lam_body_acc_necessary(),
            val_r6_lam_body_acc_necessary(),
            &[
                "whnf_step.beta",
                "beta_reduces.lam_body",
                "beta_reduces.beta",
                "selfLoop_not_whnfAcc",
            ],
            "NECESSITY of the body's strong-normalization OBLIGATION: lam (sort 0) r5_omegaV \
             whnf-steps to ITSELF (the lam_body congruence carries R5's omega loop under the \
             binder) and is therefore not whnf_acc, by R1's generic one-step self-loop refutation. \
             So no rule concluding whnf_acc (lam ty b) can leave b unconstrained — which is why \
             the fundamental theorem's lam arm must produce whnf_acc (psubst (up s) b) before it \
             may call the Tait engine. R6 produces it from the development IH rather than carrying \
             it as a premise; this guard records that the obligation is real, not decorative. Zero \
             axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_substBody_beta_inert",
            ty_r6_substbody_beta_inert(),
            val_r6_substbody_beta_inert(),
            &["r5_bvarApp_no_beta", "Empty"],
            "app (bvar 0) (bvar 0) takes NO beta_reduces step at all, at the Empty instance: R5's \
             r5_bvarApp_no_beta specialized at C := Empty. The specialization is not cosmetic — \
             r5_bvarApp_no_beta quantifies over (C : Type) and therefore lives in Type 1, so it \
             cannot inhabit an AndType slot (AndType's two arguments are Type). Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_substBody_image",
            ty_r6_substbody_image(),
            val_r6_substbody_image(),
            &["psubst", "scons", "idsubst", "Eq.refl"],
            "The image of the body app (bvar 0) (bvar 0) under the closing substitution scons (lam \
             (sort 0) (bvar 0)) idsubst IS the self-application of the identity function, by \
             Eq.refl — psubst/scons computation only, with no lift_at anywhere. Prop-valued (it is \
             an Eq), which is why it is registered on its own rather than as a conjunct: the \
             kernel is non-cumulative and AndType's slots are Type. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_subst_creates_redex",
            ty_r6_subst_creates_redex(),
            val_r6_subst_creates_redex(),
            &[
                "r6_substBody_beta_inert",
                "beta_reduces.beta",
                "AndType.intro",
            ],
            "NECESSITY of stating the lam rule's development-closure premise over psubst \
             INSTANCES of the body rather than over developments of the body itself. Read with \
             r6_substBody_image, three facts about b = app (bvar 0) (bvar 0): (1) it takes NO \
             beta_reduces step at all (r6_substBody_beta_inert, R5's r5_bvarApp_no_beta consumed, \
             not restated); (2) its image under the closing substitution scons (lam (sort 0) (bvar \
             0)) idsubst IS app (lam (sort 0) (bvar 0)) (lam (sort 0) (bvar 0)) — that is \
             r6_substBody_image, by Eq.refl; (3) that image beta-FIRES, which is the conjunct \
             paired here. So a premise quantified over developments of b alone would be satisfied \
             VACUOUSLY while the engine's obligation at the substituted body is non-trivial: the \
             weaker spelling is strictly insufficient. (Stated at psubst rather than psubst (up s) \
             so the witness needs no lift_at computation; the phenomenon is the same one de Bruijn \
             level out.) Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_dependent_pi_arg_unbounded",
            ty_r6_dependent_pi_arg_unbounded(),
            VAL_R6_DEPENDENT_PI_ARG_UNBOUNDED.to_string(),
            &["cand_inst_bvar0", "instantiate"],
            "First half of the DEPENDENT-Pi OBSTRUCTION: at codomain B := bvar 0, the dependent \
             clause's recursive argument instantiate B a is literally a — an ARBITRARY KExpr, \
             universally quantified, and in particular not a subterm of pi A B. R1's \
             cand_inst_bvar0 at full generality, registered under a name that says what it \
             obstructs. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_dependent_pi_self_argument",
            ty_r6_dependent_pi_self_argument(),
            val_r6_dependent_pi_self_argument(),
            &["cand_inst_bvar0", "instantiate"],
            "THE SELF-REFERENTIAL INSTANCE of the dependent-Pi clause: at T := pi (sort 0) (bvar \
             0) and a := T, the clause's recursive argument instantiate (bvar 0) T is T ITSELF. \
             Prop-valued (an Eq), registered on its own for that reason; read together with \
             r6_dependent_pi_self_reachable, which supplies the other half. Zero axiom_deps.",
        )?;
        add_thm(
            self,
            "r6_dependent_pi_self_reachable",
            ty_r6_dependent_pi_self_reachable(),
            val_r6_dependent_pi_self_reachable(),
            &[
                "cand_inst_bvar0",
                "candInterp_sort_mem",
                "whnfAcc_pi",
                "whnfAcc_sort",
                "cand_var_witness",
                "Eq.substType",
            ],
            "THE DEPENDENT-Pi OBSTRUCTION, PROVED (design §5 rungs R4/R5; corpus Shapes.lean). \
             Take T := pi (sort 0) (bvar 0). The dependent clause candInterp (pi A B) := PiSet \
             (candInterp A) (fun a => candInterp (instantiate B a)) would, at a := T itself, make a \
             recursive call to candInterp (instantiate (bvar 0) T) = candInterp T — the very type \
             being defined (r6_dependent_pi_self_argument). What THIS constant adds is that the \
             call is REACHABLE, not hypothetical: it states membership AT THE RECURSIVE-CALL \
             ARGUMENT, candInterp (sort 0) (instantiate (bvar 0) T), transporting along that \
             equation the fact that T inhabits the domain candidate — candInterp (sort 0) is the \
             top candidate whnf_acc, and whnf_acc (pi (sort 0) (bvar 0)) holds by whnfAcc_pi on \
             whnfAcc_sort and cand_var_witness. So `a` genuinely ranges over a set containing T, \
             and the clause is not merely non-structural in KExpr: it is NON-TERMINATING on any \
             recursion whose measure is the type. Breaking the cycle needs the corpus's \
             shape/denotation split (Sk / VD / Val / cval), where the recursion is on the SHAPE, \
             which decreases when the type does not — design rungs R4+R5, not portable inside this \
             rung. Zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::parse_check;

    /// Every (name, type, value) triple registered via `add_definition`, in
    /// registration order.
    fn theorem_sources() -> Vec<(String, String, String)> {
        vec![
            (
                "simpleTy_psubst".to_string(),
                TY_SIMPLETY_PSUBST.to_string(),
                VAL_SIMPLETY_PSUBST.to_string(),
            ),
            (
                "simpleTy_whnfAcc".to_string(),
                TY_SIMPLETY_WHNFACC.to_string(),
                VAL_SIMPLETY_WHNFACC.to_string(),
            ),
            (
                "simpleTy_not_total".to_string(),
                ty_simplety_not_total(),
                val_simplety_not_total(),
            ),
            (
                "simpleTy_arrow_witness".to_string(),
                ty_simplety_arrow_witness(),
                val_simplety_arrow_witness(),
            ),
            (
                "substOK_nil".to_string(),
                TY_SUBSTOK_NIL.to_string(),
                VAL_SUBSTOK_NIL.to_string(),
            ),
            (
                "substOK_idsubst".to_string(),
                TY_SUBSTOK_IDSUBST.to_string(),
                VAL_SUBSTOK_IDSUBST.to_string(),
            ),
            (
                "substOK_extend".to_string(),
                TY_SUBSTOK_EXTEND.to_string(),
                VAL_SUBSTOK_EXTEND.to_string(),
            ),
            (
                "synTy_fundamental".to_string(),
                TY_SYNTY_FUNDAMENTAL.to_string(),
                val_synty_fundamental(),
            ),
            (
                "synTy_sn_subst".to_string(),
                TY_SYNTY_SN_SUBST.to_string(),
                VAL_SYNTY_SN_SUBST.to_string(),
            ),
            (
                "synTy_sn".to_string(),
                TY_SYNTY_SN.to_string(),
                VAL_SYNTY_SN.to_string(),
            ),
            (
                "synTy_sn_closed".to_string(),
                TY_SYNTY_SN_CLOSED.to_string(),
                VAL_SYNTY_SN_CLOSED.to_string(),
            ),
            (
                "synTy_fundamental_typesubst".to_string(),
                TY_SYNTY_FUNDAMENTAL_TYPESUBST.to_string(),
                VAL_SYNTY_FUNDAMENTAL_TYPESUBST.to_string(),
            ),
            ("synTy_id".to_string(), ty_synty_id(), val_synty_id()),
            (
                "synTy_sort_witness".to_string(),
                ty_synty_sort_witness(),
                VAL_SYNTY_SORT_WITNESS.to_string(),
            ),
            (
                "synTy_app_witness".to_string(),
                ty_synty_app_witness(),
                val_synty_app_witness(),
            ),
            (
                "synTy_sn_witness".to_string(),
                ty_synty_sn_witness(),
                val_synty_sn_witness(),
            ),
            (
                "synTy_not_total".to_string(),
                ty_synty_not_total(),
                val_synty_not_total(),
            ),
            (
                "r6_lam_body_acc_necessary".to_string(),
                ty_r6_lam_body_acc_necessary(),
                val_r6_lam_body_acc_necessary(),
            ),
            (
                "r6_substBody_beta_inert".to_string(),
                ty_r6_substbody_beta_inert(),
                val_r6_substbody_beta_inert(),
            ),
            (
                "r6_substBody_image".to_string(),
                ty_r6_substbody_image(),
                val_r6_substbody_image(),
            ),
            (
                "r6_subst_creates_redex".to_string(),
                ty_r6_subst_creates_redex(),
                val_r6_subst_creates_redex(),
            ),
            (
                "r6_dependent_pi_arg_unbounded".to_string(),
                ty_r6_dependent_pi_arg_unbounded(),
                VAL_R6_DEPENDENT_PI_ARG_UNBOUNDED.to_string(),
            ),
            (
                "r6_dependent_pi_self_argument".to_string(),
                ty_r6_dependent_pi_self_argument(),
                val_r6_dependent_pi_self_argument(),
            ),
            (
                "r6_dependent_pi_self_reachable".to_string(),
                ty_r6_dependent_pi_self_reachable(),
                val_r6_dependent_pi_self_reachable(),
            ),
        ]
    }

    /// The two inductives and the one plain def, as full declaration sources.
    fn decl_sources() -> Vec<(String, String)> {
        vec![
            ("SimpleTy".to_string(), SRC_SIMPLE_TY.to_string()),
            ("SubstOK".to_string(), SRC_SUBST_OK.to_string()),
            ("SynTy".to_string(), src_syn_ty()),
        ]
    }

    /// Parse-check every generated source — the fast guard for the commonest
    /// failure class (assembly mistakes invisible to `cargo check`).
    #[test]
    fn test_candmodel_r6_sources_parse() {
        for (name, ty, val) in theorem_sources() {
            let assembled = format!("def {name} : {ty} := {val}");
            parse_check(&assembled)
                .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
        }
        for (name, src) in decl_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
        }
    }

    /// PER-STRING paren balance on every source.
    #[test]
    fn test_candmodel_r6_sources_paren_balanced() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (n, src) in decl_sources() {
            all.push((format!("{n}::decl"), src));
        }
        for (name, src) in &all {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in {name}: {src}");
            }
            assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
        }
    }

    /// Skip a run of parenthesised binder groups starting at `i`, returning
    /// (index after the groups, how many groups were skipped).
    fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
        let mut n = 0usize;
        loop {
            while i < b.len() && b[i] == ' ' {
                i += 1;
            }
            if i >= b.len() || b[i] != '(' {
                break;
            }
            let mut d = 0i64;
            while i < b.len() {
                if b[i] == '(' {
                    d += 1;
                } else if b[i] == ')' {
                    d -= 1;
                    if d == 0 {
                        i += 1;
                        break;
                    }
                }
                i += 1;
            }
            n += 1;
        }
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        (i, n)
    }

    /// STRUCTURAL GUARD: a `forall` binder run must be terminated by a COMMA
    /// and a `fun` binder run by `=>`.
    #[test]
    fn test_candmodel_r6_binder_runs_terminated() {
        let mut all: Vec<(String, String)> = Vec::new();
        for (n, ty, val) in theorem_sources() {
            all.push((format!("{n}::ty"), ty));
            all.push((format!("{n}::val"), val));
        }
        for (name, src) in &all {
            let b: Vec<char> = src.chars().collect();
            for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
                let mut from = 0usize;
                while let Some(rel) = src[from..].find(kw) {
                    let start = from + rel;
                    from = start + 1;
                    let ci = src[..start].chars().count() + kw.chars().count();
                    let (after, groups) = skip_binder_groups(&b, ci);
                    assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                    let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                    assert!(
                        tail.starts_with(close),
                        "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                         `{tail}`"
                    );
                }
            }
        }
    }

    /// Shape guards.
    #[test]
    fn test_candmodel_r6_shape_guards() {
        let synty = src_syn_ty();

        // (1) THE HEADLINE PROPERTY: the judgment is SYNTACTIC — no rule may
        // mention the interpretation, the model, or any closedness premise.
        // This is exactly what R5's FragTy could not claim.
        for forbidden in [
            "candInterp",
            "CandModel",
            "cm_Red",
            "RecEnvClosed",
            "DefEnvClosed",
            "IsCandHF",
            "IsCandSet",
            "PiSet",
        ] {
            assert!(
                !synty.contains(forbidden),
                "SynTy must not mention {forbidden} — the whole point of R6 is a SYNTACTIC \
                 judgment"
            );
        }

        // (2) The four rules are the ordinary shapes, var going through
        // ctx_lookup.
        for needle in [
            "| var : forall (G : ListType KExpr) (i : Nat) (T : KExpr), @Eq (OptionType KExpr) \
             (ctx_lookup G i) (@OptionType.some KExpr T) -> SynTy G (KExpr.bvar i) T",
            "| sort : forall (G : ListType KExpr) (n : Level), SynTy G (KExpr.sort n) \
             (KExpr.sort (Level.succ n))",
            "SynTy G f (KExpr.pi A B) -> SynTy G a A -> SynTy G (KExpr.app f a) B",
            "SynTy G (KExpr.lam A b) (KExpr.pi A B)",
        ] {
            assert!(
                synty.contains(needle),
                "SynTy must carry the rule `{needle}`"
            );
        }

        // (3) RECURSOR-SHAPE PIN: no fixedIndicesToParams promotion of the
        // uniform leading (G : ListType KExpr), because SynTy.lam's recursive
        // premise concludes at the EXTENDED context — the same reason
        // TypingCtx keeps its 3-ary index motive.
        assert!(
            synty.contains("SynTy (@ListType.cons KExpr A G) b2 B"),
            "SynTy.lam's recursive premise must conclude at the EXTENDED context, or the leading \
             index becomes fixed and fixedIndicesToParams promotes it"
        );
        // The development-closure premise is the LAST field of its constructor
        // and its recursive occurrence sits in the premise's CONCLUSION
        // (strict positivity).
        assert!(
            synty.contains(&format!(
                "SimpleTy A -> ({LAM_DEV_PREMISE}) -> SynTy G (KExpr.lam A b)"
            )),
            "SynTy.lam's development-closure premise must be its LAST field, after SimpleTy A"
        );

        // (4) ARM-ARITY PIN: SynTy.app has TWO recursive premises, so the
        // minor binds BOTH fields BEFORE both IHs, in constructor order — the
        // convention taken from the landed TypingCtx.rec consumer
        // fundamental_general, not guessed.
        let fund = val_synty_fundamental();
        assert!(
            fund.contains("(_qhf : SynTy qG qf (KExpr.pi qA qB)) (_qha : SynTy qG qa qA) (qihf :"),
            "the app minor must bind BOTH recursive fields before the first IH (fields-then-IHs)"
        );
        assert!(
            fund.contains("(qhA : SimpleTy qA) (_qhdev : forall"),
            "the lam minor must bind the non-recursive SimpleTy field before the recursive one"
        );

        // (5) PREMISE-FREEDOM GUARD: the capstone chain carries nothing.
        for (name, ty) in [
            ("synTy_sn", TY_SYNTY_SN.to_string()),
            ("synTy_sn_closed", TY_SYNTY_SN_CLOSED.to_string()),
            ("synTy_sn_subst", TY_SYNTY_SN_SUBST.to_string()),
            ("synTy_fundamental", TY_SYNTY_FUNDAMENTAL.to_string()),
            ("SynTy", synty.clone()),
            ("SubstOK", SRC_SUBST_OK.to_string()),
        ] {
            for forbidden in [
                "RecEnvClosed",
                "DefEnvClosed",
                "RecEnvLiftClosed",
                "CandModel",
                "cm_Red",
                "EnvAcyclic",
            ] {
                assert!(
                    !ty.contains(forbidden),
                    "{name} must carry no {forbidden} premise — the R6 capstone is unconditional"
                );
            }
        }
        // The capstone really is context-general, not closed-terms-only.
        assert!(
            TY_SYNTY_SN.contains("forall (G : ListType KExpr)"),
            "synTy_sn must hold at an ARBITRARY context (idsubst models every context)"
        );

        // (6) The fundamental theorem must consume R5's THEOREMS, never the
        // CandModel law projections of the guide's tower.
        for law in [
            "candInterp_sort_mem",
            "candInterp_app",
            "candInterp_lam",
            "candInterp_cr1",
        ] {
            assert!(
                fund.contains(law),
                "synTy_fundamental must go through R5's landed {law}"
            );
        }
        for projection in ["red_sort", "pi_elim", "pi_intro", "redAbstraction_holds"] {
            assert!(
                !fund.contains(projection),
                "synTy_fundamental must not consume the CandModel projection {projection}"
            );
        }
        // No psubst_instantiate reshaping anywhere: the codomain is NOT
        // instantiated, which is what the SimpleTy discipline buys.
        assert!(
            !fund.contains("psubst_instantiate"),
            "the non-dependent clause needs no psubst_instantiate reshaping"
        );

        // (7) The B obstruction must be about a REACHABLE argument, and must
        // consume R1's computation pin rather than restate it.
        let obs = val_r6_dependent_pi_self_reachable();
        assert!(
            obs.contains("cand_inst_bvar0") && obs.contains("candInterp_sort_mem"),
            "the dependent-Pi obstruction must pair the equation with the reachability of the \
             self-referential argument"
        );
        // Stated AT the recursive-call argument, not at the type: that is what
        // makes it a reachability claim about the call rather than about T.
        assert!(
            ty_r6_dependent_pi_self_reachable()
                .contains(&format!("candInterp {S0} (instantiate {V0} {SELF_PI})")),
            "the obstruction must claim membership AT the recursive-call argument \
             instantiate (bvar 0) (pi (sort 0) (bvar 0))"
        );
        assert!(
            ty_r6_dependent_pi_self_argument().contains(SELF_PI),
            "the obstruction must name the self-referential type pi (sort 0) (bvar 0)"
        );

        // (8) The substitution-necessity guard must CONSUME R5's beta-inertness
        // fact, never restate it.
        assert!(
            val_r6_substbody_beta_inert().contains("r5_bvarApp_no_beta"),
            "r6_substBody_beta_inert must consume R5's r5_bvarApp_no_beta"
        );
        assert!(
            val_r6_subst_creates_redex().contains("r6_substBody_beta_inert"),
            "r6_subst_creates_redex must consume the beta-inertness face"
        );

        // (8b) AndType SLOT PIN (the measured universe trap of this rung):
        // AndType (A : Type) (B : Type) is Type-in / Type-out, and the kernel
        // is NON-CUMULATIVE, so neither a Prop (an `Eq`) nor a Type-1 term
        // (anything quantifying over `(C : Type)`) may sit in a slot. Both
        // mistakes were made here and both are pinned.
        for (name, ty) in [
            ("r6_subst_creates_redex", ty_r6_subst_creates_redex()),
            ("r6_lam_body_acc_necessary", ty_r6_lam_body_acc_necessary()),
        ] {
            assert!(
                ty.starts_with("AndType "),
                "{name} should be the AndType pair"
            );
            assert!(
                !ty.contains("Eq KExpr") && !ty.contains("(C : Type)"),
                "{name}: an AndType slot may hold neither a Prop `Eq` nor a Type-1 \
                 `(C : Type)` quantification — split it into its own constant instead"
            );
        }

        // (9) PROP/TYPE PIN: the spec's Eq is Prop and the kernel is
        // NON-CUMULATIVE, so a (C : Type)-parameterised CPS eliminator may
        // never be instantiated at an Eq goal.
        for (name, ty, val) in theorem_sources() {
            for src in [&ty, &val] {
                for (elim, c_index) in [("option_none_ne_some_type", 2usize)] {
                    for c in type_valued_c_slots(src, elim, c_index) {
                        assert!(
                            !c.starts_with("(Eq ") && c != "Prop",
                            "{name}: {elim}'s C parameter is (C : Type) but got the Prop term \
                             {c}"
                        );
                    }
                }
            }
        }
    }

    /// Paren-aware extraction of the `c_index`-th argument of every
    /// application of `elim` in `src` (0-based from the first argument).
    fn type_valued_c_slots(src: &str, elim: &str, c_index: usize) -> Vec<String> {
        let bytes: Vec<char> = src.chars().collect();
        let mut out = Vec::new();
        let mut from = 0usize;
        while let Some(rel) = src[from..].find(elim) {
            let start = from + rel;
            from = start + elim.len();
            let before_ok =
                start == 0 || !src[..start].ends_with(|c: char| c.is_alphanumeric() || c == '_');
            let after = src[start + elim.len()..].chars().next();
            if !before_ok || after != Some(' ') {
                continue;
            }
            let mut i = src[..start].chars().count() + elim.chars().count();
            let mut args: Vec<String> = Vec::new();
            while i < bytes.len() && args.len() <= c_index {
                while i < bytes.len() && bytes[i] == ' ' {
                    i += 1;
                }
                if i >= bytes.len() || bytes[i] == ')' {
                    break;
                }
                let s = i;
                if bytes[i] == '(' {
                    let mut d = 0i64;
                    while i < bytes.len() {
                        if bytes[i] == '(' {
                            d += 1;
                        } else if bytes[i] == ')' {
                            d -= 1;
                            if d == 0 {
                                i += 1;
                                break;
                            }
                        }
                        i += 1;
                    }
                } else {
                    while i < bytes.len() && bytes[i] != ' ' && bytes[i] != ')' {
                        i += 1;
                    }
                }
                args.push(bytes[s..i].iter().collect());
            }
            if let Some(c) = args.get(c_index) {
                out.push(c.clone());
            }
        }
        out
    }

    /// Registration + kernel re-verification against the substitution bundle.
    #[test]
    fn test_candmodel_r6_registered_and_reverifies() {
        let spec = crate::test_utils::build_substitution_spec_with_stack();
        let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
        for (n, _) in decl_sources() {
            names.push(n);
        }
        for name in &names {
            assert!(
                spec.definitions().contains_key(name),
                "{name} should be registered by the candmodel_construct_r6 stage"
            );
        }
        for (name, _, _) in theorem_sources() {
            spec.verify_definition(&name).unwrap_or_else(|e| {
                panic!("{name} should re-typecheck in the spec environment: {e:?}")
            });
        }
    }
}

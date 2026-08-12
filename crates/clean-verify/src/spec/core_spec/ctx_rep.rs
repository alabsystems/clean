// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The **CtxRep bridge** — job C4 of the crystal program
//! (`designs/2026-07-29-crystal-deployed-kernel-bridge.md` §1.1,
//! `designs/2026-07-29-unified-implinfer-relation.md`).
//!
//! Layer 1 (`ImplInfer`, locally nameless, the DEPLOYED release
//! `infer_type_fast_inner`) and layer 2 (`KernelInfers`, de Bruijn, where the
//! metatheory lives) describe the same judgment in two representations. This
//! module builds the representation relation that connects them, and discharges
//! the bridge for the rules it can.
//!
//! # Why the obvious bridge is refutable, and this one is not
//!
//! An unrestricted identity-on-syntax bridge into the RETIRED implementation
//! model `KernelInferAccepts` is provably inconsistent: `KernelInfers.bvar` is
//! inhabited in a nonempty context while `kernel_infer_bvar_empty`
//! (`implementation_soundness_infer_accepts.rs:724-771`) makes every B
//! acceptance of a raw `BVar` `Empty`, so composing yields `Empty`. The same
//! shape of refutation applies here in the other direction:
//! `impl_infer_bvar_rejects` (`impl_infer.rs`) proves layer 1 NEVER infers a
//! type for a raw `bvar`, because the release arm is
//! `ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx))`
//! (`tc/infer.rs:350`). So no bridge that maps a layer-2 `bvar` derivation onto
//! a layer-1 `bvar` derivation can exist.
//!
//! The representation-sensitive bridge is the one that is not refuted: a
//! contextual variable maps to a successful FVar LOOKUP, never to the raw-bvar
//! error arm, because the binder case extends BOTH the renaming and the local
//! context with the fresh `FVarId`.
//!
//! # ExprRep is a FUNCTION, and that is the load-bearing design choice
//!
//! `to_kexpr e rho` back-translates a layer-1 `ImplExpr` into a layer-2 `KExpr`
//! under the renaming `rho`. Stating the bridge with a translation FUNCTION
//! rather than an inductive relation is what makes it provable in a tactic-free
//! explicit-term setting:
//!
//! * the conclusion needs **no existential** — the layer-2 type is literally
//!   `to_kexpr T_impl rho`, so no `Sigma`/`Exists` encoding is required;
//! * the proof needs **no inversion** — in every rule the layer-1 subject is a
//!   known constructor application, so `to_kexpr` iota-reduces to the matching
//!   `KExpr` head. A relational `ExprRep` would instead need a per-shape
//!   inversion lemma at every one of the nine rules.
//!
//! `ExprRep` is still registered (as the one-constructor family
//! `ExprRep rho ek ei`, inhabited exactly when `ek` is the translation), and
//! `expr_rep_of_eq` / `expr_rep_to_eq` prove it EQUIVALENT to the equation — so
//! the named relation exists and is provably not a second, weaker notion.
//!
//! # Freshness is numeric, never cofinite
//!
//! `rho` is a snoc-list of `FVarId`s whose POSITION is the de Bruijn index; the
//! binder case conses the fresh id on the front, which shifts every earlier
//! index by exactly one. That is the design's deliberate refusal of cofinite
//! quantification (crystal doc §2.1): production carries a numeric `next_id`
//! (`tc/local_context.rs:45-58`), so one renaming discipline suffices instead of
//! finite-support machinery recurring at every binder.
//!
//! # COVERAGE — stated as a fraction, never rounded up
//!
//! `ImplInfer` has nine rules. **Eight are bridged here**: `sort`, `fvar`,
//! `const`, `mdata`, `app`, `lam`, `pi`, `let_`. **The ninth, `lit`, is
//! REFUTED** — not left open, not rounded up into the numerator.
//!
//! **RE-MEASURED 2026-08-08 and DISCHARGED 2026-08-11.** The 2026-08-08 pass
//! found the blocker table stale in three of its five rows; the 2026-08-11 pass
//! proved the remaining four rules and refuted the fifth. What each row cost:
//!
//! | rule | status |
//! |---|---|
//! | `app` | **BRIDGED** (`impl_bridge_app`). Matches `KernelInfers.app` premise for premise — nothing is dropped. Its three `forall`-premises are `impl_whnf_to_whnf_to` / `impl_is_le_defeq` / `to_kexpr_at_instantiate` carried as hypotheses, for the stage reason below; the unconditional form is `impl_kinfers_app` (`impl_infer_sound.rs`). |
//! | `lam` | **BRIDGED** (`impl_bridge_lam`). Unblocked by the 2026-08-08 repair: `KernelInfers.lam` now carries `KernelInfers G A SA -> whnf_to SA (KExpr.sort u)`, the idiom its own `let_` arm always used, matching the deployed `ensure_sort` (`tc/infer.rs:521`). What was left was the open/abstract commutation, carried here as `hopen`/`habs` and discharged at M4 by `impl_kinfers_lam_scoped`. |
//! | `pi` | **BRIDGED** (`impl_bridge_pi`). Same repair, twice — `KernelInfers.pi` now carries a `whnf_to` premise for the domain (`tc/infer.rs:555`) AND the body (`:573`), which had not been modelled at all. No `habs`: a Pi result is a sort, so there is nothing to abstract back. |
//! | `let_` | **BRIDGED** (`impl_bridge_let_core` / `impl_bridge_let`). The old row was false in both halves: `KernelInfers.let_` carries `whnf_to Ty (KExpr.sort u)` and `DefEq Tv ty` as witnessed premises, so `hsort` and `hdef` land as themselves and this arm needed **no layer-2 change at all**. |
//! | `lit` | **REFUTED** (`kernelinfers_lit_rejects`, `impl_bridge_lit_refuted`, `impl_bridge_lit_unprovable`). `KernelInfers` has no literal rule (7 constructors: sort/bvar/pi/lam/const/app/let_), so there is nothing to bridge INTO — and that is now *proved*, not asserted: assuming the rule's would-be type yields `Empty`. |
//!
//! **STAGE ORDER is why several arms carry hypotheses.** `add_ctx_rep` runs
//! BEFORE `add_impl_infer_sound` (`bundles.rs`), and M4 consumes C4's
//! `to_kexpr_at` / `rho_index` / `CtxRep`, so the order cannot be swapped.
//! Nothing M4 registers — `impl_whnf_to_whnf_to`, `impl_is_le_defeq`,
//! `to_kexpr_at_instantiate`, `to_kexpr_open`, `to_kexpr_abstract`, `ImplLC`,
//! `ctx_rep_snoc_fresh` — is in scope here. Each such fact is therefore stated
//! as an explicit premise, byte-for-byte the M4 lemma that discharges it, and
//! `add_kinfers_bridge_arms` (`impl_infer_sound.rs`) supplies them:
//! `impl_kinfers_lam`, `impl_kinfers_lam_scoped`, `impl_bridge_pi_scoped`, and
//! `impl_bridge_app_witness` — the one witness that cannot fire in-stage.
//!
//! Note also that M4 bridged all nine rules into `TypingCtxConv` instead. That
//! is a different codomain, not a replacement for this table:
//! `TypingCtxConv.conv` is unrestricted and its `app`/`let_` arms carry neither
//! the `whnf_to` nor the `DefEq` premise, so it does not pin the returned type
//! or the operational steps. This table is about the `KernelInfers` lane, which
//! is the one that does.
//!
//! # The payoff corollary is STILL NOT reachable, and now for a proved reason
//!
//! "At the closed top level (`G = nil`, `rho` empty, opening is the identity)
//! the bridge collapses to a statement about closed declarations" requires the
//! GLOBAL theorem, i.e. `ImplInfer.rec` applied to all nine minors. A partial
//! set of minors cannot be assembled — the recursor demands every one.
//!
//! At 8/9 that is no longer a matter of effort: `impl_bridge_lit_unprovable`
//! proves the ninth minor **cannot exist** into this codomain, so the assembled
//! `ImplInfer.rec`-over-`KernelInfers` theorem is unreachable until
//! `KernelInfers` itself grows a literal rule. That is a decision about the
//! metatheory's expression calculus — the same class of change as the
//! 2026-08-08 `whnf_to` repair — and it is not made unilaterally here. What IS
//! landed is the closed-level fact the corollary would rest on:
//! `ctx_rep_nil_lookup_empty` proves that at `LCtx.nil` no `fvar` lookup can
//! succeed, which is the formal content of "opening is the identity when the
//! context is empty", and `ctx_rep_nil_witness` supplies `CtxRep nil nil nil`.
//!
//! ZERO new axioms: every declaration is an `add_inductive` (census-neutral) or
//! a valued definition with an empty axiom closure.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// `BinderData { info: Default, mult: Many }` — the annotation `ctx_push_let`
/// stores (`tc/config.rs:48` → `tc/local_context.rs:126`) and the one the C1
/// witnesses use, so the `CtxRep` witness lines up with
/// `implinfer_lam_identity_witness` entry for entry.
const BD: &str = "(BinderData.mk BinderInfo.default Multiplicity.many)";

impl Specification {
    /// C4: the representation apparatus (`to_kexpr`, `ExprRep`, `CtxRep`) and
    /// the bridge lemmas for the rules it discharges.
    pub(super) fn add_ctx_rep(&mut self) -> Result<(), SpecError> {
        self.add_ctx_rep_translation()?;
        self.add_ctx_rep_relation()?;
        self.add_ctx_rep_lookup()?;
        self.add_ctx_rep_bridge()?;
        self.add_ctx_rep_witnesses()?;
        Ok(())
    }

    /// The back-translation layer 1 → layer 2, and the `ExprRep` family it
    /// realizes.
    fn add_ctx_rep_translation(&mut self) -> Result<(), SpecError> {
        // rho — the renaming. A snoc-list of FVarIds whose POSITION is the de
        // Bruijn index in the layer-2 context G. Consing the fresh id at a
        // binder shifts every earlier index by one, which is exactly what
        // `KernelInfers.bvar`'s lift discipline expects.
        //
        // An absent id yields the list's LENGTH, i.e. an index one past the end
        // of G, on which `ctx_lookup` returns none. So a layer-1 free variable
        // that is not in the renaming translates to junk that layer 2 cannot
        // type — the correct failure mode, not a silent success.
        self.add_recursive_def(
            r"def rho_index (rho : ListType Nat) (x : Nat) : Nat := ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero (fun (y : Nat) (rest : ListType Nat) (ih : Nat) => Bool.rec (fun (_ : Bool) => Nat) (Nat.succ ih) Nat.zero (nat_eqb y x)) rho",
            "Position of an FVarId in the renaming = its de Bruijn index in the \
             layer-2 context. Scans most-recent-first, exactly as lctx_lookup does \
             on the layer-1 side, so both scrutinize the SAME boolean nat_eqb at \
             each entry — which is what lets the CtxRep lookup proof split once per \
             level instead of twice. An absent id returns the length, an index on \
             which ctx_lookup is none.",
        )?;

        // Literals: KExpr.lit is Nat-ONLY while ImplLit is Nat | String.
        //
        // NAMED REPRESENTATION GAP: a String literal has no layer-2 image, so
        // this map is NOT injective on literals. Nothing downstream can exploit
        // that, because `KernelInfers` has no literal rule at all — the `lit`
        // rule is unbridgeable for that independent reason (see the module
        // header's coverage table). Recorded rather than papered over.
        self.add_recursive_def(
            r"def impl_lit_to_kexpr (l : ImplLit) : KExpr := match l with
| ImplLit.natVal k => KExpr.lit k
| ImplLit.strVal k => KExpr.lit k",
            "Layer-1 literal to layer-2 literal. NOT INJECTIVE and said so: KExpr.lit \
             is Nat-only (expr_model.rs), ImplLit is Nat|String (expr::Literal), so \
             the String case has no distinct image. Inert, because KernelInfers has \
             no literal rule to bridge into.",
        )?;

        // to_kexpr_at: the back-translation, with a binder DEPTH.
        //
        // Layer 1 is locally nameless: bound variables under a binder are still
        // de Bruijn (`ImplExpr.bvar`), and only the binder the checker is
        // CURRENTLY under has been opened into an `ImplExpr.fvar`. So a
        // translation must map bvars through unchanged and map each fvar to
        // `depth + rho_index`, incrementing depth under every binder — the exact
        // inverse of the open/abstract pair the release Lam/Pi/Let arms perform
        // (tc/infer.rs:533-548, eta.rs:196-199).
        //
        // `mdata` is ERASED: KExpr has no metadata constructor and the release
        // MData arm is a pure passthrough (tc/infer.rs:657-663), so erasure is
        // the faithful translation — and it is why the mdata bridge below is an
        // identity function rather than a proof.
        //
        // The fvar case writes `Nat.add (rho_index rho y) d`, not
        // `Nat.add d (rho_index rho y)`: Nat.add recurses on its SECOND argument
        // (foundation_types.rs:525), so this form reduces definitionally to
        // `rho_index rho y` at the top-level depth d = 0, which every bridge
        // statement below relies on.
        self.add_recursive_def(
            r"def to_kexpr_at (e : ImplExpr) (rho : ListType Nat) (d : Nat) : KExpr := match e with
| ImplExpr.bvar i => KExpr.bvar i
| ImplExpr.fvar y => KExpr.bvar (Nat.add (rho_index rho y) d)
| ImplExpr.sort l => KExpr.sort l
| ImplExpr.const nm us => KExpr.const nm us
| ImplExpr.app f a => KExpr.app (to_kexpr_at f rho d) (to_kexpr_at a rho d)
| ImplExpr.lam bd ty b => KExpr.lam (to_kexpr_at ty rho d) (to_kexpr_at b rho (Nat.succ d))
| ImplExpr.pi bd ty b => KExpr.pi (to_kexpr_at ty rho d) (to_kexpr_at b rho (Nat.succ d))
| ImplExpr.let_ nm ty v b => KExpr.let_ (to_kexpr_at ty rho d) (to_kexpr_at v rho d) (to_kexpr_at b rho (Nat.succ d))
| ImplExpr.lit lt => impl_lit_to_kexpr lt
| ImplExpr.mdata inner => to_kexpr_at inner rho d",
            "Back-translation layer 1 -> layer 2 at binder depth d: bvars pass \
             through (layer 1 is only locally nameless AT the binder it is under), \
             each fvar becomes the de Bruijn index `rho_index + d`, mdata is ERASED \
             (KExpr has no metadata and the release MData arm is a passthrough, \
             tc/infer.rs:657-663), binder data and the let name are DROPPED (KExpr \
             carries neither). Depth increments under lam/pi/let bodies, mirroring \
             lift_at / instantiate_at. This is the inverse of the open/abstract pair \
             the release binder arms perform (tc/infer.rs:533-548).",
        )?;

        self.add_recursive_def(
            r"def to_kexpr (e : ImplExpr) (rho : ListType Nat) : KExpr := to_kexpr_at e rho Nat.zero",
            "to_kexpr_at at depth 0 — the translation of a term the deployed checker \
             is looking at RIGHT NOW, all of whose binders above it have already \
             been opened into fvars. Every bridge statement is stated at this depth.",
        )?;

        // ExprRep — the named relation of the C4 brief, realized as the
        // one-constructor family "ek IS the translation of ei under rho".
        // Registered so the relation exists under its own name and can be
        // audited by the vacuity firewall; the two lemmas below prove it
        // equivalent to the equation, so it cannot drift into a weaker notion.
        self.add_inductive(
            r"inductive ExprRep (rho : ListType Nat) : KExpr -> ImplExpr -> Type
| mk : forall (ei : ImplExpr), ExprRep rho (to_kexpr ei rho) ei",
            "ExprRep rho ek ei: the de Bruijn KExpr ek REPRESENTS the layer-1 ImplExpr \
             ei under the renaming rho. One constructor, because the representation \
             is functional — `to_kexpr` computes it. That is the load-bearing design \
             choice: it removes the existential from the bridge's conclusion AND the \
             per-shape inversion lemma the bridge proof would otherwise need at every \
             rule. expr_rep_of_eq / expr_rep_to_eq prove this family EQUIVALENT to \
             `Eq KExpr ek (to_kexpr ei rho)`. ZERO new axioms.",
        )?;

        self.add_definition(SpecDefinition {
            name: "expr_rep_to_eq".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (ek : KExpr) (ei : ImplExpr), ",
                "ExprRep rho ek ei -> Eq KExpr ek (to_kexpr ei rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (ek : KExpr) (ei : ImplExpr) ",
                    "(h : ExprRep rho ek ei) => ",
                    "ExprRep.rec rho ",
                    "(fun (z : KExpr) (e2 : ImplExpr) (_h : ExprRep rho z e2) => ",
                    "Eq KExpr z (to_kexpr e2 rho)) ",
                    "(fun (e2 : ImplExpr) => Eq.refl KExpr (to_kexpr e2 rho)) ",
                    "ek ei h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "ExprRep is no weaker than the equation: every ExprRep derivation yields ",
                "Eq KExpr ek (to_kexpr ei rho). Proved by ExprRep.rec; the single minor is ",
                "Eq.refl because the constructor's index IS the translation. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ExprRep".to_string(),
                "ExprRep.rec".to_string(),
                "to_kexpr".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "expr_rep_of_eq".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (ek : KExpr) (ei : ImplExpr), ",
                "Eq KExpr ek (to_kexpr ei rho) -> ExprRep rho ek ei"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (ek : KExpr) (ei : ImplExpr) ",
                    "(h : Eq KExpr ek (to_kexpr ei rho)) => ",
                    "Eq.substType KExpr (fun (z : KExpr) => ExprRep rho z ei) ",
                    "(to_kexpr ei rho) ek ",
                    "(Eq.symm KExpr ek (to_kexpr ei rho) h) ",
                    "(ExprRep.mk rho ei)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "ExprRep is no STRONGER than the equation: the equation yields the relation. ",
                "With expr_rep_to_eq this pins ExprRep as exactly `ek = to_kexpr ei rho`, so ",
                "the bridge lemmas below may state their conclusions with to_kexpr directly ",
                "without weakening the named relation. Transport via Eq.substType (Type-valued ",
                "motive). Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ExprRep".to_string(),
                "ExprRep.mk".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The layer-2 side's variable-type function and `CtxRep` itself.
    fn add_ctx_rep_relation(&mut self) -> Result<(), SpecError> {
        // opt_var_type / ctx_var_type: the type layer 2 assigns to bvar i.
        //
        // `KernelInfers.bvar` concludes `lift_at A Nat.zero (Nat.succ i)` from
        // `ctx_lookup G i = some A` — layer 2 stores each entry relative to its
        // OWN position and re-lifts on lookup. Layer 1 stores the already-open
        // type and applies NO lift (`tc/infer.rs:351-359`, the deployed FVar arm
        // is a plain `.map(|d| d.type_.clone())`). Naming the lifted form as a
        // FUNCTION is what lets CtxRep's lookup lemma be stated without an
        // existential over the stored entry.
        self.add_recursive_def(
            r"def opt_var_type (o : OptionType KExpr) (i : Nat) : OptionType KExpr := OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (A : KExpr) => OptionType.some KExpr (lift_at A Nat.zero (Nat.succ i))) o",
            "Apply KernelInfers.bvar's lift discipline to an optional context entry: \
             none stays none, some A becomes some (lift_at A 0 (succ i)).",
        )?;

        self.add_recursive_def(
            r"def ctx_var_type (G : ListType KExpr) (i : Nat) : OptionType KExpr := opt_var_type (ctx_lookup G i) i",
            "The type layer 2 assigns to the de Bruijn variable i in context G — i.e. \
             exactly the type KernelInfers.bvar concludes, packaged as a total \
             function on the OptionType so the CtxRep correspondence needs no \
             existential over the stored entry.",
        )?;

        self.add_recursive_def(
            r"def opt_lift1 (o : OptionType KExpr) : OptionType KExpr := OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (A : KExpr) => OptionType.some KExpr (lift_at A Nat.zero (Nat.succ Nat.zero))) o",
            "Lift an optional KExpr by one at cutoff zero — the single-binder \
             weakening step relating the layer-2 view of a context to the view of \
             that context extended by one entry.",
        )?;

        // CtxRep G rho D — the context correspondence.
        //
        // Kept as WEAK as possible, because it is a HYPOTHESIS everywhere it is
        // used. It says only three things, and each is an invariant of the
        // representation rather than a conclusion of anything:
        //
        //  1. the three structures grow in lockstep (nil/snoc);
        //  2. HEAD: the layer-1 entry's stored (already-open) type translates,
        //     under the EXTENDED renaming, to the layer-2 entry lifted by one —
        //     the exact statement `KernelInfers.bvar` needs at index 0;
        //  3. FRESHNESS, in the only form the proof consumes: consing the new id
        //     onto the renaming shifts the translation of everything ALREADY in
        //     the layer-1 context by exactly one. Production guarantees this by
        //     construction (`LocalContext.next_id` is incremented on every push
        //     and never rewound, `tc/local_context.rs:81,111`, and push asserts
        //     an id is never reused, `:86-89`), so nothing already stored can
        //     mention the fresh id. Stated as an equation over the entries that
        //     actually exist rather than as a set-theoretic support condition —
        //     that is the design's refusal of cofinite quantification.
        //
        // NOT masquerade: none of these fields is the bridge's conclusion. The
        // conclusion is a `KernelInfers` DERIVATION (`impl_bridge_fvar`), which
        // no field mentions; the fields are equations about syntax. The honest
        // residual is that field 3 is assumed rather than derived from a
        // well-scopedness invariant on `ImplExpr` — deriving it needs a
        // locally-closed predicate plus a translation/lift commutation lemma,
        // and is the first build item for extending this bridge to the binder
        // rules.
        self.add_inductive(
            concat!(
                "inductive CtxRep : ListType KExpr -> ListType Nat -> LCtx -> Type\n",
                "| nil : CtxRep (ListType.nil KExpr) (ListType.nil Nat) LCtx.nil\n",
                "| snoc : forall (G : ListType KExpr) (rho : ListType Nat) (D : LCtx) (x : Nat) (Ak : KExpr) (Ai : ImplExpr) (dv : OptionType ImplExpr) (bd : BinderData), CtxRep G rho D -> Eq KExpr (to_kexpr Ai (ListType.cons Nat x rho)) (lift_at Ak Nat.zero (Nat.succ Nat.zero)) -> (forall (y : Nat) (Ay : ImplExpr), Eq (OptionType ImplExpr) (lctx_lookup D y) (OptionType.some ImplExpr Ay) -> Eq KExpr (to_kexpr Ay (ListType.cons Nat x rho)) (lift_at (to_kexpr Ay rho) Nat.zero (Nat.succ Nat.zero))) -> CtxRep (ListType.cons KExpr Ak G) (ListType.cons Nat x rho) (LCtx.snoc D (LocalDecl.mk x Ai dv bd))"
            ),
            "CtxRep G rho D: the layer-2 de Bruijn context G represents the DEPLOYED \
             kernel's LocalContext D under the renaming rho. Three fields, each an \
             invariant of the representation and none of them the bridge's conclusion: \
             (1) the structures grow in lockstep; (2) the head entry's stored \
             already-open layer-1 type translates, under the extended renaming, to the \
             layer-2 entry lifted by one — precisely what KernelInfers.bvar concludes \
             at index 0, and precisely where layer 1 differs (the deployed FVar arm \
             applies NO lift, tc/infer.rs:351-359); (3) freshness in the only form the \
             proof consumes — consing the new id shifts the translation of everything \
             already in D by exactly one, which production guarantees because next_id \
             is never rewound and ids are never reused (tc/local_context.rs:81-89). \
             Field (3) is an assumed invariant, named as this bridge's residual: \
             deriving it needs a locally-closed predicate on ImplExpr plus a \
             translation/lift commutation lemma. ZERO new axioms (census-neutral).",
        )?;

        Ok(())
    }

    /// The context-lookup theorem — the substance of the bridge — and the
    /// layer-2 variable-rule inversion it feeds.
    fn add_ctx_rep_lookup(&mut self) -> Result<(), SpecError> {
        // opt_var_type_succ: layer 2's view of variable (succ i) in an extended
        // context is layer 2's view of variable i, lifted by one. The `some`
        // branch is exactly `lift_at_compose` at cutoff 0 with amounts
        // (succ i) and 1: Nat.add recurses on its second argument
        // (foundation_types.rs:525), so `Nat.add (succ i) (succ zero)` reduces
        // definitionally to `succ (succ i)` and no arithmetic lemma is needed.
        self.add_definition(SpecDefinition {
            name: "opt_var_type_succ".to_string(),
            type_src: concat!(
                "forall (o : OptionType KExpr) (i : Nat), ",
                "Eq (OptionType KExpr) (opt_var_type o (Nat.succ i)) (opt_lift1 (opt_var_type o i))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (o : OptionType KExpr) (i : Nat) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o2 : OptionType KExpr) => Eq (OptionType KExpr) ",
                    "(opt_var_type o2 (Nat.succ i)) (opt_lift1 (opt_var_type o2 i))) ",
                    "(Eq.refl (OptionType KExpr) (OptionType.none KExpr)) ",
                    "(fun (A : KExpr) => ",
                    "Eq.cong KExpr (OptionType KExpr) (fun (t : KExpr) => OptionType.some KExpr t) ",
                    "(lift_at A Nat.zero (Nat.succ (Nat.succ i))) ",
                    "(lift_at (lift_at A Nat.zero (Nat.succ i)) Nat.zero (Nat.succ Nat.zero)) ",
                    "(Eq.symm KExpr ",
                    "(lift_at (lift_at A Nat.zero (Nat.succ i)) Nat.zero (Nat.succ Nat.zero)) ",
                    "(lift_at A Nat.zero (Nat.succ (Nat.succ i))) ",
                    "(lift_at_compose A Nat.zero (Nat.succ i) (Nat.succ Nat.zero)))) ",
                    "o"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Weakening at the layer-2 lookup level: the type of variable (succ i) in a ",
                "context extended by one entry is the type of variable i in the original ",
                "context, lifted by one at cutoff zero. Proved by OptionType.rec; the none ",
                "branch is refl and the some branch is lift_at_compose at cutoff 0 with ",
                "amounts (succ i) and 1 (Nat.add recurses on its second argument, so the ",
                "summed amount reduces definitionally). This is what makes the CtxRep lookup ",
                "induction go through in the tail case. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_var_type".to_string(),
                "opt_lift1".to_string(),
                "lift_at_compose".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_rep_lookup: THE bridge's substance.
        //
        // From a layer-1 context lookup that SUCCEEDS, produce the layer-2
        // statement about the corresponding de Bruijn index. Induction on
        // CtxRep; at the snoc step both `lctx_lookup (snoc D d) x` and
        // `rho_index (cons x0 rho) x` iota-reduce to a Bool.rec on the SAME
        // scrutinee `nat_eqb x0 x`, so ONE Bool.rec case split with a
        // b-abstracted motive handles both sides at once:
        //
        //   * true  (x is the new entry): index 0, discharged by CtxRep's head
        //     field after transporting along option_some_inj;
        //   * false (x is older): index succ i, discharged by opt_var_type_succ
        //     + the IH + CtxRep's freshness field.
        self.add_definition(SpecDefinition {
            name: "ctx_rep_lookup".to_string(),
            type_src: concat!(
                "forall (G : ListType KExpr) (rho : ListType Nat) (D : LCtx), ",
                "CtxRep G rho D -> forall (x : Nat) (Ai : ImplExpr), ",
                "Eq (OptionType ImplExpr) (lctx_lookup D x) (OptionType.some ImplExpr Ai) -> ",
                "Eq (OptionType KExpr) (ctx_var_type G (rho_index rho x)) ",
                "(OptionType.some KExpr (to_kexpr Ai rho))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (G : ListType KExpr) (rho : ListType Nat) (D : LCtx) ",
                    "(h : CtxRep G rho D) => ",
                    "CtxRep.rec ",
                    "(fun (G2 : ListType KExpr) (rho2 : ListType Nat) (D2 : LCtx) ",
                    "(_h : CtxRep G2 rho2 D2) => forall (x : Nat) (Ai : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup D2 x) (OptionType.some ImplExpr Ai) -> ",
                    "Eq (OptionType KExpr) (ctx_var_type G2 (rho_index rho2 x)) ",
                    "(OptionType.some KExpr (to_kexpr Ai rho2))) ",
                    // ── nil: lctx_lookup LCtx.nil x is none, so the hypothesis
                    // is false and Empty.rec closes any goal (including this
                    // Prop-valued one).
                    "(fun (x : Nat) (Ai : ImplExpr) ",
                    "(hlk : Eq (OptionType ImplExpr) (lctx_lookup LCtx.nil x) ",
                    "(OptionType.some ImplExpr Ai)) => ",
                    "Empty.rec (fun (_e : Empty) => Eq (OptionType KExpr) ",
                    "(ctx_var_type (ListType.nil KExpr) (rho_index (ListType.nil Nat) x)) ",
                    "(OptionType.some KExpr (to_kexpr Ai (ListType.nil Nat)))) ",
                    "(option_none_ne_some_type ImplExpr Ai Empty hlk)) ",
                    // ── snoc
                    "(fun (G2 : ListType KExpr) (rho2 : ListType Nat) (D2 : LCtx) (x0 : Nat) ",
                    "(Ak : KExpr) (Ai0 : ImplExpr) (dv : OptionType ImplExpr) (bd : BinderData) ",
                    "(hrec : CtxRep G2 rho2 D2) ",
                    "(hhead : Eq KExpr (to_kexpr Ai0 (ListType.cons Nat x0 rho2)) ",
                    "(lift_at Ak Nat.zero (Nat.succ Nat.zero))) ",
                    "(hshift : forall (y : Nat) (Ay : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup D2 y) (OptionType.some ImplExpr Ay) -> ",
                    "Eq KExpr (to_kexpr Ay (ListType.cons Nat x0 rho2)) ",
                    "(lift_at (to_kexpr Ay rho2) Nat.zero (Nat.succ Nat.zero))) ",
                    "(ih : forall (x : Nat) (Ai : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup D2 x) (OptionType.some ImplExpr Ai) -> ",
                    "Eq (OptionType KExpr) (ctx_var_type G2 (rho_index rho2 x)) ",
                    "(OptionType.some KExpr (to_kexpr Ai rho2))) ",
                    "(x : Nat) (Ai : ImplExpr) => ",
                    "Bool.rec ",
                    "(fun (b : Bool) => ",
                    "Eq (OptionType ImplExpr) ",
                    "(Bool.rec (fun (_b : Bool) => OptionType ImplExpr) (lctx_lookup D2 x) ",
                    "(OptionType.some ImplExpr Ai0) b) (OptionType.some ImplExpr Ai) -> ",
                    "Eq (OptionType KExpr) ",
                    "(ctx_var_type (ListType.cons KExpr Ak G2) ",
                    "(Bool.rec (fun (_b : Bool) => Nat) (Nat.succ (rho_index rho2 x)) Nat.zero b)) ",
                    "(OptionType.some KExpr (to_kexpr Ai (ListType.cons Nat x0 rho2)))) ",
                    // false branch — x is an OLDER entry
                    "(fun (hlk : Eq (OptionType ImplExpr) (lctx_lookup D2 x) ",
                    "(OptionType.some ImplExpr Ai)) => ",
                    "Eq.trans (OptionType KExpr) ",
                    "(ctx_var_type (ListType.cons KExpr Ak G2) (Nat.succ (rho_index rho2 x))) ",
                    "(opt_lift1 (OptionType.some KExpr (to_kexpr Ai rho2))) ",
                    "(OptionType.some KExpr (to_kexpr Ai (ListType.cons Nat x0 rho2))) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(ctx_var_type (ListType.cons KExpr Ak G2) (Nat.succ (rho_index rho2 x))) ",
                    "(opt_lift1 (ctx_var_type G2 (rho_index rho2 x))) ",
                    "(opt_lift1 (OptionType.some KExpr (to_kexpr Ai rho2))) ",
                    "(opt_var_type_succ (ctx_lookup G2 (rho_index rho2 x)) (rho_index rho2 x)) ",
                    "(Eq.cong (OptionType KExpr) (OptionType KExpr) opt_lift1 ",
                    "(ctx_var_type G2 (rho_index rho2 x)) ",
                    "(OptionType.some KExpr (to_kexpr Ai rho2)) (ih x Ai hlk))) ",
                    "(Eq.cong KExpr (OptionType KExpr) ",
                    "(fun (t : KExpr) => OptionType.some KExpr t) ",
                    "(lift_at (to_kexpr Ai rho2) Nat.zero (Nat.succ Nat.zero)) ",
                    "(to_kexpr Ai (ListType.cons Nat x0 rho2)) ",
                    "(Eq.symm KExpr (to_kexpr Ai (ListType.cons Nat x0 rho2)) ",
                    "(lift_at (to_kexpr Ai rho2) Nat.zero (Nat.succ Nat.zero)) ",
                    "(hshift x Ai hlk)))) ",
                    // true branch — x IS the new entry, index 0
                    "(fun (hlk : Eq (OptionType ImplExpr) (OptionType.some ImplExpr Ai0) ",
                    "(OptionType.some ImplExpr Ai)) => ",
                    "Eq.cong KExpr (OptionType KExpr) ",
                    "(fun (t : KExpr) => OptionType.some KExpr t) ",
                    "(lift_at Ak Nat.zero (Nat.succ Nat.zero)) ",
                    "(to_kexpr Ai (ListType.cons Nat x0 rho2)) ",
                    "(Eq.symm KExpr (to_kexpr Ai (ListType.cons Nat x0 rho2)) ",
                    "(lift_at Ak Nat.zero (Nat.succ Nat.zero)) ",
                    "(Eq.substType ImplExpr ",
                    "(fun (z : ImplExpr) => Eq KExpr (to_kexpr z (ListType.cons Nat x0 rho2)) ",
                    "(lift_at Ak Nat.zero (Nat.succ Nat.zero))) ",
                    "Ai0 Ai (option_some_inj ImplExpr Ai0 Ai hlk) hhead))) ",
                    "(nat_eqb x0 x)) ",
                    "G rho D h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE CONTEXT BRIDGE: a SUCCESSFUL layer-1 lookup of an FVarId in the deployed ",
                "kernel's LocalContext yields the layer-2 statement about the corresponding de ",
                "Bruijn index — including the lift that KernelInfers.bvar applies and the ",
                "deployed FVar arm does not (tc/infer.rs:351-359). This is what makes a ",
                "contextual variable map to a successful lookup instead of the raw-bvar error ",
                "arm, and therefore what makes the bridge representation-sensitive rather than ",
                "identity-on-syntax (crystal doc 1.1). Proved by CtxRep.rec: the nil case is ",
                "vacuous (lctx_lookup of the empty context is none), and the snoc case splits ",
                "ONCE on nat_eqb x0 x because lctx_lookup and rho_index scrutinize the same ",
                "boolean — the true branch is CtxRep's head field transported along ",
                "option_some_inj, the false branch chains opt_var_type_succ, the IH and ",
                "CtxRep's freshness field. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxRep".to_string(),
                "CtxRep.rec".to_string(),
                "ctx_var_type".to_string(),
                "rho_index".to_string(),
                "lctx_lookup".to_string(),
                "opt_var_type_succ".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.symm".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kernelinfers_var_of_var_type: turn the lookup statement back into a
        // layer-2 DERIVATION. The generalize-then-case pattern: recurse on the
        // OptionType with the defining equation `ctx_lookup G i = o` carried as
        // an extra premise, so the `some` branch still knows WHICH entry it is
        // looking at and can feed KernelInfers.bvar.
        self.add_definition(SpecDefinition {
            name: "kernelinfers_var_of_var_type".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (i : Nat) (Tk : KExpr), ",
                "Eq (OptionType KExpr) (ctx_var_type G i) (OptionType.some KExpr Tk) -> ",
                "KernelInfers tenv G (KExpr.bvar i) Tk"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (i : Nat) ",
                    "(Tk : KExpr) ",
                    "(h : Eq (OptionType KExpr) (ctx_var_type G i) (OptionType.some KExpr Tk)) => ",
                    "OptionType.rec KExpr ",
                    "(fun (o : OptionType KExpr) => ",
                    "Eq (OptionType KExpr) (ctx_lookup G i) o -> ",
                    "Eq (OptionType KExpr) (opt_var_type o i) (OptionType.some KExpr Tk) -> ",
                    "KernelInfers tenv G (KExpr.bvar i) Tk) ",
                    "(fun (_hl : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.none KExpr)) ",
                    "(hs : Eq (OptionType KExpr) (OptionType.none KExpr) ",
                    "(OptionType.some KExpr Tk)) => ",
                    "option_none_ne_some_type KExpr Tk ",
                    "(KernelInfers tenv G (KExpr.bvar i) Tk) hs) ",
                    "(fun (A : KExpr) ",
                    "(hl : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) ",
                    "(hs : Eq (OptionType KExpr) ",
                    "(OptionType.some KExpr (lift_at A Nat.zero (Nat.succ i))) ",
                    "(OptionType.some KExpr Tk)) => ",
                    "Eq.substType KExpr ",
                    "(fun (T : KExpr) => KernelInfers tenv G (KExpr.bvar i) T) ",
                    "(lift_at A Nat.zero (Nat.succ i)) Tk ",
                    "(option_some_inj KExpr (lift_at A Nat.zero (Nat.succ i)) Tk hs) ",
                    "(KernelInfers.bvar tenv G i A hl)) ",
                    "(ctx_lookup G i) ",
                    "(Eq.refl (OptionType KExpr) (ctx_lookup G i)) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Layer-2 variable-rule introduction from the lookup statement: ",
                "ctx_var_type G i = some Tk yields a KernelInfers derivation of bvar i : Tk. ",
                "Proved by OptionType.rec over ctx_lookup G i with the defining equation ",
                "carried as an extra premise (the generalize-then-case pattern), so the some ",
                "branch retains the entry it is looking at and can apply KernelInfers.bvar; ",
                "the none branch is closed by option_none_ne_some_type at a Type-valued goal. ",
                "Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers".to_string(),
                "ctx_var_type".to_string(),
                "opt_var_type".to_string(),
                "ctx_lookup".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some_type".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The bridge, rule by rule — eight of `ImplInfer`'s nine, plus the
    /// kernel-checked refutation of the ninth.
    fn add_ctx_rep_bridge(&mut self) -> Result<(), SpecError> {
        // ── fvar ────────────────────────────────────────────────────────────
        // The rule the whole two-layer architecture exists for. Layer 1 looks
        // an FVarId up in the LocalContext and returns the stored type UNLIFTED
        // (tc/infer.rs:351-359); layer 2 looks a de Bruijn index up and lifts.
        // CtxRep is exactly the invariant that makes those the same statement.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_fvar".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                "(rho : ListType Nat) (D : LCtx) (x : Nat) (Ai : ImplExpr), ",
                "CtxRep G rho D -> ",
                "Eq (OptionType ImplExpr) (lctx_lookup D x) (OptionType.some ImplExpr Ai) -> ",
                "KernelInfers tenv G (to_kexpr (ImplExpr.fvar x) rho) (to_kexpr Ai rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                    "(rho : ListType Nat) (D : LCtx) (x : Nat) (Ai : ImplExpr) ",
                    "(hctx : CtxRep G rho D) ",
                    "(hlk : Eq (OptionType ImplExpr) (lctx_lookup D x) ",
                    "(OptionType.some ImplExpr Ai)) => ",
                    "kernelinfers_var_of_var_type tenv G (rho_index rho x) (to_kexpr Ai rho) ",
                    "(ctx_rep_lookup G rho D hctx x Ai hlk)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, fvar rule (ImplInfer.fvar, tc/infer.rs:351-359): under CtxRep, a ",
                "successful deployed-kernel FVar lookup yields the corresponding layer-2 ",
                "KernelInfers derivation. The subject translates definitionally — ",
                "to_kexpr (fvar x) rho reduces to KExpr.bvar (rho_index rho x) because Nat.add ",
                "recurses on its second argument and the top-level depth is zero. This is the ",
                "rule the two-layer split exists for: layer 1 returns the stored type unlifted, ",
                "layer 2 lifts by (succ i), and CtxRep is the invariant that reconciles them. ",
                "Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxRep".to_string(),
                "ctx_rep_lookup".to_string(),
                "kernelinfers_var_of_var_type".to_string(),
                "to_kexpr".to_string(),
                "rho_index".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── sort ────────────────────────────────────────────────────────────
        // Both layers agree: Sort l : Sort (succ l). Note what the layer-2 rule
        // does NOT have — the release Sort arm's check_level premise
        // (tc/infer.rs:366-368) has no counterpart in KernelInfers.sort, so the
        // declared-level-param discipline is invisible to layer 2. Recorded
        // here rather than smuggled in as a dead hypothesis.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_sort".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                "(rho : ListType Nat) (l : Level), ",
                "KernelInfers tenv G (to_kexpr (ImplExpr.sort l) rho) ",
                "(to_kexpr (ImplExpr.sort (Level.succ l)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                    "(rho : ListType Nat) (l : Level) => KernelInfers.sort tenv G l"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, sort rule (ImplInfer.sort, tc/infer.rs:360-370). Both sides reduce to ",
                "KExpr.sort, so the layer-2 derivation is the bare constructor. Recorded ",
                "asymmetry: KernelInfers.sort has NO premise, so layer 2 does not model the ",
                "declared-level-param discipline the release arm consults — the layer-1 rule's ",
                "level_params_ok premise is simply not needed here, and is deliberately not ",
                "carried as a dead hypothesis. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers".to_string(),
                "to_kexpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── mdata ───────────────────────────────────────────────────────────
        // KExpr has no metadata constructor and the release MData arm is a pure
        // passthrough, so translation ERASES the node and the bridge is the
        // identity — the cleanest possible statement that the two layers agree.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_mdata".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                "(rho : ListType Nat) (e : ImplExpr) (T : ImplExpr), ",
                "KernelInfers tenv G (to_kexpr e rho) (to_kexpr T rho) -> ",
                "KernelInfers tenv G (to_kexpr (ImplExpr.mdata e) rho) (to_kexpr T rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                    "(rho : ListType Nat) (e : ImplExpr) (T : ImplExpr) ",
                    "(h : KernelInfers tenv G (to_kexpr e rho) (to_kexpr T rho)) => h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, mdata rule (ImplInfer.mdata, tc/infer.rs:657-663). KExpr has no ",
                "metadata constructor and the release arm is a pure passthrough, so the ",
                "translation ERASES the node and the two judgments are definitionally the same ",
                "— the bridge is the identity function, which is the strongest form this ",
                "agreement can take. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers".to_string(),
                "to_kexpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── const ───────────────────────────────────────────────────────────
        // The two layers hold DIFFERENT environments: layer 1's tenv maps a name
        // to an ImplConstInfo record (level_params, type, is_unsafe, is_partial)
        // and instantiates the universe parameters at the use site; layer 2's
        // tenv maps a name straight to a KExpr and ignores `us` entirely. So the
        // bridge needs an explicit environment-correspondence hypothesis, and it
        // is spelled inline (not as a named alias) because it quantifies over
        // the universe-instantiation list, which varies per const NODE.
        //
        // The other four operations of the release Const arm — the level-arity
        // check, the per-level check_level, and the unsafe/partial gates
        // (tc/infer.rs:383,397-399,401,404) — have NO layer-2 counterpart:
        // KernelInfers.const's single premise is the environment lookup. That is
        // another measured asymmetry, not a gap in this proof.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_const".to_string(),
            type_src: concat!(
                "forall (tenv2 : Name -> OptionType KExpr) ",
                "(tenv1 : Name -> OptionType ImplConstInfo) (G : ListType KExpr) ",
                "(rho : ListType Nat) (nm : Name) (us : ListType Level) (ci : ImplConstInfo), ",
                "(forall (nm2 : Name) (us2 : ListType Level) (ci2 : ImplConstInfo), ",
                "Eq (OptionType ImplConstInfo) (tenv1 nm2) (OptionType.some ImplConstInfo ci2) -> ",
                "Eq (OptionType KExpr) (tenv2 nm2) (OptionType.some KExpr ",
                "(to_kexpr (impl_inst_levels (impl_const_lps ci2) us2 (impl_const_type ci2)) rho))) -> ",
                "Eq (OptionType ImplConstInfo) (tenv1 nm) (OptionType.some ImplConstInfo ci) -> ",
                "KernelInfers tenv2 G (to_kexpr (ImplExpr.const nm us) rho) ",
                "(to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv2 : Name -> OptionType KExpr) ",
                    "(tenv1 : Name -> OptionType ImplConstInfo) (G : ListType KExpr) ",
                    "(rho : ListType Nat) (nm : Name) (us : ListType Level) (ci : ImplConstInfo) ",
                    "(henv : forall (nm2 : Name) (us2 : ListType Level) (ci2 : ImplConstInfo), ",
                    "Eq (OptionType ImplConstInfo) (tenv1 nm2) (OptionType.some ImplConstInfo ci2) -> ",
                    "Eq (OptionType KExpr) (tenv2 nm2) (OptionType.some KExpr ",
                    "(to_kexpr (impl_inst_levels (impl_const_lps ci2) us2 (impl_const_type ci2)) rho))) ",
                    "(hget : Eq (OptionType ImplConstInfo) (tenv1 nm) ",
                    "(OptionType.some ImplConstInfo ci)) => ",
                    "KernelInfers.const tenv2 G nm us ",
                    "(to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho) ",
                    "(henv nm us ci hget)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, const rule (ImplInfer.const, tc/infer.rs:371-424). The two layers hold ",
                "DIFFERENT environments — layer 1 maps a name to an ImplConstInfo record and ",
                "instantiates universe parameters at the use site, layer 2 maps a name straight ",
                "to a KExpr and ignores the level list — so the bridge carries an explicit ",
                "environment-correspondence hypothesis, spelled inline because it must ",
                "quantify over the per-node universe-instantiation list. Measured asymmetry ",
                "recorded rather than assumed away: the release arm's level-arity check, ",
                "per-level check_level and unsafe/partial gates (tc/infer.rs:383,397-404) have ",
                "NO counterpart in KernelInfers.const, whose only premise is the lookup. ",
                "Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers".to_string(),
                "to_kexpr".to_string(),
                "impl_inst_levels".to_string(),
                "impl_const_lps".to_string(),
                "impl_const_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── app ─────────────────────────────────────────────────────────────
        // The arm that matches its layer-2 counterpart premise for premise:
        // KernelInfers.app carries whnf_to and DefEq as WITNESSED fields, which
        // is exactly what ImplInfer.app supplies. Nothing is dropped here.
        //
        // The three forall-premises are the M4 lemmas impl_whnf_to_whnf_to /
        // impl_is_le_defeq / to_kexpr_at_instantiate stated as hypotheses,
        // because add_impl_infer_sound runs AFTER add_ctx_rep (bundles.rs) and
        // nothing it registers is in scope here. Carrying them is route (A):
        // the rule lands at this stage with a self-contained proof, and the M4
        // stage discharges them (impl_kinfers_app is the unconditional form).
        self.add_definition(SpecDefinition {
            name: "impl_bridge_app".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ",
                "ListType Nat) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) (bd : ",
                "BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr), (forall (rho2 : ",
                "ListType Nat) (e2 : ImplExpr) (r2 : ImplExpr), ImplWhnfTo e2 r2 -> is_whnf ",
                "(to_kexpr r2 rho2) -> whnf_to (to_kexpr e2 rho2) (to_kexpr r2 rho2)) -> ",
                "(forall (rho2 : ListType Nat) (x2 : ImplExpr) (y2 : ImplExpr), ImplIsLe x2 ",
                "y2 -> DefEq (to_kexpr x2 rho2) (to_kexpr y2 rho2)) -> (forall (rho2 : ",
                "ListType Nat) (v2 : ImplExpr) (b2 : ImplExpr) (d2 : Nat), Eq KExpr ",
                "(to_kexpr_at (impl_instantiate_at b2 v2 d2) rho2 d2) (instantiate_at ",
                "(to_kexpr_at b2 rho2 (Nat.succ d2)) (to_kexpr_at v2 rho2 Nat.zero) d2)) -> ",
                "KernelInfers tenv G (to_kexpr f rho) (to_kexpr F rho) -> ImplWhnfTo F ",
                "(ImplExpr.pi bd A B) -> KernelInfers tenv G (to_kexpr a rho) (to_kexpr A2 ",
                "rho) -> ImplIsLe A2 A -> KernelInfers tenv G (to_kexpr (ImplExpr.app f a) ",
                "rho) (to_kexpr (impl_instantiate B a) rho)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ListType ",
                    "Nat) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) (bd : BinderData) (A : ",
                    "ImplExpr) (B : ImplExpr) (A2 : ImplExpr) (hwt : forall (rho2 : ListType ",
                    "Nat) (e2 : ImplExpr) (r2 : ImplExpr), ImplWhnfTo e2 r2 -> is_whnf (to_kexpr ",
                    "r2 rho2) -> whnf_to (to_kexpr e2 rho2) (to_kexpr r2 rho2)) (hcl : forall ",
                    "(rho2 : ListType Nat) (x2 : ImplExpr) (y2 : ImplExpr), ImplIsLe x2 y2 -> ",
                    "DefEq (to_kexpr x2 rho2) (to_kexpr y2 rho2)) (hsub : forall (rho2 : ",
                    "ListType Nat) (v2 : ImplExpr) (b2 : ImplExpr) (d2 : Nat), Eq KExpr ",
                    "(to_kexpr_at (impl_instantiate_at b2 v2 d2) rho2 d2) (instantiate_at ",
                    "(to_kexpr_at b2 rho2 (Nat.succ d2)) (to_kexpr_at v2 rho2 Nat.zero) d2)) (hf ",
                    ": KernelInfers tenv G (to_kexpr f rho) (to_kexpr F rho)) (hw : ImplWhnfTo F ",
                    "(ImplExpr.pi bd A B)) (ha : KernelInfers tenv G (to_kexpr a rho) (to_kexpr ",
                    "A2 rho)) (hle : ImplIsLe A2 A) => Eq.substType KExpr (fun (w : KExpr) => ",
                    "KernelInfers tenv G (KExpr.app (to_kexpr_at f rho Nat.zero) (to_kexpr_at a ",
                    "rho Nat.zero)) w) (instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) (to_kexpr (impl_instantiate B a) rho) ",
                    "(Eq.symm KExpr (to_kexpr (impl_instantiate B a) rho) (instantiate ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero)) (to_kexpr_at a rho Nat.zero)) (hsub ",
                    "rho a B Nat.zero)) (KernelInfers.app tenv G (to_kexpr_at f rho Nat.zero) ",
                    "(to_kexpr_at a rho Nat.zero) (to_kexpr F rho) (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero)) (to_kexpr A2 rho) hf (hwt rho F ",
                    "(ImplExpr.pi bd A B) hw (is_whnf.pi (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero)))) ha (hcl rho A2 A hle))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, app rule (ImplInfer.app, tc/infer.rs:426-470). Matches ",
                "KernelInfers.app premise for premise, so NOTHING is dropped: ImplWhnfTo F ",
                "(pi bd A B) becomes whnf_to F (KExpr.pi A B) and ImplIsLe A2 A becomes ",
                "DefEq A2 A, both inside the proof, and both operational premises are copied ",
                "VERBATIM from the layer-1 constructor into the statement. The codomain B is ",
                "translated at depth ONE because it sits under the Pi binder. STAGE-ORDER, ",
                "stated rather than hidden: the three universally quantified premises are ",
                "alpha-for-alpha the statements of impl_whnf_to_whnf_to, impl_is_le_defeq ",
                "and to_kexpr_at_instantiate, which add_impl_infer_sound registers at a ",
                "LATER stage than add_ctx_rep (bundles.rs), so they cannot be called from ",
                "here and are carried as hypotheses instead — the C4 per-rule style, ",
                "self-contained at this stage. The unconditional form, with all three ",
                "discharged, is impl_kinfers_app (impl_infer_sound.rs); ",
                "impl_bridge_app_witness fires THIS rule with the three lemmas supplied. ",
                "Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.app".to_string(),
                "to_kexpr".to_string(),
                "to_kexpr_at".to_string(),
                "impl_instantiate".to_string(),
                "is_whnf.pi".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── lam ─────────────────────────────────────────────────────────────
        // Unblocked by the 2026-08-08 repair to KernelInfers.lam, which now
        // carries `whnf_to SA (KExpr.sort u)` instead of demanding a syntactic
        // sort — the idiom its own let_ arm always used, and the one the
        // deployed ensure_sort (tc/infer.rs:521) actually implements.
        //
        // hopen / habs are to_kexpr_open / to_kexpr_abstract INSTANTIATED at
        // this node, carried as premises for the stage-order reason above.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_lam".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ",
                "ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S ",
                ": ImplExpr) (l : Level) (bt : ImplExpr), KernelInfers tenv G (to_kexpr A ",
                "rho) (to_kexpr S rho) -> whnf_to (to_kexpr S rho) (KExpr.sort l) -> ",
                "KernelInfers tenv (ListType.cons KExpr (to_kexpr A rho) G) (to_kexpr ",
                "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr bt (ListType.cons Nat ",
                "x rho)) -> Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr_at b rho (Nat.succ Nat.zero)) -> Eq KExpr (to_kexpr bt ",
                "(ListType.cons Nat x rho)) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                "(Nat.succ Nat.zero)) -> KernelInfers tenv G (to_kexpr (ImplExpr.lam bd A b) ",
                "rho) (to_kexpr (ImplExpr.pi bd A (impl_abstract_fvar bt x)) rho)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ListType ",
                    "Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S : ",
                    "ImplExpr) (l : Level) (bt : ImplExpr) (ihA : KernelInfers tenv G (to_kexpr ",
                    "A rho) (to_kexpr S rho)) (hsort : whnf_to (to_kexpr S rho) (KExpr.sort l)) ",
                    "(ihb : KernelInfers tenv (ListType.cons KExpr (to_kexpr A rho) G) (to_kexpr ",
                    "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr bt (ListType.cons Nat ",
                    "x rho))) (hopen : Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x ",
                    "rho)) (to_kexpr_at b rho (Nat.succ Nat.zero))) (habs : Eq KExpr (to_kexpr ",
                    "bt (ListType.cons Nat x rho)) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                    "(Nat.succ Nat.zero))) => KernelInfers.lam tenv G (to_kexpr A rho) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) (to_kexpr_at (impl_abstract_fvar bt ",
                    "x) rho (Nat.succ Nat.zero)) (to_kexpr S rho) l ihA hsort (Eq.substType ",
                    "KExpr (fun (w : KExpr) => KernelInfers tenv (ListType.cons KExpr (to_kexpr ",
                    "A rho) G) w (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ ",
                    "Nat.zero))) (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) hopen (Eq.substType KExpr (fun (w : ",
                    "KExpr) => KernelInfers tenv (ListType.cons KExpr (to_kexpr A rho) G) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) w) (to_kexpr bt ",
                    "(ListType.cons Nat x rho)) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                    "(Nat.succ Nat.zero)) habs ihb))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, lam rule (ImplInfer.lam, tc/infer.rs:521-548). The conclusion needs ",
                "NO transport: to_kexpr (lam bd A b) rho iota-reduces to KExpr.lam of the ",
                "two translated components, at depths zero and ONE respectively, which are ",
                "exactly KernelInfers.lam own indices. The only transports are the two ",
                "nested Eq.substType on the BODY premise — subject along hopen, then type ",
                "along habs. No CtxRep premise: the lam arm performs no context lookup, and ",
                "the discipline is that a bridge rule takes CtxRep only if it consumes it; ",
                "the extended layer-2 context and the extended renaming appear only in the ",
                "body IH, in exactly the shape ctx_rep_snoc_fresh produces. The 2026-08-08 ",
                "repair is what makes this arm possible: KernelInfers.lam now carries ",
                "KernelInfers G A SA -> whnf_to SA (sort u), so the domain premise lands as ",
                "itself with no conv step. STAGE-ORDER: the whnf premise is stated in ",
                "layer-2 form, and hopen / habs are carried as explicit equations, because ",
                "impl_whnf_to_whnf_to, to_kexpr_open and to_kexpr_abstract are registered by ",
                "add_impl_infer_sound, a LATER stage than add_ctx_rep. The discharged forms ",
                "live there: impl_kinfers_lam takes the ImplWhnfTo premise verbatim, and ",
                "impl_kinfers_lam_scoped replaces both equations by the scoping invariants ",
                "ImplScoped x b 0 and ImplLC bt 0. Recorded asymmetry: ImplInfer.lam threads ",
                "the next_id counter n -> n1 -> n2 and the LCtx bookkeeping, which have no ",
                "KernelInfers counterpart and are deliberately not carried as dead ",
                "hypotheses. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.lam".to_string(),
                "to_kexpr".to_string(),
                "to_kexpr_at".to_string(),
                "impl_open".to_string(),
                "impl_abstract_fvar".to_string(),
                "whnf_to".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── pi ──────────────────────────────────────────────────────────────
        // Same repair as lam, twice: KernelInfers.pi now carries a whnf_to
        // premise for the domain AND the body. No habs — a Pi result is a sort,
        // so there is nothing to abstract back, which is the one structural
        // difference from the lam and let_ arms.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_pi".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ",
                "ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S1 ",
                ": ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level), KernelInfers tenv Gk ",
                "(to_kexpr A rho) (to_kexpr S1 rho) -> whnf_to (to_kexpr S1 rho) (KExpr.sort ",
                "l1) -> KernelInfers tenv (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) (to_kexpr S2 ",
                "(ListType.cons Nat x rho)) -> whnf_to (to_kexpr S2 (ListType.cons Nat x ",
                "rho)) (KExpr.sort l2) -> Eq KExpr (to_kexpr (impl_open b x) (ListType.cons ",
                "Nat x rho)) (to_kexpr_at b rho (Nat.succ Nat.zero)) -> KernelInfers tenv Gk ",
                "(to_kexpr (ImplExpr.pi bd A b) rho) (to_kexpr (ImplExpr.sort (Level.imax l1 ",
                "l2)) rho)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ListType ",
                    "Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S1 : ",
                    "ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level) (ihA : KernelInfers ",
                    "tenv Gk (to_kexpr A rho) (to_kexpr S1 rho)) (hw1 : whnf_to (to_kexpr S1 ",
                    "rho) (KExpr.sort l1)) (ihb : KernelInfers tenv (ListType.cons KExpr ",
                    "(to_kexpr A rho) Gk) (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr S2 (ListType.cons Nat x rho))) (hw2 : whnf_to (to_kexpr S2 ",
                    "(ListType.cons Nat x rho)) (KExpr.sort l2)) (hopen : Eq KExpr (to_kexpr ",
                    "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr_at b rho (Nat.succ ",
                    "Nat.zero))) => KernelInfers.pi tenv Gk (to_kexpr A rho) (to_kexpr_at b rho ",
                    "(Nat.succ Nat.zero)) (to_kexpr S1 rho) l1 (to_kexpr S2 (ListType.cons Nat x ",
                    "rho)) l2 ihA hw1 (Eq.substType KExpr (fun (w : KExpr) => KernelInfers tenv ",
                    "(ListType.cons KExpr (to_kexpr A rho) Gk) w (to_kexpr S2 (ListType.cons Nat ",
                    "x rho))) (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) (to_kexpr_at ",
                    "b rho (Nat.succ Nat.zero)) hopen ihb) hw2",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, pi rule (ImplInfer.pi, tc/infer.rs:550-580). One Eq.substType, on ",
                "the body premise SUBJECT only: the conclusion needs no transport because ",
                "both indices iota-reduce to KernelInfers.pi own, and — unlike lam and let_ ",
                "— there is no habs, because a Pi result is a SORT and there is nothing to ",
                "abstract back. The body premise type stays at the extended renaming and hw2 ",
                "pins it, which is why KernelInfers.pi unconstrained SB is enough. Both ",
                "ensure_sort calls the deployed arm makes (tc/infer.rs:555 domain, :573 ",
                "body) are modelled: the 2026-08-08 repair gave KernelInfers.pi a whnf_to ",
                "premise for BOTH, and the body one had previously not been modelled at all. ",
                "STAGE-ORDER: the two whnf premises are carried in already-converted layer-2 ",
                "form rather than as ImplWhnfTo, because impl_whnf_to_whnf_to belongs to ",
                "add_impl_infer_sound, a LATER stage. That choice is strictly stronger here ",
                "AND it keeps the witness dischargeable at this stage — ",
                "impl_bridge_pi_witness proves both by whnf_to.refl on is_whnf.sort, by ",
                "computation. The faithful ImplWhnfTo form is impl_bridge_pi_scoped, ",
                "registered at the M4 stage, where the second conversion runs at the ",
                "EXTENDED renaming — which is precisely why impl_whnf_to_whnf_to is stated ",
                "for all rho. Recorded asymmetry: the next_id counter and the LCtx ",
                "bookkeeping have no KernelInfers counterpart and are not carried as dead ",
                "hypotheses. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.pi".to_string(),
                "to_kexpr".to_string(),
                "to_kexpr_at".to_string(),
                "impl_open".to_string(),
                "whnf_to".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── let_ ────────────────────────────────────────────────────────────
        // Two declarations, and the split is load-bearing: only the
        // layer-2-premise CORE admits a fired witness at this stage, because the
        // layer-1 form quantifies over the two M4 soundness lemmas and those are
        // not constructible before add_impl_infer_sound.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_let_core".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ",
                "ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ",
                "ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr), ",
                "KernelInfers tenvK Gk (to_kexpr ty rho) (to_kexpr S rho) -> whnf_to ",
                "(to_kexpr S rho) (KExpr.sort l) -> KernelInfers tenvK Gk (to_kexpr v rho) ",
                "(to_kexpr Tv rho) -> DefEq (to_kexpr Tv rho) (to_kexpr ty rho) -> ",
                "KernelInfers tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) (to_kexpr ",
                "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr bt (ListType.cons Nat ",
                "x rho)) -> Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr_at b rho (Nat.succ Nat.zero)) -> Eq KExpr (to_kexpr bt ",
                "(ListType.cons Nat x rho)) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                "(Nat.succ Nat.zero)) -> Eq KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ ",
                "Nat.zero)) (to_kexpr v rho)) -> KernelInfers tenvK Gk (to_kexpr ",
                "(ImplExpr.let_ nm ty v b) rho) (to_kexpr (impl_subst_fvar bt x v) rho)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ",
                    "ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ",
                    "ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr) (ihty ",
                    ": KernelInfers tenvK Gk (to_kexpr ty rho) (to_kexpr S rho)) (hsort : ",
                    "whnf_to (to_kexpr S rho) (KExpr.sort l)) (ihv : KernelInfers tenvK Gk ",
                    "(to_kexpr v rho) (to_kexpr Tv rho)) (hdef : DefEq (to_kexpr Tv rho) ",
                    "(to_kexpr ty rho)) (ihb : KernelInfers tenvK (ListType.cons KExpr (to_kexpr ",
                    "ty rho) Gk) (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) (to_kexpr ",
                    "bt (ListType.cons Nat x rho))) (hopen : Eq KExpr (to_kexpr (impl_open b x) ",
                    "(ListType.cons Nat x rho)) (to_kexpr_at b rho (Nat.succ Nat.zero))) (habs : ",
                    "Eq KExpr (to_kexpr bt (ListType.cons Nat x rho)) (to_kexpr_at ",
                    "(impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) (hzeta : Eq KExpr ",
                    "(to_kexpr (impl_subst_fvar bt x v) rho) (instantiate (to_kexpr_at ",
                    "(impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) (to_kexpr v rho))) => ",
                    "Eq.substType KExpr (fun (w : KExpr) => KernelInfers tenvK Gk (KExpr.let_ ",
                    "(to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) (to_kexpr_at b ",
                    "rho (Nat.succ Nat.zero))) w) (instantiate (to_kexpr_at (impl_abstract_fvar ",
                    "bt x) rho (Nat.succ Nat.zero)) (to_kexpr v rho)) (to_kexpr (impl_subst_fvar ",
                    "bt x v) rho) (Eq.symm KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                    "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ ",
                    "Nat.zero)) (to_kexpr v rho)) hzeta) (KernelInfers.let_ tenvK Gk (to_kexpr ",
                    "ty rho) (to_kexpr v rho) (to_kexpr_at b rho (Nat.succ Nat.zero)) (to_kexpr ",
                    "S rho) l (to_kexpr Tv rho) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                    "(Nat.succ Nat.zero)) ihty hsort ihv hdef (Eq.substType KExpr (fun (w : ",
                    "KExpr) => KernelInfers tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) w ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) (to_kexpr ",
                    "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr_at b rho (Nat.succ ",
                    "Nat.zero)) hopen (Eq.substType KExpr (fun (w : KExpr) => KernelInfers tenvK ",
                    "(ListType.cons KExpr (to_kexpr ty rho) Gk) (to_kexpr (impl_open b x) ",
                    "(ListType.cons Nat x rho)) w) (to_kexpr bt (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) habs ihb)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, let_ rule (ImplInfer.let_, tc/infer.rs:590-620) — the ",
                "layer-2-premise core, and the form the witness can fire at this stage. ",
                "ctx_rep.rs old coverage row for let_ was stale in BOTH halves and this ",
                "proof demonstrates it: KernelInfers.let_ carries whnf_to Ty (sort u) as a ",
                "witnessed premise, so it does not demand a syntactic sort, and it carries ",
                "DefEq Tv ty, which is exactly the counterpart of ImplIsLe Tv ty. So hsort ",
                "and hdef land AS THEMSELVES with no conv absorber, and this arm needed no ",
                "layer-2 change at all. Three equational premises, and the third is a ",
                "different animal from the other two: hopen and habs relate one operation to ",
                "its own translation, while hzeta relates two GENUINELY DIFFERENT operations ",
                "— layer 1 substitutes a free variable by name (expr/subst.rs, the deployed ",
                "Let arm at tc/infer.rs:614-617), layer 2 instantiates a de Bruijn binder. ",
                "At M4 it is assembled, not induced: Eq.trans of Eq.cong of ",
                "impl_subst_is_abstract_instantiate with to_kexpr_at_instantiate, which ",
                "additionally needs ImplLC v 0 — which is why it is carried here rather than ",
                "proved here. Recorded asymmetry: ImplInfer.let_ threads next_id through ",
                "FOUR values n -> n1 -> n2 -> n3 and fixes the pushed BinderData to ",
                "Default/Many; KernelInfers has no counterpart for either. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.let_".to_string(),
                "to_kexpr".to_string(),
                "to_kexpr_at".to_string(),
                "impl_open".to_string(),
                "impl_abstract_fvar".to_string(),
                "impl_subst_fvar".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_bridge_let".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ",
                "ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ",
                "ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr), ",
                "(forall (rho2 : ListType Nat) (e2 : ImplExpr) (r2 : ImplExpr), ImplWhnfTo ",
                "e2 r2 -> is_whnf (to_kexpr r2 rho2) -> whnf_to (to_kexpr e2 rho2) (to_kexpr ",
                "r2 rho2)) -> (forall (rho2 : ListType Nat) (x2 : ImplExpr) (y2 : ImplExpr), ",
                "ImplIsLe x2 y2 -> DefEq (to_kexpr x2 rho2) (to_kexpr y2 rho2)) -> ",
                "ImplWhnfTo S (ImplExpr.sort l) -> ImplIsLe Tv ty -> KernelInfers tenvK Gk ",
                "(to_kexpr ty rho) (to_kexpr S rho) -> KernelInfers tenvK Gk (to_kexpr v ",
                "rho) (to_kexpr Tv rho) -> KernelInfers tenvK (ListType.cons KExpr (to_kexpr ",
                "ty rho) Gk) (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) (to_kexpr ",
                "bt (ListType.cons Nat x rho)) -> Eq KExpr (to_kexpr (impl_open b x) ",
                "(ListType.cons Nat x rho)) (to_kexpr_at b rho (Nat.succ Nat.zero)) -> Eq ",
                "KExpr (to_kexpr bt (ListType.cons Nat x rho)) (to_kexpr_at ",
                "(impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) -> Eq KExpr (to_kexpr ",
                "(impl_subst_fvar bt x v) rho) (instantiate (to_kexpr_at (impl_abstract_fvar ",
                "bt x) rho (Nat.succ Nat.zero)) (to_kexpr v rho)) -> KernelInfers tenvK Gk ",
                "(to_kexpr (ImplExpr.let_ nm ty v b) rho) (to_kexpr (impl_subst_fvar bt x v) ",
                "rho)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) (rho : ",
                    "ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ",
                    "ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr) (hwhnf ",
                    ": (forall (rho2 : ListType Nat) (e2 : ImplExpr) (r2 : ImplExpr), ImplWhnfTo ",
                    "e2 r2 -> is_whnf (to_kexpr r2 rho2) -> whnf_to (to_kexpr e2 rho2) (to_kexpr ",
                    "r2 rho2))) (hisle : (forall (rho2 : ListType Nat) (x2 : ImplExpr) (y2 : ",
                    "ImplExpr), ImplIsLe x2 y2 -> DefEq (to_kexpr x2 rho2) (to_kexpr y2 rho2))) ",
                    "(hs : ImplWhnfTo S (ImplExpr.sort l)) (hle : ImplIsLe Tv ty) (ihty : ",
                    "KernelInfers tenvK Gk (to_kexpr ty rho) (to_kexpr S rho)) (ihv : ",
                    "KernelInfers tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho)) (ihb : ",
                    "KernelInfers tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) (to_kexpr ",
                    "(impl_open b x) (ListType.cons Nat x rho)) (to_kexpr bt (ListType.cons Nat ",
                    "x rho))) (hopen : Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x ",
                    "rho)) (to_kexpr_at b rho (Nat.succ Nat.zero))) (habs : Eq KExpr (to_kexpr ",
                    "bt (ListType.cons Nat x rho)) (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                    "(Nat.succ Nat.zero))) (hzeta : Eq KExpr (to_kexpr (impl_subst_fvar bt x v) ",
                    "rho) (instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ ",
                    "Nat.zero)) (to_kexpr v rho))) => impl_bridge_let_core tenvK Gk rho x nm ty ",
                    "v b S l Tv bt ihty (hwhnf rho S (ImplExpr.sort l) hs (is_whnf.sort l)) ihv ",
                    "(hisle rho Tv ty hle) ihb hopen habs hzeta",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "BRIDGE, let_ rule in the FAITHFUL form: the operational premises are copied ",
                "verbatim from ImplInfer.let_ (ImplWhnfTo S (sort l) and ImplIsLe Tv ty) and ",
                "converted inside the proof, exactly as the template requires. The two ",
                "forall-premises that do the converting are byte-identical to ",
                "impl_whnf_to_whnf_to and impl_is_le_defeq (modulo binder renaming to avoid ",
                "capture), which add_impl_infer_sound registers at a LATER stage than ",
                "add_ctx_rep — so they are carried as hypotheses and discharged by passing ",
                "those two lemmas at any post-M4 site. impl_whnf_to_whnf_to is_whnf ",
                "obligation is free here: the reduct is literally a sort, so is_whnf.sort ",
                "applies. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_let_core".to_string(),
                "ImplWhnfTo".to_string(),
                "ImplIsLe".to_string(),
                "is_whnf.sort".to_string(),
                "to_kexpr".to_string(),
                "to_kexpr_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── lit — REFUTED, not bridged ──────────────────────────────────────
        // KernelInfers has seven constructors (sort/bvar/pi/lam/const/app/let_)
        // and NONE concludes at a KExpr.lit, while the translation sends
        // ImplExpr.lit through impl_lit_to_kexpr to exactly that head. So there
        // is no bridge to write, and the honest deliverable is the proof of it —
        // the exact dual of impl_infer_bvar_rejects on the layer-1 side.
        //
        // Per the crystal program standing rule 4, a precise "cannot be done
        // because X" with a kernel-checked proof of X is a COMPLETED job, not a
        // gap. The four declarations below are that proof.
        self.add_definition_reducible(SpecDefinition {
            name: "KNotLit".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (x : KExpr) => KExpr.rec (fun (_ : KExpr) => Type) (fun (l : Level) => ",
                    "ImplUnit) (fun (i : Nat) => ImplUnit) (fun (f : KExpr) (a : KExpr) (rf : ",
                    "Type) (ra : Type) => ImplUnit) (fun (ty : KExpr) (b : KExpr) (rt : Type) ",
                    "(rb : Type) => ImplUnit) (fun (ty : KExpr) (b : KExpr) (rt : Type) (rb : ",
                    "Type) => ImplUnit) (fun (nm : Name) (us : ListType Level) => ImplUnit) (fun ",
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (rt : Type) (rv : Type) (rb : Type) => ",
                    "ImplUnit) (fun (s : Name) (i : Nat) (sub : KExpr) (rs : Type) => ImplUnit) ",
                    "(fun (k : Nat) => Empty) x",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible per-shape family for the LITERAL refutation, the layer-2 dual ",
                "of ImplNotBVar: KNotLit e reduces (KExpr.rec on e, nine minors in ",
                "constructor order sort/bvar/app/lam/pi/const/let_/proj/lit) to Empty at a ",
                "lit and to ImplUnit at every other head. Used as the KernelInfers.rec ",
                "motive so index unification happens by REDUCTION rather than injectivity ",
                "plumbing. ImplUnit is the universe adapter and it is forced: Empty is a ",
                "Type, and the spec Eq is Prop-valued, so it cannot be the other ",
                "alternative. ZERO axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "ImplUnit".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "kernelinfers_lit_rejects".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (k : Nat) (T ",
                ": KExpr), KernelInfers tenv G (KExpr.lit k) T -> Empty",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (k : Nat) (T : ",
                    "KExpr) (h : KernelInfers tenv G (KExpr.lit k) T) => KernelInfers.rec tenv ",
                    "(fun (G2 : ListType KExpr) (e2 : KExpr) (T2 : KExpr) (_h : KernelInfers ",
                    "tenv G2 e2 T2) => KNotLit e2) (fun (sG : ListType KExpr) (sn : Level) => ",
                    "ImplUnit.mk) (fun (vG : ListType KExpr) (vi : Nat) (vA : KExpr) (vlk : Eq ",
                    "(OptionType KExpr) (ctx_lookup vG vi) (OptionType.some KExpr vA)) => ",
                    "ImplUnit.mk) (fun (pG : ListType KExpr) (pA : KExpr) (pB : KExpr) (pSA : ",
                    "KExpr) (pn : Level) (pSB : KExpr) (pm : Level) (ph1 : KernelInfers tenv pG ",
                    "pA pSA) (ph2 : whnf_to pSA (KExpr.sort pn)) (ph3 : KernelInfers tenv ",
                    "(ListType.cons KExpr pA pG) pB pSB) (ph4 : whnf_to pSB (KExpr.sort pm)) ",
                    "(pih1 : KNotLit pA) (pih2 : KNotLit pB) => ImplUnit.mk) (fun (lG : ListType ",
                    "KExpr) (lA : KExpr) (lb : KExpr) (lB : KExpr) (lSA : KExpr) (lu : Level) ",
                    "(lh1 : KernelInfers tenv lG lA lSA) (lh2 : whnf_to lSA (KExpr.sort lu)) ",
                    "(lh3 : KernelInfers tenv (ListType.cons KExpr lA lG) lb lB) (lih1 : KNotLit ",
                    "lA) (lih2 : KNotLit lb) => ImplUnit.mk) (fun (cG : ListType KExpr) (cn : ",
                    "Name) (cus : ListType Level) (cA : KExpr) (cget : Eq (OptionType KExpr) ",
                    "(tenv cn) (OptionType.some KExpr cA)) => ImplUnit.mk) (fun (aG : ListType ",
                    "KExpr) (af : KExpr) (aa : KExpr) (aF : KExpr) (aA : KExpr) (aB : KExpr) ",
                    "(aA2 : KExpr) (ah1 : KernelInfers tenv aG af aF) (ah2 : whnf_to aF ",
                    "(KExpr.pi aA aB)) (ah3 : KernelInfers tenv aG aa aA2) (ah4 : DefEq aA2 aA) ",
                    "(aih1 : KNotLit af) (aih2 : KNotLit aa) => ImplUnit.mk) (fun (zG : ListType ",
                    "KExpr) (zty : KExpr) (zv : KExpr) (zb : KExpr) (zTy : KExpr) (zu : Level) ",
                    "(zTv : KExpr) (zB : KExpr) (zh1 : KernelInfers tenv zG zty zTy) (zh2 : ",
                    "whnf_to zTy (KExpr.sort zu)) (zh3 : KernelInfers tenv zG zv zTv) (zh4 : ",
                    "DefEq zTv zty) (zh5 : KernelInfers tenv (ListType.cons KExpr zty zG) zb zB) ",
                    "(zih1 : KNotLit zty) (zih2 : KNotLit zv) (zih3 : KNotLit zb) => ",
                    "ImplUnit.mk) G (KExpr.lit k) T h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "REFUTATION, layer 2: no KernelInfers derivation concludes at a literal. ",
                "Proved from the constructor set by KernelInfers.rec over the KNotLit motive ",
                "— seven minors in declaration order sort/bvar/pi/lam/const/app/let_, tenv ",
                "first because it is a family parameter. Every minor goal iota-reduces to ",
                "ImplUnit because no constructor concludes at a lit head, and the eliminated ",
                "derivation own index reduces the result to Empty. No injectivity and no ",
                "discriminator plumbing, the same shape as impl_infer_bvar_rejects. Zero ",
                "axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.rec".to_string(),
                "KNotLit".to_string(),
                "ImplUnit".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_bridge_lit_refuted".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ",
                "ListType Nat) (lt : ImplLit) (T : KExpr), KernelInfers tenv G (to_kexpr ",
                "(ImplExpr.lit lt) rho) T -> Empty",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (rho : ListType ",
                    "Nat) (lt : ImplLit) (T : KExpr) (h : KernelInfers tenv G (to_kexpr ",
                    "(ImplExpr.lit lt) rho) T) => ImplLit.rec (fun (l : ImplLit) => KernelInfers ",
                    "tenv G (to_kexpr (ImplExpr.lit l) rho) T -> Empty) (fun (k : Nat) (hk : ",
                    "KernelInfers tenv G (to_kexpr (ImplExpr.lit (ImplLit.natVal k)) rho) T) => ",
                    "kernelinfers_lit_rejects tenv G k T hk) (fun (k : Nat) (hk : KernelInfers ",
                    "tenv G (to_kexpr (ImplExpr.lit (ImplLit.strVal k)) rho) T) => ",
                    "kernelinfers_lit_rejects tenv G k T hk) lt h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "REFUTATION at the BRIDGE conclusion shape: no KernelInfers derivation ",
                "exists for the translation of a layer-1 literal, for ANY type and ANY ",
                "renaming. ImplLit.rec splits the two literal kinds only so ",
                "impl_lit_to_kexpr iota-reduces; both arms are the same call. This is where ",
                "the named representation gap recorded on impl_lit_to_kexpr (KExpr.lit is ",
                "Nat-only, ImplLit is Nat or String) becomes provably inert: the refutation ",
                "does not depend on which literal it is. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kernelinfers_lit_rejects".to_string(),
                "ImplLit.rec".to_string(),
                "to_kexpr".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_bridge_lit_unprovable".to_string(),
            type_src: concat!(
                "forall (hyp : forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                "(rho : ListType Nat) (lt : ImplLit), KernelInfers tenv G (to_kexpr ",
                "(ImplExpr.lit lt) rho) (to_kexpr (impl_lit_type lt) rho)), Empty",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (hyp : forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                    "(rho : ListType Nat) (lt : ImplLit), KernelInfers tenv G (to_kexpr ",
                    "(ImplExpr.lit lt) rho) (to_kexpr (impl_lit_type lt) rho)) => ",
                    "impl_bridge_lit_refuted (fun (nm : Name) => OptionType.none KExpr) ",
                    "(ListType.nil KExpr) (ListType.nil Nat) (ImplLit.natVal Nat.zero) (to_kexpr ",
                    "(impl_lit_type (ImplLit.natVal Nat.zero)) (ListType.nil Nat)) (hyp (fun (nm ",
                    ": Name) => OptionType.none KExpr) (ListType.nil KExpr) (ListType.nil Nat) ",
                    "(ImplLit.natVal Nat.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE DECISIVE STATEMENT: the hyp binder is verbatim the type impl_bridge_lit ",
                "WOULD have had under the sort/const template — ImplInfer.lit has zero ",
                "premises and concludes at impl_lit_type lt, so the rule statement is ",
                "exactly this forall-closure — and from it this term produces Empty. ",
                "Registering impl_bridge_lit would therefore make the specification ",
                "inconsistent. That is why the C4 tally is eight bridged plus one REFUTED ",
                "rather than nine, and why ctx_rep_tests asserts the name impl_bridge_lit is ",
                "never minted. THE HONEST RESIDUAL, named not hidden: this says the bridge ",
                "AS STATED INTO KernelInfers is impossible; it does not say the deployed Lit ",
                "arm is unmodelled. tc/infer.rs:647 returns const Nat [] / const String [] ",
                "with zero environment validation and layer 1 models that faithfully. ",
                "Closing the gap for real means ADDING a lit arm to KernelInfers — a ",
                "decision about the metatheory expression calculus, the same class of change ",
                "as the 2026-08-08 whnf_to repair, and not one this lane makes unilaterally. ",
                "Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_lit_refuted".to_string(),
                "impl_lit_type".to_string(),
                "to_kexpr".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Non-vacuity witnesses — every relation and every bridge lemma exercised
    /// on a concrete instance, each discharged by computation.
    fn add_ctx_rep_witnesses(&mut self) -> Result<(), SpecError> {
        let empty_tenv = "(fun (nm : Name) => OptionType.none KExpr)";
        // The layer-1 context the flagship C1 witness builds under its binder:
        // [FVarId 0 : Prop], value-less, Default/Many.
        let d1 = format!(
            "(LCtx.snoc LCtx.nil (LocalDecl.mk Nat.zero (ImplExpr.sort Level.zero) \
             (OptionType.none ImplExpr) {BD}))"
        );
        let g1 = "(ListType.cons KExpr (KExpr.sort Level.zero) (ListType.nil KExpr))";
        let rho1 = "(ListType.cons Nat Nat.zero (ListType.nil Nat))";

        // ── ExprRep is inhabited ────────────────────────────────────────────
        self.add_definition(SpecDefinition {
            name: "expr_rep_sort_witness".to_string(),
            type_src:
                "ExprRep (ListType.nil Nat) (KExpr.sort Level.zero) (ImplExpr.sort Level.zero)"
                    .to_string(),
            value_src: Some("ExprRep.mk (ListType.nil Nat) (ImplExpr.sort Level.zero)".to_string()),
            is_axiom: false,
            description: "Non-vacuity witness for ExprRep: the layer-2 sort represents the \
                          layer-1 sort under the empty renaming. Pure constructor application; \
                          the index matches only because to_kexpr COMPUTES. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ExprRep".to_string(),
                "to_kexpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── CtxRep at the closed top level ──────────────────────────────────
        self.add_definition(SpecDefinition {
            name: "ctx_rep_nil_witness".to_string(),
            type_src: "CtxRep (ListType.nil KExpr) (ListType.nil Nat) LCtx.nil".to_string(),
            value_src: Some("CtxRep.nil".to_string()),
            is_axiom: false,
            description: "Non-vacuity witness for CtxRep at the CLOSED TOP LEVEL — the \
                          configuration a declaration is admitted in (env/decl_add.rs runs \
                          infer_sort / check_type with an empty LocalContext). This is the \
                          left-hand side of the payoff corollary; what is still missing to \
                          reach that corollary is the other eight ImplInfer minors, not this. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["CtxRep".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // ── CtxRep under one binder — the flagship's context ─────────────────
        // Both non-recursive fields are discharged by COMPUTATION:
        //   head : to_kexpr (sort 0) [0] = lift_at (sort 0) 0 1 — both sides
        //          reduce to KExpr.sort Level.zero (sort is a lift leaf);
        //   shift: vacuous, because lctx_lookup LCtx.nil y is none.
        self.add_definition(SpecDefinition {
            name: "ctx_rep_one_witness".to_string(),
            type_src: format!("CtxRep {g1} {rho1} {d1}"),
            value_src: Some(format!(
                "CtxRep.snoc (ListType.nil KExpr) (ListType.nil Nat) LCtx.nil Nat.zero \
                 (KExpr.sort Level.zero) (ImplExpr.sort Level.zero) \
                 (OptionType.none ImplExpr) {BD} \
                 CtxRep.nil \
                 (Eq.refl KExpr (KExpr.sort Level.zero)) \
                 (fun (y : Nat) (Ay : ImplExpr) \
                 (hy : Eq (OptionType ImplExpr) (lctx_lookup LCtx.nil y) \
                 (OptionType.some ImplExpr Ay)) => \
                 Empty.rec (fun (_e : Empty) => Eq KExpr \
                 (to_kexpr Ay (ListType.cons Nat Nat.zero (ListType.nil Nat))) \
                 (lift_at (to_kexpr Ay (ListType.nil Nat)) Nat.zero (Nat.succ Nat.zero))) \
                 (option_none_ne_some_type ImplExpr Ay Empty hy))"
            )),
            is_axiom: false,
            description: "Non-vacuity witness for CtxRep's snoc rule, on EXACTLY the context \
                          implinfer_lam_identity_witness builds under its binder: FVarId 0 : \
                          Prop, opened from BVar(0) as tc/infer.rs:533-548 does. Both fields \
                          are discharged by computation — the head equation because \
                          to_kexpr (sort 0) [0] and lift_at (sort 0) 0 1 both reduce to \
                          KExpr.sort Level.zero, and the freshness field vacuously because \
                          lctx_lookup of the empty context is none. So the relation genuinely \
                          fires on the flagship configuration rather than only in principle. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxRep".to_string(),
                "to_kexpr".to_string(),
                "lift_at".to_string(),
                "lctx_lookup".to_string(),
                "option_none_ne_some_type".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the fvar bridge, fired ──────────────────────────────────────────
        // The layer-2 derivation for the very variable the flagship C1 witness
        // infers with ImplInfer.fvar. Layer 1 said "FVar(0) : Prop by an
        // unlifted LocalContext lookup"; this is the same fact in layer 2's
        // language, produced BY the bridge rather than restated.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_fvar_witness".to_string(),
            type_src: format!(
                "KernelInfers {empty_tenv} {g1} \
                 (to_kexpr (ImplExpr.fvar Nat.zero) {rho1}) \
                 (to_kexpr (ImplExpr.sort Level.zero) {rho1})"
            ),
            value_src: Some(format!(
                "impl_bridge_fvar {empty_tenv} {g1} {rho1} {d1} Nat.zero \
                 (ImplExpr.sort Level.zero) ctx_rep_one_witness \
                 (Eq.refl (OptionType ImplExpr) \
                 (OptionType.some ImplExpr (ImplExpr.sort Level.zero)))"
            )),
            is_axiom: false,
            description: "The fvar bridge FIRED on the flagship configuration: from the \
                          deployed kernel's own LocalContext lookup of FVarId 0 — the lookup \
                          implinfer_lam_identity_witness performs under its binder — the bridge \
                          produces the layer-2 KernelInfers derivation for de Bruijn index 0. \
                          The lookup premise is Eq.refl, i.e. lctx_lookup genuinely computes, \
                          and rho_index genuinely computes the index. This is the C4 claim in \
                          miniature: a contextual variable maps to a successful fvar lookup, \
                          never to the raw-bvar error arm impl_infer_bvar_rejects refutes. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_fvar".to_string(),
                "ctx_rep_one_witness".to_string(),
                "KernelInfers".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the sort bridge, fired ──────────────────────────────────────────
        self.add_definition(SpecDefinition {
            name: "impl_bridge_sort_witness".to_string(),
            type_src: format!(
                "KernelInfers {empty_tenv} (ListType.nil KExpr) \
                 (to_kexpr (ImplExpr.sort Level.zero) (ListType.nil Nat)) \
                 (to_kexpr (ImplExpr.sort (Level.succ Level.zero)) (ListType.nil Nat))"
            ),
            value_src: Some(format!(
                "impl_bridge_sort {empty_tenv} (ListType.nil KExpr) (ListType.nil Nat) Level.zero"
            )),
            is_axiom: false,
            description: "The sort bridge fired at the closed top level: (Prop : Type) in layer \
                          1 becomes (Prop : Type) in layer 2, with the empty renaming — the \
                          configuration in which opening is the identity. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_sort".to_string(),
                "KernelInfers".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the mdata bridge, fired (and composing) ─────────────────────────
        self.add_definition(SpecDefinition {
            name: "impl_bridge_mdata_witness".to_string(),
            type_src: format!(
                "KernelInfers {empty_tenv} (ListType.nil KExpr) \
                 (to_kexpr (ImplExpr.mdata (ImplExpr.sort Level.zero)) (ListType.nil Nat)) \
                 (to_kexpr (ImplExpr.sort (Level.succ Level.zero)) (ListType.nil Nat))"
            ),
            value_src: Some(format!(
                "impl_bridge_mdata {empty_tenv} (ListType.nil KExpr) (ListType.nil Nat) \
                 (ImplExpr.sort Level.zero) (ImplExpr.sort (Level.succ Level.zero)) \
                 impl_bridge_sort_witness"
            )),
            is_axiom: false,
            description: "The mdata bridge fired, consuming impl_bridge_sort_witness — so the \
                          bridge lemmas COMPOSE, and metadata is erased by the translation \
                          exactly as the release MData arm ignores it. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_mdata".to_string(),
                "impl_bridge_sort_witness".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the const bridge, fired with a REAL environment correspondence ──
        // The environment-correspondence premise is discharged by an actual
        // function, not assumed: it recovers the record from the layer-1 lookup
        // by option_some_inj and then computes, so instantiate_level_params and
        // the translation both genuinely reduce.
        let ci0 = "(ImplConstInfo.mk (ListType.nil Name) (ImplExpr.sort Level.zero) Bool.false Bool.false)";
        let tenv1 = format!("(fun (nm : Name) => OptionType.some ImplConstInfo {ci0})");
        let tenv2 = "(fun (nm : Name) => OptionType.some KExpr (KExpr.sort Level.zero))";
        let nil_rho = "(ListType.nil Nat)";
        let henv = format!(
            "(fun (nm2 : Name) (us2 : ListType Level) (ci2 : ImplConstInfo) \
             (hc : Eq (OptionType ImplConstInfo) (OptionType.some ImplConstInfo {ci0}) \
             (OptionType.some ImplConstInfo ci2)) => \
             Eq.substType ImplConstInfo \
             (fun (z : ImplConstInfo) => Eq (OptionType KExpr) \
             (OptionType.some KExpr (KExpr.sort Level.zero)) \
             (OptionType.some KExpr (to_kexpr (impl_inst_levels (impl_const_lps z) us2 \
             (impl_const_type z)) {nil_rho}))) \
             {ci0} ci2 (option_some_inj ImplConstInfo {ci0} ci2 hc) \
             (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))))"
        );
        self.add_definition(SpecDefinition {
            name: "impl_bridge_const_witness".to_string(),
            type_src: format!(
                "KernelInfers {tenv2} (ListType.nil KExpr) \
                 (to_kexpr (ImplExpr.const Name.anonymous (ListType.nil Level)) {nil_rho}) \
                 (to_kexpr (impl_inst_levels (impl_const_lps {ci0}) (ListType.nil Level) \
                 (impl_const_type {ci0})) {nil_rho})"
            ),
            value_src: Some(format!(
                "impl_bridge_const {tenv2} {tenv1} (ListType.nil KExpr) {nil_rho} \
                 Name.anonymous (ListType.nil Level) {ci0} {henv} \
                 (Eq.refl (OptionType ImplConstInfo) (OptionType.some ImplConstInfo {ci0}))"
            )),
            is_axiom: false,
            description: "The const bridge fired with a REAL environment correspondence: the \
                          premise is discharged by an actual function that recovers the \
                          ImplConstInfo record from the layer-1 lookup via option_some_inj and \
                          then computes — so instantiate_level_params_direct and the \
                          translation both genuinely reduce, and the hypothesis is not a \
                          vacuous assumption. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_const".to_string(),
                "option_some_inj".to_string(),
                "Eq.substType".to_string(),
                "impl_inst_levels".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the lam bridge, fired ───────────────────────────────────────────
        // The flagship configuration, and every premise discharged by
        // computation: the two equations are Eq.refl, so open-then-abstract is
        // not assumed to round-trip here, it is observed to.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_lam_witness".to_string(),
            type_src: concat!(
                "KernelInfers (fun (nm : Name) => OptionType.none KExpr) (ListType.nil ",
                "KExpr) (to_kexpr (ImplExpr.lam (BinderData.mk BinderInfo.default ",
                "Multiplicity.many) (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero)) ",
                "(ListType.nil Nat)) (to_kexpr (ImplExpr.pi (BinderData.mk ",
                "BinderInfo.default Multiplicity.many) (ImplExpr.sort Level.zero) ",
                "(ImplExpr.sort Level.zero)) (ListType.nil Nat))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "impl_bridge_lam (fun (nm : Name) => OptionType.none KExpr) (ListType.nil ",
                    "KExpr) (ListType.nil Nat) Nat.zero (BinderData.mk BinderInfo.default ",
                    "Multiplicity.many) (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero) ",
                    "(ImplExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero) ",
                    "(ImplExpr.sort Level.zero) (impl_bridge_sort (fun (nm : Name) => ",
                    "OptionType.none KExpr) (ListType.nil KExpr) (ListType.nil Nat) Level.zero) ",
                    "(whnf_to.refl (KExpr.sort (Level.succ Level.zero)) (is_whnf.sort ",
                    "(Level.succ Level.zero))) impl_bridge_fvar_witness (Eq.refl KExpr ",
                    "(KExpr.bvar Nat.zero)) (Eq.refl KExpr (KExpr.sort Level.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The lam bridge FIRED on exactly the configuration ",
                "implinfer_lam_identity_witness derives (impl_infer_witnesses.rs): the ",
                "identity on Prop, n = 0, fresh id 0, the same BD. It COMPOSES the two ",
                "already-discharged bridge rules — impl_bridge_sort for the domain and ",
                "impl_bridge_fvar_witness, i.e. impl_bridge_fvar over ctx_rep_one_witness, ",
                "for the body — and both equational premises are Eq.refl: the open/abstract ",
                "round trip genuinely COMPUTES at this instance. KExpr.lam and KExpr.pi ",
                "nodes really appear in the produced derivation, so the rule is not ",
                "vacuously satisfiable. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_lam".to_string(),
                "impl_bridge_sort".to_string(),
                "impl_bridge_fvar_witness".to_string(),
                "whnf_to.refl".to_string(),
                "is_whnf.sort".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the pi bridge, fired ────────────────────────────────────────────
        self.add_definition(SpecDefinition {
            name: "impl_bridge_pi_witness".to_string(),
            type_src: concat!(
                "KernelInfers (fun (nm : Name) => OptionType.none KExpr) (ListType.nil ",
                "KExpr) (to_kexpr (ImplExpr.pi (BinderData.mk BinderInfo.default ",
                "Multiplicity.many) (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero)) ",
                "(ListType.nil Nat)) (to_kexpr (ImplExpr.sort (Level.imax (Level.succ ",
                "Level.zero) (Level.succ Level.zero))) (ListType.nil Nat))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "impl_bridge_pi (fun (nm : Name) => OptionType.none KExpr) (ListType.nil ",
                    "KExpr) (ListType.nil Nat) Nat.zero (BinderData.mk BinderInfo.default ",
                    "Multiplicity.many) (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero) ",
                    "(ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.sort (Level.succ ",
                    "Level.zero)) (Level.succ Level.zero) (Level.succ Level.zero) ",
                    "(impl_bridge_sort (fun (nm : Name) => OptionType.none KExpr) (ListType.nil ",
                    "KExpr) (ListType.nil Nat) Level.zero) (whnf_to.refl (KExpr.sort (Level.succ ",
                    "Level.zero)) (is_whnf.sort (Level.succ Level.zero))) (impl_bridge_sort (fun ",
                    "(nm : Name) => OptionType.none KExpr) (ListType.cons KExpr (KExpr.sort ",
                    "Level.zero) (ListType.nil KExpr)) (ListType.cons Nat Nat.zero (ListType.nil ",
                    "Nat)) Level.zero) (whnf_to.refl (KExpr.sort (Level.succ Level.zero)) ",
                    "(is_whnf.sort (Level.succ Level.zero))) (Eq.refl KExpr (KExpr.sort ",
                    "Level.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The pi bridge fired: Prop -> Prop : Sort (imax 1 1) at the closed top ",
                "level, with the body sub-derivation built under the flagship g1 / rho1. ",
                "EVERY premise is discharged by computation — both whnf_to are refl on ",
                "is_whnf.sort because the translated sorts genuinely reduce, and hopen is ",
                "Eq.refl because impl_open (sort 0) 0 and to_kexpr_at (sort 0) nil (succ 0) ",
                "both reduce to KExpr.sort Level.zero. No hypothesis is assumed. Zero ",
                "axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_pi".to_string(),
                "impl_bridge_sort".to_string(),
                "whnf_to.refl".to_string(),
                "is_whnf.sort".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the let_ bridge, fired ──────────────────────────────────────────
        // Fires the CORE, because the layer-1-premise form quantifies over the
        // two M4 soundness lemmas, which cannot be produced at this stage.
        self.add_definition(SpecDefinition {
            name: "impl_bridge_let_witness".to_string(),
            type_src: concat!(
                "KernelInfers (fun (n0 : Name) => OptionType.none KExpr) (ListType.nil ",
                "KExpr) (to_kexpr (ImplExpr.let_ Name.anonymous (ImplExpr.sort (Level.succ ",
                "Level.zero)) (ImplExpr.sort Level.zero) (ImplExpr.bvar Nat.zero)) ",
                "(ListType.nil Nat)) (to_kexpr (impl_subst_fvar (ImplExpr.sort (Level.succ ",
                "Level.zero)) Nat.zero (ImplExpr.sort Level.zero)) (ListType.nil Nat))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "impl_bridge_let_core (fun (n0 : Name) => OptionType.none KExpr) ",
                    "(ListType.nil KExpr) (ListType.nil Nat) Nat.zero Name.anonymous ",
                    "(ImplExpr.sort (Level.succ Level.zero)) (ImplExpr.sort Level.zero) ",
                    "(ImplExpr.bvar Nat.zero) (ImplExpr.sort (Level.succ (Level.succ ",
                    "Level.zero))) (Level.succ (Level.succ Level.zero)) (ImplExpr.sort ",
                    "(Level.succ Level.zero)) (ImplExpr.sort (Level.succ Level.zero)) ",
                    "(impl_bridge_sort (fun (n0 : Name) => OptionType.none KExpr) (ListType.nil ",
                    "KExpr) (ListType.nil Nat) (Level.succ Level.zero)) (whnf_to.refl ",
                    "(KExpr.sort (Level.succ (Level.succ Level.zero))) (is_whnf.sort (Level.succ ",
                    "(Level.succ Level.zero)))) (impl_bridge_sort (fun (n0 : Name) => ",
                    "OptionType.none KExpr) (ListType.nil KExpr) (ListType.nil Nat) Level.zero) ",
                    "(DefEq.refl (KExpr.sort (Level.succ Level.zero))) (KernelInfers.bvar (fun ",
                    "(n0 : Name) => OptionType.none KExpr) (ListType.cons KExpr (KExpr.sort ",
                    "(Level.succ Level.zero)) (ListType.nil KExpr)) Nat.zero (KExpr.sort ",
                    "(Level.succ Level.zero)) (Eq.refl (OptionType KExpr) (ctx_lookup ",
                    "(ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (ListType.nil ",
                    "KExpr)) Nat.zero))) (Eq.refl KExpr (KExpr.bvar Nat.zero)) (Eq.refl KExpr ",
                    "(KExpr.sort (Level.succ Level.zero))) (Eq.refl KExpr (KExpr.sort ",
                    "(Level.succ Level.zero)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The let_ bridge fired: let (X : Type) := Prop in X : Type, at the closed ",
                "top level. All THREE syntactic equations are Eq.refl — discharged by ",
                "computation, not assumption: impl_open (bvar 0) 0 genuinely computes to ",
                "fvar 0, rho_index genuinely computes it back to de Bruijn 0 (Nat.add ",
                "reduces definitionally here because it recurses on its SECOND argument), ",
                "and impl_abstract_fvar / impl_subst_fvar / the layer-2 instantiate agree on ",
                "the nose. The annotation and value sub-derivations are produced BY ",
                "impl_bridge_sort, so the bridge lemmas compose. Zero axiom_deps.",
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_bridge_let_core".to_string(),
                "impl_bridge_sort".to_string(),
                "KernelInfers.bvar".to_string(),
                "DefEq.refl".to_string(),
                "whnf_to.refl".to_string(),
                "is_whnf.sort".to_string(),
                "ctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the closed-level fact the payoff corollary would rest on ────────
        // "At the closed top level, opening is the identity" has a formal
        // content: in the EMPTY LocalContext no fvar lookup can succeed, so no
        // layer-1 derivation there can use the fvar rule at all, and the
        // translation is renaming-independent on the terms that remain.
        self.add_definition(SpecDefinition {
            name: "ctx_rep_nil_lookup_empty".to_string(),
            type_src: concat!(
                "forall (x : Nat) (Ai : ImplExpr) (C : Type), ",
                "Eq (OptionType ImplExpr) (lctx_lookup LCtx.nil x) ",
                "(OptionType.some ImplExpr Ai) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (x : Nat) (Ai : ImplExpr) (C : Type) ",
                    "(h : Eq (OptionType ImplExpr) (lctx_lookup LCtx.nil x) ",
                    "(OptionType.some ImplExpr Ai)) => ",
                    "option_none_ne_some_type ImplExpr Ai C h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The closed-level fact: in the EMPTY LocalContext no FVarId lookup can succeed, ",
                "so at the top level a declaration is admitted in (env/decl_add.rs:829-852, ",
                "empty context) the deployed kernel's fvar arm is unreachable and opening is ",
                "the identity. This is the formal content of the payoff corollary's premise; ",
                "the corollary ITSELF is not reachable at this coverage, because assembling it ",
                "needs ImplInfer.rec and therefore all nine minors, five of which are blocked ",
                "(see the module header). Stated as an honest partial result, not as the ",
                "corollary. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lctx_lookup".to_string(),
                "option_none_ne_some_type".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "ctx_rep_tests.rs"]
mod tests;

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
//! `ImplInfer` has nine rules. **Four are bridged here**: `sort`, `fvar`,
//! `const`, `mdata`. **Five are not**, and the blockers are architectural, not
//! effort.
//!
//! **RE-MEASURED 2026-08-08 — this table was stale in three of its five rows**,
//! and the corrections are inline below. Two rows (`app`, `let_`) named
//! prerequisites that now exist or never actually blocked anything; `let_` in
//! particular needs no layer-2 change at all. The rows that survive are `lam`
//! and `pi`, and they are blocked by ONE omission: `KernelInfers`' `lam`/`pi`
//! arms demand a *syntactic* sort where the deployed body whnf-reduces first —
//! while `KernelInfers`' own `let_` arm already carries `whnf_to Ty (sort u)`
//! as a witnessed premise. So layer 2 already contains the idiom that fixes
//! them; the two arms simply were not written in it. (`lit` remains genuinely
//! unbridgeable: `KernelInfers` has no literal rule to bridge into.)
//!
//! Note also that M4 (`impl_infer_sound.rs`) has since bridged all nine rules
//! into `TypingCtxConv` instead. That is a different codomain, not a
//! replacement for this table: `TypingCtxConv.conv` is unrestricted and its
//! `app`/`let_` arms carry neither the `whnf_to` nor the `DefEq` premise, so it
//! does not pin the returned type or the operational steps. This table is about
//! the `KernelInfers` lane, which is the one that would.
//!
//! | rule | blocker |
//! |---|---|
//! | `lam` | ~~`KernelInfers.lam` demands `KernelInfers G A (KExpr.sort u)` — the domain's inferred type must be SYNTACTICALLY a sort.~~ **REPAIRED 2026-08-08**: `KernelInfers.lam` now carries `KernelInfers G A SA -> whnf_to SA (KExpr.sort u)`, the idiom its own `let_` arm always used, matching the deployed `ensure_sort` at `tc/infer.rs:521`. |
//! | `pi` | ~~Same, twice (`tc/infer.rs:555,573` — both `ensure_sort` calls).~~ **REPAIRED 2026-08-08**: `KernelInfers.pi` now carries a `whnf_to` premise for BOTH the domain (`:555`) and the body (`:573`) — the body check was previously not modelled at all. |
//! | `let_` | ~~Same for the annotation (`tc/infer.rs:594`), plus `ImplIsLe Tv ty` has no `KernelInfers`-side counterpart.~~ **BOTH HALVES FALSE — measured 2026-08-08 against `dependent_sn_richmodel.rs:235`.** `KernelInfers.let_` carries `whnf_to Ty (KExpr.sort u)` as a witnessed premise, so it does NOT demand a syntactic sort; and it carries `DefEq Tv ty`, which is exactly the counterpart of `ImplIsLe Tv ty` (supplied by `impl_is_le_defeq`). This arm needs no layer-2 change at all. |
//! | `app` | Needs `ImplWhnfTo -> whnf_to` and `ImplIsLe -> DefEq` soundness under translation, plus the substitution commutation `to_kexpr_at (impl_instantiate B a) rho 0 = instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) (to_kexpr_at a rho 0)` — note the codomain is translated at depth ONE, since it sits under the Pi binder. **STALE as of 2026-08-08: all three now exist**, in `impl_infer_sound.rs` — `impl_whnf_to_whnf_to`, `impl_is_le_defeq`, `to_kexpr_at_instantiate`. What is left for this arm is the arm lemma itself, not its prerequisites. |
//! | `lit` | `KernelInfers` has **no literal rule at all** (7 constructors: sort/bvar/pi/lam/const/app/let_). There is nothing to bridge INTO. |
//!
//! **The finding that matters** (and it is a finding about layer 2, not about
//! this bridge): `KernelInfers`' `pi`/`lam`/`let_` arms are themselves
//! unfaithful to the deployed body in exactly the `ensure_sort` step. The
//! deployed kernel whnf-reduces before matching; `KernelInfers` matches
//! syntactically. Three of the five blocked rules are blocked by that single
//! omission. The escape route is named and NOT taken here: `TypingCtxConv`
//! (`dependent_sn_richmodel.rs`) carries the CIC `conv` rule, so
//! `ImplInfer -> TypingCtxConv` would absorb every whnf step — and
//! `bootstrap_infer_sound` already lands `KernelInfers` in that same judgment.
//! Retargeting is a decision about which layer-2 relation is the bridge's
//! codomain; it is not made unilaterally here.
//!
//! # The payoff corollary is NOT reachable at this coverage, and why
//!
//! "At the closed top level (`G = nil`, `rho` empty, opening is the identity)
//! the bridge collapses to a statement about closed declarations" requires the
//! GLOBAL theorem, i.e. `ImplInfer.rec` applied to all nine minors. A partial
//! set of minors cannot be assembled — the recursor demands every one. What IS
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

    /// The bridge, rule by rule — four of `ImplInfer`'s nine.
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

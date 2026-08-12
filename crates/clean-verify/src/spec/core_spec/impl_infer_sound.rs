// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! **M4 — `impl_infer_sound`**, the layer-1 soundness theorem
//! (`designs/2026-07-29-unified-implinfer-relation.md` §2, step M4).
//!
//! # What M4 is, and why it is not C4 again
//!
//! C4 (`ctx_rep.rs`) built the representation apparatus and bridged four of
//! `ImplInfer`'s nine rules into `KernelInfers`. It stopped at four, and its
//! module header names the reason precisely: `KernelInfers`' `lam`/`pi`/`let_`
//! arms demand the domain's inferred type be **syntactically** a sort, while
//! the deployed body whnf-reduces first (`ensure_sort`, `tc/infer.rs:521`,
//! `:555`, `:573`, `:594`) — and `KernelInfers` has no conversion rule, so the
//! whnf step cannot be absorbed. Three of the five blocked rules are blocked by
//! that single omission. C4 named the escape route and deliberately declined to
//! take it unilaterally:
//!
//! > `TypingCtxConv` carries the CIC `conv` rule, so `ImplInfer -> TypingCtxConv`
//! > would absorb every whnf step — and `bootstrap_infer_sound` already lands
//! > `KernelInfers` in that same judgment. Retargeting is a decision about which
//! > layer-2 relation is the bridge's codomain; it is not made unilaterally here.
//!
//! **M4 is that decision**, and the design already made it: §2 states the target
//! as `TypingCtxConv (env_of env) (ctx_db G) e_db T_db`, not `KernelInfers`. So
//! this module is not a competing C4 — it is the step C4 was written to hand off
//! to, and it reuses C4's apparatus (`to_kexpr_at`, `CtxRep`, `ctx_rep_lookup`)
//! unchanged rather than re-deriving it.
//!
//! # The dependency spine, and where this increment sits
//!
//! Retargeting alone does not discharge the binder rules. Every one of them
//! needs the translation to commute with the operations the deployed binder arms
//! perform, and those commutation lemmas are the actual bulk the design means by
//! "**real proof**, the bulk". The spine:
//!
//! ```text
//!   to_kexpr_at_lift          <- THIS INCREMENT (the keystone)
//!     |
//!     +-- to_kexpr_at_instantiate      (substitution commutation)
//!           |
//!           +-- impl_whnf_to_defeq     (the `ensure_sort` absorber)
//!           |     |
//!           |     +-- lam / pi / let_ domain premises
//!           +-- impl_is_le_defeq
//!           +-- the app arm's result equation
//! ```
//!
//! `to_kexpr_at_lift` is first because *both* of the other two need it:
//! `instantiate_bvar_geq` substitutes `lift_at val Nat.zero depth`
//! (`expr_model.rs`) and `impl_inst_bvar_geq` substitutes
//! `impl_lift_at val Nat.zero depth` (`impl_infer_syntax.rs`) — so the hit case
//! of the substitution lemma *is* an instance of this one. Landing it separately
//! is not salami-slicing: it is the one lemma with no prerequisites of its own.
//!
//! # Why the cutoff has to be generalised
//!
//! The statement one actually wants is the depth-0 instance, but that instance
//! is **not** provable by induction on its own: under a `lam`/`pi`/`let_` binder
//! the cutoff goes to `Nat.succ k` while the translation depth goes to
//! `Nat.succ (Nat.add k c)`, so the induction hypothesis must be available at
//! every cutoff. Hence the motive quantifies over `k` and the amount `c` and the
//! renaming `rho` stay fixed.
//!
//! The interesting content is entirely in the two variable cases, and they pull
//! in opposite directions:
//!
//! * **`bvar`** — layer 1 and layer 2 run the *same* three-way comparison on
//!   `Nat.sub cutoff idx` (`impl_lift_bvar_at` vs `lift_bvar_at` are transcribed
//!   from each other), so the case split is a single `Nat.rec` on that shared
//!   scrutinee and both branches are `Eq.refl`.
//! * **`fvar`** — layer 1 treats it as a **leaf** (free variables are never
//!   lifted; the deployed `Abstractor` only touches bound ones), while layer 2
//!   has already turned it into `bvar (rho_index + k)`, which is `>= k` and so
//!   *is* lifted. The two agree only because `rho_index + k + c` is what both
//!   sides land on — an arithmetic fact (`nat_add_assoc`), not a structural one.
//!   That asymmetry is the whole reason a translation lemma is needed at all
//!   rather than reusing layer 2's own `lift_at` theory.
//!
//! ZERO new axioms: one valued definition, `DerivedProved`, empty axiom closure.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// `to_kexpr_at (impl_lift_at e k c) rho (k + c)` — the left-hand side, for `e`.
macro_rules! lhs {
    ($e:expr, $k:expr) => {
        concat!(
            "(to_kexpr_at (impl_lift_at ",
            $e,
            " ",
            $k,
            " c) rho (Nat.add ",
            $k,
            " c))"
        )
    };
}

/// `lift_at (to_kexpr_at e rho k) k c` — the right-hand side, for `e`.
macro_rules! rhs {
    ($e:expr, $k:expr) => {
        concat!("(lift_at (to_kexpr_at ", $e, " rho ", $k, ") ", $k, " c)")
    };
}

/// `to_kexpr_at (impl_instantiate_at b a d) rho d` — the left-hand side.
macro_rules! ilhs {
    ($e:expr, $d:expr) => {
        concat!(
            "(to_kexpr_at (impl_instantiate_at ",
            $e,
            " a ",
            $d,
            ") rho ",
            $d,
            ")"
        )
    };
}

/// `instantiate_at (to_kexpr_at b rho (succ d)) (to_kexpr_at a rho 0) d`.
macro_rules! irhs {
    ($e:expr, $d:expr) => {
        concat!(
            "(instantiate_at (to_kexpr_at ",
            $e,
            " rho (Nat.succ ",
            $d,
            ")) ",
            "(to_kexpr_at a rho Nat.zero)",
            " ",
            $d,
            ")"
        )
    };
}

impl Specification {
    /// M4: the commutation lemmas the binder and application rules need.
    pub(super) fn add_impl_infer_sound(&mut self) -> Result<(), SpecError> {
        self.add_to_kexpr_at_lift()?;
        self.add_to_kexpr_at_instantiate()?;
        self.add_operational_boundary_soundness()?;
        self.add_sound_arms()?;
        Ok(())
    }

    /// The `ImplInfer` rules M4's retarget discharges, one lemma per rule.
    ///
    /// Stated in C4's per-rule style — induction hypotheses as explicit
    /// arguments — rather than as `ImplInfer.rec` minors, because the assembled
    /// theorem needs *all nine* minors and `lit` is not among them (see the
    /// module header). A partial set of arms is a real deliverable; a partial
    /// `ImplInfer.rec` is not a term at all.
    fn add_sound_arms(&mut self) -> Result<(), SpecError> {
        // ── app ─────────────────────────────────────────────────────────────
        // ctx_rep.rs's coverage table lists exactly three things this rule needs
        // and closes with "All three are buildable; none exist yet." All three
        // now exist, and this is the rule assembled out of them.
        self.add_definition(SpecDefinition {
            name: "impl_sound_app".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) ",
                "(bd : BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr), ",
                "ImplWhnfTo F (ImplExpr.pi bd A B) -> ImplIsLe A2 A -> ",
                "TypingCtxConv tenvK Gk (to_kexpr f rho) (to_kexpr F rho) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr a rho) (to_kexpr A2 rho) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.app f a) rho) ",
                "(to_kexpr (impl_instantiate B a) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) ",
                    "(bd : BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr) ",
                    "(hw : ImplWhnfTo F (ImplExpr.pi bd A B)) (hle : ImplIsLe A2 A) ",
                    "(ihf : TypingCtxConv tenvK Gk (to_kexpr f rho) (to_kexpr F rho)) ",
                    "(iha : TypingCtxConv tenvK Gk (to_kexpr a rho) (to_kexpr A2 rho)) => ",
                    // The result equation is the LAST step: rewrite the
                    // conclusion's type from layer 2's `instantiate` back to
                    // layer 1's `impl_instantiate`.
                    "Eq.substType KExpr ",
                    "(fun (w : KExpr) => TypingCtxConv tenvK Gk ",
                    "(KExpr.app (to_kexpr_at f rho Nat.zero) (to_kexpr_at a rho Nat.zero)) w) ",
                    "(instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr (impl_instantiate B a) rho) ",
                    "(Eq.symm KExpr (to_kexpr (impl_instantiate B a) rho) ",
                    "(instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho a B Nat.zero)) ",
                    // TypingCtxConv.app, with each premise fixed up by conv.
                    "(TypingCtxConv.app tenvK Gk (to_kexpr f rho) (to_kexpr a rho) ",
                    "(to_kexpr_at A rho Nat.zero) (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    // f : F, and F whnf's to a Pi — THE step KernelInfers could
                    // not take. conv absorbs it.
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr f rho) (to_kexpr F rho) ",
                    "(KExpr.pi (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero))) ihf ",
                    "(impl_whnf_to_defeq rho F (ImplExpr.pi bd A B) hw)) ",
                    // a : A2, and A2 is_le A — the argument ascription.
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr a rho) (to_kexpr A2 rho) ",
                    "(to_kexpr A rho) iha (impl_is_le_defeq rho A2 A hle)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `app` RULE, bridged. ctx_rep.rs's coverage table names exactly three ",
                "things this rule needs — ImplWhnfTo -> whnf soundness, ImplIsLe -> DefEq, and ",
                "the substitution commutation with the codomain translated at depth ONE — and ",
                "closes with \"All three are buildable; none exist yet.\" All three now exist ",
                "(impl_whnf_to_defeq, impl_is_le_defeq, to_kexpr_at_instantiate) and this is the ",
                "rule assembled out of them. ",
                "BOTH conv steps are the retarget earning its keep. The deployed App arm infers ",
                "`f : F`, whnf-reduces F, and only then matches a Pi (tc/infer.rs:438); layer 2 ",
                "must therefore change f's type along a DefEq, which is exactly what ",
                "TypingCtxConv.conv does and exactly what KernelInfers has no rule for. The ",
                "second conv does the same for the argument's `is_le` ascription (:474). ",
                "The result equation is applied LAST, rewriting layer 2's `instantiate` back to ",
                "layer 1's `impl_instantiate` — note the codomain is translated at depth ONE ",
                "because it sits under the Pi binder, which is why the generalised form of the ",
                "substitution lemma was necessary rather than a depth-0 special case. ",
                "Stated with the induction hypotheses as explicit arguments, in C4's per-rule ",
                "style: the assembled theorem needs all nine ImplInfer.rec minors and `lit` is ",
                "not among them, so a partial set of ARMS is a real deliverable where a partial ",
                "recursor application would not even be a term. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.app".to_string(),
                "TypingCtxConv.conv".to_string(),
                "impl_whnf_to_defeq".to_string(),
                "impl_is_le_defeq".to_string(),
                "to_kexpr_at_instantiate".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── sort / const / mdata — the retargeted easy arms ──────────────────
        // C4 proved these against KernelInfers; retargeting them costs one
        // constructor name each. Registered so the retarget's coverage is a
        // fact in the environment rather than a claim in a comment.
        self.add_definition(SpecDefinition {
            name: "impl_sound_sort".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (l : Level), ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.sort l) rho) ",
                "(to_kexpr (ImplExpr.sort (Level.succ l)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (l : Level) => TypingCtxConv.sort tenvK Gk l"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `sort` rule, bridged. Free: the translation commutes with sort ",
                "definitionally, so this is TypingCtxConv.sort applied. Registered rather than ",
                "asserted so the retarget's coverage is checkable. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["TypingCtxConv.sort".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_sound_const".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (nm : Name) (us : ListType Level) (Ak : KExpr), ",
                "Eq (OptionType KExpr) (tenvK nm) (OptionType.some KExpr Ak) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.const nm us) rho) Ak"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (nm : Name) (us : ListType Level) (Ak : KExpr) ",
                    "(hget : Eq (OptionType KExpr) (tenvK nm) (OptionType.some KExpr Ak)) => ",
                    "TypingCtxConv.const tenvK Gk nm us Ak hget"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `const` rule, bridged. The layer-2 environment is consulted directly, ",
                "which is why the conclusion's type is the RAW `Ak` rather than a translation: ",
                "TypingCtxConv.const's environment is `Name -> OptionType KExpr` with NO `us` ",
                "argument, so layer 2 is universe-blind and cannot express a ",
                "universe-instantiated constant type. That gap is layer 2's, is inherited ",
                "unchanged from KernelInfers, and is NOT closed by the retarget — recorded here ",
                "rather than hidden behind a representation hypothesis. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["TypingCtxConv.const".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_sound_mdata".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (e : ImplExpr) (T : ImplExpr), ",
                "TypingCtxConv tenvK Gk (to_kexpr e rho) (to_kexpr T rho) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.mdata e) rho) (to_kexpr T rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (e : ImplExpr) (T : ImplExpr) ",
                    "(ih : TypingCtxConv tenvK Gk (to_kexpr e rho) (to_kexpr T rho)) => ih"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `mdata` rule, bridged. The identity function, because the translation ",
                "ERASES mdata and the deployed MData arm is a pure passthrough ",
                "(tc/infer.rs:657-663). That it type-checks as the identity is the content: it ",
                "says the two erasures agree. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["TypingCtxConv".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_binder_arms()?;
        self.add_scoping()?;
        Ok(())
    }

    /// The scoping relation, and the open commutation it discharges.
    ///
    /// `ImplScoped x e d` says the two things the deployed checker guarantees
    /// at the moment it opens a binder, and nothing else:
    ///
    /// * every loose `bvar` of `e` is `<= d` — the body's only free index is the
    ///   one about to be opened;
    /// * `e` does not mention the `FVarId` `x` — the id is fresh, which
    ///   production guarantees because `next_id` is incremented on every push
    ///   and never rewound and push asserts ids are never reused
    ///   (`tc/local_context.rs:81,86-89,111`).
    ///
    /// **Both are load-bearing and each is separately necessary**, which is why
    /// they live in one relation rather than being waved at:
    ///
    /// * drop the bound and the equation is false at `bvar j`, `j >= 1` —
    ///   `impl_open` decrements the bvars it does not replace, the un-opened
    ///   translation does not;
    /// * drop freshness and it is false at `fvar x` itself — the opened form
    ///   sends it to `bvar d`, the un-opened form to wherever `x` already sits
    ///   in `rho`.
    ///
    /// Registered as an INDUCTIVE rather than a `Bool` predicate on purpose: the
    /// proof then inducts on the derivation, so each constructor hands over its
    /// children's scoping facts directly and no `Bool.and` decomposition
    /// plumbing appears anywhere. Census-neutral (`add_inductive`).
    fn add_scoping(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            concat!(
                "inductive ImplScoped (x : Nat) : ImplExpr -> Nat -> Type\n",
                "| bvar : forall (i : Nat) (d : Nat), Le i d -> ImplScoped x (ImplExpr.bvar i) d\n",
                "| fvar : forall (y : Nat) (d : Nat), Eq Bool (nat_eqb x y) Bool.false -> ImplScoped x (ImplExpr.fvar y) d\n",
                "| sort : forall (l : Level) (d : Nat), ImplScoped x (ImplExpr.sort l) d\n",
                "| const : forall (nm : Name) (us : ListType Level) (d : Nat), ImplScoped x (ImplExpr.const nm us) d\n",
                "| app : forall (f : ImplExpr) (a : ImplExpr) (d : Nat), ImplScoped x f d -> ImplScoped x a d -> ImplScoped x (ImplExpr.app f a) d\n",
                "| lam : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplScoped x ty d -> ImplScoped x b (Nat.succ d) -> ImplScoped x (ImplExpr.lam bd ty b) d\n",
                "| pi : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplScoped x ty d -> ImplScoped x b (Nat.succ d) -> ImplScoped x (ImplExpr.pi bd ty b) d\n",
                "| let_ : forall (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (d : Nat), ImplScoped x ty d -> ImplScoped x v d -> ImplScoped x b (Nat.succ d) -> ImplScoped x (ImplExpr.let_ nm ty v b) d\n",
                "| lit : forall (lt : ImplLit) (d : Nat), ImplScoped x (ImplExpr.lit lt) d\n",
                "| mdata : forall (e : ImplExpr) (d : Nat), ImplScoped x e d -> ImplScoped x (ImplExpr.mdata e) d"
            ),
            "ImplScoped x e d: the layer-1 term e has every loose bvar <= d AND does not \
             mention the FVarId x. These are exactly the two invariants the deployed checker \
             holds when it opens a binder — the body's only free index is the one being \
             opened, and the fresh id is fresh (next_id is incremented on every push and never \
             rewound, tc/local_context.rs:81,111, and push asserts ids are never reused, \
             :86-89). BOTH are separately necessary for the open commutation: without the \
             bound it fails at bvar j for j >= 1 (impl_open decrements the bvars it does not \
             replace); without freshness it fails at fvar x itself (the opened form sends it to \
             bvar d, the un-opened form to wherever x already sits in rho). An INDUCTIVE rather \
             than a Bool predicate so the commutation proof inducts on the DERIVATION and each \
             constructor hands over its children's facts directly — no Bool.and decomposition \
             anywhere. Operational/syntactic only: no constructor field mentions a typing \
             judgment. ZERO new axioms (census-neutral).",
        )?;

        // The open commutation, unconditional given ImplScoped. This is the
        // premise `impl_sound_lam` / `_pi` / `_let` carry.
        self.add_definition(SpecDefinition {
            name: "to_kexpr_open".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (x : Nat) (b : ImplExpr) (d : Nat), ",
                "ImplScoped x b d -> ",
                "Eq KExpr (to_kexpr_at (impl_instantiate_at b (ImplExpr.fvar x) d) ",
                "(ListType.cons Nat x rho) d) ",
                "(to_kexpr_at b rho (Nat.succ d))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (x : Nat) (b : ImplExpr) (d : Nat) ",
                    "(h : ImplScoped x b d) => ",
                    "ImplScoped.rec x ",
                    "(fun (b0 : ImplExpr) (d0 : Nat) (_h0 : ImplScoped x b0 d0) => Eq KExpr ",
                    "(to_kexpr_at (impl_instantiate_at b0 (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at b0 rho (Nat.succ d0))) ",
                    // ── bvar: i <= d, so the substitution either leaves it
                    // alone (i < d) or replaces it with the fresh fvar (i = d).
                    // The i > d branch, the only one that would break, is what
                    // the Le field rules out.
                    "(fun (i : Nat) (d0 : Nat) (hle : Le i d0) => ",
                    "Nat.rec (fun (s : Nat) => Eq Nat (Nat.sub d0 i) s -> Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_inst_bvar_geq i d0 (ImplExpr.fvar x)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) ",
                    "(ListType.cons Nat x rho) d0) (KExpr.bvar i)) ",
                    // s = 0 : i >= d0, and with Le i d0 that means i = d0.
                    "(fun (hz : Eq Nat (Nat.sub d0 i) Nat.zero) => ",
                    // reduce the geq scrutinee Nat.sub i d0 to zero
                    "Eq.substType Nat (fun (t : Nat) => Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_lift_at (ImplExpr.fvar x) Nat.zero d0) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ",
                    "ImplExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) t) ",
                    "(ListType.cons Nat x rho) d0) (KExpr.bvar i)) ",
                    "Nat.zero (Nat.sub i d0) ",
                    "(Eq.symm Nat (Nat.sub i d0) Nat.zero (le_sub_zero i d0 hle)) ",
                    // now: to_kexpr_at (fvar x) (cons x rho) d0 = bvar i.
                    // reduce rho_index (cons x rho) x to zero via nat_eqb_refl
                    "(Eq.substType Bool (fun (bb : Bool) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho x)) Nat.zero bb) d0)) (KExpr.bvar i)) ",
                    "Bool.true (nat_eqb x x) ",
                    "(Eq.symm Bool (nat_eqb x x) Bool.true (nat_eqb_refl x)) ",
                    // bvar (0 + d0) = bvar d0 = bvar i
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add Nat.zero d0) i ",
                    "(Eq.trans Nat (Nat.add Nat.zero d0) d0 i (nat_zero_add d0) ",
                    "(Eq.symm Nat i d0 (nat_sub_zero_eq i d0 hle hz)))))) ",
                    // s = succ _ : i < d0, untouched on both sides.
                    "(fun (_s : Nat) (_ih : Eq Nat (Nat.sub d0 i) _s -> Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_inst_bvar_geq i d0 (ImplExpr.fvar x)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) _s) ",
                    "(ListType.cons Nat x rho) d0) (KExpr.bvar i)) => ",
                    "fun (_hs : Eq Nat (Nat.sub d0 i) (Nat.succ _s)) => ",
                    "Eq.refl KExpr (KExpr.bvar i)) ",
                    "(Nat.sub d0 i) (Eq.refl Nat (Nat.sub d0 i))) ",
                    // ── fvar y, y != x : the renaming shifts by one, and the
                    // extra binder depth shifts by one. Same place.
                    "(fun (y : Nat) (d0 : Nat) (hne : Eq Bool (nat_eqb x y) Bool.false) => ",
                    "Eq.substType Bool (fun (bb : Bool) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho y)) Nat.zero bb) d0)) ",
                    "(KExpr.bvar (Nat.add (rho_index rho y) (Nat.succ d0)))) ",
                    "Bool.false (nat_eqb x y) ",
                    "(Eq.symm Bool (nat_eqb x y) Bool.false hne) ",
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add (Nat.succ (rho_index rho y)) d0) ",
                    "(Nat.add (rho_index rho y) (Nat.succ d0)) ",
                    "(nat_succ_add (rho_index rho y) d0))) ",
                    // ── sort / const ────────────────────────────────────────
                    "(fun (l : Level) (d0 : Nat) => Eq.refl KExpr (KExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d0 : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // ── app ─────────────────────────────────────────────────
                    "(fun (f : ImplExpr) (a : ImplExpr) (d0 : Nat) ",
                    "(_sf : ImplScoped x f d0) (_sa : ImplScoped x a d0) ",
                    "(rf : Eq KExpr (to_kexpr_at (impl_instantiate_at f (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at f rho (Nat.succ d0))) ",
                    "(ra : Eq KExpr (to_kexpr_at (impl_instantiate_at a (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at a rho (Nat.succ d0))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.app (to_kexpr_at (impl_instantiate_at f (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at a (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (to_kexpr_at f rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at a (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (to_kexpr_at f rho (Nat.succ d0)) ",
                    "(to_kexpr_at a rho (Nat.succ d0))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w ",
                    "(to_kexpr_at (impl_instantiate_at a (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0)) ",
                    "(to_kexpr_at (impl_instantiate_at f (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at f rho (Nat.succ d0)) rf) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app ",
                    "(to_kexpr_at f rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at (impl_instantiate_at a (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at a rho (Nat.succ d0)) ra)) ",
                    // ── lam — the IH for the body is already at succ d0, and
                    // both sides step the depth the same way, so there is NO
                    // arithmetic transport here.
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_st : ImplScoped x ty d0) (_sb : ImplScoped x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at ty rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) ",
                    "(Nat.succ d0)) (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.lam (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0))) rb)) ",
                    // ── pi ──────────────────────────────────────────────────
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_st : ImplScoped x ty d0) (_sb : ImplScoped x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at ty rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) ",
                    "(Nat.succ d0)) (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.pi (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0))) rb)) ",
                    // ── let_ ────────────────────────────────────────────────
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_st : ImplScoped x ty d0) (_sv : ImplScoped x vv d0) ",
                    "(_sb : ImplScoped x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at ty rho (Nat.succ d0))) ",
                    "(rv : Eq KExpr (to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at vv rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) ",
                    "(Nat.succ d0)) (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.let_ (to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w ",
                    "(to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at (impl_instantiate_at ty (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) rt) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) w ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at (impl_instantiate_at vv (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at vv rho (Nat.succ d0)) rv) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(to_kexpr_at ty rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at (impl_instantiate_at bb (ImplExpr.fvar x) (Nat.succ d0)) ",
                    "(ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at bb rho (Nat.succ (Nat.succ d0))) rb))) ",
                    // ── lit / mdata ─────────────────────────────────────────
                    "(fun (lt : ImplLit) (d0 : Nat) => ",
                    "ImplLit.rec (fun (z : ImplLit) => Eq KExpr (impl_lit_to_kexpr z) ",
                    "(impl_lit_to_kexpr z)) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) lt) ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_se : ImplScoped x e0 d0) ",
                    "(ri : Eq KExpr (to_kexpr_at (impl_instantiate_at e0 (ImplExpr.fvar x) d0) ",
                    "(ListType.cons Nat x rho) d0) (to_kexpr_at e0 rho (Nat.succ d0))) => ri) ",
                    "b d h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — THE OPEN COMMUTATION, discharged. Opening a binder with a fresh FVarId and ",
                "extending the renaming is the same as translating one binder deeper. This is ",
                "the premise impl_sound_lam / _pi / _let carry, and ctx_rep.rs names its ",
                "prerequisite as \"a locally-closed predicate on ImplExpr plus a ",
                "translation/lift commutation lemma\" — the first build item for extending the ",
                "bridge to the binder rules. ",
                "TWO CASES CARRY EVERYTHING AND EACH USES A DIFFERENT FIELD OF ImplScoped. ",
                "`bvar`: the substitution splits three ways on Nat.sub, and the i > d branch — ",
                "the only one where the two sides disagree — is ruled out by the Le field ",
                "(le_sub_zero). In the remaining i = d branch, Le plus the branch's own equation ",
                "give i = d by nat_sub_zero_eq, and the fresh variable lands on bvar d because ",
                "rho_index puts it at position 0 (nat_eqb_refl) and Nat.add Nat.zero d is d ",
                "(nat_zero_add — NOT definitional, since Nat.add recurses on its second ",
                "argument). `fvar y`: the freshness field gives y != x, so the renaming scan ",
                "steps past the new head and shifts by one, matching the extra binder depth via ",
                "nat_succ_add. Take either field away and the corresponding case is FALSE, not ",
                "merely unprovable. ",
                "The binder arms need no arithmetic transport at all: both sides step the depth ",
                "to Nat.succ d0 identically, so each body IH is its goal on the nose. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplScoped.rec".to_string(),
                "to_kexpr_at".to_string(),
                "impl_instantiate_at".to_string(),
                "le_sub_zero".to_string(),
                "nat_sub_zero_eq".to_string(),
                "nat_eqb_refl".to_string(),
                "nat_zero_add".to_string(),
                "nat_succ_add".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        self.add_sub_zero_lt_succ()?;
        self.add_abstract_commutation()?;
        self.add_impl_lift_lc()?;
        self.add_subst_is_abstract_instantiate()?;
        self.add_ctx_bridge()?;
        self.add_sound_guard()?;
        self.add_assembly()?;
        self.add_sound_witnesses()?;
        Ok(())
    }

    /// `Nat.sub d i = 0 → Lt d (succ i)` — the one ordering bridge the `let_`
    /// chain needs and the arithmetic tower does not already have.
    ///
    /// It has to land in `Lt` (`Type`) rather than `Le` (`Prop`), and that is
    /// forced rather than a preference: `Le` has two constructors, so it is not
    /// a subsingleton and `Le.rec` cannot eliminate into `Type`. Anything that
    /// must *produce* a `Lt` therefore cannot route through `Le`.
    fn add_sub_zero_lt_succ(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "sub_zero_lt_succ".to_string(),
            type_src: concat!(
                "forall (d : Nat) (i : Nat), ",
                "Eq Nat (Nat.sub d i) Nat.zero -> Lt d (Nat.succ i)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (d : Nat) => ",
                    "Nat.rec (fun (d0 : Nat) => forall (i : Nat), ",
                    "Eq Nat (Nat.sub d0 i) Nat.zero -> Lt d0 (Nat.succ i)) ",
                    // d = 0 : 0 < succ i unconditionally.
                    "(fun (i : Nat) (_h : Eq Nat (Nat.sub Nat.zero i) Nat.zero) => ",
                    "Lt.zero_lt_succ i) ",
                    // d = succ d'
                    "(fun (dp : Nat) (ih : forall (i : Nat), ",
                    "Eq Nat (Nat.sub dp i) Nat.zero -> Lt dp (Nat.succ i)) => ",
                    "Nat.rec (fun (i0 : Nat) => ",
                    "Eq Nat (Nat.sub (Nat.succ dp) i0) Nat.zero -> ",
                    "Lt (Nat.succ dp) (Nat.succ i0)) ",
                    // i = 0 : succ dp - 0 = succ dp, so the hypothesis says
                    // succ dp = 0. Absurd, and nat_zero_ne_succ is Type-valued
                    // precisely so it can discharge a Lt goal.
                    "(fun (h0 : Eq Nat (Nat.sub (Nat.succ dp) Nat.zero) Nat.zero) => ",
                    "nat_zero_ne_succ dp (Lt (Nat.succ dp) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat (Nat.succ dp) Nat.zero ",
                    "(Eq.trans Nat (Nat.succ dp) (Nat.sub (Nat.succ dp) Nat.zero) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ dp) Nat.zero) (Nat.succ dp) ",
                    "(nat_sub_zero_right (Nat.succ dp))) h0))) ",
                    // i = succ i' : peel both and recurse.
                    "(fun (ip : Nat) (_ihi : Eq Nat (Nat.sub (Nat.succ dp) ip) Nat.zero -> ",
                    "Lt (Nat.succ dp) (Nat.succ ip)) => ",
                    "fun (hs : Eq Nat (Nat.sub (Nat.succ dp) (Nat.succ ip)) Nat.zero) => ",
                    "Lt.succ_lt_succ dp (Nat.succ ip) ",
                    "(ih ip (Eq.trans Nat (Nat.sub dp ip) ",
                    "(Nat.sub (Nat.succ dp) (Nat.succ ip)) Nat.zero ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ dp) (Nat.succ ip)) (Nat.sub dp ip) ",
                    "(nat_sub_succ_succ dp ip)) hs)))) ",
                    "d"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "d - i = 0 implies d < i + 1. The one ordering bridge M4's let_ chain needs and ",
                "the existing arithmetic tower does not have. ",
                "IT MUST LAND IN Lt (Type), NOT Le (Prop), and that is forced: Le has two ",
                "constructors, so it is not a subsingleton and Le.rec cannot eliminate into ",
                "Type. Anything that must PRODUCE a Lt — as impl_lift_lc and the abstract ",
                "commutation's bvar case do — cannot route through Le at all. ",
                "Double Nat.rec with the query generalised. The i = 0 case is the interesting ",
                "one: `Nat.sub (succ dp) Nat.zero` is `succ dp` (nat_sub_zero_right, ",
                "propositional — Nat.sub does not reduce on a zero SUBTRAHEND), so the ",
                "hypothesis says succ dp = 0 and nat_zero_ne_succ discharges it. That ",
                "eliminator is Type-valued for exactly this reason. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt.zero_lt_succ".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "nat_zero_ne_succ".to_string(),
                "nat_sub_zero_right".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Lifting is the identity on a term whose loose bvars are all below the
    /// cutoff — the fact the `let_` chain's `fvar` case turns on.
    ///
    /// `impl_subst_fvar` inserts the value **raw** (no shifting, by design —
    /// `expr/subst.rs:1162`), while abstract-then-instantiate inserts
    /// `impl_lift_at v Nat.zero d`. The two agree exactly when that lift does
    /// nothing, which is what this says.
    fn add_impl_lift_lc(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "impl_lift_lc".to_string(),
            type_src: concat!(
                "forall (e : ImplExpr) (d : Nat), ImplLC e d -> ",
                "forall (c : Nat), Le d c -> forall (amount : Nat), ",
                "Eq ImplExpr (impl_lift_at e c amount) e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : ImplExpr) (d : Nat) (h : ImplLC e d) => ",
                    "ImplLC.rec ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_h0 : ImplLC e0 d0) => ",
                    "forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at e0 c amount) e0) ",
                    // bvar : i < d <= c, so the cutoff test keeps it.
                    "(fun (i : Nat) (d0 : Nat) (hlt : Lt i d0) => ",
                    "fun (c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.substType Nat (fun (s : Nat) => Eq ImplExpr ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.add i amount)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) (ImplExpr.bvar i)) ",
                    "(Nat.succ (Nat.sub (Nat.sub c i) (Nat.succ Nat.zero))) (Nat.sub c i) ",
                    "(Eq.symm Nat (Nat.sub c i) ",
                    "(Nat.succ (Nat.sub (Nat.sub c i) (Nat.succ Nat.zero))) ",
                    "(lt_sub_succ i c (lt_of_lt_of_le i d0 c hlt hle))) ",
                    "(Eq.refl ImplExpr (ImplExpr.bvar i))) ",
                    // fvar / sort / const : leaves the lift never touches.
                    "(fun (y : Nat) (d0 : Nat) (c : Nat) (_hle : Le d0 c) (amount : Nat) => ",
                    "Eq.refl ImplExpr (ImplExpr.fvar y)) ",
                    "(fun (l : Level) (d0 : Nat) (c : Nat) (_hle : Le d0 c) (amount : Nat) => ",
                    "Eq.refl ImplExpr (ImplExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d0 : Nat) (c : Nat) ",
                    "(_hle : Le d0 c) (amount : Nat) => ",
                    "Eq.refl ImplExpr (ImplExpr.const nm us)) ",
                    // app
                    "(fun (f : ImplExpr) (a : ImplExpr) (d0 : Nat) ",
                    "(_lf : ImplLC f d0) (_la : ImplLC a d0) ",
                    "(rf : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at f c amount) f) ",
                    "(ra : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at a c amount) a) ",
                    "(c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.app (impl_lift_at f c amount) (impl_lift_at a c amount)) ",
                    "(ImplExpr.app f (impl_lift_at a c amount)) (ImplExpr.app f a) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.app w (impl_lift_at a c amount)) ",
                    "(impl_lift_at f c amount) f (rf c hle amount)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.app f w) ",
                    "(impl_lift_at a c amount) a (ra c hle amount))) ",
                    // lam : the body's cutoff steps to succ c, and its bound to
                    // succ d0 — le_succ_succ carries the hypothesis across.
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at ty c amount) ty) ",
                    "(rb : forall (c : Nat), Le (Nat.succ d0) c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at bb c amount) bb) ",
                    "(c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.lam bd (impl_lift_at ty c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.lam bd ty (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.lam bd ty bb) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.lam bd w (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(impl_lift_at ty c amount) ty (rt c hle amount)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.lam bd ty w) ",
                    "(impl_lift_at bb (Nat.succ c) amount) bb ",
                    "(rb (Nat.succ c) (le_succ_succ d0 c hle) amount))) ",
                    // pi
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at ty c amount) ty) ",
                    "(rb : forall (c : Nat), Le (Nat.succ d0) c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at bb c amount) bb) ",
                    "(c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.pi bd (impl_lift_at ty c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.pi bd ty (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.pi bd ty bb) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.pi bd w (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(impl_lift_at ty c amount) ty (rt c hle amount)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.pi bd ty w) ",
                    "(impl_lift_at bb (Nat.succ c) amount) bb ",
                    "(rb (Nat.succ c) (le_succ_succ d0 c hle) amount))) ",
                    // let_
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lv : ImplLC vv d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at ty c amount) ty) ",
                    "(rv : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at vv c amount) vv) ",
                    "(rb : forall (c : Nat), Le (Nat.succ d0) c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at bb c amount) bb) ",
                    "(c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.let_ nm (impl_lift_at ty c amount) (impl_lift_at vv c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.let_ nm ty (impl_lift_at vv c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.let_ nm ty vv bb) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.let_ nm w (impl_lift_at vv c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(impl_lift_at ty c amount) ty (rt c hle amount)) ",
                    "(Eq.trans ImplExpr ",
                    "(ImplExpr.let_ nm ty (impl_lift_at vv c amount) ",
                    "(impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.let_ nm ty vv (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(ImplExpr.let_ nm ty vv bb) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.let_ nm ty w (impl_lift_at bb (Nat.succ c) amount)) ",
                    "(impl_lift_at vv c amount) vv (rv c hle amount)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.let_ nm ty vv w) ",
                    "(impl_lift_at bb (Nat.succ c) amount) bb ",
                    "(rb (Nat.succ c) (le_succ_succ d0 c hle) amount)))) ",
                    // lit / mdata
                    "(fun (lt : ImplLit) (d0 : Nat) (c : Nat) (_hle : Le d0 c) (amount : Nat) => ",
                    "Eq.refl ImplExpr (ImplExpr.lit lt)) ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_le : ImplLC e0 d0) ",
                    "(ri : forall (c : Nat), Le d0 c -> forall (amount : Nat), ",
                    "Eq ImplExpr (impl_lift_at e0 c amount) e0) ",
                    "(c : Nat) (hle : Le d0 c) (amount : Nat) => ",
                    "Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.mdata w) ",
                    "(impl_lift_at e0 c amount) e0 (ri c hle amount)) ",
                    "e d h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lifting is the IDENTITY on a term whose loose bvars all sit below the cutoff. ",
                "This is the fact M4's let_ chain turns on: impl_subst_fvar inserts the value ",
                "RAW — no shifting, by design (expr/subst.rs:1162, and its registration says so) ",
                "— while abstract-then-instantiate inserts `impl_lift_at v Nat.zero d`. The two ",
                "agree exactly when that lift does nothing. ",
                "The cutoff and the bound are SEPARATE parameters related by Le, not identified, ",
                "because they move together but are not the same thing: under a binder the ",
                "cutoff steps to `succ c` and the bound to `succ d0`, and le_succ_succ carries ",
                "the hypothesis across. Identifying them would make the binder cases unprovable. ",
                "The bvar case composes lt_of_lt_of_le (i < d0 <= c) with lt_sub_succ to put the ",
                "cutoff test in its keep branch. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplLC.rec".to_string(),
                "impl_lift_at".to_string(),
                "lt_of_lt_of_le".to_string(),
                "lt_sub_succ".to_string(),
                "le_succ_succ".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// `impl_subst_fvar bt x v = impl_instantiate_at (impl_abstract_at bt x d) v d`
    /// — the `let_` rule's zeta equation, reduced to pure layer 1.
    ///
    /// The reduction is the point. Composing `to_kexpr_abstract` with
    /// `to_kexpr_at_instantiate` makes the **translation cancel out entirely**,
    /// so `let_`'s remaining obligation is not a statement about `to_kexpr` at
    /// all — it is the classical fact that substituting a free variable *is*
    /// abstract-then-instantiate. No new translation reasoning is required.
    ///
    /// Needs no scoping on `bt`: the `bvar` case works at every index, because
    /// abstraction's shift-up and instantiation's shift-down are inverse on the
    /// nose. The only hypothesis is on the *value* — `impl_subst_fvar` inserts
    /// it raw while the composite inserts `impl_lift_at v 0 d`, so `v` must be
    /// locally closed for those to agree.
    fn add_subst_is_abstract_instantiate(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "impl_subst_is_abstract_instantiate".to_string(),
            type_src: concat!(
                "forall (v : ImplExpr), ImplLC v Nat.zero -> ",
                "forall (x : Nat) (bt : ImplExpr) (d : Nat), ",
                "Eq ImplExpr (impl_subst_fvar bt x v) ",
                "(impl_instantiate_at (impl_abstract_at bt x d) v d)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (v : ImplExpr) (hlc : ImplLC v Nat.zero) (x : Nat) (bt : ImplExpr) => ",
                    "ImplExpr.rec ",
                    "(fun (z : ImplExpr) => forall (d : Nat), Eq ImplExpr ",
                    "(impl_subst_fvar z x v) ",
                    "(impl_instantiate_at (impl_abstract_at z x d) v d)) ",
                    // ── bvar — abstraction's shift-up and instantiation's
                    // shift-down cancel at EVERY index, so no scoping on bt.
                    "(fun (i : Nat) (d : Nat) => ",
                    "Nat.rec (fun (s : Nat) => Eq Nat (Nat.sub d i) s -> Eq ImplExpr ",
                    "(ImplExpr.bvar i) ",
                    "(impl_instantiate_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.succ i)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) v d)) ",
                    // s = 0 : i >= d, so abstraction bumped it to succ i and
                    // instantiation must bring it back down.
                    "(fun (hz : Eq Nat (Nat.sub d i) Nat.zero) => ",
                    "Eq.substType Nat (fun (t : Nat) => Eq ImplExpr (ImplExpr.bvar i) ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_inst_bvar_geq (Nat.succ i) d v) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar (Nat.succ i)) t)) ",
                    "Nat.zero (Nat.sub d (Nat.succ i)) ",
                    "(Eq.symm Nat (Nat.sub d (Nat.succ i)) Nat.zero ",
                    "(nat_sub_zero_implies_sub_succ_zero d i hz)) ",
                    "(Eq.substType Nat (fun (u : Nat) => Eq ImplExpr (ImplExpr.bvar i) ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) (impl_lift_at v Nat.zero d) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ",
                    "ImplExpr.bvar (Nat.sub (Nat.succ i) (Nat.succ Nat.zero))) u)) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ i) d) (Nat.succ Nat.zero))) ",
                    "(Nat.sub (Nat.succ i) d) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ i) d) ",
                    "(Nat.succ (Nat.sub (Nat.sub (Nat.succ i) d) (Nat.succ Nat.zero))) ",
                    "(lt_sub_succ d (Nat.succ i) (sub_zero_lt_succ d i hz))) ",
                    "(Eq.cong Nat ImplExpr (fun (w : Nat) => ImplExpr.bvar w) ",
                    "i (Nat.sub (Nat.succ i) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ i) (Nat.succ Nat.zero)) i ",
                    "(nat_sub_succ_one i))))) ",
                    // s = succ : i < d, so abstraction left it alone and so
                    // does instantiation — the SAME scrutinee decides both.
                    "(fun (sp : Nat) (_ihs : Eq Nat (Nat.sub d i) sp -> Eq ImplExpr ",
                    "(ImplExpr.bvar i) ",
                    "(impl_instantiate_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.succ i)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) sp) v d)) => ",
                    "fun (hs : Eq Nat (Nat.sub d i) (Nat.succ sp)) => ",
                    "Eq.substType Nat (fun (t : Nat) => Eq ImplExpr (ImplExpr.bvar i) ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) (impl_inst_bvar_geq i d v) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) t)) ",
                    "(Nat.succ sp) (Nat.sub d i) ",
                    "(Eq.symm Nat (Nat.sub d i) (Nat.succ sp) hs) ",
                    "(Eq.refl ImplExpr (ImplExpr.bvar i))) ",
                    "(Nat.sub d i) (Eq.refl Nat (Nat.sub d i))) ",
                    // ── fvar — BOTH sides scrutinise the same nat_eqb y x, so
                    // one Bool.rec with it abstracted in both places.
                    "(fun (y : Nat) (d : Nat) => ",
                    "Bool.rec (fun (bb : Bool) => Eq Bool (nat_eqb y x) bb -> Eq ImplExpr ",
                    "(Bool.rec (fun (_c : Bool) => ImplExpr) (ImplExpr.fvar y) v bb) ",
                    "(impl_instantiate_at (Bool.rec (fun (_c : Bool) => ImplExpr) ",
                    "(ImplExpr.fvar y) (ImplExpr.bvar d) bb) v d)) ",
                    // bb = false : untouched on both sides.
                    "(fun (_hf : Eq Bool (nat_eqb y x) Bool.false) => ",
                    "Eq.refl ImplExpr (ImplExpr.fvar y)) ",
                    // bb = true : abstraction put a bvar d here, and
                    // instantiating at depth d substitutes the LIFTED value —
                    // which is v itself, by impl_lift_lc.
                    "(fun (_ht : Eq Bool (nat_eqb y x) Bool.true) => ",
                    "Eq.substType Nat (fun (t : Nat) => Eq ImplExpr v ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) (impl_inst_bvar_geq d d v) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar d) t)) ",
                    "Nat.zero (Nat.sub d d) ",
                    "(Eq.symm Nat (Nat.sub d d) Nat.zero (nat_sub_self d)) ",
                    "(Eq.substType Nat (fun (u : Nat) => Eq ImplExpr v ",
                    "(Nat.rec (fun (_m : Nat) => ImplExpr) (impl_lift_at v Nat.zero d) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ",
                    "ImplExpr.bvar (Nat.sub d (Nat.succ Nat.zero))) u)) ",
                    "Nat.zero (Nat.sub d d) ",
                    "(Eq.symm Nat (Nat.sub d d) Nat.zero (nat_sub_self d)) ",
                    "(Eq.symm ImplExpr (impl_lift_at v Nat.zero d) v ",
                    "(impl_lift_lc v Nat.zero hlc Nat.zero (Le.refl Nat.zero) d)))) ",
                    "(nat_eqb y x) (Eq.refl Bool (nat_eqb y x))) ",
                    // ── sort / const ────────────────────────────────────────
                    "(fun (l : Level) (d : Nat) => Eq.refl ImplExpr (ImplExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d : Nat) => ",
                    "Eq.refl ImplExpr (ImplExpr.const nm us)) ",
                    // ── app ─────────────────────────────────────────────────
                    "(fun (f : ImplExpr) (a : ImplExpr) ",
                    "(rf : forall (d : Nat), Eq ImplExpr (impl_subst_fvar f x v) ",
                    "(impl_instantiate_at (impl_abstract_at f x d) v d)) ",
                    "(ra : forall (d : Nat), Eq ImplExpr (impl_subst_fvar a x v) ",
                    "(impl_instantiate_at (impl_abstract_at a x d) v d)) (d : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.app (impl_subst_fvar f x v) (impl_subst_fvar a x v)) ",
                    "(ImplExpr.app (impl_instantiate_at (impl_abstract_at f x d) v d) ",
                    "(impl_subst_fvar a x v)) ",
                    "(ImplExpr.app (impl_instantiate_at (impl_abstract_at f x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at a x d) v d)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.app w (impl_subst_fvar a x v)) ",
                    "(impl_subst_fvar f x v) ",
                    "(impl_instantiate_at (impl_abstract_at f x d) v d) (rf d)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.app (impl_instantiate_at (impl_abstract_at f x d) v d) w) ",
                    "(impl_subst_fvar a x v) ",
                    "(impl_instantiate_at (impl_abstract_at a x d) v d) (ra d))) ",
                    // ── lam — impl_subst_fvar has NO depth, so the body's IH
                    // is used at succ d while the LHS is unchanged. That is
                    // exactly why the statement generalises over d.
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq ImplExpr (impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d)) ",
                    "(rb : forall (d : Nat), Eq ImplExpr (impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x d) v d)) (d : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.lam bd (impl_subst_fvar ty x v) (impl_subst_fvar bb x v)) ",
                    "(ImplExpr.lam bd (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_subst_fvar bb x v)) ",
                    "(ImplExpr.lam bd (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d))) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.lam bd w (impl_subst_fvar bb x v)) ",
                    "(impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) (rt d)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.lam bd ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) w) ",
                    "(impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d)) ",
                    "(rb (Nat.succ d)))) ",
                    // ── pi ──────────────────────────────────────────────────
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq ImplExpr (impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d)) ",
                    "(rb : forall (d : Nat), Eq ImplExpr (impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x d) v d)) (d : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.pi bd (impl_subst_fvar ty x v) (impl_subst_fvar bb x v)) ",
                    "(ImplExpr.pi bd (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_subst_fvar bb x v)) ",
                    "(ImplExpr.pi bd (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d))) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.pi bd w (impl_subst_fvar bb x v)) ",
                    "(impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) (rt d)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.pi bd ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) w) ",
                    "(impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d)) ",
                    "(rb (Nat.succ d)))) ",
                    // ── let_ ────────────────────────────────────────────────
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq ImplExpr (impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d)) ",
                    "(rv : forall (d : Nat), Eq ImplExpr (impl_subst_fvar vv x v) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d)) ",
                    "(rb : forall (d : Nat), Eq ImplExpr (impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x d) v d)) (d : Nat) => ",
                    "Eq.trans ImplExpr ",
                    "(ImplExpr.let_ nm (impl_subst_fvar ty x v) (impl_subst_fvar vv x v) ",
                    "(impl_subst_fvar bb x v)) ",
                    "(ImplExpr.let_ nm (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_subst_fvar vv x v) (impl_subst_fvar bb x v)) ",
                    "(ImplExpr.let_ nm (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d))) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ",
                    "ImplExpr.let_ nm w (impl_subst_fvar vv x v) (impl_subst_fvar bb x v)) ",
                    "(impl_subst_fvar ty x v) ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) (rt d)) ",
                    "(Eq.trans ImplExpr ",
                    "(ImplExpr.let_ nm (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_subst_fvar vv x v) (impl_subst_fvar bb x v)) ",
                    "(ImplExpr.let_ nm (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d) ",
                    "(impl_subst_fvar bb x v)) ",
                    "(ImplExpr.let_ nm (impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d))) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.let_ nm ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) w ",
                    "(impl_subst_fvar bb x v)) ",
                    "(impl_subst_fvar vv x v) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d) (rv d)) ",
                    "(Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.let_ nm ",
                    "(impl_instantiate_at (impl_abstract_at ty x d) v d) ",
                    "(impl_instantiate_at (impl_abstract_at vv x d) v d) w) ",
                    "(impl_subst_fvar bb x v) ",
                    "(impl_instantiate_at (impl_abstract_at bb x (Nat.succ d)) v (Nat.succ d)) ",
                    "(rb (Nat.succ d))))) ",
                    // ── lit / mdata ─────────────────────────────────────────
                    "(fun (lt : ImplLit) (d : Nat) => Eq.refl ImplExpr (ImplExpr.lit lt)) ",
                    "(fun (inner : ImplExpr) ",
                    "(ri : forall (d : Nat), Eq ImplExpr (impl_subst_fvar inner x v) ",
                    "(impl_instantiate_at (impl_abstract_at inner x d) v d)) (d : Nat) => ",
                    "Eq.cong ImplExpr ImplExpr (fun (w : ImplExpr) => ImplExpr.mdata w) ",
                    "(impl_subst_fvar inner x v) ",
                    "(impl_instantiate_at (impl_abstract_at inner x d) v d) (ri d)) ",
                    "bt"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — THE let_ ZETA EQUATION, reduced to pure layer 1 and proved. ",
                "THE REDUCTION IS THE FINDING. Composing to_kexpr_abstract with ",
                "to_kexpr_at_instantiate makes the TRANSLATION CANCEL OUT ENTIRELY, so let_'s ",
                "remaining obligation is not a statement about to_kexpr at all — it is the ",
                "classical fact that substituting a free variable IS abstract-then-instantiate. ",
                "No new translation reasoning was needed, which is why this lemma mentions ",
                "neither to_kexpr nor KExpr. ",
                "NO SCOPING ON THE SUBJECT is required: the bvar case holds at EVERY index, ",
                "because abstraction's shift-up and instantiation's shift-down are inverse on ",
                "the nose — and the two helpers scrutinise the SAME `Nat.sub d i`, so the ",
                "i < d branch is Eq.refl. The i >= d branch is where the arithmetic lives: ",
                "nat_sub_zero_implies_sub_succ_zero puts instantiation in its geq branch, ",
                "sub_zero_lt_succ + lt_sub_succ put THAT in its decrement branch, and ",
                "nat_sub_succ_one lands it back on i. ",
                "The ONE hypothesis is on the VALUE, and it is forced: impl_subst_fvar inserts ",
                "v raw (no shifting, expr/subst.rs:1162) while the composite inserts ",
                "`impl_lift_at v Nat.zero d`, so those agree exactly when v is locally closed ",
                "— impl_lift_lc. ",
                "The binder arms are where the statement's generalisation over d pays for ",
                "itself: impl_subst_fvar has NO depth parameter, so the left side is unchanged ",
                "under a binder while the right side steps to `Nat.succ d`, and the IH must be ",
                "available there. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplExpr.rec".to_string(),
                "impl_subst_fvar".to_string(),
                "impl_abstract_at".to_string(),
                "impl_instantiate_at".to_string(),
                "impl_lift_lc".to_string(),
                "sub_zero_lt_succ".to_string(),
                "lt_sub_succ".to_string(),
                "nat_sub_zero_implies_sub_succ_zero".to_string(),
                "nat_sub_succ_one".to_string(),
                "nat_sub_self".to_string(),
                "Le.refl".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        // ── let_, with all THREE equations discharged ────────────────────────
        // The zeta premise is assembled here rather than proved again: rewrite
        // the layer-1 subject by impl_subst_is_abstract_instantiate, then push
        // the translation through by to_kexpr_at_instantiate. Both are already
        // theorems, so this is composition, not a fourth induction.
        self.add_definition(SpecDefinition {
            name: "impl_sound_let_scoped".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) ",
                "(b : ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr), ",
                "ImplScoped x b Nat.zero -> ImplLC bt Nat.zero -> ImplLC v Nat.zero -> ",
                "ImplWhnfTo S (ImplExpr.sort l) -> ImplIsLe Tv ty -> ",
                "TypingCtxConv tenvK Gk (to_kexpr ty rho) (to_kexpr S rho) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr bt (ListType.cons Nat x rho)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.let_ nm ty v b) rho) ",
                "(to_kexpr (impl_subst_fvar bt x v) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) ",
                    "(b : ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr) ",
                    "(hsc : ImplScoped x b Nat.zero) (hlcbt : ImplLC bt Nat.zero) ",
                    "(hlcv : ImplLC v Nat.zero) ",
                    "(hs : ImplWhnfTo S (ImplExpr.sort l)) (hle : ImplIsLe Tv ty) ",
                    "(ihty : TypingCtxConv tenvK Gk (to_kexpr ty rho) (to_kexpr S rho)) ",
                    "(ihv : TypingCtxConv tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr bt (ListType.cons Nat x rho))) => ",
                    "impl_sound_let tenvK Gk rho x nm ty v b S l Tv bt hs hle ihty ihv ihb ",
                    "(to_kexpr_open rho x b Nat.zero hsc) ",
                    "(to_kexpr_abstract rho x bt Nat.zero hlcbt) ",
                    "(Eq.trans KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                    "(to_kexpr_at (impl_instantiate_at (impl_abstract_fvar bt x) v Nat.zero) ",
                    "rho Nat.zero) ",
                    "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho ",
                    "(Nat.succ Nat.zero)) (to_kexpr v rho)) ",
                    "(Eq.cong ImplExpr KExpr ",
                    "(fun (w : ImplExpr) => to_kexpr_at w rho Nat.zero) ",
                    "(impl_subst_fvar bt x v) ",
                    "(impl_instantiate_at (impl_abstract_fvar bt x) v Nat.zero) ",
                    "(impl_subst_is_abstract_instantiate v hlcv x bt Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho v (impl_abstract_fvar bt x) Nat.zero))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `let_` rule with NO EQUATIONAL PREMISES LEFT, completing the binder ",
                "family. All three equations impl_sound_let carried are now theorems: the open ",
                "and abstract commutations directly, and the zeta result equation by ",
                "COMPOSITION rather than a fourth induction — rewrite the layer-1 subject by ",
                "impl_subst_is_abstract_instantiate, then push the translation through by ",
                "to_kexpr_at_instantiate. ",
                "It carries one more scoping hypothesis than lam does, ImplLC v Nat.zero, and ",
                "that is forced by the deployed arm rather than by the proof: impl_subst_fvar ",
                "inserts the value RAW where abstract-then-instantiate inserts it lifted, so ",
                "the two agree only on a locally-closed value. lam never substitutes a value at ",
                "all, so it never needs this. ",
                "COVERAGE: sort, const, mdata, app unconditional; lam, pi, let_ unconditional ",
                "modulo SCOPING — genuine invariants of the deployed checker, not unproved ",
                "equations. That is 7 of ImplInfer's 9 rules, and 7 is the ceiling for this ",
                "codomain: lit has no TypingCtxConv rule to bridge into, and bvar is a ",
                "refutation rather than a rule. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_sound_let".to_string(),
                "to_kexpr_open".to_string(),
                "to_kexpr_abstract".to_string(),
                "impl_subst_is_abstract_instantiate".to_string(),
                "to_kexpr_at_instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The abstract commutation, and the strictly-tighter scoping relation it
    /// needs.
    ///
    /// A SECOND relation is required here and the difference is not cosmetic.
    /// `ImplScoped`'s bvar field is `Le i d` — loose bvars up to *and
    /// including* `d`, correct for a lam **body**, whose `bvar 0` is the binder
    /// about to be opened. But `impl_abstract_at` shifts bvars `>= depth` **up**
    /// by one, so at `i = d` the two sides land on `bvar d` and `bvar (succ d)`.
    /// The subject here is the inferred **type** of an already-opened body,
    /// which has no loose bvar at all: `Lt i d`, uninhabited at `d = 0`, exactly
    /// as it should be.
    fn add_abstract_commutation(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            concat!(
                "inductive ImplLC : ImplExpr -> Nat -> Type\n",
                "| bvar : forall (i : Nat) (d : Nat), Lt i d -> ImplLC (ImplExpr.bvar i) d\n",
                "| fvar : forall (y : Nat) (d : Nat), ImplLC (ImplExpr.fvar y) d\n",
                "| sort : forall (l : Level) (d : Nat), ImplLC (ImplExpr.sort l) d\n",
                "| const : forall (nm : Name) (us : ListType Level) (d : Nat), ImplLC (ImplExpr.const nm us) d\n",
                "| app : forall (f : ImplExpr) (a : ImplExpr) (d : Nat), ImplLC f d -> ImplLC a d -> ImplLC (ImplExpr.app f a) d\n",
                "| lam : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplLC ty d -> ImplLC b (Nat.succ d) -> ImplLC (ImplExpr.lam bd ty b) d\n",
                "| pi : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplLC ty d -> ImplLC b (Nat.succ d) -> ImplLC (ImplExpr.pi bd ty b) d\n",
                "| let_ : forall (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (d : Nat), ImplLC ty d -> ImplLC v d -> ImplLC b (Nat.succ d) -> ImplLC (ImplExpr.let_ nm ty v b) d\n",
                "| lit : forall (lt : ImplLit) (d : Nat), ImplLC (ImplExpr.lit lt) d\n",
                "| mdata : forall (e : ImplExpr) (d : Nat), ImplLC e d -> ImplLC (ImplExpr.mdata e) d"
            ),
            "ImplLC e d: every loose bvar of e is STRICTLY below d. Deliberately tighter than \
             ImplScoped's Le bound, and the difference is load-bearing rather than stylistic: \
             impl_abstract_at shifts bvars >= depth UP by one, so at i = d the two sides of the \
             abstract commutation land on bvar d and bvar (succ d). ImplScoped's Le is right for \
             a lam BODY (whose bvar 0 is the binder about to be opened); ImplLC's Lt is right \
             for the inferred TYPE of an already-opened body, which has no loose bvar at all — \
             and at d = 0, `Lt i Nat.zero` is uninhabited, which is exactly the correct reading. \
             Carries NO freshness field, unlike ImplScoped: abstraction needs to FIND x, not \
             avoid it, so both branches of its fvar test are proved rather than one excluded. \
             Operational/syntactic only; no constructor field mentions a typing judgment. \
             ZERO new axioms (census-neutral).",
        )?;

        self.add_definition(SpecDefinition {
            name: "to_kexpr_abstract".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (x : Nat) (e : ImplExpr) (d : Nat), ",
                "ImplLC e d -> ",
                "Eq KExpr (to_kexpr_at e (ListType.cons Nat x rho) d) ",
                "(to_kexpr_at (impl_abstract_at e x d) rho (Nat.succ d))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (x : Nat) (e : ImplExpr) (d : Nat) ",
                    "(h : ImplLC e d) => ",
                    "ImplLC.rec ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_h0 : ImplLC e0 d0) => Eq KExpr ",
                    "(to_kexpr_at e0 (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at e0 x d0) rho (Nat.succ d0))) ",
                    // bvar: i < d, so impl_abstract_bvar leaves it alone.
                    "(fun (i : Nat) (d0 : Nat) (hlt : Lt i d0) => ",
                    "Eq.substType Nat (fun (s : Nat) => Eq KExpr (KExpr.bvar i) ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.succ i)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) rho (Nat.succ d0))) ",
                    "(Nat.succ (Nat.sub (Nat.sub d0 i) (Nat.succ Nat.zero))) (Nat.sub d0 i) ",
                    "(Eq.symm Nat (Nat.sub d0 i) ",
                    "(Nat.succ (Nat.sub (Nat.sub d0 i) (Nat.succ Nat.zero))) ",
                    "(lt_sub_succ i d0 hlt)) ",
                    "(Eq.refl KExpr (KExpr.bvar i))) ",
                    // fvar: BOTH branches — abstraction is looking FOR x.
                    "(fun (y : Nat) (d0 : Nat) => ",
                    "Bool.rec (fun (bb : Bool) => Eq Bool (nat_eqb y x) bb -> Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho y)) Nat.zero (nat_eqb x y)) d0)) ",
                    "(to_kexpr_at (Bool.rec (fun (_c : Bool) => ImplExpr) (ImplExpr.fvar y) ",
                    "(ImplExpr.bvar d0) bb) rho (Nat.succ d0))) ",
                    "(fun (hf : Eq Bool (nat_eqb y x) Bool.false) => ",
                    "Eq.substType Bool (fun (cc : Bool) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho y)) Nat.zero cc) d0)) ",
                    "(KExpr.bvar (Nat.add (rho_index rho y) (Nat.succ d0)))) ",
                    "Bool.false (nat_eqb x y) ",
                    "(Eq.symm Bool (nat_eqb x y) Bool.false ",
                    "(Eq.trans Bool (nat_eqb x y) (nat_eqb y x) Bool.false ",
                    "(nat_eqb_symm x y) hf)) ",
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add (Nat.succ (rho_index rho y)) d0) ",
                    "(Nat.add (rho_index rho y) (Nat.succ d0)) ",
                    "(nat_succ_add (rho_index rho y) d0))) ",
                    "(fun (ht : Eq Bool (nat_eqb y x) Bool.true) => ",
                    "Eq.substType Bool (fun (cc : Bool) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho y)) Nat.zero cc) d0)) (KExpr.bvar d0)) ",
                    "Bool.true (nat_eqb x y) ",
                    "(Eq.symm Bool (nat_eqb x y) Bool.true ",
                    "(Eq.trans Bool (nat_eqb x y) (nat_eqb y x) Bool.true ",
                    "(nat_eqb_symm x y) ht)) ",
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add Nat.zero d0) d0 (nat_zero_add d0))) ",
                    "(nat_eqb y x) (Eq.refl Bool (nat_eqb y x))) ",
                    // sort / const
                    "(fun (l : Level) (d0 : Nat) => Eq.refl KExpr (KExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d0 : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // app
                    "(fun (f : ImplExpr) (a : ImplExpr) (d0 : Nat) ",
                    "(_lf : ImplLC f d0) (_la : ImplLC a d0) ",
                    "(rf : Eq KExpr (to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at f x d0) rho (Nat.succ d0))) ",
                    "(ra : Eq KExpr (to_kexpr_at a (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at a x d0) rho (Nat.succ d0))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.app (to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (to_kexpr_at (impl_abstract_at f x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (to_kexpr_at (impl_abstract_at f x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at a x d0) rho (Nat.succ d0))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at f x d0) rho (Nat.succ d0)) rf) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app ",
                    "(to_kexpr_at (impl_abstract_at f x d0) rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at a x d0) rho (Nat.succ d0)) ra)) ",
                    // lam
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.lam (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0))) rb)) ",
                    // pi
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.pi (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0))) rb)) ",
                    // let_
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplLC ty d0) (_lv : ImplLC vv d0) (_lb : ImplLC bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0))) ",
                    "(rv : Eq KExpr (to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.let_ (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) rt) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0)))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0)) rv) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(to_kexpr_at (impl_abstract_at ty x d0) rho (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at vv x d0) rho (Nat.succ d0)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(to_kexpr_at (impl_abstract_at bb x (Nat.succ d0)) rho ",
                    "(Nat.succ (Nat.succ d0))) rb))) ",
                    // lit / mdata
                    "(fun (lt : ImplLit) (d0 : Nat) => ",
                    "ImplLit.rec (fun (z : ImplLit) => Eq KExpr (impl_lit_to_kexpr z) ",
                    "(impl_lit_to_kexpr z)) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) lt) ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_le : ImplLC e0 d0) ",
                    "(ri : Eq KExpr (to_kexpr_at e0 (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at (impl_abstract_at e0 x d0) rho (Nat.succ d0))) => ri) ",
                    "e d h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — THE ABSTRACT COMMUTATION, discharged. Abstracting the fresh FVarId back ",
                "out and dropping it from the renaming is the same as translating one binder ",
                "deeper. Together with to_kexpr_open this discharges BOTH premises of ",
                "impl_sound_lam and impl_sound_pi. ",
                "THE fvar CASE PROVES BOTH BRANCHES, unlike to_kexpr_open's, and that is the ",
                "structural difference between the two lemmas: opening must AVOID the fresh ",
                "name (so ImplScoped carries a freshness field and the x-case is excluded), ",
                "while abstraction is looking FOR it (so no freshness field exists and both ",
                "branches are proved). The two sides also scrutinise nat_eqb with the operands ",
                "in OPPOSITE orders — rho_index tests head-vs-query, impl_abstract_at tests ",
                "query-vs-target — so nat_eqb_symm is needed in BOTH branches, not as a ",
                "convenience but because the two booleans are genuinely different terms. ",
                "The bvar case is where the strict bound earns its keep: impl_abstract_bvar ",
                "shifts bvars >= depth UP by one, and Lt i d (through lt_sub_succ) is exactly ",
                "what puts the scrutinee in the leave-alone branch. Under ImplScoped's Le this ",
                "case would be FALSE at i = d. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplLC.rec".to_string(),
                "to_kexpr_at".to_string(),
                "impl_abstract_at".to_string(),
                "lt_sub_succ".to_string(),
                "nat_eqb_symm".to_string(),
                "nat_zero_add".to_string(),
                "nat_succ_add".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── the payoff: lam and pi with NO equational premises left ──────────
        // Both commutations are theorems now, so instantiating them at depth
        // zero discharges the equations impl_sound_lam / _pi carried. What
        // remains as a hypothesis is SCOPING — a genuine invariant of the
        // deployed checker — rather than an unproved equation.
        self.add_definition(SpecDefinition {
            name: "impl_sound_lam_scoped".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                "(b : ImplExpr) (S : ImplExpr) (l : Level) (bt : ImplExpr), ",
                "ImplScoped x b Nat.zero -> ImplLC bt Nat.zero -> ",
                "ImplWhnfTo S (ImplExpr.sort l) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr bt (ListType.cons Nat x rho)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.lam bd A b) rho) ",
                "(to_kexpr (ImplExpr.pi bd A (impl_abstract_fvar bt x)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                    "(b : ImplExpr) (S : ImplExpr) (l : Level) (bt : ImplExpr) ",
                    "(hsc : ImplScoped x b Nat.zero) (hlc : ImplLC bt Nat.zero) ",
                    "(hs : ImplWhnfTo S (ImplExpr.sort l)) ",
                    "(ihA : TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr bt (ListType.cons Nat x rho))) => ",
                    "impl_sound_lam tenvK Gk rho x bd A b S l bt hs ihA ihb ",
                    "(to_kexpr_open rho x b Nat.zero hsc) ",
                    "(to_kexpr_abstract rho x bt Nat.zero hlc)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `lam` rule with NO EQUATIONAL PREMISES LEFT. impl_sound_lam carried ",
                "the open and abstract commutations as hypotheses because both are false ",
                "without a scoping side condition; both are theorems now, so instantiating them ",
                "at depth zero discharges both. ",
                "What remains is SCOPING: ImplScoped x b 0 (the body's only loose bvar is the ",
                "one being opened, and x is fresh) and ImplLC bt 0 (the inferred type has no ",
                "loose bvar at all). Those are genuine invariants of the deployed checker, not ",
                "unproved equations — production never reuses an FVarId ",
                "(tc/local_context.rs:86-89) and the inferred type of an opened body is closed. ",
                "The instantiation is DEFINITIONAL on both sides — `impl_open b x` IS ",
                "`impl_instantiate_at b (fvar x) Nat.zero` and `impl_abstract_fvar bt x` IS ",
                "`impl_abstract_at bt x Nat.zero` — so this is a one-line corollary, not a ",
                "second proof. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_sound_lam".to_string(),
                "to_kexpr_open".to_string(),
                "to_kexpr_abstract".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_sound_pi_scoped".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                "(b : ImplExpr) (S1 : ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level), ",
                "ImplScoped x b Nat.zero -> ",
                "ImplWhnfTo S1 (ImplExpr.sort l1) -> ImplWhnfTo S2 (ImplExpr.sort l2) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S1 rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr S2 (ListType.cons Nat x rho)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.pi bd A b) rho) ",
                "(to_kexpr (ImplExpr.sort (Level.imax l1 l2)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                    "(b : ImplExpr) (S1 : ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level) ",
                    "(hsc : ImplScoped x b Nat.zero) ",
                    "(hs1 : ImplWhnfTo S1 (ImplExpr.sort l1)) ",
                    "(hs2 : ImplWhnfTo S2 (ImplExpr.sort l2)) ",
                    "(ihA : TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S1 rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr S2 (ListType.cons Nat x rho))) => ",
                    "impl_sound_pi tenvK Gk rho x bd A b S1 S2 l1 l2 hs1 hs2 ihA ihb ",
                    "(to_kexpr_open rho x b Nat.zero hsc)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `pi` rule with NO EQUATIONAL PREMISES LEFT, and it needs only the ",
                "SCOPING hypothesis on the body: a Pi's result type is a sort, so there is ",
                "nothing to abstract back and ImplLC never appears. That asymmetry with lam is ",
                "in the deployed arms, not in this proof. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_sound_pi".to_string(),
                "to_kexpr_open".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The `lam` and `pi` rules, with the open/abstract round trip carried as
    /// EXPLICIT premises.
    ///
    /// This is a deliberate decomposition, not a dodge. Two independent
    /// questions are tangled together in the binder rules:
    ///
    /// 1. *Does `conv` make the binder arms work?* — the M4 retarget question.
    ///    The deployed `lam` arm infers `A : S` and then whnf's `S` to a sort
    ///    (`ensure_sort`, `tc/infer.rs:521`), which `KernelInfers` had no rule
    ///    to express. **Answered here, in full.**
    /// 2. *Does the translation commute with `impl_open` / `impl_abstract_fvar`?*
    ///    — a pure question about syntax, with no typing in it at all.
    ///
    /// The second is genuinely open and is **false as stated without a scoping
    /// hypothesis**: `impl_open` decrements the bvars it does not replace while
    /// the un-opened translation does not, so on any `bvar j` with `j >= 1` the
    /// two sides differ. It holds exactly when the body is locally closed at 1.
    /// Discharging it needs a locally-closed predicate on `ImplExpr` and its
    /// induction — the same predicate `ctx_rep.rs` names as what `CtxRep.snoc`'s
    /// assumed field 3 would need in order to be *derived* rather than assumed.
    ///
    /// So the equations are premises: syntactic equalities, containing no
    /// typing judgment and in particular not the conclusion. Whoever proves them
    /// gets these two rules for free.
    fn add_binder_arms(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "impl_sound_lam".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                "(b : ImplExpr) (S : ImplExpr) (l : Level) (bt : ImplExpr), ",
                "ImplWhnfTo S (ImplExpr.sort l) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr bt (ListType.cons Nat x rho)) -> ",
                "Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr_at b rho (Nat.succ Nat.zero)) -> ",
                "Eq KExpr (to_kexpr bt (ListType.cons Nat x rho)) ",
                "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.lam bd A b) rho) ",
                "(to_kexpr (ImplExpr.pi bd A (impl_abstract_fvar bt x)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                    "(b : ImplExpr) (S : ImplExpr) (l : Level) (bt : ImplExpr) ",
                    "(hs : ImplWhnfTo S (ImplExpr.sort l)) ",
                    "(ihA : TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr bt (ListType.cons Nat x rho))) ",
                    "(hopen : Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(habs : Eq KExpr (to_kexpr bt (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) => ",
                    "TypingCtxConv.lam tenvK Gk (to_kexpr A rho) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) l ",
                    // domain : sort — THE step KernelInfers could not take.
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr A rho) (to_kexpr S rho) ",
                    "(KExpr.sort l) ihA ",
                    "(impl_whnf_to_defeq rho S (ImplExpr.sort l) hs)) ",
                    // body : rewrite subject then type, along the two equations.
                    "(Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK ",
                    "(ListType.cons KExpr (to_kexpr A rho) Gk) w ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) hopen ",
                    "(Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK ",
                    "(ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) w) ",
                    "(to_kexpr bt (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                    "habs ihb))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `lam` RULE, modulo the open/abstract round trip. ctx_rep.rs listed this ",
                "rule as blocked because KernelInfers.lam demanded the domain's inferred type be ",
                "SYNTACTICALLY a sort while the deployed body whnf-reduces first (ensure_sort, ",
                "tc/infer.rs:521). THAT blocker is gone twice over: here, because the domain ",
                "premise is TypingCtxConv.conv applied to impl_whnf_to_defeq; and at the source, ",
                "since 2026-08-08 KernelInfers.lam itself carries `whnf_to SA (KExpr.sort u)` as ",
                "a witnessed premise, in the idiom its own let_ arm always used. ",
                "WHAT IS CARRIED AS A PREMISE AND WHY. The open/abstract commutation equations ",
                "are hypotheses because they are FALSE without a scoping side condition — ",
                "checked case by case, not assumed: impl_open decrements the bvars it does not ",
                "replace while the un-opened translation does not, so on any `bvar j` with j >= 1 ",
                "the two sides differ. They hold exactly when the body is locally closed at 1. ",
                "Discharging them needs a locally-closed predicate on ImplExpr and its ",
                "induction — the SAME predicate ctx_rep.rs names as what CtxRep.snoc's assumed ",
                "field 3 would need in order to be derived rather than assumed. ",
                "This is a decomposition, not a masquerade: the premises are syntactic ",
                "EQUATIONS containing no typing judgment, and neither is the conclusion. It ",
                "separates the retarget question (does conv make the binder arms work? — ",
                "answered here, in full) from a pure question about syntax. Whoever proves the ",
                "equations gets this rule for free. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.lam".to_string(),
                "TypingCtxConv.conv".to_string(),
                "impl_whnf_to_defeq".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // pi needs only the OPEN equation — its result type is a sort, so there
        // is nothing to abstract back.
        self.add_definition(SpecDefinition {
            name: "impl_sound_pi".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                "(b : ImplExpr) (S1 : ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level), ",
                "ImplWhnfTo S1 (ImplExpr.sort l1) -> ImplWhnfTo S2 (ImplExpr.sort l2) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S1 rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr S2 (ListType.cons Nat x rho)) -> ",
                "Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr_at b rho (Nat.succ Nat.zero)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.pi bd A b) rho) ",
                "(to_kexpr (ImplExpr.sort (Level.imax l1 l2)) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (bd : BinderData) (A : ImplExpr) ",
                    "(b : ImplExpr) (S1 : ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level) ",
                    "(hs1 : ImplWhnfTo S1 (ImplExpr.sort l1)) ",
                    "(hs2 : ImplWhnfTo S2 (ImplExpr.sort l2)) ",
                    "(ihA : TypingCtxConv tenvK Gk (to_kexpr A rho) (to_kexpr S1 rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr S2 (ListType.cons Nat x rho))) ",
                    "(hopen : Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) => ",
                    "TypingCtxConv.pi tenvK Gk (to_kexpr A rho) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) l1 l2 ",
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr A rho) (to_kexpr S1 rho) ",
                    "(KExpr.sort l1) ihA ",
                    "(impl_whnf_to_defeq rho S1 (ImplExpr.sort l1) hs1)) ",
                    "(Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK ",
                    "(ListType.cons KExpr (to_kexpr A rho) Gk) w (KExpr.sort l2)) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) hopen ",
                    "(TypingCtxConv.conv tenvK (ListType.cons KExpr (to_kexpr A rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr S2 (ListType.cons Nat x rho)) (KExpr.sort l2) ihb ",
                    "(impl_whnf_to_defeq (ListType.cons Nat x rho) S2 (ImplExpr.sort l2) hs2)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `pi` RULE, modulo the open equation. ctx_rep.rs lists pi as blocked by ",
                "the same ensure_sort omission as lam, but TWICE (tc/infer.rs:555 and :573 — ",
                "which is why the layer-1 rule carries two ImplWhnfTo premises). Both are ",
                "discharged here by TypingCtxConv.conv over impl_whnf_to_defeq. ",
                "Needs only the OPEN equation and not the abstract one, because a Pi's result ",
                "type is a SORT — there is nothing to abstract back. That asymmetry with `lam` ",
                "is in the deployed arms, not in this proof. ",
                "Note the second conv runs under the EXTENDED renaming (cons x rho), which is ",
                "the first place impl_whnf_to_defeq is used at a renaming other than the ",
                "ambient one — it is stated for all rho precisely so that works. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.pi".to_string(),
                "TypingCtxConv.conv".to_string(),
                "impl_whnf_to_defeq".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // let_ needs a THIRD equation, and it is not the same shape as the
        // other two. The deployed Let arm concludes with `subst_fvar`
        // DIRECTLY — zeta, not instantiate (tc/infer.rs:614-617) — while
        // TypingCtxConv.let_ concludes at `instantiate B v`. So the result
        // equation relates two genuinely different operations, where lam's
        // relates one operation to its own translation.
        self.add_definition(SpecDefinition {
            name: "impl_sound_let".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                "(rho : ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) ",
                "(b : ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr), ",
                "ImplWhnfTo S (ImplExpr.sort l) -> ImplIsLe Tv ty -> ",
                "TypingCtxConv tenvK Gk (to_kexpr ty rho) (to_kexpr S rho) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho) -> ",
                "TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) ",
                "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr bt (ListType.cons Nat x rho)) -> ",
                "Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                "(to_kexpr_at b rho (Nat.succ Nat.zero)) -> ",
                "Eq KExpr (to_kexpr bt (ListType.cons Nat x rho)) ",
                "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) -> ",
                "Eq KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                "(to_kexpr v rho)) -> ",
                "TypingCtxConv tenvK Gk (to_kexpr (ImplExpr.let_ nm ty v b) rho) ",
                "(to_kexpr (impl_subst_fvar bt x v) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (Gk : ListType KExpr) ",
                    "(rho : ListType Nat) (x : Nat) (nm : Name) (ty : ImplExpr) (v : ImplExpr) ",
                    "(b : ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr) ",
                    "(hs : ImplWhnfTo S (ImplExpr.sort l)) (hle : ImplIsLe Tv ty) ",
                    "(ihty : TypingCtxConv tenvK Gk (to_kexpr ty rho) (to_kexpr S rho)) ",
                    "(ihv : TypingCtxConv tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho)) ",
                    "(ihb : TypingCtxConv tenvK (ListType.cons KExpr (to_kexpr ty rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr bt (ListType.cons Nat x rho))) ",
                    "(hopen : Eq KExpr (to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(habs : Eq KExpr (to_kexpr bt (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) ",
                    "(hzeta : Eq KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                    "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr v rho))) => ",
                    // Rewrite the CONCLUSION's type from layer 2's instantiate
                    // back to layer 1's subst_fvar — the zeta result equation.
                    "Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK Gk ",
                    "(KExpr.let_ (to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) w) ",
                    "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr v rho)) ",
                    "(to_kexpr (impl_subst_fvar bt x v) rho) ",
                    "(Eq.symm KExpr (to_kexpr (impl_subst_fvar bt x v) rho) ",
                    "(instantiate (to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr v rho)) hzeta) ",
                    "(TypingCtxConv.let_ tenvK Gk (to_kexpr ty rho) (to_kexpr v rho) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) l ",
                    // annotation : sort — conv over the whnf step.
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr ty rho) (to_kexpr S rho) ",
                    "(KExpr.sort l) ihty ",
                    "(impl_whnf_to_defeq rho S (ImplExpr.sort l) hs)) ",
                    // value : annotation — conv over the is_le ascription.
                    "(TypingCtxConv.conv tenvK Gk (to_kexpr v rho) (to_kexpr Tv rho) ",
                    "(to_kexpr ty rho) ihv (impl_is_le_defeq rho Tv ty hle)) ",
                    // body, under the extended context.
                    "(Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK ",
                    "(ListType.cons KExpr (to_kexpr ty rho) Gk) w ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero))) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) hopen ",
                    "(Eq.substType KExpr (fun (w : KExpr) => TypingCtxConv tenvK ",
                    "(ListType.cons KExpr (to_kexpr ty rho) Gk) ",
                    "(to_kexpr (impl_open b x) (ListType.cons Nat x rho)) w) ",
                    "(to_kexpr bt (ListType.cons Nat x rho)) ",
                    "(to_kexpr_at (impl_abstract_fvar bt x) rho (Nat.succ Nat.zero)) ",
                    "habs ihb)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the `let_` RULE, modulo three equations. ctx_rep.rs lists let_ as blocked ",
                "by the ensure_sort omission for the annotation (tc/infer.rs:594) PLUS ",
                "\"ImplIsLe Tv ty has no KernelInfers-side counterpart\". Both are discharged ",
                "here — the first by conv over impl_whnf_to_defeq, the second by conv over ",
                "impl_is_le_defeq — and neither was expressible against KernelInfers. ",
                "THE THIRD EQUATION IS NOT THE SAME SHAPE AS lam's TWO, and that is the finding ",
                "worth recording. The deployed Let arm concludes with `subst_fvar` DIRECTLY — ",
                "zeta, tc/infer.rs:614-617 — where TypingCtxConv.let_ concludes at ",
                "`instantiate B v`. So this equation relates two genuinely DIFFERENT operations ",
                "(layer 1 substitutes a free variable by name; layer 2 instantiates a de Bruijn ",
                "binder), whereas lam's relate one operation to its own translation. It is ",
                "carried as a premise for the same reason as the others: it needs the ",
                "locally-closed predicate, and it is a syntactic equation containing no typing ",
                "judgment. ",
                "COVERAGE with this: 7 of ImplInfer's 9 rules. `lit` is permanently ",
                "unbridgeable (TypingCtxConv has no literal rule) and `bvar` is a refutation ",
                "rather than a rule (impl_infer_bvar_rejects), so 7 is every rule that CAN be ",
                "bridged into this codomain. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.let_".to_string(),
                "TypingCtxConv.conv".to_string(),
                "impl_whnf_to_defeq".to_string(),
                "impl_is_le_defeq".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The two soundness theorems `impl_infer.rs` records as OWED.
    ///
    /// `ImplWhnfTo` and `ImplIsLe` are separately-modelled operational calls —
    /// vacuity-firewall rule 3 permits a relation constructor to invoke them
    /// precisely *because* they are not typing judgments, and the price of that
    /// permission is an independent soundness theorem against layer-2 `DefEq`
    /// under the representation relation. Both registrations say so in as many
    /// words ("owes an independent … soundness theorem … the C4 bridge job").
    /// These are those theorems.
    ///
    /// They are also what makes M4's retarget pay off. `TypingCtxConv.conv`
    /// turns a `DefEq` into a type change, so `impl_whnf_to_defeq` is exactly
    /// the `ensure_sort` absorber that `KernelInfers` had no way to express —
    /// the single omission that blocked three of C4's five unbridged rules.
    fn add_operational_boundary_soundness(&mut self) -> Result<(), SpecError> {
        // ImplWhnfTo -> DefEq. Both reduction rules are discharged by the
        // matching layer-2 rule composed with the substitution lemma; the
        // translation turns `impl_instantiate` into `instantiate` and that is
        // the ONLY reason `DefEq.beta` / `DefEq.zeta` apply on the nose.
        self.add_definition(SpecDefinition {
            name: "impl_whnf_to_defeq".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (e : ImplExpr) (r : ImplExpr), ",
                "ImplWhnfTo e r -> DefEq (to_kexpr e rho) (to_kexpr r rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (e : ImplExpr) (r : ImplExpr) ",
                    "(h : ImplWhnfTo e r) => ",
                    "ImplWhnfTo.rec ",
                    "(fun (e0 : ImplExpr) (r0 : ImplExpr) (_h0 : ImplWhnfTo e0 r0) => ",
                    "DefEq (to_kexpr e0 rho) (to_kexpr r0 rho)) ",
                    // done — reflexivity, and note this arm is why the relation
                    // OVER-approximates whnf: `done` holds at every ImplExpr,
                    // not only at whnf-normal ones. Soundness is untroubled by
                    // that; it is completeness that would care.
                    "(fun (e0 : ImplExpr) => DefEq.refl (to_kexpr e0 rho)) ",
                    // beta
                    "(fun (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (a : ImplExpr) ",
                    "(r0 : ImplExpr) (_hp : ImplWhnfTo (impl_instantiate b a) r0) ",
                    "(ih : DefEq (to_kexpr (impl_instantiate b a) rho) (to_kexpr r0 rho)) => ",
                    "DefEq.trans ",
                    "(KExpr.app (KExpr.lam (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) (to_kexpr_at a rho Nat.zero)) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr r0 rho) ",
                    "(DefEq.beta (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) (to_kexpr_at a rho Nat.zero)) ",
                    "(Eq.substType KExpr (fun (w : KExpr) => DefEq w (to_kexpr r0 rho)) ",
                    "(to_kexpr (impl_instantiate b a) rho) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho a b Nat.zero) ih)) ",
                    // zeta
                    "(fun (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) ",
                    "(r0 : ImplExpr) (_hp : ImplWhnfTo (impl_instantiate b v) r0) ",
                    "(ih : DefEq (to_kexpr (impl_instantiate b v) rho) (to_kexpr r0 rho)) => ",
                    "DefEq.trans ",
                    "(KExpr.let_ (to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at v rho Nat.zero)) ",
                    "(to_kexpr r0 rho) ",
                    "(DefEq.zeta (to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(Eq.substType KExpr (fun (w : KExpr) => DefEq w (to_kexpr r0 rho)) ",
                    "(to_kexpr (impl_instantiate b v) rho) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at v rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho v b Nat.zero) ih)) ",
                    // mdataStep — the translation ERASES mdata, so both sides
                    // are already the inner term's and the IH is the whole proof.
                    "(fun (e0 : ImplExpr) (r0 : ImplExpr) (_hp : ImplWhnfTo e0 r0) ",
                    "(ih : DefEq (to_kexpr e0 rho) (to_kexpr r0 rho)) => ih) ",
                    "e r h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "OWED SOUNDNESS THEOREM #1, discharged. impl_infer.rs registers ImplWhnfTo as a ",
                "separately-modelled operational call and records that it \"owes an independent ",
                "ImplWhnfTo -> DefEq soundness theorem under the representation relation (the ",
                "C4 bridge job)\". This is it: layer-1 weak-head reduction is layer-2 ",
                "definitional equality on the translated terms. ",
                "THIS IS ALSO WHAT MAKES M4'S RETARGET PAY OFF. TypingCtxConv.conv converts a ",
                "DefEq into a type change, so this lemma is precisely the `ensure_sort` ",
                "absorber KernelInfers could not express — the single layer-2 omission that ",
                "blocked three of C4's five unbridged rules (lam, pi, let_). ",
                "Proved by ImplWhnfTo.rec. `done` is DefEq.refl — and note that arm is why the ",
                "relation OVER-approximates whnf (`done` holds at every ImplExpr, not only at ",
                "normal ones); soundness is untroubled by that, completeness would not be. ",
                "`beta` and `zeta` are the matching layer-2 rules composed with ",
                "to_kexpr_at_instantiate, which is the ONLY reason DefEq.beta / DefEq.zeta ",
                "apply on the nose: the translation has to turn impl_instantiate into ",
                "instantiate first. `mdataStep` is the identity because the translation erases ",
                "mdata. ",
                "SCOPE, unchanged and not silently widened: ImplWhnfTo still covers only the ",
                "env-free fragment (done/beta/zeta/mdata); delta, iota, proj and eta need the ",
                "environment and remain Phase-B width. This theorem is sound for what the ",
                "relation contains, and the relation's own registration names what it does not. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplWhnfTo.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.trans".to_string(),
                "to_kexpr_at_instantiate".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ImplWhnfTo -> whnf_to, the SHARPER companion of the lemma above.
        //
        // Why bother, when impl_whnf_to_defeq already unblocks M4: because DefEq
        // is what `TypingCtxConv.conv` consumes, and conv is unrestricted — a
        // type reached through it is *some* member of the conversion class, not
        // the type the checker returned. `whnf_to` is what `KernelInfers.app`
        // and `.let_` take as WITNESSED premises, so this lemma is what a bridge
        // into `KernelInfers` needs: it says layer-1 weak-head reduction really
        // is layer-2 weak-head reduction, not merely that the endpoints are
        // convertible. It is the difference between "the result is def-equal to
        // something well-typed" and "the checker's reduction step was correct".
        //
        // The `is_whnf` hypothesis is FORCED, not defensive. `ImplWhnfTo.done`
        // is unrestricted reflexivity — it holds at every ImplExpr, which is
        // exactly the over-approximation impl_whnf_to_defeq's own comment names —
        // while `whnf_to.refl` demands `is_whnf e`. Without the hypothesis the
        // `done` arm is unprovable, and it is free at every use site, where the
        // reduct's shape is known (a Pi for the App rule, a Sort for ensure_sort).
        self.add_definition(SpecDefinition {
            name: "impl_whnf_to_whnf_to".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (e : ImplExpr) (r : ImplExpr), ",
                "ImplWhnfTo e r -> is_whnf (to_kexpr r rho) -> ",
                "whnf_to (to_kexpr e rho) (to_kexpr r rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (e : ImplExpr) (r : ImplExpr) ",
                    "(h : ImplWhnfTo e r) => ",
                    "ImplWhnfTo.rec ",
                    "(fun (e0 : ImplExpr) (r0 : ImplExpr) (_h0 : ImplWhnfTo e0 r0) => ",
                    "is_whnf (to_kexpr r0 rho) -> ",
                    "whnf_to (to_kexpr e0 rho) (to_kexpr r0 rho)) ",
                    // done — the arm the is_whnf hypothesis exists for.
                    "(fun (e0 : ImplExpr) (hw : is_whnf (to_kexpr e0 rho)) => ",
                    "whnf_to.refl (to_kexpr e0 rho) hw) ",
                    // beta — one layer-2 beta step, then the IH.
                    "(fun (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (a : ImplExpr) ",
                    "(r0 : ImplExpr) (_hp : ImplWhnfTo (impl_instantiate b a) r0) ",
                    "(ih : is_whnf (to_kexpr r0 rho) -> ",
                    "whnf_to (to_kexpr (impl_instantiate b a) rho) (to_kexpr r0 rho)) ",
                    "(hw : is_whnf (to_kexpr r0 rho)) => ",
                    "whnf_to.step ",
                    "(KExpr.app (KExpr.lam (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) (to_kexpr_at a rho Nat.zero)) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr r0 rho) ",
                    "(whnf_step.beta ",
                    "(KExpr.app (KExpr.lam (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) (to_kexpr_at a rho Nat.zero)) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(beta_reduces.beta (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)) (to_kexpr_at a rho Nat.zero))) ",
                    "(Eq.substType KExpr ",
                    "(fun (w : KExpr) => whnf_to w (to_kexpr r0 rho)) ",
                    "(to_kexpr (impl_instantiate b a) rho) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho a b Nat.zero) (ih hw))) ",
                    // zeta — the same shape over the genuine let_ constructor.
                    "(fun (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) ",
                    "(r0 : ImplExpr) (_hp : ImplWhnfTo (impl_instantiate b v) r0) ",
                    "(ih : is_whnf (to_kexpr r0 rho) -> ",
                    "whnf_to (to_kexpr (impl_instantiate b v) rho) (to_kexpr r0 rho)) ",
                    "(hw : is_whnf (to_kexpr r0 rho)) => ",
                    "whnf_to.step ",
                    "(KExpr.let_ (to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at v rho Nat.zero)) ",
                    "(to_kexpr r0 rho) ",
                    "(whnf_step.beta ",
                    "(KExpr.let_ (to_kexpr_at ty rho Nat.zero) (to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero))) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at v rho Nat.zero)) ",
                    "(beta_reduces.zeta (to_kexpr_at ty rho Nat.zero) ",
                    "(to_kexpr_at v rho Nat.zero) ",
                    "(to_kexpr_at b rho (Nat.succ Nat.zero)))) ",
                    "(Eq.substType KExpr ",
                    "(fun (w : KExpr) => whnf_to w (to_kexpr r0 rho)) ",
                    "(to_kexpr (impl_instantiate b v) rho) ",
                    "(instantiate (to_kexpr_at b rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at v rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho v b Nat.zero) (ih hw))) ",
                    // mdataStep — the translation erases mdata, so both sides
                    // are already the inner term's and the IH is the whole proof.
                    "(fun (e0 : ImplExpr) (r0 : ImplExpr) (_hp : ImplWhnfTo e0 r0) ",
                    "(ih : is_whnf (to_kexpr r0 rho) -> ",
                    "whnf_to (to_kexpr e0 rho) (to_kexpr r0 rho)) => ih) ",
                    "e r h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The SHARPER companion of impl_whnf_to_defeq: layer-1 weak-head reduction is ",
                "layer-2 WEAK-HEAD REDUCTION, not merely definitional equality of the ",
                "endpoints. Why it is worth having when impl_whnf_to_defeq already unblocks ",
                "M4: DefEq is what TypingCtxConv.conv consumes, and conv is UNRESTRICTED, so a ",
                "type reached through it is some member of the conversion class rather than ",
                "the type the checker returned. whnf_to is what KernelInfers.app and .let_ take ",
                "as witnessed premises, so this is the lemma a KernelInfers-codomain bridge ",
                "needs — the difference between \"the result is def-equal to something ",
                "well-typed\" and \"the checker's reduction step was correct\". ",
                "The is_whnf hypothesis is FORCED, not defensive: ImplWhnfTo.done is ",
                "unrestricted reflexivity (it holds at every ImplExpr — the over-approximation ",
                "impl_whnf_to_defeq's own comment records) while whnf_to.refl demands is_whnf, ",
                "so without it the done arm is unprovable. It is free at every use site, where ",
                "the reduct's shape is known: a Pi at the App rule, a Sort at ensure_sort. ",
                "Proved by ImplWhnfTo.rec with the motive carrying the hypothesis, so each arm ",
                "receives it: done is whnf_to.refl; beta and zeta are one whnf_step.beta over ",
                "beta_reduces.beta / beta_reduces.zeta followed by the IH, with ",
                "to_kexpr_at_instantiate the only transport (the translation must turn ",
                "impl_instantiate into instantiate before the layer-2 rules apply on the nose); ",
                "mdataStep is the IH because the translation erases mdata. ",
                "SCOPE, unchanged and not silently widened: ImplWhnfTo covers only the env-free ",
                "fragment (done/beta/zeta/mdata) — delta, iota, proj and eta need the ",
                "environment and remain Phase-B width. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplWhnfTo.rec".to_string(),
                "whnf_to.refl".to_string(),
                "whnf_to.step".to_string(),
                "whnf_step.beta".to_string(),
                "beta_reduces.beta".to_string(),
                "beta_reduces.zeta".to_string(),
                "is_whnf".to_string(),
                "to_kexpr_at_instantiate".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ImplIsLe -> DefEq. Small, but it is the OTHER owed theorem, and it is
        // what the App-argument and Let-value ascription points need.
        self.add_definition(SpecDefinition {
            name: "impl_is_le_defeq".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (x : ImplExpr) (y : ImplExpr), ",
                "ImplIsLe x y -> DefEq (to_kexpr x rho) (to_kexpr y rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (x : ImplExpr) (y : ImplExpr) ",
                    "(h : ImplIsLe x y) => ",
                    "ImplIsLe.rec ",
                    "(fun (x0 : ImplExpr) (y0 : ImplExpr) (_h0 : ImplIsLe x0 y0) => ",
                    "DefEq (to_kexpr x0 rho) (to_kexpr y0 rho)) ",
                    "(fun (e0 : ImplExpr) => DefEq.refl (to_kexpr e0 rho)) ",
                    // whnfL: a ->whnf r, r <= b.
                    "(fun (a0 : ImplExpr) (b0 : ImplExpr) (r0 : ImplExpr) ",
                    "(hw : ImplWhnfTo a0 r0) (_hl : ImplIsLe r0 b0) ",
                    "(ih : DefEq (to_kexpr r0 rho) (to_kexpr b0 rho)) => ",
                    "DefEq.trans (to_kexpr a0 rho) (to_kexpr r0 rho) (to_kexpr b0 rho) ",
                    "(impl_whnf_to_defeq rho a0 r0 hw) ih) ",
                    // whnfR: b ->whnf r, a <= r. Needs symm, because the
                    // reduction runs on the RIGHT operand.
                    "(fun (a0 : ImplExpr) (b0 : ImplExpr) (r0 : ImplExpr) ",
                    "(hw : ImplWhnfTo b0 r0) (_hl : ImplIsLe a0 r0) ",
                    "(ih : DefEq (to_kexpr a0 rho) (to_kexpr r0 rho)) => ",
                    "DefEq.trans (to_kexpr a0 rho) (to_kexpr r0 rho) (to_kexpr b0 rho) ",
                    "ih (DefEq.symm (to_kexpr b0 rho) (to_kexpr r0 rho) ",
                    "(impl_whnf_to_defeq rho b0 r0 hw))) ",
                    "x y h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "OWED SOUNDNESS THEOREM #2, discharged. ImplIsLe models the `is_le` check the ",
                "release App-argument (tc/infer.rs:474) and Let-value (:617) ascription points ",
                "perform, and its registration records the same debt as ImplWhnfTo's. This ",
                "discharges it: layer-1 `is_le` implies layer-2 definitional equality on the ",
                "translated terms. ",
                "Proved by ImplIsLe.rec over three arms. `refl` is DefEq.refl; `whnfL` composes ",
                "impl_whnf_to_defeq with the IH; `whnfR` needs DefEq.symm as well, because ",
                "there the reduction runs on the RIGHT operand — the asymmetry is in the ",
                "relation, not in the proof. ",
                "SCOPE: ImplIsLe is modelled as the reflexive, whnf-closed fragment of is_le. ",
                "Congruence, eta, proof irrelevance and universe cumulativity are Phase-B width ",
                "and are named as residuals at the relation itself; nothing here widens that. ",
                "Note what the conclusion is: DefEq, i.e. EQUALITY, not a subtyping relation. ",
                "That is faithful to the modelled fragment (is_le == is_def_eq unless the Coq ",
                "cumulative lane is enabled) and is exactly what TypingCtxConv.conv consumes. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplIsLe.rec".to_string(),
                "impl_whnf_to_defeq".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The App arm into KernelInfers — the STRONGER codomain.
        //
        // M4 bridges every rule into TypingCtxConv, and that is a genuine
        // soundness theorem. But TypingCtxConv.conv is unrestricted and its app
        // arm carries neither a whnf_to nor a DefEq premise, so a derivation
        // there does not pin the type the checker RETURNED, nor witness that the
        // reduction and the subtype check were performed correctly.
        // KernelInfers.app carries both as witnessed fields — and it turns out
        // ImplInfer.app matches it premise-for-premise:
        //
        //     ImplInfer.app        KernelInfers.app
        //     ImplWhnfTo F (pi …)  whnf_to F (KExpr.pi A B)   <- impl_whnf_to_whnf_to
        //     ImplIsLe A2 A        DefEq A' A                 <- impl_is_le_defeq
        //
        // so this arm needs NO conv step and NO layer-2 change: both operational
        // premises land as themselves. The two recursive KernelInfers facts are
        // taken as hypotheses, exactly as the impl_bridge_* arms take theirs;
        // assembling them into a whole-relation induction is a separate step.
        //
        // The `is_whnf` obligation impl_whnf_to_whnf_to carries is discharged
        // here for free: the reduct is literally a Pi, so `is_whnf.pi` applies.
        // That is why the hypothesis was worth stating rather than avoiding.
        self.add_definition(SpecDefinition {
            name: "impl_kinfers_app".to_string(),
            type_src: concat!(
                "forall (tenvK : Name -> OptionType KExpr) (rho : ListType Nat) ",
                "(Gk : ListType KExpr) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) ",
                "(bd : BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr), ",
                "KernelInfers tenvK Gk (to_kexpr f rho) (to_kexpr F rho) -> ",
                "ImplWhnfTo F (ImplExpr.pi bd A B) -> ",
                "KernelInfers tenvK Gk (to_kexpr a rho) (to_kexpr A2 rho) -> ",
                "ImplIsLe A2 A -> ",
                "KernelInfers tenvK Gk (to_kexpr (ImplExpr.app f a) rho) ",
                "(to_kexpr (impl_instantiate B a) rho)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenvK : Name -> OptionType KExpr) (rho : ListType Nat) ",
                    "(Gk : ListType KExpr) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) ",
                    "(bd : BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr) ",
                    "(hf : KernelInfers tenvK Gk (to_kexpr f rho) (to_kexpr F rho)) ",
                    "(hw : ImplWhnfTo F (ImplExpr.pi bd A B)) ",
                    "(ha : KernelInfers tenvK Gk (to_kexpr a rho) (to_kexpr A2 rho)) ",
                    "(hle : ImplIsLe A2 A) => ",
                    // The conclusion's type is `to_kexpr (impl_instantiate B a) rho`;
                    // KernelInfers.app produces the `instantiate` form. The
                    // translation lemma is the only transport needed.
                    "Eq.substType KExpr ",
                    "(fun (w : KExpr) => KernelInfers tenvK Gk ",
                    "(KExpr.app (to_kexpr_at f rho Nat.zero) (to_kexpr_at a rho Nat.zero)) w) ",
                    "(instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr (impl_instantiate B a) rho) ",
                    "(Eq.symm KExpr (to_kexpr (impl_instantiate B a) rho) ",
                    "(instantiate (to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a rho Nat.zero)) ",
                    "(to_kexpr_at_instantiate rho a B Nat.zero)) ",
                    "(KernelInfers.app tenvK Gk ",
                    "(to_kexpr_at f rho Nat.zero) (to_kexpr_at a rho Nat.zero) ",
                    "(to_kexpr F rho) ",
                    "(to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero)) ",
                    "(to_kexpr A2 rho) ",
                    "hf ",
                    "(impl_whnf_to_whnf_to rho F (ImplExpr.pi bd A B) hw ",
                    "(is_whnf.pi (to_kexpr_at A rho Nat.zero) ",
                    "(to_kexpr_at B rho (Nat.succ Nat.zero)))) ",
                    "ha ",
                    "(impl_is_le_defeq rho A2 A hle))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The App rule bridged into KernelInfers — the codomain that PINS what M4's ",
                "TypingCtxConv codomain cannot. TypingCtxConv.conv is unrestricted and its app ",
                "arm carries neither a whnf_to nor a DefEq premise, so a derivation there says ",
                "the result is convertible to something well-typed; it does not say the checker ",
                "returned this type, nor that the reduction and subtype check were correct. ",
                "KernelInfers.app carries both as WITNESSED fields, and ImplInfer.app matches it ",
                "premise-for-premise: ImplWhnfTo F (pi ...) maps to whnf_to F (KExpr.pi A B) by ",
                "impl_whnf_to_whnf_to, and ImplIsLe A2 A maps to DefEq A' A by impl_is_le_defeq. ",
                "So this arm needs NO conv step and NO layer-2 change — both operational ",
                "premises land as themselves, which is the whole point. ",
                "impl_whnf_to_whnf_to's is_whnf obligation is discharged for free here: the ",
                "reduct is literally a Pi, so is_whnf.pi applies — the hypothesis was worth ",
                "stating rather than designing around. to_kexpr_at_instantiate is the only ",
                "transport, converting the arm's impl_instantiate conclusion into the ",
                "instantiate form KernelInfers.app produces; note the codomain is translated at ",
                "depth ONE because it sits under the Pi binder. ",
                "SCOPE, stated as a fraction: this is ONE arm. The two recursive KernelInfers ",
                "facts are hypotheses, exactly as the impl_bridge_* arms take theirs; ",
                "assembling the arms into a whole-relation induction with KernelInfers as ",
                "codomain is a separate step, and lam/pi remain blocked until KernelInfers' own ",
                "lam/pi arms are restated in the whnf idiom its let_ arm already uses. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KernelInfers.app".to_string(),
                "impl_whnf_to_whnf_to".to_string(),
                "impl_is_le_defeq".to_string(),
                "to_kexpr_at_instantiate".to_string(),
                "is_whnf.pi".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// `to_kexpr_at (impl_lift_at e k c) rho (k+c) = lift_at (to_kexpr_at e rho k) k c`.
    fn add_to_kexpr_at_lift(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "to_kexpr_at_lift".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (c : Nat) (e : ImplExpr) (k : Nat), ",
                "Eq KExpr ",
                lhs!("e", "k"),
                " ",
                rhs!("e", "k")
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (c : Nat) (e : ImplExpr) => ",
                    "ImplExpr.rec ",
                    // motive — k generalised, rho and c fixed.
                    "(fun (z : ImplExpr) => forall (k : Nat), Eq KExpr ",
                    lhs!("z", "k"),
                    " ",
                    rhs!("z", "k"),
                    ") ",
                    // ── bvar ────────────────────────────────────────────────
                    // Both sides are the SAME Nat.rec on Nat.sub k i, so the
                    // split is one Nat.rec and each branch is Eq.refl. The
                    // motive re-abstracts that shared scrutinee.
                    "(fun (i : Nat) (k : Nat) => ",
                    "Nat.rec (fun (s : Nat) => Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.add i c)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) rho (Nat.add k c)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) (KExpr.bvar (Nat.add i c)) ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) s)) ",
                    "(Eq.refl KExpr (KExpr.bvar (Nat.add i c))) ",
                    "(fun (_s : Nat) (_ih : Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(ImplExpr.bvar (Nat.add i c)) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) _s) rho (Nat.add k c)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) (KExpr.bvar (Nat.add i c)) ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) _s)) => ",
                    "Eq.refl KExpr (KExpr.bvar i)) ",
                    "(Nat.sub k i)) ",
                    // ── fvar — the asymmetric case ──────────────────────────
                    // Layer 1: a leaf. Layer 2: bvar (rho_index + k), which is
                    // >= k and so DOES lift. They meet at rho_index + k + c.
                    "(fun (y : Nat) (k : Nat) => ",
                    "Eq.substType Nat ",
                    "(fun (s : Nat) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (rho_index rho y) (Nat.add k c))) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add (Nat.add (rho_index rho y) k) c)) ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar (Nat.add (rho_index rho y) k)) s)) ",
                    "Nat.zero (Nat.sub k (Nat.add (rho_index rho y) k)) ",
                    // k <= rho_index + k, so the lift fires: sub k (r+k) = 0.
                    "(Eq.symm Nat (Nat.sub k (Nat.add (rho_index rho y) k)) Nat.zero ",
                    "(Eq.trans Nat (Nat.sub k (Nat.add (rho_index rho y) k)) ",
                    "(Nat.sub k (Nat.add k (rho_index rho y))) Nat.zero ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.sub k w) ",
                    "(Nat.add (rho_index rho y) k) (Nat.add k (rho_index rho y)) ",
                    "(nat_add_comm (rho_index rho y) k)) ",
                    "(nat_sub_self_add_zero k (rho_index rho y)))) ",
                    // ...and then it is pure associativity.
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add (rho_index rho y) (Nat.add k c)) ",
                    "(Nat.add (Nat.add (rho_index rho y) k) c) ",
                    "(Eq.symm Nat (Nat.add (Nat.add (rho_index rho y) k) c) ",
                    "(Nat.add (rho_index rho y) (Nat.add k c)) ",
                    "(nat_add_assoc (rho_index rho y) k c)))) ",
                    // ── sort / const — translation-inert leaves ─────────────
                    "(fun (l : Level) (k : Nat) => Eq.refl KExpr (KExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (k : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // ── app ─────────────────────────────────────────────────
                    "(fun (f : ImplExpr) (a : ImplExpr) ",
                    "(rf : forall (k : Nat), Eq KExpr ",
                    lhs!("f", "k"),
                    " ",
                    rhs!("f", "k"),
                    ") ",
                    "(ra : forall (k : Nat), Eq KExpr ",
                    lhs!("a", "k"),
                    " ",
                    rhs!("a", "k"),
                    ") (k : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.app ",
                    lhs!("f", "k"),
                    " ",
                    lhs!("a", "k"),
                    ") ",
                    "(KExpr.app ",
                    rhs!("f", "k"),
                    " ",
                    lhs!("a", "k"),
                    ") ",
                    "(KExpr.app ",
                    rhs!("f", "k"),
                    " ",
                    rhs!("a", "k"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w ",
                    lhs!("a", "k"),
                    ") ",
                    lhs!("f", "k"),
                    " ",
                    rhs!("f", "k"),
                    " (rf k)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app ",
                    rhs!("f", "k"),
                    " w) ",
                    lhs!("a", "k"),
                    " ",
                    rhs!("a", "k"),
                    " (ra k))) ",
                    // ── lam — the binder case, where the depth bookkeeping bites
                    // The body IH arrives at depth `Nat.add (Nat.succ k) c`; the
                    // goal needs `Nat.succ (Nat.add k c)`. Nat.add recurses on
                    // its SECOND argument, so those are NOT definitionally equal
                    // and nat_succ_add has to transport it.
                    "(fun (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) ",
                    "(rt : forall (k : Nat), Eq KExpr ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    ") ",
                    "(rb : forall (k : Nat), Eq KExpr ",
                    lhs!("b", "k"),
                    " ",
                    rhs!("b", "k"),
                    ") (k : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.lam ",
                    lhs!("ty", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.lam ",
                    rhs!("ty", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.lam ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    " (rt k)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam ",
                    rhs!("ty", "k"),
                    " w) ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c))) ",
                    rhs!("b", "(Nat.succ k)"),
                    " ",
                    "(Eq.substType Nat (fun (dd : Nat) => Eq KExpr ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho dd) ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Nat.add (Nat.succ k) c) (Nat.succ (Nat.add k c)) ",
                    "(nat_succ_add k c) (rb (Nat.succ k))))) ",
                    // ── pi — identical shape to lam ─────────────────────────
                    "(fun (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) ",
                    "(rt : forall (k : Nat), Eq KExpr ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    ") ",
                    "(rb : forall (k : Nat), Eq KExpr ",
                    lhs!("b", "k"),
                    " ",
                    rhs!("b", "k"),
                    ") (k : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.pi ",
                    lhs!("ty", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.pi ",
                    rhs!("ty", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.pi ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    " (rt k)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi ",
                    rhs!("ty", "k"),
                    " w) ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c))) ",
                    rhs!("b", "(Nat.succ k)"),
                    " ",
                    "(Eq.substType Nat (fun (dd : Nat) => Eq KExpr ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho dd) ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Nat.add (Nat.succ k) c) (Nat.succ (Nat.add k c)) ",
                    "(nat_succ_add k c) (rb (Nat.succ k))))) ",
                    // ── let_ — three subterms, only the body under a binder ──
                    "(fun (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) ",
                    "(rt : forall (k : Nat), Eq KExpr ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    ") ",
                    "(rv : forall (k : Nat), Eq KExpr ",
                    lhs!("v", "k"),
                    " ",
                    rhs!("v", "k"),
                    ") ",
                    "(rb : forall (k : Nat), Eq KExpr ",
                    lhs!("b", "k"),
                    " ",
                    rhs!("b", "k"),
                    ") (k : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.let_ ",
                    lhs!("ty", "k"),
                    " ",
                    lhs!("v", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    lhs!("v", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("v", "k"),
                    " ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w ",
                    lhs!("v", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    lhs!("ty", "k"),
                    " ",
                    rhs!("ty", "k"),
                    " (rt k)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    lhs!("v", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("v", "k"),
                    " (to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    "(KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("v", "k"),
                    " ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    rhs!("ty", "k"),
                    " w ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c)))) ",
                    lhs!("v", "k"),
                    " ",
                    rhs!("v", "k"),
                    " (rv k)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    rhs!("ty", "k"),
                    " ",
                    rhs!("v", "k"),
                    " w) ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho (Nat.succ (Nat.add k c))) ",
                    rhs!("b", "(Nat.succ k)"),
                    " ",
                    "(Eq.substType Nat (fun (dd : Nat) => Eq KExpr ",
                    "(to_kexpr_at (impl_lift_at b (Nat.succ k) c) rho dd) ",
                    rhs!("b", "(Nat.succ k)"),
                    ") ",
                    "(Nat.add (Nat.succ k) c) (Nat.succ (Nat.add k c)) ",
                    "(nat_succ_add k c) (rb (Nat.succ k)))))) ",
                    // ── lit — a leaf on both sides, but NOT by Eq.refl ──────
                    // `impl_lit_to_kexpr lt` is stuck on the variable `lt` (it
                    // is an ImplLit.rec application), so layer 2's `lift_at`
                    // cannot iota-reduce past it and the two sides are not
                    // definitionally equal until `lt` is a constructor. Hence
                    // the split; both arms then land on `KExpr.lit n`, which
                    // `lift_at` does discard. (`sort`/`const` need no split —
                    // their translations are already constructor-headed.)
                    "(fun (lt : ImplLit) (k : Nat) => ",
                    "ImplLit.rec (fun (z : ImplLit) => Eq KExpr (impl_lit_to_kexpr z) ",
                    "(lift_at (impl_lit_to_kexpr z) k c)) ",
                    "(fun (n : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                    "(fun (n : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                    "lt) ",
                    // ── mdata — ERASED by the translation, so the IH is the
                    // whole proof: both sides reduce to the inner term's.
                    "(fun (inner : ImplExpr) ",
                    "(ri : forall (k : Nat), Eq KExpr ",
                    lhs!("inner", "k"),
                    " ",
                    rhs!("inner", "k"),
                    ") (k : Nat) => ri k) ",
                    "e"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 KEYSTONE — the layer-1/layer-2 LIFT COMMUTATION lemma: translating a ",
                "lifted ImplExpr at depth k+c is the same as lifting its translation at depth ",
                "k. Both of M4's remaining prerequisites need it, because the substitution ",
                "helpers on BOTH sides substitute a LIFTED value (instantiate_bvar_geq uses ",
                "`lift_at val 0 depth`, impl_inst_bvar_geq uses `impl_lift_at val 0 depth`), ",
                "so the hit case of the substitution commutation lemma is an instance of this ",
                "one. ",
                "THE CUTOFF IS GENERALISED BECAUSE THE DEPTH-0 INSTANCE IS NOT INDUCTIVE: ",
                "under a binder the cutoff becomes `succ k` while the translation depth becomes ",
                "`succ (k + c)`, so the IH is needed at every cutoff. ",
                "Two cases carry all the content and they are asymmetric. `bvar`: layer 1 and ",
                "layer 2 run the SAME three-way comparison on `Nat.sub cutoff idx`, so one ",
                "Nat.rec on that shared scrutinee closes both branches by Eq.refl. `fvar`: ",
                "layer 1 treats it as a LEAF (free variables are never lifted) while layer 2 ",
                "has already turned it into `bvar (rho_index + k)`, which IS lifted — they ",
                "agree only via `nat_sub_self_add_zero` (the lift fires) and `nat_add_assoc` ",
                "(it lands on the same index). That asymmetry is exactly why layer 2's own ",
                "lift theory cannot be reused and a translation lemma is needed. ",
                "The binder arms transport the body IH along `nat_succ_add` because Nat.add ",
                "recurses on its SECOND argument, so `Nat.add (succ k) c` and ",
                "`Nat.succ (Nat.add k c)` are propositionally but not definitionally equal. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplExpr.rec".to_string(),
                "to_kexpr_at".to_string(),
                "impl_lift_at".to_string(),
                "lift_at".to_string(),
                "rho_index".to_string(),
                "nat_add_assoc".to_string(),
                "nat_add_comm".to_string(),
                "nat_sub_self_add_zero".to_string(),
                "nat_succ_add".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// `to_kexpr_at (impl_instantiate_at b a d) rho d`
    /// `= instantiate_at (to_kexpr_at b rho (succ d)) (to_kexpr_at a rho 0) d`.
    ///
    /// The lemma C4's header names as missing for the `app` rule, stated with
    /// the depth generalised so it carries its own induction through binders.
    ///
    /// Note where the substituted value is translated: at depth **zero**, not
    /// at `d`. That is forced, not stylistic — the hit case must line up with
    /// `to_kexpr_at_lift`, whose right-hand side is `lift_at (… rho 0) 0 c`. A
    /// version stating the value at depth `d` would double-count the depth on
    /// every free variable inside it and is simply false.
    fn add_to_kexpr_at_instantiate(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "to_kexpr_at_instantiate".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (a : ImplExpr) (b : ImplExpr) (d : Nat), ",
                "Eq KExpr ",
                ilhs!("b", "d"),
                " ",
                irhs!("b", "d")
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (a : ImplExpr) (b : ImplExpr) => ",
                    "ImplExpr.rec ",
                    "(fun (z : ImplExpr) => forall (d : Nat), Eq KExpr ",
                    ilhs!("z", "d"),
                    " ",
                    irhs!("z", "d"),
                    ") ",
                    // ── bvar — a NESTED split, because both helpers are two
                    // nested three-way comparisons and layer 1 / layer 2 share
                    // both scrutinees (`Nat.sub d i` then `Nat.sub i d`).
                    "(fun (i : Nat) (d : Nat) => ",
                    "Nat.rec (fun (s : Nat) => Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_inst_bvar_geq i d a) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) s) rho d) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(instantiate_bvar_geq i d ",
                    "(to_kexpr_at a rho Nat.zero)",
                    ") ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) s)) ",
                    // s = 0, i.e. i >= d: descend into the geq helpers.
                    "(Nat.rec (fun (t : Nat) => Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_lift_at a Nat.zero d) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ",
                    "ImplExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) t) rho d) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(lift_at ",
                    "(to_kexpr_at a rho Nat.zero)",
                    " Nat.zero d) ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) t)) ",
                    // t = 0, i.e. i == d: THE HIT CASE — an instance of the
                    // keystone, modulo `Nat.add Nat.zero d` vs `d` (Nat.add
                    // recurses on its second argument, so that is a transport,
                    // not a reduction).
                    "(Eq.substType Nat (fun (dd : Nat) => Eq KExpr ",
                    "(to_kexpr_at (impl_lift_at a Nat.zero d) rho dd) ",
                    "(lift_at ",
                    "(to_kexpr_at a rho Nat.zero)",
                    " Nat.zero d)) ",
                    "(Nat.add Nat.zero d) d (nat_zero_add d) ",
                    "(to_kexpr_at_lift rho d a Nat.zero)) ",
                    // t = succ _, i.e. i > d: both sides decrement identically.
                    "(fun (_t : Nat) (_iht : Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_lift_at a Nat.zero d) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ",
                    "ImplExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) _t) rho d) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(lift_at ",
                    "(to_kexpr_at a rho Nat.zero)",
                    " Nat.zero d) ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) _t)) => ",
                    "Eq.refl KExpr (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))) ",
                    "(Nat.sub i d)) ",
                    // s = succ _, i.e. i < d: untouched on both sides.
                    "(fun (_s : Nat) (_ihs : Eq KExpr ",
                    "(to_kexpr_at (Nat.rec (fun (_m : Nat) => ImplExpr) ",
                    "(impl_inst_bvar_geq i d a) ",
                    "(fun (_q : Nat) (_r : ImplExpr) => ImplExpr.bvar i) _s) rho d) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(instantiate_bvar_geq i d ",
                    "(to_kexpr_at a rho Nat.zero)",
                    ") ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) _s)) => ",
                    "Eq.refl KExpr (KExpr.bvar i)) ",
                    "(Nat.sub d i)) ",
                    // ── fvar — layer 1 leaves it alone; layer 2 has already
                    // turned it into `bvar (r + succ d)`, which is ABOVE the
                    // substitution depth, so layer 2 decrements it. The two meet
                    // at `r + d` only after both scrutinees are pinned.
                    "(fun (y : Nat) (d : Nat) => ",
                    // 1. the outer comparison: d <= succ (r + d), so we are in
                    //    the geq branch.
                    "Eq.substType Nat (fun (s : Nat) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (rho_index rho y) d)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(instantiate_bvar_geq (Nat.succ (Nat.add (rho_index rho y) d)) d ",
                    "(to_kexpr_at a rho Nat.zero)",
                    ") ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.succ (Nat.add (rho_index rho y) d))) s)) ",
                    "Nat.zero (Nat.sub d (Nat.succ (Nat.add (rho_index rho y) d))) ",
                    "(Eq.symm Nat (Nat.sub d (Nat.succ (Nat.add (rho_index rho y) d))) Nat.zero ",
                    "(Eq.trans Nat (Nat.sub d (Nat.succ (Nat.add (rho_index rho y) d))) ",
                    "(Nat.sub d (Nat.add d (Nat.succ (rho_index rho y)))) Nat.zero ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.sub d w) ",
                    "(Nat.succ (Nat.add (rho_index rho y) d)) ",
                    "(Nat.add d (Nat.succ (rho_index rho y))) ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) ",
                    "(Nat.add (rho_index rho y) d) (Nat.add d (rho_index rho y)) ",
                    "(nat_add_comm (rho_index rho y) d))) ",
                    "(nat_sub_self_add_zero d (Nat.succ (rho_index rho y))))) ",
                    // 2. the inner comparison: succ (r + d) - d = succ r, a
                    //    SUCC, so we are in the decrement branch, not the
                    //    substitute branch. This is what makes the fvar case
                    //    independent of `a` entirely.
                    "(Eq.substType Nat (fun (t : Nat) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (rho_index rho y) d)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(lift_at ",
                    "(to_kexpr_at a rho Nat.zero)",
                    " Nat.zero d) ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) ",
                    "(Nat.succ Nat.zero))) t)) ",
                    "(Nat.succ (rho_index rho y)) ",
                    "(Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) d) ",
                    "(Eq.symm Nat (Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) d) ",
                    "(Nat.succ (rho_index rho y)) ",
                    "(Eq.trans Nat (Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) d) ",
                    "(Nat.sub (Nat.add d (Nat.succ (rho_index rho y))) d) ",
                    "(Nat.succ (rho_index rho y)) ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.sub w d) ",
                    "(Nat.succ (Nat.add (rho_index rho y) d)) ",
                    "(Nat.add d (Nat.succ (rho_index rho y))) ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) ",
                    "(Nat.add (rho_index rho y) d) (Nat.add d (rho_index rho y)) ",
                    "(nat_add_comm (rho_index rho y) d))) ",
                    "(nat_sub_add_left_cancel d (Nat.succ (rho_index rho y))))) ",
                    // 3. and the decremented index is r + d again:
                    //    succ (r+d) - 1 = r + d.
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add (rho_index rho y) d) ",
                    "(Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) (Nat.succ Nat.zero)) ",
                    "(Eq.symm Nat ",
                    "(Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) (Nat.succ Nat.zero)) ",
                    "(Nat.add (rho_index rho y) d) ",
                    "(Eq.trans Nat ",
                    "(Nat.sub (Nat.succ (Nat.add (rho_index rho y) d)) (Nat.succ Nat.zero)) ",
                    "(Nat.sub (Nat.add (rho_index rho y) d) Nat.zero) ",
                    "(Nat.add (rho_index rho y) d) ",
                    "(nat_sub_succ_succ (Nat.add (rho_index rho y) d) Nat.zero) ",
                    "(nat_sub_zero_right (Nat.add (rho_index rho y) d))))))) ",
                    // ── sort / const ────────────────────────────────────────
                    "(fun (l : Level) (d : Nat) => Eq.refl KExpr (KExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // ── app ─────────────────────────────────────────────────
                    "(fun (f : ImplExpr) (aa : ImplExpr) ",
                    "(rf : forall (d : Nat), Eq KExpr ",
                    ilhs!("f", "d"),
                    " ",
                    irhs!("f", "d"),
                    ") ",
                    "(ra : forall (d : Nat), Eq KExpr ",
                    ilhs!("aa", "d"),
                    " ",
                    irhs!("aa", "d"),
                    ") (d : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.app ",
                    ilhs!("f", "d"),
                    " ",
                    ilhs!("aa", "d"),
                    ") ",
                    "(KExpr.app ",
                    irhs!("f", "d"),
                    " ",
                    ilhs!("aa", "d"),
                    ") ",
                    "(KExpr.app ",
                    irhs!("f", "d"),
                    " ",
                    irhs!("aa", "d"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w ",
                    ilhs!("aa", "d"),
                    ") ",
                    ilhs!("f", "d"),
                    " ",
                    irhs!("f", "d"),
                    " (rf d)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app ",
                    irhs!("f", "d"),
                    " w) ",
                    ilhs!("aa", "d"),
                    " ",
                    irhs!("aa", "d"),
                    " (ra d))) ",
                    // ── lam — NO arithmetic transport, unlike the lift lemma.
                    // Both sides step the depth to `Nat.succ d` directly, so the
                    // body IH at `Nat.succ d` is the body goal on the nose.
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq KExpr ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    ") ",
                    "(rb : forall (d : Nat), Eq KExpr ",
                    ilhs!("bb", "d"),
                    " ",
                    irhs!("bb", "d"),
                    ") (d : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.lam ",
                    ilhs!("ty", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.lam ",
                    irhs!("ty", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.lam ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    " (rt d)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam ",
                    irhs!("ty", "d"),
                    " w) ",
                    ilhs!("bb", "(Nat.succ d)"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    " (rb (Nat.succ d)))) ",
                    // ── pi ──────────────────────────────────────────────────
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq KExpr ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    ") ",
                    "(rb : forall (d : Nat), Eq KExpr ",
                    ilhs!("bb", "d"),
                    " ",
                    irhs!("bb", "d"),
                    ") (d : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.pi ",
                    ilhs!("ty", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.pi ",
                    irhs!("ty", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.pi ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    " (rt d)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi ",
                    irhs!("ty", "d"),
                    " w) ",
                    ilhs!("bb", "(Nat.succ d)"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    " (rb (Nat.succ d)))) ",
                    // ── let_ ────────────────────────────────────────────────
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) ",
                    "(rt : forall (d : Nat), Eq KExpr ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    ") ",
                    "(rv : forall (d : Nat), Eq KExpr ",
                    ilhs!("vv", "d"),
                    " ",
                    irhs!("vv", "d"),
                    ") ",
                    "(rb : forall (d : Nat), Eq KExpr ",
                    ilhs!("bb", "d"),
                    " ",
                    irhs!("bb", "d"),
                    ") (d : Nat) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.let_ ",
                    ilhs!("ty", "d"),
                    " ",
                    ilhs!("vv", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    ilhs!("vv", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("vv", "d"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w ",
                    ilhs!("vv", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    ilhs!("ty", "d"),
                    " ",
                    irhs!("ty", "d"),
                    " (rt d)) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    ilhs!("vv", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("vv", "d"),
                    " ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("vv", "d"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    ") ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    irhs!("ty", "d"),
                    " w ",
                    ilhs!("bb", "(Nat.succ d)"),
                    ") ",
                    ilhs!("vv", "d"),
                    " ",
                    irhs!("vv", "d"),
                    " (rv d)) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    irhs!("ty", "d"),
                    " ",
                    irhs!("vv", "d"),
                    " w) ",
                    ilhs!("bb", "(Nat.succ d)"),
                    " ",
                    irhs!("bb", "(Nat.succ d)"),
                    " (rb (Nat.succ d))))) ",
                    // ── lit — the same stuck-scrutinee split as the keystone.
                    "(fun (lt : ImplLit) (d : Nat) => ",
                    "ImplLit.rec (fun (z : ImplLit) => Eq KExpr (impl_lit_to_kexpr z) ",
                    "(instantiate_at (impl_lit_to_kexpr z) ",
                    "(to_kexpr_at a rho Nat.zero)",
                    " d)) ",
                    "(fun (n : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                    "(fun (n : Nat) => Eq.refl KExpr (KExpr.lit n)) ",
                    "lt) ",
                    // ── mdata — erased by the translation on both sides ──────
                    "(fun (inner : ImplExpr) ",
                    "(ri : forall (d : Nat), Eq KExpr ",
                    ilhs!("inner", "d"),
                    " ",
                    irhs!("inner", "d"),
                    ") (d : Nat) => ri d) ",
                    "b"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4 — the layer-1/layer-2 SUBSTITUTION COMMUTATION lemma, named in ctx_rep.rs's ",
                "coverage table as one of the three things the `app` rule needs and which \"none ",
                "exist yet\". Translating a layer-1 instantiation equals instantiating the ",
                "translation, with the body translated one binder deeper. ",
                "THE VALUE IS TRANSLATED AT DEPTH ZERO, NOT AT d, and that is forced rather ",
                "than stylistic: the hit case has to line up with to_kexpr_at_lift, whose ",
                "right-hand side is `lift_at (... rho Nat.zero) Nat.zero c`. Stating the value ",
                "at depth d would double-count the depth on every free variable inside it — the ",
                "resulting statement is not merely harder, it is FALSE. ",
                "Structure: induction on the body with the depth generalised. The bvar case is a ",
                "NESTED Nat.rec, because both sides run the same two comparisons (`Nat.sub d i` ",
                "then `Nat.sub i d`) — layer 1's impl_inst_bvar_at/_geq are transcriptions of ",
                "layer 2's instantiate_bvar_at/_geq — so three of the four leaves are Eq.refl ",
                "and the fourth (i == d) is exactly to_kexpr_at_lift, transported along ",
                "nat_zero_add. The fvar case is where the layers genuinely disagree: layer 1 ",
                "leaves a free variable alone, while layer 2 has already turned it into ",
                "`bvar (rho_index + succ d)` — ABOVE the substitution depth — and so DECREMENTS ",
                "it; pinning both scrutinees (nat_sub_self_add_zero, then ",
                "nat_sub_add_left_cancel) shows the decrement lands back on `rho_index + d`, ",
                "and in particular that the case never touches the substituted value at all. ",
                "Unlike the lift lemma the binder arms need NO arithmetic transport, because ",
                "both sides step the depth to `Nat.succ d` directly. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplExpr.rec".to_string(),
                "to_kexpr_at".to_string(),
                "to_kexpr_at_lift".to_string(),
                "impl_instantiate_at".to_string(),
                "instantiate_at".to_string(),
                "impl_inst_bvar_geq".to_string(),
                "instantiate_bvar_geq".to_string(),
                "nat_zero_add".to_string(),
                "nat_add_comm".to_string(),
                "nat_sub_self_add_zero".to_string(),
                "nat_sub_add_left_cancel".to_string(),
                "nat_sub_succ_succ".to_string(),
                "nat_sub_zero_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The coverage guard: which `ImplInfer` derivations M4 speaks about, and
    /// the scoping each of their rules needs — computed FROM the derivation.
    ///
    /// Defined by `ImplInfer.rec` into `Type`, so it is not a comment about
    /// coverage but a function of the derivation: `Empty` at `lit`, `ImplUnit`
    /// at the leaves, and at every recursive rule the conjunction of that rule's
    /// scoping side conditions with its children's guards.
    ///
    /// This is what makes "7 of 9, and 7 is the ceiling" checkable rather than
    /// asserted, and it is exactly what the assembled theorem will consume: the
    /// guard iota-reduces at each constructor, so a minor projects its
    /// children's guards out with `AndType.left` / `AndType.right` and feeds
    /// them to the induction hypotheses.
    fn add_sound_guard(&mut self) -> Result<(), SpecError> {
        self.add_definition_reducible(SpecDefinition {
            name: "ImplSoundGuard".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                "(n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat), ",
                "ImplInfer tenv lps n G e T m -> Type"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                    "(n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat) ",
                    "(h : ImplInfer tenv lps n G e T m) => ",
                    "ImplInfer.rec tenv lps ",
                    "(fun (n0 : Nat) (G0 : LCtx) (e0 : ImplExpr) (T0 : ImplExpr) (m0 : Nat) ",
                    "(_h0 : ImplInfer tenv lps n0 G0 e0 T0 m0) => Type) ",
                    // sort / fvar / const — no scoping obligation.
                    "(fun (sn : Nat) (sG : LCtx) (sl : Level) ",
                    "(_shl : Eq Bool (level_params_ok lps sl) Bool.true) => ImplUnit) ",
                    "(fun (vn : Nat) (vG : LCtx) (vx : Nat) (vA : ImplExpr) ",
                    "(_vlk : Eq (OptionType ImplExpr) (lctx_lookup vG vx) ",
                    "(OptionType.some ImplExpr vA)) => ImplUnit) ",
                    "(fun (cn : Nat) (cG : LCtx) (cnm : Name) (cus : ListType Level) ",
                    "(cci : ImplConstInfo) ",
                    "(_cget : Eq (OptionType ImplConstInfo) (tenv cnm) ",
                    "(OptionType.some ImplConstInfo cci)) ",
                    "(_car : Eq Nat (name_list_len (impl_const_lps cci)) (level_list_len cus)) ",
                    "(_clv : Eq Bool (impl_levels_ok lps cus) Bool.true) ",
                    "(_cuf : Eq Bool (impl_const_unsafe cci) Bool.false) ",
                    "(_cpf : Eq Bool (impl_const_partial cci) Bool.false) => ImplUnit) ",
                    // app — no scoping of its own; just both children.
                    "(fun (an : Nat) (an1 : Nat) (an2 : Nat) (aG : LCtx) (af : ImplExpr) ",
                    "(aa : ImplExpr) (aF : ImplExpr) (abd : BinderData) (aA : ImplExpr) ",
                    "(aB : ImplExpr) (aA2 : ImplExpr) ",
                    "(_ahf : ImplInfer tenv lps an aG af aF an1) ",
                    "(_ahw : ImplWhnfTo aF (ImplExpr.pi abd aA aB)) ",
                    "(_aha : ImplInfer tenv lps an1 aG aa aA2 an2) ",
                    "(_ahle : ImplIsLe aA2 aA) (rf : Type) (ra : Type) => AndType rf ra) ",
                    // lam — the fresh id is ln1; body scoped, inferred type closed.
                    "(fun (ln : Nat) (ln1 : Nat) (ln2 : Nat) (lG : LCtx) (lbd : BinderData) ",
                    "(lA : ImplExpr) (lb : ImplExpr) (lS : ImplExpr) (ll : Level) ",
                    "(lbt : ImplExpr) ",
                    "(_lhA : ImplInfer tenv lps ln lG lA lS ln1) ",
                    "(_lhS : ImplWhnfTo lS (ImplExpr.sort ll)) ",
                    "(_lhb : ImplInfer tenv lps (Nat.succ ln1) ",
                    "(LCtx.snoc lG (LocalDecl.mk ln1 lA (OptionType.none ImplExpr) lbd)) ",
                    "(impl_open lb ln1) lbt ln2) ",
                    "(rA : Type) (rb : Type) => ",
                    "AndType (ImplScoped ln1 lb Nat.zero) ",
                    "(AndType (ImplLC lbt Nat.zero) ",
                    "(AndType (ImplFreshLC ln1 lA Nat.zero) ",
                    "(AndType (forall (y : Nat) (Ay : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup lG y) ",
                    "(OptionType.some ImplExpr Ay) -> ImplFreshLC ln1 Ay Nat.zero) ",
                    "(AndType rA rb))))) ",
                    // pi — body scoped; its result is a SORT, so nothing to close.
                    "(fun (pn : Nat) (pn1 : Nat) (pn2 : Nat) (pG : LCtx) (pbd : BinderData) ",
                    "(pA : ImplExpr) (pb : ImplExpr) (pS1 : ImplExpr) (pS2 : ImplExpr) ",
                    "(pl1 : Level) (pl2 : Level) ",
                    "(_phA : ImplInfer tenv lps pn pG pA pS1 pn1) ",
                    "(_phS1 : ImplWhnfTo pS1 (ImplExpr.sort pl1)) ",
                    "(_phb : ImplInfer tenv lps (Nat.succ pn1) ",
                    "(LCtx.snoc pG (LocalDecl.mk pn1 pA (OptionType.none ImplExpr) pbd)) ",
                    "(impl_open pb pn1) pS2 pn2) ",
                    "(_phS2 : ImplWhnfTo pS2 (ImplExpr.sort pl2)) ",
                    "(rA : Type) (rb : Type) => ",
                    "AndType (ImplScoped pn1 pb Nat.zero) ",
                    "(AndType (ImplFreshLC pn1 pA Nat.zero) ",
                    "(AndType (forall (y : Nat) (Ay : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup pG y) ",
                    "(OptionType.some ImplExpr Ay) -> ImplFreshLC pn1 Ay Nat.zero) ",
                    "(AndType rA rb)))) ",
                    // let_ — one MORE than lam: the substituted value must be
                    // closed too, because impl_subst_fvar inserts it raw.
                    "(fun (zn : Nat) (zn1 : Nat) (zn2 : Nat) (zn3 : Nat) (zG : LCtx) ",
                    "(znm : Name) (zty : ImplExpr) (zv : ImplExpr) (zb : ImplExpr) ",
                    "(zS : ImplExpr) (zl : Level) (zTv : ImplExpr) (zbt : ImplExpr) ",
                    "(_zhty : ImplInfer tenv lps zn zG zty zS zn1) ",
                    "(_zhS : ImplWhnfTo zS (ImplExpr.sort zl)) ",
                    "(_zhv : ImplInfer tenv lps zn1 zG zv zTv zn2) ",
                    "(_zhle : ImplIsLe zTv zty) ",
                    "(_zhb : ImplInfer tenv lps (Nat.succ zn2) ",
                    "(LCtx.snoc zG (LocalDecl.mk zn2 zty (OptionType.some ImplExpr zv) ",
                    "(BinderData.mk BinderInfo.default Multiplicity.many))) ",
                    "(impl_open zb zn2) zbt zn3) ",
                    "(rty : Type) (rv : Type) (rb : Type) => ",
                    "AndType (ImplScoped zn2 zb Nat.zero) ",
                    "(AndType (ImplLC zbt Nat.zero) ",
                    "(AndType (ImplLC zv Nat.zero) ",
                    "(AndType (ImplFreshLC zn2 zty Nat.zero) ",
                    "(AndType (forall (y : Nat) (Ay : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup zG y) ",
                    "(OptionType.some ImplExpr Ay) -> ImplFreshLC zn2 Ay Nat.zero) ",
                    "(AndType rty (AndType rv rb))))))) ",
                    // lit — PERMANENTLY out of scope.
                    "(fun (in2 : Nat) (iG : LCtx) (ilt : ImplLit) => Empty) ",
                    // mdata — transparent, so the guard is the inner one.
                    "(fun (mn : Nat) (mn1 : Nat) (mG : LCtx) (me : ImplExpr) (mT : ImplExpr) ",
                    "(_mh : ImplInfer tenv lps mn mG me mT mn1) (mih : Type) => mih) ",
                    "n G e T m h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "M4's COVERAGE GUARD, computed FROM the derivation rather than asserted about ",
                "it. Defined by ImplInfer.rec into Type: Empty at lit, ImplUnit at the ",
                "obligation-free leaves (sort / fvar / const), and at every recursive rule the ",
                "conjunction of that rule's scoping side conditions with its children's guards. ",
                "This makes \"7 of 9, and 7 is the ceiling\" a fact in the environment. lit is ",
                "Empty because TypingCtxConv has no literal rule to bridge into — the same ",
                "permanent gap KernelInfers had, unaffected by the retarget. bvar does not ",
                "appear at all because it is not a rule: layer 1 REFUTES it ",
                "(impl_infer_bvar_rejects, tc/infer.rs:350). ",
                "THE SCOPING FIELDS ARE EXACTLY WHAT THE PROVED ARMS ASK FOR, per rule and not ",
                "uniformly: lam needs the body scoped and its inferred type closed; pi needs ",
                "only the body scoped, because a Pi's result is a SORT and there is nothing to ",
                "abstract back; let_ needs one MORE than lam — the substituted value closed — ",
                "because impl_subst_fvar inserts it RAW (expr/subst.rs:1162) where ",
                "abstract-then-instantiate inserts it lifted. Those asymmetries are in the ",
                "deployed arms, not in the proofs. ",
                "REDUCIBLE, so each minor of the assembled theorem iota-reduces its guard to the ",
                "conjunction and projects the children's out with AndType.left / AndType.right ",
                "— and so widening M4's claim requires editing THIS definition, where a test can ",
                "see it. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer.rec".to_string(),
                "ImplScoped".to_string(),
                "ImplLC".to_string(),
                "AndType".to_string(),
                "ImplUnit".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// The third scoping relation, the weakening lemma, and the two adapters
    /// the assembly needs.
    ///
    /// `ImplFreshLC x e d` is `ImplLC`'s bound **and** `ImplScoped`'s freshness
    /// in one relation, and it exists because the weakening lemma needs both at
    /// once and neither existing relation has both. That is not bookkeeping:
    /// with only `Le` the lemma is **false**. At `d = 1` a local `bvar 1` and a
    /// context variable at renaming position 0 both translate to `bvar 1`, and
    /// the lift must move one and not the other — no cutoff separates them.
    /// Under `Lt` locals sit at `<= d-1` and context variables at `>= d`, so the
    /// cutoff `d` splits them cleanly.
    ///
    /// `ctx_rep_snoc_fresh` is the payoff beyond M4: `CtxRep.snoc`'s two
    /// equation fields — the second of which is the assumption b209ba0df calls
    /// out as what all four C4 arms rest on — are **derived** here from
    /// freshness by `to_kexpr_weaken`. The assumption does not disappear, but it
    /// stops being an equation about translations and becomes a scoping
    /// invariant of the deployed checker, which is a far more tractable thing to
    /// discharge later.
    fn add_ctx_bridge(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            concat!(
                "inductive ImplFreshLC (x : Nat) : ImplExpr -> Nat -> Type\n",
                "| bvar : forall (i : Nat) (d : Nat), Lt i d -> ImplFreshLC x (ImplExpr.bvar i) d\n",
                "| fvar : forall (y : Nat) (d : Nat), Eq Bool (nat_eqb x y) Bool.false -> ImplFreshLC x (ImplExpr.fvar y) d\n",
                "| sort : forall (l : Level) (d : Nat), ImplFreshLC x (ImplExpr.sort l) d\n",
                "| const : forall (nm : Name) (us : ListType Level) (d : Nat), ImplFreshLC x (ImplExpr.const nm us) d\n",
                "| app : forall (f : ImplExpr) (a : ImplExpr) (d : Nat), ImplFreshLC x f d -> ImplFreshLC x a d -> ImplFreshLC x (ImplExpr.app f a) d\n",
                "| lam : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplFreshLC x ty d -> ImplFreshLC x b (Nat.succ d) -> ImplFreshLC x (ImplExpr.lam bd ty b) d\n",
                "| pi : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (d : Nat), ImplFreshLC x ty d -> ImplFreshLC x b (Nat.succ d) -> ImplFreshLC x (ImplExpr.pi bd ty b) d\n",
                "| let_ : forall (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (d : Nat), ImplFreshLC x ty d -> ImplFreshLC x v d -> ImplFreshLC x b (Nat.succ d) -> ImplFreshLC x (ImplExpr.let_ nm ty v b) d\n",
                "| lit : forall (lt : ImplLit) (d : Nat), ImplFreshLC x (ImplExpr.lit lt) d\n",
                "| mdata : forall (e : ImplExpr) (d : Nat), ImplFreshLC x e d -> ImplFreshLC x (ImplExpr.mdata e) d"
            ),
            "ImplFreshLC x e d: every loose bvar of e is STRICTLY below d AND e does not mention \
             the FVarId x. It is ImplLC's bound together with ImplScoped's freshness, and it \
             exists because the weakening lemma needs both AT ONCE while neither existing \
             relation has both. The strictness is not bookkeeping: under Le the weakening lemma \
             is FALSE. At d = 1 a local `bvar 1` and a context variable at renaming position 0 \
             both translate to `bvar 1`, and the lift must move one and not the other — no \
             cutoff can separate them. Under Lt, locals sit at <= d-1 and context variables at \
             >= d, so cutoff d splits them. Operational/syntactic only. ZERO new axioms.",
        )?;

        self.add_definition(SpecDefinition {
            name: "to_kexpr_weaken".to_string(),
            type_src: concat!(
                "forall (rho : ListType Nat) (x : Nat) (e : ImplExpr) (d : Nat), ",
                "ImplFreshLC x e d -> ",
                "Eq KExpr (to_kexpr_at e (ListType.cons Nat x rho) d) ",
                "(lift_at (to_kexpr_at e rho d) d (Nat.succ Nat.zero))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (rho : ListType Nat) (x : Nat) (e : ImplExpr) (d : Nat) ",
                    "(h : ImplFreshLC x e d) => ",
                    "ImplFreshLC.rec x ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_h0 : ImplFreshLC x e0 d0) => Eq KExpr ",
                    "(to_kexpr_at e0 (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at e0 rho d0) d0 (Nat.succ Nat.zero))) ",
                    // bvar : i < d, below the cutoff, so the lift keeps it.
                    "(fun (i : Nat) (d0 : Nat) (hlt : Lt i d0) => ",
                    "Eq.substType Nat (fun (s : Nat) => Eq KExpr (KExpr.bvar i) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) ",
                    "(fun (_q : Nat) (_r : KExpr) => KExpr.bvar i) s)) ",
                    "(Nat.succ (Nat.sub (Nat.sub d0 i) (Nat.succ Nat.zero))) (Nat.sub d0 i) ",
                    "(Eq.symm Nat (Nat.sub d0 i) ",
                    "(Nat.succ (Nat.sub (Nat.sub d0 i) (Nat.succ Nat.zero))) ",
                    "(lt_sub_succ i d0 hlt)) ",
                    "(Eq.refl KExpr (KExpr.bvar i))) ",
                    // fvar : y != x, so the scan steps past the new head; on the
                    // right the lift fires because rho_index + d is >= d.
                    "(fun (y : Nat) (d0 : Nat) (hne : Eq Bool (nat_eqb x y) Bool.false) => ",
                    "Eq.substType Bool (fun (bb : Bool) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Bool.rec (fun (_c : Bool) => Nat) ",
                    "(Nat.succ (rho_index rho y)) Nat.zero bb) d0)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add (Nat.add (rho_index rho y) d0) (Nat.succ Nat.zero))) ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.add (rho_index rho y) d0)) ",
                    "(Nat.sub d0 (Nat.add (rho_index rho y) d0)))) ",
                    "Bool.false (nat_eqb x y) ",
                    "(Eq.symm Bool (nat_eqb x y) Bool.false hne) ",
                    "(Eq.substType Nat (fun (s : Nat) => Eq KExpr ",
                    "(KExpr.bvar (Nat.add (Nat.succ (rho_index rho y)) d0)) ",
                    "(Nat.rec (fun (_m : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add (Nat.add (rho_index rho y) d0) (Nat.succ Nat.zero))) ",
                    "(fun (_q : Nat) (_r : KExpr) => ",
                    "KExpr.bvar (Nat.add (rho_index rho y) d0)) s)) ",
                    "Nat.zero (Nat.sub d0 (Nat.add (rho_index rho y) d0)) ",
                    "(Eq.symm Nat (Nat.sub d0 (Nat.add (rho_index rho y) d0)) Nat.zero ",
                    "(Eq.trans Nat (Nat.sub d0 (Nat.add (rho_index rho y) d0)) ",
                    "(Nat.sub d0 (Nat.add d0 (rho_index rho y))) Nat.zero ",
                    "(Eq.cong Nat Nat (fun (w : Nat) => Nat.sub d0 w) ",
                    "(Nat.add (rho_index rho y) d0) (Nat.add d0 (rho_index rho y)) ",
                    "(nat_add_comm (rho_index rho y) d0)) ",
                    "(nat_sub_self_add_zero d0 (rho_index rho y)))) ",
                    "(Eq.cong Nat KExpr (fun (w : Nat) => KExpr.bvar w) ",
                    "(Nat.add (Nat.succ (rho_index rho y)) d0) ",
                    "(Nat.add (Nat.add (rho_index rho y) d0) (Nat.succ Nat.zero)) ",
                    "(nat_succ_add (rho_index rho y) d0)))) ",
                    // sort / const
                    "(fun (l : Level) (d0 : Nat) => Eq.refl KExpr (KExpr.sort l)) ",
                    "(fun (nm : Name) (us : ListType Level) (d0 : Nat) => ",
                    "Eq.refl KExpr (KExpr.const nm us)) ",
                    // app
                    "(fun (f : ImplExpr) (a : ImplExpr) (d0 : Nat) ",
                    "(_lf : ImplFreshLC x f d0) (_la : ImplFreshLC x a d0) ",
                    "(rf : Eq KExpr (to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at f rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(ra : Eq KExpr (to_kexpr_at a (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at a rho d0) d0 (Nat.succ Nat.zero))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.app (to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (lift_at (to_kexpr_at f rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(KExpr.app (lift_at (to_kexpr_at f rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at a rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0)) ",
                    "(to_kexpr_at f (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at f rho d0) d0 (Nat.succ Nat.zero)) rf) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app ",
                    "(lift_at (to_kexpr_at f rho d0) d0 (Nat.succ Nat.zero)) w) ",
                    "(to_kexpr_at a (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at a rho d0) d0 (Nat.succ Nat.zero)) ra)) ",
                    // lam / pi / let_ : both sides step depth AND cutoff to succ d0.
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplFreshLC x ty d0) (_lb : ImplFreshLC x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.lam (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.lam (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero)) rb)) ",
                    "(fun (bd : BinderData) (ty : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplFreshLC x ty d0) (_lb : ImplFreshLC x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.pi (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.pi (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) rt) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero)) rb)) ",
                    "(fun (nm : Name) (ty : ImplExpr) (vv : ImplExpr) (bb : ImplExpr) (d0 : Nat) ",
                    "(_lt : ImplFreshLC x ty d0) (_lv : ImplFreshLC x vv d0) ",
                    "(_lb : ImplFreshLC x bb (Nat.succ d0)) ",
                    "(rt : Eq KExpr (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(rv : Eq KExpr (to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero))) ",
                    "(rb : Eq KExpr (to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) => ",
                    "Eq.trans KExpr ",
                    "(KExpr.let_ (to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at ty (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) rt) ",
                    "(Eq.trans KExpr ",
                    "(KExpr.let_ (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(KExpr.let_ (lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero))) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) w ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0))) ",
                    "(to_kexpr_at vv (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero)) rv) ",
                    "(Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ ",
                    "(lift_at (to_kexpr_at ty rho d0) d0 (Nat.succ Nat.zero)) ",
                    "(lift_at (to_kexpr_at vv rho d0) d0 (Nat.succ Nat.zero)) w) ",
                    "(to_kexpr_at bb (ListType.cons Nat x rho) (Nat.succ d0)) ",
                    "(lift_at (to_kexpr_at bb rho (Nat.succ d0)) (Nat.succ d0) ",
                    "(Nat.succ Nat.zero)) rb))) ",
                    // lit / mdata
                    "(fun (lt : ImplLit) (d0 : Nat) => ",
                    "ImplLit.rec (fun (z : ImplLit) => Eq KExpr (impl_lit_to_kexpr z) ",
                    "(lift_at (impl_lit_to_kexpr z) d0 (Nat.succ Nat.zero))) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) ",
                    "(fun (k : Nat) => Eq.refl KExpr (KExpr.lit k)) lt) ",
                    "(fun (e0 : ImplExpr) (d0 : Nat) (_le : ImplFreshLC x e0 d0) ",
                    "(ri : Eq KExpr (to_kexpr_at e0 (ListType.cons Nat x rho) d0) ",
                    "(lift_at (to_kexpr_at e0 rho d0) d0 (Nat.succ Nat.zero))) => ri) ",
                    "e d h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE CONTEXT-WEAKENING LEMMA: putting a new name at the front of the renaming ",
                "shifts every existing variable up by exactly one. This is what CtxRep.snoc's ",
                "two equation fields assert, and what the assembly needs in order to EXTEND a ",
                "context representation at a binder. ",
                "THE CUTOFF IS FORCED TO BE d, WHICH IS WHY THE BOUND MUST BE STRICT. A local ",
                "bvar must NOT move (so it must sit below the cutoff) while a context variable, ",
                "which translates to `rho_index + d` and so is at least d, MUST move (so the ",
                "cutoff can be at most d). Both constraints meet only at cutoff = d with all ",
                "loose bvars < d. Under ImplScoped's Le, a loose bvar may EQUAL d and then it ",
                "collides with the position-0 context variable — same index, opposite ",
                "requirements — so the statement is false, not merely unproven. ",
                "The fvar case needs nat_add_comm + nat_sub_self_add_zero to fire the lift and ",
                "nat_succ_add to land it, and it uses that `Nat.add X (Nat.succ Nat.zero)` is ",
                "DEFINITIONALLY `Nat.succ X` because Nat.add recurses on its second argument. ",
                "The binder arms need no transport: both sides step depth and cutoff together. ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplFreshLC.rec".to_string(),
                "to_kexpr_at".to_string(),
                "lift_at".to_string(),
                "lt_sub_succ".to_string(),
                "nat_add_comm".to_string(),
                "nat_sub_self_add_zero".to_string(),
                "nat_succ_add".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // CtxRep.snoc's equation fields, DERIVED from freshness.
        self.add_definition(SpecDefinition {
            name: "ctx_rep_snoc_fresh".to_string(),
            type_src: concat!(
                "forall (Gk : ListType KExpr) (rho : ListType Nat) (D : LCtx) (x : Nat) ",
                "(A : ImplExpr) (dv : OptionType ImplExpr) (bd : BinderData), ",
                "CtxRep Gk rho D -> ImplFreshLC x A Nat.zero -> ",
                "(forall (y : Nat) (Ay : ImplExpr), ",
                "Eq (OptionType ImplExpr) (lctx_lookup D y) (OptionType.some ImplExpr Ay) -> ",
                "ImplFreshLC x Ay Nat.zero) -> ",
                "CtxRep (ListType.cons KExpr (to_kexpr A rho) Gk) (ListType.cons Nat x rho) ",
                "(LCtx.snoc D (LocalDecl.mk x A dv bd))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (Gk : ListType KExpr) (rho : ListType Nat) (D : LCtx) (x : Nat) ",
                    "(A : ImplExpr) (dv : OptionType ImplExpr) (bd : BinderData) ",
                    "(crep : CtxRep Gk rho D) (hfa : ImplFreshLC x A Nat.zero) ",
                    "(hfd : forall (y : Nat) (Ay : ImplExpr), ",
                    "Eq (OptionType ImplExpr) (lctx_lookup D y) (OptionType.some ImplExpr Ay) -> ",
                    "ImplFreshLC x Ay Nat.zero) => ",
                    "CtxRep.snoc Gk rho D x (to_kexpr A rho) A dv bd crep ",
                    "(to_kexpr_weaken rho x A Nat.zero hfa) ",
                    "(fun (y : Nat) (Ay : ImplExpr) ",
                    "(hy : Eq (OptionType ImplExpr) (lctx_lookup D y) ",
                    "(OptionType.some ImplExpr Ay)) => ",
                    "to_kexpr_weaken rho x Ay Nat.zero (hfd y Ay hy))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "CtxRep.snoc BUILT FROM FRESHNESS — and this is the payoff beyond M4. b209ba0df ",
                "records that all four of C4's bridged arms rest on CtxRep.snoc's assumed ",
                "field 3, an EQUATION about translations. Here both equation fields are ",
                "DERIVED, by to_kexpr_weaken, from a scoping hypothesis instead. ",
                "The assumption does not vanish — one still supplies ImplFreshLC for the new ",
                "entry and for everything already in the context — but it stops being an ",
                "equation relating to_kexpr at two renamings and becomes a plain freshness ",
                "invariant of the deployed checker, which production guarantees by construction ",
                "(next_id is never rewound and ids are never reused, tc/local_context.rs:81-89, ",
                ":111). That is a far more tractable thing for a later increment to discharge, ",
                "and it is exactly the shape ctx_rep.rs's header asks for when it names \"a ",
                "locally-closed predicate on ImplExpr plus a translation/lift commutation ",
                "lemma\" as the first build item. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxRep.snoc".to_string(),
                "to_kexpr_weaken".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The TypingCtxConv analogue of kernelinfers_var_of_var_type.
        self.add_definition(SpecDefinition {
            name: "tconv_var_of_var_type".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr) (i : Nat) ",
                "(Tk : KExpr), ",
                "Eq (OptionType KExpr) (ctx_var_type G i) (OptionType.some KExpr Tk) -> ",
                "TypingCtxConv tenv G (KExpr.bvar i) Tk"
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
                    "TypingCtxConv tenv G (KExpr.bvar i) Tk) ",
                    "(fun (_hl : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.none KExpr)) ",
                    "(hs : Eq (OptionType KExpr) (OptionType.none KExpr) ",
                    "(OptionType.some KExpr Tk)) => ",
                    "option_none_ne_some_type KExpr Tk ",
                    "(TypingCtxConv tenv G (KExpr.bvar i) Tk) hs) ",
                    "(fun (A : KExpr) ",
                    "(hl : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) ",
                    "(hs : Eq (OptionType KExpr) ",
                    "(OptionType.some KExpr (lift_at A Nat.zero (Nat.succ i))) ",
                    "(OptionType.some KExpr Tk)) => ",
                    "Eq.substType KExpr ",
                    "(fun (T : KExpr) => TypingCtxConv tenv G (KExpr.bvar i) T) ",
                    "(lift_at A Nat.zero (Nat.succ i)) Tk ",
                    "(option_some_inj KExpr (lift_at A Nat.zero (Nat.succ i)) Tk hs) ",
                    "(TypingCtxConv.var tenv G i A hl)) ",
                    "(ctx_lookup G i) ",
                    "(Eq.refl (OptionType KExpr) (ctx_lookup G i)) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The TypingCtxConv analogue of kernelinfers_var_of_var_type: turn the packaged ",
                "`ctx_var_type G i = some Tk` back into a variable DERIVATION. Same proof shape ",
                "— case on ctx_lookup with the scrutinee carried, none is impossible, some ",
                "applies TypingCtxConv.var and transports along option_some_inj. Registered so ",
                "the assembly's fvar arm can consume ctx_rep_lookup, which is already proved ",
                "against ctx_var_type and is therefore codomain-agnostic. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.var".to_string(),
                "ctx_var_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "option_some_inj".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// **`impl_infer_sound`** — the M4 theorem, assembled.
    ///
    /// `ImplInfer.rec` over a guarded motive: every derivation whose guard is
    /// inhabited translates to a `TypingCtxConv` derivation on the erased terms,
    /// under any context representation.
    ///
    /// The motive quantifies over `rho` and `Gk` *inside*, because both change
    /// at a binder while the layer-1 context is an index of the relation — so
    /// they cannot be fixed outside the induction.
    fn add_assembly(&mut self) -> Result<(), SpecError> {
        // The environment representation the `const` rule needs.
        self.add_definition_reducible(SpecDefinition {
            name: "TEnvRepC".to_string(),
            type_src: "(Name -> OptionType ImplConstInfo) -> (Name -> OptionType KExpr) -> Prop"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType ImplConstInfo) ",
                    "(tenvK : Name -> OptionType KExpr) => ",
                    "forall (nm : Name) (ci : ImplConstInfo) (us : ListType Level) ",
                    "(rho : ListType Nat), ",
                    "Eq (OptionType ImplConstInfo) (tenv nm) (OptionType.some ImplConstInfo ci) -> ",
                    "Eq (OptionType KExpr) (tenvK nm) (OptionType.some KExpr ",
                    "(to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "ENVIRONMENT REPRESENTATION for the assembled theorem's const rule. Quantifying ",
                "over `us` AND `rho` makes it satisfiable only for constants whose translated ",
                "type depends on neither — i.e. level-monomorphic constants with fvar-free ",
                "types. That is not a shortcut, it is FORCED: TypingCtxConv.const's environment ",
                "is `Name -> OptionType KExpr` with no `us` argument, so layer 2 is ",
                "universe-blind and cannot express a universe-instantiated constant type. The ",
                "gap is inherited from KernelInfers and is untouched by the retarget; widening ",
                "it is a layer-2 modelling change, not an M4 obligation. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "to_kexpr".to_string(),
                "impl_inst_levels".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── guard sub-terms, written once and reused by the projections ──────
        let lam_decl = "(LocalDecl.mk ln1 lA (OptionType.none ImplExpr) lbd)";
        let pi_decl = "(LocalDecl.mk pn1 pA (OptionType.none ImplExpr) pbd)";
        let let_decl = concat!(
            "(LocalDecl.mk zn2 zty (OptionType.some ImplExpr zv) ",
            "(BinderData.mk BinderInfo.default Multiplicity.many))"
        );
        let lam_ga = "(ImplSoundGuard tenv lps ln lG lA lS ln1 lhA)";
        let lam_gb = format!(
            "(ImplSoundGuard tenv lps (Nat.succ ln1) (LCtx.snoc lG {lam_decl}) \
             (impl_open lb ln1) lbt ln2 lhb)"
        );
        let pi_ga = "(ImplSoundGuard tenv lps pn pG pA pS1 pn1 phA)";
        let pi_gb = format!(
            "(ImplSoundGuard tenv lps (Nat.succ pn1) (LCtx.snoc pG {pi_decl}) \
             (impl_open pb pn1) pS2 pn2 phb)"
        );
        let let_gt = "(ImplSoundGuard tenv lps zn zG zty zS zn1 zhty)";
        let let_gv = "(ImplSoundGuard tenv lps zn1 zG zv zTv zn2 zhv)";
        let let_gb = format!(
            "(ImplSoundGuard tenv lps (Nat.succ zn2) (LCtx.snoc zG {let_decl}) \
             (impl_open zb zn2) zbt zn3 zhb)"
        );
        let lam_cf = "(forall (y : Nat) (Ay : ImplExpr), Eq (OptionType ImplExpr) \
                      (lctx_lookup lG y) (OptionType.some ImplExpr Ay) -> \
                      ImplFreshLC ln1 Ay Nat.zero)";
        let pi_cf = "(forall (y : Nat) (Ay : ImplExpr), Eq (OptionType ImplExpr) \
                     (lctx_lookup pG y) (OptionType.some ImplExpr Ay) -> \
                     ImplFreshLC pn1 Ay Nat.zero)";
        let let_cf = "(forall (y : Nat) (Ay : ImplExpr), Eq (OptionType ImplExpr) \
                      (lctx_lookup zG y) (OptionType.some ImplExpr Ay) -> \
                      ImplFreshLC zn2 Ay Nat.zero)";

        let motive = "(fun (n0 : Nat) (G0 : LCtx) (e0 : ImplExpr) (T0 : ImplExpr) (m0 : Nat) \
                      (h0 : ImplInfer tenv lps n0 G0 e0 T0 m0) => \
                      ImplSoundGuard tenv lps n0 G0 e0 T0 m0 h0 -> \
                      forall (rho : ListType Nat) (Gk : ListType KExpr), \
                      CtxRep Gk rho G0 -> \
                      TypingCtxConv tenvK Gk (to_kexpr e0 rho) (to_kexpr T0 rho))";

        // The lam minor's guard chain, projected step by step.
        let lam_r1 = format!("(AndType (ImplLC lbt Nat.zero) (AndType (ImplFreshLC ln1 lA Nat.zero) (AndType {lam_cf} (AndType {lam_ga} {lam_gb}))))");
        let lam_r2 = format!("(AndType (ImplFreshLC ln1 lA Nat.zero) (AndType {lam_cf} (AndType {lam_ga} {lam_gb})))");
        let lam_r3 = format!("(AndType {lam_cf} (AndType {lam_ga} {lam_gb}))");
        let lam_r4 = format!("(AndType {lam_ga} {lam_gb})");

        let pi_r1 = format!(
            "(AndType (ImplFreshLC pn1 pA Nat.zero) (AndType {pi_cf} (AndType {pi_ga} {pi_gb})))"
        );
        let pi_r2 = format!("(AndType {pi_cf} (AndType {pi_ga} {pi_gb}))");
        let pi_r3 = format!("(AndType {pi_ga} {pi_gb})");

        let let_r1 = format!("(AndType (ImplLC zbt Nat.zero) (AndType (ImplLC zv Nat.zero) (AndType (ImplFreshLC zn2 zty Nat.zero) (AndType {let_cf} (AndType {let_gt} (AndType {let_gv} {let_gb}))))))");
        let let_r2 = format!("(AndType (ImplLC zv Nat.zero) (AndType (ImplFreshLC zn2 zty Nat.zero) (AndType {let_cf} (AndType {let_gt} (AndType {let_gv} {let_gb})))))");
        let let_r3 = format!("(AndType (ImplFreshLC zn2 zty Nat.zero) (AndType {let_cf} (AndType {let_gt} (AndType {let_gv} {let_gb}))))");
        let let_r4 = format!("(AndType {let_cf} (AndType {let_gt} (AndType {let_gv} {let_gb})))");
        let let_r5 = format!("(AndType {let_gt} (AndType {let_gv} {let_gb}))");
        let let_r6 = format!("(AndType {let_gv} {let_gb})");

        let value = format!(
            "fun (tenv : Name -> OptionType ImplConstInfo) \
             (tenvK : Name -> OptionType KExpr) (lps : ListType Name) \
             (te : TEnvRepC tenv tenvK) (n : Nat) (G : LCtx) (e : ImplExpr) \
             (T : ImplExpr) (m : Nat) (h : ImplInfer tenv lps n G e T m) => \
             ImplInfer.rec tenv lps {motive} \
             \
             (fun (sn : Nat) (sG : LCtx) (sl : Level) \
             (_shl : Eq Bool (level_params_ok lps sl) Bool.true) => \
             fun (_g : ImplUnit) (rho : ListType Nat) (Gk : ListType KExpr) \
             (_c : CtxRep Gk rho sG) => TypingCtxConv.sort tenvK Gk sl) \
             \
             (fun (vn : Nat) (vG : LCtx) (vx : Nat) (vA : ImplExpr) \
             (vlk : Eq (OptionType ImplExpr) (lctx_lookup vG vx) \
             (OptionType.some ImplExpr vA)) => \
             fun (_g : ImplUnit) (rho : ListType Nat) (Gk : ListType KExpr) \
             (c : CtxRep Gk rho vG) => \
             tconv_var_of_var_type tenvK Gk (rho_index rho vx) (to_kexpr vA rho) \
             (ctx_rep_lookup Gk rho vG c vx vA vlk)) \
             \
             (fun (cn : Nat) (cG : LCtx) (cnm : Name) (cus : ListType Level) \
             (cci : ImplConstInfo) \
             (cget : Eq (OptionType ImplConstInfo) (tenv cnm) \
             (OptionType.some ImplConstInfo cci)) \
             (_car : Eq Nat (name_list_len (impl_const_lps cci)) (level_list_len cus)) \
             (_clv : Eq Bool (impl_levels_ok lps cus) Bool.true) \
             (_cuf : Eq Bool (impl_const_unsafe cci) Bool.false) \
             (_cpf : Eq Bool (impl_const_partial cci) Bool.false) => \
             fun (_g : ImplUnit) (rho : ListType Nat) (Gk : ListType KExpr) \
             (_c : CtxRep Gk rho cG) => \
             TypingCtxConv.const tenvK Gk cnm cus \
             (to_kexpr (impl_inst_levels (impl_const_lps cci) cus (impl_const_type cci)) rho) \
             (te cnm cci cus rho cget)) \
             \
             (fun (an : Nat) (an1 : Nat) (an2 : Nat) (aG : LCtx) (af : ImplExpr) \
             (aa : ImplExpr) (aF : ImplExpr) (abd : BinderData) (aA : ImplExpr) \
             (aB : ImplExpr) (aA2 : ImplExpr) \
             (ahf : ImplInfer tenv lps an aG af aF an1) \
             (ahw : ImplWhnfTo aF (ImplExpr.pi abd aA aB)) \
             (aha : ImplInfer tenv lps an1 aG aa aA2 an2) \
             (ahle : ImplIsLe aA2 aA) \
             (aihf : {motive} an aG af aF an1 ahf) \
             (aiha : {motive} an1 aG aa aA2 an2 aha) => \
             fun (g : AndType (ImplSoundGuard tenv lps an aG af aF an1 ahf) \
             (ImplSoundGuard tenv lps an1 aG aa aA2 an2 aha)) \
             (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho aG) => \
             impl_sound_app tenvK Gk rho af aa aF abd aA aB aA2 ahw ahle \
             (aihf (AndType.left (ImplSoundGuard tenv lps an aG af aF an1 ahf) \
             (ImplSoundGuard tenv lps an1 aG aa aA2 an2 aha) g) rho Gk c) \
             (aiha (AndType.right (ImplSoundGuard tenv lps an aG af aF an1 ahf) \
             (ImplSoundGuard tenv lps an1 aG aa aA2 an2 aha) g) rho Gk c)) \
             \
             (fun (ln : Nat) (ln1 : Nat) (ln2 : Nat) (lG : LCtx) (lbd : BinderData) \
             (lA : ImplExpr) (lb : ImplExpr) (lS : ImplExpr) (ll : Level) \
             (lbt : ImplExpr) \
             (lhA : ImplInfer tenv lps ln lG lA lS ln1) \
             (lhS : ImplWhnfTo lS (ImplExpr.sort ll)) \
             (lhb : ImplInfer tenv lps (Nat.succ ln1) (LCtx.snoc lG {lam_decl}) \
             (impl_open lb ln1) lbt ln2) \
             (lihA : {motive} ln lG lA lS ln1 lhA) \
             (lihb : {motive} (Nat.succ ln1) (LCtx.snoc lG {lam_decl}) \
             (impl_open lb ln1) lbt ln2 lhb) => \
             fun (g : AndType (ImplScoped ln1 lb Nat.zero) {lam_r1}) \
             (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho lG) => \
             impl_sound_lam_scoped tenvK Gk rho ln1 lbd lA lb lS ll lbt \
             (AndType.left (ImplScoped ln1 lb Nat.zero) {lam_r1} g) \
             (AndType.left (ImplLC lbt Nat.zero) {lam_r2} \
             (AndType.right (ImplScoped ln1 lb Nat.zero) {lam_r1} g)) \
             lhS \
             (lihA (AndType.left {lam_ga} {lam_gb} \
             (AndType.right {lam_cf} {lam_r4} \
             (AndType.right (ImplFreshLC ln1 lA Nat.zero) {lam_r3} \
             (AndType.right (ImplLC lbt Nat.zero) {lam_r2} \
             (AndType.right (ImplScoped ln1 lb Nat.zero) {lam_r1} g))))) rho Gk c) \
             (lihb (AndType.right {lam_ga} {lam_gb} \
             (AndType.right {lam_cf} {lam_r4} \
             (AndType.right (ImplFreshLC ln1 lA Nat.zero) {lam_r3} \
             (AndType.right (ImplLC lbt Nat.zero) {lam_r2} \
             (AndType.right (ImplScoped ln1 lb Nat.zero) {lam_r1} g))))) \
             (ListType.cons Nat ln1 rho) \
             (ListType.cons KExpr (to_kexpr lA rho) Gk) \
             (ctx_rep_snoc_fresh Gk rho lG ln1 lA (OptionType.none ImplExpr) lbd c \
             (AndType.left (ImplFreshLC ln1 lA Nat.zero) {lam_r3} \
             (AndType.right (ImplLC lbt Nat.zero) {lam_r2} \
             (AndType.right (ImplScoped ln1 lb Nat.zero) {lam_r1} g))) \
             (AndType.left {lam_cf} {lam_r4} \
             (AndType.right (ImplFreshLC ln1 lA Nat.zero) {lam_r3} \
             (AndType.right (ImplLC lbt Nat.zero) {lam_r2} \
             (AndType.right (ImplScoped ln1 lb Nat.zero) {lam_r1} g))))))) \
             \
             (fun (pn : Nat) (pn1 : Nat) (pn2 : Nat) (pG : LCtx) (pbd : BinderData) \
             (pA : ImplExpr) (pb : ImplExpr) (pS1 : ImplExpr) (pS2 : ImplExpr) \
             (pl1 : Level) (pl2 : Level) \
             (phA : ImplInfer tenv lps pn pG pA pS1 pn1) \
             (phS1 : ImplWhnfTo pS1 (ImplExpr.sort pl1)) \
             (phb : ImplInfer tenv lps (Nat.succ pn1) (LCtx.snoc pG {pi_decl}) \
             (impl_open pb pn1) pS2 pn2) \
             (phS2 : ImplWhnfTo pS2 (ImplExpr.sort pl2)) \
             (pihA : {motive} pn pG pA pS1 pn1 phA) \
             (pihb : {motive} (Nat.succ pn1) (LCtx.snoc pG {pi_decl}) \
             (impl_open pb pn1) pS2 pn2 phb) => \
             fun (g : AndType (ImplScoped pn1 pb Nat.zero) {pi_r1}) \
             (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho pG) => \
             impl_sound_pi_scoped tenvK Gk rho pn1 pbd pA pb pS1 pS2 pl1 pl2 \
             (AndType.left (ImplScoped pn1 pb Nat.zero) {pi_r1} g) \
             phS1 phS2 \
             (pihA (AndType.left {pi_ga} {pi_gb} \
             (AndType.right {pi_cf} {pi_r3} \
             (AndType.right (ImplFreshLC pn1 pA Nat.zero) {pi_r2} \
             (AndType.right (ImplScoped pn1 pb Nat.zero) {pi_r1} g)))) rho Gk c) \
             (pihb (AndType.right {pi_ga} {pi_gb} \
             (AndType.right {pi_cf} {pi_r3} \
             (AndType.right (ImplFreshLC pn1 pA Nat.zero) {pi_r2} \
             (AndType.right (ImplScoped pn1 pb Nat.zero) {pi_r1} g)))) \
             (ListType.cons Nat pn1 rho) \
             (ListType.cons KExpr (to_kexpr pA rho) Gk) \
             (ctx_rep_snoc_fresh Gk rho pG pn1 pA (OptionType.none ImplExpr) pbd c \
             (AndType.left (ImplFreshLC pn1 pA Nat.zero) {pi_r2} \
             (AndType.right (ImplScoped pn1 pb Nat.zero) {pi_r1} g)) \
             (AndType.left {pi_cf} {pi_r3} \
             (AndType.right (ImplFreshLC pn1 pA Nat.zero) {pi_r2} \
             (AndType.right (ImplScoped pn1 pb Nat.zero) {pi_r1} g)))))) \
             \
             (fun (zn : Nat) (zn1 : Nat) (zn2 : Nat) (zn3 : Nat) (zG : LCtx) \
             (znm : Name) (zty : ImplExpr) (zv : ImplExpr) (zb : ImplExpr) \
             (zS : ImplExpr) (zl : Level) (zTv : ImplExpr) (zbt : ImplExpr) \
             (zhty : ImplInfer tenv lps zn zG zty zS zn1) \
             (zhS : ImplWhnfTo zS (ImplExpr.sort zl)) \
             (zhv : ImplInfer tenv lps zn1 zG zv zTv zn2) \
             (zhle : ImplIsLe zTv zty) \
             (zhb : ImplInfer tenv lps (Nat.succ zn2) (LCtx.snoc zG {let_decl}) \
             (impl_open zb zn2) zbt zn3) \
             (zihty : {motive} zn zG zty zS zn1 zhty) \
             (zihv : {motive} zn1 zG zv zTv zn2 zhv) \
             (zihb : {motive} (Nat.succ zn2) (LCtx.snoc zG {let_decl}) \
             (impl_open zb zn2) zbt zn3 zhb) => \
             fun (g : AndType (ImplScoped zn2 zb Nat.zero) {let_r1}) \
             (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho zG) => \
             impl_sound_let_scoped tenvK Gk rho zn2 znm zty zv zb zS zl zTv zbt \
             (AndType.left (ImplScoped zn2 zb Nat.zero) {let_r1} g) \
             (AndType.left (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g)) \
             (AndType.left (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g))) \
             zhS zhle \
             (zihty (AndType.left {let_gt} {let_r6} \
             (AndType.right {let_cf} {let_r5} \
             (AndType.right (ImplFreshLC zn2 zty Nat.zero) {let_r4} \
             (AndType.right (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g)))))) rho Gk c) \
             (zihv (AndType.left {let_gv} {let_gb} \
             (AndType.right {let_gt} {let_r6} \
             (AndType.right {let_cf} {let_r5} \
             (AndType.right (ImplFreshLC zn2 zty Nat.zero) {let_r4} \
             (AndType.right (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g))))))) rho Gk c) \
             (zihb (AndType.right {let_gv} {let_gb} \
             (AndType.right {let_gt} {let_r6} \
             (AndType.right {let_cf} {let_r5} \
             (AndType.right (ImplFreshLC zn2 zty Nat.zero) {let_r4} \
             (AndType.right (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g))))))) \
             (ListType.cons Nat zn2 rho) \
             (ListType.cons KExpr (to_kexpr zty rho) Gk) \
             (ctx_rep_snoc_fresh Gk rho zG zn2 zty (OptionType.some ImplExpr zv) \
             (BinderData.mk BinderInfo.default Multiplicity.many) c \
             (AndType.left (ImplFreshLC zn2 zty Nat.zero) {let_r4} \
             (AndType.right (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g)))) \
             (AndType.left {let_cf} {let_r5} \
             (AndType.right (ImplFreshLC zn2 zty Nat.zero) {let_r4} \
             (AndType.right (ImplLC zv Nat.zero) {let_r3} \
             (AndType.right (ImplLC zbt Nat.zero) {let_r2} \
             (AndType.right (ImplScoped zn2 zb Nat.zero) {let_r1} g)))))))) \
             \
             (fun (in2 : Nat) (iG : LCtx) (ilt : ImplLit) => \
             fun (g : Empty) (rho : ListType Nat) (Gk : ListType KExpr) \
             (_c : CtxRep Gk rho iG) => \
             Empty.rec (fun (_z : Empty) => TypingCtxConv tenvK Gk \
             (to_kexpr (ImplExpr.lit ilt) rho) (to_kexpr (impl_lit_type ilt) rho)) g) \
             \
             (fun (mn : Nat) (mn1 : Nat) (mG : LCtx) (me : ImplExpr) (mT : ImplExpr) \
             (mh : ImplInfer tenv lps mn mG me mT mn1) \
             (mih : {motive} mn mG me mT mn1 mh) => \
             fun (g : ImplSoundGuard tenv lps mn mG me mT mn1 mh) \
             (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho mG) => \
             mih g rho Gk c) \
             \
             n G e T m h"
        );

        self.add_definition(SpecDefinition {
            name: "impl_infer_sound".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType ImplConstInfo) ",
                "(tenvK : Name -> OptionType KExpr) (lps : ListType Name), ",
                "TEnvRepC tenv tenvK -> ",
                "forall (n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat) ",
                "(h : ImplInfer tenv lps n G e T m), ",
                "ImplSoundGuard tenv lps n G e T m h -> ",
                "forall (rho : ListType Nat) (Gk : ListType KExpr), ",
                "CtxRep Gk rho G -> ",
                "TypingCtxConv tenvK Gk (to_kexpr e rho) (to_kexpr T rho)"
            )
            .to_string(),
            value_src: Some(value),
            is_axiom: false,
            description: concat!(
                "**THE M4 THEOREM.** Every ImplInfer derivation whose guard is inhabited ",
                "translates, under any context representation, to a TypingCtxConv derivation on ",
                "the erased terms. This is step M4 of ",
                "designs/2026-07-29-unified-implinfer-relation.md — \"impl_infer_sound (§2). ",
                "Port bootstrap_infer_sound's proof term: swap bvar/ctx_lookup/lift_at -> ",
                "fvar/lctx_lookup/identity; binder arms gain the open/abstract round trip.\" ",
                "THE MOTIVE QUANTIFIES OVER rho AND Gk INSIDE, which is forced: both change at ",
                "a binder while the layer-1 context is an INDEX of the relation, so they cannot ",
                "be fixed outside the induction. Each binder minor instantiates them at ",
                "`cons x rho` and `cons (to_kexpr A rho) Gk` and builds the extended context ",
                "representation with ctx_rep_snoc_fresh. ",
                "The nine minors are exactly the seven proved arms, one Empty.rec, and one ",
                "identity: sort/const are direct, fvar is ctx_rep_lookup composed with ",
                "tconv_var_of_var_type, app/lam/pi/let_ are impl_sound_app / ",
                "impl_sound_lam_scoped / impl_sound_pi_scoped / impl_sound_let_scoped, lit is ",
                "discharged by Empty.rec because the guard reduces to Empty there, and mdata is ",
                "the inner call because the translation erases it. ",
                "WHAT IS ASSUMED, stated plainly: TEnvRepC (layer 2 is universe-blind — ",
                "inherited from KernelInfers, untouched by the retarget), CtxRep (whose two ",
                "equation fields ctx_rep_snoc_fresh now DERIVES from freshness rather than ",
                "assuming), and the guard's per-rule scoping, which is a genuine invariant of ",
                "the deployed checker. Nothing here is an axiom: DerivedProved, EMPTY axiom ",
                "closure, census unchanged at 11."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer.rec".to_string(),
                "ImplSoundGuard".to_string(),
                "CtxRep".to_string(),
                "TEnvRepC".to_string(),
                "ctx_rep_lookup".to_string(),
                "tconv_var_of_var_type".to_string(),
                "ctx_rep_snoc_fresh".to_string(),
                "impl_sound_app".to_string(),
                "impl_sound_lam_scoped".to_string(),
                "impl_sound_pi_scoped".to_string(),
                "impl_sound_let_scoped".to_string(),
                "TypingCtxConv.sort".to_string(),
                "TypingCtxConv.const".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Non-vacuity witnesses for everything M4 assumes.
    ///
    /// The premise-satisfiability gate states the principle exactly: *a
    /// conditional theorem whose premises cannot be satisfied is not a weak
    /// result, it is a NON-result* — and it passes the axiom census, the
    /// domain-axiom count and the `DerivedProved`-debt count while looking
    /// green. `impl_infer_sound` is conditional on `TEnvRepC`, `CtxRep` and
    /// `ImplSoundGuard`, so each needs an inhabitant, and the theorem itself
    /// needs to be seen producing a derivation.
    fn add_sound_witnesses(&mut self) -> Result<(), SpecError> {
        let tenv = "(fun (nm : Name) => OptionType.none ImplConstInfo)";
        let tenvk = "(fun (nm : Name) => OptionType.none KExpr)";
        // The sort derivation written OUT, not named. ImplSoundGuard recurses on
        // the DERIVATION via ImplInfer.rec, so it only iota-reduces once the
        // derivation is a literal constructor application — a named constant
        // leaves the guard stuck and `ImplUnit.mk` will not typecheck against it.
        let deriv = format!(
            "(ImplInfer.sort {tenv} (ListType.nil Name) Nat.zero LCtx.nil Level.zero \
             (Eq.refl Bool Bool.true))"
        );

        for (name, ty, val, why) in [
            (
                "implscoped_witness",
                "ImplScoped Nat.zero (ImplExpr.bvar Nat.zero) Nat.zero".to_string(),
                "ImplScoped.bvar Nat.zero Nat.zero Nat.zero (Le.refl Nat.zero)".to_string(),
                "ImplScoped IS INHABITED, on the term that matters: the body of the identity \
                 lambda. Its single loose index is 0 and the bound is Le 0 0 — the boundary \
                 case, which is precisely why this relation carries Le and not Lt.",
            ),
            (
                "impllc_witness",
                "ImplLC (ImplExpr.sort Level.zero) Nat.zero".to_string(),
                "ImplLC.sort Level.zero Nat.zero".to_string(),
                "ImplLC IS INHABITED at depth zero, where its bvar constructor is UNINHABITABLE \
                 (Lt i Nat.zero has no inhabitant). A closed term still satisfies it, which is \
                 the point: the relation excludes loose indices without excluding everything.",
            ),
            (
                "implwhnfto_witness",
                "ImplWhnfTo (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero)".to_string(),
                "ImplWhnfTo.done (ImplExpr.sort Level.zero)".to_string(),
                "ImplWhnfTo IS INHABITED. impl_whnf_to_defeq is conditional on it, so without \
                 this that theorem is conditional on an unsatisfiable premise — a NON-result. \
                 `done` is unrestricted reflexivity, which is exactly why the relation \
                 over-approximates whnf and why its soundness theorem, not its shape, is what \
                 constrains it.",
            ),
            (
                "implisle_witness",
                "ImplIsLe (ImplExpr.sort Level.zero) (ImplExpr.sort Level.zero)".to_string(),
                "ImplIsLe.refl (ImplExpr.sort Level.zero)".to_string(),
                "ImplIsLe IS INHABITED, for the same reason: impl_is_le_defeq assumes it.",
            ),
            (
                "implunit_witness",
                "ImplUnit".to_string(),
                "ImplUnit.mk".to_string(),
                "ImplUnit IS INHABITED — the guard reduces to it at every rule M4 proves, so an \
                 uninhabited ImplUnit would make ImplSoundGuard, and with it impl_infer_sound, \
                 vacuous everywhere.",
            ),
            (
                "impllit_witness",
                "ImplLit".to_string(),
                "ImplLit.natVal Nat.zero".to_string(),
                "ImplLit IS INHABITED. It is the payload of the one ImplExpr head M4 \
                 permanently excludes, so it is worth knowing the exclusion is of something \
                 real rather than of an empty case.",
            ),
            (
                "multiplicity_witness",
                "Multiplicity".to_string(),
                "Multiplicity.many".to_string(),
                "Multiplicity IS INHABITED — it sits inside every BinderData the binder rules \
                 carry.",
            ),
            (
                "implfreshlc_witness",
                "ImplFreshLC Nat.zero (ImplExpr.sort Level.zero) Nat.zero".to_string(),
                "ImplFreshLC.sort Nat.zero Level.zero Nat.zero".to_string(),
                "ImplFreshLC IS INHABITED. Both of its restrictions — the strict bound and the \
                 freshness — are vacuous on a sort, which is exactly the shape a stored context \
                 entry has in the smallest real case.",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: ty,
                value_src: Some(val),
                is_axiom: false,
                description: format!("{why} Zero axiom_deps."),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: HashSet::new(),
            })?;
        }

        self.add_definition(SpecDefinition {
            name: "tenvrepc_empty".to_string(),
            type_src: format!("TEnvRepC {tenv} {tenvk}"),
            value_src: Some(format!(
                "fun (nm : Name) (ci : ImplConstInfo) (us : ListType Level) \
                 (rho : ListType Nat) \
                 (h : Eq (OptionType ImplConstInfo) (OptionType.none ImplConstInfo) \
                 (OptionType.some ImplConstInfo ci)) => \
                 option_none_ne_some ImplConstInfo ci \
                 (Eq (OptionType KExpr) ({tenvk} nm) (OptionType.some KExpr \
                 (to_kexpr (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) rho))) h"
            )),
            is_axiom: false,
            description: concat!(
                "TEnvRepC IS INHABITED: the empty layer-1 environment represents the empty ",
                "layer-2 one, vacuously — its resolution hypothesis is `none = some ci`, which ",
                "option_none_ne_some eliminates. Small, but it is the difference between a ",
                "hypothesis and an unsatisfiable one, and impl_infer_sound's const rule rests ",
                "on it. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TEnvRepC".to_string(),
                "option_none_ne_some".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "impl_sound_guard_witness".to_string(),
            type_src: format!(
                "ImplSoundGuard {tenv} (ListType.nil Name) Nat.zero LCtx.nil \
                 (ImplExpr.sort Level.zero) (ImplExpr.sort (Level.succ Level.zero)) Nat.zero \
                 {deriv}"
            ),
            value_src: Some("ImplUnit.mk".to_string()),
            is_axiom: false,
            description: concat!(
                "ImplSoundGuard IS INHABITED, on C1's own sort witness. The guard is reducible, ",
                "so at a sort derivation it iota-reduces to ImplUnit and ImplUnit.mk closes it. ",
                "That this type-checks is the content: it says the guard admits a real ",
                "derivation rather than being Empty everywhere, which an all-Empty guard would ",
                "make impl_infer_sound true and empty. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplSoundGuard".to_string(),
                "ImplInfer.sort".to_string(),
                "ImplUnit.mk".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // THE ONE THAT MATTERS: the theorem, run.
        self.add_definition(SpecDefinition {
            name: "impl_infer_sound_witness".to_string(),
            type_src: format!(
                "TypingCtxConv {tenvk} (ListType.nil KExpr) (KExpr.sort Level.zero) \
                 (KExpr.sort (Level.succ Level.zero))"
            ),
            value_src: Some(format!(
                "impl_infer_sound {tenv} {tenvk} (ListType.nil Name) tenvrepc_empty \
                 Nat.zero LCtx.nil (ImplExpr.sort Level.zero) \
                 (ImplExpr.sort (Level.succ Level.zero)) Nat.zero {deriv} \
                 impl_sound_guard_witness (ListType.nil Nat) (ListType.nil KExpr) \
                 ctx_rep_nil_witness"
            )),
            is_axiom: false,
            description: concat!(
                "**THE M4 THEOREM, RUN.** A layer-1 ImplInfer derivation goes in and a real ",
                "layer-2 TypingCtxConv derivation comes out, with every hypothesis discharged ",
                "by a witness rather than assumed: tenvrepc_empty for the environment, ",
                "ctx_rep_nil_witness (C4's) for the context, impl_sound_guard_witness for the ",
                "guard. ",
                "This is what makes impl_infer_sound a result rather than a NON-result. The ",
                "premise-satisfiability gate states the principle exactly — a conditional ",
                "theorem whose premises cannot be satisfied passes the axiom census, the ",
                "domain-axiom count and the DerivedProved-debt count while looking green. Note ",
                "the STATED type mentions neither ImplExpr nor to_kexpr: the layer-1 subject ",
                "and the translation have both been carried out by computation, so this is also ",
                "a live check that the erasure computes. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "impl_infer_sound".to_string(),
                "tenvrepc_empty".to_string(),
                "impl_sound_guard_witness".to_string(),
                "ctx_rep_nil_witness".to_string(),
                "ImplInfer.sort".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "impl_infer_sound_tests.rs"]
mod tests;

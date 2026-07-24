// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Canonical forms at Pi type for a CONTEXT-INDEXED, SYNTAX-DIRECTED
//! (conv-free) typing fragment `CtxTyping` (Aristotle port-back, Item 4).
//!
//! Clean-kernel port of the Aristotle-proven Lean development
//! `proofs/lean-aristotle/canonical_forms_pi.lean` (0 sorry). The Lean proof
//! is the STRATEGY guide only; every lemma here is a closed spec proof term
//! re-checked by the Clean kernel at spec build (`DerivedProved`, empty
//! non-foundational closure).
//!
//! ## SCOPE (the honesty note that IS the point of this module)
//!
//! `CtxTyping` is a NEW OBJECT OF STUDY registered by this module: a
//! list-context-indexed (`ListType KExpr`), SYNTAX-DIRECTED dependent typing
//! judgment with a de Bruijn `var` rule and NO conversion rule. It is a
//! DIFFERENT judgment from the spec's context-free five-rule `Typing`
//! (typing_def_eq.rs, which has `conv` and no `var`); **no relation between
//! the two is claimed, stated, or implied** — there is no embedding lemma in
//! either direction in this module, and none should be inferred from the
//! names. The conv-extension of canonical forms additionally requires
//! DefEq-consistency (a Pi type is never DefEq to a Sort or a neutral —
//! Church-Rosser-grade input, not yet in-tree), which is a strictly deeper,
//! SEPARATE obligation. What is proved here is the canonical-forms
//! combinatorics of the conv-free fragment, exactly as in the Lean source.
//!
//! Normality is over the exact in-tree NON-reflexive single-step relation
//! **`beta_reduces_bd`** (par_reduction.rs: the iota-free 10-constructor beta
//! fragment with full congruence), the in-tree counterpart of the Lean file's
//! `Step`: `is_normal_bd e := forall e', beta_reduces_bd e e' -> Empty`.
//!
//! ## Registered objects
//!
//! Inductives (object-of-study, `FoundationalRule` via `add_inductive` — real
//! kernel inductives with generated recursors, NOT census axioms):
//!   - `CtxLookup ctx i A` — de Bruijn lookup into a `ListType KExpr` context.
//!   - `CtxTyping ctx e T` — the syntax-directed judgment
//!     (var/sort/pi/lam/app/let_; NO conv, NO const rule), mirroring the rule
//!     SHAPES of the Lean source (`Sort n : Sort (n+1)`, pi at `imax_nat`,
//!     dependent app at `instantiate B a`, var at `lift_at A 0 (i+1)`, the
//!     standard dependent let_ at `instantiate B v`).
//!   - `CanonAt e T` — the canonical-shape/type-head correlation (lam:pi,
//!     sort:sort, pi:sort) the induction carries.
//!   - `IsLamShape e` — "e is a lambda" (the Lean `∃ A' b, e = .lam A' b`).
//!
//! Ladder (all `DerivedProved`, zero axiom_deps):
//!   1. `ctx_is_nil` / `is_normal_bd` — semireducible Type-valued predicates.
//!   2. `ctx_lookup_not_nil` — no lookup into the empty context.
//!   3. `ctx_typing_normal_canonical` — every EMPTY-context `beta_reduces_bd`-
//!      normal `CtxTyping`-typable term is canonical with matching type head
//!      (the Lean `closed_normal_form`, strengthened with the type
//!      correlation; induction on the typing derivation).
//!   4. `ctx_canonical_forms_pi` — THE GOAL: a closed normal `CtxTyping`-
//!      typable term of Pi type is a lambda.
//!   5. `ctx_canonical_forms_pi_is_lam` — the computational `kexpr_is_lam`
//!      Bool pin of the same statement.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the context-indexed syntax-directed canonical-forms fragment.
    ///
    /// Must run after `add_expr_model` (KExpr/ListType/lift_at/instantiate),
    /// `add_foundation_types` (Nat/Bool/Empty/Eq), `add_typing_universe_levels`
    /// (imax_nat), `add_expr_model_pi_discrimination` (sort_ne_pi),
    /// `add_par_reduction` (beta_reduces_bd), and `add_complete_development`
    /// (kexpr_is_lam). Purely additive; zero new axioms (all new constants are
    /// inductives/constructors/recursors or DerivedProved terms).
    pub(super) fn add_ctx_canonical_forms(&mut self) -> Result<(), SpecError> {
        self.add_ctx_canonical_forms_inductives()?;
        self.add_ctx_canonical_forms_predicates()?;
        self.add_ctx_canonical_forms_lemmas()?;
        Ok(())
    }

    /// The four object-of-study inductives.
    fn add_ctx_canonical_forms_inductives(&mut self) -> Result<(), SpecError> {
        // CtxLookup: de Bruijn lookup into a ListType KExpr context.
        // CtxLookup ctx i A holds iff the i-th entry of ctx is A.
        self.add_inductive(
            r"inductive CtxLookup : ListType KExpr → Nat → KExpr → Type
| here : forall (A : KExpr) (rest : ListType KExpr), CtxLookup (ListType.cons KExpr A rest) Nat.zero A
| there : forall (B : KExpr) (rest : ListType KExpr) (i : Nat) (A : KExpr), CtxLookup rest i A → CtxLookup (ListType.cons KExpr B rest) (Nat.succ i) A",
            "CtxLookup ctx i A: the i-th entry of the ListType KExpr context ctx is A (de Bruijn \
             lookup; here = index 0 at the head, there = shift into the tail). Context substrate \
             for the SEPARATE context-indexed syntax-directed judgment CtxTyping (object of \
             study; NOT the spec's context-free Typing). Part of the ctx canonical-forms \
             fragment (Aristotle port, Item 4).",
        )?;

        // CtxTyping: the context-indexed SYNTAX-DIRECTED judgment. Rule
        // shapes mirror the Lean source (and the shapes of the context-free
        // rules where they overlap), but this is a NEW judgment: it has a de
        // Bruijn var rule and NO conversion (conv) rule and NO const rule.
        self.add_inductive(
            r"inductive CtxTyping : ListType KExpr → KExpr → KExpr → Type
| var : forall (ctx : ListType KExpr) (i : Nat) (A : KExpr), CtxLookup ctx i A → CtxTyping ctx (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| sort : forall (ctx : ListType KExpr) (n : Level), CtxTyping ctx (KExpr.sort n) (KExpr.sort (Level.succ n))
| pi : forall (ctx : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level), CtxTyping ctx A (KExpr.sort n) → CtxTyping (ListType.cons KExpr A ctx) B (KExpr.sort m) → CtxTyping ctx (KExpr.pi A B) (KExpr.sort (Level.imax n m))
| lam : forall (ctx : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), CtxTyping ctx A (KExpr.sort u) → CtxTyping (ListType.cons KExpr A ctx) b B → CtxTyping ctx (KExpr.lam A b) (KExpr.pi A B)
| app : forall (ctx : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), CtxTyping ctx f (KExpr.pi A B) → CtxTyping ctx a A → CtxTyping ctx (KExpr.app f a) (instantiate B a)
| let_ : forall (ctx : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), CtxTyping ctx ty (KExpr.sort u) → CtxTyping ctx v ty → CtxTyping (ListType.cons KExpr ty ctx) b B → CtxTyping ctx (KExpr.let_ ty v b) (instantiate B v)",
            "CtxTyping ctx e T: CONTEXT-INDEXED, SYNTAX-DIRECTED (conv-free) dependent typing \
             fragment — a NEW object of study, ported from \
             proofs/lean-aristotle/canonical_forms_pi.lean. Six rules: de Bruijn var (type \
             lift_at A 0 (i+1)), sort (Sort n : Sort (n+1)), dependent pi formation (codomain \
             under the extended context, level imax_nat), lam, dependent app (result type \
             instantiate B a), and the standard dependent let_ rule (the annotation ty is a \
             sort, the value v : ty, the body b : B under the ty-extended context, and the \
             let's type is instantiate B v — instantiate-typed exactly like app). It \
             deliberately OMITS the conversion rule: with untyped conv, \
             canonical forms additionally requires DefEq-consistency (a Pi type is never DefEq \
             to a Sort or a neutral) — a strictly deeper obligation not yet in-tree; the \
             conv-extension is gated on it. This judgment is DISTINCT from the spec's \
             context-free Typing (which has conv and no var rule); no relation between the two \
             is claimed or implied. Part of the ctx canonical-forms fragment (Aristotle port, \
             Item 4).",
        )?;

        // CanonAt: canonical shape correlated with the type head. The
        // strengthened induction target: lam at pi type, sort at sort type,
        // pi at sort type.
        self.add_inductive(
            r"inductive CanonAt : KExpr → KExpr → Type
| lam_pi : forall (A : KExpr) (b : KExpr) (P : KExpr) (Q : KExpr), CanonAt (KExpr.lam A b) (KExpr.pi P Q)
| sort_sort : forall (n : Level) (m : Level), CanonAt (KExpr.sort n) (KExpr.sort m)
| pi_sort : forall (A : KExpr) (B : KExpr) (m : Level), CanonAt (KExpr.pi A B) (KExpr.sort m)",
            "CanonAt e T: e is canonical WITH matching type head — a lambda at a Pi type, a sort \
             at a Sort type, or a Pi at a Sort type. The strengthened target of the \
             canonical-forms induction over the syntax-directed CtxTyping fragment (carrying the \
             type-head correlation makes the app case self-contained: the head's type is a Pi, \
             so the head must be a lambda and a beta_reduces_bd redex fires). Encodes the Lean \
             disjunction of closed_normal_form together with the type information. Part of the \
             ctx canonical-forms fragment (Aristotle port, Item 4).",
        )?;

        // IsLamShape: "e is a lambda" — the Lean `∃ A' b, e = .lam A' b` as
        // an index-based witness.
        self.add_inductive(
            r"inductive IsLamShape : KExpr → Type
| intro : forall (A : KExpr) (b : KExpr), IsLamShape (KExpr.lam A b)",
            "IsLamShape e: e is a lambda (inhabited exactly when e = KExpr.lam A b for some A, \
             b) — the index-based encoding of the Lean conclusion (exists A' b, e = lam A' b) of \
             canonical_forms_pi. Part of the ctx canonical-forms fragment (Aristotle port, \
             Item 4).",
        )?;

        Ok(())
    }

    /// The two semireducible Type-valued predicates.
    fn add_ctx_canonical_forms_predicates(&mut self) -> Result<(), SpecError> {
        // ctx_is_nil: large-elimination discriminator on the context — nil ->
        // Nat (inhabited by Nat.zero), cons -> Empty. Semireducible so the
        // kernel can reduce it at literal nil/cons contexts during checking.
        self.add_definition_reducible(SpecDefinition {
            name: "ctx_is_nil".to_string(),
            type_src: "ListType KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (ctx : ListType KExpr) => ",
                    "ListType.rec KExpr (fun (_ : ListType KExpr) => Type) ",
                    "Nat ",
                    "(fun (_ : KExpr) (_ : ListType KExpr) (_ : Type) => Empty) ",
                    "ctx"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Large-elimination discriminator for the empty context: ctx_is_nil ctx is Nat ",
                "(inhabited, witness Nat.zero) when ctx is ListType.nil and Empty when ctx is a ",
                "cons. The Type-valued \"ctx = nil\" evidence the canonical-forms induction ",
                "threads (kexpr_not_pi precedent). Semireducible so it computes at literal ",
                "contexts. Part of the ctx canonical-forms fragment (Aristotle port, Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ListType".to_string(),
                "ListType.rec".to_string(),
                "KExpr".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // is_normal_bd: normality for the NON-reflexive iota-free single-step
        // beta relation beta_reduces_bd — "no step applies", the honest
        // classical notion for a non-reflexive step relation (the in-tree
        // counterpart of the Lean file's is_normal over Step).
        self.add_definition_reducible(SpecDefinition {
            name: "is_normal_bd".to_string(),
            type_src: "KExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) => ",
                    "forall (e' : KExpr), beta_reduces_bd e e' -> Empty"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Normality for the NON-reflexive iota-free single-step beta relation ",
                "beta_reduces_bd (par_reduction.rs): is_normal_bd e holds iff NO beta_reduces_bd ",
                "step applies to e. This is a statement about beta_reduces_bd ONLY (not the full ",
                "beta_reduces, whose env-dependent iota arm is a different relation; not ",
                "whnf_step). The in-tree counterpart of is_normal over Step in ",
                "proofs/lean-aristotle/canonical_forms_pi.lean. Semireducible so normality ",
                "hypotheses can be applied in proof terms. Part of the ctx canonical-forms ",
                "fragment (Aristotle port, Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "Empty".to_string(),
                "KExpr".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The canonical-forms ladder.
    fn add_ctx_canonical_forms_lemmas(&mut self) -> Result<(), SpecError> {
        // ctx_lookup_not_nil: there is no lookup into the empty context.
        // CtxLookup.rec; both constructors conclude at a cons context, where
        // ctx_is_nil reduces to Empty, so each arm is the identity on Empty.
        self.add_definition(SpecDefinition {
            name: "ctx_lookup_not_nil".to_string(),
            type_src: concat!(
                "forall (ctx : ListType KExpr) (i : Nat) (A : KExpr), ",
                "CtxLookup ctx i A -> ctx_is_nil ctx -> Empty"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (ctx : ListType KExpr) (i : Nat) (A : KExpr) (hlk : CtxLookup ctx i A) => ",
                    "CtxLookup.rec ",
                    "(fun (c : ListType KExpr) (j : Nat) (X : KExpr) (_h : CtxLookup c j X) => ",
                    "ctx_is_nil c -> Empty) ",
                    "(fun (A0 : KExpr) (rest : ListType KExpr) (h : Empty) => h) ",
                    "(fun (B0 : KExpr) (rest : ListType KExpr) (j : Nat) (A0 : KExpr) ",
                    "(_hlk : CtxLookup rest j A0) (_ih : ctx_is_nil rest -> Empty) ",
                    "(h : Empty) => h) ",
                    "ctx i A hlk"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "No CtxLookup into the empty context: CtxLookup ctx i A -> ctx_is_nil ctx -> ",
                "Empty. CtxLookup.rec; both constructors conclude at a cons context, where the ",
                "semireducible ctx_is_nil computes to Empty, so both arms are the identity. The ",
                "var-rule refutation of the empty-context canonical-forms induction (the Lean ",
                "`simp at hlk` step). DerivedProved, zero axiom_deps. Part of the ctx ",
                "canonical-forms fragment (Aristotle port, Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxLookup".to_string(),
                "CtxLookup.rec".to_string(),
                "ctx_is_nil".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_typing_normal_canonical: every empty-context, beta_reduces_bd-
        // normal, CtxTyping-typable term is canonical with matching type head.
        self.add_definition(SpecDefinition {
            name: "ctx_typing_normal_canonical".to_string(),
            type_src: concat!(
                "forall (ctx : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "CtxTyping ctx e T -> ctx_is_nil ctx -> is_normal_bd e -> CanonAt e T"
            )
            .to_string(),
            value_src: Some(ctx_typing_normal_canonical_proof()),
            is_axiom: false,
            description: concat!(
                "Every EMPTY-context (ctx_is_nil), beta_reduces_bd-NORMAL (is_normal_bd), ",
                "CtxTyping-typable term is canonical with matching type head: a lambda at a Pi ",
                "type, a sort at a Sort type, or a Pi at a Sort type (CanonAt e T). Induction on ",
                "the SYNTAX-DIRECTED (conv-free) CtxTyping derivation: var is refuted by ",
                "ctx_lookup_not_nil; sort/pi/lam conclude by the matching CanonAt constructor; ",
                "in the app arm the head f is normal (app_left congruence contrapositive) and of ",
                "Pi type, so the IH forces f canonical-at-Pi — the sort/pi shapes live at ",
                "Sort-headed types, refuted by the landed sort_ne_pi discrimination (via an ",
                "Eq-generalized elimination motive fed Eq.refl), and the lam ",
                "shape fires a beta_reduces_bd.beta redex against normality, so the app case is ",
                "vacuous; the let_ arm is likewise vacuous — a let_ is a zeta redex, so ",
                "beta_reduces_bd.zeta contradicts normality (CanonAt has no let_-headed shape). ",
                "The Lean closed_normal_form strengthened with the type-head ",
                "correlation. Holds for the conv-free fragment ONLY: with an untyped conv rule ",
                "the same statement needs DefEq-consistency (not yet in-tree). DerivedProved, ",
                "zero axiom_deps. Part of the ctx canonical-forms fragment (Aristotle port, ",
                "Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxTyping".to_string(),
                "CtxTyping.rec".to_string(),
                "CtxLookup".to_string(),
                "ctx_lookup_not_nil".to_string(),
                "ctx_is_nil".to_string(),
                "is_normal_bd".to_string(),
                "CanonAt".to_string(),
                "CanonAt.rec".to_string(),
                "CanonAt.lam_pi".to_string(),
                "CanonAt.sort_sort".to_string(),
                "CanonAt.pi_sort".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.beta".to_string(),
                "beta_reduces_bd.app_left".to_string(),
                "beta_reduces_bd.zeta".to_string(),
                "sort_ne_pi".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.refl".to_string(),
                "instantiate".to_string(),
                "lift_at".to_string(),
                "imax_nat".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_canonical_forms_pi — THE GOAL: canonical forms at Pi type for
        // the syntax-directed fragment.
        self.add_definition(SpecDefinition {
            name: "ctx_canonical_forms_pi".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (A : KExpr) (B : KExpr), ",
                "CtxTyping (ListType.nil KExpr) e (KExpr.pi A B) -> ",
                "is_normal_bd e -> IsLamShape e"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (A : KExpr) (B : KExpr) ",
                    "(h : CtxTyping (ListType.nil KExpr) e (KExpr.pi A B)) ",
                    "(hn : is_normal_bd e) => ",
                    "CanonAt.rec ",
                    "(fun (x : KExpr) (X : KExpr) (_c : CanonAt x X) => ",
                    "Eq KExpr X (KExpr.pi A B) -> IsLamShape x) ",
                    "(fun (A0 : KExpr) (b0 : KExpr) (P : KExpr) (Q : KExpr) ",
                    "(_heq : Eq KExpr (KExpr.pi P Q) (KExpr.pi A B)) => ",
                    "IsLamShape.intro A0 b0) ",
                    "(fun (n : Level) (m : Level) ",
                    "(heq : Eq KExpr (KExpr.sort m) (KExpr.pi A B)) => ",
                    "sort_ne_pi m A B (IsLamShape (KExpr.sort n)) heq) ",
                    "(fun (A0 : KExpr) (B0 : KExpr) (m : Level) ",
                    "(heq : Eq KExpr (KExpr.sort m) (KExpr.pi A B)) => ",
                    "sort_ne_pi m A B (IsLamShape (KExpr.pi A0 B0)) heq) ",
                    "e (KExpr.pi A B) ",
                    "(ctx_typing_normal_canonical (ListType.nil KExpr) e (KExpr.pi A B) ",
                    "h Nat.zero hn) ",
                    "(Eq.refl KExpr (KExpr.pi A B))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "CANONICAL FORMS AT PI TYPE for the context-indexed SYNTAX-DIRECTED (conv-free) ",
                "fragment CtxTyping: every EMPTY-context term in beta_reduces_bd-NORMAL form ",
                "whose CtxTyping type is a Pi type is a lambda (IsLamShape). Kernel-checked port ",
                "of canonical_forms_pi in proofs/lean-aristotle/canonical_forms_pi.lean: project ",
                "ctx_typing_normal_canonical through an Eq-generalized CanonAt elimination (the ",
                "sort/pi canonical shapes live at Sort types, refuted by sort_ne_pi). SCOPE: a ",
                "theorem about ",
                "the conv-free CtxTyping fragment ONLY; the conv-extension is gated on ",
                "DefEq-consistency (not yet in-tree), and no claim is made about the spec's ",
                "context-free Typing judgment. DerivedProved, zero axiom_deps. Part of the ctx ",
                "canonical-forms fragment (Aristotle port, Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxTyping".to_string(),
                "ctx_typing_normal_canonical".to_string(),
                "ctx_is_nil".to_string(),
                "is_normal_bd".to_string(),
                "CanonAt".to_string(),
                "CanonAt.rec".to_string(),
                "IsLamShape".to_string(),
                "IsLamShape.intro".to_string(),
                "ListType".to_string(),
                "sort_ne_pi".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_canonical_forms_pi_is_lam: the computational Bool pin — the
        // landed kexpr_is_lam discriminator returns true on the canonical
        // form. IsLamShape.rec; the arm is Eq.refl (kexpr_is_lam computes to
        // Bool.true on a literal lam).
        self.add_definition(SpecDefinition {
            name: "ctx_canonical_forms_pi_is_lam".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (A : KExpr) (B : KExpr), ",
                "CtxTyping (ListType.nil KExpr) e (KExpr.pi A B) -> ",
                "is_normal_bd e -> Eq Bool (kexpr_is_lam e) Bool.true"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (A : KExpr) (B : KExpr) ",
                    "(h : CtxTyping (ListType.nil KExpr) e (KExpr.pi A B)) ",
                    "(hn : is_normal_bd e) => ",
                    "IsLamShape.rec ",
                    "(fun (x : KExpr) (_w : IsLamShape x) => ",
                    "Eq Bool (kexpr_is_lam x) Bool.true) ",
                    "(fun (A0 : KExpr) (b0 : KExpr) => Eq.refl Bool Bool.true) ",
                    "e (ctx_canonical_forms_pi e A B h hn)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Computational pin of ctx_canonical_forms_pi through the landed kexpr_is_lam ",
                "Bool discriminator (complete_development.rs): a closed beta_reduces_bd-normal ",
                "CtxTyping-typable term of Pi type satisfies kexpr_is_lam e = true. ",
                "IsLamShape.rec on the canonical-forms witness; the lambda arm is Eq.refl ",
                "(kexpr_is_lam computes to Bool.true on a literal lam). Same scope as ",
                "ctx_canonical_forms_pi: the conv-free CtxTyping fragment ONLY. DerivedProved, ",
                "zero axiom_deps. Part of the ctx canonical-forms fragment (Aristotle port, ",
                "Item 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxTyping".to_string(),
                "ctx_canonical_forms_pi".to_string(),
                "is_normal_bd".to_string(),
                "IsLamShape".to_string(),
                "IsLamShape.rec".to_string(),
                "kexpr_is_lam".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `ctx_typing_normal_canonical`. `CtxTyping.rec` with
/// motive `ctx_is_nil ctx -> is_normal_bd e -> CanonAt e T` (6 arms):
/// var refutes via `ctx_lookup_not_nil`; sort/pi/lam are the matching
/// `CanonAt` constructors; app eliminates the head's `CanonAt f (pi A B)` IH
/// with an Eq-generalized motive (`Eq KExpr X (KExpr.pi A B)`, fed
/// `Eq.refl`) — the lam shape fires a `beta_reduces_bd.beta` redex against
/// normality, and the sort/pi shapes live at Sort-headed types, refuted by
/// the landed `sort_ne_pi` discrimination; the trailing `let_` arm is vacuous
/// — a `let_` is a `beta_reduces_bd.zeta` redex, contradicting normality
/// (`CanonAt` has no `let_`-headed constructor), so the arm is `Empty.rec`.
fn ctx_typing_normal_canonical_proof() -> String {
    concat!(
        "fun (ctx0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (h0 : CtxTyping ctx0 e0 T0) => ",
        "CtxTyping.rec ",
        "(fun (ctx : ListType KExpr) (x : KExpr) (X : KExpr) (_h : CtxTyping ctx x X) => ",
        "ctx_is_nil ctx -> is_normal_bd x -> CanonAt x X) ",
        // var ctx i A hlk — refuted: no lookup into the empty context.
        "(fun (ctx : ListType KExpr) (i : Nat) (A : KExpr) (hlk : CtxLookup ctx i A) ",
        "(hnil : ctx_is_nil ctx) (_hn : is_normal_bd (KExpr.bvar i)) => ",
        "Empty.rec ",
        "(fun (_ : Empty) => CanonAt (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))) ",
        "(ctx_lookup_not_nil ctx i A hlk hnil)) ",
        // sort ctx n
        "(fun (ctx : ListType KExpr) (n : Level) ",
        "(_hnil : ctx_is_nil ctx) (_hn : is_normal_bd (KExpr.sort n)) => ",
        "CanonAt.sort_sort n (Level.succ n)) ",
        // pi ctx A B n m hA hB ihA ihB
        "(fun (ctx : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) ",
        "(_hA : CtxTyping ctx A (KExpr.sort n)) ",
        "(_hB : CtxTyping (ListType.cons KExpr A ctx) B (KExpr.sort m)) ",
        "(_ihA : ctx_is_nil ctx -> is_normal_bd A -> CanonAt A (KExpr.sort n)) ",
        "(_ihB : ctx_is_nil (ListType.cons KExpr A ctx) -> is_normal_bd B -> ",
        "CanonAt B (KExpr.sort m)) ",
        "(_hnil : ctx_is_nil ctx) (_hn : is_normal_bd (KExpr.pi A B)) => ",
        "CanonAt.pi_sort A B (Level.imax n m)) ",
        // lam ctx A b B u hA hb ihA ihb
        "(fun (ctx : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
        "(_hA : CtxTyping ctx A (KExpr.sort u)) ",
        "(_hb : CtxTyping (ListType.cons KExpr A ctx) b B) ",
        "(_ihA : ctx_is_nil ctx -> is_normal_bd A -> CanonAt A (KExpr.sort u)) ",
        "(_ihb : ctx_is_nil (ListType.cons KExpr A ctx) -> is_normal_bd b -> CanonAt b B) ",
        "(_hnil : ctx_is_nil ctx) (_hn : is_normal_bd (KExpr.lam A b)) => ",
        "CanonAt.lam_pi A b A B) ",
        // app ctx f a A B hf ha ihf iha — the head is normal (app_left
        // contrapositive) and canonical at a Pi type; eliminate its CanonAt
        // with the Eq-generalized motive.
        "(fun (ctx : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) ",
        "(_hf : CtxTyping ctx f (KExpr.pi A B)) (_ha : CtxTyping ctx a A) ",
        "(ihf : ctx_is_nil ctx -> is_normal_bd f -> CanonAt f (KExpr.pi A B)) ",
        "(_iha : ctx_is_nil ctx -> is_normal_bd a -> CanonAt a A) ",
        "(hnil : ctx_is_nil ctx) (hn : is_normal_bd (KExpr.app f a)) => ",
        "CanonAt.rec ",
        "(fun (x : KExpr) (X : KExpr) (_c : CanonAt x X) => ",
        "Eq KExpr X (KExpr.pi A B) -> is_normal_bd (KExpr.app x a) -> ",
        "CanonAt (KExpr.app x a) (instantiate B a)) ",
        // lam_pi A0 b0 P Q — a beta redex at the head, killed by normality.
        "(fun (A0 : KExpr) (b0 : KExpr) (P : KExpr) (Q : KExpr) ",
        "(_heq : Eq KExpr (KExpr.pi P Q) (KExpr.pi A B)) ",
        "(hna : is_normal_bd (KExpr.app (KExpr.lam A0 b0) a)) => ",
        "Empty.rec ",
        "(fun (_ : Empty) => CanonAt (KExpr.app (KExpr.lam A0 b0) a) (instantiate B a)) ",
        "(hna (instantiate b0 a) (beta_reduces_bd.beta A0 b0 a))) ",
        // sort_sort n m — the type head is a Sort, not a Pi: sort_ne_pi.
        "(fun (n : Level) (m : Level) (heq : Eq KExpr (KExpr.sort m) (KExpr.pi A B)) => ",
        "sort_ne_pi m A B ",
        "(is_normal_bd (KExpr.app (KExpr.sort n) a) -> ",
        "CanonAt (KExpr.app (KExpr.sort n) a) (instantiate B a)) ",
        "heq) ",
        // pi_sort A0 B0 m — same Sort-headed refutation.
        "(fun (A0 : KExpr) (B0 : KExpr) (m : Level) ",
        "(heq : Eq KExpr (KExpr.sort m) (KExpr.pi A B)) => ",
        "sort_ne_pi m A B ",
        "(is_normal_bd (KExpr.app (KExpr.pi A0 B0) a) -> ",
        "CanonAt (KExpr.app (KExpr.pi A0 B0) a) (instantiate B a)) ",
        "heq) ",
        "f (KExpr.pi A B) ",
        "(ihf hnil ",
        "(fun (f' : KExpr) (hs : beta_reduces_bd f f') => ",
        "hn (KExpr.app f' a) (beta_reduces_bd.app_left f f' a hs))) ",
        "(Eq.refl KExpr (KExpr.pi A B)) hn) ",
        // let_ ctx ty v b B u hty hv hb ihty ihv ihb — a let_ is a zeta redex, so
        // it is never beta_reduces_bd-normal: fire beta_reduces_bd.zeta against the
        // normality hypothesis for Empty (CanonAt has no let_-headed constructor,
        // so this case is vacuous — exactly the lam-headed-app-is-a-beta-redex move).
        "(fun (ctx : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
        "(_hty : CtxTyping ctx ty (KExpr.sort u)) ",
        "(_hv : CtxTyping ctx v ty) ",
        "(_hb : CtxTyping (ListType.cons KExpr ty ctx) b B) ",
        "(_ihty : ctx_is_nil ctx -> is_normal_bd ty -> CanonAt ty (KExpr.sort u)) ",
        "(_ihv : ctx_is_nil ctx -> is_normal_bd v -> CanonAt v ty) ",
        "(_ihb : ctx_is_nil (ListType.cons KExpr ty ctx) -> is_normal_bd b -> CanonAt b B) ",
        "(_hnil : ctx_is_nil ctx) (hn : is_normal_bd (KExpr.let_ ty v b)) => ",
        "Empty.rec ",
        "(fun (_ : Empty) => CanonAt (KExpr.let_ ty v b) (instantiate B v)) ",
        "(hn (instantiate b v) (beta_reduces_bd.zeta ty v b))) ",
        // indices + major
        "ctx0 e0 T0 h0"
    )
    .to_string()
}

#[cfg(test)]
#[path = "ctx_canonical_forms_tests.rs"]
mod ctx_canonical_forms_tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strong normalization of the IOTA-FREE beta relation `beta_reduces_bd` for
//! well-typed terms (the beta-only leg of `whnf_terminates_well_typed`).
//!
//! Clean-kernel port of the Aristotle-proven Lean development
//! `proofs/lean-aristotle/beta_sn_kexpr.lean` (0 sorry). The Lean proof is the
//! STRATEGY guide; every lemma here is a closed spec proof term re-checked by
//! the Clean kernel at spec build (`DerivedProved`, empty non-foundational
//! closure). No Lean tactic output is trusted.
//!
//! ## The exact relation targeted (honesty note)
//!
//! The census axiom `whnf_terminates_well_typed` (`whnf_lemmas.rs`,
//! `forall e T, has_type e T -> terminates_whnf e`) is termination of
//! `whnf_step = beta_reduces | delta_reduces`, where `beta_reduces`
//! (`whnf_reduction.rs`) itself carries the env-dependent 11th arm
//! `iota : iota_reduces e e' -> beta_reduces e e'`. The FULL axiom is NOT
//! discharged here and is left untouched. What IS proved is strong
//! normalization of **`beta_reduces_bd`** (`par_reduction.rs`) — the existing
//! iota-free single-step beta relation, i.e. the 13 non-iota constructors of
//! `beta_reduces` (beta + zeta head contractions, app/lam/pi/forall_ and
//! let_ty/let_val/let_body congruences) — for every term typable in the spec's
//! context-free `Typing` fragment. Delta and iota legs remain axiom-backed
//! debt on the census axiom.
//!
//! ## Proof structure (mirrors the Lean file)
//!
//! The spec's `Typing` judgment is CONTEXT-FREE with NO rule for `bvar` (or
//! `const`), so every typable term is bvar-free. Bvar-freeness is encoded as
//! `Eq Nat (bvar_ceiling e) Nat.zero` over the landed Brick-1 ceiling measure
//! (`expr_model_inst_ceiling.rs`): `bvar_ceiling` sums `succ i` over `bvar i`
//! leaves, so ceiling 0 <-> no bvar node. On bvar-free terms `instantiate` is
//! the identity (`inst_above_ceiling_id` at depth 0), hence every
//! `beta_reduces_bd` step strictly decreases `expr_size`, and accessibility
//! (`beta_bd_acc`, the `whnf_acc`-shaped inductive over `beta_reduces_bd`)
//! follows by strong induction on the size via the landed `nat_strong_rec`
//! (Nat-bounded course-of-values recursion — the spec fragment has no
//! `WellFounded`/`brecOn`).
//!
//! Ladder (all `DerivedProved`, zero axiom_deps):
//!   1. `nat_add_zero_zero`, `lt_add_right_mono`, `lt_add_left_mono` — small
//!      Nat/Lt toolkit gaps (the zero-sum decomposition direction reuses the
//!      landed `nat_add_eq_zero_left/right` from `faithful_red_env.rs`).
//!   2. `CeilZeroBox` + `ceil_zero_unbox` — Type-valued box around the Prop
//!      equality `bvar_ceiling e = 0` (`HeadConstBox` precedent), because the
//!      axiomatized `Typing.rec` motive lands in Type.
//!   3. `typable_ceil_zero_box` / `typable_bvar_ceiling_zero` — every typable
//!      term is bvar-free (Typing.rec; conv arm forwards the IH).
//!   4. `inst_id_of_ceiling_zero` — `instantiate body val = body` on bvar-free
//!      bodies (specializes the Brick-1 keystone to depth 0).
//!   5. `beta_bd_step_preserves_ceiling_zero` / `beta_bd_step_decreases_size`
//!      — a `beta_reduces_bd` step out of a bvar-free term keeps it bvar-free
//!      and strictly decreases `expr_size` (beta_reduces_bd.rec, 13 arms; the
//!      zeta arm mirrors beta — on a bvar-free body the contractum IS the
//!      body, strictly below the let_ node via `size_let_thd`).
//!   6. `beta_bd_acc` + `beta_bd_acc_of_ceiling_zero` — accessibility of every
//!      bvar-free term by `nat_strong_rec` on `expr_size`.
//!   7. `beta_bd_sn_well_typed` / `beta_bd_sn_has_type` — the goal:
//!      `forall e T, Typing e T -> beta_bd_acc e`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the `beta_reduces_bd` strong-normalization ladder.
    ///
    /// Must run after `add_par_reduction` (`beta_reduces_bd`),
    /// `add_expr_model_inst_ceiling` (`bvar_ceiling` / `inst_above_ceiling_id`),
    /// `add_iota_core` (`nat_strong_rec`, `lt_trans`, `size_*`, `le_zero_n`),
    /// `add_typing_def_eq_typed_support` (`Typing.rec`),
    /// `add_whnf_reduction` (`expr_size`), and `add_faithful_red_env`
    /// (`nat_add_eq_zero_left/right` from the decidable-equality tower).
    /// Purely additive; zero new axioms.
    pub(super) fn add_beta_bd_sn(&mut self) -> Result<(), SpecError> {
        self.add_beta_bd_sn_arith()?;
        self.add_beta_bd_sn_ceiling()?;
        self.add_beta_bd_sn_step()?;
        self.add_beta_bd_sn_acc()?;
        Ok(())
    }

    /// Small Nat/Lt toolkit gaps the ladder composes from. All defeq-driven
    /// via the `Nat.add` reduction rules (`add a 0 ≡ a`,
    /// `add a (succ m) ≡ succ (add a m)`).
    ///
    /// The zero-sum DECOMPOSITION direction is NOT re-registered here: the
    /// ladder reuses the landed `nat_add_eq_zero_left` / `nat_add_eq_zero_right`
    /// from the decidable-equality tower (`faithful_red_env.rs`,
    /// `add_decidable_name_eq`) — which is why the `add_beta_bd_sn` stage sits
    /// AFTER `add_faithful_red_env` in `bundles.rs`.
    fn add_beta_bd_sn_arith(&mut self) -> Result<(), SpecError> {
        // nat_add_zero_zero : a = 0 -> b = 0 -> add a b = 0. Rewrite b to 0
        // via Eq.cong (add a 0 ≡ a definitionally), then chain with a = 0.
        self.add_definition(SpecDefinition {
            name: "nat_add_zero_zero".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat), Eq Nat a Nat.zero -> Eq Nat b Nat.zero -> ",
                "Eq Nat (Nat.add a b) Nat.zero"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (ha : Eq Nat a Nat.zero) ",
                    "(hb : Eq Nat b Nat.zero) => ",
                    "Eq.trans Nat (Nat.add a b) a Nat.zero ",
                    "(Eq.cong Nat Nat (fun (z : Nat) => Nat.add a z) b Nat.zero hb) ",
                    "ha"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Sum of zeros is zero: a = 0 -> b = 0 -> add a b = 0. Eq.cong rewrites the ",
                "second summand (add a 0 reduces to a), then Eq.trans with a = 0. DerivedProved, ",
                "zero axiom_deps. Part of the beta_reduces_bd SN ladder (Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.add".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_add_right_mono : Lt a b -> Lt (add a c) (add b c). Nat.rec on c;
        // the base reduces to the hypothesis, the succ arm is Lt.succ_lt_succ
        // on the IH (add x (succ m) ≡ succ (add x m)).
        self.add_definition(SpecDefinition {
            name: "lt_add_right_mono".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (c : Nat), ",
                "Lt a b -> Lt (Nat.add a c) (Nat.add b c)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) (h : Lt a b) => ",
                    "Nat.rec (fun (c0 : Nat) => Lt (Nat.add a c0) (Nat.add b c0)) ",
                    "h ",
                    "(fun (m : Nat) (ih : Lt (Nat.add a m) (Nat.add b m)) => ",
                    "Lt.succ_lt_succ (Nat.add a m) (Nat.add b m) ih) ",
                    "c"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Strict add-monotonicity in the left summand: Lt a b -> Lt (add a c) (add b c). ",
                "Nat.rec on c (base reduces to the hypothesis, succ via Lt.succ_lt_succ on the ",
                "IH). DerivedProved, zero axiom_deps. Part of the beta_reduces_bd SN ladder ",
                "(Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "Nat.rec".to_string(),
                "Nat.add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_add_left_mono : Lt a b -> Lt (add c a) (add c b). Lt.rec on the
        // proof; the zero_lt_succ arm reduces to Lt c (succ (add c m)) =
        // lt_add_succ_left, the succ_lt_succ arm is Lt.succ_lt_succ on the IH.
        self.add_definition(SpecDefinition {
            name: "lt_add_left_mono".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat) (c : Nat), ",
                "Lt a b -> Lt (Nat.add c a) (Nat.add c b)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) (h : Lt a b) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => Lt (Nat.add c x) (Nat.add c y)) ",
                    "(fun (m : Nat) => lt_add_succ_left c m) ",
                    "(fun (n : Nat) (m : Nat) (_hnm : Lt n m) ",
                    "(ih : Lt (Nat.add c n) (Nat.add c m)) => ",
                    "Lt.succ_lt_succ (Nat.add c n) (Nat.add c m) ih) ",
                    "a b h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Strict add-monotonicity in the right summand: Lt a b -> Lt (add c a) ",
                "(add c b). Lt.rec on the proof; zero_lt_succ reduces to lt_add_succ_left, ",
                "succ_lt_succ lifts the IH via Lt.succ_lt_succ. DerivedProved, zero axiom_deps. ",
                "Part of the beta_reduces_bd SN ladder (Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "lt_add_succ_left".to_string(),
                "Nat.add".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The bvar-freeness leg: the `CeilZeroBox` Type box, typable terms are
    /// bvar-free (`Typing.rec`), and instantiate-identity on bvar-free bodies.
    fn add_beta_bd_sn_ceiling(&mut self) -> Result<(), SpecError> {
        // CeilZeroBox e: Type-valued box around the Prop equality
        // bvar_ceiling e = 0. Needed because the axiomatized Typing.rec motive
        // lands in Type (the HeadConstBox precedent). One constructor wrapping
        // the Prop eq; CeilZeroBox.rec unwraps it.
        self.add_inductive(
            r"inductive CeilZeroBox (e : KExpr) : Type
| mk : Eq Nat (bvar_ceiling e) Nat.zero → CeilZeroBox e",
            "Type-valued box around the Prop equality bvar_ceiling e = 0 (bvar-freeness), \
             so the Type-motive Typing.rec can carry it. Part of the beta_reduces_bd SN \
             ladder (Aristotle port).",
        )?;

        // ceil_zero_unbox: project the Prop equality back out of the box.
        self.add_definition(SpecDefinition {
            name: "ceil_zero_unbox".to_string(),
            type_src: "forall (e : KExpr), CeilZeroBox e -> Eq Nat (bvar_ceiling e) Nat.zero"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (bx : CeilZeroBox e) => ",
                    "CeilZeroBox.rec e ",
                    "(fun (_b : CeilZeroBox e) => Eq Nat (bvar_ceiling e) Nat.zero) ",
                    "(fun (h : Eq Nat (bvar_ceiling e) Nat.zero) => h) ",
                    "bx"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Unbox the bvar-freeness witness: CeilZeroBox e -> bvar_ceiling e = 0, via the ",
                "single-constructor CeilZeroBox.rec. DerivedProved, zero axiom_deps. Part of ",
                "the beta_reduces_bd SN ladder (Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CeilZeroBox".to_string(),
                "CeilZeroBox.rec".to_string(),
                "bvar_ceiling".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // typable_ceil_zero_box: every typable term is bvar-free (boxed).
        // Typing.rec with motive CeilZeroBox e. The spec's context-free Typing
        // judgment is generated solely by sort/pi/lam/app (NO bvar or const
        // rule — faithful to the current fragment), and conv leaves the
        // subject term unchanged, so the ceiling is a sum of zeros throughout.
        self.add_definition(SpecDefinition {
            name: "typable_ceil_zero_box".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), Typing e T -> CeilZeroBox e".to_string(),
            value_src: Some(typable_ceil_zero_box_proof()),
            is_axiom: false,
            description: concat!(
                "Every typable term is bvar-free (boxed): Typing e T -> CeilZeroBox e. ",
                "Typing.rec; sort is a closed leaf, pi/lam/app compose the child witnesses via ",
                "nat_add_zero_zero (bvar_ceiling of a binder/app node is the sum of the child ",
                "ceilings), conv forwards the IH (the subject term is unchanged). Sound because ",
                "the spec's context-free Typing fragment has NO rule for bvar (or const). ",
                "DerivedProved, zero axiom_deps. Part of the beta_reduces_bd SN ladder ",
                "(Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing".to_string(),
                "Typing.rec".to_string(),
                "CeilZeroBox".to_string(),
                "CeilZeroBox.mk".to_string(),
                "ceil_zero_unbox".to_string(),
                "nat_add_zero_zero".to_string(),
                "bvar_ceiling".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // typable_bvar_ceiling_zero: the unboxed Prop form.
        self.add_definition(SpecDefinition {
            name: "typable_bvar_ceiling_zero".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (T : KExpr), Typing e T -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (T : KExpr) (h : Typing e T) => ",
                    "ceil_zero_unbox e (typable_ceil_zero_box e T h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Every typable term is bvar-free: Typing e T -> bvar_ceiling e = 0. Unboxes ",
                "typable_ceil_zero_box. DerivedProved, zero axiom_deps. Part of the ",
                "beta_reduces_bd SN ladder (Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ceil_zero_unbox".to_string(),
                "typable_ceil_zero_box".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // inst_id_of_ceiling_zero: instantiate is the identity on a bvar-free
        // body — the Brick-1 keystone inst_above_ceiling_id at depth 0, with
        // the Le bound transported from the ceiling-zero equality.
        self.add_definition(SpecDefinition {
            name: "inst_id_of_ceiling_zero".to_string(),
            type_src: concat!(
                "forall (body : KExpr) (val : KExpr), ",
                "Eq Nat (bvar_ceiling body) Nat.zero -> ",
                "Eq KExpr (instantiate body val) body"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (body : KExpr) (val : KExpr) ",
                    "(h : Eq Nat (bvar_ceiling body) Nat.zero) => ",
                    "inst_above_ceiling_id body val Nat.zero ",
                    "(Eq.subst Nat (fun (z : Nat) => Le z Nat.zero) ",
                    "Nat.zero (bvar_ceiling body) ",
                    "(Eq.symm Nat (bvar_ceiling body) Nat.zero h) ",
                    "(le_zero_n Nat.zero))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "instantiate body val = body on a bvar-free body (bvar_ceiling body = 0): the ",
                "Brick-1 keystone inst_above_ceiling_id specialized to depth 0, the Le bound ",
                "obtained by transporting Le 0 0 along the ceiling-zero equality. DerivedProved, ",
                "zero axiom_deps. Part of the beta_reduces_bd SN ladder (Aristotle port)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "inst_above_ceiling_id".to_string(),
                "bvar_ceiling".to_string(),
                "instantiate".to_string(),
                "le_zero_n".to_string(),
                "Le".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The two step lemmas over `beta_reduces_bd`: a single iota-free beta
    /// step out of a bvar-free term (i) preserves bvar-freeness and
    /// (ii) strictly decreases `expr_size`. Split in two (rather than the Lean
    /// file's single conjunction) so each `beta_reduces_bd.rec` motive stays a
    /// plain arrow — the Type-valued `AndType` cannot carry the Prop equality
    /// without an extra box, and neither induction needs the other's IH.
    fn add_beta_bd_sn_step(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "beta_bd_step_preserves_ceiling_zero".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), beta_reduces_bd e e' -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> Eq Nat (bvar_ceiling e') Nat.zero"
            )
            .to_string(),
            value_src: Some(beta_bd_step_preserves_ceiling_zero_proof()),
            is_axiom: false,
            description: concat!(
                "A single IOTA-FREE beta step (beta_reduces_bd, the 13 non-iota constructors of ",
                "beta_reduces) out of a bvar-free term stays bvar-free: beta_reduces_bd e e' -> ",
                "bvar_ceiling e = 0 -> bvar_ceiling e' = 0. beta_reduces_bd.rec; the beta and ",
                "zeta contraction arms rewrite instantiate body v = body via ",
                "inst_id_of_ceiling_zero (bvar-free bodies are fixed by substitution), the eleven ",
                "congruence arms (app/lam/pi/forall_ two-position, let_ty/let_val/let_body ",
                "three-position) split the zero sum (nat_add_eq_zero_left/right), forward the ",
                "changed position through the IH, and recompose (nat_add_zero_zero). Mirrors ",
                "the NoBvar half of step_clean_and_lt in the Aristotle Lean source (SnLet). ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.rec".to_string(),
                "bvar_ceiling".to_string(),
                "instantiate".to_string(),
                "inst_id_of_ceiling_zero".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "nat_add_zero_zero".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "beta_bd_step_decreases_size".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (e' : KExpr), beta_reduces_bd e e' -> ",
                "Eq Nat (bvar_ceiling e) Nat.zero -> Lt (expr_size e') (expr_size e)"
            )
            .to_string(),
            value_src: Some(beta_bd_step_decreases_size_proof()),
            is_axiom: false,
            description: concat!(
                "A single IOTA-FREE beta step (beta_reduces_bd) out of a bvar-free term strictly ",
                "decreases expr_size: beta_reduces_bd e e' -> bvar_ceiling e = 0 -> ",
                "Lt (expr_size e') (expr_size e). beta_reduces_bd.rec; the beta contraction arm ",
                "rewrites instantiate body v = body (inst_id_of_ceiling_zero) ",
                "and chains the landed subterm decreases size_lam_snd / size_app_fst via ",
                "lt_trans, the zeta contraction arm rewrites the same way and lands ",
                "size_let_thd directly (the bvar-free contractum IS the let_ body, a strict ",
                "subterm), the eleven congruence arms lift the IH through the strict add ",
                "monotonicities (lt_add_right_mono / lt_add_left_mono) and Lt.succ_lt_succ. ",
                "This is FALSE for the full beta_reduces (its iota arm rewrites via the ",
                "env-dependent iota_reduces, which need not shrink) — the honest statement is ",
                "over beta_reduces_bd only. Mirrors the size half of step_clean_and_lt in the ",
                "Aristotle Lean source (SnLet). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces_bd".to_string(),
                "beta_reduces_bd.rec".to_string(),
                "bvar_ceiling".to_string(),
                "expr_size".to_string(),
                "instantiate".to_string(),
                "inst_id_of_ceiling_zero".to_string(),
                "nat_add_eq_zero_left".to_string(),
                "nat_add_eq_zero_right".to_string(),
                "lt_add_right_mono".to_string(),
                "lt_add_left_mono".to_string(),
                "lt_trans".to_string(),
                "size_lam_snd".to_string(),
                "size_app_fst".to_string(),
                "size_let_thd".to_string(),
                "Lt".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "Eq.subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Accessibility and the goal theorems.
    fn add_beta_bd_sn_acc(&mut self) -> Result<(), SpecError> {
        // beta_bd_acc: accessibility under beta_reduces_bd — the whnf_acc
        // pattern over the iota-free relation. Inhabited exactly when every
        // beta_reduces_bd sequence from e is finite; NOT vacuous.
        self.add_inductive(
            r"inductive beta_bd_acc : KExpr → Type
| intro : forall (e : KExpr), (forall (e' : KExpr), beta_reduces_bd e e' → beta_bd_acc e') → beta_bd_acc e",
            "Accessibility of e under the IOTA-FREE single-step beta relation beta_reduces_bd: \
             inhabited iff every beta_reduces_bd reduction sequence from e is finite (Acc over \
             the flipped step relation, the whnf_acc pattern). The SN predicate of the \
             beta-only leg; says nothing about the delta/iota legs of whnf_step. Part of the \
             beta_reduces_bd SN ladder (Aristotle port).",
        )?;

        // beta_bd_acc_of_ceiling_zero: every bvar-free term is accessible.
        // Strong induction on expr_size via the landed nat_strong_rec (the
        // spec fragment has no WellFounded/brecOn): motive
        //   P n := forall x, expr_size x = n -> bvar_ceiling x = 0 -> beta_bd_acc x,
        // step: intro; each reduct y has strictly smaller size (transported to
        // Lt (expr_size y) k along the size equation) and stays bvar-free, so
        // the course-of-values IH applies at expr_size y.
        self.add_definition(SpecDefinition {
            name: "beta_bd_acc_of_ceiling_zero".to_string(),
            type_src: "forall (e : KExpr), Eq Nat (bvar_ceiling e) Nat.zero -> beta_bd_acc e"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) => ",
                    "nat_strong_rec ",
                    "(fun (n : Nat) => forall (x : KExpr), Eq Nat (expr_size x) n -> ",
                    "Eq Nat (bvar_ceiling x) Nat.zero -> beta_bd_acc x) ",
                    "(fun (k : Nat) ",
                    "(ih : forall (j : Nat), Lt j k -> forall (x : KExpr), ",
                    "Eq Nat (expr_size x) j -> Eq Nat (bvar_ceiling x) Nat.zero -> ",
                    "beta_bd_acc x) ",
                    "(x : KExpr) (hsz : Eq Nat (expr_size x) k) ",
                    "(hnb : Eq Nat (bvar_ceiling x) Nat.zero) => ",
                    "beta_bd_acc.intro x ",
                    "(fun (y : KExpr) (hstep : beta_reduces_bd x y) => ",
                    "ih (expr_size y) ",
                    "(Eq.substType Nat (fun (z : Nat) => Lt (expr_size y) z) ",
                    "(expr_size x) k hsz ",
                    "(beta_bd_step_decreases_size x y hstep hnb)) ",
                    "y (Eq.refl Nat (expr_size y)) ",
                    "(beta_bd_step_preserves_ceiling_zero x y hstep hnb))) ",
                    "(expr_size e) e (Eq.refl Nat (expr_size e))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Every bvar-free term is beta_bd_acc (accessible under the iota-free ",
                "beta_reduces_bd): strong induction on expr_size via the landed nat_strong_rec ",
                "with the size-equation-indexed motive (the spec fragment has no WellFounded/",
                "brecOn — Nat-bounded course-of-values recursion is the encoding). Each reduct ",
                "strictly shrinks (beta_bd_step_decreases_size, transported along the size ",
                "equation) and stays bvar-free (beta_bd_step_preserves_ceiling_zero). Mirrors ",
                "betaAcc_of_noBvar_bounded in the Aristotle Lean source. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "nat_strong_rec".to_string(),
                "beta_bd_acc".to_string(),
                "beta_bd_acc.intro".to_string(),
                "beta_reduces_bd".to_string(),
                "beta_bd_step_decreases_size".to_string(),
                "beta_bd_step_preserves_ceiling_zero".to_string(),
                "expr_size".to_string(),
                "bvar_ceiling".to_string(),
                "Lt".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_bd_sn_well_typed — THE GOAL: strong normalization of the
        // iota-free beta_reduces_bd for every term typable in the spec's
        // context-free Typing fragment.
        self.add_definition(SpecDefinition {
            name: "beta_bd_sn_well_typed".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), Typing e T -> beta_bd_acc e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (T : KExpr) (h : Typing e T) => ",
                    "beta_bd_acc_of_ceiling_zero e (typable_bvar_ceiling_zero e T h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Strong normalization of the IOTA-FREE single-step beta relation ",
                "beta_reduces_bd for well-typed terms: Typing e T -> beta_bd_acc e. This is the ",
                "BETA-ONLY leg of the census axiom whnf_terminates_well_typed (whnf_lemmas.rs), ",
                "which remains in place: the full axiom is over whnf_step = beta_reduces | ",
                "delta_reduces, and beta_reduces carries the env-dependent iota arm — neither ",
                "the iota nor the delta leg is discharged here. Kernel-checked port of beta_sn ",
                "in proofs/lean-aristotle/beta_sn_kexpr.lean (typable terms are bvar-free in ",
                "the context-free Typing fragment; steps then strictly shrink expr_size). ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing".to_string(),
                "beta_bd_acc".to_string(),
                "beta_bd_acc_of_ceiling_zero".to_string(),
                "typable_bvar_ceiling_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_bd_sn_has_type — the same theorem phrased through the has_type
        // reducible alias, mirroring the census axiom's statement shape
        // (`has_type e T -> terminates_whnf e` vs `has_type e T -> beta_bd_acc e`).
        self.add_definition(SpecDefinition {
            name: "beta_bd_sn_has_type".to_string(),
            type_src: "forall (e : KExpr) (T : KExpr), has_type e T -> beta_bd_acc e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (T : KExpr) (h : has_type e T) => ",
                    "beta_bd_sn_well_typed e T h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "beta_bd_sn_well_typed rephrased through the has_type reducible alias, matching ",
                "the statement shape of the census axiom whnf_terminates_well_typed (has_type ",
                "e T -> terminates_whnf e). Same honesty scope: SN of beta_reduces_bd ONLY — ",
                "the iota and delta legs of whnf_step are not covered. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "has_type".to_string(),
                "beta_bd_acc".to_string(),
                "beta_bd_sn_well_typed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `typable_ceil_zero_box`. `Typing.rec` with motive
/// `CeilZeroBox e`; sort is a closed leaf, pi/lam/app compose the unboxed
/// child equalities via `nat_add_zero_zero` (the ceiling of a binder/app node
/// definitionally reduces to the sum of the child ceilings), conv forwards
/// the IH.
fn typable_ceil_zero_box_proof() -> String {
    concat!(
        "fun (e0 : KExpr) (T0 : KExpr) (h0 : Typing e0 T0) => ",
        "Typing.rec ",
        "(fun (e : KExpr) (T : KExpr) (_ : Typing e T) => CeilZeroBox e) ",
        // sort n : bvar_ceiling (sort n) ≡ 0.
        "(fun (n : Level) => CeilZeroBox.mk (KExpr.sort n) (Eq.refl Nat Nat.zero)) ",
        // pi A B n m
        "(fun (A : KExpr) (B : KExpr) (n : Level) (m : Level) ",
        "(_hA : Typing A (KExpr.sort n)) (_hB : Typing B (KExpr.sort m)) ",
        "(ihA : CeilZeroBox A) (ihB : CeilZeroBox B) => ",
        "CeilZeroBox.mk (KExpr.pi A B) ",
        "(nat_add_zero_zero (bvar_ceiling A) (bvar_ceiling B) ",
        "(ceil_zero_unbox A ihA) (ceil_zero_unbox B ihB))) ",
        // lam A b B u
        "(fun (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) ",
        "(_hA : Typing A (KExpr.sort u)) (_hb : Typing b B) ",
        "(ihA : CeilZeroBox A) (ihb : CeilZeroBox b) => ",
        "CeilZeroBox.mk (KExpr.lam A b) ",
        "(nat_add_zero_zero (bvar_ceiling A) (bvar_ceiling b) ",
        "(ceil_zero_unbox A ihA) (ceil_zero_unbox b ihb))) ",
        // app f a A B
        "(fun (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) ",
        "(_hf : Typing f (KExpr.pi A B)) (_ha : Typing a A) ",
        "(ihf : CeilZeroBox f) (iha : CeilZeroBox a) => ",
        "CeilZeroBox.mk (KExpr.app f a) ",
        "(nat_add_zero_zero (bvar_ceiling f) (bvar_ceiling a) ",
        "(ceil_zero_unbox f ihf) (ceil_zero_unbox a iha))) ",
        // conv e A B — subject unchanged, forward the IH.
        "(fun (e : KExpr) (A : KExpr) (B : KExpr) ",
        "(_he : Typing e A) (_eq : DefEq A B) ",
        "(ihe : CeilZeroBox e) => ihe) ",
        // indices + major
        "e0 T0 h0"
    )
    .to_string()
}

/// Closed proof term for `beta_bd_step_preserves_ceiling_zero`.
/// `beta_reduces_bd.rec` with motive
/// `bvar_ceiling e = 0 -> bvar_ceiling e' = 0` (13 arms: beta, app_left,
/// app_right, lam_ty, lam_body, pi_dom, pi_cod, forall_congr_dom,
/// forall_congr_cod, zeta, let_ty, let_val, let_body).
fn beta_bd_step_preserves_ceiling_zero_proof() -> String {
    concat!(
        "fun (s : KExpr) (t : KExpr) (hst : beta_reduces_bd s t) => ",
        "beta_reduces_bd.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces_bd e e') => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> Eq Nat (bvar_ceiling e') Nat.zero) ",
        // beta A body arg : (app (lam A body) arg) ~> instantiate body arg.
        // Split the zero sum down to the body, then rewrite the instantiation
        // away (bvar-free bodies are fixed points of instantiate).
        "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app (KExpr.lam A body) arg)) Nat.zero) => ",
        "(fun (hbody : Eq Nat (bvar_ceiling body) Nat.zero) => ",
        "Eq.subst KExpr (fun (z : KExpr) => Eq Nat (bvar_ceiling z) Nat.zero) ",
        "body (instantiate body arg) ",
        "(Eq.symm KExpr (instantiate body arg) body ",
        "(inst_id_of_ceiling_zero body arg hbody)) ",
        "hbody) ",
        "(nat_add_eq_zero_right (bvar_ceiling A) (bvar_ceiling body) ",
        "(nat_add_eq_zero_left (Nat.add (bvar_ceiling A) (bvar_ceiling body)) ",
        "(bvar_ceiling arg) h))) ",
        // app_left f f' a
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_hf : beta_reduces_bd f f') ",
        "(ih : Eq Nat (bvar_ceiling f) Nat.zero -> Eq Nat (bvar_ceiling f') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling f') (bvar_ceiling a) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) h)) ",
        "(nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) h)) ",
        // app_right f a a'
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_ha : beta_reduces_bd a a') ",
        "(ih : Eq Nat (bvar_ceiling a) Nat.zero -> Eq Nat (bvar_ceiling a') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling f) (bvar_ceiling a') ",
        "(nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) h) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) h))) ",
        // lam_ty ty ty' body
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> Eq Nat (bvar_ceiling ty') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling ty') (bvar_ceiling body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) (bvar_ceiling body) h)) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) (bvar_ceiling body) h)) ",
        // lam_body ty body body'
        "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Eq Nat (bvar_ceiling body') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling ty) (bvar_ceiling body') ",
        "(nat_add_eq_zero_left (bvar_ceiling ty) (bvar_ceiling body) h) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling ty) (bvar_ceiling body) h))) ",
        // pi_dom dom dom' body
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> ",
        "Eq Nat (bvar_ceiling dom') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling dom') (bvar_ceiling body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h)) ",
        "(nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h)) ",
        // pi_cod dom body body'
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Eq Nat (bvar_ceiling body') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling dom) (bvar_ceiling body') ",
        "(nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h))) ",
        // forall_congr_dom — forall_ is the reducible pi alias; same proof.
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> ",
        "Eq Nat (bvar_ceiling dom') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling dom') (bvar_ceiling body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h)) ",
        "(nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h)) ",
        // forall_congr_cod
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Eq Nat (bvar_ceiling body') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling dom) (bvar_ceiling body') ",
        "(nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h))) ",
        // zeta ty val body — the genuine let_ head contraction: on the
        // bvar-free body the contractum IS the body (inst_id_of_ceiling_zero);
        // transport its ceiling. Triple split: bvar_ceiling (let_ ty val body)
        // = add (ceil ty) (add (ceil val) (ceil body)).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "(fun (hbody : Eq Nat (bvar_ceiling body) Nat.zero) => ",
        "Eq.subst KExpr (fun (z : KExpr) => Eq Nat (bvar_ceiling z) Nat.zero) ",
        "body (instantiate body val) ",
        "(Eq.symm KExpr (instantiate body val) body ",
        "(inst_id_of_ceiling_zero body val hbody)) ",
        "hbody) ",
        "(nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h))) ",
        // let_ty ty ty' val body — plain congruence; recompose the zero sum.
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> Eq Nat (bvar_ceiling ty') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling ty') (Nat.add (bvar_ceiling val) (bvar_ceiling body)) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)) ",
        // let_val ty val val' body
        "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
        "(_hv : beta_reduces_bd val val') ",
        "(ih : Eq Nat (bvar_ceiling val) Nat.zero -> Eq Nat (bvar_ceiling val') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling ty) (Nat.add (bvar_ceiling val') (bvar_ceiling body)) ",
        "(nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h) ",
        "(nat_add_zero_zero (bvar_ceiling val') (bvar_ceiling body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h))) ",
        "(nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)))) ",
        // let_body ty val body body' — now a PLAIN congruence (the old bundled
        // instantiate premise is gone; zeta carries the contraction).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> Eq Nat (bvar_ceiling body') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "nat_add_zero_zero (bvar_ceiling ty) (Nat.add (bvar_ceiling val) (bvar_ceiling body')) ",
        "(nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h) ",
        "(nat_add_zero_zero (bvar_ceiling val) (bvar_ceiling body') ",
        "(nat_add_eq_zero_left (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h))))) ",
        // proj ps pidx sub sub' (proj/lit rung): bvar_ceiling (proj ..) = bvar_ceiling
        // sub by defeq (proj is a transparent node), so the ceiling is carried by ih.
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : beta_reduces_bd sub sub') ",
        "(ih : Eq Nat (bvar_ceiling sub) Nat.zero -> Eq Nat (bvar_ceiling sub') Nat.zero) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.proj ps pidx sub)) Nat.zero) => ih h) ",
        // indices + major
        "s t hst"
    )
    .to_string()
}

/// Closed proof term for `beta_bd_step_decreases_size`.
/// `beta_reduces_bd.rec` with motive
/// `bvar_ceiling e = 0 -> Lt (expr_size e') (expr_size e)` (13 arms: beta,
/// app_left, app_right, lam_ty, lam_body, pi_dom, pi_cod, forall_congr_dom,
/// forall_congr_cod, zeta, let_ty, let_val, let_body).
fn beta_bd_step_decreases_size_proof() -> String {
    concat!(
        "fun (s : KExpr) (t : KExpr) (hst : beta_reduces_bd s t) => ",
        "beta_reduces_bd.rec ",
        "(fun (e : KExpr) (e' : KExpr) (_ : beta_reduces_bd e e') => ",
        "Eq Nat (bvar_ceiling e) Nat.zero -> Lt (expr_size e') (expr_size e)) ",
        // beta A body arg: size (instantiate body arg) = size body (bvar-free)
        // < size (lam A body) < size (app (lam A body) arg).
        "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app (KExpr.lam A body) arg)) Nat.zero) => ",
        "Eq.substType KExpr ",
        "(fun (z : KExpr) => Lt (expr_size z) ",
        "(expr_size (KExpr.app (KExpr.lam A body) arg))) ",
        "body (instantiate body arg) ",
        "(Eq.symm KExpr (instantiate body arg) body ",
        "(inst_id_of_ceiling_zero body arg ",
        "(nat_add_eq_zero_right (bvar_ceiling A) (bvar_ceiling body) ",
        "(nat_add_eq_zero_left (Nat.add (bvar_ceiling A) (bvar_ceiling body)) ",
        "(bvar_ceiling arg) h)))) ",
        "(lt_trans (expr_size body) (expr_size (KExpr.lam A body)) ",
        "(expr_size (KExpr.app (KExpr.lam A body) arg)) ",
        "(size_lam_snd A body) ",
        "(size_app_fst (KExpr.lam A body) arg))) ",
        // app_left f f' a: succ (add sf' sa) < succ (add sf sa).
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) ",
        "(_hf : beta_reduces_bd f f') ",
        "(ih : Eq Nat (bvar_ceiling f) Nat.zero -> Lt (expr_size f') (expr_size f)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size f') (expr_size a)) ",
        "(Nat.add (expr_size f) (expr_size a)) ",
        "(lt_add_right_mono (expr_size f') (expr_size f) (expr_size a) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling f) (bvar_ceiling a) h)))) ",
        // app_right f a a'
        "(fun (f : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_ha : beta_reduces_bd a a') ",
        "(ih : Eq Nat (bvar_ceiling a) Nat.zero -> Lt (expr_size a') (expr_size a)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.app f a)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size f) (expr_size a')) ",
        "(Nat.add (expr_size f) (expr_size a)) ",
        "(lt_add_left_mono (expr_size a') (expr_size a) (expr_size f) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling f) (bvar_ceiling a) h)))) ",
        // lam_ty ty ty' body
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> Lt (expr_size ty') (expr_size ty)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size ty') (expr_size body)) ",
        "(Nat.add (expr_size ty) (expr_size body)) ",
        "(lt_add_right_mono (expr_size ty') (expr_size ty) (expr_size body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) (bvar_ceiling body) h)))) ",
        // lam_body ty body body'
        "(fun (ty : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Lt (expr_size body') (expr_size body)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.lam ty body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size ty) (expr_size body')) ",
        "(Nat.add (expr_size ty) (expr_size body)) ",
        "(lt_add_left_mono (expr_size body') (expr_size body) (expr_size ty) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling ty) (bvar_ceiling body) h)))) ",
        // pi_dom dom dom' body
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> ",
        "Lt (expr_size dom') (expr_size dom)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size dom') (expr_size body)) ",
        "(Nat.add (expr_size dom) (expr_size body)) ",
        "(lt_add_right_mono (expr_size dom') (expr_size dom) (expr_size body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h)))) ",
        // pi_cod dom body body'
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Lt (expr_size body') (expr_size body)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.pi dom body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size dom) (expr_size body')) ",
        "(Nat.add (expr_size dom) (expr_size body)) ",
        "(lt_add_left_mono (expr_size body') (expr_size body) (expr_size dom) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h)))) ",
        // forall_congr_dom — forall_ is the reducible pi alias; same proof.
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) ",
        "(_hd : beta_reduces_bd dom dom') ",
        "(ih : Eq Nat (bvar_ceiling dom) Nat.zero -> ",
        "Lt (expr_size dom') (expr_size dom)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size dom') (expr_size body)) ",
        "(Nat.add (expr_size dom) (expr_size body)) ",
        "(lt_add_right_mono (expr_size dom') (expr_size dom) (expr_size body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling dom) (bvar_ceiling body) h)))) ",
        // forall_congr_cod
        "(fun (dom : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> ",
        "Lt (expr_size body') (expr_size body)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.forall_ dom body)) Nat.zero) => ",
        "Lt.succ_lt_succ (Nat.add (expr_size dom) (expr_size body')) ",
        "(Nat.add (expr_size dom) (expr_size body)) ",
        "(lt_add_left_mono (expr_size body') (expr_size body) (expr_size dom) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling dom) (bvar_ceiling body) h)))) ",
        // zeta ty val body: size (instantiate body val) = size body (bvar-free)
        // < size (let_ ty val body), directly via size_let_thd (the contractum
        // is the genuine third component of the let_ node).
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "Eq.substType KExpr ",
        "(fun (z : KExpr) => Lt (expr_size z) (expr_size (KExpr.let_ ty val body))) ",
        "body (instantiate body val) ",
        "(Eq.symm KExpr (instantiate body val) body ",
        "(inst_id_of_ceiling_zero body val ",
        "(nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)))) ",
        "(size_let_thd ty val body)) ",
        // let_ty ty ty' val body: succ (add sty' (add sval sbody)) <
        // succ (add sty (add sval sbody)).
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (body : KExpr) ",
        "(_hty : beta_reduces_bd ty ty') ",
        "(ih : Eq Nat (bvar_ceiling ty) Nat.zero -> Lt (expr_size ty') (expr_size ty)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "Lt.succ_lt_succ ",
        "(Nat.add (expr_size ty') (Nat.add (expr_size val) (expr_size body))) ",
        "(Nat.add (expr_size ty) (Nat.add (expr_size val) (expr_size body))) ",
        "(lt_add_right_mono (expr_size ty') (expr_size ty) ",
        "(Nat.add (expr_size val) (expr_size body)) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)))) ",
        // let_val ty val val' body
        "(fun (ty : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) ",
        "(_hv : beta_reduces_bd val val') ",
        "(ih : Eq Nat (bvar_ceiling val) Nat.zero -> Lt (expr_size val') (expr_size val)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "Lt.succ_lt_succ ",
        "(Nat.add (expr_size ty) (Nat.add (expr_size val') (expr_size body))) ",
        "(Nat.add (expr_size ty) (Nat.add (expr_size val) (expr_size body))) ",
        "(lt_add_left_mono ",
        "(Nat.add (expr_size val') (expr_size body)) ",
        "(Nat.add (expr_size val) (expr_size body)) ",
        "(expr_size ty) ",
        "(lt_add_right_mono (expr_size val') (expr_size val) (expr_size body) ",
        "(ih (nat_add_eq_zero_left (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)))))) ",
        // let_body ty val body body'
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hb : beta_reduces_bd body body') ",
        "(ih : Eq Nat (bvar_ceiling body) Nat.zero -> Lt (expr_size body') (expr_size body)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.let_ ty val body)) Nat.zero) => ",
        "Lt.succ_lt_succ ",
        "(Nat.add (expr_size ty) (Nat.add (expr_size val) (expr_size body'))) ",
        "(Nat.add (expr_size ty) (Nat.add (expr_size val) (expr_size body))) ",
        "(lt_add_left_mono ",
        "(Nat.add (expr_size val) (expr_size body')) ",
        "(Nat.add (expr_size val) (expr_size body)) ",
        "(expr_size ty) ",
        "(lt_add_left_mono (expr_size body') (expr_size body) (expr_size val) ",
        "(ih (nat_add_eq_zero_right (bvar_ceiling val) (bvar_ceiling body) ",
        "(nat_add_eq_zero_right (bvar_ceiling ty) ",
        "(Nat.add (bvar_ceiling val) (bvar_ceiling body)) h)))))) ",
        // proj ps pidx sub sub' (proj/lit rung): expr_size (proj ..) = succ (expr_size
        // sub) by defeq, so the strict decrease lifts through succ monotonicity.
        "(fun (ps : Name) (pidx : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : beta_reduces_bd sub sub') ",
        "(ih : Eq Nat (bvar_ceiling sub) Nat.zero -> Lt (expr_size sub') (expr_size sub)) ",
        "(h : Eq Nat (bvar_ceiling (KExpr.proj ps pidx sub)) Nat.zero) => ",
        "Lt.succ_lt_succ (expr_size sub') (expr_size sub) (ih h)) ",
        // indices + major
        "s t hst"
    )
    .to_string()
}

#[cfg(test)]
#[path = "beta_bd_sn_tests.rs"]
mod beta_bd_sn_tests;

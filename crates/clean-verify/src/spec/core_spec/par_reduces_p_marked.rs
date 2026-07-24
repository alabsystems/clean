// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F++ (#2859 computational-iota/delta track): the MARKED / fuel-counted
//! parallel reduction `par_reduces_pL` — the Tait–Martin-Löf *labeled-development*
//! technique built specifically to crack the confirmed-immovable double-iota wall of
//! the unlabeled `cd_triangle` (design §13-§15).
//!
//! WHY. The unlabeled `cd_triangle` iota arm is immovable: its kbeta-sub /
//! kiota-sub double-iota fires have NO decreasing structural measure (iota reducts
//! GROW), the symmetric join is provably circular, and iota-commutation is blocked by
//! redex-creation-through-substitution. The standard CIC/lambda fix is *labeling*: mark
//! a finite set of redexes; reduction contracts ONLY marked redexes; redexes CREATED by
//! contraction are UNMARKED, so the marked-development is BOUNDED → a measure EXISTS →
//! the diamond closes → erase labels → unlabeled confluence.
//!
//! REPRESENTATION (Option (i)+(ii) fused, kept LIGHT — NO parallel labeled-KExpr type).
//! The marking is realized as a `Nat` FUEL index on the relation:
//!
//!   `par_reduces_pL : RecEnv → Nat → KExpr → KExpr → Type`
//!
//! where the fuel `n` is exactly the number of CONTRACTIONS (beta + iota fires) in the
//! derivation. The structural congruence constructors thread the fuel ADDITIVELY
//! (`Nat.add` of the sub-fuels); each contraction constructor adds `Nat.succ`. Thus:
//!   * `n` is a genuine, kernel-visible decreasing measure on marked reduction — the
//!     thing the unlabeled `par_reduces_p` provably lacks;
//!   * the redexes a contraction CREATES are not themselves contracted in this same
//!     derivation, so they do not inflate `n` (the bounded-development property);
//!   * erasure `par_reduces_pL env n e e' → par_reduces_p env e e'` drops the fuel —
//!     every marked step is an unlabeled step, and every unlabeled step is a
//!     fully-marked step, so the marked diamond lifts to the unlabeled one.
//!
//! This module is ADDITIVE — it does NOT touch `par_reduces_p`, `par_reduces_c`, `cd`,
//! or any landed lemma. See `designs/2026-06-14-computational-iota-delta-track.md` §16.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_p_marked(&mut self) -> Result<(), SpecError> {
        // par_reduces_pL env n e e' — the MARKED (fuel-counted) parallel reduction.
        // Identical to par_reduces_p (INCLUDING the trailing let_cong congruence ctor)
        // except a Nat index `n` counts the contractions (beta + zeta + iota fires). The
        // congruence ctors (app/lam/pi/forall_/let_cong) sum the sub-fuels via Nat.add;
        // refl is fuel 0; the contraction ctors (beta/let_ ZETA/iota_p) add Nat.succ. The
        // fuel is the decreasing measure the unlabeled relation lacks.
        self.add_inductive(
            r"inductive par_reduces_pL (env : RecEnv) : Nat → KExpr → KExpr → Type
| refl : forall (e : KExpr), par_reduces_pL env Nat.zero e e
| beta : forall (nA : Nat) (nb : Nat) (na : Nat) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr), par_reduces_pL env nA A A' → par_reduces_pL env nb body body' → par_reduces_pL env na arg arg' → par_reduces_pL env (Nat.succ (Nat.add (Nat.add nA nb) na)) (KExpr.app (KExpr.lam A body) arg) (instantiate body' arg')
| app : forall (nf : Nat) (na : Nat) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), par_reduces_pL env nf f f' → par_reduces_pL env na a a' → par_reduces_pL env (Nat.add nf na) (KExpr.app f a) (KExpr.app f' a')
| lam : forall (nt : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pL env nt ty ty' → par_reduces_pL env nb body body' → par_reduces_pL env (Nat.add nt nb) (KExpr.lam ty body) (KExpr.lam ty' body')
| pi : forall (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pL env nt dom dom' → par_reduces_pL env nb body body' → par_reduces_pL env (Nat.add nt nb) (KExpr.pi dom body) (KExpr.pi dom' body')
| forall_ : forall (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pL env nt dom dom' → par_reduces_pL env nb body body' → par_reduces_pL env (Nat.add nt nb) (KExpr.forall_ dom body) (KExpr.forall_ dom' body')
| let_ : forall (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pL env nt ty ty' → par_reduces_pL env nv val val' → par_reduces_pL env nb body body' → par_reduces_pL env (Nat.succ (Nat.add (Nat.add nt nv) nb)) (KExpr.let_ ty val body) (instantiate body' val')
| iota_p : forall (ne : Nat) (e : KExpr) (e2 : KExpr) (r : KExpr), par_reduces_pL env ne e e2 → iota_step env e2 r → par_reduces_pL env (Nat.succ ne) e r
| let_cong : forall (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), par_reduces_pL env nt ty ty' → par_reduces_pL env nv val val' → par_reduces_pL env nb body body' → par_reduces_pL env (Nat.add (Nat.add nt nv) nb) (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')",
            "par_reduces_pL env n e e' — the MARKED (Tait–Martin-Löf) parallel reduction: par_reduces_p with a \
             Nat FUEL index n counting the contractions (beta + zeta + iota fires) of the derivation. Congruence ctors \
             (app/lam/pi/forall_/let_cong) sum the sub-fuels (Nat.add); refl is fuel 0; contraction ctors \
             (beta/let_ ZETA/iota_p) add Nat.succ. let_ is the genuine ZETA contraction (target instantiate body' val'), \
             let_cong is the trailing let CONGRUENCE (target KExpr.let_ ty' val' body', additive fuel — no contraction). \
             The fuel is the decreasing measure the unlabeled par_reduces_p provably lacks — redexes \
             CREATED by a contraction are not contracted in this same derivation, so the marked development is \
             bounded by n. Erases to par_reduces_p by dropping the fuel. Additive; the crack of the double-iota \
             wall. Part of #2859 (Increment F++, marked development).",
        )?;

        self.add_par_reduces_p_marked_erase()?;
        self.add_par_reduces_p_marked_refl0()?;
        self.add_par_reduces_p_marked_measure()?;
        self.add_par_reduces_p_marked_triangle_scaffold()?;
        self.add_par_reduces_p_marked_reduct_cong()?;
        self.add_par_reduces_p_marked_triangle_star()?;

        Ok(())
    }

    /// ERASURE (the labels-drop direction): every marked step is an unlabeled
    /// `par_reduces_p` step. `par_reduces_pL.rec` maps each constructor to the matching
    /// `par_reduces_p` constructor, discarding the fuel index. The motive ignores the
    /// fuel (`fun (_n : Nat) (a b : KExpr) (_ : par_reduces_pL env _n a b) =>
    /// par_reduces_p env a b`). This is one of the two erasure halves that lift the
    /// marked diamond to the unlabeled `par_strips_p` (L3).
    fn add_par_reduces_p_marked_erase(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_erase".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : Nat) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pL env n e e' -> par_reduces_p env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_p_marked_erase_proof()),
            is_axiom: false,
            description: concat!(
                "Erasure par_reduces_pL ⊆ par_reduces_p: every MARKED par-step is an unlabeled par-step ",
                "(drop the fuel). par_reduces_pL.rec mapping refl/beta/app/lam/pi/forall_/let_/iota_p/let_cong to the ",
                "matching par_reduces_p ctor via the recursor IHs; the motive discards the Nat fuel. The ",
                "labels-drop half of the marked→unlabeled diamond lift (L3). DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pL".to_string(),
                "par_reduces_pL.rec".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_cong".to_string(),
                "iota_step".to_string(),
                "Nat".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// FULL-MARK (the labels-add direction, refl seed): the reflexive marked step has
    /// fuel 0. This is the trivial base of the "every unlabeled step is reachable as a
    /// fully-marked step" direction; the genuine lift (every `par_reduces_p` step admits
    /// SOME marked witness) follows by `par_reduces_p.rec`, landed separately once the
    /// marked congruence smart-constructors are banked.
    fn add_par_reduces_p_marked_refl0(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_refl0".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr), ",
                "par_reduces_pL env Nat.zero e e"
            )
            .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (e : KExpr) => par_reduces_pL.refl env e".to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The reflexive marked step has fuel 0 (par_reduces_pL.refl). Base of the labels-add direction ",
                "(every term marked-reduces to itself contracting zero redexes). DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pL".to_string(),
                "par_reduces_pL.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// TARGET 2 — the MEASURE on marked reduction (the key new capability the unlabeled
    /// route provably lacks). The fuel index is the decreasing measure; here we bank the
    /// per-constructor fuel-decrease facts and the well-founded recursion scaffold the
    /// marked triangle/diamond strong-induct with.
    ///
    /// The marked complete development's TARGET is the existing structural `cd env e`
    /// (marking restricts WHICH redexes a derivation fires, not the development target —
    /// `cd` already contracts every present redex). What marking adds is the BOUND: a
    /// marked derivation of fuel `n` contracts exactly `n` redexes, and every
    /// sub-derivation a constructor exposes has strictly smaller fuel. The kiota-sub
    /// recursion the unlabeled triangle could not justify (`e2` may be LARGER than the
    /// source) recurses on the iota_p premise, whose fuel is strictly smaller —
    /// `lt_succ_self` — making the recursion well-founded under `nat_strong_rec`.
    fn add_par_reduces_p_marked_measure(&mut self) -> Result<(), SpecError> {
        // par_reduces_pL_iota_premise_lt — THE WALL-CASE decrease. The iota_p
        // constructor produces fuel (succ ne) from a premise of fuel ne; ne < succ ne.
        // This is the decreasing measure the unlabeled kiota arm provably lacked (where
        // the recursion target e2 could be larger than the source with NO measure). In
        // the marked relation the recursion is on the fuel, which strictly drops.
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_iota_premise_lt".to_string(),
            type_src: "forall (ne : Nat), Lt ne (Nat.succ ne)".to_string(),
            value_src: Some("fun (ne : Nat) => lt_succ_self ne".to_string()),
            is_axiom: false,
            description: concat!(
                "THE WALL-CASE measure (#2859 Increment F++): the iota_p constructor builds fuel (succ ne) from ",
                "a premise of fuel ne, and ne < succ ne (lt_succ_self). This is the strictly-decreasing measure ",
                "the unlabeled cd_triangle kiota arm provably LACKED — there the nested-iota recursion target e2 ",
                "could be larger than the source with no structural measure; in the marked relation the recursion ",
                "is on the fuel, which always drops at a contraction. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development measure)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "lt_succ_self".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_pL_beta_premise_lt — the beta/let contraction's premises drop. The
        // beta ctor builds fuel (succ (add (add nA nb) na)); each premise (nA, nb, na)
        // is < that successor. Stated for the arg premise na (the load-bearing one for
        // the kbeta-sub redex-creation-through-substitution case): na < succ(...).
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_beta_arg_premise_lt".to_string(),
            type_src: concat!(
                "forall (nA : Nat) (nb : Nat) (na : Nat), ",
                "Lt na (Nat.succ (Nat.add (Nat.add nA nb) na))"
            )
            .to_string(),
            value_src: Some(
                "fun (nA : Nat) (nb : Nat) (na : Nat) => lt_add_succ_right (Nat.add nA nb) na"
                    .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The marked beta/let contraction's arg-premise fuel drops: na < succ (add (add nA nb) na) ",
                "(lt_add_succ_right at a = add nA nb, b = na). The decreasing measure for the kbeta-sub case ",
                "(redex created AFTER a beta substitution): the substituted argument's marked derivation has ",
                "strictly smaller fuel than the beta contraction. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development measure)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.add".to_string(),
                "lt_add_succ_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_pL_app_fst_premise_le / _snd — the congruence (app) premises do
        // NOT increase the fuel: nf <= add nf na and na <= add nf na. (Congruence is not
        // a contraction, so the measure is preserved-or-split, never grown.) Used to
        // bound the structural-arm recursions of the marked triangle. We give the strict
        // forms guarded by the OUTER succ that every well-founded recursion threads.
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_app_fst_premise_lt_succ".to_string(),
            type_src: concat!(
                "forall (nf : Nat) (na : Nat), ",
                "Lt nf (Nat.succ (Nat.add nf na))"
            )
            .to_string(),
            value_src: Some(
                "fun (nf : Nat) (na : Nat) => lt_add_succ_left nf na".to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The marked app-congruence's head-premise fuel is bounded by the successor of the sum: ",
                "nf < succ (add nf na) (lt_add_succ_left). Bounds the head structural-arm recursion of the ",
                "marked triangle under a threading successor. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development measure)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.add".to_string(),
                "lt_add_succ_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_app_snd_premise_lt_succ".to_string(),
            type_src: concat!(
                "forall (nf : Nat) (na : Nat), ",
                "Lt na (Nat.succ (Nat.add nf na))"
            )
            .to_string(),
            value_src: Some(
                "fun (nf : Nat) (na : Nat) => lt_add_succ_right nf na".to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The marked app-congruence's arg-premise fuel is bounded by the successor of the sum: ",
                "na < succ (add nf na) (lt_add_succ_right). Bounds the arg structural-arm recursion of the ",
                "marked triangle under a threading successor. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development measure)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.add".to_string(),
                "lt_add_succ_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_pL_fuel_rec — THE WELL-FOUNDED RECURSION SCAFFOLD on marked fuel.
        // Specializes nat_strong_rec to a motive Q : Nat -> Type indexed by the marked
        // fuel: to prove Q n for all fuels n, it suffices to prove Q k assuming Q j for
        // every j < k. The marked triangle/diamond recurse with THIS, discharging the
        // kiota-sub / kbeta-sub redex-creation cases by the fuel-decrease facts above —
        // the recursion the unlabeled route could not justify. This is the marked
        // development's TERMINATION certificate: the fuel is a well-founded measure.
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_fuel_rec".to_string(),
            type_src: concat!(
                "forall (Q : Nat -> Type), ",
                "(forall (k : Nat), (forall (j : Nat), Lt j k -> Q j) -> Q k) -> ",
                "forall (n : Nat), Q n"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (Q : Nat -> Type) ",
                    "(step : forall (k : Nat), (forall (j : Nat), Lt j k -> Q j) -> Q k) ",
                    "(n : Nat) => nat_strong_rec Q step n"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "THE TERMINATION certificate for marked reduction (#2859 Increment F++): well-founded recursion ",
                "on the marked FUEL. Specializes nat_strong_rec to a fuel-indexed motive Q : Nat -> Type — prove ",
                "Q n for every fuel n given Q at every strictly-smaller fuel. The marked triangle and diamond ",
                "recurse with this, discharging the kiota-sub / kbeta-sub redex-creation cases (which the ",
                "unlabeled cd_triangle had NO measure for) by the per-constructor fuel-decrease facts ",
                "(par_reduces_pL_iota_premise_lt etc.). The fuel is a genuine decreasing measure; this is the ",
                "capability the unlabeled par_reduces_p provably lacks. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development measure)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "nat_strong_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// TARGET 3 (#2859 Increment F++) — the MARKED TRIANGLE scaffold, the crux. Proves
    /// `e ⇒L_n e' → e' ⇒_p cd e` by STRUCTURAL recursion on the marked derivation
    /// (`par_reduces_pL.rec`).
    ///
    /// THE CRACK. In the UNLABELED route the iota arm fires on a SEPARATELY-built
    /// derivation `app f a ⇒_p e2` (recovered by `par_reduces_p_app_inv`), so the
    /// nested-iota (kiota-sub) recursion had NO structural sub-derivation and NO
    /// decreasing measure — the immovable wall. The MARKED relation's `iota_p`
    /// constructor carries `e ⇒L_ne e2` as a POSITIVE RECURSIVE PREMISE, so
    /// `par_reduces_pL.rec` hands the iota arm its IH directly: `e2 ⇒_p cd e` (the
    /// development of `e2`). The fuel is the SEMANTIC well-foundedness certificate (the
    /// premise fuel `ne < succ ne`, `par_reduces_pL_iota_premise_lt`) that justifies the
    /// inductive — but the recursor IS that well-founded recursion, so the iota arm gets
    /// its IH for free, exactly the thing the unlabeled `cd_triangle` provably lacked.
    ///
    /// All EIGHT non-iota arms close with LANDED development bricks (refl ⟹ cd_refl;
    /// app ⟹ par_reduces_p_app_dev with the rec-IHs f'⇒_p cd f, a'⇒_p cd a + the erased
    /// source steps; beta ⟹ par_reduces_p_beta_dev; lam/pi/forall_ ⟹
    /// par_reduces_p.{lam,pi,forall_} + cd_{lam,pi}; let_ ZETA ⟹ par_subst_p + cd_let;
    /// let_cong ⟹ par_reduces_p.let_ (zeta-fire) + cd_let). The IOTA arm — the wall — is isolated as the single
    /// clean hypothesis `iota_join` (`e2 ⇒_p cd e0 → iota_step e2 r → r ⇒_p cd e0`), FED
    /// the development `e2 ⇒_p cd e0` straight from the recursor's structural IH on the
    /// `iota_p` premise. Banking this reduces the entire remaining wall to discharging
    /// `iota_join` — the genuinely-bounded redex-creation join the measure now permits.
    fn add_par_reduces_p_marked_triangle_scaffold(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_triangle_scaffold".to_string(),
            type_src: concat!(
                "forall (env : RecEnv), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                // iota_join: the isolated wall — the iota arm's exact semantic content.
                "(forall (e0 : KExpr) (e2 : KExpr) (r : KExpr), ",
                "par_reduces_p env e2 (cd env e0) -> iota_step env e2 r -> ",
                "par_reduces_p env r (cd env e0)) -> ",
                "forall (n : Nat) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pL env n e e' -> par_reduces_p env e' (cd env e)"
            )
            .to_string(),
            value_src: Some(par_reduces_p_marked_triangle_scaffold_proof()),
            is_axiom: false,
            description: concat!(
                "THE MARKED TRIANGLE scaffold (#2859 Increment F++, the crux). Proves e ⇒L_n e' → e' ⇒_p cd e by ",
                "STRUCTURAL recursion on the marked derivation (par_reduces_pL.rec). THE CRACK: the marked iota_p ",
                "constructor carries e ⇒L_ne e2 as a positive recursive premise, so the recursor hands the iota arm ",
                "its IH e2 ⇒_p cd e directly — the development the unlabeled cd_triangle could not obtain (there the ",
                "iota fired on a separately-built app_inv derivation with no structural sub-derivation / measure). ",
                "The fuel (par_reduces_pL_iota_premise_lt: ne < succ ne) is the semantic well-foundedness ",
                "certificate that the recursor embodies. Eight non-iota arms close with landed bricks (cd_refl; ",
                "par_reduces_p_app_dev; par_reduces_p_beta_dev; par_reduces_p.{lam,pi,forall_}+cd_{lam,pi}; let_ ZETA ",
                "via par_subst_p+cd_let; let_cong via par_reduces_p.let_ zeta-fire+cd_let). The IOTA arm — the wall — is the single isolated hypothesis iota_join, FED the ",
                "development e2 ⇒_p cd e0 from the recursor's structural IH. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F++, marked development triangle)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pL".to_string(),
                "par_reduces_pL.rec".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.forall_".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_pL_erase".to_string(),
                "par_subst_p".to_string(),
                "cd_refl".to_string(),
                "cd_lam".to_string(),
                "cd_pi".to_string(),
                "cd_let".to_string(),
                "par_reduces_p_app_dev".to_string(),
                "par_reduces_p_beta_dev".to_string(),
                "cd".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "Nat.zero".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// THE load-bearing marked-fuel keystone (#2859 Increment F++, design §16): the
    /// MARKED SYMMETRIC reduct congruence `par_reduces_pL_reduct_cong`. This is the
    /// brick design §16 identified as the genuine fix for the kiota wall — it
    /// recurses on the marked FUEL (the decreasing measure the unlabeled
    /// `par_reduces_p` provably lacks), closing the double-iota case the unlabeled
    /// `par_reduces_p_iota_redex_cong` could only attack circularly.
    ///
    /// Statement (STAR-valued — see design §10/§14: an ATOMIC-free symmetric reduct
    /// congruence is intrinsically multi-step in the nested-iota case, so the join
    /// lands in `par_reduces_p_star`, NOT single-step):
    /// ```text
    /// par_reduces_pL env n e m -> iota_step env e r -> iota_step env m rm
    ///   -> par_reduces_p_star env r rm
    /// ```
    /// "If `e` MARKED-reduces to `m` (fuel `n`), and BOTH endpoints are iota redexes
    /// (`e -> r`, `m -> rm`), then the reducts join in `par_reduces_p_star`."
    ///
    /// Proof: `par_reduces_pL_fuel_rec` on `n` (the OUTER well-founded recursion on
    /// fuel) with the universalized motive `Q k := forall e m r rm,
    /// par_reduces_pL env k e m -> iota_step e r -> iota_step m rm -> r =>*_p rm`,
    /// then an INNER `par_reduces_pL.rec` (case-split the first leg) with a
    /// fuel-equation convoy motive `M k0 a b _ := Eq Nat k0 k -> forall r0 rm0,
    /// iota_step a r0 -> iota_step b rm0 -> r0 =>*_p rm0`:
    ///   * **refl** (`m = e`): both fires on `e`, so `r0 = rm0` by
    ///     `iota_step_deterministic`; `r0 =>*_p r0` (refl) transported.
    ///   * **iota_p** (`e =>L_ne e2`, `iota_step e2 rfire`, target `= rfire`): THE
    ///     CRUX. The structural IH is useless (its `Eq Nat ne k` precondition is
    ///     false), so recurse via the OUTER fuel IH at `ne` — `Lt ne k` from
    ///     `lt_succ_self ne` rewritten by the convoy `Eq Nat (succ ne) k`. The outer
    ///     IH on the sub-leg `e =>L_ne e2` with the fires `(r0 on e, rfire on e2)`
    ///     yields `r0 =>*_p rfire`; then `rfire =>_p rm0` via
    ///     `par_reduces_p_iota_redex_to_reduct` (rfire fires to rm0), and
    ///     `par_reduces_p_star_trans` joins `r0 =>*_p rfire =>*_p rm0`. This is the
    ///     nested-double-iota join the unlabeled route had NO measure for — the fuel
    ///     supplies it.
    ///   * **app** (`a = app f g`, `b = app f' g'`): the STRUCTURAL-args reduct
    ///     congruence (both endpoints are app-headed redexes). Isolated to the single
    ///     hypothesis `happ` (the app reduct congruence over `f =>_p f'`, `g =>_p g'`),
    ///     fed the erased sub-legs — the residual structural assembly, NOT the wall.
    ///   * **beta/lam/pi/forall_/let_**: the source is binder/lam-app-headed, so
    ///     `kexpr_const_name (kapp_fn a) = none` contradicts the iota fire — discharged
    ///     via `iota_step_head_none_absurd_type`.
    ///
    /// Banking this proves the marked fuel genuinely closes the kiota double-iota wall
    /// (the iota_p arm), reducing the entire symmetric reduct congruence to the
    /// structural app hypothesis `happ`. NO fabricated term; the wall-case is a real
    /// fuel-recursive proof.
    fn add_par_reduces_p_marked_reduct_cong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_reduct_cong".to_string(),
            type_src: concat!(
                "forall (env : RecEnv), ",
                // disjoint: the faithful ctor/recursor-disjointness interface (NOT an
                // axiom — discharged at end-of-track with the real kernel-env witness,
                // exactly like RecEnvClosed/RecEnvLiftClosed). The minimal app arm needs
                // recmeta_for(ctor) = none.
                "RecEnvCtorNoRecMeta env -> ",
                // happ_over: the OVER-APPLICATION residual (f itself an iota redex). The
                // directed fuel IH cannot supply the confluence sub-diamond this needs;
                // it stays an explicit hypothesis (the single remaining residual — the
                // MINIMAL/boundary app case is now discharged INTERNALLY via the landed
                // par_reduces_p_app_reduct_cong_minimal).
                "(forall (f : KExpr) (f' : KExpr) (g : KExpr) (g' : KExpr) (f1 : KExpr) (r0 : KExpr) (rm0 : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> ",
                "par_reduces_p env f f' -> par_reduces_p env g g' -> ",
                "iota_step env (KExpr.app f g) r0 -> iota_step env (KExpr.app f' g') rm0 -> ",
                "par_reduces_p_star env r0 rm0) -> ",
                "forall (n : Nat) (e : KExpr) (m : KExpr) (r : KExpr) (rm : KExpr), ",
                "par_reduces_pL env n e m -> iota_step env e r -> iota_step env m rm -> ",
                "par_reduces_p_star env r rm"
            )
            .to_string(),
            value_src: Some(par_reduces_p_marked_reduct_cong_proof()),
            is_axiom: false,
            description: concat!(
                "THE marked-fuel keystone (#2859 Increment F++, design §16): the MARKED SYMMETRIC reduct ",
                "congruence par_reduces_pL_reduct_cong. Given a MARKED derivation e ⇒L_n m and both endpoints ",
                "iota redexes (e -> r, m -> rm), the reducts join in par_reduces_p_star. Proved by ",
                "par_reduces_pL_fuel_rec on the fuel (outer well-founded recursion) + an inner par_reduces_pL.rec ",
                "(fuel-equation convoy motive). THE CRUX is the iota_p arm (the double-iota wall §14/§16): the ",
                "structural IH is useless (false fuel precondition), so it recurses via the OUTER fuel IH at the ",
                "premise fuel ne < succ ne (par_reduces_pL_iota_premise_lt / lt_succ_self) — the decreasing measure ",
                "the unlabeled par_reduces_p provably lacks — yielding r0 ⇒*_p rfire, then ",
                "par_reduces_p_iota_redex_to_reduct + par_reduces_p_star_trans join through rfire. refl closes by ",
                "iota_step_deterministic; binder/beta/let arms discharge via iota_step_head_none_absurd_type (a ",
                "binder-headed term is not a redex). The app arm CASE-SPLITS on iota_reduct env f: the none arm ",
                "(f not a redex — the MINIMAL/boundary case) is now discharged INTERNALLY by the landed ",
                "par_reduces_p_app_reduct_cong_minimal (threading the faithful disjointness interface ",
                "RecEnvCtorNoRecMeta, NOT an axiom — discharged at end-of-track like RecEnvClosed); the some arm ",
                "(f itself a redex — OVER-APPLICATION) is the single remaining residual happ_over (the directed ",
                "fuel IH cannot supply the confluence sub-diamond it needs). DerivedProved, zero axiom_deps. The ",
                "fuel recursion CLOSES the kiota double-iota join the unlabeled cd_triangle could only attack ",
                "circularly; the minimal app-args reduct congruence is now unconditional-modulo-{RecEnvCtorNoRecMeta}."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pL".to_string(),
                "par_reduces_pL.rec".to_string(),
                "par_reduces_pL_fuel_rec".to_string(),
                "par_reduces_pL_erase".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "par_reduces_p_iota_redex_to_reduct".to_string(),
                "par_reduces_p_app_reduct_cong_minimal".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "iota_reduct".to_string(),
                "OptionType.rec".to_string(),
                "iota_step".to_string(),
                "iota_step_deterministic".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "lt_succ_self".to_string(),
                "Lt".to_string(),
                "Nat".to_string(),
                "Nat.succ".to_string(),
                "Nat.add".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// STEP 2 (#2859 Increment F++, design §17) — the STAR-VALUED MARKED TRIANGLE
    /// `par_reduces_pL_triangle_star`: `e ⇒L_n e' → e' ⇒*_p cd e`. The star-valued
    /// sibling of the single-step `par_reduces_pL_triangle_scaffold`, lifted to land in
    /// `par_reduces_p_star` (the level §10/§14 established the symmetric/iota join is
    /// intrinsically multi-step at). This is the development relation the erasure bridge
    /// to `par_strips_p` (Step 3) consumes.
    ///
    /// MOTIVE `M n a b _ := par_reduces_p_star env b (cd env a)`. The EIGHT non-iota arms
    /// close UNCONDITIONALLY by lifting the landed single-step development bricks to the
    /// star motive via the new `par_reduces_p_star_{app,lam,pi,forall}` / `par_subst_p_star`
    /// congruences (built in par_reduces_p.rs):
    ///   * refl ⟹ `par_subsumes_par_p_star (cd_refl env x)`.
    ///   * app ⟹ `par_reduces_p_star_app` on the rec star-IHs (f' ⇒* cd f, a' ⇒* cd a)
    ///     reaching `app f' a' ⇒* app (cd f)(cd a)`, then ONE landed `par_reduces_p_app_dev`
    ///     development step `app (cd f)(cd a) ⇒_p cd (app f a)` (its single-step IHs are
    ///     `cd_refl` / `par_reduces_p.refl`), subsumed + star-trans'd.
    ///   * lam/pi/forall_ ⟹ `par_reduces_p_star_{lam,pi,forall}` on the rec star-IHs
    ///     (cd (HEAD t b) ≡ HEAD (cd t)(cd b) by defeq).
    ///   * beta/let_ ZETA ⟹ `par_subst_p_star` on the rec star-IHs (body' ⇒* cd body,
    ///     arg'/val' ⇒* cd arg/val) reaching `instantiate body' arg' ⇒* instantiate
    ///     (cd body)(cd arg)`, transported to `cd (app (lam A body) arg)` by `cd_app_lam`
    ///     (resp. `cd (let_ ty val body)` by the genuine-let `cd_let`).
    ///   * let_cong ⟹ one zeta-fire (`par_reduces_p.let_` with reflexive premises,
    ///     subsumed) + `par_subst_p_star`, star-trans'd, transported by `cd_let`.
    ///
    /// THE IOTA ARM (the residual). Goal `rfire ⇒*_p cd x` from `ihe : e2 ⇒*_p cd x`
    /// (the star development of e2) and `hi : iota_step e2 rfire` (one iota fire of e2).
    /// This is the fire-vs-development local-confluence join. As of this STEP it is
    /// isolated as the single faithful STAR hypothesis
    /// `iota_join_star : e2 ⇒*_p cd e0 → iota_step e2 r → r ⇒*_p cd e0` — the honest
    /// star analogue of the scaffold's single-step `iota_join`. It is FED the recursor's
    /// structural star-IH `ihe` and the fire `hi` (the development the unlabeled route
    /// could not obtain, supplied here by the marked recursor).
    ///
    /// HONEST SCOPE (design §16/§17, two independent cross-checked analyses): the keystone
    /// `par_reduces_pL_reduct_cong` joins TWO iota fires out of the two endpoints of a
    /// MARKED derivation, landing in star. It does NOT directly close THIS arm: the arm
    /// has the marked derivation `he : x ⇒L_ne e2` but only ONE fire (`hi` on e2), and no
    /// fire on the source x; and `ihe` is a plain star development, NOT the keystone's
    /// marked both-endpoints-redex currency. Consuming the keystone here requires the
    /// motive itself to deliver a MARKED development of e2 (a confluence/marked-valued
    /// triangle motive), which is a larger restructuring than this star lift — left as the
    /// precise next residual. NO fabricated term: `iota_join_star` is an honest isolated
    /// hypothesis exactly like the landed scaffold's `iota_join`, now at the star level the
    /// erasure bridge needs.
    fn add_par_reduces_p_marked_triangle_star(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_pL_triangle_star".to_string(),
            type_src: concat!(
                "forall (env : RecEnv), ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                // iota_join_star: the isolated wall — the iota arm's exact STAR content.
                "(forall (e0 : KExpr) (e2 : KExpr) (r : KExpr), ",
                "par_reduces_p_star env e2 (cd env e0) -> iota_step env e2 r -> ",
                "par_reduces_p_star env r (cd env e0)) -> ",
                "forall (n : Nat) (e : KExpr) (e' : KExpr), ",
                "par_reduces_pL env n e e' -> par_reduces_p_star env e' (cd env e)"
            )
            .to_string(),
            value_src: Some(par_reduces_p_marked_triangle_star_proof()),
            is_axiom: false,
            description: concat!(
                "STEP 2 (#2859 Increment F++, design §17): the STAR-VALUED MARKED TRIANGLE ",
                "par_reduces_pL_triangle_star — e ⇒L_n e' → e' ⇒*_p cd e, the star sibling of ",
                "par_reduces_pL_triangle_scaffold. Structural recursion on the marked derivation ",
                "(par_reduces_pL.rec) with motive M n a b _ := par_reduces_p_star env b (cd env a). The eight ",
                "non-iota arms close UNCONDITIONALLY by lifting the landed single-step development bricks to the ",
                "star motive via par_reduces_p_star_{app,lam,pi,forall} / par_subst_p_star (refl: ",
                "par_subsumes_par_p_star cd_refl; app: par_reduces_p_star_app on the rec star-IHs + one ",
                "par_reduces_p_app_dev development step subsumed+star-trans'd; lam/pi/forall_: ",
                "par_reduces_p_star_{lam,pi,forall} on the rec star-IHs by cd-defeq; beta: par_subst_p_star + ",
                "cd_app_lam transport; let_ ZETA: par_subst_p_star + cd_let transport; let_cong: one zeta-fire ",
                "(par_reduces_p.let_, reflexive premises, subsumed) + par_subst_p_star star-trans'd + cd_let ",
                "transport). The iota arm — the fire-vs-development local-confluence join — is isolated ",
                "as the single faithful STAR hypothesis iota_join_star (e2 ⇒*_p cd e0 → iota_step e2 r → r ⇒*_p ",
                "cd e0), FED the recursor's structural star-IH e2 ⇒*_p cd x and the fire. Honest scope (§16/§17): ",
                "the keystone par_reduces_pL_reduct_cong joins TWO iota fires of a marked derivation's endpoints; ",
                "this arm has only one fire + a plain star development IH, so consuming the keystone needs a ",
                "marked/confluence-valued triangle motive (the precise next residual). NO fabricated term. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F++, STAR-valued marked triangle)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_pL".to_string(),
                "par_reduces_pL.rec".to_string(),
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p_star".to_string(),
                "par_reduces_p_star.refl".to_string(),
                "par_reduces_p_star.step".to_string(),
                "par_reduces_p_star_app".to_string(),
                "par_reduces_p_star_lam".to_string(),
                "par_reduces_p_star_pi".to_string(),
                "par_reduces_p_star_forall".to_string(),
                "par_subst_p_star".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_star_trans".to_string(),
                "par_reduces_pL_erase".to_string(),
                "cd_refl".to_string(),
                "cd_app_lam".to_string(),
                "cd_let".to_string(),
                "par_reduces_p_app_dev".to_string(),
                "cd".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `par_reduces_pL_erase` — the labels-drop erasure. A single
/// `par_reduces_pL.rec` whose motive forgets the fuel index, mapping each marked
/// constructor to the matching unlabeled `par_reduces_p` constructor on the recursor
/// IHs (which are already `par_reduces_p` derivations).
fn par_reduces_p_marked_erase_proof() -> String {
    concat!(
        "fun (env : RecEnv) (n : Nat) (e : KExpr) (e' : KExpr) (h : par_reduces_pL env n e e') => ",
        "@par_reduces_pL.rec env ",
        // motive: forget the fuel index, land in par_reduces_p env a b
        "(fun (_n : Nat) (a : KExpr) (b : KExpr) (_ : par_reduces_pL env _n a b) => par_reduces_p env a b) ",
        // refl
        "(fun (x : KExpr) => par_reduces_p.refl env x) ",
        // beta
        "(fun (nA : Nat) (nb : Nat) (na : Nat) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_pL env nA A A') (_hb : par_reduces_pL env nb body body') (_ha : par_reduces_pL env na arg arg') ",
        "(ihA : par_reduces_p env A A') (ihb : par_reduces_p env body body') (iha : par_reduces_p env arg arg') => ",
        "par_reduces_p.beta env A A' body body' arg arg' ihA ihb iha) ",
        // app
        "(fun (nf : Nat) (na : Nat) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_pL env nf f f') (_ha : par_reduces_pL env na a a') ",
        "(ihf : par_reduces_p env f f') (iha : par_reduces_p env a a') => ",
        "par_reduces_p.app env f f' a a' ihf iha) ",
        // lam
        "(fun (nt : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env ty ty') (ihb : par_reduces_p env body body') => ",
        "par_reduces_p.lam env ty ty' body body' iht ihb) ",
        // pi
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env dom dom') (ihb : par_reduces_p env body body') => ",
        "par_reduces_p.pi env dom dom' body body' iht ihb) ",
        // forall_
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env dom dom') (ihb : par_reduces_p env body body') => ",
        "par_reduces_p.forall_ env dom dom' body body' iht ihb) ",
        // let_
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env ty ty') (ihv : par_reduces_p env val val') (ihb : par_reduces_p env body body') => ",
        "par_reduces_p.let_ env ty ty' val val' body body' iht ihv ihb) ",
        // iota_p
        "(fun (ne : Nat) (x : KExpr) (e2 : KExpr) (r : KExpr) ",
        "(_he : par_reduces_pL env ne x e2) (hi : iota_step env e2 r) ",
        "(ihe : par_reduces_p env x e2) => ",
        "par_reduces_p.iota_p env x e2 r ihe hi) ",
        // let_cong (trailing congruence ctor -> par_reduces_p.let_cong)
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env ty ty') (ihv : par_reduces_p env val val') (ihb : par_reduces_p env body body') => ",
        "par_reduces_p.let_cong env ty ty' val val' body body' iht ihv ihb) ",
        // indices + scrutinee
        "n e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_reduces_pL_reduct_cong` — THE marked-fuel keystone.
///
/// Outer `par_reduces_pL_fuel_rec` on the fuel with the universalized motive
/// `Q k := forall e m r rm, par_reduces_pL env k e m -> iota_step env e r ->
/// iota_step env m rm -> par_reduces_p_star env r rm`. In the step `(k, IH)` we get
/// `Q k`: take `(e m r rm)(h : e ⇒L_k m)(hr : iota_step e r)(hrm : iota_step m rm)`
/// and dispatch with an INNER `par_reduces_pL.rec` over `h` with the fuel-equation
/// convoy motive
/// `M k0 a b _ := Eq Nat k0 k -> forall r0 rm0, iota_step a r0 -> iota_step b rm0
///                -> par_reduces_p_star env r0 rm0`.
/// The iota_p arm is the crux: it recurses via the OUTER `IH` at the premise fuel
/// `ne` (`Lt ne k` from `lt_succ_self ne` transported along the convoy
/// `Eq Nat (succ ne) k`), joining `r0 ⇒*_p rfire ⇒*_p rm0`.
fn par_reduces_p_marked_reduct_cong_proof() -> String {
    // Outer motive Q : Nat -> Type.
    let q_motive = concat!(
        "(fun (k : Nat) => forall (e0 : KExpr) (m0 : KExpr) (r0 : KExpr) (rm0 : KExpr), ",
        "par_reduces_pL env k e0 m0 -> iota_step env e0 r0 -> iota_step env m0 rm0 -> ",
        "par_reduces_p_star env r0 rm0)"
    );
    // Inner par_reduces_pL.rec convoy motive: keeps the fuel equation + universalizes
    // the two fires over the recursion. a = source, b = target.
    let inner_motive = concat!(
        "(fun (k0 : Nat) (a : KExpr) (b : KExpr) (_d : par_reduces_pL env k0 a b) => ",
        "Eq Nat k0 k -> forall (r0 : KExpr) (rm0 : KExpr), ",
        "iota_step env a r0 -> iota_step env b rm0 -> par_reduces_p_star env r0 rm0)"
    );

    // The binder/beta/let discharge: the source `a` is binder/lam-app-headed, so its
    // head const is none — `iota_step env a r0` is absurd. shape = the concrete source.
    let head_none_arm = |binders: &str, shape: &str| -> String {
        format!(
            "(fun {binders} \
             (_g : Eq Nat _k0 k) (r0 : KExpr) (rm0 : KExpr) \
             (hr0 : iota_step env ({shape}) r0) (_hrm0 : iota_step env _b rm0) => \
             iota_step_head_none_absurd_type env ({shape}) r0 (par_reduces_p_star env r0 rm0) \
             (Eq.refl (OptionType Name) (OptionType.none Name)) hr0)"
        )
    };

    // refl arm: a = b = s; both fires on s; r0 = rm0 (determinism); refl transported.
    let refl_arm = concat!(
        "(fun (s : KExpr) (_g : Eq Nat Nat.zero k) (r0 : KExpr) (rm0 : KExpr) ",
        "(hr0 : iota_step env s r0) (hrm0 : iota_step env s rm0) => ",
        "Eq.substType KExpr (fun (z : KExpr) => par_reduces_p_star env r0 z) r0 rm0 ",
        "(iota_step_deterministic env s r0 rm0 hr0 hrm0) ",
        "(par_reduces_p_star.refl env r0))"
    );

    // beta arm: a = app (lam A body) arg ; discharge.
    let beta_arm = head_none_arm(
        "(nA : Nat) (nb : Nat) (na : Nat) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (_hA : par_reduces_pL env nA A A') (_hb : par_reduces_pL env nb body body') (_ha : par_reduces_pL env na arg arg') \
         (_ihA : Eq Nat nA k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env A r1 -> iota_step env A' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1) \
         (_iha : Eq Nat na k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env arg r1 -> iota_step env arg' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.app (KExpr.lam A body) arg",
    )
    .replace("_k0", "(Nat.succ (Nat.add (Nat.add nA nb) na))")
    .replace("_b", "(instantiate body' arg')");

    // app arm: a = app f g, b = app f' g'. Case-split on iota_reduct env f (the
    // over-application discriminator) via OptionType.rec with the equation-carrying
    // motive M o := Eq (iota_reduct env f) o -> par_reduces_p_star env r0 rm0:
    //   * none arm (f NOT a redex — the MINIMAL/boundary case): discharge internally via
    //     the landed par_reduces_p_app_reduct_cong_minimal (the boundary-case happ
    //     congruence), fed the erased sub-legs + the faithful disjointness interface.
    //   * some f1 arm (f ITSELF a redex — OVER-APPLICATION): the residual; routed to the
    //     narrower hypothesis happ_over (the over-app sub-case the directed fuel IH cannot
    //     supply a confluence sub-diamond for — design §16 residual).
    let app_arm = concat!(
        "(fun (nf : Nat) (ng : Nat) (f : KExpr) (f' : KExpr) (g : KExpr) (g' : KExpr) ",
        "(hf : par_reduces_pL env nf f f') (hg : par_reduces_pL env ng g g') ",
        "(_ihf : Eq Nat nf k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env f r1 -> iota_step env f' rm1 -> par_reduces_p_star env r1 rm1) ",
        "(_ihg : Eq Nat ng k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env g r1 -> iota_step env g' rm1 -> par_reduces_p_star env r1 rm1) ",
        "(_g : Eq Nat (Nat.add nf ng) k) (r0 : KExpr) (rm0 : KExpr) ",
        "(hr0 : iota_step env (KExpr.app f g) r0) (hrm0 : iota_step env (KExpr.app f' g') rm0) => ",
        "@OptionType.rec KExpr ",
        // motive M o := Eq (iota_reduct env f) o -> par_reduces_p_star env r0 rm0
        "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env f) o -> par_reduces_p_star env r0 rm0) ",
        // none arm: the MINIMAL case.
        "(fun (hfn0 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => ",
        "par_reduces_p_app_reduct_cong_minimal env f f' g g' r0 rm0 disjoint hfn0 ",
        "(par_reduces_pL_erase env nf f f' hf) (par_reduces_pL_erase env ng g g' hg) hr0 hrm0) ",
        // some f1 arm: the OVER-APPLICATION residual.
        "(fun (f1 : KExpr) (hfs0 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => ",
        "happ_over f f' g g' f1 r0 rm0 hfs0 ",
        "(par_reduces_pL_erase env nf f f' hf) (par_reduces_pL_erase env ng g g' hg) hr0 hrm0) ",
        "(iota_reduct env f) (Eq.refl (OptionType KExpr) (iota_reduct env f)))"
    );

    // lam arm.
    let lam_arm = head_none_arm(
        "(nt : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
         (_ht : par_reduces_pL env nt ty ty') (_hb : par_reduces_pL env nb body body') \
         (_iht : Eq Nat nt k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env ty r1 -> iota_step env ty' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.lam ty body",
    )
    .replace("_k0", "(Nat.add nt nb)")
    .replace("_b", "(KExpr.lam ty' body')");

    // pi arm.
    let pi_arm = head_none_arm(
        "(nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') \
         (_iht : Eq Nat nt k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env dom r1 -> iota_step env dom' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.pi dom body",
    )
    .replace("_k0", "(Nat.add nt nb)")
    .replace("_b", "(KExpr.pi dom' body')");

    // forall_ arm.
    let forall_arm = head_none_arm(
        "(nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') \
         (_iht : Eq Nat nt k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env dom r1 -> iota_step env dom' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.forall_ dom body",
    )
    .replace("_k0", "(Nat.add nt nb)")
    .replace("_b", "(KExpr.forall_ dom' body')");

    // let_ arm (ZETA ctor): a = let_ ty val body, a genuine let node whose spine head is
    // itself (kexpr_const_name (kapp_fn (let_ ...)) = none), so iota_step env a r0 is
    // absurd — discharge. Fuel succ (add (add nt nv) nb), target instantiate body' val'.
    let let_arm = head_none_arm(
        "(nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') \
         (_iht : Eq Nat nt k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env ty r1 -> iota_step env ty' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihv : Eq Nat nv k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env val r1 -> iota_step env val' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.let_ ty val body",
    )
    .replace("_k0", "(Nat.succ (Nat.add (Nat.add nt nv) nb))")
    .replace("_b", "(instantiate body' val')");

    // let_cong arm (the NEW trailing congruence ctor): SAME let_-headed source (still
    // head-none, so the iota fire is absurd — discharge), only the fuel (additive: add
    // (add nt nv) nb, no succ) and target (let_ ty' val' body') differ.
    let let_cong_arm = head_none_arm(
        "(nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') \
         (_iht : Eq Nat nt k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env ty r1 -> iota_step env ty' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihv : Eq Nat nv k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env val r1 -> iota_step env val' rm1 -> par_reduces_p_star env r1 rm1) \
         (_ihb : Eq Nat nb k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env body r1 -> iota_step env body' rm1 -> par_reduces_p_star env r1 rm1)",
        "KExpr.let_ ty val body",
    )
    .replace("_k0", "(Nat.add (Nat.add nt nv) nb)")
    .replace("_b", "(KExpr.let_ ty' val' body')");

    // iota_p arm — THE CRUX. a = source x, b = rfire (the fire reduct), the whole
    // derivation is x ⇒L (succ ne) rfire. Convoy gives Eq Nat (succ ne) k. The fires
    // are hr0 : iota_step x r0 and hrm0 : iota_step rfire rm0. Recurse via the OUTER
    // IH at fuel ne (Lt ne k via lt_succ_self transported along the convoy), on the
    // sub-leg he : x ⇒L_ne e2 with the fires (r0 on x, rfire on e2 = hi):
    //   r0 ⇒*_p rfire ; then rfire ⇒_p rm0 (iota_redex_to_reduct) ; star_trans.
    let iota_arm = concat!(
        "(fun (ne : Nat) (x : KExpr) (e2 : KExpr) (rfire : KExpr) ",
        "(he : par_reduces_pL env ne x e2) (hi : iota_step env e2 rfire) ",
        "(_ihe : Eq Nat ne k -> forall (r1 : KExpr) (rm1 : KExpr), iota_step env x r1 -> iota_step env e2 rm1 -> par_reduces_p_star env r1 rm1) ",
        "(g : Eq Nat (Nat.succ ne) k) (r0 : KExpr) (rm0 : KExpr) ",
        "(hr0 : iota_step env x r0) (hrm0 : iota_step env rfire rm0) => ",
        // r0 ⇒*_p rfire via the outer IH at fuel ne.
        "par_reduces_p_star_trans env r0 rfire rm0 ",
        "(IH ne ",
        // Lt ne k : transport lt_succ_self ne : Lt ne (succ ne) along g : Eq (succ ne) k.
        "(Eq.substType Nat (fun (z : Nat) => Lt ne z) (Nat.succ ne) k g (lt_succ_self ne)) ",
        // Q ne applied: x e2 r0 rfire, with he, hr0, hi.
        "x e2 r0 rfire he hr0 hi) ",
        // rfire ⇒*_p rm0 : embed the single iota_redex_to_reduct step.
        "(par_subsumes_par_p_star env rfire rm0 ",
        "(par_reduces_p_iota_redex_to_reduct env rfire rm0 hrm0)))"
    );

    // The fuel_rec step lambda: (k, IH) -> Q k. Take (e0 m0 r m_rm)(h)(hr)(hrm), run
    // the inner par_reduces_pL.rec, then apply the convoy (refl Eq) + the fires.
    let step = format!(
        "(fun (k : Nat) (IH : forall (j : Nat), Lt j k -> {q_motive_applied}) \
         (e0 : KExpr) (m0 : KExpr) (r : KExpr) (rm : KExpr) \
         (h : par_reduces_pL env k e0 m0) (hr : iota_step env e0 r) (hrm : iota_step env m0 rm) => \
         @par_reduces_pL.rec env {inner_motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} \
         k e0 m0 h (Eq.refl Nat k) r rm hr hrm)",
        q_motive_applied = concat!(
            "forall (e0 : KExpr) (m0 : KExpr) (r0 : KExpr) (rm0 : KExpr), ",
            "par_reduces_pL env j e0 m0 -> iota_step env e0 r0 -> iota_step env m0 rm0 -> ",
            "par_reduces_p_star env r0 rm0"
        ),
    );

    format!(
        "fun (env : RecEnv) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (happ_over : forall (f : KExpr) (f' : KExpr) (g : KExpr) (g' : KExpr) (f1 : KExpr) (r0 : KExpr) (rm0 : KExpr), \
         Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> \
         par_reduces_p env f f' -> par_reduces_p env g g' -> \
         iota_step env (KExpr.app f g) r0 -> iota_step env (KExpr.app f' g') rm0 -> \
         par_reduces_p_star env r0 rm0) \
         (n : Nat) (e : KExpr) (m : KExpr) (r : KExpr) (rm : KExpr) \
         (h : par_reduces_pL env n e m) (hr : iota_step env e r) (hrm : iota_step env m rm) => \
         par_reduces_pL_fuel_rec {q_motive} {step} n e m r rm h hr hrm"
    )
}

/// Closed proof term for `par_reduces_pL_triangle_scaffold` — the MARKED TRIANGLE.
/// A single `par_reduces_pL.rec` (structural on the marked derivation) with the triangle
/// motive `M n a b _ := par_reduces_p env b (cd env a)`. Each arm's rec-IH on a premise
/// `par_reduces_pL env nx X X'` is `par_reduces_p env X' (cd env X)` (the development of
/// `X`). Non-iota arms close with the landed cd-development bricks; the iota arm feeds
/// `iota_join` the IH development `e2 ⇒_p cd x` (THE CRACK — the recursor supplies it
/// structurally, the development the unlabeled route could not obtain). forall_ rides
/// the `forall_ ≡ pi` definitional alias (cd computes through it); the two let arms
/// (let_ ZETA and let_cong) use genuine-let reasoning via `cd_let` (the OLD let_ ≡
/// app(lam) alias is gone).
fn par_reduces_p_marked_triangle_scaffold_proof() -> String {
    concat!(
        "fun (env : RecEnv) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
        "(iota_join : forall (e0 : KExpr) (e2 : KExpr) (r : KExpr), ",
        "par_reduces_p env e2 (cd env e0) -> iota_step env e2 r -> par_reduces_p env r (cd env e0)) ",
        "(n : Nat) (e : KExpr) (e' : KExpr) (h : par_reduces_pL env n e e') => ",
        "@par_reduces_pL.rec env ",
        // triangle motive: M n a b _ := par_reduces_p env b (cd env a)
        "(fun (_n : Nat) (a : KExpr) (b : KExpr) (_ : par_reduces_pL env _n a b) => par_reduces_p env b (cd env a)) ",
        // refl: a = b = x, goal x ⇒_p cd x = cd_refl env x
        "(fun (x : KExpr) => cd_refl env x) ",
        // beta: source app (lam A body) arg, reduct instantiate body' arg'.
        // ihbody : body' ⇒_p cd body, iharg : arg' ⇒_p cd arg. par_reduces_p_beta_dev.
        "(fun (nA : Nat) (nb : Nat) (na : Nat) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_pL env nA A A') (_hb : par_reduces_pL env nb body body') (_ha : par_reduces_pL env na arg arg') ",
        "(_ihA : par_reduces_p env A' (cd env A)) (ihbody : par_reduces_p env body' (cd env body)) (iharg : par_reduces_p env arg' (cd env arg)) => ",
        "par_reduces_p_beta_dev env A body arg body' arg' ihbody iharg closed liftclosed) ",
        // app: source app f a, reduct app f' a'. erase hf : f ⇒_p f', erase ha : a ⇒_p a';
        // ihf : f' ⇒_p cd f, iha : a' ⇒_p cd a. par_reduces_p_app_dev.
        "(fun (nf : Nat) (na : Nat) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(hf : par_reduces_pL env nf f f') (ha : par_reduces_pL env na a a') ",
        "(ihf : par_reduces_p env f' (cd env f)) (iha : par_reduces_p env a' (cd env a)) => ",
        "par_reduces_p_app_dev env f f' a a' ",
        "(par_reduces_pL_erase env nf f f' hf) (par_reduces_pL_erase env na a a' ha) ihf iha) ",
        // lam: source lam ty body, reduct lam ty' body'. Goal lam ty' body' ⇒_p cd (lam ty body).
        // par_reduces_p.lam env ty' (cd ty) body' (cd body) iht ihb : lam ty' body' ⇒_p lam (cd ty)(cd body) ≡ cd (lam ty body).
        "(fun (nt : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env ty' (cd env ty)) (ihb : par_reduces_p env body' (cd env body)) => ",
        "par_reduces_p.lam env ty' (cd env ty) body' (cd env body) iht ihb) ",
        // pi: same shape via par_reduces_p.pi.
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env dom' (cd env dom)) (ihb : par_reduces_p env body' (cd env body)) => ",
        "par_reduces_p.pi env dom' (cd env dom) body' (cd env body) iht ihb) ",
        // forall_: source forall_ dom body ≡ pi dom body; cd (forall_ dom body) ≡ pi (cd dom)(cd body)
        // ≡ forall_ (cd dom)(cd body). par_reduces_p.forall_ lands forall_ dom' body' ⇒_p forall_ (cd dom)(cd body).
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env dom' (cd env dom)) (ihb : par_reduces_p env body' (cd env body)) => ",
        "par_reduces_p.forall_ env dom' (cd env dom) body' (cd env body) iht ihb) ",
        // let_ (ZETA ctor): source let_ ty val body, reduct instantiate body' val'. Genuine
        // let reasoning (the OLD let_ ≡ app(lam) alias is gone): cd (let_ ty val body) =
        // instantiate (cd body)(cd val) (cd_let, the cd analogue of cd_app_lam). par_subst_p
        // (depth 0) lands instantiate body' val' ⇒_p instantiate (cd body)(cd val) from
        // ihbody/ihval, transported to cd (let_ ty val body) by cd_let. (Type IH _iht dropped.)
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(_iht : par_reduces_p env ty' (cd env ty)) (ihval : par_reduces_p env val' (cd env val)) (ihbody : par_reduces_p env body' (cd env body)) => ",
        "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env (instantiate body' val') Z) ",
        "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
        "(cd_let env ty val body)) ",
        "(par_subst_p env body' (cd env body) val' (cd env val) Nat.zero ihbody ihval closed liftclosed)) ",
        // iota_p: THE WALL. source x, reduct r; he : x ⇒L_ne e2, hi : iota_step e2 r.
        // ihe : e2 ⇒_p cd x (THE CRACK — the recursor's structural IH). Feed iota_join.
        "(fun (ne : Nat) (x : KExpr) (e2 : KExpr) (r : KExpr) ",
        "(_he : par_reduces_pL env ne x e2) (hi : iota_step env e2 r) ",
        "(ihe : par_reduces_p env e2 (cd env x)) => ",
        "iota_join x e2 r ihe hi) ",
        // let_cong (trailing congruence ctor): source let_ ty val body, target let_ ty' val'
        // body'. The reduct let_ ty' val' body' fires the zeta cd took — par_reduces_p.let_
        // (ZETA) on iht/ihval/ihbody lands it at instantiate (cd body)(cd val), transported
        // to cd (let_ ty val body) by cd_let.
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p env ty' (cd env ty)) (ihval : par_reduces_p env val' (cd env val)) (ihbody : par_reduces_p env body' (cd env body)) => ",
        "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env (KExpr.let_ ty' val' body') Z) ",
        "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
        "(cd_let env ty val body)) ",
        "(par_reduces_p.let_ env ty' (cd env ty) val' (cd env val) body' (cd env body) iht ihval ihbody)) ",
        // indices + scrutinee
        "n e e' h"
    )
    .to_string()
}

/// Closed proof term for `par_reduces_pL_triangle_star` — the STAR-VALUED MARKED
/// TRIANGLE (#2859 Increment F++, design §17). A single `par_reduces_pL.rec` (structural
/// on the marked derivation) with the STAR triangle motive
/// `M n a b _ := par_reduces_p_star env b (cd env a)`. Each arm's rec-IH on a premise
/// `par_reduces_pL env nx X X'` is the STAR development `par_reduces_p_star env X' (cd env X)`.
/// The eight non-iota arms close UNCONDITIONALLY by lifting the landed single-step
/// development bricks to the star motive via the new
/// `par_reduces_p_star_{app,lam,pi,forall}` / `par_subst_p_star` congruences; the iota arm
/// feeds the isolated STAR hypothesis `iota_join` its star-IH development `e2 ⇒*_p cd x`
/// (the level §10/§14 established the iota join lives at). forall_ rides the
/// `forall_ ≡ pi` definitional alias (cd computes through it); the two let arms (let_ ZETA
/// and let_cong) use genuine-let reasoning via `cd_let` (the OLD let_ ≡ app(lam) alias is gone).
fn par_reduces_p_marked_triangle_star_proof() -> String {
    concat!(
        "fun (env : RecEnv) (closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) ",
        "(iota_join : forall (e0 : KExpr) (e2 : KExpr) (r : KExpr), ",
        "par_reduces_p_star env e2 (cd env e0) -> iota_step env e2 r -> par_reduces_p_star env r (cd env e0)) ",
        "(n : Nat) (e : KExpr) (e' : KExpr) (h : par_reduces_pL env n e e') => ",
        "@par_reduces_pL.rec env ",
        // STAR triangle motive: M n a b _ := par_reduces_p_star env b (cd env a)
        "(fun (_n : Nat) (a : KExpr) (b : KExpr) (_ : par_reduces_pL env _n a b) => par_reduces_p_star env b (cd env a)) ",
        // refl: a = b = x, goal x ⇒*_p cd x = star-wrap cd_refl env x.
        "(fun (x : KExpr) => par_subsumes_par_p_star env x (cd env x) (cd_refl env x)) ",
        // beta: source app (lam A body) arg, reduct instantiate body' arg'.
        // ihbody : body' ⇒*_p cd body, iharg : arg' ⇒*_p cd arg. par_subst_p_star reaches
        // instantiate body' arg' ⇒*_p instantiate (cd body)(cd arg); transport the TARGET to
        // cd (app (lam A body) arg) by Eq.symm (cd_app_lam env A body arg).
        "(fun (nA : Nat) (nb : Nat) (na : Nat) (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_pL env nA A A') (_hb : par_reduces_pL env nb body body') (_ha : par_reduces_pL env na arg arg') ",
        "(_ihA : par_reduces_p_star env A' (cd env A)) (ihbody : par_reduces_p_star env body' (cd env body)) (iharg : par_reduces_p_star env arg' (cd env arg)) => ",
        "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p_star env (instantiate body' arg') Z) ",
        "(instantiate (cd env body) (cd env arg)) (cd env (KExpr.app (KExpr.lam A body) arg)) ",
        "(Eq.symm KExpr (cd env (KExpr.app (KExpr.lam A body) arg)) (instantiate (cd env body) (cd env arg)) ",
        "(cd_app_lam env A body arg)) ",
        "(par_subst_p_star env body' (cd env body) arg' (cd env arg) ihbody iharg closed liftclosed)) ",
        // app: source app f a, reduct app f' a'. ihf : f' ⇒*_p cd f, iha : a' ⇒*_p cd a.
        // Phase 1: par_reduces_p_star_app reaches app f' a' ⇒*_p app (cd f)(cd a).
        // Phase 2: ONE landed par_reduces_p_app_dev development step
        //   app (cd f)(cd a) ⇒_p cd (app f a)  (its single-step IHs are cd_refl f / cd_refl a
        //   and the post-IHs cd f ⇒_p cd f / cd a ⇒_p cd a via par_reduces_p.refl),
        // subsumed to star and composed by par_reduces_p_star_trans.
        "(fun (nf : Nat) (na : Nat) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_pL env nf f f') (_ha : par_reduces_pL env na a a') ",
        "(ihf : par_reduces_p_star env f' (cd env f)) (iha : par_reduces_p_star env a' (cd env a)) => ",
        "par_reduces_p_star_trans env (KExpr.app f' a') (KExpr.app (cd env f) (cd env a)) (cd env (KExpr.app f a)) ",
        "(par_reduces_p_star_app env f' (cd env f) a' (cd env a) ihf iha) ",
        "(par_subsumes_par_p_star env (KExpr.app (cd env f) (cd env a)) (cd env (KExpr.app f a)) ",
        "(par_reduces_p_app_dev env f (cd env f) a (cd env a) ",
        "(cd_refl env f) (cd_refl env a) ",
        "(par_reduces_p.refl env (cd env f)) (par_reduces_p.refl env (cd env a))))) ",
        // lam: source lam ty body, reduct lam ty' body'. iht : ty' ⇒*_p cd ty, ihb : body' ⇒*_p cd body.
        // par_reduces_p_star_lam : lam ty' body' ⇒*_p lam (cd ty)(cd body) ≡ cd (lam ty body) (defeq).
        "(fun (nt : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p_star env ty' (cd env ty)) (ihb : par_reduces_p_star env body' (cd env body)) => ",
        "par_reduces_p_star_lam env ty' (cd env ty) body' (cd env body) iht ihb) ",
        // pi: same shape via par_reduces_p_star_pi.
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p_star env dom' (cd env dom)) (ihb : par_reduces_p_star env body' (cd env body)) => ",
        "par_reduces_p_star_pi env dom' (cd env dom) body' (cd env body) iht ihb) ",
        // forall_: forall_ dom body ≡ pi dom body; cd (forall_ dom body) ≡ forall_ (cd dom)(cd body) (defeq).
        // par_reduces_p_star_forall : forall_ dom' body' ⇒*_p forall_ (cd dom)(cd body).
        "(fun (nt : Nat) (nb : Nat) (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt dom dom') (_hb : par_reduces_pL env nb body body') ",
        "(iht : par_reduces_p_star env dom' (cd env dom)) (ihb : par_reduces_p_star env body' (cd env body)) => ",
        "par_reduces_p_star_forall env dom' (cd env dom) body' (cd env body) iht ihb) ",
        // let_ (ZETA ctor): source let_ ty val body, reduct instantiate body' val'. Genuine
        // let reasoning (the OLD let_ ≡ app(lam) alias is gone): cd (let_ ty val body) =
        // instantiate (cd body)(cd val) (cd_let, the cd analogue of cd_app_lam).
        // par_subst_p_star reaches instantiate body' val' ⇒*_p instantiate (cd body)(cd val);
        // transport the TARGET by Eq.symm (cd_let env ty val body).
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(_iht : par_reduces_p_star env ty' (cd env ty)) (ihval : par_reduces_p_star env val' (cd env val)) (ihbody : par_reduces_p_star env body' (cd env body)) => ",
        "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p_star env (instantiate body' val') Z) ",
        "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
        "(cd_let env ty val body)) ",
        "(par_subst_p_star env body' (cd env body) val' (cd env val) ihbody ihval closed liftclosed)) ",
        // iota_p: THE WALL (star). source x, reduct r; he : x ⇒L_ne e2, hi : iota_step e2 r.
        // ihe : e2 ⇒*_p cd x (THE CRACK — the recursor's structural STAR IH). Feed iota_join.
        "(fun (ne : Nat) (x : KExpr) (e2 : KExpr) (r : KExpr) ",
        "(_he : par_reduces_pL env ne x e2) (hi : iota_step env e2 r) ",
        "(ihe : par_reduces_p_star env e2 (cd env x)) => ",
        "iota_join x e2 r ihe hi) ",
        // let_cong (trailing congruence ctor): source let_ ty val body, target let_ ty' val'
        // body'. cd (let_ ty val body) = instantiate (cd body)(cd val) (cd_let). Route in
        // star: one zeta step let_ ty' val' body' ⇒_p instantiate body' val'
        // (par_reduces_p.let_ with reflexive premises, subsumed to star), then
        // par_subst_p_star to instantiate (cd body)(cd val), joined by star_trans and
        // transported to cd (let_ ty val body) by cd_let. (Avoids needing par_reduces_p_star_let.)
        "(fun (nt : Nat) (nv : Nat) (nb : Nat) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_ht : par_reduces_pL env nt ty ty') (_hv : par_reduces_pL env nv val val') (_hb : par_reduces_pL env nb body body') ",
        "(_iht : par_reduces_p_star env ty' (cd env ty)) (ihval : par_reduces_p_star env val' (cd env val)) (ihbody : par_reduces_p_star env body' (cd env body)) => ",
        "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p_star env (KExpr.let_ ty' val' body') Z) ",
        "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
        "(cd_let env ty val body)) ",
        "(par_reduces_p_star_trans env (KExpr.let_ ty' val' body') (instantiate body' val') (instantiate (cd env body) (cd env val)) ",
        "(par_subsumes_par_p_star env (KExpr.let_ ty' val' body') (instantiate body' val') ",
        "(par_reduces_p.let_ env ty' ty' val' val' body' body' (par_reduces_p.refl env ty') (par_reduces_p.refl env val') (par_reduces_p.refl env body'))) ",
        "(par_subst_p_star env body' (cd env body) val' (cd env val) ihbody ihval closed liftclosed))) ",
        // indices + scrutinee
        "n e e' h"
    )
    .to_string()
}

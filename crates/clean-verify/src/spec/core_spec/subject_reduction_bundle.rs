// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Subject reduction for the context-indexed declarative-with-conversion
//! judgment `TypingCtxConv` (Aristotle port, strategy guide
//! `scratch/aristotle-harvest/aristotle-subjred/aristotle-subjred_aristotle/
//! SubjRed.lean`, namespace
//! `CleanSubjectReduction`, [propext, Quot.sound]-only closure there; explicit
//! zero-axiom terms here).
//!
//! Deliverables (registered bottom-up, every decl `DerivedProved` with EMPTY
//! axiom closure):
//!
//!  - `TypingEnvCoherent` — the LABELED env-coherence hypothesis bundle (the
//!    mirror's `EnvAssumptions`), an interface inductive in the
//!    `RecEnvWellformed`/`RedEnvFaithful` carried-hypothesis discipline. See
//!    the field-by-field in-tree mapping on the inductive below. NEVER an
//!    axiom: every theorem takes a `TypingEnvCoherent tenv` parameter.
//!  - the weakening tower: `CtxWk` (context insertion at a cutoff),
//!    `ctx_wk_lookup` (CPS lookup transport), `weaken_gen`, `weaken1`.
//!  - `def_eq_psubst` — DefEq is stable under parallel substitution (the
//!    psubst generalization of the in-tree `def_eq_respects_subst_at`).
//!  - the substitution tower: `SubstTyping`, `subst_typing_id/up/scons`,
//!    `substitution_general` (the psubst-general substitution lemma) and its
//!    classic single-substitution instance `substitution_typing_ctx`.
//!  - context conversion: `CtxDefEq`, `ctx_def_eq_refl`, `ctx_def_eq_lookup`,
//!    `ctx_conv`.
//!  - generation (inversion) lemmas `ctx_app_gen` / `ctx_lam_gen` /
//!    `ctx_pi_gen` / `ctx_let_gen` in the in-tree CPS style (`typing_app_gen`).
//!  - preservation: `delta_preserves_typing_ctx` (PROVED from the labeled
//!    `defval_typed` field + the computational delta_reduct decomposition),
//!    `beta_reduces_preserves_typing_ctx` (the full 14-arm subject reduction
//!    over `beta_reduces`), and the WHNF-step dispatcher
//!    `subject_reduction_ctx`.
//!
//! LET INCREMENT (let promotion, task #28; strategy guide
//! `scratch/aristotle-harvest/aristotle-subjred-zeta/
//! aristotle-subjred-zeta_aristotle/SubjRedZeta.lean`): `KExpr.let_` is a
//! genuine 7th constructor, `beta_reduces` gained `zeta`/`let_ty`/`let_val`/
//! `let_body` (the old bundled alias arm is gone), `DefEq` gained `zeta` +
//! ternary `let_cong`, and `TypingCtxConv` gains the standard DEPENDENT let
//! rule (trailing ctor, after `conv`):
//!   `G ⊢ ty : sort u` + `G ⊢ v : ty` + `(ty::G) ⊢ b : B` ⟹
//!   `G ⊢ let_ ty v b : instantiate B v`.
//! Zeta preservation is the textbook SECOND consumer of the substitution
//! lemma — `ctx_let_gen` inversion, then `substitution_typing_ctx`, then one
//! `conv`; NO pi-injectivity, NO new `TypingEnvCoherent` field. Every
//! `TypingCtxConv.rec` tower below gains exactly one trailing `let_` minor;
//! `def_eq_psubst`'s `DefEq.rec` gains the `zeta` + `let_cong` minors.
//!
//! REUSE (map, don't re-port): the ENTIRE psubst calculus of the mirror's §8
//! already exists in `dependent_sn_richmodel.rs` (`scons`/`up`/`upn`/`psubst`,
//! `psubst_cancel(_gen)`, `psubst_up_lift(_gen)`, `psubst_comp`,
//! `instantiate(_at)_eq_psubst`, `psubst_instantiate`,
//! `psubst_scons_instantiate`, `psubst_id`); the lift algebra comes from
//! `lift_at_compose` / `lift_at_lift_at_exchange` / `lift_instantiate_swap`;
//! pi-injectivity is the in-tree confluence-backed
//! `pi_injectivity_def_eq_dom/_cod` (carrying `RedEnvFaithful the_red_env`);
//! lift/DefEq congruence is `def_eq_respects_lift_at_gen`; instantiate/DefEq
//! congruence is `def_eq_respects_subst_at` + `def_eq_instantiate_arg_congr`.
//!
//! Registered AFTER `add_def_eq_lift_congr_lemmas` (Full bundle only): needs
//! `TypingCtxConv`+psubst (add_dependent_sn_richmodel, Full+Substitution),
//! `pi_injectivity_def_eq_*` (Full+ImplSoundness) — Full is the only bundle
//! containing both.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The six labeled env-coherence fields (the mirror's `EnvAssumptions`), with
/// their in-tree mapping:
///
/// 1. `tenv_psubst_closed` — declared constant TYPES are psubst-invariant.
///    NO in-tree analogue (tenv is a bare judgment parameter); carried fresh.
/// 2. `tenv_lift_closed` — declared constant TYPES are lift-invariant.
///    NO in-tree analogue; carried fresh (same reason).
/// 3. `delta_psubst` — δ steps are DefEq-stable under PARALLEL substitution.
///    The instantiate_at INSTANCE is in-tree (`delta_subst_preserves_def_eq_at`
///    via `DefEnvWellformed`'s DEF_WF_SUBST / i5 `DefEnvClosed`); the psubst
///    generalization has no in-tree analogue, so it is carried fresh. (The
///    mirror PROVES it from psubst-closedness of δ values; deriving it in-tree
///    from `DefEnvClosed` is a follow-up — see the module docs.)
/// 4. `iota_psubst` — ι steps are DefEq-stable under parallel substitution.
///    psubst generalization of the in-tree WF_SUBST /
///    `iota_subst_preserves_def_eq_at`; carried fresh (same status).
/// 5. `defval_typed` — δ values are well-typed at their declared tenv types,
///    in any context. The context-indexed generalization of
///    `DefEnvWellformed`'s DEF_WF_FWD; carried fresh.
/// 6. `iota_typed` — ι steps preserve `TypingCtxConv` typing. The
///    context-indexed generalization of `RecEnvWellformed`'s WF_FWD; carried
///    fresh.
const TEC_FIELDS: [&str; 6] = [
    // 1 tenv_psubst_closed
    "forall (n : Name) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> \
     forall (s : Nat -> KExpr), Eq KExpr (psubst s A) A",
    // 2 tenv_lift_closed
    "forall (n : Name) (A : KExpr), Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> \
     forall (c : Nat) (k : Nat), Eq KExpr (lift_at A c k) A",
    // 3 delta_psubst
    "forall (e : KExpr) (e' : KExpr), delta_reduces e e' -> \
     forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')",
    // 4 iota_psubst
    "forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> \
     forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')",
    // 5 defval_typed
    "forall (n : Name) (v : KExpr) (A : KExpr), \
     Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (OptionType.some KExpr v) -> \
     Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A) -> \
     forall (G : ListType KExpr), TypingCtxConv tenv G v A",
    // 6 iota_typed
    "forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> \
     forall (G : ListType KExpr) (T : KExpr), \
     TypingCtxConv tenv G e T -> TypingCtxConv tenv G e' T",
];

const TEC_PROJ_NAMES: [&str; 6] = [
    "tec_tenv_psubst_closed",
    "tec_tenv_lift_closed",
    "tec_delta_psubst",
    "tec_iota_psubst",
    "tec_defval_typed",
    "tec_iota_typed",
];

/// Large-elimination discriminator (`KExpr -> Type`): the genuine `let_`
/// constructor maps to `Empty`, every other constructor to `Nat`. Local copy
/// for the srb-lane sort/bvar/const vs let_ no-confusion lemmas (the B3
/// discrimination lane registers only the app/lam/pi pairings —
/// `let_ne_app`/`app_ne_let` etc. in `expr_model_discrimination_let.rs`).
const SRB_KEXPR_NOT_LET: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Inline KExpr.rec discriminator: non-Proj -> Nat, Proj -> Empty. Used to
/// refute `TypingCtxConv tenv G (KExpr.proj ..) T` by inversion (TypingCtxConv
/// has no proj rule — proj is outside the declarative typing fragment).
const SRB_KEXPR_NOT_PROJ: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    /// Register the full subject-reduction bundle (see module docs).
    pub(super) fn add_subject_reduction_bundle(&mut self) -> Result<(), SpecError> {
        self.add_srb_interface()?;
        self.add_srb_lift_helpers()?;
        self.add_srb_weakening()?;
        self.add_srb_substitution()?;
        self.add_srb_ctx_conv()?;
        self.add_srb_generation()?;
        self.add_srb_preservation()?;
        Ok(())
    }

    /// `TypingEnvCoherent` interface inductive + its six projectors.
    fn add_srb_interface(&mut self) -> Result<(), SpecError> {
        let mk_args = TEC_FIELDS
            .iter()
            .enumerate()
            .map(|(k, t)| format!("(h{} : {t})", k + 1))
            .collect::<Vec<_>>()
            .join(" ");
        self.add_inductive(
            &format!(
                "inductive TypingEnvCoherent (tenv : Name -> OptionType KExpr) : Type\n\
                 | mk : forall {mk_args}, TypingEnvCoherent tenv"
            ),
            "LABELED env-coherence hypothesis bundle for the context-indexed subject-reduction \
             tower (the SubjRed.lean mirror's EnvAssumptions). Six fields: tenv psubst/lift \
             closure, delta/iota DefEq-stability under parallel substitution (psubst \
             generalizations of DEF_WF_SUBST/WF_SUBST), defval_typed (ctx-indexed DEF_WF_FWD), \
             iota_typed (ctx-indexed WF_FWD). A carried HYPOTHESIS interface in the \
             RecEnvWellformed/RedEnvFaithful discipline — never an axiom.",
        )?;

        let binders = TEC_FIELDS
            .iter()
            .enumerate()
            .map(|(k, t)| format!("(a{} : {t})", k + 1))
            .collect::<Vec<_>>()
            .join(" ");
        for (k, field) in TEC_FIELDS.iter().enumerate() {
            let n = k + 1;
            self.add_definition(SpecDefinition {
                name: TEC_PROJ_NAMES[k].to_string(),
                type_src: format!(
                    "forall (tenv : Name -> OptionType KExpr), TypingEnvCoherent tenv -> {field}"
                ),
                value_src: Some(format!(
                    "fun (tenv : Name -> OptionType KExpr) (w : TypingEnvCoherent tenv) => \
                     TypingEnvCoherent.rec tenv \
                     (fun (_ : TypingEnvCoherent tenv) => {field}) \
                     (fun {binders} => a{n}) w"
                )),
                is_axiom: false,
                description: format!(
                    "Projector {n} of TypingEnvCoherent (via TypingEnvCoherent.rec). \
                     DerivedProved, zero axiom_deps. Subject-reduction bundle."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "TypingEnvCoherent".to_string(),
                    "TypingEnvCoherent.rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// `wkpos` + the lift-algebra instances the weakening tower consumes.
    fn add_srb_lift_helpers(&mut self) -> Result<(), SpecError> {
        // wkpos i c: the de Bruijn position of variable i after inserting a
        // fresh context entry at cutoff c (i+1 if c <= i, else i). Same
        // Nat.rec-on-(c - i) shape as lift_bvar_at, so the two compute in step.
        self.add_recursive_def(
            "def wkpos (i : Nat) (c : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) \
             (Nat.succ i) (fun (_ : Nat) (_ : Nat) => i) (Nat.sub c i)",
            "Position of de Bruijn variable i after inserting a context entry at cutoff c \
             (mirror `wkpos`). Nat.rec on (c - i), the lift_bvar_at discriminator shape. \
             Subject-reduction bundle.",
        )?;

        // wkpos_zero: wkpos i 0 = succ i (insertion at the head shifts all).
        self.add_definition(SpecDefinition {
            name: "wkpos_zero".to_string(),
            type_src: "forall (i : Nat), Eq Nat (wkpos i Nat.zero) (Nat.succ i)".to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) => Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) (Nat.succ i) ",
                    "(fun (_ : Nat) (_ : Nat) => i) n) ",
                    "(Nat.sub Nat.zero i) Nat.zero (nat_sub_zero_left i)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "wkpos i 0 = succ i. DerivedProved via Eq.cong over nat_sub_zero_left. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "wkpos".to_string(),
                "nat_sub_zero_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // wkpos_rec_succ: the generalized-discriminator step law behind
        // wkpos_succ_succ (both branches are Eq.refl once n is a literal).
        self.add_definition(SpecDefinition {
            name: "wkpos_rec_succ".to_string(),
            type_src: concat!(
                "forall (j : Nat) (n : Nat), Eq Nat ",
                "(Nat.rec (fun (_ : Nat) => Nat) (Nat.succ (Nat.succ j)) ",
                "(fun (_ : Nat) (_ : Nat) => Nat.succ j) n) ",
                "(Nat.succ (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ j) ",
                "(fun (_ : Nat) (_ : Nat) => j) n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (n : Nat) => Nat.rec ",
                    "(fun (m : Nat) => Eq Nat ",
                    "(Nat.rec (fun (_ : Nat) => Nat) (Nat.succ (Nat.succ j)) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.succ j) m) ",
                    "(Nat.succ (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ j) ",
                    "(fun (_ : Nat) (_ : Nat) => j) m))) ",
                    "(Eq.refl Nat (Nat.succ (Nat.succ j))) ",
                    "(fun (k : Nat) (_ : Eq Nat ",
                    "(Nat.rec (fun (_ : Nat) => Nat) (Nat.succ (Nat.succ j)) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.succ j) k) ",
                    "(Nat.succ (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ j) ",
                    "(fun (_ : Nat) (_ : Nat) => j) k))) => ",
                    "Eq.refl Nat (Nat.succ j)) ",
                    "n",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Discriminator step law: the (succ succ j / succ j) Nat.rec equals succ \
                          of the (succ j / j) Nat.rec, for every discriminant. DerivedProved via \
                          Nat.rec (both arms Eq.refl). Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Nat.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // wkpos_succ_succ: wkpos (succ j) (succ c) = succ (wkpos j c).
        self.add_definition(SpecDefinition {
            name: "wkpos_succ_succ".to_string(),
            type_src: concat!(
                "forall (j : Nat) (c : Nat), ",
                "Eq Nat (wkpos (Nat.succ j) (Nat.succ c)) (Nat.succ (wkpos j c))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (c : Nat) => Eq.trans Nat ",
                    "(wkpos (Nat.succ j) (Nat.succ c)) ",
                    "(Nat.rec (fun (_ : Nat) => Nat) (Nat.succ (Nat.succ j)) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.succ j) (Nat.sub c j)) ",
                    "(Nat.succ (wkpos j c)) ",
                    "(Eq.cong Nat Nat ",
                    "(fun (n : Nat) => Nat.rec (fun (_ : Nat) => Nat) (Nat.succ (Nat.succ j)) ",
                    "(fun (_ : Nat) (_ : Nat) => Nat.succ j) n) ",
                    "(Nat.sub (Nat.succ c) (Nat.succ j)) (Nat.sub c j) ",
                    "(nat_sub_succ_succ c j)) ",
                    "(wkpos_rec_succ j (Nat.sub c j))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "wkpos (succ j) (succ c) = succ (wkpos j c). DerivedProved via \
                          nat_sub_succ_succ transport + wkpos_rec_succ. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "wkpos".to_string(),
                "wkpos_rec_succ".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_bvar_wkpos_rec: lift_bvar_at and wkpos compute in step over the
        // shared discriminant (both arms Eq.refl on a literal).
        self.add_definition(SpecDefinition {
            name: "lift_bvar_wkpos_rec".to_string(),
            type_src: concat!(
                "forall (i : Nat) (n : Nat), Eq KExpr ",
                "(Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) n) ",
                "(KExpr.bvar (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ i) ",
                "(fun (_ : Nat) (_ : Nat) => i) n))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (n : Nat) => Nat.rec ",
                    "(fun (m : Nat) => Eq KExpr ",
                    "(Nat.rec (fun (_ : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) ",
                    "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) m) ",
                    "(KExpr.bvar (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ i) ",
                    "(fun (_ : Nat) (_ : Nat) => i) m))) ",
                    "(Eq.refl KExpr (KExpr.bvar (Nat.succ i))) ",
                    "(fun (k : Nat) (_ : Eq KExpr ",
                    "(Nat.rec (fun (_ : Nat) => KExpr) ",
                    "(KExpr.bvar (Nat.add i (Nat.succ Nat.zero))) ",
                    "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k) ",
                    "(KExpr.bvar (Nat.rec (fun (_ : Nat) => Nat) (Nat.succ i) ",
                    "(fun (_ : Nat) (_ : Nat) => i) k))) => ",
                    "Eq.refl KExpr (KExpr.bvar i)) ",
                    "n",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "lift_bvar_at's KExpr-discriminator and wkpos's Nat-discriminator agree \
                          pointwise. DerivedProved via Nat.rec (both arms Eq.refl). \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Nat.rec".to_string(), "KExpr".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_at_bvar_wkpos: lift_at (bvar i) c 1 = bvar (wkpos i c).
        self.add_definition(SpecDefinition {
            name: "lift_at_bvar_wkpos".to_string(),
            type_src: concat!(
                "forall (i : Nat) (c : Nat), ",
                "Eq KExpr (lift_at (KExpr.bvar i) c (Nat.succ Nat.zero)) ",
                "(KExpr.bvar (wkpos i c))",
            )
            .to_string(),
            value_src: Some(
                "fun (i : Nat) (c : Nat) => lift_bvar_wkpos_rec i (Nat.sub c i)".to_string(),
            ),
            is_axiom: false,
            description: "lift_at on a bvar computes to wkpos (mirror lift_at_bvar_wkpos). \
                          DerivedProved: lift_bvar_wkpos_rec at the shared discriminant c - i \
                          (lift_at/wkpos unfold definitionally). Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "wkpos".to_string(),
                "lift_bvar_wkpos_rec".to_string(),
                "lift_at".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_exchange_zero: the (cutoff-0, unit-amount) instance of the
        // in-tree cross-cutoff lift exchange, with the Nat.add clutter
        // transported away once so the weakening tower can consume it plainly.
        self.add_definition(SpecDefinition {
            name: "lift_exchange_zero".to_string(),
            type_src: concat!(
                "forall (X : KExpr) (c : Nat), Eq KExpr ",
                "(lift_at (lift_at X c (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at (lift_at X Nat.zero (Nat.succ Nat.zero)) (Nat.succ c) ",
                "(Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (X : KExpr) (c : Nat) => ",
                    "Eq.subst Nat ",
                    "(fun (z : Nat) => Eq KExpr ",
                    "(lift_at (lift_at X c (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at X Nat.zero (Nat.succ Nat.zero)) z (Nat.succ Nat.zero))) ",
                    "(Nat.add Nat.zero (Nat.add (Nat.succ Nat.zero) c)) (Nat.succ c) ",
                    // t2 : add 0 (add 1 c) = succ c
                    "(Eq.trans Nat ",
                    "(Nat.add Nat.zero (Nat.add (Nat.succ Nat.zero) c)) ",
                    "(Nat.add (Nat.succ Nat.zero) c) ",
                    "(Nat.succ c) ",
                    "(nat_zero_add (Nat.add (Nat.succ Nat.zero) c)) ",
                    "(Eq.trans Nat ",
                    "(Nat.add (Nat.succ Nat.zero) c) ",
                    "(Nat.succ (Nat.add Nat.zero c)) ",
                    "(Nat.succ c) ",
                    "(nat_succ_add Nat.zero c) ",
                    "(Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) ",
                    "(Nat.add Nat.zero c) c (nat_zero_add c)))) ",
                    // h1 : exchange with the LHS cutoff already rewritten to c
                    "(Eq.subst Nat ",
                    "(fun (z : Nat) => Eq KExpr ",
                    "(lift_at (lift_at X z (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) ",
                    "(lift_at (lift_at X Nat.zero (Nat.succ Nat.zero)) ",
                    "(Nat.add Nat.zero (Nat.add (Nat.succ Nat.zero) c)) (Nat.succ Nat.zero))) ",
                    "(Nat.add Nat.zero c) c (nat_zero_add c) ",
                    "(lift_at_lift_at_exchange X Nat.zero c (Nat.succ Nat.zero) ",
                    "(Nat.succ Nat.zero)))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Unit-lift exchange at cutoff 0: lift(lift(X,c,1),0,1) = \
                          lift(lift(X,0,1),succ c,1) (mirror lift_lift_exchange instance). \
                          DerivedProved: lift_at_lift_at_exchange + nat_zero_add/nat_succ_add \
                          transports. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_at_lift_at_exchange".to_string(),
                "nat_zero_add".to_string(),
                "nat_succ_add".to_string(),
                "Eq.subst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lift_instantiate_zero: the depth-0 unit instance of
        // lift_instantiate_swap (mirror lift_instantiate).
        self.add_definition(SpecDefinition {
            name: "lift_instantiate_zero".to_string(),
            type_src: concat!(
                "forall (B : KExpr) (a : KExpr) (c : Nat), Eq KExpr ",
                "(lift_at (instantiate B a) c (Nat.succ Nat.zero)) ",
                "(instantiate (lift_at B (Nat.succ c) (Nat.succ Nat.zero)) ",
                "(lift_at a c (Nat.succ Nat.zero)))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (B : KExpr) (a : KExpr) (c : Nat) => ",
                    "Eq.subst Nat ",
                    "(fun (z : Nat) => Eq KExpr ",
                    "(lift_at (instantiate B a) z (Nat.succ Nat.zero)) ",
                    "(instantiate (lift_at B (Nat.succ z) (Nat.succ Nat.zero)) ",
                    "(lift_at a c (Nat.succ Nat.zero)))) ",
                    "(Nat.add Nat.zero c) c (nat_zero_add c) ",
                    "(lift_instantiate_swap B a Nat.zero c (Nat.succ Nat.zero))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Lifting commutes with instantiation at depth 0 (mirror \
                          lift_instantiate). DerivedProved: lift_instantiate_swap at d=0 with the \
                          Nat.add 0 c transported away. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_instantiate_swap".to_string(),
                "nat_zero_add".to_string(),
                "Eq.subst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The weakening tower: `CtxWk`, `ctx_wk_lookup`, `weaken_gen`, `weaken1`.
    fn add_srb_weakening(&mut self) -> Result<(), SpecError> {
        // CtxWk C c G G2: G2 is G with C inserted at cutoff c (entries above
        // the cut have their stored types lifted). Mirror CtxWk.
        self.add_inductive(
            concat!(
                "inductive CtxWk (C : KExpr) : Nat -> ListType KExpr -> ListType KExpr -> Type\n",
                "| zero : forall (G : ListType KExpr), ",
                "CtxWk C Nat.zero G (ListType.cons KExpr C G)\n",
                "| succ : forall (c : Nat) (A : KExpr) (G : ListType KExpr) ",
                "(G2 : ListType KExpr), CtxWk C c G G2 -> ",
                "CtxWk C (Nat.succ c) (ListType.cons KExpr A G) ",
                "(ListType.cons KExpr (lift_at A c (Nat.succ Nat.zero)) G2)"
            ),
            "Context weakening relation (mirror CtxWk): G2 is G with entry C inserted at cutoff \
             c; entries above the cut carry lifted types. Subject-reduction bundle.",
        )?;

        // ctx_wk_lookup (CPS): lookup transports across CtxWk with the
        // corresponding type lift.
        self.add_definition(SpecDefinition {
            name: "ctx_wk_lookup".to_string(),
            type_src: concat!(
                "forall (C : KExpr) (c : Nat) (G : ListType KExpr) (G2 : ListType KExpr), ",
                "CtxWk C c G G2 -> ",
                "forall (i : Nat) (A : KExpr), ",
                "Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> ",
                "forall (R : Type), ",
                "(forall (A2 : KExpr), ",
                "Eq (OptionType KExpr) (ctx_lookup G2 (wkpos i c)) (OptionType.some KExpr A2) -> ",
                "Eq KExpr (lift_at A2 Nat.zero (Nat.succ (wkpos i c))) ",
                "(lift_at (lift_at A Nat.zero (Nat.succ i)) c (Nat.succ Nat.zero)) -> R) ",
                "-> R",
            )
            .to_string(),
            value_src: Some(ctx_wk_lookup_value()),
            is_axiom: false,
            description: "Lookup transports across CtxWk with the matching type lift (mirror \
                          ctx_wk_lookup, CPS form). DerivedProved via CtxWk.rec with an inner \
                          Nat.rec index split; index arithmetic via wkpos_zero/wkpos_succ_succ, \
                          lift algebra via lift_at_compose/lift_exchange_zero. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxWk".to_string(),
                "CtxWk.rec".to_string(),
                "wkpos".to_string(),
                "wkpos_zero".to_string(),
                "wkpos_succ_succ".to_string(),
                "lift_at_compose".to_string(),
                "lift_exchange_zero".to_string(),
                "ctx_lookup".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // weaken_gen: generalized weakening — insertion at an arbitrary cutoff.
        self.add_definition(SpecDefinition {
            name: "weaken_gen".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "forall (C : KExpr) (G : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> ",
                "forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> ",
                "TypingCtxConv tenv G2 (lift_at e c (Nat.succ Nat.zero)) ",
                "(lift_at T c (Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(weaken_gen_value()),
            is_axiom: false,
            description: "Generalized weakening over TypingCtxConv: insertion at an arbitrary \
                          cutoff (mirror weaken_gen). DerivedProved via TypingCtxConv.rec; var \
                          arm via ctx_wk_lookup + lift_at_bvar_wkpos, app and let_ arms via \
                          lift_instantiate_zero, const arm via the carried tenv_lift_closed \
                          field, conv arm via def_eq_respects_lift_at_gen (carrying \
                          RedEnvFaithful the_red_env). Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "ctx_wk_lookup".to_string(),
                "lift_at_bvar_wkpos".to_string(),
                "lift_instantiate_zero".to_string(),
                "def_eq_respects_lift_at_gen".to_string(),
                "tec_tenv_lift_closed".to_string(),
                "CtxWk.succ".to_string(),
                "RedEnvFaithful".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // weaken1: weakening by one entry at the context head.
        self.add_definition(SpecDefinition {
            name: "weaken1".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> ",
                "forall (C : KExpr), ",
                "TypingCtxConv tenv (ListType.cons KExpr C G) ",
                "(lift_at e Nat.zero (Nat.succ Nat.zero)) ",
                "(lift_at T Nat.zero (Nat.succ Nat.zero))",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) ",
                    "(W : TypingEnvCoherent tenv) ",
                    "(G : ListType KExpr) (e : KExpr) (T : KExpr) ",
                    "(h : TypingCtxConv tenv G e T) (C : KExpr) => ",
                    "weaken_gen tenv hf W C G e T h Nat.zero ",
                    "(ListType.cons KExpr C G) (CtxWk.zero C G)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Weakening by one entry at the context head (mirror weaken1): \
                          weaken_gen at cutoff 0 via CtxWk.zero. DerivedProved. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "weaken_gen".to_string(),
                "CtxWk.zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// def_eq_psubst + the SubstTyping tower + substitution_general/_typing_ctx.
    fn add_srb_substitution(&mut self) -> Result<(), SpecError> {
        // def_eq_psubst: DefEq is stable under parallel substitution — the
        // psubst generalization of def_eq_respects_subst_at. The delta/iota
        // arms are exactly the carried TypingEnvCoherent fields 3/4 (passed
        // here as bare hypotheses so this lemma does not depend on the
        // interface inductive); the beta arm is psubst_instantiate.
        self.add_definition(SpecDefinition {
            name: "def_eq_psubst".to_string(),
            type_src: concat!(
                "forall ",
                "(hdp : forall (e : KExpr) (e' : KExpr), delta_reduces e e' -> ",
                "forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')) ",
                "(hip : forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> ",
                "forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')) ",
                "(A : KExpr) (B : KExpr), DefEq A B -> ",
                "forall (s : Nat -> KExpr), DefEq (psubst s A) (psubst s B)",
            )
            .to_string(),
            value_src: Some(def_eq_psubst_value()),
            is_axiom: false,
            description: "DefEq respects parallel substitution (mirror def_eq_psubst): the psubst \
                          generalization of def_eq_respects_subst_at. By DefEq.rec; beta AND zeta \
                          via psubst_instantiate (the zeta minor is the beta minor's exact shape \
                          on the genuine let_ constructor); let_cong is the ternary congruence \
                          with the body IH at (up s); delta/iota are the carried psubst-stability \
                          hypotheses (TypingEnvCoherent fields 3/4). DerivedProved, zero \
                          axiom_deps. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefEq.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.zeta".to_string(),
                "DefEq.let_cong".to_string(),
                "DefEq.proj_cong".to_string(),
                "psubst".to_string(),
                "psubst_instantiate".to_string(),
                "psubst_proj".to_string(),
                "Eq.substType".to_string(),
                "up".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // SubstTyping: s is a well-typed substitution from source context G
        // into target context G2 (mirror SubstTyping — the psubst-general
        // device that makes the substitution induction go through).
        self.add_recursive_def(
            "def SubstTyping (tenv : Name -> OptionType KExpr) (G2 : ListType KExpr) \
             (s : Nat -> KExpr) (G : ListType KExpr) : Type := \
             forall (i : Nat) (A : KExpr), \
             Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> \
             TypingCtxConv tenv G2 (s i) (psubst s (lift_at A Nat.zero (Nat.succ i)))",
            "s is a well-typed substitution G -> G2: every variable is sent to a term of the \
             s-image of the type the var rule assigns it (mirror SubstTyping). \
             Subject-reduction bundle.",
        )?;

        // subst_typing_id: the identity substitution is well-typed.
        self.add_definition(SpecDefinition {
            name: "subst_typing_id".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (G : ListType KExpr), ",
                "SubstTyping tenv G idsubst G",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) (G : ListType KExpr) ",
                    "(i : Nat) (A : KExpr) ",
                    "(hA : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) => ",
                    "Eq.substType KExpr ",
                    "(fun (z : KExpr) => TypingCtxConv tenv G (KExpr.bvar i) z) ",
                    "(lift_at A Nat.zero (Nat.succ i)) ",
                    "(psubst idsubst (lift_at A Nat.zero (Nat.succ i))) ",
                    "(Eq.symm KExpr (psubst idsubst (lift_at A Nat.zero (Nat.succ i))) ",
                    "(lift_at A Nat.zero (Nat.succ i)) ",
                    "(psubst_id (lift_at A Nat.zero (Nat.succ i)))) ",
                    "(TypingCtxConv.var tenv G i A hA)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "The identity substitution is well-typed (mirror subst_typing_id): the \
                          var rule + psubst_id transport. DerivedProved. Subject-reduction \
                          bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "SubstTyping".to_string(),
                "idsubst".to_string(),
                "psubst_id".to_string(),
                "TypingCtxConv.var".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subst_typing_up: extension of a well-typed substitution under a
        // binder (the key binder-case lemma; consumes weaken1).
        self.add_definition(SpecDefinition {
            name: "subst_typing_up".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "forall (G : ListType KExpr) (G2 : ListType KExpr) (s : Nat -> KExpr), ",
                "SubstTyping tenv G2 s G -> ",
                "forall (A : KExpr), ",
                "SubstTyping tenv (ListType.cons KExpr (psubst s A) G2) (up s) ",
                "(ListType.cons KExpr A G)",
            )
            .to_string(),
            value_src: Some(subst_typing_up_value()),
            is_axiom: false,
            description: "Extension of a well-typed substitution under a binder (mirror \
                          subst_typing_up): index 0 via the var rule + psubst_up_lift, index j+1 \
                          via weaken1 + lift_at_compose + psubst_up_lift. DerivedProved. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "SubstTyping".to_string(),
                "weaken1".to_string(),
                "psubst_up_lift".to_string(),
                "lift_at_compose".to_string(),
                "option_some_inj".to_string(),
                "TypingCtxConv.var".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subst_typing_scons: cons-extension by a well-typed term.
        self.add_definition(SpecDefinition {
            name: "subst_typing_scons".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) ",
                "(G : ListType KExpr) (G2 : ListType KExpr) (s : Nat -> KExpr) ",
                "(a : KExpr) (A : KExpr), ",
                "SubstTyping tenv G2 s G -> ",
                "TypingCtxConv tenv G2 a (psubst s A) -> ",
                "SubstTyping tenv G2 (scons a s) (ListType.cons KExpr A G)",
            )
            .to_string(),
            value_src: Some(subst_typing_scons_value()),
            is_axiom: false,
            description: "Cons-extension of a well-typed substitution by a well-typed term \
                          (mirror subst_typing_scons): index 0 via psubst_cancel, index j+1 via \
                          psubst_cancel + lift_at_compose. DerivedProved. Subject-reduction \
                          bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "SubstTyping".to_string(),
                "psubst_cancel".to_string(),
                "lift_at_compose".to_string(),
                "option_some_inj".to_string(),
                "scons".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // substitution_general: THE substitution lemma, psubst form.
        self.add_definition(SpecDefinition {
            name: "substitution_general".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "forall (G : ListType KExpr) (b : KExpr) (B : KExpr), ",
                "TypingCtxConv tenv G b B -> ",
                "forall (G2 : ListType KExpr) (s : Nat -> KExpr), ",
                "SubstTyping tenv G2 s G -> ",
                "TypingCtxConv tenv G2 (psubst s b) (psubst s B)",
            )
            .to_string(),
            value_src: Some(substitution_general_value()),
            is_axiom: false,
            description: "THE SUBSTITUTION LEMMA in parallel-substitution form (mirror \
                          substitution_general) — the real content of subject reduction's beta \
                          AND zeta cases. By TypingCtxConv.rec generalizing the target context \
                          and substitution; binder arms (pi/lam/let_) via subst_typing_up, app \
                          and let_ conclusions via psubst_instantiate, const via the carried \
                          tenv_psubst_closed field, conv via def_eq_psubst. DerivedProved. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "SubstTyping".to_string(),
                "subst_typing_up".to_string(),
                "psubst_instantiate".to_string(),
                "def_eq_psubst".to_string(),
                "tec_tenv_psubst_closed".to_string(),
                "tec_delta_psubst".to_string(),
                "tec_iota_psubst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // substitution_typing_ctx: the classic single-substitution instance.
        self.add_definition(SpecDefinition {
            name: "substitution_typing_ctx".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (a : KExpr), ",
                "TypingCtxConv tenv (ListType.cons KExpr A G) b B -> ",
                "TypingCtxConv tenv G a A -> ",
                "TypingCtxConv tenv G (instantiate b a) (instantiate B a)",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) ",
                    "(W : TypingEnvCoherent tenv) ",
                    "(G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (a : KExpr) ",
                    "(hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) ",
                    "(ha : TypingCtxConv tenv G a A) => ",
                    "Eq.substType KExpr ",
                    "(fun (z : KExpr) => TypingCtxConv tenv G z (instantiate B a)) ",
                    "(psubst (scons a idsubst) b) (instantiate b a) ",
                    "(Eq.symm KExpr (instantiate b a) (psubst (scons a idsubst) b) ",
                    "(instantiate_eq_psubst b a)) ",
                    "(Eq.substType KExpr ",
                    "(fun (z : KExpr) => TypingCtxConv tenv G (psubst (scons a idsubst) b) z) ",
                    "(psubst (scons a idsubst) B) (instantiate B a) ",
                    "(Eq.symm KExpr (instantiate B a) (psubst (scons a idsubst) B) ",
                    "(instantiate_eq_psubst B a)) ",
                    "(substitution_general tenv hf W (ListType.cons KExpr A G) b B hb G ",
                    "(scons a idsubst) ",
                    "(subst_typing_scons tenv G G idsubst a A (subst_typing_id tenv G) ",
                    "(Eq.substType KExpr ",
                    "(fun (z : KExpr) => TypingCtxConv tenv G a z) ",
                    "A (psubst idsubst A) ",
                    "(Eq.symm KExpr (psubst idsubst A) A (psubst_id A)) ",
                    "ha))))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "THE SUBSTITUTION LEMMA, classic single-substitution instance (mirror \
                          substitution_typing): substitution_general at scons a idsubst, \
                          transported through instantiate_eq_psubst. DerivedProved. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "substitution_general".to_string(),
                "subst_typing_scons".to_string(),
                "subst_typing_id".to_string(),
                "instantiate_eq_psubst".to_string(),
                "psubst_id".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// CtxDefEq + ctx_def_eq_refl + ctx_def_eq_lookup + ctx_conv.
    fn add_srb_ctx_conv(&mut self) -> Result<(), SpecError> {
        // CtxDefEq: pointwise DefEq of contexts (mirror CtxDefEq).
        self.add_inductive(
            concat!(
                "inductive CtxDefEq : ListType KExpr -> ListType KExpr -> Type\n",
                "| nil : CtxDefEq (ListType.nil KExpr) (ListType.nil KExpr)\n",
                "| cons : forall (A : KExpr) (A2 : KExpr) (G : ListType KExpr) ",
                "(G2 : ListType KExpr), DefEq A A2 -> CtxDefEq G G2 -> ",
                "CtxDefEq (ListType.cons KExpr A G) (ListType.cons KExpr A2 G2)"
            ),
            "Pointwise DefEq of typing contexts (mirror CtxDefEq) — the transport relation for \
             the congruence arms that reduce a binder's domain annotation. Subject-reduction \
             bundle.",
        )?;

        // ctx_def_eq_refl.
        self.add_definition(SpecDefinition {
            name: "ctx_def_eq_refl".to_string(),
            type_src: "forall (G : ListType KExpr), CtxDefEq G G".to_string(),
            value_src: Some(
                concat!(
                    "fun (G : ListType KExpr) => ListType.rec KExpr ",
                    "(fun (g : ListType KExpr) => CtxDefEq g g) ",
                    "CtxDefEq.nil ",
                    "(fun (a : KExpr) (rest : ListType KExpr) (ihr : CtxDefEq rest rest) => ",
                    "CtxDefEq.cons a a rest rest (DefEq.refl a) ihr) ",
                    "G",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "CtxDefEq is reflexive (mirror ctx_def_eq_refl). DerivedProved via \
                          ListType.rec. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxDefEq".to_string(),
                "DefEq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_def_eq_lookup (CPS): lookup transports across CtxDefEq.
        self.add_definition(SpecDefinition {
            name: "ctx_def_eq_lookup".to_string(),
            type_src: concat!(
                "forall (G : ListType KExpr) (G2 : ListType KExpr), CtxDefEq G G2 -> ",
                "forall (i : Nat) (A : KExpr), ",
                "Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> ",
                "forall (R : Type), ",
                "(forall (A2 : KExpr), ",
                "Eq (OptionType KExpr) (ctx_lookup G2 i) (OptionType.some KExpr A2) -> ",
                "DefEq A A2 -> R) -> R",
            )
            .to_string(),
            value_src: Some(ctx_def_eq_lookup_value()),
            is_axiom: false,
            description: "Lookup transports across pointwise-DefEq contexts (mirror \
                          ctx_def_eq_lookup, CPS form). DerivedProved via CtxDefEq.rec with an \
                          inner Nat.rec index split. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "CtxDefEq".to_string(),
                "CtxDefEq.rec".to_string(),
                "option_some_inj".to_string(),
                "option_none_ne_some_type".to_string(),
                "ctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_conv: typing transports across pointwise-DefEq contexts.
        self.add_definition(SpecDefinition {
            name: "ctx_conv".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "forall (G : ListType KExpr) (G2 : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> CtxDefEq G G2 -> ",
                "TypingCtxConv tenv G2 e T",
            )
            .to_string(),
            value_src: Some(ctx_conv_value()),
            is_axiom: false,
            description: "CONTEXT CONVERSION (mirror ctx_conv): typing transports across \
                          pointwise-DefEq contexts. By TypingCtxConv.rec generalizing the target \
                          context; var arm via ctx_def_eq_lookup + def_eq_respects_lift_at_gen \
                          (carrying RedEnvFaithful the_red_env); binder arms extend the CtxDefEq \
                          with DefEq.refl. DerivedProved. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "CtxDefEq".to_string(),
                "CtxDefEq.cons".to_string(),
                "ctx_def_eq_lookup".to_string(),
                "ctx_def_eq_refl".to_string(),
                "def_eq_respects_lift_at_gen".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// CPS generation (inversion) lemmas over TypingCtxConv.
    ///
    /// The const-headed discrimination lemmas (`const_ne_app` / `const_ne_lam`
    /// / `const_ne_pi`) are REUSED from `par_reduces_d_diamond`'s
    /// `add_kexpr_bvar_const_discriminators` (an earlier stage) — same
    /// signatures the mirror needs.
    fn add_srb_generation(&mut self) -> Result<(), SpecError> {
        // KExpr field projectors (with defaults) — turn constructor-equations
        // into field equations via Eq.cong (the injectivity device).
        for (name, arms, doc) in [
            (
                "srb_app_fn",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (f : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => f) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "app function-position projector",
            ),
            (
                "srb_app_arg",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (_ : KExpr) (a : KExpr) (_ : KExpr) (_ : KExpr) => a) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "app argument-position projector",
            ),
            (
                "srb_lam_ty",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (ty : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => ty) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "lam domain-annotation projector",
            ),
            (
                "srb_lam_body",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) => b) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "lam body projector",
            ),
            (
                "srb_pi_dom",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (dom : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => dom) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "pi domain projector",
            ),
            (
                "srb_pi_cod",
                "(fun (_ : Level) => d) (fun (_ : Nat) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : KExpr) (cod : KExpr) (_ : KExpr) (_ : KExpr) => cod) \
                 (fun (_ : Name) (_ : ListType Level) => d) \
                 (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => d) \
                 (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => d) (fun (_ : Nat) => d)",
                "pi codomain projector",
            ),
        ] {
            self.add_recursive_def(
                &format!(
                    "def {name} (e : KExpr) (d : KExpr) : KExpr := \
                     KExpr.rec (fun (_ : KExpr) => KExpr) {arms} e"
                ),
                &format!("{doc} (default d off-shape). Subject-reduction bundle."),
            )?;
        }

        // ctx_app_gen: generation for app (CPS, in-tree typing_app_gen style).
        self.add_definition(SpecDefinition {
            name: "ctx_app_gen".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) ",
                "(G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G (KExpr.app f a) T -> ",
                "forall (R : Type), ",
                "(forall (A : KExpr) (B : KExpr), ",
                "TypingCtxConv tenv G f (KExpr.pi A B) -> ",
                "TypingCtxConv tenv G a A -> ",
                "DefEq (instantiate B a) T -> R) -> R",
            )
            .to_string(),
            value_src: Some(ctx_app_gen_value()),
            is_axiom: false,
            description: "Generation (inversion) for app over TypingCtxConv (mirror app_gen, \
                          CPS form): peels the trailing conv chain, composing the DefEq by \
                          trans. DerivedProved via TypingCtxConv.rec with an Eq-keyed motive; \
                          non-app arms discriminate, the app arm splits the constructor \
                          equation with the srb field projectors. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "sort_ne_app".to_string(),
                "app_ne_bvar".to_string(),
                "pi_ne_app".to_string(),
                "lam_ne_app".to_string(),
                "const_ne_app".to_string(),
                "let_ne_app".to_string(),
                "srb_app_fn".to_string(),
                "srb_app_arg".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_lam_gen: generation for lam.
        self.add_definition(SpecDefinition {
            name: "ctx_lam_gen".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) ",
                "(G : ListType KExpr) (A : KExpr) (b : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G (KExpr.lam A b) T -> ",
                "forall (R : Type), ",
                "(forall (B : KExpr) (u : Level), ",
                "TypingCtxConv tenv G A (KExpr.sort u) -> ",
                "TypingCtxConv tenv (ListType.cons KExpr A G) b B -> ",
                "DefEq (KExpr.pi A B) T -> R) -> R",
            )
            .to_string(),
            value_src: Some(ctx_lam_gen_value()),
            is_axiom: false,
            description: "Generation (inversion) for lam over TypingCtxConv (mirror lam_gen, \
                          CPS form). DerivedProved via TypingCtxConv.rec with an Eq-keyed \
                          motive. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "sort_ne_lam".to_string(),
                "lam_ne_bvar".to_string(),
                "pi_ne_lam".to_string(),
                "app_ne_lam".to_string(),
                "const_ne_lam".to_string(),
                "let_ne_lam".to_string(),
                "srb_lam_ty".to_string(),
                "srb_lam_body".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_pi_gen: generation for pi.
        self.add_definition(SpecDefinition {
            name: "ctx_pi_gen".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) ",
                "(G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G (KExpr.pi A B) T -> ",
                "forall (R : Type), ",
                "(forall (n : Level) (m : Level), ",
                "TypingCtxConv tenv G A (KExpr.sort n) -> ",
                "TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m) -> ",
                "DefEq (KExpr.sort (Level.imax n m)) T -> R) -> R",
            )
            .to_string(),
            value_src: Some(ctx_pi_gen_value()),
            is_axiom: false,
            description: "Generation (inversion) for pi over TypingCtxConv (mirror pi_gen, CPS \
                          form). DerivedProved via TypingCtxConv.rec with an Eq-keyed motive. \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "sort_ne_pi".to_string(),
                "pi_ne_bvar".to_string(),
                "lam_ne_pi".to_string(),
                "app_ne_pi".to_string(),
                "const_ne_pi".to_string(),
                "let_ne_pi".to_string(),
                "srb_pi_dom".to_string(),
                "srb_pi_cod".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // srb sort/bvar/const vs let_ no-confusion (let promotion, task #28).
        // The B3 lane registers only the app/lam/pi pairings; ctx_let_gen's
        // Eq-keyed inversion additionally needs the sort/bvar/const heads.
        // Same Eq.substType + inline-discriminator + Empty.rec pattern.
        for (name, binders, lhs, desc) in [
            (
                "srb_sort_ne_let",
                "(n : Level) (ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.sort n)",
                "Sort ≠ Let_ discrimination (srb lane, let promotion, task #28).",
            ),
            (
                "srb_bvar_ne_let",
                "(i : Nat) (ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.bvar i)",
                "Bvar ≠ Let_ discrimination (srb lane, let promotion, task #28).",
            ),
            (
                "srb_const_ne_let",
                "(n : Name) (us : ListType Level) (ty : KExpr) (val : KExpr) (body : KExpr)",
                "(KExpr.const n us)",
                "Const ≠ Let_ discrimination (srb lane, let promotion, task #28).",
            ),
        ] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall {binders} (R : Type), \
                     Eq KExpr {lhs} (KExpr.let_ ty val body) -> R"
                ),
                value_src: Some(format!(
                    "fun {binders} (R : Type) \
                     (h : Eq KExpr {lhs} (KExpr.let_ ty val body)) => \
                     Empty.rec (fun (_ : Empty) => R) \
                     (Eq.substType KExpr {discr} {lhs} (KExpr.let_ ty val body) h Nat.zero)",
                    discr = SRB_KEXPR_NOT_LET,
                )),
                is_axiom: false,
                description: format!("{desc} Subject-reduction bundle."),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "KExpr.rec".to_string(),
                    "Eq.substType".to_string(),
                    "Empty.rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // ctx_let_gen: generation for the genuine let_ (mirror let_gen, CPS
        // form) — the let-increment analogue of ctx_app_gen, consumed by the
        // zeta and let-congruence arms of subject reduction.
        self.add_definition(SpecDefinition {
            name: "ctx_let_gen".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) ",
                "(G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G (KExpr.let_ ty v b) T -> ",
                "forall (R : Type), ",
                "(forall (Bg : KExpr) (ug : Level), ",
                "TypingCtxConv tenv G ty (KExpr.sort ug) -> ",
                "TypingCtxConv tenv G v ty -> ",
                "TypingCtxConv tenv (ListType.cons KExpr ty G) b Bg -> ",
                "DefEq (instantiate Bg v) T -> R) -> R",
            )
            .to_string(),
            value_src: Some(ctx_let_gen_value()),
            is_axiom: false,
            description: "Generation (inversion) for the genuine let_ over TypingCtxConv \
                          (mirror let_gen, CPS form): peels the trailing conv chain, composing \
                          the DefEq by trans — only let_ and conv can conclude a let_. \
                          DerivedProved via TypingCtxConv.rec with an Eq-keyed motive; non-let \
                          arms discriminate (let_ne_*/srb_*_ne_let), the let_ arm splits the \
                          constructor equation with let_inj_fst/snd/thd. Consumed by the zeta \
                          and let-congruence preservation arms. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "srb_sort_ne_let".to_string(),
                "srb_bvar_ne_let".to_string(),
                "srb_const_ne_let".to_string(),
                "pi_ne_let".to_string(),
                "lam_ne_let".to_string(),
                "app_ne_let".to_string(),
                "let_inj_fst".to_string(),
                "let_inj_snd".to_string(),
                "let_inj_thd".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// delta/beta preservation + the subject_reduction_ctx dispatcher.
    fn add_srb_preservation(&mut self) -> Result<(), SpecError> {
        // opt_case_type: Type-valued CPS case split on an OptionType value
        // (the in-tree opt_bind_some_inv is Prop-bounded; preservation needs a
        // Type conclusion).
        self.add_definition(SpecDefinition {
            name: "opt_case_type".to_string(),
            type_src: concat!(
                "forall (T : Type) (o : OptionType T) (C : Type), ",
                "(Eq (OptionType T) o (OptionType.none T) -> C) -> ",
                "(forall (x : T), Eq (OptionType T) o (OptionType.some T x) -> C) -> C",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (T : Type) (o : OptionType T) (C : Type) => ",
                    "OptionType.rec T ",
                    "(fun (o2 : OptionType T) => ",
                    "(Eq (OptionType T) o2 (OptionType.none T) -> C) -> ",
                    "(forall (x : T), Eq (OptionType T) o2 (OptionType.some T x) -> C) -> C) ",
                    "(fun (kn : Eq (OptionType T) (OptionType.none T) (OptionType.none T) -> C) ",
                    "(_ks : forall (x : T), ",
                    "Eq (OptionType T) (OptionType.none T) (OptionType.some T x) -> C) => ",
                    "kn (Eq.refl (OptionType T) (OptionType.none T))) ",
                    "(fun (x : T) ",
                    "(_kn : Eq (OptionType T) (OptionType.some T x) (OptionType.none T) -> C) ",
                    "(ks : forall (y : T), ",
                    "Eq (OptionType T) (OptionType.some T x) (OptionType.some T y) -> C) => ",
                    "ks x (Eq.refl (OptionType T) (OptionType.some T x))) ",
                    "o",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Type-valued CPS case split on an OptionType (with the equation \
                          witnesses). DerivedProved via OptionType.rec. Subject-reduction \
                          bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["OptionType.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_preserves_typing_ctx: the delta arm, PROVED from the carried
        // defval_typed field + the computational delta_reduct decomposition.
        self.add_definition(SpecDefinition {
            name: "delta_preserves_typing_ctx".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "TypingEnvCoherent tenv -> ",
                "forall (G : ListType KExpr) (e : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> ",
                "forall (e' : KExpr), delta_reduces e e' -> ",
                "TypingCtxConv tenv G e' T",
            )
            .to_string(),
            value_src: Some(delta_preserves_typing_ctx_value()),
            is_axiom: false,
            description: "Delta preservation over TypingCtxConv (mirror delta_preserves_typing), \
                          PROVED from the carried defval_typed field: by TypingCtxConv.rec with \
                          motive over the delta_step graph; var/sort/pi/lam/let_ heads are absurd \
                          (delta_reduct computes to none — a let is its own spine head, never a \
                          const head), app decomposes via \
                          delta_step_app_inv_type, const resolves the lookup via opt_case_type + \
                          tec_defval_typed. Incoming delta_reduces converts via \
                          delta_reduces_to_step. DerivedProved. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "delta_reduces_to_step".to_string(),
                "delta_step_app_inv_type".to_string(),
                "opt_case_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "option_some_inj".to_string(),
                "tec_defval_typed".to_string(),
                "the_red_env".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // srb_beta_redex_preserves: the typed beta-redex contraction (the HARD
        // case — the beta arm; zeta has its own SIMPLER path via ctx_let_gen +
        // substitution_typing_ctx, no pi-injectivity).
        self.add_definition(SpecDefinition {
            name: "srb_beta_redex_preserves".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "DefEnvWellformed the_red_env -> ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "forall (A : KExpr) (b : KExpr) (a : KExpr) ",
                "(G : ListType KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G (KExpr.app (KExpr.lam A b) a) T -> ",
                "TypingCtxConv tenv G (instantiate b a) T",
            )
            .to_string(),
            value_src: Some(srb_beta_redex_preserves_value()),
            is_axiom: false,
            description: "Typed beta-redex contraction preserves TypingCtxConv typing (the beta \
                          arm of subject reduction): invert with \
                          ctx_app_gen + ctx_lam_gen, bridge the lam domain to the expected \
                          domain through pi_injectivity_def_eq_dom (confluence-backed, carrying \
                          RedEnvFaithful the_red_env), substitute via substitution_typing_ctx, \
                          re-establish the type through pi_injectivity_def_eq_cod + \
                          def_eq_respects_subst_at (carrying DefEnvWellformed/RecEnvWellformed). \
                          DerivedProved. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ctx_app_gen".to_string(),
                "ctx_lam_gen".to_string(),
                "pi_injectivity_def_eq_dom".to_string(),
                "pi_injectivity_def_eq_cod".to_string(),
                "substitution_typing_ctx".to_string(),
                "def_eq_respects_subst_at".to_string(),
                "TypingCtxConv.conv".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ctx_proj_absurd: a proj-headed subject is not typeable under
        // TypingCtxConv (no proj rule) — discharges the proj congruence arm of
        // beta_reduces_preserves_typing_ctx now that proj is a KExpr constructor.
        self.add_definition(SpecDefinition {
            name: "ctx_proj_absurd".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr) (s : Name) (i : Nat) (sub : KExpr) ",
                "(G : ListType KExpr) (T : KExpr) (C : Type), ",
                "TypingCtxConv tenv G (KExpr.proj s i sub) T -> C"
            )
            .to_string(),
            value_src: Some(ctx_proj_absurd_value()),
            is_axiom: false,
            description: concat!(
                "Inversion: a proj-headed term is not typeable under TypingCtxConv ",
                "(no proj rule), so TypingCtxConv tenv G (proj s i sub) T eliminates into ",
                "any C. By TypingCtxConv.rec with an Eq-keyed motive; the rigid-head arms ",
                "refute via the not-proj discriminator + Empty.rec, conv arm forwards the IH. ",
                "Dual of typing_proj_absurd for the context-aware judgment. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypingCtxConv.rec".to_string(),
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "Empty.rec".to_string(),
                "ctx_lookup".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_reduces_preserves_typing_ctx: subject reduction along the full
        // 14-arm beta_reduces (mirror beta_reduces_preserves_typing; zeta is
        // the substitution lemma's second consumer).
        self.add_definition(SpecDefinition {
            name: "beta_reduces_preserves_typing_ctx".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "DefEnvWellformed the_red_env -> ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "forall (e : KExpr) (e' : KExpr), beta_reduces e e' -> ",
                "forall (G : ListType KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> TypingCtxConv tenv G e' T",
            )
            .to_string(),
            value_src: Some(beta_reduces_preserves_typing_ctx_value()),
            is_axiom: false,
            description: "SUBJECT REDUCTION along the full 14-arm beta_reduces over the \
                          context-indexed TypingCtxConv (mirror \
                          beta_reduces_preserves_typing): by beta_reduces.rec — beta via \
                          srb_beta_redex_preserves; zeta = THE textbook second consumer of the \
                          substitution lemma (ctx_let_gen inversion + substitution_typing_ctx + \
                          one conv — NO pi-injectivity); congruence arms (incl. \
                          let_ty/let_val/let_body) invert with the ctx generation lemmas + \
                          rebuild + conv (domain-reducing arms transport the binder context via \
                          ctx_conv over beta_reduces_preserves_def_eq, the argument-position \
                          let_val arm bridges the dependent type via \
                          def_eq_instantiate_arg_congr), iota arm is the carried iota_typed \
                          field. Hypotheses: RedEnvFaithful + TypingEnvCoherent + \
                          DefEnvWellformed + RecEnvWellformed the_red_env — all carried \
                          interfaces, never axioms. DerivedProved. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "beta_reduces.rec".to_string(),
                "srb_beta_redex_preserves".to_string(),
                "ctx_app_gen".to_string(),
                "ctx_lam_gen".to_string(),
                "ctx_pi_gen".to_string(),
                "ctx_let_gen".to_string(),
                "substitution_typing_ctx".to_string(),
                "ctx_conv".to_string(),
                "ctx_def_eq_refl".to_string(),
                "CtxDefEq.cons".to_string(),
                "beta_reduces_preserves_def_eq".to_string(),
                "def_eq_instantiate_arg_congr".to_string(),
                "tec_iota_typed".to_string(),
                "ctx_proj_absurd".to_string(),
                "TypingCtxConv.conv".to_string(),
                "TypingCtxConv.let_".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subject_reduction_ctx motive alias (the kernel-generated
        // whnf_step.rec is indices-first; the motive must be a named
        // reducible constant — same pattern as whnf_step_preserves_typing).
        self.add_definition_reducible(SpecDefinition {
            name: "subject_reduction_ctx_motive".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), whnf_step e e' -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (_h : whnf_step e e') => ",
                    "forall (tenv : Name -> OptionType KExpr), ",
                    "RedEnvFaithful the_red_env -> ",
                    "TypingEnvCoherent tenv -> ",
                    "DefEnvWellformed the_red_env -> ",
                    "RecEnvWellformed (red_rec the_red_env) -> ",
                    "forall (G : ListType KExpr) (T : KExpr), ",
                    "TypingCtxConv tenv G e T -> TypingCtxConv tenv G e' T",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Semireducible motive alias for the whnf_step dispatcher of the \
                          context-indexed subject reduction (whnf_step.rec is indices-first). \
                          Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step".to_string(),
                "TypingCtxConv".to_string(),
                "TypingEnvCoherent".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // subject_reduction_ctx (MAIN TARGET): TypingCtxConv is preserved by a
        // single WHNF step.
        self.add_definition(SpecDefinition {
            name: "subject_reduction_ctx".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType KExpr), ",
                "RedEnvFaithful the_red_env -> ",
                "TypingEnvCoherent tenv -> ",
                "DefEnvWellformed the_red_env -> ",
                "RecEnvWellformed (red_rec the_red_env) -> ",
                "forall (G : ListType KExpr) (e : KExpr) (e' : KExpr) (T : KExpr), ",
                "TypingCtxConv tenv G e T -> ",
                "whnf_step e e' -> ",
                "TypingCtxConv tenv G e' T",
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType KExpr) ",
                    "(hf : RedEnvFaithful the_red_env) ",
                    "(W : TypingEnvCoherent tenv) ",
                    "(wd : DefEnvWellformed the_red_env) ",
                    "(wr : RecEnvWellformed (red_rec the_red_env)) ",
                    "(G : ListType KExpr) (e : KExpr) (e' : KExpr) (T : KExpr) ",
                    "(h : TypingCtxConv tenv G e T) (hs : whnf_step e e') => ",
                    "whnf_step.rec e e' ",
                    "(subject_reduction_ctx_motive e e') ",
                    "(fun (hb : beta_reduces e e') => ",
                    "fun (tenv2 : Name -> OptionType KExpr) ",
                    "(hf2 : RedEnvFaithful the_red_env) ",
                    "(W2 : TypingEnvCoherent tenv2) ",
                    "(wd2 : DefEnvWellformed the_red_env) ",
                    "(wr2 : RecEnvWellformed (red_rec the_red_env)) ",
                    "(G2 : ListType KExpr) (T2 : KExpr) ",
                    "(h2 : TypingCtxConv tenv2 G2 e T2) => ",
                    "beta_reduces_preserves_typing_ctx tenv2 hf2 W2 wd2 wr2 e e' hb G2 T2 h2) ",
                    "(fun (hd : delta_reduces e e') => ",
                    "fun (tenv2 : Name -> OptionType KExpr) ",
                    "(_hf2 : RedEnvFaithful the_red_env) ",
                    "(W2 : TypingEnvCoherent tenv2) ",
                    "(_wd2 : DefEnvWellformed the_red_env) ",
                    "(_wr2 : RecEnvWellformed (red_rec the_red_env)) ",
                    "(G2 : ListType KExpr) (T2 : KExpr) ",
                    "(h2 : TypingCtxConv tenv2 G2 e T2) => ",
                    "delta_preserves_typing_ctx tenv2 W2 G2 e T2 h2 e' hd) ",
                    "hs tenv hf W wd wr G T h",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "SUBJECT REDUCTION (MAIN TARGET, mirror subject_reduction): \
                          TypingCtxConv typing is preserved by a single real WHNF step \
                          (beta_reduces union delta_reduces). By whnf_step.rec dispatch to \
                          beta_reduces_preserves_typing_ctx / delta_preserves_typing_ctx. All \
                          env-coherence facts are CARRIED interface hypotheses (RedEnvFaithful, \
                          TypingEnvCoherent, DefEnvWellformed, RecEnvWellformed) — zero axioms. \
                          DerivedProved. Subject-reduction bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "whnf_step.rec".to_string(),
                "subject_reduction_ctx_motive".to_string(),
                "beta_reduces_preserves_typing_ctx".to_string(),
                "delta_preserves_typing_ctx".to_string(),
                "the_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// The `ctx_def_eq_lookup` proof term: CtxDefEq.rec with an inner Nat.rec
/// index split in the cons arm.
fn ctx_def_eq_lookup_value() -> String {
    let kont = |g2: &str, i: &str, a: &str| {
        format!(
            "(forall (A2 : KExpr), \
             Eq (OptionType KExpr) (ctx_lookup {g2} {i}) (OptionType.some KExpr A2) -> \
             DefEq {a} A2 -> R)"
        )
    };
    let motive = format!(
        "(fun (G : ListType KExpr) (G2 : ListType KExpr) (_ : CtxDefEq G G2) => \
         forall (i : Nat) (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> \
         forall (R : Type), {k} -> R)",
        k = kont("G2", "i", "A")
    );
    let nil_arm = format!(
        "(fun (i : Nat) (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.nil KExpr) i) \
         (OptionType.some KExpr A)) \
         (R : Type) (_k : {k}) => \
         option_none_ne_some_type KExpr A R hlk)",
        k = kont("(ListType.nil KExpr)", "i", "A")
    );
    let cons_zero = format!(
        "(fun (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) Nat.zero) \
         (OptionType.some KExpr A)) \
         (R : Type) (k : {k}) => \
         k A02 (Eq.refl (OptionType KExpr) (OptionType.some KExpr A02)) \
         (Eq.substType KExpr (fun (X : KExpr) => DefEq X A02) A0 A \
         (option_some_inj KExpr A0 A hlk) hd))",
        k = kont("(ListType.cons KExpr A02 G2)", "Nat.zero", "A")
    );
    let cons_succ = format!(
        "(fun (j : Nat) (_ihm : forall (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) j) \
         (OptionType.some KExpr A) -> forall (R : Type), {kj} -> R) \
         (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) (Nat.succ j)) \
         (OptionType.some KExpr A)) \
         (R : Type) (k : {ks}) => \
         ihc j A hlk R k)",
        kj = kont("(ListType.cons KExpr A02 G2)", "j", "A"),
        ks = kont("(ListType.cons KExpr A02 G2)", "(Nat.succ j)", "A")
    );
    let cons_arm = format!(
        "(fun (A0 : KExpr) (A02 : KExpr) (G : ListType KExpr) (G2 : ListType KExpr) \
         (hd : DefEq A0 A02) (_hctx : CtxDefEq G G2) \
         (ihc : forall (i : Nat) (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> \
         forall (R : Type), {ki} -> R) => \
         fun (i : Nat) => Nat.rec \
         (fun (m : Nat) => forall (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) m) \
         (OptionType.some KExpr A) -> \
         forall (R : Type), {km} -> R) \
         {cons_zero} {cons_succ} i)",
        ki = kont("G2", "i", "A"),
        km = kont("(ListType.cons KExpr A02 G2)", "m", "A")
    );
    format!(
        "fun (G0 : ListType KExpr) (G20 : ListType KExpr) (hctx0 : CtxDefEq G0 G20) => \
         CtxDefEq.rec {motive} {nil_arm} {cons_arm} G0 G20 hctx0"
    )
}

/// The `ctx_conv` proof term: TypingCtxConv.rec generalizing the target
/// context over CtxDefEq.
fn ctx_conv_value() -> String {
    let motive = "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (G2 : ListType KExpr), CtxDefEq G G2 -> TypingCtxConv tenv G2 e T)";
    let var_arm = "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         ctx_def_eq_lookup G G2 hctx i A hlk \
         (TypingCtxConv tenv G2 (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))) \
         (fun (A2 : KExpr) \
         (hlk2 : Eq (OptionType KExpr) (ctx_lookup G2 i) (OptionType.some KExpr A2)) \
         (hd : DefEq A A2) => \
         TypingCtxConv.conv tenv G2 (KExpr.bvar i) \
         (lift_at A2 Nat.zero (Nat.succ i)) (lift_at A Nat.zero (Nat.succ i)) \
         (TypingCtxConv.var tenv G2 i A2 hlk2) \
         (def_eq_respects_lift_at_gen A2 A (Nat.succ i) hf (DefEq.symm A A2 hd) Nat.zero)))";
    let sort_arm = "(fun (G : ListType KExpr) (n : Level) \
         (G2 : ListType KExpr) (_hctx : CtxDefEq G G2) => TypingCtxConv.sort tenv G2 n)";
    let pi_arm = "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (ihA : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 A (KExpr.sort n)) \
         (ihB : forall (G2 : ListType KExpr), CtxDefEq (ListType.cons KExpr A G) G2 -> \
         TypingCtxConv tenv G2 B (KExpr.sort m)) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         TypingCtxConv.pi tenv G2 A B n m (ihA G2 hctx) \
         (ihB (ListType.cons KExpr A G2) \
         (CtxDefEq.cons A A G G2 (DefEq.refl A) hctx)))";
    let lam_arm = "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (ihA : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 A (KExpr.sort u)) \
         (ihb : forall (G2 : ListType KExpr), CtxDefEq (ListType.cons KExpr A G) G2 -> \
         TypingCtxConv tenv G2 b B) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         TypingCtxConv.lam tenv G2 A b B u (ihA G2 hctx) \
         (ihb (ListType.cons KExpr A G2) \
         (CtxDefEq.cons A A G G2 (DefEq.refl A) hctx)))";
    let app_arm = "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (ihf : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 f (KExpr.pi A B)) \
         (iha : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 a A) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         TypingCtxConv.app tenv G2 f a A B (ihf G2 hctx) (iha G2 hctx))";
    let const_arm = "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (G2 : ListType KExpr) (_hctx : CtxDefEq G G2) => \
         TypingCtxConv.const tenv G2 n us A hA)";
    let conv_arm = "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 e A) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         TypingCtxConv.conv tenv G2 e A B (ih1 G2 hctx) hd)";
    let let_arm = "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (ihty : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 ty (KExpr.sort u)) \
         (ihv : forall (G2 : ListType KExpr), CtxDefEq G G2 -> \
         TypingCtxConv tenv G2 v ty) \
         (ihb : forall (G2 : ListType KExpr), CtxDefEq (ListType.cons KExpr ty G) G2 -> \
         TypingCtxConv tenv G2 b B) \
         (G2 : ListType KExpr) (hctx : CtxDefEq G G2) => \
         TypingCtxConv.let_ tenv G2 ty v b B u (ihty G2 hctx) (ihv G2 hctx) \
         (ihb (ListType.cons KExpr ty G2) \
         (CtxDefEq.cons ty ty G G2 (DefEq.refl ty) hctx)))";
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (hf : RedEnvFaithful the_red_env) \
         (G0 : ListType KExpr) (G20 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) \
         (h0 : TypingCtxConv tenv G0 e0 T0) (hctx0 : CtxDefEq G0 G20) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G0 e0 T0 h0 G20 hctx0"
    )
}

/// The `ctx_app_gen` proof term: TypingCtxConv.rec with an Eq-keyed motive
/// (the in-tree typing_app_gen technique over the ctx judgment).
fn ctx_app_gen_value() -> String {
    // NOTE the kont binder names (Ag/Bg) are deliberately collision-free: the
    // T slot references arm binders (A, B, u, n, m, ...), which the
    // continuation's own binders must NOT shadow.
    let kont = |f0: &str, a0: &str, t: &str| {
        format!(
            "(forall (Ag : KExpr) (Bg : KExpr), \
             TypingCtxConv tenv G {f0} (KExpr.pi Ag Bg) -> \
             TypingCtxConv tenv G {a0} Ag -> \
             DefEq (instantiate Bg {a0}) {t} -> R)"
        )
    };
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (f0 : KExpr) (a0 : KExpr), Eq KExpr e (KExpr.app f0 a0) -> \
         forall (R : Type), {k} -> R)",
        k = kont("f0", "a0", "T")
    );
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (f0 : KExpr) (a0 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.app f0 a0)) \
         (R : Type) (_k : {k}) => \
         app_ne_bvar f0 a0 i R \
         (Eq.symm KExpr (KExpr.bvar i) (KExpr.app f0 a0) heq))",
        k = kont("f0", "a0", "(lift_at A Nat.zero (Nat.succ i))")
    );
    let sort_arm = format!(
        "(fun (G : ListType KExpr) (n : Level) \
         (f0 : KExpr) (a0 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.app f0 a0)) \
         (R : Type) (_k : {k}) => sort_ne_app n f0 a0 R heq)",
        k = kont("f0", "a0", "(KExpr.sort (Level.succ n))")
    );
    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (_ihA : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr A (KExpr.app f0 a0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihB : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr B (KExpr.app f0 a0) -> \
         forall (R : Type), {kB} -> R) \
         (f0 : KExpr) (a0 : KExpr) \
         (heq : Eq KExpr (KExpr.pi A B) (KExpr.app f0 a0)) \
         (R : Type) (_k : {kt}) => pi_ne_app A B f0 a0 R heq)",
        kA = kont_ctx_app_inner("f0", "a0", "(KExpr.sort n)", "G"),
        kB = kont_ctx_app_inner("f0", "a0", "(KExpr.sort m)", "(ListType.cons KExpr A G)"),
        kt = kont("f0", "a0", "(KExpr.sort (Level.imax n m))")
    );
    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (_ihA : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr A (KExpr.app f0 a0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihb : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr b (KExpr.app f0 a0) -> \
         forall (R : Type), {kb} -> R) \
         (f0 : KExpr) (a0 : KExpr) \
         (heq : Eq KExpr (KExpr.lam A b) (KExpr.app f0 a0)) \
         (R : Type) (_k : {kt}) => lam_ne_app A b f0 a0 R heq)",
        kA = kont_ctx_app_inner("f0", "a0", "(KExpr.sort u)", "G"),
        kb = kont_ctx_app_inner("f0", "a0", "B", "(ListType.cons KExpr A G)"),
        kt = kont("f0", "a0", "(KExpr.pi A B)")
    );
    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (hfp : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (hap : TypingCtxConv tenv G a A) \
         (_ihf : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr f (KExpr.app f0 a0) -> \
         forall (R : Type), {kf} -> R) \
         (_iha : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr a (KExpr.app f0 a0) -> \
         forall (R : Type), {ka} -> R) \
         (f0 : KExpr) (a0 : KExpr) \
         (heq : Eq KExpr (KExpr.app f a) (KExpr.app f0 a0)) \
         (R : Type) (k : {kt}) => \
         k A B \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G x (KExpr.pi A B)) f f0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_app_fn x f) \
         (KExpr.app f a) (KExpr.app f0 a0) heq) hfp) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G x A) a a0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_app_arg x a) \
         (KExpr.app f a) (KExpr.app f0 a0) heq) hap) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => DefEq (instantiate B x) (instantiate B a)) a a0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_app_arg x a) \
         (KExpr.app f a) (KExpr.app f0 a0) heq) \
         (DefEq.refl (instantiate B a))))",
        kf = kont_ctx_app_inner("f0", "a0", "(KExpr.pi A B)", "G"),
        ka = kont_ctx_app_inner("f0", "a0", "A", "G"),
        kt = kont("f0", "a0", "(instantiate B a)")
    );
    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (_hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (f0 : KExpr) (a0 : KExpr) \
         (heq : Eq KExpr (KExpr.const n us) (KExpr.app f0 a0)) \
         (R : Type) (_k : {kt}) => const_ne_app n us f0 a0 R heq)",
        kt = kont("f0", "a0", "A")
    );
    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr e (KExpr.app f0 a0) -> \
         forall (R : Type), {kA} -> R) \
         (f0 : KExpr) (a0 : KExpr) (heq : Eq KExpr e (KExpr.app f0 a0)) \
         (R : Type) (k : {kB}) => \
         ih1 f0 a0 heq R \
         (fun (A2 : KExpr) (B2 : KExpr) \
         (hf2 : TypingCtxConv tenv G f0 (KExpr.pi A2 B2)) \
         (ha2 : TypingCtxConv tenv G a0 A2) \
         (hd2 : DefEq (instantiate B2 a0) A) => \
         k A2 B2 hf2 ha2 (DefEq.trans (instantiate B2 a0) A B hd2 hd)))",
        kA = kont("f0", "a0", "A"),
        kB = kont("f0", "a0", "B")
    );
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (_ihty : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr ty (KExpr.app f0 a0) -> \
         forall (R : Type), {kty} -> R) \
         (_ihv : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr v (KExpr.app f0 a0) -> \
         forall (R : Type), {kv} -> R) \
         (_ihb : forall (f0 : KExpr) (a0 : KExpr), Eq KExpr b (KExpr.app f0 a0) -> \
         forall (R : Type), {kb} -> R) \
         (f0 : KExpr) (a0 : KExpr) \
         (heq : Eq KExpr (KExpr.let_ ty v b) (KExpr.app f0 a0)) \
         (R : Type) (_k : {kt}) => let_ne_app ty v b f0 a0 R heq)",
        kty = kont_ctx_app_inner("f0", "a0", "(KExpr.sort u)", "G"),
        kv = kont_ctx_app_inner("f0", "a0", "ty", "G"),
        kb = kont_ctx_app_inner("f0", "a0", "B", "(ListType.cons KExpr ty G)"),
        kt = kont("f0", "a0", "(instantiate B v)")
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (G : ListType KExpr) (f : KExpr) (a : KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.app f a) T) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G (KExpr.app f a) T h f a (Eq.refl KExpr (KExpr.app f a))"
    )
}

/// The app-generation continuation shape in an arbitrary context (needed for
/// the unused IH binders of the non-app arms).
fn kont_ctx_app_inner(f0: &str, a0: &str, t: &str, g: &str) -> String {
    // Collision-free kont binders (see ctx_app_gen_value).
    format!(
        "(forall (Ag : KExpr) (Bg : KExpr), \
         TypingCtxConv tenv {g} {f0} (KExpr.pi Ag Bg) -> \
         TypingCtxConv tenv {g} {a0} Ag -> \
         DefEq (instantiate Bg {a0}) {t} -> R)"
    )
}

/// The `ctx_lam_gen` proof term (same Eq-keyed technique as ctx_app_gen).
fn ctx_lam_gen_value() -> String {
    // Collision-free kont binders (Bg/ug): the T slot references arm binders.
    let kont = |a0: &str, b0: &str, t: &str, g: &str| {
        format!(
            "(forall (Bg : KExpr) (ug : Level), \
             TypingCtxConv tenv {g} {a0} (KExpr.sort ug) -> \
             TypingCtxConv tenv (ListType.cons KExpr {a0} {g}) {b0} Bg -> \
             DefEq (KExpr.pi {a0} Bg) {t} -> R)"
        )
    };
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (A0 : KExpr) (b0 : KExpr), Eq KExpr e (KExpr.lam A0 b0) -> \
         forall (R : Type), {k} -> R)",
        k = kont("A0", "b0", "T", "G")
    );
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (A0 : KExpr) (b0 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {k}) => \
         lam_ne_bvar A0 b0 i R \
         (Eq.symm KExpr (KExpr.bvar i) (KExpr.lam A0 b0) heq))",
        k = kont("A0", "b0", "(lift_at A Nat.zero (Nat.succ i))", "G")
    );
    let sort_arm = format!(
        "(fun (G : ListType KExpr) (n : Level) \
         (A0 : KExpr) (b0 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {k}) => sort_ne_lam n A0 b0 R heq)",
        k = kont("A0", "b0", "(KExpr.sort (Level.succ n))", "G")
    );
    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (_ihA : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr A (KExpr.lam A0 b0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihB : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr B (KExpr.lam A0 b0) -> \
         forall (R : Type), {kB} -> R) \
         (A0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.pi A B) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {kt}) => pi_ne_lam A B A0 b0 R heq)",
        kA = kont("A0", "b0", "(KExpr.sort n)", "G"),
        kB = kont("A0", "b0", "(KExpr.sort m)", "(ListType.cons KExpr A G)"),
        kt = kont("A0", "b0", "(KExpr.sort (Level.imax n m))", "G")
    );
    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (_ihA : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr A (KExpr.lam A0 b0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihb : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr b (KExpr.lam A0 b0) -> \
         forall (R : Type), {kb} -> R) \
         (A0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.lam A b) (KExpr.lam A0 b0)) \
         (R : Type) (k : {kt}) => \
         k B u \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G x (KExpr.sort u)) A A0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_lam_ty x A) \
         (KExpr.lam A b) (KExpr.lam A0 b0) heq) hA) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv (ListType.cons KExpr x G) b0 B) A A0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_lam_ty x A) \
         (KExpr.lam A b) (KExpr.lam A0 b0) heq) \
         (Eq.substType KExpr \
         (fun (y : KExpr) => TypingCtxConv tenv (ListType.cons KExpr A G) y B) b b0 \
         (Eq.cong KExpr KExpr (fun (y : KExpr) => srb_lam_body y b) \
         (KExpr.lam A b) (KExpr.lam A0 b0) heq) hb)) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => DefEq (KExpr.pi x B) (KExpr.pi A B)) A A0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_lam_ty x A) \
         (KExpr.lam A b) (KExpr.lam A0 b0) heq) \
         (DefEq.refl (KExpr.pi A B))))",
        kA = kont("A0", "b0", "(KExpr.sort u)", "G"),
        kb = kont("A0", "b0", "B", "(ListType.cons KExpr A G)"),
        kt = kont("A0", "b0", "(KExpr.pi A B)", "G")
    );
    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (_ihf : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr f (KExpr.lam A0 b0) -> \
         forall (R : Type), {kf} -> R) \
         (_iha : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr a (KExpr.lam A0 b0) -> \
         forall (R : Type), {ka} -> R) \
         (A0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.app f a) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {kt}) => app_ne_lam f a A0 b0 R heq)",
        kf = kont("A0", "b0", "(KExpr.pi A B)", "G"),
        ka = kont("A0", "b0", "A", "G"),
        kt = kont("A0", "b0", "(instantiate B a)", "G")
    );
    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (_hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (A0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.const n us) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {kt}) => const_ne_lam n us A0 b0 R heq)",
        kt = kont("A0", "b0", "A", "G")
    );
    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr e (KExpr.lam A0 b0) -> \
         forall (R : Type), {kA} -> R) \
         (A0 : KExpr) (b0 : KExpr) (heq : Eq KExpr e (KExpr.lam A0 b0)) \
         (R : Type) (k : {kB}) => \
         ih1 A0 b0 heq R \
         (fun (B2 : KExpr) (u2 : Level) \
         (h1 : TypingCtxConv tenv G A0 (KExpr.sort u2)) \
         (h2 : TypingCtxConv tenv (ListType.cons KExpr A0 G) b0 B2) \
         (hd2 : DefEq (KExpr.pi A0 B2) A) => \
         k B2 u2 h1 h2 (DefEq.trans (KExpr.pi A0 B2) A B hd2 hd)))",
        kA = kont("A0", "b0", "A", "G"),
        kB = kont("A0", "b0", "B", "G")
    );
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (lb : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hlb : TypingCtxConv tenv (ListType.cons KExpr ty G) lb B) \
         (_ihty : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr ty (KExpr.lam A0 b0) -> \
         forall (R : Type), {kty} -> R) \
         (_ihv : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr v (KExpr.lam A0 b0) -> \
         forall (R : Type), {kv} -> R) \
         (_ihlb : forall (A0 : KExpr) (b0 : KExpr), Eq KExpr lb (KExpr.lam A0 b0) -> \
         forall (R : Type), {klb} -> R) \
         (A0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.let_ ty v lb) (KExpr.lam A0 b0)) \
         (R : Type) (_k : {kt}) => let_ne_lam ty v lb A0 b0 R heq)",
        kty = kont("A0", "b0", "(KExpr.sort u)", "G"),
        kv = kont("A0", "b0", "ty", "G"),
        klb = kont("A0", "b0", "B", "(ListType.cons KExpr ty G)"),
        kt = kont("A0", "b0", "(instantiate B v)", "G")
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (G : ListType KExpr) (A : KExpr) (b : KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.lam A b) T) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G (KExpr.lam A b) T h A b (Eq.refl KExpr (KExpr.lam A b))"
    )
}

/// The `ctx_pi_gen` proof term (same Eq-keyed technique).
fn ctx_pi_gen_value() -> String {
    // Collision-free kont binders (ng/mg): the T slot references arm binders.
    let kont = |a0: &str, b0: &str, t: &str, g: &str| {
        format!(
            "(forall (ng : Level) (mg : Level), \
             TypingCtxConv tenv {g} {a0} (KExpr.sort ng) -> \
             TypingCtxConv tenv (ListType.cons KExpr {a0} {g}) {b0} (KExpr.sort mg) -> \
             DefEq (KExpr.sort (Level.imax ng mg)) {t} -> R)"
        )
    };
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (A0 : KExpr) (B0 : KExpr), Eq KExpr e (KExpr.pi A0 B0) -> \
         forall (R : Type), {k} -> R)",
        k = kont("A0", "B0", "T", "G")
    );
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (A0 : KExpr) (B0 : KExpr) (heq : Eq KExpr (KExpr.bvar i) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {k}) => \
         pi_ne_bvar A0 B0 i R \
         (Eq.symm KExpr (KExpr.bvar i) (KExpr.pi A0 B0) heq))",
        k = kont("A0", "B0", "(lift_at A Nat.zero (Nat.succ i))", "G")
    );
    let sort_arm = format!(
        "(fun (G : ListType KExpr) (n : Level) \
         (A0 : KExpr) (B0 : KExpr) (heq : Eq KExpr (KExpr.sort n) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {k}) => sort_ne_pi n A0 B0 R heq)",
        k = kont("A0", "B0", "(KExpr.sort (Level.succ n))", "G")
    );
    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (_ihA : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr A (KExpr.pi A0 B0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihB : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr B (KExpr.pi A0 B0) -> \
         forall (R : Type), {kB} -> R) \
         (A0 : KExpr) (B0 : KExpr) \
         (heq : Eq KExpr (KExpr.pi A B) (KExpr.pi A0 B0)) \
         (R : Type) (k : {kt}) => \
         k n m \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G x (KExpr.sort n)) A A0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_pi_dom x A) \
         (KExpr.pi A B) (KExpr.pi A0 B0) heq) hA) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv (ListType.cons KExpr x G) B0 \
         (KExpr.sort m)) A A0 \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => srb_pi_dom x A) \
         (KExpr.pi A B) (KExpr.pi A0 B0) heq) \
         (Eq.substType KExpr \
         (fun (y : KExpr) => TypingCtxConv tenv (ListType.cons KExpr A G) y \
         (KExpr.sort m)) B B0 \
         (Eq.cong KExpr KExpr (fun (y : KExpr) => srb_pi_cod y B) \
         (KExpr.pi A B) (KExpr.pi A0 B0) heq) hB)) \
         (DefEq.refl (KExpr.sort (Level.imax n m))))",
        kA = kont("A0", "B0", "(KExpr.sort n)", "G"),
        kB = kont("A0", "B0", "(KExpr.sort m)", "(ListType.cons KExpr A G)"),
        kt = kont("A0", "B0", "(KExpr.sort (Level.imax n m))", "G")
    );
    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (_ihA : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr A (KExpr.pi A0 B0) -> \
         forall (R : Type), {kA} -> R) \
         (_ihb : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr b (KExpr.pi A0 B0) -> \
         forall (R : Type), {kb} -> R) \
         (A0 : KExpr) (B0 : KExpr) \
         (heq : Eq KExpr (KExpr.lam A b) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {kt}) => lam_ne_pi A b A0 B0 R heq)",
        kA = kont("A0", "B0", "(KExpr.sort u)", "G"),
        kb = kont("A0", "B0", "B", "(ListType.cons KExpr A G)"),
        kt = kont("A0", "B0", "(KExpr.pi A B)", "G")
    );
    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (_ihf : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr f (KExpr.pi A0 B0) -> \
         forall (R : Type), {kf} -> R) \
         (_iha : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr a (KExpr.pi A0 B0) -> \
         forall (R : Type), {ka} -> R) \
         (A0 : KExpr) (B0 : KExpr) \
         (heq : Eq KExpr (KExpr.app f a) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {kt}) => app_ne_pi f a A0 B0 R heq)",
        kf = kont("A0", "B0", "(KExpr.pi A B)", "G"),
        ka = kont("A0", "B0", "A", "G"),
        kt = kont("A0", "B0", "(instantiate B a)", "G")
    );
    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (_hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (A0 : KExpr) (B0 : KExpr) \
         (heq : Eq KExpr (KExpr.const n us) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {kt}) => const_ne_pi n us A0 B0 R heq)",
        kt = kont("A0", "B0", "A", "G")
    );
    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr e (KExpr.pi A0 B0) -> \
         forall (R : Type), {kA} -> R) \
         (A0 : KExpr) (B0 : KExpr) (heq : Eq KExpr e (KExpr.pi A0 B0)) \
         (R : Type) (k : {kB}) => \
         ih1 A0 B0 heq R \
         (fun (n2 : Level) (m2 : Level) \
         (h1 : TypingCtxConv tenv G A0 (KExpr.sort n2)) \
         (h2 : TypingCtxConv tenv (ListType.cons KExpr A0 G) B0 (KExpr.sort m2)) \
         (hd2 : DefEq (KExpr.sort (Level.imax n2 m2)) A) => \
         k n2 m2 h1 h2 (DefEq.trans (KExpr.sort (Level.imax n2 m2)) A B hd2 hd)))",
        kA = kont("A0", "B0", "A", "G"),
        kB = kont("A0", "B0", "B", "G")
    );
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (Bl : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b Bl) \
         (_ihty : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr ty (KExpr.pi A0 B0) -> \
         forall (R : Type), {kty} -> R) \
         (_ihv : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr v (KExpr.pi A0 B0) -> \
         forall (R : Type), {kv} -> R) \
         (_ihb : forall (A0 : KExpr) (B0 : KExpr), Eq KExpr b (KExpr.pi A0 B0) -> \
         forall (R : Type), {kb} -> R) \
         (A0 : KExpr) (B0 : KExpr) \
         (heq : Eq KExpr (KExpr.let_ ty v b) (KExpr.pi A0 B0)) \
         (R : Type) (_k : {kt}) => let_ne_pi ty v b A0 B0 R heq)",
        kty = kont("A0", "B0", "(KExpr.sort u)", "G"),
        kv = kont("A0", "B0", "ty", "G"),
        kb = kont("A0", "B0", "Bl", "(ListType.cons KExpr ty G)"),
        kt = kont("A0", "B0", "(instantiate Bl v)", "G")
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (G : ListType KExpr) (A : KExpr) (B : KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.pi A B) T) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G (KExpr.pi A B) T h A B (Eq.refl KExpr (KExpr.pi A B))"
    )
}

/// The `ctx_let_gen` proof term (same Eq-keyed technique as ctx_app_gen) —
/// the let-increment generation lemma consumed by the zeta and
/// let-congruence preservation arms. Only `let_` and `conv` can conclude a
/// `let_`; every other head discriminates.
fn ctx_let_gen_value() -> String {
    // Collision-free kont binders (Bg/ug): the T slot references arm binders.
    let kont = |ty0: &str, v0: &str, b0: &str, t: &str, g: &str| {
        format!(
            "(forall (Bg : KExpr) (ug : Level), \
             TypingCtxConv tenv {g} {ty0} (KExpr.sort ug) -> \
             TypingCtxConv tenv {g} {v0} {ty0} -> \
             TypingCtxConv tenv (ListType.cons KExpr {ty0} {g}) {b0} Bg -> \
             DefEq (instantiate Bg {v0}) {t} -> R)"
        )
    };
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr e (KExpr.let_ ty0 v0 b0) -> \
         forall (R : Type), {k} -> R)",
        k = kont("ty0", "v0", "b0", "T", "G")
    );
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.bvar i) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {k}) => srb_bvar_ne_let i ty0 v0 b0 R heq)",
        k = kont("ty0", "v0", "b0", "(lift_at A Nat.zero (Nat.succ i))", "G")
    );
    let sort_arm = format!(
        "(fun (G : ListType KExpr) (n : Level) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.sort n) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {k}) => srb_sort_ne_let n ty0 v0 b0 R heq)",
        k = kont("ty0", "v0", "b0", "(KExpr.sort (Level.succ n))", "G")
    );
    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (_ihA : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr A (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kA} -> R) \
         (_ihB : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr B (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kB} -> R) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.pi A B) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {kt}) => pi_ne_let A B ty0 v0 b0 R heq)",
        kA = kont("ty0", "v0", "b0", "(KExpr.sort n)", "G"),
        kB = kont(
            "ty0",
            "v0",
            "b0",
            "(KExpr.sort m)",
            "(ListType.cons KExpr A G)"
        ),
        kt = kont("ty0", "v0", "b0", "(KExpr.sort (Level.imax n m))", "G")
    );
    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (_ihA : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr A (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kA} -> R) \
         (_ihb : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr b (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kb} -> R) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.lam A b) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {kt}) => lam_ne_let A b ty0 v0 b0 R heq)",
        kA = kont("ty0", "v0", "b0", "(KExpr.sort u)", "G"),
        kb = kont("ty0", "v0", "b0", "B", "(ListType.cons KExpr A G)"),
        kt = kont("ty0", "v0", "b0", "(KExpr.pi A B)", "G")
    );
    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (_ihf : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr f (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kf} -> R) \
         (_iha : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr a (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {ka} -> R) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.app f a) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {kt}) => app_ne_let f a ty0 v0 b0 R heq)",
        kf = kont("ty0", "v0", "b0", "(KExpr.pi A B)", "G"),
        ka = kont("ty0", "v0", "b0", "A", "G"),
        kt = kont("ty0", "v0", "b0", "(instantiate B a)", "G")
    );
    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (_hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.const n us) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (_k : {kt}) => srb_const_ne_let n us ty0 v0 b0 R heq)",
        kt = kont("ty0", "v0", "b0", "A", "G")
    );
    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr e (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kA} -> R) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr e (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (k : {kB}) => \
         ih1 ty0 v0 b0 heq R \
         (fun (B2 : KExpr) (u2 : Level) \
         (h1 : TypingCtxConv tenv G ty0 (KExpr.sort u2)) \
         (h2 : TypingCtxConv tenv G v0 ty0) \
         (h3 : TypingCtxConv tenv (ListType.cons KExpr ty0 G) b0 B2) \
         (hd2 : DefEq (instantiate B2 v0) A) => \
         k B2 u2 h1 h2 h3 (DefEq.trans (instantiate B2 v0) A B hd2 hd)))",
        kA = kont("ty0", "v0", "b0", "A", "G"),
        kB = kont("ty0", "v0", "b0", "B", "G")
    );
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hv : TypingCtxConv tenv G v ty) \
         (hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (_ihty : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr ty (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kty} -> R) \
         (_ihv : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr v (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kv} -> R) \
         (_ihb : forall (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr), \
         Eq KExpr b (KExpr.let_ ty0 v0 b0) -> forall (R : Type), {kb} -> R) \
         (ty0 : KExpr) (v0 : KExpr) (b0 : KExpr) \
         (heq : Eq KExpr (KExpr.let_ ty v b) (KExpr.let_ ty0 v0 b0)) \
         (R : Type) (k : {kt}) => \
         k B u \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G x (KExpr.sort u)) ty ty0 \
         (let_inj_fst ty v b ty0 v0 b0 heq) hty) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G v0 x) ty ty0 \
         (let_inj_fst ty v b ty0 v0 b0 heq) \
         (Eq.substType KExpr \
         (fun (y : KExpr) => TypingCtxConv tenv G y ty) v v0 \
         (let_inj_snd ty v b ty0 v0 b0 heq) hv)) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv (ListType.cons KExpr x G) b0 B) ty ty0 \
         (let_inj_fst ty v b ty0 v0 b0 heq) \
         (Eq.substType KExpr \
         (fun (y : KExpr) => TypingCtxConv tenv (ListType.cons KExpr ty G) y B) b b0 \
         (let_inj_thd ty v b ty0 v0 b0 heq) hb)) \
         (Eq.substType KExpr \
         (fun (x : KExpr) => DefEq (instantiate B x) (instantiate B v)) v v0 \
         (let_inj_snd ty v b ty0 v0 b0 heq) \
         (DefEq.refl (instantiate B v))))",
        kty = kont("ty0", "v0", "b0", "(KExpr.sort u)", "G"),
        kv = kont("ty0", "v0", "b0", "ty", "G"),
        kb = kont("ty0", "v0", "b0", "B", "(ListType.cons KExpr ty G)"),
        kt = kont("ty0", "v0", "b0", "(instantiate B v)", "G")
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.let_ ty v b) T) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G (KExpr.let_ ty v b) T h ty v b (Eq.refl KExpr (KExpr.let_ ty v b))"
    )
}

/// The `delta_preserves_typing_ctx` proof term. Works over the delta_step
/// graph internally (converting the incoming delta_reduces once).
fn delta_preserves_typing_ctx_value() -> String {
    let env = "(red_def the_red_env)";
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (e2 : KExpr), delta_step {env} e e2 -> TypingCtxConv tenv G e2 T)"
    );
    // Off-shape heads: delta_reduct computes to none — absurd.
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.bvar i) e2) => \
         option_none_ne_some_type KExpr e2 \
         (TypingCtxConv tenv G e2 (lift_at A Nat.zero (Nat.succ i))) hs)"
    );
    let sort_arm = format!(
        "(fun (G : ListType KExpr) (n : Level) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.sort n) e2) => \
         option_none_ne_some_type KExpr e2 \
         (TypingCtxConv tenv G e2 (KExpr.sort (Level.succ n))) hs)"
    );
    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (_ihA : forall (e2 : KExpr), delta_step {env} A e2 -> \
         TypingCtxConv tenv G e2 (KExpr.sort n)) \
         (_ihB : forall (e2 : KExpr), delta_step {env} B e2 -> \
         TypingCtxConv tenv (ListType.cons KExpr A G) e2 (KExpr.sort m)) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.pi A B) e2) => \
         option_none_ne_some_type KExpr e2 \
         (TypingCtxConv tenv G e2 (KExpr.sort (Level.imax n m))) hs)"
    );
    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (_ihA : forall (e2 : KExpr), delta_step {env} A e2 -> \
         TypingCtxConv tenv G e2 (KExpr.sort u)) \
         (_ihb : forall (e2 : KExpr), delta_step {env} b e2 -> \
         TypingCtxConv tenv (ListType.cons KExpr A G) e2 B) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.lam A b) e2) => \
         option_none_ne_some_type KExpr e2 \
         (TypingCtxConv tenv G e2 (KExpr.pi A B)) hs)"
    );
    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (ha : TypingCtxConv tenv G a A) \
         (ihf : forall (e2 : KExpr), delta_step {env} f e2 -> \
         TypingCtxConv tenv G e2 (KExpr.pi A B)) \
         (_iha : forall (e2 : KExpr), delta_step {env} a e2 -> \
         TypingCtxConv tenv G e2 A) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.app f a) e2) => \
         delta_step_app_inv_type {env} f a e2 \
         (TypingCtxConv tenv G e2 (instantiate B a)) hs \
         (fun (f0 : KExpr) (hsf : delta_step {env} f f0) \
         (heq : Eq KExpr e2 (KExpr.app f0 a)) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G z (instantiate B a)) \
         (KExpr.app f0 a) e2 \
         (Eq.symm KExpr e2 (KExpr.app f0 a) heq) \
         (TypingCtxConv.app tenv G f0 a A B (ihf f0 hsf) ha)))"
    );
    // const head: resolve the lookup with opt_case_type; the some-case feeds
    // the carried defval_typed field.
    let bind_body = "(fun (val : KExpr) => OptionType.some KExpr \
         (apply_spine (kapp_args (KExpr.const n us)) val))"
        .to_string();
    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.const n us) e2) => \
         opt_case_type KExpr (defval_for {env} n) (TypingCtxConv tenv G e2 A) \
         (fun (hnone : Eq (OptionType KExpr) (defval_for {env} n) (OptionType.none KExpr)) => \
         option_none_ne_some_type KExpr e2 (TypingCtxConv tenv G e2 A) \
         (Eq.subst (OptionType KExpr) \
         (fun (o : OptionType KExpr) => Eq (OptionType KExpr) \
         (opt_bind KExpr KExpr o {bind_body}) \
         (OptionType.some KExpr e2)) \
         (defval_for {env} n) (OptionType.none KExpr) hnone hs)) \
         (fun (v : KExpr) \
         (hsome : Eq (OptionType KExpr) (defval_for {env} n) (OptionType.some KExpr v)) => \
         Eq.substType KExpr (fun (z : KExpr) => TypingCtxConv tenv G z A) v e2 \
         (option_some_inj KExpr v e2 \
         (Eq.subst (OptionType KExpr) \
         (fun (o : OptionType KExpr) => Eq (OptionType KExpr) \
         (opt_bind KExpr KExpr o {bind_body}) \
         (OptionType.some KExpr e2)) \
         (defval_for {env} n) (OptionType.some KExpr v) hsome hs)) \
         (tec_defval_typed tenv W n v A hsome hA G)))"
    );
    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (e2 : KExpr), delta_step {env} e e2 -> \
         TypingCtxConv tenv G e2 A) \
         (e2 : KExpr) (hs : delta_step {env} e e2) => \
         TypingCtxConv.conv tenv G e2 A B (ih1 e2 hs) hd)"
    );
    // let_ head: a let is its own spine head, never a const head —
    // delta_reduct computes to none, absurd (same shape as the lam arm).
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (_ihty : forall (e2 : KExpr), delta_step {env} ty e2 -> \
         TypingCtxConv tenv G e2 (KExpr.sort u)) \
         (_ihv : forall (e2 : KExpr), delta_step {env} v e2 -> \
         TypingCtxConv tenv G e2 ty) \
         (_ihb : forall (e2 : KExpr), delta_step {env} b e2 -> \
         TypingCtxConv tenv (ListType.cons KExpr ty G) e2 B) \
         (e2 : KExpr) (hs : delta_step {env} (KExpr.let_ ty v b) e2) => \
         option_none_ne_some_type KExpr e2 \
         (TypingCtxConv tenv G e2 (instantiate B v)) hs)"
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (W : TypingEnvCoherent tenv) \
         (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) \
         (h0 : TypingCtxConv tenv G0 e0 T0) \
         (e02 : KExpr) (hr : delta_reduces e0 e02) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G0 e0 T0 h0 e02 (delta_reduces_to_step e0 e02 hr)"
    )
}

/// The `srb_beta_redex_preserves` proof term (the beta arm's content).
fn srb_beta_redex_preserves_value() -> String {
    "fun (tenv : Name -> OptionType KExpr) \
     (hf : RedEnvFaithful the_red_env) \
     (W : TypingEnvCoherent tenv) \
     (wd : DefEnvWellformed the_red_env) \
     (wr : RecEnvWellformed (red_rec the_red_env)) \
     (A : KExpr) (b : KExpr) (a : KExpr) \
     (G : ListType KExpr) (T : KExpr) \
     (h : TypingCtxConv tenv G (KExpr.app (KExpr.lam A b) a) T) => \
     ctx_app_gen tenv G (KExpr.lam A b) a T h \
     (TypingCtxConv tenv G (instantiate b a) T) \
     (fun (A0 : KExpr) (B0 : KExpr) \
     (hlam : TypingCtxConv tenv G (KExpr.lam A b) (KExpr.pi A0 B0)) \
     (harg : TypingCtxConv tenv G a A0) \
     (hdefT : DefEq (instantiate B0 a) T) => \
     ctx_lam_gen tenv G A b (KExpr.pi A0 B0) hlam \
     (TypingCtxConv tenv G (instantiate b a) T) \
     (fun (B1 : KExpr) (u : Level) \
     (_hAsort : TypingCtxConv tenv G A (KExpr.sort u)) \
     (hbody : TypingCtxConv tenv (ListType.cons KExpr A G) b B1) \
     (hdefpi : DefEq (KExpr.pi A B1) (KExpr.pi A0 B0)) => \
     TypingCtxConv.conv tenv G (instantiate b a) (instantiate B1 a) T \
     (substitution_typing_ctx tenv hf W G A b B1 a hbody \
     (TypingCtxConv.conv tenv G a A0 A harg \
     (DefEq.symm A A0 (pi_injectivity_def_eq_dom hf A A0 B1 B0 hdefpi)))) \
     (DefEq.trans (instantiate B1 a) (instantiate B0 a) T \
     (def_eq_respects_subst_at B1 B0 a Nat.zero wd wr \
     (pi_injectivity_def_eq_cod hf A A0 B1 B0 hdefpi)) \
     hdefT)))"
        .to_string()
}

/// The `beta_reduces_preserves_typing_ctx` proof term: beta_reduces.rec over
/// all 11 arms.
fn beta_reduces_preserves_typing_ctx_value() -> String {
    let goal = |e2: &str| format!("(TypingCtxConv tenv G {e2} T)");
    let ih = "forall (G : ListType KExpr) (T : KExpr), TypingCtxConv tenv G";
    let motive = format!(
        "(fun (x : KExpr) (y : KExpr) (_ : beta_reduces x y) => \
         {ih} x T -> TypingCtxConv tenv G y T)"
    );
    let beta_arm = "(fun (A : KExpr) (body : KExpr) (arg : KExpr) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.app (KExpr.lam A body) arg) T) => \
         srb_beta_redex_preserves tenv hf W wd wr A body arg G T h)"
        .to_string();
    let app_left_arm = format!(
        "(fun (f : KExpr) (f2 : KExpr) (a : KExpr) \
         (_hs : beta_reduces f f2) \
         (ih : {ih} f T -> TypingCtxConv tenv G f2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.app f a) T) => \
         ctx_app_gen tenv G f a T h {g} \
         (fun (A : KExpr) (B : KExpr) \
         (hfp : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (hap : TypingCtxConv tenv G a A) \
         (hdefT : DefEq (instantiate B a) T) => \
         TypingCtxConv.conv tenv G (KExpr.app f2 a) (instantiate B a) T \
         (TypingCtxConv.app tenv G f2 a A B (ih G (KExpr.pi A B) hfp) hap) \
         hdefT))",
        g = goal("(KExpr.app f2 a)")
    );
    let app_right_arm = format!(
        "(fun (f : KExpr) (a : KExpr) (a2 : KExpr) \
         (hs : beta_reduces a a2) \
         (ih : {ih} a T -> TypingCtxConv tenv G a2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.app f a) T) => \
         ctx_app_gen tenv G f a T h {g} \
         (fun (A : KExpr) (B : KExpr) \
         (hfp : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (hap : TypingCtxConv tenv G a A) \
         (hdefT : DefEq (instantiate B a) T) => \
         TypingCtxConv.conv tenv G (KExpr.app f a2) (instantiate B a2) T \
         (TypingCtxConv.app tenv G f a2 A B hfp (ih G A hap)) \
         (DefEq.trans (instantiate B a2) (instantiate B a) T \
         (def_eq_instantiate_arg_congr B a2 a hf \
         (DefEq.symm a a2 (beta_reduces_preserves_def_eq a a2 hs))) \
         hdefT)))",
        g = goal("(KExpr.app f a2)")
    );
    let lam_ty_arm = format!(
        "(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) \
         (hs : beta_reduces ty ty2) \
         (ih : {ih} ty T -> TypingCtxConv tenv G ty2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.lam ty body) T) => \
         ctx_lam_gen tenv G ty body T h {g} \
         (fun (B : KExpr) (u : Level) \
         (hAsort : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefpi : DefEq (KExpr.pi ty B) T) => \
         TypingCtxConv.conv tenv G (KExpr.lam ty2 body) (KExpr.pi ty2 B) T \
         (TypingCtxConv.lam tenv G ty2 body B u (ih G (KExpr.sort u) hAsort) \
         (ctx_conv tenv hf (ListType.cons KExpr ty G) (ListType.cons KExpr ty2 G) \
         body B hbody \
         (CtxDefEq.cons ty ty2 G G \
         (beta_reduces_preserves_def_eq ty ty2 hs) (ctx_def_eq_refl G)))) \
         (DefEq.trans (KExpr.pi ty2 B) (KExpr.pi ty B) T \
         (DefEq.pi_cong ty2 ty B B \
         (DefEq.symm ty ty2 (beta_reduces_preserves_def_eq ty ty2 hs)) \
         (DefEq.refl B)) \
         hdefpi)))",
        g = goal("(KExpr.lam ty2 body)")
    );
    let lam_body_arm = format!(
        "(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) \
         (_hs : beta_reduces body body2) \
         (ih : {ih} body T -> TypingCtxConv tenv G body2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.lam ty body) T) => \
         ctx_lam_gen tenv G ty body T h {g} \
         (fun (B : KExpr) (u : Level) \
         (hAsort : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefpi : DefEq (KExpr.pi ty B) T) => \
         TypingCtxConv.conv tenv G (KExpr.lam ty body2) (KExpr.pi ty B) T \
         (TypingCtxConv.lam tenv G ty body2 B u hAsort \
         (ih (ListType.cons KExpr ty G) B hbody)) \
         hdefpi))",
        g = goal("(KExpr.lam ty body2)")
    );
    let pi_dom_arm_body = |alias: &str| {
        format!(
            "(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) \
         (hs : beta_reduces dom dom2) \
         (ih : {ih} dom T -> TypingCtxConv tenv G dom2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G ({alias} dom body) T) => \
         ctx_pi_gen tenv G dom body T h \
         (TypingCtxConv tenv G ({alias} dom2 body) T) \
         (fun (n : Level) (m : Level) \
         (hdomsort : TypingCtxConv tenv G dom (KExpr.sort n)) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr dom G) body (KExpr.sort m)) \
         (hdefsort : DefEq (KExpr.sort (Level.imax n m)) T) => \
         TypingCtxConv.conv tenv G (KExpr.pi dom2 body) \
         (KExpr.sort (Level.imax n m)) T \
         (TypingCtxConv.pi tenv G dom2 body n m (ih G (KExpr.sort n) hdomsort) \
         (ctx_conv tenv hf (ListType.cons KExpr dom G) (ListType.cons KExpr dom2 G) \
         body (KExpr.sort m) hbody \
         (CtxDefEq.cons dom dom2 G G \
         (beta_reduces_preserves_def_eq dom dom2 hs) (ctx_def_eq_refl G)))) \
         hdefsort))"
        )
    };
    let pi_cod_arm_body = |alias: &str| {
        format!(
            "(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) \
         (_hs : beta_reduces body body2) \
         (ih : {ih} body T -> TypingCtxConv tenv G body2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G ({alias} dom body) T) => \
         ctx_pi_gen tenv G dom body T h \
         (TypingCtxConv tenv G ({alias} dom body2) T) \
         (fun (n : Level) (m : Level) \
         (hdomsort : TypingCtxConv tenv G dom (KExpr.sort n)) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr dom G) body (KExpr.sort m)) \
         (hdefsort : DefEq (KExpr.sort (Level.imax n m)) T) => \
         TypingCtxConv.conv tenv G (KExpr.pi dom body2) \
         (KExpr.sort (Level.imax n m)) T \
         (TypingCtxConv.pi tenv G dom body2 n m hdomsort \
         (ih (ListType.cons KExpr dom G) (KExpr.sort m) hbody)) \
         hdefsort))"
        )
    };
    let pi_dom_arm = pi_dom_arm_body("KExpr.pi");
    let pi_cod_arm = pi_cod_arm_body("KExpr.pi");
    let forall_dom_arm = pi_dom_arm_body("KExpr.forall_");
    let forall_cod_arm = pi_cod_arm_body("KExpr.forall_");
    // zeta: THE textbook second consumer of the substitution lemma — exactly
    // the beta arm's shape but SIMPLER (no pi-injectivity: the let rule's
    // premises hand over `val : ty` and `(ty::G) ⊢ body : B` directly).
    // ctx_let_gen inversion, substitution_typing_ctx, one conv.
    let zeta_arm = format!(
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.let_ ty val body) T) => \
         ctx_let_gen tenv G ty val body T h \
         {g} \
         (fun (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hval : TypingCtxConv tenv G val ty) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefT : DefEq (instantiate B val) T) => \
         TypingCtxConv.conv tenv G (instantiate body val) (instantiate B val) T \
         (substitution_typing_ctx tenv hf W G ty body B val hbody hval) \
         hdefT))",
        g = goal("(instantiate body val)")
    );
    // let_ty: mirror lam_ty — IH re-types the annotation; the value premise
    // converts along the step DefEq; the body premise transports across the
    // reduced context entry via ctx_conv; the rebuilt type (instantiate B val)
    // is UNCHANGED, one conv along the generation equation.
    let let_ty_arm = format!(
        "(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
         (hs : beta_reduces ty ty2) \
         (ih : {ih} ty T -> TypingCtxConv tenv G ty2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.let_ ty val body) T) => \
         ctx_let_gen tenv G ty val body T h {g} \
         (fun (B : KExpr) (u : Level) \
         (hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hval : TypingCtxConv tenv G val ty) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefT : DefEq (instantiate B val) T) => \
         TypingCtxConv.conv tenv G (KExpr.let_ ty2 val body) (instantiate B val) T \
         (TypingCtxConv.let_ tenv G ty2 val body B u \
         (ih G (KExpr.sort u) hty) \
         (TypingCtxConv.conv tenv G val ty ty2 hval \
         (beta_reduces_preserves_def_eq ty ty2 hs)) \
         (ctx_conv tenv hf (ListType.cons KExpr ty G) (ListType.cons KExpr ty2 G) \
         body B hbody \
         (CtxDefEq.cons ty ty2 G G \
         (beta_reduces_preserves_def_eq ty ty2 hs) (ctx_def_eq_refl G)))) \
         hdefT))",
        g = goal("(KExpr.let_ ty2 val body)")
    );
    // let_val: mirror app_right — the let's type is DEPENDENT on the value;
    // rebuild at instantiate B val2, bridge back via
    // def_eq_instantiate_arg_congr (symm of the step DefEq), conv twice.
    let let_val_arm = format!(
        "(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
         (hs : beta_reduces val val2) \
         (ih : {ih} val T -> TypingCtxConv tenv G val2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.let_ ty val body) T) => \
         ctx_let_gen tenv G ty val body T h {g} \
         (fun (B : KExpr) (u : Level) \
         (hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hval : TypingCtxConv tenv G val ty) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefT : DefEq (instantiate B val) T) => \
         TypingCtxConv.conv tenv G (KExpr.let_ ty val2 body) (instantiate B val2) T \
         (TypingCtxConv.let_ tenv G ty val2 body B u hty (ih G ty hval) hbody) \
         (DefEq.trans (instantiate B val2) (instantiate B val) T \
         (def_eq_instantiate_arg_congr B val2 val hf \
         (DefEq.symm val val2 (beta_reduces_preserves_def_eq val val2 hs))) \
         hdefT)))",
        g = goal("(KExpr.let_ ty val2 body)")
    );
    // let_body: mirror lam_body — IH in the extended context, rebuild, one
    // conv along the generation equation (type unchanged).
    let let_body_arm = format!(
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
         (_hs : beta_reduces body body2) \
         (ih : {ih} body T -> TypingCtxConv tenv G body2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.let_ ty val body) T) => \
         ctx_let_gen tenv G ty val body T h {g} \
         (fun (B : KExpr) (u : Level) \
         (hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (hval : TypingCtxConv tenv G val ty) \
         (hbody : TypingCtxConv tenv (ListType.cons KExpr ty G) body B) \
         (hdefT : DefEq (instantiate B val) T) => \
         TypingCtxConv.conv tenv G (KExpr.let_ ty val body2) (instantiate B val) T \
         (TypingCtxConv.let_ tenv G ty val body2 B u hty hval \
         (ih (ListType.cons KExpr ty G) B hbody)) \
         hdefT))",
        g = goal("(KExpr.let_ ty val body2)")
    );
    let iota_arm = "(fun (e : KExpr) (e2 : KExpr) (hi : iota_reduces e e2) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G e T) => \
         tec_iota_typed tenv W e e2 hi G T h)"
        .to_string();
    // proj: proj-headed subjects are not typeable under TypingCtxConv (no proj
    // rule), so the premise is absurd — discharged by ctx_proj_absurd.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) \
         (_hs : beta_reduces sub sub2) \
         (_ih : forall (G : ListType KExpr) (T : KExpr), \
         TypingCtxConv tenv G sub T -> TypingCtxConv tenv G sub2 T) \
         (G : ListType KExpr) (T : KExpr) \
         (h : TypingCtxConv tenv G (KExpr.proj s i sub) T) => \
         ctx_proj_absurd tenv s i sub G T {g} h)",
        g = goal("(KExpr.proj s i sub2)")
    );
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (hf : RedEnvFaithful the_red_env) \
         (W : TypingEnvCoherent tenv) \
         (wd : DefEnvWellformed the_red_env) \
         (wr : RecEnvWellformed (red_rec the_red_env)) \
         (e0 : KExpr) (e02 : KExpr) (hbr : beta_reduces e0 e02) => \
         beta_reduces.rec {motive} \
         {beta_arm} {app_left_arm} {app_right_arm} {lam_ty_arm} {lam_body_arm} \
         {pi_dom_arm} {pi_cod_arm} {forall_dom_arm} {forall_cod_arm} \
         {zeta_arm} {let_ty_arm} {let_val_arm} {let_body_arm} {iota_arm} {proj_arm} \
         e0 e02 hbr"
    )
}

/// The `ctx_proj_absurd` proof term: a proj-headed subject is not typeable
/// under `TypingCtxConv` (no proj rule), so `TypingCtxConv tenv G (proj ..) T`
/// eliminates into any `C`. `TypingCtxConv.rec` with an Eq-keyed motive; the
/// seven rigid-head arms (var/sort/pi/lam/app/const/let_) refute via the
/// NOT_PROJ discriminator + Empty.rec; the conv arm forwards the IH.
fn ctx_proj_absurd_value() -> String {
    format!(
        "fun (tenv : Name -> OptionType KExpr) (s : Name) (i : Nat) (sub : KExpr) \
         (G : ListType KExpr) (T : KExpr) (C : Type) \
         (h : TypingCtxConv tenv G (KExpr.proj s i sub) T) => \
         TypingCtxConv.rec tenv \
         (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_ : TypingCtxConv tenv G0 e0 T0) => \
         Eq KExpr e0 (KExpr.proj s i sub) -> C) \
         (fun (G0 : ListType KExpr) (i0 : Nat) (A : KExpr) \
         (_hlk : Eq (OptionType KExpr) (ctx_lookup G0 i0) (OptionType.some KExpr A)) \
         (eq : Eq KExpr (KExpr.bvar i0) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.bvar i0) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (n : Level) \
         (eq : Eq KExpr (KExpr.sort n) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.sort n) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G0 A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G0) B (KExpr.sort m)) \
         (_ihA : Eq KExpr A (KExpr.proj s i sub) -> C) \
         (_ihB : Eq KExpr B (KExpr.proj s i sub) -> C) \
         (eq : Eq KExpr (KExpr.pi A B) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.pi A B) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G0 A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G0) b B) \
         (_ihA : Eq KExpr A (KExpr.proj s i sub) -> C) \
         (_ihb : Eq KExpr b (KExpr.proj s i sub) -> C) \
         (eq : Eq KExpr (KExpr.lam A b) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.lam A b) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G0 f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G0 a A) \
         (_ihf : Eq KExpr f (KExpr.proj s i sub) -> C) \
         (_iha : Eq KExpr a (KExpr.proj s i sub) -> C) \
         (eq : Eq KExpr (KExpr.app f a) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.app f a) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (_hc : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (eq : Eq KExpr (KExpr.const n us) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.const n us) (KExpr.proj s i sub) eq Nat.zero)) \
         (fun (G0 : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_hd : TypingCtxConv tenv G0 e A) (_hdefeq : DefEq A B) \
         (ih : Eq KExpr e (KExpr.proj s i sub) -> C) \
         (eq : Eq KExpr e (KExpr.proj s i sub)) => ih eq) \
         (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G0 ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G0 v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G0) b B) \
         (_ihty : Eq KExpr ty (KExpr.proj s i sub) -> C) \
         (_ihv : Eq KExpr v (KExpr.proj s i sub) -> C) \
         (_ihb : Eq KExpr b (KExpr.proj s i sub) -> C) \
         (eq : Eq KExpr (KExpr.let_ ty v b) (KExpr.proj s i sub)) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {discr} (KExpr.let_ ty v b) (KExpr.proj s i sub) eq Nat.zero)) \
         G (KExpr.proj s i sub) T h (Eq.refl KExpr (KExpr.proj s i sub))",
        discr = SRB_KEXPR_NOT_PROJ
    )
}

/// The `def_eq_psubst` proof term: DefEq.rec with the substitution
/// universalized in the motive; binder congruences step to `up s`. The
/// trailing zeta minor is the beta minor's exact shape on the genuine let_
/// constructor (psubst_instantiate); let_cong is the ternary congruence with
/// the body IH at `up s`.
fn def_eq_psubst_value() -> String {
    let ih = |x: &str, y: &str| {
        format!("(forall (s : Nat -> KExpr), DefEq (psubst s {x}) (psubst s {y}))")
    };
    format!(
        "fun (hdp : forall (e : KExpr) (e' : KExpr), delta_reduces e e' -> \
         forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')) \
         (hip : forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> \
         forall (s : Nat -> KExpr), DefEq (psubst s e) (psubst s e')) \
         (A : KExpr) (B : KExpr) (h : DefEq A B) => \
         DefEq.rec \
         (fun (a : KExpr) (b : KExpr) (_h : DefEq a b) => \
         forall (s : Nat -> KExpr), DefEq (psubst s a) (psubst s b)) \
         (fun (a : KExpr) (s : Nat -> KExpr) => DefEq.refl (psubst s a)) \
         (fun (a : KExpr) (b : KExpr) (_h : DefEq a b) (ih : {ih_ab}) \
         (s : Nat -> KExpr) => DefEq.symm (psubst s a) (psubst s b) (ih s)) \
         (fun (a : KExpr) (b : KExpr) (c : KExpr) (_hab : DefEq a b) (_hbc : DefEq b c) \
         (ih1 : {ih_ab}) (ih2 : {ih_bc}) (s : Nat -> KExpr) => \
         DefEq.trans (psubst s a) (psubst s b) (psubst s c) (ih1 s) (ih2 s)) \
         (fun (A0 : KExpr) (b : KExpr) (a : KExpr) (s : Nat -> KExpr) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => DefEq (KExpr.app (KExpr.lam (psubst s A0) (psubst (up s) b)) \
         (psubst s a)) z) \
         (instantiate (psubst (up s) b) (psubst s a)) \
         (psubst s (instantiate b a)) \
         (Eq.symm KExpr (psubst s (instantiate b a)) \
         (instantiate (psubst (up s) b) (psubst s a)) \
         (psubst_instantiate b a s)) \
         (DefEq.beta (psubst s A0) (psubst (up s) b) (psubst s a))) \
         (fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (_hf : DefEq f f') (_ha : DefEq a a') \
         (ihf : {ih_ff}) (iha : {ih_aa}) (s : Nat -> KExpr) => \
         DefEq.app_cong (psubst s f) (psubst s f') (psubst s a) (psubst s a') \
         (ihf s) (iha s)) \
         (fun (A0 : KExpr) (A0' : KExpr) (b : KExpr) (b' : KExpr) \
         (_hA : DefEq A0 A0') (_hb : DefEq b b') \
         (ihA : {ih_AA}) (ihb : {ih_bb}) (s : Nat -> KExpr) => \
         DefEq.lam_cong (psubst s A0) (psubst s A0') (psubst (up s) b) (psubst (up s) b') \
         (ihA s) (ihb (up s))) \
         (fun (A0 : KExpr) (A0' : KExpr) (B0 : KExpr) (B0' : KExpr) \
         (_hA : DefEq A0 A0') (_hB : DefEq B0 B0') \
         (ihA : {ih_AA}) (ihB : {ih_BB}) (s : Nat -> KExpr) => \
         DefEq.pi_cong (psubst s A0) (psubst s A0') (psubst (up s) B0) (psubst (up s) B0') \
         (ihA s) (ihB (up s))) \
         (fun (e : KExpr) (e' : KExpr) (hd : delta_reduces e e') (s : Nat -> KExpr) => \
         hdp e e' hd s) \
         (fun (e : KExpr) (e' : KExpr) (hi : iota_reduces e e') (s : Nat -> KExpr) => \
         hip e e' hi s) \
         (fun (ty : KExpr) (v : KExpr) (b : KExpr) (s : Nat -> KExpr) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => DefEq (KExpr.let_ (psubst s ty) (psubst s v) \
         (psubst (up s) b)) z) \
         (instantiate (psubst (up s) b) (psubst s v)) \
         (psubst s (instantiate b v)) \
         (Eq.symm KExpr (psubst s (instantiate b v)) \
         (instantiate (psubst (up s) b) (psubst s v)) \
         (psubst_instantiate b v s)) \
         (DefEq.zeta (psubst s ty) (psubst s v) (psubst (up s) b))) \
         (fun (ty : KExpr) (ty' : KExpr) (v : KExpr) (v' : KExpr) \
         (b : KExpr) (b' : KExpr) \
         (_hty : DefEq ty ty') (_hv : DefEq v v') (_hb : DefEq b b') \
         (ihty : {ih_tt}) (ihv : {ih_vv}) (ihb : {ih_bb2}) (s : Nat -> KExpr) => \
         DefEq.let_cong (psubst s ty) (psubst s ty') (psubst s v) (psubst s v') \
         (psubst (up s) b) (psubst (up s) b') \
         (ihty s) (ihv s) (ihb (up s))) \
         (fun (sn : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) \
         (_hsub : DefEq sub sub') (ihsub : {ih_ss}) (s : Nat -> KExpr) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => DefEq (KExpr.proj sn i (psubst s sub)) z) \
         (KExpr.proj sn i (psubst s sub')) \
         (psubst s (KExpr.proj sn i sub')) \
         (Eq.symm KExpr (psubst s (KExpr.proj sn i sub')) \
         (KExpr.proj sn i (psubst s sub')) (psubst_proj s sn i sub')) \
         (Eq.substType KExpr \
         (fun (z : KExpr) => DefEq z (KExpr.proj sn i (psubst s sub'))) \
         (KExpr.proj sn i (psubst s sub)) (psubst s (KExpr.proj sn i sub)) \
         (Eq.symm KExpr (psubst s (KExpr.proj sn i sub)) \
         (KExpr.proj sn i (psubst s sub)) (psubst_proj s sn i sub)) \
         (DefEq.proj_cong sn i (psubst s sub) (psubst s sub') (ihsub s)))) \
         A B h",
        ih_ab = ih("a", "b"),
        ih_bc = ih("b", "c"),
        ih_ff = ih("f", "f'"),
        ih_aa = ih("a", "a'"),
        ih_AA = ih("A0", "A0'"),
        ih_bb = ih("b", "b'"),
        ih_BB = ih("B0", "B0'"),
        ih_tt = ih("ty", "ty'"),
        ih_vv = ih("v", "v'"),
        ih_bb2 = ih("b", "b'"),
        ih_ss = ih("sub", "sub'"),
    )
}

/// The `subst_typing_up` proof term: index split via Nat.rec; index 0 is the
/// var rule + psubst_up_lift, index j+1 weakens the source substitution entry.
fn subst_typing_up_value() -> String {
    let s0 = "(Nat.succ Nat.zero)";
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (hf : RedEnvFaithful the_red_env) \
         (W : TypingEnvCoherent tenv) \
         (G : ListType KExpr) (G2 : ListType KExpr) (s : Nat -> KExpr) \
         (hs : SubstTyping tenv G2 s G) (A : KExpr) (i : Nat) => \
         Nat.rec \
         (fun (m : Nat) => forall (A2 : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) m) \
         (OptionType.some KExpr A2) -> \
         TypingCtxConv tenv (ListType.cons KExpr (psubst s A) G2) (up s m) \
         (psubst (up s) (lift_at A2 Nat.zero (Nat.succ m)))) \
         (fun (A2 : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) Nat.zero) \
         (OptionType.some KExpr A2)) => \
         Eq.substType KExpr \
         (fun (X : KExpr) => TypingCtxConv tenv (ListType.cons KExpr (psubst s A) G2) \
         (up s Nat.zero) (psubst (up s) (lift_at X Nat.zero {s0}))) \
         A A2 (option_some_inj KExpr A A2 hlk) \
         (Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv (ListType.cons KExpr (psubst s A) G2) \
         (KExpr.bvar Nat.zero) z) \
         (lift_at (psubst s A) Nat.zero {s0}) \
         (psubst (up s) (lift_at A Nat.zero {s0})) \
         (Eq.symm KExpr (psubst (up s) (lift_at A Nat.zero {s0})) \
         (lift_at (psubst s A) Nat.zero {s0}) \
         (psubst_up_lift A s)) \
         (TypingCtxConv.var tenv (ListType.cons KExpr (psubst s A) G2) Nat.zero \
         (psubst s A) \
         (Eq.refl (OptionType KExpr) (OptionType.some KExpr (psubst s A)))))) \
         (fun (j : Nat) (_ih : forall (A2 : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) j) \
         (OptionType.some KExpr A2) -> \
         TypingCtxConv tenv (ListType.cons KExpr (psubst s A) G2) (up s j) \
         (psubst (up s) (lift_at A2 Nat.zero (Nat.succ j)))) \
         (A2 : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) (Nat.succ j)) \
         (OptionType.some KExpr A2)) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv (ListType.cons KExpr (psubst s A) G2) \
         (up s (Nat.succ j)) z) \
         (lift_at (psubst s (lift_at A2 Nat.zero (Nat.succ j))) Nat.zero {s0}) \
         (psubst (up s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (Eq.symm KExpr \
         (psubst (up s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (lift_at (psubst s (lift_at A2 Nat.zero (Nat.succ j))) Nat.zero {s0}) \
         (Eq.trans KExpr \
         (psubst (up s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (psubst (up s) (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0})) \
         (lift_at (psubst s (lift_at A2 Nat.zero (Nat.succ j))) Nat.zero {s0}) \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => psubst (up s) x) \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ j))) \
         (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0}) \
         (Eq.symm KExpr \
         (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0}) \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ j))) \
         (lift_at_compose A2 Nat.zero (Nat.succ j) {s0}))) \
         (psubst_up_lift (lift_at A2 Nat.zero (Nat.succ j)) s))) \
         (weaken1 tenv hf W G2 (s j) (psubst s (lift_at A2 Nat.zero (Nat.succ j))) \
         (hs j A2 hlk) (psubst s A))) \
         i"
    )
}

/// The `subst_typing_scons` proof term: index split via Nat.rec; both cases
/// close with psubst_cancel.
fn subst_typing_scons_value() -> String {
    let s0 = "(Nat.succ Nat.zero)";
    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (G : ListType KExpr) (G2 : ListType KExpr) (s : Nat -> KExpr) \
         (a : KExpr) (A : KExpr) \
         (hs : SubstTyping tenv G2 s G) \
         (ha : TypingCtxConv tenv G2 a (psubst s A)) (i : Nat) => \
         Nat.rec \
         (fun (m : Nat) => forall (A2 : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) m) \
         (OptionType.some KExpr A2) -> \
         TypingCtxConv tenv G2 (scons a s m) \
         (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ m)))) \
         (fun (A2 : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) Nat.zero) \
         (OptionType.some KExpr A2)) => \
         Eq.substType KExpr \
         (fun (X : KExpr) => TypingCtxConv tenv G2 (scons a s Nat.zero) \
         (psubst (scons a s) (lift_at X Nat.zero {s0}))) \
         A A2 (option_some_inj KExpr A A2 hlk) \
         (Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G2 a z) \
         (psubst s A) \
         (psubst (scons a s) (lift_at A Nat.zero {s0})) \
         (Eq.symm KExpr (psubst (scons a s) (lift_at A Nat.zero {s0})) (psubst s A) \
         (psubst_cancel A a s)) \
         ha)) \
         (fun (j : Nat) (_ih : forall (A2 : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) j) \
         (OptionType.some KExpr A2) -> \
         TypingCtxConv tenv G2 (scons a s j) \
         (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ j)))) \
         (A2 : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A G) (Nat.succ j)) \
         (OptionType.some KExpr A2)) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G2 (scons a s (Nat.succ j)) z) \
         (psubst s (lift_at A2 Nat.zero (Nat.succ j))) \
         (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (Eq.symm KExpr \
         (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (psubst s (lift_at A2 Nat.zero (Nat.succ j))) \
         (Eq.trans KExpr \
         (psubst (scons a s) (lift_at A2 Nat.zero (Nat.succ (Nat.succ j)))) \
         (psubst (scons a s) (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0})) \
         (psubst s (lift_at A2 Nat.zero (Nat.succ j))) \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => psubst (scons a s) x) \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ j))) \
         (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0}) \
         (Eq.symm KExpr \
         (lift_at (lift_at A2 Nat.zero (Nat.succ j)) Nat.zero {s0}) \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ j))) \
         (lift_at_compose A2 Nat.zero (Nat.succ j) {s0}))) \
         (psubst_cancel (lift_at A2 Nat.zero (Nat.succ j)) a s))) \
         (hs j A2 hlk)) \
         i"
    )
}

/// The `substitution_general` proof term: TypingCtxConv.rec generalizing the
/// target context and substitution. See the mirror for the arm strategy.
fn substitution_general_value() -> String {
    let motive = "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s e) (psubst s T))";

    let var_arm = "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         hs i A hlk)";

    let sort_arm = "(fun (G : ListType KExpr) (n : Level) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (_hs : SubstTyping tenv G2 s G) => \
         TypingCtxConv.sort tenv G2 n)";

    let pi_arm = "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (ihA : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s A) (psubst s (KExpr.sort n))) \
         (ihB : forall (G2 : ListType KExpr) (s : Nat -> KExpr), \
         SubstTyping tenv G2 s (ListType.cons KExpr A G) -> \
         TypingCtxConv tenv G2 (psubst s B) (psubst s (KExpr.sort m))) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         TypingCtxConv.pi tenv G2 (psubst s A) (psubst (up s) B) n m \
         (ihA G2 s hs) \
         (ihB (ListType.cons KExpr (psubst s A) G2) (up s) \
         (subst_typing_up tenv hf W G G2 s hs A)))";

    let lam_arm = "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (ihA : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s A) (psubst s (KExpr.sort u))) \
         (ihb : forall (G2 : ListType KExpr) (s : Nat -> KExpr), \
         SubstTyping tenv G2 s (ListType.cons KExpr A G) -> \
         TypingCtxConv tenv G2 (psubst s b) (psubst s B)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         TypingCtxConv.lam tenv G2 (psubst s A) (psubst (up s) b) (psubst (up s) B) u \
         (ihA G2 s hs) \
         (ihb (ListType.cons KExpr (psubst s A) G2) (up s) \
         (subst_typing_up tenv hf W G G2 s hs A)))";

    let app_arm = "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (ihf : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s f) (psubst s (KExpr.pi A B))) \
         (iha : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s a) (psubst s A)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G2 \
         (KExpr.app (psubst s f) (psubst s a)) z) \
         (instantiate (psubst (up s) B) (psubst s a)) \
         (psubst s (instantiate B a)) \
         (Eq.symm KExpr (psubst s (instantiate B a)) \
         (instantiate (psubst (up s) B) (psubst s a)) \
         (psubst_instantiate B a s)) \
         (TypingCtxConv.app tenv G2 (psubst s f) (psubst s a) (psubst s A) \
         (psubst (up s) B) (ihf G2 s hs) (iha G2 s hs)))";

    let const_arm = "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (_hs : SubstTyping tenv G2 s G) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G2 (KExpr.const n us) z) \
         A (psubst s A) \
         (Eq.symm KExpr (psubst s A) A (tec_tenv_psubst_closed tenv W n A hA s)) \
         (TypingCtxConv.const tenv G2 n us A hA))";

    let conv_arm = "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s e) (psubst s A)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         TypingCtxConv.conv tenv G2 (psubst s e) (psubst s A) (psubst s B) \
         (ih1 G2 s hs) \
         (def_eq_psubst (tec_delta_psubst tenv W) (tec_iota_psubst tenv W) A B hd s))";

    // let_ arm: mirror the app + lam arms — rebuild with TypingCtxConv.let_
    // over the IHs (binder premise via subst_typing_up, exactly as lam), the
    // conclusion type aligned by psubst_instantiate (exactly as app).
    let let_arm = "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (ihty : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s ty) (psubst s (KExpr.sort u))) \
         (ihv : forall (G2 : ListType KExpr) (s : Nat -> KExpr), SubstTyping tenv G2 s G -> \
         TypingCtxConv tenv G2 (psubst s v) (psubst s ty)) \
         (ihb : forall (G2 : ListType KExpr) (s : Nat -> KExpr), \
         SubstTyping tenv G2 s (ListType.cons KExpr ty G) -> \
         TypingCtxConv tenv G2 (psubst s b) (psubst s B)) \
         (G2 : ListType KExpr) (s : Nat -> KExpr) (hs : SubstTyping tenv G2 s G) => \
         Eq.substType KExpr \
         (fun (z : KExpr) => TypingCtxConv tenv G2 \
         (KExpr.let_ (psubst s ty) (psubst s v) (psubst (up s) b)) z) \
         (instantiate (psubst (up s) B) (psubst s v)) \
         (psubst s (instantiate B v)) \
         (Eq.symm KExpr (psubst s (instantiate B v)) \
         (instantiate (psubst (up s) B) (psubst s v)) \
         (psubst_instantiate B v s)) \
         (TypingCtxConv.let_ tenv G2 (psubst s ty) (psubst s v) (psubst (up s) b) \
         (psubst (up s) B) u \
         (ihty G2 s hs) (ihv G2 s hs) \
         (ihb (ListType.cons KExpr (psubst s ty) G2) (up s) \
         (subst_typing_up tenv hf W G G2 s hs ty))))";

    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (hf : RedEnvFaithful the_red_env) \
         (W : TypingEnvCoherent tenv) \
         (G0 : ListType KExpr) (b0 : KExpr) (B0 : KExpr) \
         (h0 : TypingCtxConv tenv G0 b0 B0) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G0 b0 B0 h0"
    )
}

/// The `ctx_wk_lookup` proof term: CtxWk.rec with an inner Nat.rec index split
/// in the succ arm. See the mirror's ctx_wk_lookup for the strategy.
fn ctx_wk_lookup_value() -> String {
    // Shared shapes.
    let s0 = "(Nat.succ Nat.zero)";
    // The CPS result shape at (G2, c) for source lookup (i, A).
    let kont = |g2: &str, pos: &str, a: &str, i: &str, c: &str| {
        format!(
            "(forall (A2 : KExpr), \
             Eq (OptionType KExpr) (ctx_lookup {g2} {pos}) (OptionType.some KExpr A2) -> \
             Eq KExpr (lift_at A2 Nat.zero (Nat.succ {pos})) \
             (lift_at (lift_at {a} Nat.zero (Nat.succ {i})) {c} {s0}) -> R)"
        )
    };

    let motive = format!(
        "(fun (c : Nat) (G : ListType KExpr) (G2 : ListType KExpr) (_ : CtxWk C c G G2) => \
         forall (i : Nat) (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> \
         forall (R : Type), {k} -> R)",
        k = kont("G2", "(wkpos i c)", "A", "i", "c")
    );

    // zero arm: G2 = cons C G, c = 0, wkpos i 0 = succ i.
    let zero_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (R : Type) \
         (k : {k}) => \
         k A \
         (Eq.subst Nat (fun (p : Nat) => Eq (OptionType KExpr) \
         (ctx_lookup (ListType.cons KExpr C G) p) (OptionType.some KExpr A)) \
         (Nat.succ i) (wkpos i Nat.zero) \
         (Eq.symm Nat (wkpos i Nat.zero) (Nat.succ i) (wkpos_zero i)) hlk) \
         (Eq.subst Nat (fun (p : Nat) => Eq KExpr \
         (lift_at A Nat.zero (Nat.succ p)) \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) Nat.zero {s0})) \
         (Nat.succ i) (wkpos i Nat.zero) \
         (Eq.symm Nat (wkpos i Nat.zero) (Nat.succ i) (wkpos_zero i)) \
         (Eq.symm KExpr \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) Nat.zero {s0}) \
         (lift_at A Nat.zero (Nat.succ (Nat.succ i))) \
         (lift_at_compose A Nat.zero (Nat.succ i) {s0}))))",
        k = kont(
            "(ListType.cons KExpr C G)",
            "(wkpos i Nat.zero)",
            "A",
            "i",
            "Nat.zero"
        )
    );

    // succ arm inner zero case (i = 0): the hit entry is the cons head.
    // wkpos 0 (succ c) computes to 0; A = A0 by option injectivity.
    let succ_zero_case = format!(
        "(fun (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) Nat.zero) \
         (OptionType.some KExpr A)) \
         (R : Type) \
         (k : {k}) => \
         k (lift_at A0 c {s0}) \
         (Eq.refl (OptionType KExpr) (OptionType.some KExpr (lift_at A0 c {s0}))) \
         (Eq.subst KExpr (fun (X : KExpr) => Eq KExpr \
         (lift_at (lift_at A0 c {s0}) Nat.zero {s0}) \
         (lift_at (lift_at X Nat.zero {s0}) (Nat.succ c) {s0})) \
         A0 A (option_some_inj KExpr A0 A hlk) \
         (lift_exchange_zero A0 c)))",
        k = kont(
            "(ListType.cons KExpr (lift_at A0 c (Nat.succ Nat.zero)) G2)",
            "(wkpos Nat.zero (Nat.succ c))",
            "A",
            "Nat.zero",
            "(Nat.succ c)"
        )
    );

    // succ arm inner succ case (i = succ j): recurse via the CtxWk IH.
    let succ_succ_case = format!(
        "(fun (j : Nat) (_ihm : forall (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) j) \
         (OptionType.some KExpr A) -> forall (R : Type), {kj_prev} -> R) \
         (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) (Nat.succ j)) \
         (OptionType.some KExpr A)) \
         (R : Type) \
         (k : {ks}) => \
         ih j A hlk R \
         (fun (A2 : KExpr) \
         (hlk2 : Eq (OptionType KExpr) (ctx_lookup G2 (wkpos j c)) \
         (OptionType.some KExpr A2)) \
         (heq : Eq KExpr (lift_at A2 Nat.zero (Nat.succ (wkpos j c))) \
         (lift_at (lift_at A Nat.zero (Nat.succ j)) c {s0})) => \
         k A2 \
         (Eq.subst Nat (fun (p : Nat) => Eq (OptionType KExpr) \
         (ctx_lookup (ListType.cons KExpr (lift_at A0 c {s0}) G2) p) \
         (OptionType.some KExpr A2)) \
         (Nat.succ (wkpos j c)) (wkpos (Nat.succ j) (Nat.succ c)) \
         (Eq.symm Nat (wkpos (Nat.succ j) (Nat.succ c)) (Nat.succ (wkpos j c)) \
         (wkpos_succ_succ j c)) hlk2) \
         (Eq.subst Nat (fun (p : Nat) => Eq KExpr \
         (lift_at A2 Nat.zero (Nat.succ p)) \
         (lift_at (lift_at A Nat.zero (Nat.succ (Nat.succ j))) (Nat.succ c) {s0})) \
         (Nat.succ (wkpos j c)) (wkpos (Nat.succ j) (Nat.succ c)) \
         (Eq.symm Nat (wkpos (Nat.succ j) (Nat.succ c)) (Nat.succ (wkpos j c)) \
         (wkpos_succ_succ j c)) \
         (Eq.trans KExpr \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ (wkpos j c)))) \
         (lift_at (lift_at A2 Nat.zero (Nat.succ (wkpos j c))) Nat.zero {s0}) \
         (lift_at (lift_at A Nat.zero (Nat.succ (Nat.succ j))) (Nat.succ c) {s0}) \
         (Eq.symm KExpr \
         (lift_at (lift_at A2 Nat.zero (Nat.succ (wkpos j c))) Nat.zero {s0}) \
         (lift_at A2 Nat.zero (Nat.succ (Nat.succ (wkpos j c)))) \
         (lift_at_compose A2 Nat.zero (Nat.succ (wkpos j c)) {s0})) \
         (Eq.trans KExpr \
         (lift_at (lift_at A2 Nat.zero (Nat.succ (wkpos j c))) Nat.zero {s0}) \
         (lift_at (lift_at (lift_at A Nat.zero (Nat.succ j)) c {s0}) Nat.zero {s0}) \
         (lift_at (lift_at A Nat.zero (Nat.succ (Nat.succ j))) (Nat.succ c) {s0}) \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x Nat.zero {s0}) \
         (lift_at A2 Nat.zero (Nat.succ (wkpos j c))) \
         (lift_at (lift_at A Nat.zero (Nat.succ j)) c {s0}) heq) \
         (Eq.trans KExpr \
         (lift_at (lift_at (lift_at A Nat.zero (Nat.succ j)) c {s0}) Nat.zero {s0}) \
         (lift_at (lift_at (lift_at A Nat.zero (Nat.succ j)) Nat.zero {s0}) (Nat.succ c) {s0}) \
         (lift_at (lift_at A Nat.zero (Nat.succ (Nat.succ j))) (Nat.succ c) {s0}) \
         (lift_exchange_zero (lift_at A Nat.zero (Nat.succ j)) c) \
         (Eq.cong KExpr KExpr (fun (x : KExpr) => lift_at x (Nat.succ c) {s0}) \
         (lift_at (lift_at A Nat.zero (Nat.succ j)) Nat.zero {s0}) \
         (lift_at A Nat.zero (Nat.succ (Nat.succ j))) \
         (lift_at_compose A Nat.zero (Nat.succ j) {s0}))))))))",
        kj_prev = kont(
            "(ListType.cons KExpr (lift_at A0 c (Nat.succ Nat.zero)) G2)",
            "(wkpos j (Nat.succ c))",
            "A",
            "j",
            "(Nat.succ c)"
        ),
        ks = kont(
            "(ListType.cons KExpr (lift_at A0 c (Nat.succ Nat.zero)) G2)",
            "(wkpos (Nat.succ j) (Nat.succ c))",
            "A",
            "(Nat.succ j)",
            "(Nat.succ c)"
        )
    );

    // succ arm: split the source index with Nat.rec.
    let succ_arm = format!(
        "(fun (c : Nat) (A0 : KExpr) (G : ListType KExpr) (G2 : ListType KExpr) \
         (_hwk : CtxWk C c G G2) \
         (ih : forall (i : Nat) (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A) -> \
         forall (R : Type), {kih} -> R) => \
         fun (i : Nat) => Nat.rec \
         (fun (m : Nat) => forall (A : KExpr), \
         Eq (OptionType KExpr) (ctx_lookup (ListType.cons KExpr A0 G) m) \
         (OptionType.some KExpr A) -> \
         forall (R : Type), {km} -> R) \
         {succ_zero_case} \
         {succ_succ_case} \
         i)",
        kih = kont("G2", "(wkpos i c)", "A", "i", "c"),
        km = kont(
            "(ListType.cons KExpr (lift_at A0 c (Nat.succ Nat.zero)) G2)",
            "(wkpos m (Nat.succ c))",
            "A",
            "m",
            "(Nat.succ c)"
        )
    );

    format!(
        "fun (C : KExpr) (c0 : Nat) (G0 : ListType KExpr) (G20 : ListType KExpr) \
         (hwk0 : CtxWk C c0 G0 G20) => \
         CtxWk.rec C {motive} {zero_arm} {succ_arm} c0 G0 G20 hwk0"
    )
}

/// The `weaken_gen` proof term: TypingCtxConv.rec with a cutoff-generalized,
/// CtxWk-carrying motive. See the mirror's weaken_gen for the strategy.
fn weaken_gen_value() -> String {
    let s0 = "(Nat.succ Nat.zero)";
    let motive = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (T : KExpr) \
         (_ : TypingCtxConv tenv G e T) => \
         forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at e c {s0}) (lift_at T c {s0}))"
    );

    // var arm: transport the looked-up entry across the weakening.
    let var_arm = format!(
        "(fun (G : ListType KExpr) (i : Nat) (A : KExpr) \
         (hlk : Eq (OptionType KExpr) (ctx_lookup G i) (OptionType.some KExpr A)) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         ctx_wk_lookup C c G G2 hwk i A hlk \
         (TypingCtxConv tenv G2 (lift_at (KExpr.bvar i) c {s0}) \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) c {s0})) \
         (fun (A2 : KExpr) \
         (hlk2 : Eq (OptionType KExpr) (ctx_lookup G2 (wkpos i c)) \
         (OptionType.some KExpr A2)) \
         (heq : Eq KExpr (lift_at A2 Nat.zero (Nat.succ (wkpos i c))) \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) c {s0})) => \
         Eq.substType KExpr \
         (fun (x : KExpr) => TypingCtxConv tenv G2 x \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) c {s0})) \
         (KExpr.bvar (wkpos i c)) (lift_at (KExpr.bvar i) c {s0}) \
         (Eq.symm KExpr (lift_at (KExpr.bvar i) c {s0}) (KExpr.bvar (wkpos i c)) \
         (lift_at_bvar_wkpos i c)) \
         (Eq.substType KExpr \
         (fun (T : KExpr) => TypingCtxConv tenv G2 (KExpr.bvar (wkpos i c)) T) \
         (lift_at A2 Nat.zero (Nat.succ (wkpos i c))) \
         (lift_at (lift_at A Nat.zero (Nat.succ i)) c {s0}) \
         heq \
         (TypingCtxConv.var tenv G2 (wkpos i c) A2 hlk2))))"
    );

    let sort_arm = "(fun (G : ListType KExpr) (n : Level) \
         (c : Nat) (G2 : ListType KExpr) (_hwk : CtxWk C c G G2) => \
         TypingCtxConv.sort tenv G2 n)"
        .to_string();

    let pi_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (B : KExpr) (n : Level) (m : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort n)) \
         (_hB : TypingCtxConv tenv (ListType.cons KExpr A G) B (KExpr.sort m)) \
         (ihA : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at A c {s0}) (lift_at (KExpr.sort n) c {s0})) \
         (ihB : forall (c : Nat) (G2 : ListType KExpr), \
         CtxWk C c (ListType.cons KExpr A G) G2 -> \
         TypingCtxConv tenv G2 (lift_at B c {s0}) (lift_at (KExpr.sort m) c {s0})) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         TypingCtxConv.pi tenv G2 (lift_at A c {s0}) (lift_at B (Nat.succ c) {s0}) n m \
         (ihA c G2 hwk) \
         (ihB (Nat.succ c) (ListType.cons KExpr (lift_at A c {s0}) G2) \
         (CtxWk.succ C c A G G2 hwk)))"
    );

    let lam_arm = format!(
        "(fun (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level) \
         (_hA : TypingCtxConv tenv G A (KExpr.sort u)) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr A G) b B) \
         (ihA : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at A c {s0}) (lift_at (KExpr.sort u) c {s0})) \
         (ihb : forall (c : Nat) (G2 : ListType KExpr), \
         CtxWk C c (ListType.cons KExpr A G) G2 -> \
         TypingCtxConv tenv G2 (lift_at b c {s0}) (lift_at B c {s0})) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         TypingCtxConv.lam tenv G2 (lift_at A c {s0}) (lift_at b (Nat.succ c) {s0}) \
         (lift_at B (Nat.succ c) {s0}) u \
         (ihA c G2 hwk) \
         (ihb (Nat.succ c) (ListType.cons KExpr (lift_at A c {s0}) G2) \
         (CtxWk.succ C c A G G2 hwk)))"
    );

    let app_arm = format!(
        "(fun (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr) \
         (_hf : TypingCtxConv tenv G f (KExpr.pi A B)) \
         (_ha : TypingCtxConv tenv G a A) \
         (ihf : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at f c {s0}) (lift_at (KExpr.pi A B) c {s0})) \
         (iha : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at a c {s0}) (lift_at A c {s0})) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         Eq.substType KExpr \
         (fun (T : KExpr) => TypingCtxConv tenv G2 \
         (KExpr.app (lift_at f c {s0}) (lift_at a c {s0})) T) \
         (instantiate (lift_at B (Nat.succ c) {s0}) (lift_at a c {s0})) \
         (lift_at (instantiate B a) c {s0}) \
         (Eq.symm KExpr \
         (lift_at (instantiate B a) c {s0}) \
         (instantiate (lift_at B (Nat.succ c) {s0}) (lift_at a c {s0})) \
         (lift_instantiate_zero B a c)) \
         (TypingCtxConv.app tenv G2 (lift_at f c {s0}) (lift_at a c {s0}) \
         (lift_at A c {s0}) (lift_at B (Nat.succ c) {s0}) \
         (ihf c G2 hwk) (iha c G2 hwk)))"
    );

    let const_arm = format!(
        "(fun (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) \
         (hA : Eq (OptionType KExpr) (tenv n) (OptionType.some KExpr A)) \
         (c : Nat) (G2 : ListType KExpr) (_hwk : CtxWk C c G G2) => \
         Eq.substType KExpr \
         (fun (T : KExpr) => TypingCtxConv tenv G2 (KExpr.const n us) T) \
         A (lift_at A c {s0}) \
         (Eq.symm KExpr (lift_at A c {s0}) A \
         (tec_tenv_lift_closed tenv W n A hA c {s0})) \
         (TypingCtxConv.const tenv G2 n us A hA))"
    );

    let conv_arm = format!(
        "(fun (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr) \
         (_h1 : TypingCtxConv tenv G e A) (hd : DefEq A B) \
         (ih1 : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at e c {s0}) (lift_at A c {s0})) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         TypingCtxConv.conv tenv G2 (lift_at e c {s0}) (lift_at A c {s0}) \
         (lift_at B c {s0}) \
         (ih1 c G2 hwk) \
         (def_eq_respects_lift_at_gen A B {s0} hf hd c))"
    );

    // let_ arm: ty and v lift at the cutoff, b and B under the binder (the
    // lam treatment); the dependent conclusion type transports along
    // lift_instantiate_zero exactly as the app arm.
    let let_arm = format!(
        "(fun (G : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) \
         (B : KExpr) (u : Level) \
         (_hty : TypingCtxConv tenv G ty (KExpr.sort u)) \
         (_hv : TypingCtxConv tenv G v ty) \
         (_hb : TypingCtxConv tenv (ListType.cons KExpr ty G) b B) \
         (ihty : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at ty c {s0}) (lift_at (KExpr.sort u) c {s0})) \
         (ihv : forall (c : Nat) (G2 : ListType KExpr), CtxWk C c G G2 -> \
         TypingCtxConv tenv G2 (lift_at v c {s0}) (lift_at ty c {s0})) \
         (ihb : forall (c : Nat) (G2 : ListType KExpr), \
         CtxWk C c (ListType.cons KExpr ty G) G2 -> \
         TypingCtxConv tenv G2 (lift_at b c {s0}) (lift_at B c {s0})) \
         (c : Nat) (G2 : ListType KExpr) (hwk : CtxWk C c G G2) => \
         Eq.substType KExpr \
         (fun (T : KExpr) => TypingCtxConv tenv G2 \
         (KExpr.let_ (lift_at ty c {s0}) (lift_at v c {s0}) \
         (lift_at b (Nat.succ c) {s0})) T) \
         (instantiate (lift_at B (Nat.succ c) {s0}) (lift_at v c {s0})) \
         (lift_at (instantiate B v) c {s0}) \
         (Eq.symm KExpr \
         (lift_at (instantiate B v) c {s0}) \
         (instantiate (lift_at B (Nat.succ c) {s0}) (lift_at v c {s0})) \
         (lift_instantiate_zero B v c)) \
         (TypingCtxConv.let_ tenv G2 (lift_at ty c {s0}) (lift_at v c {s0}) \
         (lift_at b (Nat.succ c) {s0}) (lift_at B (Nat.succ c) {s0}) u \
         (ihty c G2 hwk) (ihv c G2 hwk) \
         (ihb (Nat.succ c) (ListType.cons KExpr (lift_at ty c {s0}) G2) \
         (CtxWk.succ C c ty G G2 hwk))))"
    );

    format!(
        "fun (tenv : Name -> OptionType KExpr) \
         (hf : RedEnvFaithful the_red_env) \
         (W : TypingEnvCoherent tenv) \
         (C : KExpr) (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) \
         (h0 : TypingCtxConv tenv G0 e0 T0) => \
         TypingCtxConv.rec tenv {motive} \
         {var_arm} {sort_arm} {pi_arm} {lam_arm} {app_arm} {const_arm} {conv_arm} \
         {let_arm} \
         G0 e0 T0 h0"
    )
}

#[cfg(test)]
#[path = "subject_reduction_bundle_tests.rs"]
mod subject_reduction_bundle_tests;

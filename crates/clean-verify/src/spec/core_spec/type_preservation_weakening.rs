// Copyright 2026 Andrew Yates.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Weakening (lift preserves typing) — the third structural metatheorem of the
//! reflected typing judgment, alongside substitution typing
//! (`type_preservation_subst.rs`) and forward subject reduction
//! (`beta_reduces_preserves_typing.rs`).
//!
//! ## What this proves
//!
//! `weakening_typing_gen`:
//!   `has_type e T -> forall c, has_type (lift_at e c amount) (lift_at T c amount)`
//!
//! i.e. inserting `amount` fresh de Bruijn variables at ANY cutoff `c` preserves
//! typing, with both the term and its type lifted in lockstep. `weakening_typing`
//! specializes to cutoff 0 (the `lift` alias), the "add fresh variables at the
//! front of the context" form.
//!
//! ## Structure — the Aristotle `weakening_typing.lean` skeleton mapped onto the
//! REAL dependent typing rules.
//!
//! The banked Aristotle guide states weakening over a MINIMAL (STLC-shaped)
//! typing judgment. This proof re-derives it over clean-verify's ACTUAL reflected
//! kernel typing (`Typing`), which is dependent (`Typing.app`'s result is
//! `instantiate B a`), universe-aware (`Typing.pi`/`Typing.lam` carry Sort
//! levels), and has an untyped conversion rule (`Typing.conv` on raw `DefEq`).
//! The proof is a single `Typing.rec` induction whose motive universalizes the
//! cutoff `c` (so binder arms may recurse at `Nat.succ c`), mirroring the
//! `substitution_typing_gen` template case-for-case but with `lift_at` /
//! `lift_at_*` in place of `instantiate_at` / `instantiate_at_*`:
//!
//!   - sort : transport `Typing.sort n` through `lift_at_sort` on both sides.
//!   - pi   : `Typing.pi` at cutoff `c` and `Nat.succ c` (the codomain binder),
//!            IHs transported via `lift_at_sort`, source/result via `lift_at_pi`
//!            / `lift_at_sort`.
//!   - lam  : `Typing.lam` mirror of pi (`lift_at_lam`; the body IH lands its
//!            type directly, no transport).
//!   - app  : the DEPENDENT arm. `Typing.app` on the lifted pieces yields result
//!            `instantiate (lift_at B0 (succ c) amount) (lift_at a0 c amount)`; the
//!            lift/instantiate interchange `lift_instantiate_swap` (at d=0, k=c,
//!            a=amount, modulo `nat_zero_add` on the `0+c` cutoffs) rewrites the
//!            motive target `lift_at (instantiate B0 a0) c amount` to it.
//!   - conv : `Typing.conv` on the lifted subject, its raw `DefEq` obligation
//!            discharged by `def_eq_respects_lift_at_gen` (the cutoff-general lift
//!            congruence) at the ambient cutoff.
//!
//! ## Guards — ZERO new axioms, genuinely DerivedProved.
//!
//! Every definition here is `is_axiom: false` with a full `value_src`. The conv
//! arm rests on `def_eq_respects_lift_at_gen`, which is DerivedProved with an
//! EMPTY kernel debt closure — so, unlike `substitution_typing_gen` (whose conv
//! arm rides `def_eq_respects_subst_at`'s pending frontier), this lemma inherits
//! NO pending leaf and is a genuine DerivedProved with zero non-foundational
//! debt. The carried `RedEnvFaithful the_red_env` is a HYPOTHESIS threaded into
//! `def_eq_respects_lift_at_gen` (an interface, not an axiom; the env is the
//! literal `the_red_env`). Additive: does not touch any existing definition.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// `Typing.rec` preamble: outer binders + motive (universalizing the cutoff).
const WEAK_PROOF_PREAMBLE: &str = concat!(
    "fun (e : KExpr) (T : KExpr) (amount : Nat) (c : Nat) ",
    "(hf : RedEnvFaithful the_red_env) (ht : Typing e T) => ",
    "Typing.rec ",
    "(fun (e0 : KExpr) (T0 : KExpr) (_ : Typing e0 T0) => ",
    "forall (c0 : Nat), ",
    "Typing (lift_at e0 c0 amount) (lift_at T0 c0 amount)) ",
);

/// sort arm: transport `Typing.sort n` through `lift_at_sort` (both sides).
const WEAK_SORT_CASE: &str = concat!(
    "(fun (n : Level) (c0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (lift_at (KExpr.sort (Level.succ n)) c0 amount)) ",
    "(KExpr.sort n) (lift_at (KExpr.sort n) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.sort n) c0 amount) (KExpr.sort n) ",
    "(lift_at_sort n c0 amount)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.sort n) y) ",
    "(KExpr.sort (Level.succ n)) (lift_at (KExpr.sort (Level.succ n)) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.sort (Level.succ n)) c0 amount) ",
    "(KExpr.sort (Level.succ n)) (lift_at_sort (Level.succ n) c0 amount)) ",
    "(Typing.sort n))) ",
);

/// pi arm: `Typing.pi` with IHs at `c0` / `Nat.succ c0`, transported via
/// `lift_at_pi` / `lift_at_sort`.
const WEAK_PI_CASE: &str = concat!(
    "(fun (A0 : KExpr) (B0 : KExpr) (n : Level) (m : Level) ",
    "(_hA0 : Typing A0 (KExpr.sort n)) (_hB0 : Typing B0 (KExpr.sort m)) ",
    "(ih_A0 : forall (c2 : Nat), Typing (lift_at A0 c2 amount) ",
    "(lift_at (KExpr.sort n) c2 amount)) ",
    "(ih_B0 : forall (c2 : Nat), Typing (lift_at B0 c2 amount) ",
    "(lift_at (KExpr.sort m) c2 amount)) ",
    "(c0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (lift_at (KExpr.sort (Level.imax n m)) c0 amount)) ",
    "(KExpr.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount)) ",
    "(lift_at (KExpr.pi A0 B0) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.pi A0 B0) c0 amount) ",
    "(KExpr.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount)) ",
    "(lift_at_pi A0 B0 c0 amount)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.pi (lift_at A0 c0 amount) ",
    "(lift_at B0 (Nat.succ c0) amount)) y) ",
    "(KExpr.sort (Level.imax n m)) (lift_at (KExpr.sort (Level.imax n m)) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.sort (Level.imax n m)) c0 amount) ",
    "(KExpr.sort (Level.imax n m)) (lift_at_sort (Level.imax n m) c0 amount)) ",
    "(Typing.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount) n m ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (lift_at A0 c0 amount) y) ",
    "(lift_at (KExpr.sort n) c0 amount) (KExpr.sort n) ",
    "(lift_at_sort n c0 amount) (ih_A0 c0)) ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (lift_at B0 (Nat.succ c0) amount) y) ",
    "(lift_at (KExpr.sort m) (Nat.succ c0) amount) (KExpr.sort m) ",
    "(lift_at_sort m (Nat.succ c0) amount) (ih_B0 (Nat.succ c0)))))) ",
);

/// lam arm: `Typing.lam` mirror of pi via `lift_at_lam`; the body IH lands its
/// type directly.
const WEAK_LAM_CASE: &str = concat!(
    "(fun (A0 : KExpr) (b0 : KExpr) (B0 : KExpr) (u0 : Level) ",
    "(_hA0 : Typing A0 (KExpr.sort u0)) (_hb0 : Typing b0 B0) ",
    "(ih_A0 : forall (c2 : Nat), Typing (lift_at A0 c2 amount) ",
    "(lift_at (KExpr.sort u0) c2 amount)) ",
    "(ih_b0 : forall (c2 : Nat), Typing (lift_at b0 c2 amount) ",
    "(lift_at B0 c2 amount)) ",
    "(c0 : Nat) => ",
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (lift_at (KExpr.pi A0 B0) c0 amount)) ",
    "(KExpr.lam (lift_at A0 c0 amount) (lift_at b0 (Nat.succ c0) amount)) ",
    "(lift_at (KExpr.lam A0 b0) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.lam A0 b0) c0 amount) ",
    "(KExpr.lam (lift_at A0 c0 amount) (lift_at b0 (Nat.succ c0) amount)) ",
    "(lift_at_lam A0 b0 c0 amount)) ",
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.lam (lift_at A0 c0 amount) ",
    "(lift_at b0 (Nat.succ c0) amount)) y) ",
    "(KExpr.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount)) ",
    "(lift_at (KExpr.pi A0 B0) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.pi A0 B0) c0 amount) ",
    "(KExpr.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount)) ",
    "(lift_at_pi A0 B0 c0 amount)) ",
    "(Typing.lam (lift_at A0 c0 amount) (lift_at b0 (Nat.succ c0) amount) ",
    "(lift_at B0 (Nat.succ c0) amount) u0 ",
    "(Eq.substType KExpr (fun (y : KExpr) => Typing (lift_at A0 c0 amount) y) ",
    "(lift_at (KExpr.sort u0) c0 amount) (KExpr.sort u0) ",
    "(lift_at_sort u0 c0 amount) (ih_A0 c0)) ",
    "(ih_b0 (Nat.succ c0))))) ",
);

/// app arm (dependent): `Typing.app` on lifted pieces, result type re-established
/// via the lift/instantiate interchange `lift_instantiate_swap` (d=0, k=c0,
/// a=amount) with the `0+c0 -> c0` cutoff rewrites carried by `nat_zero_add`.
const WEAK_APP_CASE: &str = concat!(
    "(fun (f0 : KExpr) (a0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
    "(_hf0 : Typing f0 (KExpr.pi A0 B0)) (_ha0 : Typing a0 A0) ",
    "(ih_f0 : forall (c2 : Nat), Typing (lift_at f0 c2 amount) ",
    "(lift_at (KExpr.pi A0 B0) c2 amount)) ",
    "(ih_a0 : forall (c2 : Nat), Typing (lift_at a0 c2 amount) ",
    "(lift_at A0 c2 amount)) ",
    "(c0 : Nat) => ",
    // Outer transport: source via lift_at_app.
    "Eq.substType KExpr ",
    "(fun (x : KExpr) => Typing x (lift_at (instantiate B0 a0) c0 amount)) ",
    "(KExpr.app (lift_at f0 c0 amount) (lift_at a0 c0 amount)) ",
    "(lift_at (KExpr.app f0 a0) c0 amount) ",
    "(Eq.symm KExpr (lift_at (KExpr.app f0 a0) c0 amount) ",
    "(KExpr.app (lift_at f0 c0 amount) (lift_at a0 c0 amount)) ",
    "(lift_at_app f0 a0 c0 amount)) ",
    // Inner transport: result type via the lift/instantiate swap (built below).
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (KExpr.app (lift_at f0 c0 amount) ",
    "(lift_at a0 c0 amount)) y) ",
    "(instantiate (lift_at B0 (Nat.succ c0) amount) (lift_at a0 c0 amount)) ",
    "(lift_at (instantiate B0 a0) c0 amount) ",
    "(Eq.symm KExpr ",
    "(lift_at (instantiate B0 a0) c0 amount) ",
    "(instantiate (lift_at B0 (Nat.succ c0) amount) (lift_at a0 c0 amount)) ",
    // TARGET : Eq (lift_at (instantiate B0 a0) c0 amount)
    //             (instantiate (lift_at B0 (succ c0) amount) (lift_at a0 c0 amount))
    // = Eq.trans eqL (Eq.trans SWAP eqR), rewriting `Nat.add Nat.zero c0 -> c0`.
    "(Eq.trans KExpr ",
    "(lift_at (instantiate_at B0 a0 Nat.zero) c0 amount) ",
    "(lift_at (instantiate_at B0 a0 Nat.zero) (Nat.add Nat.zero c0) amount) ",
    "(instantiate_at (lift_at B0 (Nat.succ c0) amount) (lift_at a0 c0 amount) Nat.zero) ",
    // eqL : Eq L_tgt L_gen (cong on the cutoff arg, c0 = 0+c0)
    "(Eq.cong Nat KExpr ",
    "(fun (nn : Nat) => lift_at (instantiate_at B0 a0 Nat.zero) nn amount) ",
    "c0 (Nat.add Nat.zero c0) ",
    "(Eq.symm Nat (Nat.add Nat.zero c0) c0 (nat_zero_add c0))) ",
    // Eq.trans SWAP eqR : Eq L_gen R_tgt
    "(Eq.trans KExpr ",
    "(lift_at (instantiate_at B0 a0 Nat.zero) (Nat.add Nat.zero c0) amount) ",
    "(instantiate_at (lift_at B0 (Nat.succ (Nat.add Nat.zero c0)) amount) ",
    "(lift_at a0 c0 amount) Nat.zero) ",
    "(instantiate_at (lift_at B0 (Nat.succ c0) amount) (lift_at a0 c0 amount) Nat.zero) ",
    // SWAP : Eq L_gen R_gen
    "(lift_instantiate_swap B0 a0 Nat.zero c0 amount) ",
    // eqR : Eq R_gen R_tgt (cong on the binder-shift arg, 0+c0 = c0)
    "(Eq.cong Nat KExpr ",
    "(fun (nn : Nat) => instantiate_at (lift_at B0 (Nat.succ nn) amount) ",
    "(lift_at a0 c0 amount) Nat.zero) ",
    "(Nat.add Nat.zero c0) c0 (nat_zero_add c0))))) ",
    // Typing.app on the lifted pieces.
    "(Typing.app (lift_at f0 c0 amount) (lift_at a0 c0 amount) ",
    "(lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount) ",
    // Transport f0 IH via lift_at_pi.
    "(Eq.substType KExpr ",
    "(fun (y : KExpr) => Typing (lift_at f0 c0 amount) y) ",
    "(lift_at (KExpr.pi A0 B0) c0 amount) ",
    "(KExpr.pi (lift_at A0 c0 amount) (lift_at B0 (Nat.succ c0) amount)) ",
    "(lift_at_pi A0 B0 c0 amount) ",
    "(ih_f0 c0)) ",
    // a0 IH directly.
    "(ih_a0 c0)))) ",
);

/// conv arm: `Typing.conv` on the lifted subject; the raw `DefEq` obligation is
/// discharged by `def_eq_respects_lift_at_gen` at the ambient cutoff.
const WEAK_CONV_CASE: &str = concat!(
    "(fun (e0 : KExpr) (A0 : KExpr) (B0 : KExpr) ",
    "(_he0 : Typing e0 A0) (eq0 : DefEq A0 B0) ",
    "(ih_e0 : forall (c2 : Nat), Typing (lift_at e0 c2 amount) ",
    "(lift_at A0 c2 amount)) ",
    "(c0 : Nat) => ",
    "Typing.conv (lift_at e0 c0 amount) ",
    "(lift_at A0 c0 amount) (lift_at B0 c0 amount) ",
    "(ih_e0 c0) ",
    "(def_eq_respects_lift_at_gen A0 B0 amount hf eq0 c0)) ",
);

/// `Typing.rec` epilogue: indices + major premise + the motive cutoff `c`.
const WEAK_PROOF_EPILOGUE: &str = "e T ht c";

fn weakening_typing_gen_proof() -> String {
    format!(
        "{preamble}{sort}{pi}{lam}{app}{conv}{epilogue}",
        preamble = WEAK_PROOF_PREAMBLE,
        sort = WEAK_SORT_CASE,
        pi = WEAK_PI_CASE,
        lam = WEAK_LAM_CASE,
        app = WEAK_APP_CASE,
        conv = WEAK_CONV_CASE,
        epilogue = WEAK_PROOF_EPILOGUE,
    )
}

impl Specification {
    /// Register weakening (lift preserves typing) over the reflected `Typing`
    /// judgment.
    ///
    /// MUST be staged AFTER `add_type_preservation` (Typing.rec + the `Typing.*`
    /// constructors) and AFTER `add_def_eq_lift_congr_lemmas`
    /// (`def_eq_respects_lift_at_gen`). The lift structural lemmas
    /// (`lift_at_sort`/`_app`/`_lam`/`_pi`), `lift_instantiate_swap`, and
    /// `nat_zero_add` are registered earlier in the expr-model / foundation
    /// bundles.
    pub(super) fn add_type_preservation_weakening(&mut self) -> Result<(), SpecError> {
        self.add_weakening_typing_gen()?;
        self.add_weakening_typing()?;
        Ok(())
    }

    fn add_weakening_typing_gen(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "weakening_typing_gen".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (T : KExpr) (amount : Nat) (c : Nat), ",
                "RedEnvFaithful the_red_env -> ",
                "has_type e T -> ",
                "has_type (lift_at e c amount) (lift_at T c amount)"
            )
            .to_string(),
            value_src: Some(weakening_typing_gen_proof()),
            is_axiom: false,
            description: concat!(
                "Weakening / lift preservation (cutoff-general): if e : T then ",
                "(lift_at e c amount) : (lift_at T c amount) for EVERY cutoff c — inserting ",
                "`amount` fresh de Bruijn variables at cutoff c preserves typing, term and type ",
                "lifted in lockstep. By Typing.rec (motive universalizes the cutoff): sort/pi/lam ",
                "transport through lift_at_sort/pi/lam; the DEPENDENT app arm re-establishes the ",
                "result type via lift_instantiate_swap (+ nat_zero_add cutoff rewrites); the conv ",
                "arm rides def_eq_respects_lift_at_gen. DerivedProved, zero non-foundational debt ",
                "(the conv arm's def_eq_respects_lift_at_gen is itself empty-debt DerivedProved — ",
                "weakening inherits NO pending leaf, and since #3221 neither does ",
                "substitution_typing_gen). Carries ",
                "RedEnvFaithful the_red_env as a hypothesis (Guard 4 interface, not an axiom). ",
                "Third structural metatheorem of the reflected typing judgment (Aristotle ",
                "weakening_typing skeleton mapped onto the full dependent typing)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Typing.rec".to_string(),
                "Typing.sort".to_string(),
                "Typing.pi".to_string(),
                "Typing.lam".to_string(),
                "Typing.app".to_string(),
                "Typing.conv".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "lift_at".to_string(),
                "lift_at_sort".to_string(),
                "lift_at_app".to_string(),
                "lift_at_lam".to_string(),
                "lift_at_pi".to_string(),
                "lift_instantiate_swap".to_string(),
                "nat_zero_add".to_string(),
                "def_eq_respects_lift_at_gen".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "imax_nat".to_string(),
                "the_red_env".to_string(),
                "RedEnvFaithful".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    fn add_weakening_typing(&mut self) -> Result<(), SpecError> {
        // Cutoff-0 specialization using the `lift` alias (lift e amount =
        // lift_at e Nat.zero amount): weakening at the front of the context.
        self.add_definition(SpecDefinition {
            name: "weakening_typing".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (T : KExpr) (amount : Nat), ",
                "RedEnvFaithful the_red_env -> ",
                "has_type e T -> ",
                "has_type (lift e amount) (lift T amount)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (T : KExpr) (amount : Nat) ",
                    "(hf : RedEnvFaithful the_red_env) (ht : has_type e T) => ",
                    "weakening_typing_gen e T amount Nat.zero hf ht"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Weakening / lift preservation at cutoff 0: if e : T then ",
                "(lift e amount) : (lift T amount). Specializes weakening_typing_gen to cutoff ",
                "Nat.zero (lift e amount = lift_at e Nat.zero amount). DerivedProved, zero ",
                "non-foundational debt (inherits from weakening_typing_gen)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "weakening_typing_gen".to_string(),
                "lift".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }
}

#[cfg(test)]
#[path = "type_preservation_weakening_tests.rs"]
mod type_preservation_weakening_tests;

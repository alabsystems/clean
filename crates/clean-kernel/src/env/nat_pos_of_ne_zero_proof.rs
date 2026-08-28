// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The positivity bridge `Nat.pos_of_ne_zero`, as an axiom-free proved theorem.
//!
//! ```text
//! Nat.pos_of_ne_zero : ∀ (n : Nat), Not (@Eq Nat n Nat.zero) → Nat.lt Nat.zero n
//! ```
//!
//! **Binder divergence, deliberate and gated.** Lean 4 core spells this
//! `{n : Nat}` (implicit). Clean registers `n` EXPLICIT with the side condition
//! last, matching the convention its only consumer already uses — `Nat.mod_lt`,
//! which diverges from Lean's `(x : Nat) {y : Nat}` in exactly the same way.
//! Because the `.olean` loader dedups by name, the divergent form is WITHHELD
//! in import mode so the genuine canonical theorem can register through the
//! checked import path; see the gate in `register_nat_pos_of_ne_zero`.
//!
//! # Why it exists
//!
//! `Nat.mod_lt : ∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n`
//! (`data_types_nat_div_mod_lemmas.rs`) is the decrease every `gcd`-shaped
//! well-founded recursion needs, and its side condition is POSITIVITY. A source
//! program that tests `b == 0` never produces `0 < b` directly — the negative
//! branch of the test yields a *disequality*. Without a route from `n ≠ 0` to
//! `0 < n` the decrease is underivable, which is exactly why the verbatim
//! Bool-test spelling
//!
//! ```text
//! def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)
//! ```
//!
//! stayed refused after the multi-parameter well-founded lowering landed.
//!
//! # Proof
//!
//! Case analysis on `n` via `@Nat.rec.{0}` (Prop motive), with
//! `motive := fun t => Not (@Eq Nat t Nat.zero) → Nat.lt Nat.zero t`:
//!
//! * **`Nat.zero`** — the hypothesis is `Not (@Eq Nat Nat.zero Nat.zero)`, which
//!   is refuted by `@Eq.refl.{1} Nat Nat.zero`; the goal follows by
//!   `@False.elim.{0}`. (This is the only branch that uses the hypothesis, and
//!   it uses it to derive `False` — so the theorem is vacuous exactly where it
//!   should be.)
//! * **`Nat.succ k`** — the goal `Nat.lt Nat.zero (Nat.succ k)` holds outright;
//!   the hypothesis is discarded. Witness: `Nat.zero_lt_succ k`, itself a
//!   constructive `Declaration::Theorem` (`nat_top_level_ordering_proof.rs`,
//!   #3599), stated in the `LT.lt`/`instLTNat` typeclass form which is
//!   definitionally the raw `Nat.lt` form used here.
//!
//! # Closure
//!
//! `Nat.rec`, `Eq.refl`, `False.elim`, `Not` and `Nat.zero_lt_succ` are all
//! kernel primitives or constructive theorems, so `env.axiom_deps` is EMPTY —
//! foundational-only, matching the standard this file's neighbours hold
//! themselves to. An `axiom` here would be a trust-root escape; the module test
//! below and `clean-elab/tests/r4_gcd_bool_spelling_e2e.rs` both assert it is
//! not one.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Nat.pos_of_ne_zero` as a constructive `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Nat.lt`, `Eq.refl`,
    /// `False.elim`, `Not` and `Nat.zero_lt_succ` are registered — the first
    /// eight by prelude core, the last by `init_nat_top_level_ordering`, which
    /// this function calls itself.
    ///
    /// ENSURES: On success `Nat.pos_of_ne_zero` is present as a proof-carrying
    /// `Theorem` with an empty domain-specific axiom closure.
    /// ENSURES: Idempotent — a no-op if the constant already exists.
    /// ENSURES: A no-op in import mode — see the gate below.
    pub(crate) fn register_nat_pos_of_ne_zero(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS / IMPORT MODE (`suppress_lossy_structure_stubs`): this is a
        // BINDER-divergent spelling of a genuine Lean 4 core name. Lean has
        // `theorem Nat.pos_of_ne_zero {n : Nat} : n ≠ 0 → 0 < n` with `n`
        // IMPLICIT; Clean registers it with the value argument EXPLICIT and the
        // side condition last, matching the local convention its only consumer
        // uses (`Nat.mod_lt` in `data_types_nat_div_mod_lemmas.rs` diverges from
        // Lean the same way, and is import-gated for the same reason).
        //
        // The `.olean` loader dedups by NAME, so registering the divergent form
        // first would SHADOW the genuine canonical theorem and mask every
        // imported proof that applies it with the implicit convention. Withhold
        // it in import mode and let the real one register through the checked
        // import path. SOUNDNESS-NEUTRAL: this only WITHHOLDS a Clean-native
        // theorem; the non-import lane is unchanged. Downstream this is
        // fail-closed by construction — the well-founded discharge cascade
        // (`clean-elab/.../wf_recursion/decreasing.rs::positivity_candidates`)
        // probes for the constant and simply offers fewer candidates when it is
        // absent, so the Bool-test lane refuses rather than misbehaving.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.pos_of_ne_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // `Nat.zero_lt_succ` in its constructive Theorem form.
        self.init_nat_top_level_ordering()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let zero_lt_succ = Expr::const_(Name::from_string("Nat.zero_lt_succ"), vec![]);
        // `Nat.rec.{0}` — Prop motive. `Eq`/`Eq.refl` at `Sort 1` (Nat : Type).
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
        let l1 = Level::succ(Level::zero());
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);

        // `Not (@Eq Nat t Nat.zero)` — the shape a `dite`'s negative branch
        // binds, so the elaborator can pass such a hypothesis straight in.
        let ne_zero = |t: &Expr| {
            Expr::app(
                not_c.clone(),
                Expr::apps(eq_c.clone(), [nat.clone(), t.clone(), nat_zero.clone()]),
            )
        };
        let pos = |t: &Expr| Expr::apps(nat_lt.clone(), [nat_zero.clone(), t.clone()]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());

        // Type: ∀ (n : Nat), Not (@Eq Nat n Nat.zero) → Nat.lt Nat.zero n
        let type_ = {
            let hyp = ne_zero(&n);
            let inner = {
                let (h_id, _h) = b.fresh_local(hyp.clone());
                b.mk_pi(h_id, BinderInfo::Default, hyp.clone(), pos(&n))
            };
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), inner);
            b.finish(e)
        };

        // motive : fun (t : Nat) => Not (@Eq Nat t Nat.zero) → Nat.lt Nat.zero t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat.clone());
            let hyp = ne_zero(&t);
            let (h_id, _h) = mb.fresh_local(hyp.clone());
            let inner = mb.mk_pi(h_id, BinderInfo::Default, hyp, pos(&t));
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat.clone(), inner);
            mb.finish_child(lam)
        };

        // base : motive Nat.zero
        //      = fun (h : Not (@Eq Nat Nat.zero Nat.zero)) =>
        //          @False.elim.{0} (Nat.lt Nat.zero Nat.zero)
        //                          (h (@Eq.refl.{1} Nat Nat.zero))
        let base = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let hyp = ne_zero(&nat_zero);
            let (h_id, h) = cb.fresh_local(hyp.clone());
            let refl = Expr::apps(eq_refl.clone(), [nat.clone(), nat_zero.clone()]);
            let absurd = Expr::app(h, refl);
            let body = Expr::apps(false_elim.clone(), [pos(&nat_zero), absurd]);
            let lam = cb.mk_lam(h_id, BinderInfo::Default, hyp, body);
            cb.finish_child(lam)
        };

        // step : fun (k : Nat) (_ih : motive k) =>
        //          fun (_h : Not (@Eq Nat (Nat.succ k) Nat.zero)) => Nat.zero_lt_succ k
        //
        // `Nat.zero_lt_succ k : LT.lt @Nat instLTNat Nat.zero (Nat.succ k)`,
        // definitionally the raw `Nat.lt Nat.zero (Nat.succ k)` the motive asks
        // for (`instLTNat` and `Nat.lt` are both reducible).
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat.clone());
            let succ_k = Expr::app(nat_succ.clone(), k.clone());
            let ih_ty = {
                let hyp = ne_zero(&k);
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (hh_id, _hh) = ib.fresh_local(hyp.clone());
                ib.finish_child(ib.mk_pi(hh_id, BinderInfo::Default, hyp, pos(&k)))
            };
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let hyp = ne_zero(&succ_k);
            let (h_id, _h) = sb.fresh_local(hyp.clone());
            let body = Expr::app(zero_lt_succ.clone(), k.clone());
            let lam_h = sb.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam_h);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // value : fun (n : Nat) => @Nat.rec.{0} motive base step n
        let value = {
            let rec_app = Expr::apps(nat_rec, [motive, base, step, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), rec_app);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn nat_pos_of_ne_zero_is_a_proved_axiom_free_theorem() {
        let mut env = Environment::with_prelude();
        env.register_nat_pos_of_ne_zero().expect("register");
        env.register_nat_pos_of_ne_zero().expect("idempotent");

        let n = Name::from_string("Nat.pos_of_ne_zero");
        let c = env.get_const(&n).expect("registered");
        assert_eq!(c.kind, ConstantKind::Theorem, "must not be an axiom");
        assert!(c.value.is_some(), "must carry its proof term");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _inferred = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .expect("Nat.pos_of_ne_zero should type-check");

        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(ToString::to_string).collect();
        assert!(
            names.is_empty(),
            "Nat.pos_of_ne_zero must be axiom-free, got {names:?}"
        );
    }

    /// The import-mode gate actually gates. Without this the withholding is a
    /// comment rather than a behaviour, and the divergent binder convention
    /// would silently shadow the genuine Lean `Nat.pos_of_ne_zero` on the
    /// `.olean` lane.
    #[test]
    fn nat_pos_of_ne_zero_is_withheld_in_import_mode() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        let n = Name::from_string("Nat.pos_of_ne_zero");
        assert!(
            env.get_const(&n).is_none(),
            "import mode must WITHHOLD the binder-divergent spelling so the \
             genuine olean theorem can register through the checked path"
        );
        // And an explicit call is still a no-op there, not a back door.
        env.register_nat_pos_of_ne_zero()
            .expect("gated registration must succeed as a no-op");
        assert!(
            env.get_const(&n).is_none(),
            "the gate must not be bypassable"
        );
    }

    /// CONTROL: the default (non-import) lane DOES carry it, so the gate above
    /// is not passing because the theorem never registers anywhere.
    #[test]
    fn nat_pos_of_ne_zero_is_present_on_the_default_lane() {
        let env = Environment::with_prelude();
        assert!(
            env.get_const(&Name::from_string("Nat.pos_of_ne_zero"))
                .is_some(),
            "with_prelude must carry the positivity bridge"
        );
    }
}

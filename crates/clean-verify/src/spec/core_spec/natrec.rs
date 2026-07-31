// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat.rec spec port — batch N0: the concrete Nat recursor instantiated into
//! the generic `RecEnv`/`RecMeta`/`RecRule` framework (`rec_env.rs`).
//!
//! The first OBJECT-level inductive with a real typed dependent recursor. This
//! batch registers the Nat constant heads (`natTypeC`/`natZeroC`/`natSuccC`/
//! `natRecC`), the real dependent recursor type (`natRecTy`), the two
//! recursor-rule RHS lambdas (`natRecRhsZero`/`natRecRhsSucc`), the argument-order
//! metadata (`natRecMeta`), the two rules (`natRecRules`), and the Nat recursor
//! environment (`natREnv`) — the schematic `RecEnv` INSTANTIATED with Nat.
//!
//! Transcribed from `scratch/aristotle-harvest/aristotle-sn-natrec2/aristotle-sn-natrec2_aristotle/SnNatRec2.lean`
//! §4b (1029-1134). That file is the SUCCESSOR of the original `SnNatRec.lean`
//! and is byte-identical to it through line 1640, so this cited span is
//! unchanged — but it is NOT a superset: `SnNatRec2` completed the one `sorry`
//! (`onePlusOne_whnfAcc`) while DROPPING 45 declarations, chiefly the
//! parallel-substitution layer (`psubst_*`), the `betaSteps_*` congruences, and
//! the `whnfAcc_*`/`whnfStep_lam_inv` inversion lemmas. Both files are in-tree;
//! consult `aristotle-sn-natrec/.../SnNatRec.lean` for anything in that set.
//! Faithful to `clean-kernel/src/inductive/mod.rs` (Nat.rec). Const-level
//! instantiation is not modeled (documented base deviation): the development is
//! parametric in a FIXED motive universe `u`. Census-neutral (all `def`s).
//!
//! Batches N1-N4 have SINCE LANDED: N1 = `NatRecContract` +
//! `natRecContract_steps` (iota realization); N2 = the `NatFresh`/`NatRecEnvOK`
//! gates (here) plus the SN-model Nat iota-closure law (`RedNatRec` /
//! `redNatRec_holds` in `dependent_sn_richmodel.rs`, now DERIVED from the
//! generic `redRecGen` CandModel field); N3 = `natRec_adequacy_numeral`;
//! N4 = `whnf_terminates_well_typed_nat` + `onePlusOne_computes`.
//! See `designs/2026-07-11-natrec-spec-port-plan.md`.

use crate::spec::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Nat.rec OBJECT prefix (task #30, Batch 0 ordering split): the Nat names /
    /// constants / recursor type / natREnv / natRecApp / the iota-fire rfls /
    /// NatRecContract / NatRecEnvOK. Registered by its OWN bundle stage ahead of
    /// add_dependent_sn_richmodel so the CandModel `redNatRec` field (added there)
    /// can reference NatRecContract/NatRecEnvOK/natRecApp. Consumes only early
    /// stages (RecEnv, iota_step, recmeta_for/recrule_for) — no psubst calculus.
    pub(super) fn add_natrec_objects(&mut self) -> Result<(), SpecError> {
        // ── The Nat object-level names (interned as `str anonymous k` towers,
        // matching the kernel's real-name → Name convention used by the_red_env).
        // natName = str anonymous 0; zero/succ/rec = str natName 0/1/2.
        self.add_recursive_def(
            "def natName : Name := Name.str Name.anonymous Nat.zero",
            "Nat inductive type name (str anonymous 0). Nat.rec port N0.",
        )?;
        self.add_recursive_def(
            "def zeroName : Name := Name.str natName Nat.zero",
            "Nat.zero constructor name (str natName 0). Nat.rec port N0.",
        )?;
        self.add_recursive_def(
            "def succName : Name := Name.str natName (Nat.succ Nat.zero)",
            "Nat.succ constructor name (str natName 1). Nat.rec port N0.",
        )?;
        self.add_recursive_def(
            "def recName : Name := Name.str natName (Nat.succ (Nat.succ Nat.zero))",
            "Nat.rec recursor name (str natName 2). Nat.rec port N0.",
        )?;

        // ── The Nat constant heads (opaque consts; their reduction behaviour is
        // supplied by the RecEnv iota rules, not a DefEnv value).
        self.add_recursive_def(
            "def natTypeC : KExpr := KExpr.const natName (ListType.nil Level)",
            "Nat : the object-level type constant. Nat.rec port N0.",
        )?;
        self.add_recursive_def(
            "def natZeroC : KExpr := KExpr.const zeroName (ListType.nil Level)",
            "Nat.zero constant. Nat.rec port N0.",
        )?;
        self.add_recursive_def(
            "def natSuccC : KExpr := KExpr.const succName (ListType.nil Level)",
            "Nat.succ constant. Nat.rec port N0.",
        )?;
        // Nat.rec.{u} carries its ONE level parameter (the motive universe).
        self.add_recursive_def(
            "def natRecC (u : Level) : KExpr := KExpr.const recName (ListType.cons Level u (ListType.nil Level))",
            "Nat.rec.{u} constant (carries the motive-universe level param u). Nat.rec port N0.",
        )?;

        // ── The recursor type components.
        // motive type: Π Nat. sort u  (the {C : Nat → Sort u} binder, explicit).
        self.add_recursive_def(
            "def natMotiveTy (u : Level) : KExpr := KExpr.pi natTypeC (KExpr.sort u)",
            "Nat.rec motive type Nat -> Sort u. Nat.rec port N0.",
        )?;
        // succ-minor arm (n : Nat) -> C n -> C (succ n), authored under [C, z].
        // de Bruijn under [C, z]: after `Π Nat.` n=bvar0; inside `Π (C n).` the
        // motive C is bvar 2 (ctx [C,z,n]); the body's C is bvar 3, n is bvar 1
        // (ctx [C,z,n,(C n)]).
        self.add_recursive_def(
            "def natRecSArm : KExpr := KExpr.pi natTypeC (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))))",
            "Nat.rec succ-minor arm (n : Nat) -> C n -> C (succ n), under [C, z]. Nat.rec port N0.",
        )?;
        // THE REAL DEPENDENT RECURSOR TYPE (binder order C, z, s, t):
        //   Π (C : Π Nat. sort u). Π (app C zero). Π (sArm). Π Nat. app C t
        // codomain `app (bvar 3) (bvar 0)` = C t (dependent: motive at the major).
        self.add_recursive_def(
            "def natRecTy (u : Level) : KExpr := KExpr.pi (natMotiveTy u) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.pi natTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))",
            "Nat.rec dependent recursor type (C, z, s, t binders). Nat.rec port N0.",
        )?;

        // ── The recursor-rule RHS lambdas (the kernel's pre-built reducts).
        // zero rule rhs: fun C z s => z   (0 ctor fields; z = bvar 1 under [C,z,s]).
        self.add_recursive_def(
            "def natRecRhsZero (u : Level) : KExpr := KExpr.lam (natMotiveTy u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero))))",
            "Nat.rec zero-rule rhs: fun C z s => z. Nat.rec port N0.",
        )?;
        // succ rule rhs: fun C z s n => s n (Nat.rec C z s n)   (1 ctor field).
        // under [C,z,s,n]: s=bvar1, n=bvar0, C=bvar3, z=bvar2.
        self.add_recursive_def(
            "def natRecRhsSucc (u : Level) : KExpr := KExpr.lam (natMotiveTy u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.lam natTypeC (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecC u) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))))",
            "Nat.rec succ-rule rhs: fun C z s n => s n (Nat.rec C z s n). Nat.rec port N0.",
        )?;

        // ── Argument-order metadata: num_params=0, num_motives=1, num_minors=2,
        // num_indices=0, major_after_minors=true (RecursorArgOrder::MajorAfterMinors).
        self.add_recursive_def(
            "def natRecMeta : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero)) Nat.zero Bool.true",
            "Nat.rec arg-order metadata (0 params, 1 motive, 2 minors, 0 indices, major-after-minors). Nat.rec port N0.",
        )?;
        // The two rules, one per constructor.
        self.add_recursive_def(
            "def natRecRules (u : Level) : RecRules := RecRules.cons (RecRule.mk zeroName Nat.zero (natRecRhsZero u)) (RecRules.cons (RecRule.mk succName (Nat.succ Nat.zero) (natRecRhsSucc u)) RecRules.nil)",
            "Nat.rec recursor rules (zero: 0 fields, succ: 1 field). Nat.rec port N0.",
        )?;
        // The Nat recursor environment: the schematic RecEnv INSTANTIATED with Nat.
        self.add_recursive_def(
            "def natREnv (u : Level) : RecEnv := RecEnv.addRec RecEnv.empty recName natRecMeta (natRecRules u)",
            "Nat recursor environment (schematic RecEnv instantiated with Nat.rec). Nat.rec port N0.",
        )?;
        // The fully-applied recursor spine Nat.rec C z s t (a Neutral app spine).
        self.add_recursive_def(
            "def natRecApp (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (t : KExpr) : KExpr := KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecC u) m) z) s) t",
            "Nat.rec C z s t application spine. Nat.rec port N0.",
        )?;

        // ── N1a: the two OBJECT-LEVEL Nat.rec computation rules (the Nat instance
        // of iota) as an inductive SPEC:
        //   natRec m z s zero     ~>  z
        //   natRec m z s (succ n) ~>  s n (natRec m z s n)
        // N1b (`natRecContract_steps`) will prove the schematic iota_reduct+beta
        // machinery REALIZES this relation.
        self.add_inductive(
            r"inductive NatRecContract (u : Level) : KExpr -> KExpr -> Type
| zero : forall (m : KExpr) (z : KExpr) (s : KExpr), NatRecContract u (natRecApp u m z s natZeroC) z
| succ : forall (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr), NatRecContract u (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app s n) (natRecApp u m z s n))",
            "NatRecContract u lhs rhs: the object-level Nat.rec iota computation rules \
             (zero -> z; succ n -> s n (natRec .. n)). The SPEC that natRecContract_steps \
             (N1b) proves the schematic iota_reduct realizes. Nat.rec port N1a.",
        )?;

        // ── N1b (iota half): the Nat recursor's iota ACTUALLY FIRES in the
        // schematic iota_reduct machinery, to the rule-rhs applied to the minor
        // spine — provable by rfl-computation (recmeta_for/recrule_for/apply_spine/
        // list ops all reduce). The subsequent beta-chain from the applied lambda
        // down to the contract RHS (z / s n (natRec..n)) is the WhnfSteps part
        // (natRecContract_steps, farmed as SnNatRec). These two are the genuine
        // computational-fidelity core: Nat.rec's object-level iota is real, not
        // asserted. Zero axiom_deps (Eq.refl).
        self.add_recursive_def(
            "def natREnv_iota_zero (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) : iota_step (natREnv u) (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s))",
            "Nat.rec iota fires on a zero major: iota_step (natREnv u) (natRec m z s zero) ((natRecRhsZero u) m z s), by rfl-computation. Nat.rec port N1b-iota.",
        )?;
        self.add_recursive_def(
            "def natREnv_iota_succ (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) : iota_step (natREnv u) (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n))",
            "Nat.rec iota fires on a succ major: iota_step (natREnv u) (natRec m z s (succ n)) ((natRecRhsSucc u) m z s n), by rfl-computation. Nat.rec port N1b-iota.",
        )?;

        // ── N3-gate: NatFresh (denv δ-freshness). denv δ-defines NONE of the four
        // Nat names, i.e. every defval_for = none. Together with NatRecEnvOK it
        // gates the CandModel redNatRec field (N3/N4) vacuous over adversarial
        // δ-environments that bind the Nat names. Now buildable: add_natrec_objects
        // runs AFTER add_delta_step_core (defval_for), so the old deferral is lifted.
        self.add_inductive(
            "inductive NatFresh : DefEnv -> Type\n| mk : forall (denv : DefEnv), Eq (OptionType KExpr) (defval_for denv natName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv zeroName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv succName) (OptionType.none KExpr) -> Eq (OptionType KExpr) (defval_for denv recName) (OptionType.none KExpr) -> NatFresh denv",
            "NatFresh denv: denv δ-defines none of Nat/zero/succ/rec (all defval_for = none). Freshness gate keeping the model redNatRec field vacuous over adversarial δ-envs. Nat.rec port N3-gate.",
        )?;
        // ── N2 (gate): NatRecEnvOK (renv really carries the Nat.rec recursor data).
        self.add_inductive(
            "inductive NatRecEnvOK : Level -> RecEnv -> Type\n| mk : forall (u : Level) (renv : RecEnv), Eq (OptionType RecMeta) (recmeta_for renv recName) (OptionType.some RecMeta natRecMeta) -> Eq (OptionType RecRule) (recrule_for renv recName zeroName) (OptionType.some RecRule (RecRule.mk zeroName Nat.zero (natRecRhsZero u))) -> Eq (OptionType RecRule) (recrule_for renv recName succName) (OptionType.some RecRule (RecRule.mk succName (Nat.succ Nat.zero) (natRecRhsSucc u))) -> NatRecEnvOK u renv",
            "NatRecEnvOK u renv: renv carries the Nat.rec metadata + both rules. Gates the model redNatRec field vacuous off non-Nat envs. Nat.rec port N2.",
        )?;
        // natREnv actually satisfies NatRecEnvOK — the three fields hold by rfl
        // (recmeta_for/recrule_for on natREnv compute to the Nat.rec data).
        // Non-vacuity: the Nat recursor env is real. Zero axiom_deps.
        self.add_recursive_def(
            "def natREnv_recEnvOK (u : Level) : NatRecEnvOK u (natREnv u) := NatRecEnvOK.mk u (natREnv u) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta natRecMeta)) (Eq.refl (OptionType RecRule) (OptionType.some RecRule (RecRule.mk zeroName Nat.zero (natRecRhsZero u)))) (Eq.refl (OptionType RecRule) (OptionType.some RecRule (RecRule.mk succName (Nat.succ Nat.zero) (natRecRhsSucc u))))",
            "natREnv satisfies NatRecEnvOK, by rfl: recmeta_for/recrule_for on natREnv compute to the Nat.rec metadata + rules. The Nat recursor env is real. Nat.rec port N2.",
        )?;

        // ── X15 ι-LIVENESS INSTANCES over the 3-way step: the Nat recursor on a
        // constructor-headed major ALWAYS takes a whnf_red_step, for ANY
        // definition environment paired with natREnv and ANY motive/minors —
        // the in-spec sibling of the Aristotle-proved natrec_fires, lifted
        // from the natREnv_iota_zero/succ rfl-witnesses through the ι arm
        // (red_rec (RedEnv.mk r d) computes to r).
        self.add_recursive_def(
            "def natrec_fires_red_zero (u : Level) (d : DefEnv) (m : KExpr) (z : KExpr) (s : KExpr) : whnf_red_step (RedEnv.mk (natREnv u) d) (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) := whnf_red_step.iota (RedEnv.mk (natREnv u) d) (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (natREnv_iota_zero u m z s)",
            "ι-LIVENESS (X15, Nat instance, zero major): for ANY definition environment and ANY motive/minors, the Nat recursor applied to the zero constructor takes a whnf_red_step — the natREnv_iota_zero rfl-witness through the ι arm. The in-spec natrec_fires (zero case).",
        )?;
        self.add_recursive_def(
            "def natrec_fires_red_succ (u : Level) (d : DefEnv) (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) : whnf_red_step (RedEnv.mk (natREnv u) d) (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) := whnf_red_step.iota (RedEnv.mk (natREnv u) d) (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) (natREnv_iota_succ u m z s n)",
            "ι-LIVENESS (X15, Nat instance, succ major): for ANY definition environment and ANY motive/minors and ANY major tail n, the Nat recursor applied to succ n takes a whnf_red_step — the natREnv_iota_succ rfl-witness through the ι arm. The in-spec natrec_fires (succ case).",
        )?;

        Ok(())
    }

    /// Nat.rec RELATION + β-chain + N4-demo half (task #30). Kept AFTER
    /// add_dependent_sn_richmodel: the β-chain uses its psubst calculus
    /// (psubst / scons / up / instantiate_eq_psubst / psubst_scons_instantiate).
    /// The Nat OBJECTS it consumes are registered earlier by add_natrec_objects.
    pub(super) fn add_natrec(&mut self) -> Result<(), SpecError> {
        // ── N1b (relation): the Nat.rec-specific weak-head reduction relation.
        // ARCHITECTURE DECISION (option c): the spec's par_reduces/iota_reduces are
        // hardwired to the single the_red_env recursor, so rather than entangle Nat.rec
        // with that (or generalize par_reduces over RecEnv), the Nat.rec port carries
        // its OWN reduction relation — natStep = (iota over natREnv) ∪ beta — and its
        // reflexive-transitive closure natSteps. Mirrors the guide's WhnfSteps. Self-
        // contained; connects to the SN/adequacy layer later.
        // iotaCong = one-hole congruence closure of the object-level iota_step over
        // natREnv (head iota + app_left/app_right congruences). This is what lets an
        // iota fire in a subterm position — e.g. the inner recursor of `succ (Nat.rec
        // .. 0)` collapsing to a numeral. The guide's BetaReduces unifies beta+iota in
        // ONE congruence; the port keeps beta_reduces (already congruent) as its own
        // leg and adds this iota congruence, so natStep = iotaCong ∪ beta_reduces.
        self.add_inductive(
            "inductive iotaCong (u : Level) : KExpr -> KExpr -> Type\n| head : forall (e : KExpr) (e2 : KExpr), iota_step (natREnv u) e e2 -> iotaCong u e e2\n| app_left : forall (f : KExpr) (f2 : KExpr) (a : KExpr), iotaCong u f f2 -> iotaCong u (KExpr.app f a) (KExpr.app f2 a)\n| app_right : forall (f : KExpr) (a : KExpr) (a2 : KExpr), iotaCong u a a2 -> iotaCong u (KExpr.app f a) (KExpr.app f a2)",
            "iotaCong u e e2: one-hole congruence closure of object-level iota over natREnv (head + app congruences). Lets iota fire under an application spine. Nat.rec port N1b/N4-demo.",
        )?;
        self.add_inductive(
            "inductive natStep (u : Level) : KExpr -> KExpr -> Type\n| iota : forall (e : KExpr) (e2 : KExpr), iotaCong u e e2 -> natStep u e e2\n| beta : forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> natStep u e e2",
            "natStep u e e2: one Nat.rec weak-head step — object-level iota (congruent) over natREnv, or a beta/congruence step. Nat.rec port N1b.",
        )?;
        self.add_inductive(
            "inductive natSteps (u : Level) : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), natSteps u e e\n| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), natStep u e e2 -> natSteps u e2 e3 -> natSteps u e e3",
            "natSteps u e e3: reflexive-transitive closure of natStep (multi-step Nat.rec reduction). Nat.rec port N1b.",
        )?;
        // Lift the verified iota-fire (N1b-iota) into the reduction relation: the
        // Nat.rec spine at a numeral major takes a natStep to the rule-rhs spine.
        self.add_recursive_def(
            "def natStep_iota_zero (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) : natStep u (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) := natStep.iota u (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (iotaCong.head u (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (natREnv_iota_zero u m z s))",
            "Nat.rec zero major takes a natStep (iota) to (natRecRhsZero u) m z s. Nat.rec port N1b.",
        )?;
        self.add_recursive_def(
            "def natStep_iota_succ (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) : natStep u (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) := natStep.iota u (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) (iotaCong.head u (natRecApp u m z s (KExpr.app natSuccC n)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n) (natREnv_iota_succ u m z s n))",
            "Nat.rec succ major takes a natStep (iota) to (natRecRhsSucc u) m z s n. Nat.rec port N1b.",
        )?;

        // ── N1b-full (β-chain foundation): a beta redex reduces to the psubst
        // form of its body — beta_reduces (app (lam A body) arg) (psubst (scons arg
        // idsubst) body). Ported from SnNatRec.lean (`rw [← instantiate_eq_psubst];
        // beta`): beta_reduces.beta gives instantiate body arg, rewritten to
        // psubst (scons arg idsubst) body via instantiate_eq_psubst. The psubst form
        // lets the β-chain compose symbolically (avoiding hand-computed instantiate
        // intermediates). Zero axiom_deps. Needs psubst calculus (why add_natrec
        // moved after add_dependent_sn_richmodel).
        self.add_recursive_def(
            "def betaReduces_psubst (A : KExpr) (body : KExpr) (arg : KExpr) : beta_reduces (KExpr.app (KExpr.lam A body) arg) (psubst (scons arg idsubst) body) := Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (KExpr.lam A body) arg) w) (instantiate body arg) (psubst (scons arg idsubst) body) (instantiate_eq_psubst body arg) (beta_reduces.beta A body arg)",
            "betaReduces_psubst: beta_reduces (app (lam A body) arg) (psubst (scons arg idsubst) body), the β-chain foundation (beta.beta transported along instantiate_eq_psubst). Nat.rec port N1b-full.",
        )?;
        // psubst_scons_up: psubst (scons a idsubst) (psubst (up s) b) = psubst
        // (scons a s) b — the substitution-composition step that folds each β-step's
        // psubst back into a single accumulating substitution. Both sides equal
        // instantiate (psubst (up s) b) a (symm instantiate_eq_psubst / symm
        // psubst_scons_instantiate). Ported from SnNatRec.lean. Zero axiom_deps.
        self.add_recursive_def(
            "def psubst_scons_up (a : KExpr) (b : KExpr) (s : Nat -> KExpr) : Eq KExpr (psubst (scons a idsubst) (psubst (up s) b)) (psubst (scons a s) b) := Eq.trans KExpr (psubst (scons a idsubst) (psubst (up s) b)) (instantiate (psubst (up s) b) a) (psubst (scons a s) b) (Eq.symm KExpr (instantiate (psubst (up s) b) a) (psubst (scons a idsubst) (psubst (up s) b)) (instantiate_eq_psubst (psubst (up s) b) a)) (Eq.symm KExpr (psubst (scons a s) b) (instantiate (psubst (up s) b) a) (psubst_scons_instantiate b a s))",
            "psubst_scons_up: psubst (scons a idsubst) (psubst (up s) b) = psubst (scons a s) b, the β-chain substitution-composition step. Nat.rec port N1b-full.",
        )?;

        // ── N1b-full: natRec_zero_betaSteps — the zero rule as a multi-step
        // natSteps reduction: natRec m z s zero ⟶* z. Ported from SnNatRec.lean:
        // iota (natStep_iota_zero) to (natRecRhsZero u) m z s, then 3 β-steps
        // (each betaReduces_psubst under app_left congruences, its psubst result
        // folded by psubst_scons_up), ending at psubst (scons s (scons z (scons m
        // idsubst))) (bvar 1) which is DEFEQ z (psubst σ (bvar 1) = σ 1 = z), closed
        // by natSteps.refl. Zero axiom_deps.
        let body1 = "(KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero)))";
        let body0 = format!("(KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) {body1})");
        let e1 = "(KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s)";
        let e2 = format!("(KExpr.app (KExpr.app (psubst (scons m idsubst) {body0}) z) s)");
        let e3 = format!("(KExpr.app (psubst (scons z (scons m idsubst)) {body1}) s)");
        let e4 = "(psubst (scons s (scons z (scons m idsubst))) (KExpr.bvar (Nat.succ Nat.zero)))";
        let beta1 = format!(
            "(natStep.beta u {e1} {e2} (beta_reduces.app_left (KExpr.app (KExpr.app (natRecRhsZero u) m) z) (KExpr.app (psubst (scons m idsubst) {body0}) z) s (beta_reduces.app_left (KExpr.app (natRecRhsZero u) m) (psubst (scons m idsubst) {body0}) z (betaReduces_psubst (natMotiveTy u) {body0} m))))"
        );
        let brp2 = format!(
            "(betaReduces_psubst (psubst (scons m idsubst) (KExpr.app (KExpr.bvar Nat.zero) natZeroC)) (psubst (up (scons m idsubst)) {body1}) z)"
        );
        let trans2 = format!(
            "(Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons m idsubst) {body0}) z) w) (psubst (scons z idsubst) (psubst (up (scons m idsubst)) {body1})) (psubst (scons z (scons m idsubst)) {body1}) (psubst_scons_up z {body1} (scons m idsubst)) {brp2})"
        );
        let beta2 = format!(
            "(natStep.beta u {e2} {e3} (beta_reduces.app_left (KExpr.app (psubst (scons m idsubst) {body0}) z) (psubst (scons z (scons m idsubst)) {body1}) s {trans2}))"
        );
        let brp3 = "(betaReduces_psubst (psubst (scons z (scons m idsubst)) natRecSArm) (psubst (up (scons z (scons m idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) s)";
        let trans3 = format!(
            "(Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons z (scons m idsubst)) {body1}) s) w) (psubst (scons s idsubst) (psubst (up (scons z (scons m idsubst))) (KExpr.bvar (Nat.succ Nat.zero)))) (psubst (scons s (scons z (scons m idsubst))) (KExpr.bvar (Nat.succ Nat.zero))) (psubst_scons_up s (KExpr.bvar (Nat.succ Nat.zero)) (scons z (scons m idsubst))) {brp3})"
        );
        let beta3 = format!("(natStep.beta u {e3} {e4} {trans3})");
        let natrec_zero = format!(
            "def natRec_zero_betaSteps (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) : natSteps u (natRecApp u m z s natZeroC) z := natSteps.step u (natRecApp u m z s natZeroC) {e1} z (natStep_iota_zero u m z s) (natSteps.step u {e1} {e2} z {beta1} (natSteps.step u {e2} {e3} z {beta2} (natSteps.step u {e3} {e4} z {beta3} (natSteps.refl u z))))"
        );
        self.add_recursive_def(
            &natrec_zero,
            "natRec_zero_betaSteps: natRec m z s zero ⟶* z over natSteps (iota + 3 β-steps via betaReduces_psubst/psubst_scons_up). Nat.rec port N1b-full.",
        )?;

        // ── N1b-full: natRec_succ_betaSteps — natRec m z s (succ n) ⟶* s n
        // (natRec m z s n). Same shape as zero but natRecRhsSucc is a 4-λ, so 4
        // β-steps; the final psubst (scons n (scons s (scons z (scons m idsubst))))
        // BODY is DEFEQ s n (natRec m z s n) (BODY = s n (Nat.rec C z s n) with
        // C/z/s/n = bvar 3/2/1/0 substituted).
        let s_body = "(KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecC u) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))";
        let sb2 = format!("(KExpr.lam natTypeC {s_body})");
        let sb1 = format!("(KExpr.lam natRecSArm {sb2})");
        let sb0 = format!("(KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) {sb1})");
        let se1 = "(KExpr.app (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) n)";
        let se2 =
            format!("(KExpr.app (KExpr.app (KExpr.app (psubst (scons m idsubst) {sb0}) z) s) n)");
        let se3 = format!("(KExpr.app (KExpr.app (psubst (scons z (scons m idsubst)) {sb1}) s) n)");
        let se4 = format!("(KExpr.app (psubst (scons s (scons z (scons m idsubst))) {sb2}) n)");
        let se5 = format!("(psubst (scons n (scons s (scons z (scons m idsubst)))) {s_body})");
        // β1: reduce app(natRecRhsSucc u)m under 3 app_left (z,s,n)
        let sbeta1 = format!(
            "(natStep.beta u {se1} {se2} (beta_reduces.app_left (KExpr.app (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) s) (KExpr.app (KExpr.app (psubst (scons m idsubst) {sb0}) z) s) n (beta_reduces.app_left (KExpr.app (KExpr.app (natRecRhsSucc u) m) z) (KExpr.app (psubst (scons m idsubst) {sb0}) z) s (beta_reduces.app_left (KExpr.app (natRecRhsSucc u) m) (psubst (scons m idsubst) {sb0}) z (betaReduces_psubst (natMotiveTy u) {sb0} m)))))"
        );
        // β2: under 2 app_left (s,n)
        let sbrp2 = format!("(betaReduces_psubst (psubst (scons m idsubst) (KExpr.app (KExpr.bvar Nat.zero) natZeroC)) (psubst (up (scons m idsubst)) {sb1}) z)");
        let strans2 = format!("(Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons m idsubst) {sb0}) z) w) (psubst (scons z idsubst) (psubst (up (scons m idsubst)) {sb1})) (psubst (scons z (scons m idsubst)) {sb1}) (psubst_scons_up z {sb1} (scons m idsubst)) {sbrp2})");
        let sbeta2 = format!("(natStep.beta u {se2} {se3} (beta_reduces.app_left (KExpr.app (KExpr.app (psubst (scons m idsubst) {sb0}) z) s) (KExpr.app (psubst (scons z (scons m idsubst)) {sb1}) s) n (beta_reduces.app_left (KExpr.app (psubst (scons m idsubst) {sb0}) z) (psubst (scons z (scons m idsubst)) {sb1}) s {strans2})))");
        // β3: under 1 app_left (n)
        let sbrp3 = format!("(betaReduces_psubst (psubst (scons z (scons m idsubst)) natRecSArm) (psubst (up (scons z (scons m idsubst))) {sb2}) s)");
        let strans3 = format!("(Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons z (scons m idsubst)) {sb1}) s) w) (psubst (scons s idsubst) (psubst (up (scons z (scons m idsubst))) {sb2})) (psubst (scons s (scons z (scons m idsubst))) {sb2}) (psubst_scons_up s {sb2} (scons z (scons m idsubst))) {sbrp3})");
        let sbeta3 = format!("(natStep.beta u {se3} {se4} (beta_reduces.app_left (KExpr.app (psubst (scons z (scons m idsubst)) {sb1}) s) (psubst (scons s (scons z (scons m idsubst))) {sb2}) n {strans3}))");
        // β4: no app_left
        let sbrp4 = format!("(betaReduces_psubst (psubst (scons s (scons z (scons m idsubst))) natTypeC) (psubst (up (scons s (scons z (scons m idsubst)))) {s_body}) n)");
        let strans4 = format!("(Eq.substType KExpr (fun (w : KExpr) => beta_reduces (KExpr.app (psubst (scons s (scons z (scons m idsubst))) {sb2}) n) w) (psubst (scons n idsubst) (psubst (up (scons s (scons z (scons m idsubst)))) {s_body})) (psubst (scons n (scons s (scons z (scons m idsubst)))) {s_body}) (psubst_scons_up n {s_body} (scons s (scons z (scons m idsubst)))) {sbrp4})");
        let sbeta4 = format!("(natStep.beta u {se4} {se5} {strans4})");
        let target = "(KExpr.app (KExpr.app s n) (natRecApp u m z s n))";
        let natrec_succ = format!(
            "def natRec_succ_betaSteps (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) : natSteps u (natRecApp u m z s (KExpr.app natSuccC n)) {target} := natSteps.step u (natRecApp u m z s (KExpr.app natSuccC n)) {se1} {target} (natStep_iota_succ u m z s n) (natSteps.step u {se1} {se2} {target} {sbeta1} (natSteps.step u {se2} {se3} {target} {sbeta2} (natSteps.step u {se3} {se4} {target} {sbeta3} (natSteps.step u {se4} {se5} {target} {sbeta4} (natSteps.refl u {target})))))"
        );
        self.add_recursive_def(
            &natrec_succ,
            "natRec_succ_betaSteps: natRec m z s (succ n) ⟶* s n (natRec m z s n) over natSteps (iota + 4 β-steps). Nat.rec port N1b-full.",
        )?;

        // ── N1b-full COMPLETE: natRecContract_steps — every NatRecContract step is
        // realized as a real multi-step natSteps reduction. Cases on NatRecContract
        // (via .rec), dispatching to the two β-chains. This is THE object-level
        // Nat.rec computation-fidelity theorem: the recursor's iota rules genuinely
        // reduce (iota + β) in the spec's reduction relation. Zero axiom_deps.
        self.add_recursive_def(
            "def natRecContract_steps (u : Level) (e : KExpr) (e2 : KExpr) (h : NatRecContract u e e2) : natSteps u e e2 := NatRecContract.rec u (fun (e0 : KExpr) (e0b : KExpr) (_ : NatRecContract u e0 e0b) => natSteps u e0 e0b) (fun (m : KExpr) (z : KExpr) (s : KExpr) => natRec_zero_betaSteps u m z s) (fun (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) => natRec_succ_betaSteps u m z s n) e e2 h",
            "natRecContract_steps: NatRecContract u e e2 -> natSteps u e e2 — every object-level Nat.rec iota rule is realized as a real iota+β multi-step reduction. THE Nat.rec computation-fidelity theorem. Nat.rec port N1b-full COMPLETE.",
        )?;

        // ── N4-demo (1+1 computes): natSteps transitivity + the numeral/add-one
        // encoding, toward onePlusOne_computes (concrete demo that 1+1 ⟶* 2 through
        // the object-level Nat.rec iota — a REDUCTION, not SN; no CandModel needed).
        self.add_recursive_def(
            "def natSteps_trans (u : Level) (a : KExpr) (b : KExpr) (c : KExpr) (h1 : natSteps u a b) (h2 : natSteps u b c) : natSteps u a c := natSteps.rec u (fun (a0 : KExpr) (b0 : KExpr) (_ : natSteps u a0 b0) => natSteps u b0 c -> natSteps u a0 c) (fun (e : KExpr) => fun (hc : natSteps u e c) => hc) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : natStep u e e2) (_rest : natSteps u e2 e3) (ih : natSteps u e3 c -> natSteps u e2 c) => fun (hc : natSteps u e3 c) => natSteps.step u e e2 c st (ih hc)) a b h1 h2",
            "natSteps_trans: transitivity of natSteps (via natSteps.rec). Nat.rec port N4-demo.",
        )?;
        self.add_recursive_def(
            "def natOne : KExpr := KExpr.app natSuccC natZeroC",
            "natOne = succ zero (the numeral 1). Nat.rec port N4-demo.",
        )?;
        self.add_recursive_def(
            "def natTwo : KExpr := KExpr.app natSuccC natOne",
            "natTwo = succ one (the numeral 2). Nat.rec port N4-demo.",
        )?;
        self.add_recursive_def(
            "def natConstMotive : KExpr := KExpr.lam natTypeC natTypeC",
            "natConstMotive = (fun _ : Nat => Nat), the constant motive. Nat.rec port N4-demo.",
        )?;
        self.add_recursive_def(
            "def natAddOneCase : KExpr := KExpr.lam natTypeC (KExpr.lam natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero)))",
            "natAddOneCase = (fun n ih => succ ih), the +1 step case. Nat.rec port N4-demo.",
        )?;
        self.add_recursive_def(
            "def natOnePlusOne (u : Level) : KExpr := natRecApp u natConstMotive natOne natAddOneCase natOne",
            "natOnePlusOne = Nat.rec (fun _ => Nat) 1 (fun n ih => succ ih) 1 = 1 + 1. Nat.rec port N4-demo.",
        )?;

        // app_right congruence for a single natStep: the iota leg lifts via
        // iotaCong.app_right, the beta leg via beta_reduces.app_right.
        self.add_recursive_def(
            "def natStep_app_right (u : Level) (f : KExpr) (e : KExpr) (e2 : KExpr) (h : natStep u e e2) : natStep u (KExpr.app f e) (KExpr.app f e2) := match h with\n| natStep.iota ic => natStep.iota u (KExpr.app f e) (KExpr.app f e2) (iotaCong.app_right u f e e2 ic)\n| natStep.beta br => natStep.beta u (KExpr.app f e) (KExpr.app f e2) (beta_reduces.app_right f e e2 br)",
            "natStep_app_right: one natStep lifts under an application argument (iota via iotaCong.app_right, beta via beta_reduces.app_right). Nat.rec port N4-demo.",
        )?;
        // app_right congruence for a multi-step natSteps (induct + natStep_app_right).
        self.add_recursive_def(
            "def natSteps_app_right (u : Level) (f : KExpr) (a : KExpr) (b : KExpr) (h : natSteps u a b) : natSteps u (KExpr.app f a) (KExpr.app f b) := natSteps.rec u (fun (a0 : KExpr) (b0 : KExpr) (_ : natSteps u a0 b0) => natSteps u (KExpr.app f a0) (KExpr.app f b0)) (fun (e : KExpr) => natSteps.refl u (KExpr.app f e)) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : natStep u e e2) (_rest : natSteps u e2 e3) (ih : natSteps u (KExpr.app f e2) (KExpr.app f e3)) => natSteps.step u (KExpr.app f e) (KExpr.app f e2) (KExpr.app f e3) (natStep_app_right u f e e2 st) ih) a b h",
            "natSteps_app_right: a multi-step natSteps reduction lifts under an application argument (congruence). Nat.rec port N4-demo.",
        )?;

        // onePlusOne_computes: 1 + 1 ⟶* 2 through the object-level Nat.rec iota.
        // succ-iota fires (major 1 = succ 0) → β² contracts the step case against
        // (0, ih) → succ (Nat.rec (fun _=>Nat) 1 S 0); then under the outer succ the
        // zero-iota collapses the inner recursor to 1, giving succ 1 = 2. A genuine
        // REDUCTION (iota+β multi-step); no SN / CandModel hypothesis. Non-vacuity
        // witness: the Nat.rec fidelity machinery actually computes a closed numeral.
        {
            let inner_rec = "(natRecApp u natConstMotive natOne natAddOneCase natZeroC)";
            let stepfn = "(KExpr.lam natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero)))";
            let t1 = format!("(KExpr.app (KExpr.app natAddOneCase natZeroC) {inner_rec})");
            let t2 = format!("(KExpr.app {stepfn} {inner_rec})");
            let t3 = format!("(KExpr.app natSuccC {inner_rec})");
            let one_plus_one = "(natOnePlusOne u)";
            // hA: succ-rule iota + β⁴ takes 1+1 to `(λn ih.succ ih) 0 (Nat.rec .. 0)`.
            let h_a = "(natRec_succ_betaSteps u natConstMotive natOne natAddOneCase natZeroC)";
            // β1: contract the step case `natAddOneCase` against the field 0 (n discarded).
            let beta1 = format!(
                "(natStep.beta u {t1} {t2} (beta_reduces.app_left (KExpr.app natAddOneCase natZeroC) {stepfn} {inner_rec} (beta_reduces.beta natTypeC {stepfn} natZeroC)))"
            );
            // β2: apply `λ ih. succ ih` to the inner recursor → succ (Nat.rec .. 0).
            let beta2 = format!(
                "(natStep.beta u {t2} {t3} (beta_reduces.beta natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero)) {inner_rec}))"
            );
            let s_b = format!(
                "(natSteps.step u {t1} {t2} {t3} {beta1} (natSteps.step u {t2} {t3} {t3} {beta2} (natSteps.refl u {t3})))"
            );
            // sC: under the outer succ, the zero-iota collapses the inner recursor to 1.
            let s_c = format!(
                "(natSteps_app_right u natSuccC {inner_rec} natOne (natRec_zero_betaSteps u natConstMotive natOne natAddOneCase))"
            );
            let body = format!(
                "def onePlusOne_computes (u : Level) : natSteps u (natOnePlusOne u) natTwo := natSteps_trans u {one_plus_one} {t1} natTwo {h_a} (natSteps_trans u {t1} {t3} natTwo {s_b} {s_c})"
            );
            self.add_recursive_def(
                &body,
                "onePlusOne_computes: 1 + 1 ⟶* 2 via the object-level Nat.rec iota (iota+β multi-step, zero axioms). Non-vacuity witness that the recursor fidelity machinery computes. Nat.rec port N4-demo.",
            )?;
        }

        // ── B4 (adequacy prep): IsNumeral (a closed Nat numeral) + neutral_numeral.
        // IsNumeral is Type-valued (large-eliminates into Neutral/whnf_acc/Red, all
        // Type). A numeral is natZeroC (const head) or app natSuccC n (app head);
        // Neutral computes to ConstFreeUnit on both heads, witnessed by
        // ConstFreeUnit.triv (exactly the neutral_{const,app}_witness values).
        self.add_inductive(
            "inductive IsNumeral : KExpr -> Type\n| zero : IsNumeral natZeroC\n| succ : forall (n : KExpr), IsNumeral n -> IsNumeral (KExpr.app natSuccC n)",
            "IsNumeral t: t is a closed Nat numeral (zero, or succ of a numeral). Nat.rec port B4.",
        )?;
        self.add_recursive_def(
            "def neutral_numeral (t : KExpr) (h : IsNumeral t) : Neutral t := IsNumeral.rec (fun (t0 : KExpr) (_ : IsNumeral t0) => Neutral t0) ConstFreeUnit.triv (fun (n : KExpr) (_ : IsNumeral n) (_ : Neutral n) => ConstFreeUnit.triv) t h",
            "neutral_numeral: every numeral is Neutral — its head is const (zero) or app (succ), on which Neutral computes to ConstFreeUnit (witness ConstFreeUnit.triv). Nat.rec port B4.",
        )?;

        // ── B5-precondition: the_red_env is Nat-FRESH (it δ-defines none of the four
        // Nat names — Nat's type/ctors/recursor are inductive entities, not DefEnv
        // definitions). Proven by rfl: defval_for (red_def the_red_env) NAME computes
        // to none for each. This makes whnfAcc_numeral UNCONDITIONAL over the spec's
        // fixed reduction env (confirms the static de-risking empirically).
        self.add_recursive_def(
            "def natFresh_red : NatFresh (red_def the_red_env) := NatFresh.mk (red_def the_red_env) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))",
            "natFresh_red: the_red_env δ-defines none of Nat/zero/succ/rec (defval_for (red_def the_red_env) = none, by rfl). the_red_env is Nat-fresh ⇒ whnfAcc_numeral unconditional. Nat.rec port B5-precondition.",
        )?;

        // ── B5(a): numeral_no_delta — a numeral takes NO delta step. delta_reduct
        // (red_def the_red_env) t = none for a numeral t (its head const's defval is
        // none, by natFresh_red / delta_reduct_eq_none_of_defval_none), so the
        // delta_step Eq (delta_reduct t) (some e') is Eq none (some e') = absurd.
        // Per-case (src, nm): eliminate delta_reduces (1 ctor) with a source-eq motive,
        // transport delta_reduct e0 = none along heq, contradict via option_none_ne_some.
        {
            // Use delta_reduces_to_step to extract the delta_step directly (no match /
            // rec needed); src is concrete so delta_reduct src = none discharges via
            // delta_reduct_eq_none_of_defval_none + the option_none_ne_some absurdity.
            let dnd_case = |src: &str, nm: &str| -> String {
                format!(
                    "fun (e2 : KExpr) (C : Type) (hd : delta_reduces {src} e2) => option_none_ne_some_type KExpr e2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) {src}) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) {src}) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none (red_def the_red_env) {src} {nm} (Eq.refl (OptionType Name) (OptionType.some Name {nm})) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (delta_reduces_to_step {src} e2 hd))"
                )
            };
            let zero_case = dnd_case("natZeroC", "zeroName");
            let succ_body = dnd_case("(KExpr.app natSuccC n)", "succName");
            let body = format!(
                "def numeral_no_delta (t : KExpr) (h : IsNumeral t) : forall (e2 : KExpr) (C : Type), delta_reduces t e2 -> C := IsNumeral.rec (fun (t0 : KExpr) (_ : IsNumeral t0) => forall (e2 : KExpr) (C : Type), delta_reduces t0 e2 -> C) ({zero_case}) (fun (n : KExpr) (_ : IsNumeral n) (_ : forall (e2 : KExpr) (C : Type), delta_reduces n e2 -> C) => {succ_body}) t h"
            );
            self.add_recursive_def(
                &body,
                "numeral_no_delta: a numeral admits no delta_reduces step — its head const (zero/succ) has defval_for = none (natFresh_red), so delta_reduct = none contradicts the delta_step. Nat.rec port B5(a).",
            )?;
        }

        // const_ne_let: no-confusion (no global one exists; srb_const_ne_let is local
        // to subject_reduction_bundle). KExpr.rec discriminator D = ConstFreeUnit on
        // every head except let_ (Empty); transport D (const n us)=CFU along heq to
        // D (let_ ..)=Empty, then Empty.rec. Mirrors the Neutral discriminator shape.
        self.add_recursive_def(
            "def const_ne_let (n : Name) (us : ListType Level) (lty : KExpr) (lval : KExpr) (lbody : KExpr) (C : Type) (heq : Eq KExpr (KExpr.const n us) (KExpr.let_ lty lval lbody)) : C := Empty.rec (fun (_ : Empty) => C) (Eq.rec KExpr (KExpr.const n us) (fun (x : KExpr) (_ : Eq KExpr (KExpr.const n us) x) => KExpr.rec (fun (_ : KExpr) => Type) (fun (l : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (nf : Type) (na : Type) => ConstFreeUnit) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => ConstFreeUnit) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => ConstFreeUnit) (fun (nm : Name) (uss : ListType Level) => ConstFreeUnit) (fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (nty : Type) (nv : Type) (nb : Type) => Empty) (fun (ps : Name) (pin : Nat) (psub : KExpr) (np : Type) => ConstFreeUnit) (fun (lv2 : Nat) => ConstFreeUnit) x) ConstFreeUnit.triv (KExpr.let_ lty lval lbody) heq)",
            "const_ne_let: a const is not a let_ (KExpr.rec discriminator + Eq.rec transport + Empty.rec). Nat.rec port B5(b) helper.",
        )?;

        // const_ne_proj: a const is not a proj (proj/lit fragment rung). Same
        // discriminator shape as const_ne_let (proj -> Empty, every other head ->
        // ConstFreeUnit); transport ConstFreeUnit.triv along heq to Empty, then Empty.rec.
        self.add_recursive_def(
            "def const_ne_proj (n : Name) (us : ListType Level) (ps : Name) (pin : Nat) (psub : KExpr) (C : Type) (heq : Eq KExpr (KExpr.const n us) (KExpr.proj ps pin psub)) : C := Empty.rec (fun (_ : Empty) => C) (Eq.rec KExpr (KExpr.const n us) (fun (x : KExpr) (_ : Eq KExpr (KExpr.const n us) x) => KExpr.rec (fun (_ : KExpr) => Type) (fun (l : Level) => ConstFreeUnit) (fun (i : Nat) => ConstFreeUnit) (fun (f : KExpr) (a : KExpr) (nf : Type) (na : Type) => ConstFreeUnit) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => ConstFreeUnit) (fun (ty : KExpr) (b : KExpr) (nty : Type) (nb : Type) => ConstFreeUnit) (fun (nm : Name) (uss : ListType Level) => ConstFreeUnit) (fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (nty : Type) (nv : Type) (nb : Type) => ConstFreeUnit) (fun (qs : Name) (qi : Nat) (qsub : KExpr) (nq : Type) => Empty) (fun (lv2 : Nat) => ConstFreeUnit) x) ConstFreeUnit.triv (KExpr.proj ps pin psub) heq)",
            "const_ne_proj: a const is not a proj (KExpr.rec discriminator + Eq.rec transport + Empty.rec). Proj/lit fragment rung.",
        )?;

        // ── B5(b): const_no_beta_reduces — a bare const admits NO beta_reduces step.
        // 15-case beta_reduces.rec with a source-eq motive (mirror no_whnf_step_bvar's
        // beta arm, bvar -> const): app/lam/pi/forall arms via const_ne_{app,lam,pi}
        // (forall_ is defeq pi) + Eq.symm; let arms via srb_const_ne_let + Eq.symm; the
        // iota arm via iota_reduces_to_step + iota_reduct_const_none (a bare const has
        // no iota reduct) + option_none_ne_some_type.
        {
            let cn = "(KExpr.const n us)";
            let mot = format!(
                "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {cn} -> C)"
            );
            // helper: Eq.symm of a source-eq heq (Eq S (const)) -> Eq (const) S
            let sym = |s: &str| format!("(Eq.symm KExpr {s} {cn} heq)");
            let c_beta = format!("(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {cn}) => const_ne_app n us (KExpr.lam A0 body) arg C {})", sym("(KExpr.app (KExpr.lam A0 body) arg)"));
            let c_appl = format!("(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_hstep : beta_reduces f f2) (_ih : Eq KExpr f {cn} -> C) (heq : Eq KExpr (KExpr.app f a) {cn}) => const_ne_app n us f a C {})", sym("(KExpr.app f a)"));
            let c_appr = format!("(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_hstep : beta_reduces a a2) (_ih : Eq KExpr a {cn} -> C) (heq : Eq KExpr (KExpr.app f a) {cn}) => const_ne_app n us f a C {})", sym("(KExpr.app f a)"));
            let c_lamty = format!("(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty {cn} -> C) (heq : Eq KExpr (KExpr.lam ty body) {cn}) => const_ne_lam n us ty body C {})", sym("(KExpr.lam ty body)"));
            let c_lambd = format!("(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {cn} -> C) (heq : Eq KExpr (KExpr.lam ty body) {cn}) => const_ne_lam n us ty body C {})", sym("(KExpr.lam ty body)"));
            let c_pidom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom {cn} -> C) (heq : Eq KExpr (KExpr.pi dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.pi dom body)"));
            let c_picod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {cn} -> C) (heq : Eq KExpr (KExpr.pi dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.pi dom body)"));
            let c_fadom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom {cn} -> C) (heq : Eq KExpr (KExpr.forall_ dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.forall_ dom body)"));
            let c_facod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {cn} -> C) (heq : Eq KExpr (KExpr.forall_ dom body) {cn}) => const_ne_pi n us dom body C {})", sym("(KExpr.forall_ dom body)"));
            let c_zeta = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) {cn}) => const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
            let c_letty = format!("(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty {cn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {cn}) => const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
            let c_letval = format!("(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val {cn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {cn}) => const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
            let c_letbd = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {cn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {cn}) => const_ne_let n us ty val body C {})", sym("(KExpr.let_ ty val body)"));
            // iota: transport hiota (iota_reduces e0 e02) to const via heq, then
            // iota_reduct_const_none gives iota_reduct = none, contradicting the step.
            let c_iota = format!("(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {cn}) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) {cn}) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 {cn} heq) (iota_reduct_const_none (red_rec the_red_env) n us))) (iota_reduces_to_step e0 e02 hiota)))");
            // proj (proj/lit rung): source proj ps pin sub != const, discharge via const_ne_proj + Eq.symm.
            let c_proj = format!("(fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub {cn} -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) {cn}) => const_ne_proj n us ps pin sub C {})", sym("(KExpr.proj ps pin sub)"));
            let body = format!(
                "def const_no_beta_reduces (n : Name) (us : ListType Level) (e' : KExpr) (C : Type) (hbr : beta_reduces {cn} e') : C := beta_reduces.rec {mot} {c_beta} {c_appl} {c_appr} {c_lamty} {c_lambd} {c_pidom} {c_picod} {c_fadom} {c_facod} {c_zeta} {c_letty} {c_letval} {c_letbd} {c_iota} {c_proj} {cn} e' hbr (Eq.refl KExpr {cn})"
            );
            self.add_recursive_def(
                &body,
                "const_no_beta_reduces: a bare const admits no beta_reduces step (all 15 beta_reduces ctors have app/lam/pi/forall/let/proj sources ≠ const, or an iota over a const with no reduct). Nat.rec port B5(b).",
            )?;
        }

        // ── B5(c): numeral_no_beta — a numeral admits no beta_reduces step.
        // IsNumeral induction: zero = const_no_beta_reduces (natZeroC is const zeroName);
        // succ (app natSuccC n) = a 15-case beta_reduces.rec — app-source ctors use
        // app_inj + (const_no_beta on the head / IsNumeral IH on the arg), non-app
        // sources use lam_ne_app/pi_ne_app/let_ne_app, iota via iota_reduct=none (rfl).
        {
            let asn = "(KExpr.app natSuccC n)";
            let mot = format!(
                "(fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s {asn} -> C)"
            );
            let s_beta = format!("(fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) {asn}) => const_ne_lam succName (ListType.nil Level) A0 body C (Eq.symm KExpr (KExpr.lam A0 body) natSuccC (app_inj_fst (KExpr.lam A0 body) arg natSuccC n heq)))");
            let s_appl = format!("(fun (f : KExpr) (f2 : KExpr) (a : KExpr) (hstep : beta_reduces f f2) (_ih : Eq KExpr f {asn} -> C) (heq : Eq KExpr (KExpr.app f a) {asn}) => const_no_beta_reduces succName (ListType.nil Level) f2 C (Eq.rec KExpr f (fun (x : KExpr) (_ : Eq KExpr f x) => beta_reduces x f2) hstep natSuccC (app_inj_fst f a natSuccC n heq)))");
            let s_appr = format!("(fun (f : KExpr) (a : KExpr) (a2 : KExpr) (hstep : beta_reduces a a2) (_ih : Eq KExpr a {asn} -> C) (heq : Eq KExpr (KExpr.app f a) {asn}) => ihn a2 C (Eq.rec KExpr a (fun (x : KExpr) (_ : Eq KExpr a x) => beta_reduces x a2) hstep n (app_inj_snd f a natSuccC n heq)))");
            let s_lamty = format!("(fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty {asn} -> C) (heq : Eq KExpr (KExpr.lam ty body) {asn}) => lam_ne_app ty body natSuccC n C heq)");
            let s_lambd = format!("(fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {asn} -> C) (heq : Eq KExpr (KExpr.lam ty body) {asn}) => lam_ne_app ty body natSuccC n C heq)");
            let s_pidom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom {asn} -> C) (heq : Eq KExpr (KExpr.pi dom body) {asn}) => pi_ne_app dom body natSuccC n C heq)");
            let s_picod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {asn} -> C) (heq : Eq KExpr (KExpr.pi dom body) {asn}) => pi_ne_app dom body natSuccC n C heq)");
            let s_fadom = format!("(fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hstep : beta_reduces dom dom2) (_ih : Eq KExpr dom {asn} -> C) (heq : Eq KExpr (KExpr.forall_ dom body) {asn}) => pi_ne_app dom body natSuccC n C heq)");
            let s_facod = format!("(fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {asn} -> C) (heq : Eq KExpr (KExpr.forall_ dom body) {asn}) => pi_ne_app dom body natSuccC n C heq)");
            let s_zeta = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) {asn}) => let_ne_app ty val body natSuccC n C heq)");
            let s_letty = format!("(fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hstep : beta_reduces ty ty2) (_ih : Eq KExpr ty {asn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {asn}) => let_ne_app ty val body natSuccC n C heq)");
            let s_letval = format!("(fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hstep : beta_reduces val val2) (_ih : Eq KExpr val {asn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {asn}) => let_ne_app ty val body natSuccC n C heq)");
            let s_letbd = format!("(fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hstep : beta_reduces body body2) (_ih : Eq KExpr body {asn} -> C) (heq : Eq KExpr (KExpr.let_ ty val body) {asn}) => let_ne_app ty val body natSuccC n C heq)");
            let s_iota = format!("(fun (e0 : KExpr) (e02 : KExpr) (hiota : iota_reduces e0 e02) (heq : Eq KExpr e0 {asn}) => option_none_ne_some_type KExpr e02 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.some KExpr e02) (Eq.symm (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (OptionType.none KExpr) (Eq.trans (OptionType KExpr) (iota_reduct (red_rec the_red_env) e0) (iota_reduct (red_rec the_red_env) {asn}) (OptionType.none KExpr) (Eq.cong KExpr (OptionType KExpr) (fun (x : KExpr) => iota_reduct (red_rec the_red_env) x) e0 {asn} heq) (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))) (iota_reduces_to_step e0 e02 hiota)))");
            // proj (proj/lit rung): source proj != app, discharge via proj_ne_app.
            let s_proj = format!("(fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hstep : beta_reduces sub sub2) (_ih : Eq KExpr sub {asn} -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) {asn}) => proj_ne_app ps pin sub natSuccC n C heq)");
            let succ_body = format!(
                "fun (e' : KExpr) (C : Type) (hbr : beta_reduces {asn} e') => beta_reduces.rec {mot} {s_beta} {s_appl} {s_appr} {s_lamty} {s_lambd} {s_pidom} {s_picod} {s_fadom} {s_facod} {s_zeta} {s_letty} {s_letval} {s_letbd} {s_iota} {s_proj} {asn} e' hbr (Eq.refl KExpr {asn})"
            );
            let zero_body = "fun (e' : KExpr) (C : Type) (hbr : beta_reduces natZeroC e') => const_no_beta_reduces zeroName (ListType.nil Level) e' C hbr";
            let body = format!(
                "def numeral_no_beta (t : KExpr) (h : IsNumeral t) : forall (e' : KExpr) (C : Type), beta_reduces t e' -> C := IsNumeral.rec (fun (t0 : KExpr) (_ : IsNumeral t0) => forall (e' : KExpr) (C : Type), beta_reduces t0 e' -> C) ({zero_body}) (fun (n : KExpr) (_ : IsNumeral n) (ihn : forall (e' : KExpr) (C : Type), beta_reduces n e' -> C) => {succ_body}) t h"
            );
            self.add_recursive_def(
                &body,
                "numeral_no_beta: a numeral admits no beta_reduces step (zero via const_no_beta_reduces; succ via app_inj + const_no_beta on the succ head + IsNumeral IH on the arg). Nat.rec port B5(c).",
            )?;
        }

        // ── B5(d): numeral_no_step — a numeral admits NO whnf_step. whnf_step is
        // beta ∪ delta; match dispatches to numeral_no_beta / numeral_no_delta.
        self.add_recursive_def(
            "def numeral_no_step (t : KExpr) (h : IsNumeral t) (e2 : KExpr) (C : Type) (hs : whnf_step t e2) : C := match hs with\n| whnf_step.beta hbr => numeral_no_beta t h e2 C hbr\n| whnf_step.delta hdr => numeral_no_delta t h e2 C hdr",
            "numeral_no_step: a numeral admits no whnf_step (beta via numeral_no_beta, delta via numeral_no_delta). THE Nat.rec numeral-stuckness theorem. Nat.rec port B5(d).",
        )?;

        // ── B5(e): whnfAcc_numeral — a numeral is whnf-accessible (SN). Its step_fn
        // is vacuous: numeral_no_step rules out every reduct. UNCONDITIONAL (numeral
        // stuckness holds over the_red_env by natFresh_red).
        self.add_recursive_def(
            "def whnfAcc_numeral (t : KExpr) (h : IsNumeral t) : whnf_acc t := whnf_acc.intro t (fun (e' : KExpr) (hstep : whnf_step t e') => numeral_no_step t h e' (whnf_acc e') hstep)",
            "whnfAcc_numeral: every numeral is whnf-accessible (strongly normalizing) — vacuously, since it admits no whnf_step. Nat.rec port B5(e).",
        )?;

        // ── B5(f): red_numeral — a numeral is reducible (cm_Red) at EVERY type over
        // any CandModel M. Numerals are neutral (neutral_numeral) with no reducts
        // (numeral_no_step), so CR3 applies vacuously. Genuine, from the bare interface.
        self.add_recursive_def(
            "def red_numeral (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (t : KExpr) (h : IsNumeral t) (T : KExpr) : cm_Red tenv M T t := CR3 tenv M T t (neutral_numeral t h) (fun (e2 : KExpr) (hstep : whnf_step t e2) => numeral_no_step t h e2 (cm_Red tenv M T e2) hstep)",
            "red_numeral: every numeral is reducible (cm_Red) at every type — neutral (neutral_numeral) + no reducts (numeral_no_step) ⇒ CR3 vacuously. Nat.rec port B5(f).",
        )?;

        // ── B5(g) prep: de Bruijn cancel lemmas (both DIRECT specializations of
        // instantiate_lift_cancel_general — no psubst chain needed) + natSuccCaseSem.
        // inst_lift1: instantiate (lift_at m 0 1) n = m (cancel a=1,j=0 then lift_at m 0 0 = m).
        self.add_recursive_def(
            "def inst_lift1 (m : KExpr) (n : KExpr) : Eq KExpr (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) n) m := Eq.trans KExpr (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) n) (lift_at m Nat.zero Nat.zero) m (instantiate_lift_cancel_general m n Nat.zero (Nat.succ Nat.zero) Nat.zero (Eq.refl Nat (Nat.succ Nat.zero))) (lift_zero_identity m)",
            "inst_lift1: instantiate (lift_at m 0 1) n = m — a unit lift cancels under instantiate. Nat.rec port B5(g) prep.",
        )?;
        // inst_at1_lift2: instantiate_at (lift_at m 0 2) n 1 = lift_at m 0 1 (cancel a=2,j=1).
        self.add_recursive_def(
            "def inst_at1_lift2 (m : KExpr) (n : KExpr) : Eq KExpr (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) n (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) := instantiate_lift_cancel_general m n Nat.zero (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero) (Eq.refl Nat (Nat.succ Nat.zero))",
            "inst_at1_lift2: instantiate_at (lift_at m 0 2) n 1 = lift_at m 0 1 — depth-1 lift-cancel. Nat.rec port B5(g) prep.",
        )?;
        // natSuccCaseSem: the succ-minor's semantic type (fun n ih => C(succ n)),
        // Pi natTypeC (Pi (app (lift m 0 1) (bvar 0)) (app (lift m 0 2) (succ (bvar 1)))).
        self.add_recursive_def(
            "def natSuccCaseSem (m : KExpr) : KExpr := KExpr.pi natTypeC (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))))",
            "natSuccCaseSem m: the succ-minor semantic type (n : Nat) -> C n -> C (succ n), motive m. Nat.rec port B5(g) prep.",
        )?;

        // ── B5(g) prep: natSuccArm_inst1/2 — the two dependent-elimination equations.
        // The LHS instantiate computes (defeq) to a pi/app form with instantiate/
        // instantiate_at/lift subterms; rewrite each via inst_lift1/inst_at1_lift2/
        // lift_zero_identity as nested Eq.cong congruences.
        {
            let z1 = "(Nat.succ Nat.zero)";
            let z2 = "(Nat.succ (Nat.succ Nat.zero))";
            let lm1 = format!("(lift_at m Nat.zero {z1})");
            let lm2 = format!("(lift_at m Nat.zero {z2})");
            let ln0 = "(lift_at n Nat.zero Nat.zero)";
            let ln1 = format!("(lift_at n Nat.zero {z1})");
            // natSuccArm_inst1
            let pp = format!("(KExpr.app (instantiate {lm1} n) {ln0})");
            let qq =
                format!("(KExpr.app (instantiate_at {lm2} n {z1}) (KExpr.app natSuccC {ln1}))");
            let appmn = "(KExpr.app m n)";
            let qprime = format!("(KExpr.app {lm1} (KExpr.app natSuccC {ln1}))");
            let rhs1 = format!("(KExpr.pi {appmn} {qprime})");
            let eqdom = format!("(Eq.trans KExpr {pp} (KExpr.app m {ln0}) {appmn} (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x {ln0}) (instantiate {lm1} n) m (inst_lift1 m n)) (Eq.cong KExpr KExpr (fun (y : KExpr) => KExpr.app m y) {ln0} n (lift_zero_identity n)))");
            let eqbody = format!("(Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x (KExpr.app natSuccC {ln1})) (instantiate_at {lm2} n {z1}) {lm1} (inst_at1_lift2 m n))");
            let result1 = format!("(Eq.trans KExpr (KExpr.pi {pp} {qq}) (KExpr.pi {appmn} {qq}) {rhs1} (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi x {qq}) {pp} {appmn} {eqdom}) (Eq.cong KExpr KExpr (fun (yy : KExpr) => KExpr.pi {appmn} yy) {qq} {qprime} {eqbody}))");
            let lhs1 = format!("(instantiate (KExpr.pi (KExpr.app {lm1} (KExpr.bvar Nat.zero)) (KExpr.app {lm2} (KExpr.app natSuccC (KExpr.bvar {z1})))) n)");
            self.add_recursive_def(
                &format!("def natSuccArm_inst1 (m : KExpr) (n : KExpr) : Eq KExpr {lhs1} {rhs1} := {result1}"),
                "natSuccArm_inst1: instantiating the succ-minor Pi-body at the argument n. Nat.rec port B5(g) prep.",
            )?;
            // natSuccArm_inst2 (m n r)
            let inner = format!("(KExpr.app natSuccC (instantiate {ln1} r))");
            let innerp = "(KExpr.app natSuccC n)";
            let lhs2form = format!("(KExpr.app (instantiate {lm1} r) {inner})");
            let rhs2 = format!("(KExpr.app m {innerp})");
            let eqinner = format!("(Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.app natSuccC z) (instantiate {ln1} r) n (inst_lift1 n r))");
            let result2 = format!("(Eq.trans KExpr {lhs2form} (KExpr.app m {inner}) {rhs2} (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x {inner}) (instantiate {lm1} r) m (inst_lift1 m r)) (Eq.cong KExpr KExpr (fun (y : KExpr) => KExpr.app m y) {inner} {innerp} {eqinner}))");
            let lhs2 = format!("(instantiate (KExpr.app {lm1} (KExpr.app natSuccC {ln1})) r)");
            self.add_recursive_def(
                &format!("def natSuccArm_inst2 (m : KExpr) (n : KExpr) (r : KExpr) : Eq KExpr {lhs2} {rhs2} := {result2}"),
                "natSuccArm_inst2: instantiating the succ codomain at the recursive call r. Nat.rec port B5(g) prep.",
            )?;
        }

        // ── B5(g): natRec_adequacy_numeral — THE recursor-reducibility theorem for
        // numeral majors. If the motive/zero/succ minors are reducible at their
        // (dependent) types, then Nat.rec m z s t is reducible at (m t) for every
        // numeral t. IsNumeral induction: zero = redNatRec head-expansion at the zero
        // contractum; succ = pi_elim ×2 through the dependent succ-minor type
        // (natSuccArm_inst1/2 as Eq.rec transports) + inner IH + redNatRec at the succ
        // contractum. Genuine SN content, CandModel-conditional, zero axioms.
        {
            let z1 = "(Nat.succ Nat.zero)";
            let z2 = "(Nat.succ (Nat.succ Nat.zero))";
            let rr = "(red_def the_red_env)";
            let re = "(natREnv u)";
            // cm_Red shorthand: cm_Red tenv M T e
            let mtym = "(natMotiveTy u)";
            let scs = "(natSuccCaseSem m)";
            // the succ-minor Pi-body and the natSuccArm targets
            let succbody = format!("(KExpr.pi (KExpr.app (lift_at m Nat.zero {z1}) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero {z2}) (KExpr.app natSuccC (KExpr.bvar {z1}))))");
            let bodyinst = format!("(KExpr.app (lift_at m Nat.zero {z1}) (KExpr.app natSuccC (lift_at n Nat.zero {z1})))");
            let arm1lhs = format!("(instantiate {succbody} n)");
            let arm1rhs = format!("(KExpr.pi (KExpr.app m n) {bodyinst})");
            let nra = "(natRecApp u m z s n)";
            let arm2lhs = format!("(instantiate {bodyinst} {nra})");
            let succt = "(KExpr.app natSuccC n)";
            let succcontr = format!("(KExpr.app (KExpr.app s n) {nra})");
            // reason: `succT` mirrors proof notation — the motive `m` applied to the
            // successor term (the "T"/type instance at succ), deliberately distinct
            // from the lowercase numeral `succt`; a snake_case rename would collide
            // visually and lose the term-vs-motive reading. See JUSTIFIED_EXCEPTIONS §10.
            #[allow(non_snake_case)]
            let succT = format!("(KExpr.app m {succt})");
            let motive = format!("(fun (t0 : KExpr) (_ : IsNumeral t0) => forall (m : KExpr) (z : KExpr) (s : KExpr), cm_Red tenv M {mtym} m -> cm_Red tenv M (KExpr.app m natZeroC) z -> cm_Red tenv M {scs} s -> cm_Red tenv M (KExpr.app m t0) (natRecApp u m z s t0))");
            let zero_case = format!("(fun (m : KExpr) (z : KExpr) (s : KExpr) (hm : cm_Red tenv M {mtym} m) (hz : cm_Red tenv M (KExpr.app m natZeroC) z) (hs : cm_Red tenv M {scs} s) => redNatRec_holds tenv M u {rr} {re} m z s natZeroC z (KExpr.app m natZeroC) natFresh_red (natREnv_recEnvOK u) (NatRecContract.zero u m z s) (CR1 tenv M {mtym} m hm) (CR1 tenv M (KExpr.app m natZeroC) z hz) (CR1 tenv M {scs} s hs) (whnfAcc_numeral natZeroC IsNumeral.zero) hz)");
            // succ case
            let h1 = format!(
                "(pi_elim tenv M natTypeC {succbody} s n hs (red_numeral tenv M n hn natTypeC))"
            );
            let h1t = format!("(Eq.rec KExpr {arm1lhs} (fun (Tv : KExpr) (_ : Eq KExpr {arm1lhs} Tv) => cm_Red tenv M Tv (KExpr.app s n)) {h1} {arm1rhs} (natSuccArm_inst1 m n))");
            let hih = "(ihn m z s hm hz hs)";
            let h2 = format!(
                "(pi_elim tenv M (KExpr.app m n) {bodyinst} (KExpr.app s n) {nra} {h1t} {hih})"
            );
            let h2t = format!("(Eq.rec KExpr {arm2lhs} (fun (Tv : KExpr) (_ : Eq KExpr {arm2lhs} Tv) => cm_Red tenv M Tv {succcontr}) {h2} {succT} (natSuccArm_inst2 m n {nra}))");
            let succ_case = format!("(fun (n : KExpr) (hn : IsNumeral n) (ihn : forall (m : KExpr) (z : KExpr) (s : KExpr), cm_Red tenv M {mtym} m -> cm_Red tenv M (KExpr.app m natZeroC) z -> cm_Red tenv M {scs} s -> cm_Red tenv M (KExpr.app m n) (natRecApp u m z s n)) (m : KExpr) (z : KExpr) (s : KExpr) (hm : cm_Red tenv M {mtym} m) (hz : cm_Red tenv M (KExpr.app m natZeroC) z) (hs : cm_Red tenv M {scs} s) => redNatRec_holds tenv M u {rr} {re} m z s {succt} {succcontr} {succT} natFresh_red (natREnv_recEnvOK u) (NatRecContract.succ u m z s n) (CR1 tenv M {mtym} m hm) (CR1 tenv M (KExpr.app m natZeroC) z hz) (CR1 tenv M {scs} s hs) (whnfAcc_numeral {succt} (IsNumeral.succ n hn)) {h2t})");
            let body = format!("def natRec_adequacy_numeral (tenv : Name -> OptionType KExpr) (M : CandModel tenv) (u : Level) (t : KExpr) (h : IsNumeral t) : forall (m : KExpr) (z : KExpr) (s : KExpr), cm_Red tenv M {mtym} m -> cm_Red tenv M (KExpr.app m natZeroC) z -> cm_Red tenv M {scs} s -> cm_Red tenv M (KExpr.app m t) (natRecApp u m z s t) := IsNumeral.rec {motive} {zero_case} {succ_case} t h");
            self.add_recursive_def(
                &body,
                "natRec_adequacy_numeral: for every numeral t, if the motive/zero/succ minors are reducible at their dependent types then Nat.rec m z s t is reducible at (m t). THE recursor-reducibility payoff (redNatRec head-expansion + pi_elim + numeral induction). Nat.rec port B5(g).",
            )?;
        }

        // ── B6: whnf_terminates_well_typed_nat — every Nat-typed closed term is
        // whnf-accessible (SN). A one-liner over the general whnf_terminates_well_typed_
        // dependent, specialized to the Nat const-typing env natTEnv (Nat:sort 1,
        // zero:Nat, succ:Nat->Nat, rec:natRecTy). VARIABLE-motive only (conv-free
        // TypingCtx ceiling — the honest limit). CandModel-conditional, zero axioms.
        self.add_recursive_def(
            "def natTEnv (u : Level) (n : Name) : OptionType KExpr := opt_pick KExpr (name_eqb n natName) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n zeroName) natTypeC (opt_pick KExpr (name_eqb n succName) (KExpr.pi natTypeC natTypeC) (opt_pick KExpr (name_eqb n recName) (natRecTy u) (OptionType.none KExpr))))",
            "natTEnv u: the Nat const-typing env (Nat : sort 1, zero : Nat, succ : Nat -> Nat, rec : natRecTy). Nat.rec port B6.",
        )?;
        self.add_recursive_def(
            "def whnf_terminates_well_typed_nat (u : Level) (M : CandModel (natTEnv u)) (e : KExpr) (T : KExpr) (h : TypingCtx (natTEnv u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (natTEnv u) M e T h",
            "whnf_terminates_well_typed_nat: every Nat-typed closed term is whnf-accessible (SN), specializing the dependent SN theorem to natTEnv. Variable-motive ceiling. THE Nat.rec SN theorem. Nat.rec port B6.",
        )?;

        Ok(())
    }
}

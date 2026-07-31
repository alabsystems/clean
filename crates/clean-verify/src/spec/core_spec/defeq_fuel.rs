// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Step 2b of the def-eq completeness program: THE ALGORITHM OBJECT.
//!
//! See `docs/plans/DEFEQ_COMPLETENESS_PROGRAM_2026-07-25.md`. Completeness is a
//! statement RELATING AN ALGORITHM to a relation. Until now the reflected
//! calculus had no conversion algorithm at all — no `Bool`-valued def-eq, no
//! `Decidable` instance, and fuel-indexed functions only for *reduction* — so
//! completeness was not merely unproven, it was unstatable. `kexpr_beq` went
//! live in step 2a; this composes it with the executable whnf loop into the
//! first conversion algorithm on `KExpr`, and proves it SOUND.
//!
//! `def_eq_whnf_fuel` is deliberately the WEAKEST honest algorithm: reduce both
//! sides with the executable loop, then compare the results syntactically. It is
//! NOT complete — two convertible terms need not have syntactically equal weak
//! head normal forms (`pi A B` vs `pi A' B'` with `A` convertible to but not
//! syntactically equal to `A'`). Closing that gap is what the structural
//! recursion in step 4 is for, and this is its base case.
//!
//! What is proven here is the soundness direction, which is the half that can be
//! established outright: if the algorithm accepts, the two terms really are
//! convertible. Stated over `whnf_red_conv` — the spec's own reduction-conversion
//! relation — because that is what `whnf_fuel_red_conv` delivers; bridging
//! `whnf_red_conv` to `DefEq` is a separate lemma that does not yet exist.
//!
//! ORDERING: this module must be registered AFTER `add_kexpr_beq_sound`
//! (stage 138), since it consumes `kexpr_beq` and `kexpr_beq_eq`. Its other
//! dependencies (`whnf_fuel_red`, `whnf_fuel_red_conv`, `whnf_red_conv_trans`,
//! `whnf_red_conv_symm`) come from `add_reduce_once_red` inside `whnf_progress`
//! (stage 72). Every one of those stages was checked before this was placed.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The first conversion ALGORITHM on `KExpr`, plus its soundness.
    pub(super) fn add_defeq_fuel(&mut self) -> Result<(), SpecError> {
        // The algorithm. `OptionType.rec` twice: the fuel loop returns
        // `none` when it runs out, and running out must FAIL CLOSED (`false`,
        // "not known equal") rather than accept — an out-of-fuel accept would be
        // exactly the unsoundness this whole program exists to prevent.
        self.add_recursive_def(
            "def def_eq_whnf_fuel (renv : RedEnv) (fuel : Nat) (a : KExpr) (b : KExpr) : Bool := \
             OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (nb : KExpr) => kexpr_beq na nb) (whnf_fuel_red renv fuel b)) \
             (whnf_fuel_red renv fuel a)",
            "def_eq_whnf_fuel renv fuel a b: THE FIRST CONVERSION ALGORITHM on KExpr — run the \
             executable whnf loop on both sides at the given fuel, then compare the results with \
             kexpr_beq. Fails CLOSED on exhausted fuel (none => false), never accepts on \
             exhaustion. Deliberately the weakest honest algorithm: it is SOUND but NOT complete \
             (convertible terms need not have syntactically equal whnfs), and it is the base case \
             the structural recursion extends. Step 2b of the def-eq completeness program.",
        )?;

        // Soundness, in legs form: given that the loop produced `na` and `nb` and
        // that they compare equal, the inputs are convertible. Legs form rather
        // than `def_eq_whnf_fuel … = true -> …` because the Bool form requires a
        // dependent case analysis on two `OptionType`s to recover the legs, while
        // every consumer that runs the algorithm already HAS them.
        //
        // Chain: a ~ na (the loop is conversion-preserving), na = nb (kexpr_beq
        // is sound), b ~ nb; so a ~ na ~ b by transitivity, with the middle step
        // transported along na = nb and flipped.
        self.add_recursive_def(
            "def def_eq_whnf_fuel_sound (renv : RedEnv) (fuel : Nat) (a : KExpr) (b : KExpr) \
             (na : KExpr) (nb : KExpr) \
             (ha : Eq (OptionType KExpr) (whnf_fuel_red renv fuel a) (OptionType.some KExpr na)) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red renv fuel b) (OptionType.some KExpr nb)) \
             (heq : Eq Bool (kexpr_beq na nb) Bool.true) : whnf_red_conv renv a b := \
             whnf_red_conv_trans renv a na b (whnf_fuel_red_conv renv fuel a na ha) \
             (whnf_red_conv_symm renv b na \
             (Eq.substType KExpr (fun (x : KExpr) => whnf_red_conv renv b x) nb na \
             (Eq.symm KExpr na nb (kexpr_beq_eq na nb heq)) \
             (whnf_fuel_red_conv renv fuel b nb hb)))",
            "def_eq_whnf_fuel_sound: SOUNDNESS of the conversion algorithm — if the executable \
             whnf loop reduces a to na and b to nb, and kexpr_beq accepts na against nb, then a \
             and b are genuinely convertible (whnf_red_conv). Composes whnf_fuel_red_conv (the \
             loop preserves conversion) with kexpr_beq_eq (syntactic acceptance implies equality), \
             then transports and closes by symm/trans. Stated over whnf_red_conv rather than DefEq \
             because that is what whnf_fuel_red_conv delivers; the whnf_red_conv -> DefEq bridge \
             does not exist yet. DerivedProved, zero axiom_deps. Step 3 of the def-eq completeness \
             program.",
        )?;

        // COMPLETENESS — the exact converse of the soundness theorem above, and
        // the first completeness result about a conversion algorithm in this
        // spec. Whenever the criterion the algorithm is meant to decide holds
        // (both sides reduce, and the reducts are equal), the algorithm ACCEPTS.
        // Together with `def_eq_whnf_fuel_sound` this makes acceptance an exact
        // characterisation: `def_eq_whnf_fuel` accepts IFF the whnfs coincide.
        //
        // SCOPE, stated so this is not read as more than it is. This is
        // completeness of THIS algorithm against ITS OWN criterion — syntactic
        // equality of weak head normal forms. It is NOT completeness against
        // `DefEq`: convertible terms need not have syntactically equal whnfs
        // (`pi A B` vs `pi A' B'` with `A` convertible to but not syntactically
        // equal to `A'`), so the implication `DefEq a b -> def_eq_whnf_fuel … =
        // true` is FALSE and is deliberately not stated. Closing that distance is
        // the structural recursion over `below_plus`, for which this is the base
        // case. Per `docs/SELF_VERIFICATION_CERTIFICATE.md:504`, any completeness
        // claim is a conditional theorem and never an axiom — this one is
        // conditional on its two reduction legs and carries no axioms at all.
        //
        // Proof: transport the goal along the two reduction legs so the
        // `OptionType.rec` scrutinees become `some na` / `some nb` and iota-fire,
        // reducing the goal to `kexpr_beq na nb = true`; rewrite along `na = nb`
        // and close with `kexpr_beq_refl`.
        self.add_recursive_def(
            "def def_eq_whnf_fuel_complete (renv : RedEnv) (fuel : Nat) (a : KExpr) (b : KExpr) \
             (na : KExpr) (nb : KExpr) \
             (ha : Eq (OptionType KExpr) (whnf_fuel_red renv fuel a) (OptionType.some KExpr na)) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red renv fuel b) (OptionType.some KExpr nb)) \
             (heq : Eq KExpr na nb) : Eq Bool (def_eq_whnf_fuel renv fuel a b) Bool.true := \
             Eq.substType (OptionType KExpr) \
             (fun (o : OptionType KExpr) => Eq Bool (OptionType.rec KExpr \
             (fun (_ : OptionType KExpr) => Bool) Bool.false (fun (na2 : KExpr) => \
             OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (nb2 : KExpr) => kexpr_beq na2 nb2) (whnf_fuel_red renv fuel b)) o) Bool.true) \
             (OptionType.some KExpr na) (whnf_fuel_red renv fuel a) \
             (Eq.symm (OptionType KExpr) (whnf_fuel_red renv fuel a) (OptionType.some KExpr na) ha) \
             (Eq.substType (OptionType KExpr) \
             (fun (o : OptionType KExpr) => Eq Bool (OptionType.rec KExpr \
             (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (nb2 : KExpr) => kexpr_beq na nb2) o) Bool.true) \
             (OptionType.some KExpr nb) (whnf_fuel_red renv fuel b) \
             (Eq.symm (OptionType KExpr) (whnf_fuel_red renv fuel b) (OptionType.some KExpr nb) hb) \
             (Eq.substType KExpr (fun (x : KExpr) => Eq Bool (kexpr_beq na x) Bool.true) \
             na nb heq (kexpr_beq_refl na)))",
            "def_eq_whnf_fuel_complete: COMPLETENESS of the conversion algorithm against its own \
             criterion — if the executable whnf loop reduces a to na and b to nb and those reducts \
             are equal, the algorithm ACCEPTS. Exact converse of def_eq_whnf_fuel_sound, so \
             together they characterise acceptance: def_eq_whnf_fuel accepts IFF the whnfs \
             coincide. NOT completeness against DefEq — convertible terms need not have \
             syntactically equal whnfs, so that implication is FALSE and is deliberately not \
             stated; closing the distance is the structural recursion over below_plus, for which \
             this is the base case. A conditional theorem (conditional on its two reduction legs), \
             never an axiom, per SELF_VERIFICATION_CERTIFICATE.md:504. DerivedProved, zero \
             axiom_deps. Step 4 of the def-eq completeness program.",
        )?;

        // GAP B, first half: beta_reduces_bd -> DefEq.
        //
        // The only genuine recursion in the whnf_red_conv -> DefEq bridge. Twelve
        // of the fourteen arms map onto a DefEq congruence with `refl` on the
        // unchanged component; `beta` and `zeta` map onto the corresponding DefEq
        // constructors directly.
        //
        // The `forall_congr_*` arms are stated over `KExpr.forall_`, which is NOT
        // a KExpr constructor — it is a REDUCIBLE ALIAS for `KExpr.pi`
        // (`whnf_reduction.rs:92-105`, registered via add_definition_reducible so
        // it is delta-transparent). They are therefore `pi_dom` / `pi_cod` up to
        // unfolding and discharge with the same `DefEq.pi_cong` terms. That was
        // the one open question blocking this bridge; settling it empirically
        // (a minimal spec showed KExpr.pi present and KExpr.forall_ absent after
        // add_expr_model, proving it was registered later) is what made this
        // writable.
        self.add_recursive_def(
            "def beta_reduces_bd_to_def_eq (e : KExpr) (e2 : KExpr) (h : beta_reduces_bd e e2) : \
             DefEq e e2 := beta_reduces_bd.rec \
             (fun (x : KExpr) (y : KExpr) (_ : beta_reduces_bd x y) => DefEq x y) \
             (fun (A : KExpr) (body : KExpr) (arg : KExpr) => DefEq.beta A body arg) \
             (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (_ : beta_reduces_bd f f2) \
             (ih : DefEq f f2) => DefEq.app_cong f f2 a a ih (DefEq.refl a)) \
             (fun (f : KExpr) (a : KExpr) (a2 : KExpr) (_ : beta_reduces_bd a a2) \
             (ih : DefEq a a2) => DefEq.app_cong f f a a2 (DefEq.refl f) ih) \
             (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_ : beta_reduces_bd ty ty2) \
             (ih : DefEq ty ty2) => DefEq.lam_cong ty ty2 body body ih (DefEq.refl body)) \
             (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_ : beta_reduces_bd body body2) \
             (ih : DefEq body body2) => DefEq.lam_cong ty ty body body2 (DefEq.refl ty) ih) \
             (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_ : beta_reduces_bd dom dom2) \
             (ih : DefEq dom dom2) => DefEq.pi_cong dom dom2 body body ih (DefEq.refl body)) \
             (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_ : beta_reduces_bd body body2) \
             (ih : DefEq body body2) => DefEq.pi_cong dom dom body body2 (DefEq.refl dom) ih) \
             (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_ : beta_reduces_bd dom dom2) \
             (ih : DefEq dom dom2) => DefEq.pi_cong dom dom2 body body ih (DefEq.refl body)) \
             (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_ : beta_reduces_bd body body2) \
             (ih : DefEq body body2) => DefEq.pi_cong dom dom body body2 (DefEq.refl dom) ih) \
             (fun (ty : KExpr) (val : KExpr) (body : KExpr) => DefEq.zeta ty val body) \
             (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) \
             (_ : beta_reduces_bd ty ty2) (ih : DefEq ty ty2) => \
             DefEq.let_cong ty ty2 val val body body ih (DefEq.refl val) (DefEq.refl body)) \
             (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) \
             (_ : beta_reduces_bd val val2) (ih : DefEq val val2) => \
             DefEq.let_cong ty ty val val2 body body (DefEq.refl ty) ih (DefEq.refl body)) \
             (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) \
             (_ : beta_reduces_bd body body2) (ih : DefEq body body2) => \
             DefEq.let_cong ty ty val val body body2 (DefEq.refl ty) (DefEq.refl val) ih) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) \
             (_ : beta_reduces_bd sub sub2) (ih : DefEq sub sub2) => \
             DefEq.proj_cong s i sub sub2 ih) e e2 h",
            "beta_reduces_bd_to_def_eq: every iota-free beta/zeta/congruence reduction step is a \
             definitional equality. The load-bearing recursion of the whnf_red_conv -> DefEq \
             bridge (Gap B of the def-eq completeness program): 14 arms, with beta/zeta mapping to \
             DefEq.beta/DefEq.zeta and the twelve congruence arms to app_cong/lam_cong/pi_cong/ \
             let_cong/proj_cong carrying DefEq.refl on the unchanged component. The forall_congr_* \
             arms discharge via pi_cong because KExpr.forall_ is a REDUCIBLE ALIAS for KExpr.pi \
             (whnf_reduction.rs:92), not a distinct constructor. DerivedProved, zero axiom_deps.",
        )?;

        // GAP B, second half: the two dispatch bridges, at the FIXED env.
        //
        // Stated at `the_red_env` and not for a general `renv`, and that is
        // forced rather than convenient: `whnf_red_step`'s delta/iota fields are
        // `Eq (delta_reduct (red_def renv) e) (some e2)`, while `DefEq.delta` /
        // `DefEq.iota` consume `delta_reduces` / `iota_reduces`, which are FIXED
        // at `the_red_env`. At that instantiation the field is *definitionally*
        // `delta_step (red_def the_red_env) e e2` — exactly what
        // `delta_reduces.mk` takes — so both arms are free. For a general `renv`
        // the statement is simply not provable, and anyone generalising it would
        // be chasing a theorem that does not hold.
        self.add_recursive_def(
            "def whnf_red_step_to_def_eq (e : KExpr) (e2 : KExpr) \
             (h : whnf_red_step the_red_env e e2) : DefEq e e2 := \
             whnf_red_step.rec the_red_env \
             (fun (x : KExpr) (y : KExpr) (_ : whnf_red_step the_red_env x y) => DefEq x y) \
             (fun (x : KExpr) (y : KExpr) (hb : beta_reduces_bd x y) => \
             beta_reduces_bd_to_def_eq x y hb) \
             (fun (x : KExpr) (y : KExpr) (hd : Eq (OptionType KExpr) \
             (delta_reduct (red_def the_red_env) x) (OptionType.some KExpr y)) => \
             DefEq.delta x y (delta_reduces.mk x y hd)) \
             (fun (x : KExpr) (y : KExpr) (hi : Eq (OptionType KExpr) \
             (iota_reduct (red_rec the_red_env) x) (OptionType.some KExpr y)) => \
             DefEq.iota x y (iota_reduces.mk x y hi)) \
             (fun (f : KExpr) (f2 : KExpr) (a : KExpr) \
             (_ : whnf_red_step the_red_env f f2) (ih : DefEq f f2) => \
             DefEq.app_cong f f2 a a ih (DefEq.refl a)) \
             (fun (s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) \
             (_ : whnf_red_step the_red_env sub sub2) (ih : DefEq sub sub2) => \
             DefEq.proj_cong s i sub sub2 ih) e e2 h",
            "whnf_red_step_to_def_eq: one weak-head reduction step at the fixed env is a \
             definitional equality. Five arms: beta delegates to beta_reduces_bd_to_def_eq; delta \
             and iota are FREE because at the_red_env the step's field is definitionally the \
             delta_step / iota_step that delta_reduces.mk / iota_reduces.mk consume; app_left and \
             proj are congruences carrying DefEq.refl on the unchanged component. Stated at the \
             fixed env by necessity — DefEq.delta/iota are fixed there, so the general-renv \
             statement does not hold. DerivedProved, zero axiom_deps.",
        )?;

        // GAP B, capstone: the reduction-conversion relation implies DefEq.
        // Three arms; fwd and bwd differ only in which side the step runs on,
        // so bwd inserts a DefEq.symm.
        self.add_recursive_def(
            "def whnf_red_conv_to_def_eq (e : KExpr) (e2 : KExpr) \
             (h : whnf_red_conv the_red_env e e2) : DefEq e e2 := \
             whnf_red_conv.rec the_red_env \
             (fun (x : KExpr) (y : KExpr) (_ : whnf_red_conv the_red_env x y) => DefEq x y) \
             (fun (x : KExpr) => DefEq.refl x) \
             (fun (a : KExpr) (b : KExpr) (c : KExpr) (hs : whnf_red_step the_red_env a b) \
             (_ : whnf_red_conv the_red_env b c) (ih : DefEq b c) => \
             DefEq.trans a b c (whnf_red_step_to_def_eq a b hs) ih) \
             (fun (a : KExpr) (b : KExpr) (c : KExpr) (hs : whnf_red_step the_red_env b a) \
             (_ : whnf_red_conv the_red_env b c) (ih : DefEq b c) => \
             DefEq.trans a b c (DefEq.symm b a (whnf_red_step_to_def_eq b a hs)) ih) e e2 h",
            "whnf_red_conv_to_def_eq: THE GAP-B CAPSTONE — the reduction-conversion relation \
             implies definitional equality at the fixed env. refl maps to DefEq.refl; fwd chains \
             the step with the IH by DefEq.trans; bwd does the same with a DefEq.symm because its \
             step runs backwards. Composing this with def_eq_whnf_fuel_sound upgrades the \
             conversion algorithm's soundness guarantee from whnf_red_conv to DefEq itself. \
             DerivedProved, zero axiom_deps.",
        )?;

        // ── GAP A: THE STRUCTURAL ALGORITHM ─────────────────────────────────
        //
        // `def_eq_whnf_fuel` compares whnfs SYNTACTICALLY, so it rejects
        // convertible terms whose whnfs differ structurally (`pi A B` vs
        // `pi A' B'` with A convertible to but not syntactically equal to A').
        // That is why its completeness is against syntactic equality rather than
        // DefEq. This is the fix: descend into components and recurse.
        //
        // `def_eq_struct rec a b` is the one-layer structural comparison — a 9x9
        // double `KExpr.rec` in exactly the shape `kexpr_beq` uses, except that
        // matching arms call the supplied `rec` on the components instead of
        // recursing structurally. Non-matching head pairs are `Bool.false`;
        // leaves compare with level_eqb / nat_eqb / name_eqb / ulist_eqb.
        //
        // The term is MACHINE-GENERATED from the 9-constructor table rather than
        // hand-written: 81 arms is exactly the scale at which a hand-written
        // recursor grid acquires a silent transposition, and the generator makes
        // the arm/leaf counts checkable (9 outer arms, 72 Bool.false mismatches).
        self.add_recursive_def(
            "def def_eq_struct (cmp : KExpr -> KExpr -> Bool) (a : KExpr) (b : KExpr) : Bool := \
             KExpr.rec (fun (_ : KExpr) => KExpr -> Bool) (fun (n : Level) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => level_eqb n m) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (i : Nat) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => nat_eqb i j) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (f : KExpr) (a1 : KExpr) (_ : KExpr -> Bool) (_ : KExpr -> Bool) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.and (cmp f g) (cmp a1 c)) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (ty1 : KExpr) (b1 : KExpr) (_ : KExpr -> Bool) (_ : KExpr -> Bool) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.and (cmp ty1 t) (cmp b1 d)) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (ty1 : KExpr) (b1 : KExpr) (_ : KExpr -> Bool) (_ : KExpr -> Bool) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.and (cmp ty1 t) (cmp b1 d)) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (nm : Name) (us : ListType Level) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.and (name_eqb nm nm2) (ulist_eqb us us2)) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : KExpr -> Bool) (_ : KExpr -> Bool) (_ : KExpr -> Bool) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.and (cmp lt t2) (Bool.and (cmp lv v2) (cmp lb b2))) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => Bool.false) y) (fun (ps : Name) (pidx : Nat) (psub : KExpr) (_ : KExpr -> Bool) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.and (Bool.and (name_eqb ps s2) (nat_eqb pidx i2)) (cmp psub sub2)) (fun (w2 : Nat) => Bool.false) y) (fun (w : Nat) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) (fun (m : Level) => Bool.false) (fun (j : Nat) => Bool.false) (fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm2 : Name) (us2 : ListType Level) => Bool.false) (fun (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s2 : Name) (i2 : Nat) (sub2 : KExpr) (_ : Bool) => Bool.false) (fun (w2 : Nat) => nat_eqb w w2) y) a b",
            "def_eq_struct rec a b: one-layer structural conversion comparison — 9x9 double \
             KExpr.rec, matching heads compare components via the supplied `rec`, mismatched heads \
             are false, leaves via level_eqb / nat_eqb / name_eqb / ulist_eqb. The congruence step \
             def_eq_whnf_fuel lacks. Machine-generated from the constructor table. Gap A.",
        )?;

        // The fuel-indexed structural algorithm: at each level, reduce both sides
        // to weak head normal form and then compare structurally, recursing at
        // `fuel - 1`. Fuel 0 fails CLOSED, as in `def_eq_whnf_fuel`.
        //
        // This is the algorithm whose completeness against DefEq is the goal.
        // Registering it does NOT yet prove that — the completeness theorem needs
        // an induction on DefEq with the `below_plus` accessibility order, and
        // its fuel-adequacy hypothesis. What this does is make the statement
        // EXPRESSIBLE about an algorithm that could satisfy it.
        self.add_recursive_def(
            "def def_eq_fuel (renv : RedEnv) (fuel : Nat) : KExpr -> KExpr -> Bool := \
             Nat.rec (fun (_ : Nat) => KExpr -> KExpr -> Bool) \
             (fun (_ : KExpr) (_ : KExpr) => Bool.false) \
             (fun (k : Nat) (ih : KExpr -> KExpr -> Bool) => fun (a : KExpr) (b : KExpr) => \
             OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) Bool.false \
             (fun (na : KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Bool) \
             Bool.false (fun (nb : KExpr) => def_eq_struct ih na nb) (whnf_fuel_red renv k b)) \
             (whnf_fuel_red renv k a)) fuel",
            "def_eq_fuel renv fuel a b: THE STRUCTURAL CONVERSION ALGORITHM — at each fuel level \
             reduce both sides to whnf, then compare structurally, recursing on components at \
             fuel-1. Fails CLOSED at fuel 0. Unlike def_eq_whnf_fuel it accepts convertible terms \
             whose whnfs differ structurally but whose components are convertible, which is what \
             completeness against DefEq requires. The completeness THEOREM is not yet proved — it \
             needs an induction on DefEq over the below_plus order plus fuel adequacy; this makes \
             that statement expressible about an algorithm that can satisfy it. Gap A.",
        )?;

        // SOUNDNESS of the algorithm just registered, in `defeq_struct_sound.rs`.
        // Called from here rather than added as its own `STAGES` entry so that
        // its position relative to `def_eq_struct` / `def_eq_fuel` cannot drift:
        // it consumes both, and a stage-ordering slip in this spec is invisible
        // to `cargo check` (these are source strings elaborated at spec-build
        // time) and costs a full ~40-minute build to discover.
        self.add_defeq_struct_sound()?;

        // Link 3 of the completeness chain (`defeq_struct_intro.rs`): matching
        // heads imply the algorithm accepts. Must follow the soundness module —
        // not for dependency reasons (it consumes none of it) but so the
        // registration order matches the honest reading order: an acceptance
        // criterion is only worth deriving once it is known not to accept junk.
        self.add_defeq_struct_intro()?;
        self.add_defeq_fuel_congruences()?;

        // First named sub-goal of link 4 (`beta_bd_embedding.rs`). It depends
        // only on `beta_reduces` (stage 30) and `beta_reduces_bd` (stage 48),
        // so it could sit much earlier; it is called from here because a
        // stage-ordering slip costs a full ~40-minute build to discover and
        // this position is unconditionally safe.
        self.add_beta_bd_embedding()?;

        // Link 4 (`fuel_adequacy.rs`): the algorithm-matched well-founded order
        // plus accessibility -> fuel. Must follow `def_eq_fuel`, since the fuel
        // witness quantifies over `whnf_fuel_red` at the same environment.
        self.add_fuel_adequacy()?;

        // Fuel monotonicity (`defeq_fuel_mono.rs`). Must follow both
        // `def_eq_struct` (it traverses the grid) and `def_eq_fuel_of_struct`
        // (it rebuilds acceptances one fuel level up).
        self.add_defeq_fuel_mono()?;

        // Descent (`rbelow_descent.rs`): whnf components inherit accessibility.
        // Must follow `add_fuel_adequacy`, which declares the rbelow order.
        self.add_rbelow_descent()?;

        // Head rigidity (`kexpr_discr.rs`): generic constructor discrimination
        // plus the lit / bvar reduction inversions the capstone needs.
        self.add_kexpr_discr()?;

        // The last head-rigidity inversion (`proj_rigidity.rs`).
        self.add_proj_rigidity()?;

        // What a whnf cannot be (`whnf_shape.rs`) — let_ and beta-redex
        // exclusions, routed through the UNCONDITIONAL whnf_fuel_red_no_redex
        // so the capstone inherits no closedness premises.
        self.add_whnf_shape()?;

        // Result-side classification + the capstone's target type
        // (`whnf_classify.rs`).
        self.add_whnf_classify()?;

        // Stuck spines are iota/delta-immune (`stuck_immunity.rs`) — closes the
        // iota_immune gap the program's scoping audit recorded as open.
        self.add_stuck_immunity()?;

        // Head rigidity for stuck-headed applications (`stuck_app_rigidity.rs`)
        // — the shape iota_neutral does not cover.
        self.add_stuck_app_rigidity()?;

        // The shape-only rigid-head predicate (`rigid_app_head.rs`), which
        // unlike whnf_stuck_head IS preserved by reduction.
        self.add_rigid_app_head()?;

        // Preservation of the rigid head under reduction (`rigid_preservation.rs`).
        self.add_rigid_preservation()?;

        // The multi-step application inversion, now unblocked
        // (`rigid_app_inv.rs`).
        self.add_rigid_app_inv()?;

        // Head-tag preservation (`rigid_tag.rs`) — the linear decomposition the
        // capstone's head argument factors through.
        self.add_rigid_tag()?;

        // Two-sided tag agreement + Nat discrimination (`join_tag.rs`).
        self.add_join_tag()?;

        // Normal-form heads = rigid + lam (`nf_head.rs`), and their tag
        // stability — the form the capstone case-splits on.
        self.add_nf_head()?;

        // Tag agreement forces the head SHAPE (`nf_shape.rs`) — six sibling
        // lemmas in place of one 36-arm grid.
        self.add_nf_shape()?;

        // Common-bound fuel pairing (`fuel_pairing.rs`) — the last assembly
        // plumbing the capstone needs.
        self.add_fuel_pairing()?;

        // ONE ROUND of completeness over the algorithm's own legs
        // (`defeq_nf_agree.rs`) — the landed def_eq_whnf_complete's premises
        // replaced by dischargeable ones.
        self.add_defeq_nf_agree()?;

        // The JOIN of the two whnf results (`defeq_whnf_join.rs`) — strictly
        // more informative than the tag, and what the capstone consumes.
        self.add_defeq_whnf_join()?;

        // The recursion's per-head STEPS (`defeq_complete_steps.rs`) — where
        // three independent fuels collapse to one.
        self.add_defeq_complete_steps()?;

        // The recursion's LEAF steps (`defeq_complete_leaves.rs`) — heads with
        // no components, hence no fuel collapse.
        self.add_defeq_complete_leaves()?;

        // Component joins for the binder heads (`binder_join_components.rs`) —
        // what lets the recursion actually descend.
        self.add_binder_join_components()?;

        // Component joins for the spine heads (`spine_join_components.rs`) —
        // application (two variants) and projection.
        self.add_spine_join_components()?;

        // One completeness ROUND per binder head (`defeq_round_binder.rs`),
        // given the recursion as a hypothesis.
        self.add_defeq_round_binder()?;

        // The application round (`defeq_round_app.rs`) — four evidence
        // combinations collapsed to one lemma via a shared witness.
        self.add_defeq_round_app()?;

        // Rounds at the leaf heads (`defeq_round_leaf.rs`) — no recursion,
        // payload equality derived from the meet.
        self.add_defeq_round_leaf()?;

        // The last two rounds (`defeq_round_rest.rs`): const, whose
        // delta-deadness is derived from the loop, and proj.
        self.add_defeq_round_rest()?;

        // Choosing an application leg-inverter from nf_head alone
        // (`nf_app_leg.rs`) — eight leaves once, instead of 64 in the dispatch.
        self.add_nf_app_leg()?;

        // THE CAPSTONE (`defeq_capstone.rs`): the eight-leaf dispatch and the
        // rbelow_plus_acc induction that supplies its recursion.
        self.add_defeq_capstone()?;
        // Registered immediately after the capstone, deliberately: the
        // refutation of the capstone's own last premise must not be able to
        // drift away from it.
        self.add_hnf_refutation()?;
        // The first supply for `iota_immune` at an application. Registered LAST
        // on purpose: registration is sequential and aborts at the first
        // elaboration failure, so anything ordered ahead of the refutation can
        // prevent the refutation from ever being checked. It was ordered first
        // once and did exactly that, costing a validation cycle. Nothing above
        // consumes it, so last is both safe and cheaper to iterate on.
        self.add_iota_immunity()?;

        Ok(())
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-polymorphism rung (7th fragment increment, opener): the SEMANTIC
//! Level theory — valuation semantics `evalL`, level substitution `substL`,
//! the semantic order `levelLeqSem`/`levelEqSem`, and the substitution-
//! stability theorems. Ported from the Aristotle-proven strategy guide
//! `scratch/aristotle-harvest/r3-univ-poly/.../UnivPoly.lean` (all four
//! targets proven there: evalL_substL, levelLeq/Eq_subst_stable,
//! typing_level_subst) — per the no-masquerade rule each term below is
//! RE-DERIVED against the live spec `Level` (param carries `Name`, not the
//! mirror's positional `Nat`) and kernel-checked; the Lean proof is a
//! strategy guide only.
//!
//! WHY SEMANTIC: the syntactic `level_leb` in `env_extensions.rs` is
//! deliberately conservative (it cannot see `a <= max a b`; documented at
//! env_extensions.rs:420-430 as the FieldsBounded completeness ceiling). The
//! valuation semantics makes the order COMPLETE for such facts:
//! `levelLeq_max_left` below IS `a <= max a b`, proven, zero axioms — the
//! lemma that unlocks FieldsBounded completeness when the conv/const ctor
//! arms land. The imax trap (naive syntactic monotonicity is FALSE for
//! imax) is dodged the same way: stability under substitution is proven
//! SEMANTICALLY via `evalL_substL` (substitution reindexes valuations).
//!
//! Census stays PINNED at 11 with zero domain axioms; every def here is an
//! `add_recursive_def` explicit term (no tactics, no axioms).

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Universe-polymorphism rung: semantic Level theory. Registered AFTER
    /// `add_snschema` (terminal lemma layer; consumes only foundation
    /// Nat/Bool/Le + Level + Eq machinery, all registered far earlier).
    pub(super) fn add_univ_poly(&mut self) -> Result<(), SpecError> {
        // ── natMax: the standard double-recursion max on Nat.
        //    max 0 b = b; max (succ a) 0 = succ a; max (succ a)(succ b) = succ (max a b).
        self.add_recursive_def(
            "def natMax (a : Nat) (b : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat -> Nat) (fun (b0 : Nat) => b0) (fun (a0 : Nat) (ih : Nat -> Nat) => fun (b0 : Nat) => Nat.rec (fun (_ : Nat) => Nat) (Nat.succ a0) (fun (b1 : Nat) (_ : Nat) => Nat.succ (ih b1)) b0) a b",
            "natMax a b: maximum on Nat (double Nat.rec; 0/b -> b, succ/0 -> succ a, succ/succ -> succ of max). UnivPoly rung.",
        )?;
        // ── imaxNat: the impredicative-max SEMANTICS on Nat —
        //    imaxNat a 0 = 0 (a Prop-codomain collapses), imaxNat a (succ b) = natMax a (succ b).
        self.add_recursive_def(
            "def imaxNat (a : Nat) (b : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (b0 : Nat) (_ : Nat) => natMax a (Nat.succ b0)) b",
            "imaxNat a b: the imax valuation semantics (0 when b=0, else natMax). UnivPoly rung.",
        )?;
        // ── evalL: valuation semantics of Level — a valuation v : Name -> Nat
        //    interprets params; zero/succ/max/imax homomorphically (imax via imaxNat).
        self.add_recursive_def(
            "def evalL (v : Name -> Nat) (l : Level) : Nat := Level.rec (fun (_ : Level) => Nat) Nat.zero (fun (l0 : Level) (ih : Nat) => Nat.succ ih) (fun (a : Level) (b : Level) (iha : Nat) (ihb : Nat) => natMax iha ihb) (fun (a : Level) (b : Level) (iha : Nat) (ihb : Nat) => imaxNat iha ihb) (fun (n : Name) => v n) l",
            "evalL v l: valuation semantics of a Level under v : Name -> Nat (Level.rec; imax via imaxNat). The semantic ground of the universe-polymorphism rung. UnivPoly rung.",
        )?;
        // ── substL: level substitution — param n ↦ s n, homomorphic elsewhere.
        self.add_recursive_def(
            "def substL (s : Name -> Level) (l : Level) : Level := Level.rec (fun (_ : Level) => Level) Level.zero (fun (l0 : Level) (ih : Level) => Level.succ ih) (fun (a : Level) (b : Level) (iha : Level) (ihb : Level) => Level.max iha ihb) (fun (a : Level) (b : Level) (iha : Level) (ihb : Level) => Level.imax iha ihb) (fun (n : Name) => s n) l",
            "substL s l: level substitution (param n -> s n, homomorphic elsewhere). The instantiation operation of universe polymorphism. UnivPoly rung.",
        )?;
        // ── The semantic order and equivalence: forall-valuations. This is the
        //    definition that makes stability-under-substitution PROVABLE (the
        //    syntactic route is false for imax).
        self.add_recursive_def(
            "def levelLeqSem (a : Level) (b : Level) : Prop := forall (v : Name -> Nat), Le (evalL v a) (evalL v b)",
            "levelLeqSem a b: semantic level order (Le under every valuation). Complete for facts the syntactic level_leb cannot see (a <= max a b). UnivPoly rung.",
        )?;
        self.add_recursive_def(
            "def levelEqSem (a : Level) (b : Level) : Prop := forall (v : Name -> Nat), Eq Nat (evalL v a) (evalL v b)",
            "levelEqSem a b: semantic level equivalence (equal under every valuation). UnivPoly rung.",
        )?;
        // ── le_natMax_left: a <= max a b — the semantic fact behind
        //    levelLeq_max_left. Nat.rec on a with inner Nat.rec on b; every arm
        //    lands on a natMax defeq firing. Reuses the pre-existing spec Le kit
        //    (le_zero_n / le_succ_succ — already registered by earlier stages).
        self.add_recursive_def(
            "def le_natMax_left (a : Nat) : forall (b : Nat), Le a (natMax a b) := Nat.rec (fun (a0 : Nat) => forall (b : Nat), Le a0 (natMax a0 b)) (fun (b : Nat) => le_zero_n (natMax Nat.zero b)) (fun (a0 : Nat) (ih : forall (b : Nat), Le a0 (natMax a0 b)) => fun (b : Nat) => Nat.rec (fun (b0 : Nat) => Le (Nat.succ a0) (natMax (Nat.succ a0) b0)) (Le.refl (Nat.succ a0)) (fun (b0 : Nat) (_ : Le (Nat.succ a0) (natMax (Nat.succ a0) b0)) => le_succ_succ a0 (natMax a0 b0) (ih b0)) b) a",
            "Le a (natMax a b) (double Nat.rec; 0-arm le_zero_n, succ/0 refl via natMax defeq, succ/succ le_succ_succ of ih). UnivPoly rung kit.",
        )?;
        // ── THE punchline the conservative level_leb cannot see: a <= max a b at
        //    the LEVEL layer, semantically, zero axioms. Defeq: evalL v (Level.max
        //    a b) fires to natMax (evalL v a) (evalL v b).
        self.add_recursive_def(
            "def levelLeq_max_left (a : Level) (b : Level) : levelLeqSem a (Level.max a b) := fun (v : Name -> Nat) => le_natMax_left (evalL v a) (evalL v b)",
            "levelLeqSem a (max a b) — THE completeness fact the syntactic level_leb cannot prove (env_extensions FieldsBounded ceiling), one line semantically. UnivPoly rung.",
        )?;
        // ── evalL_substL: THE substitution-evaluation theorem — substitution
        //    reindexes valuations: evalL v (substL s l) = evalL (v ∘ evalL-of-s) l.
        //    Level.rec, 5 arms: zero/param rfl, succ one cong, max/imax two-cong
        //    chains into natMax/imaxNat (both sides fire by defeq). Ported from
        //    the guide's evalL_substL (structural induction).
        self.add_recursive_def(
            "def evalL_substL (v : Name -> Nat) (s : Name -> Level) (l : Level) : Eq Nat (evalL v (substL s l)) (evalL (fun (n : Name) => evalL v (s n)) l) := Level.rec (fun (l0 : Level) => Eq Nat (evalL v (substL s l0)) (evalL (fun (n : Name) => evalL v (s n)) l0)) (Eq.refl Nat Nat.zero) (fun (l0 : Level) (ih : Eq Nat (evalL v (substL s l0)) (evalL (fun (n : Name) => evalL v (s n)) l0)) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (evalL v (substL s l0)) (evalL (fun (n : Name) => evalL v (s n)) l0) ih) (fun (a : Level) (b : Level) (iha : Eq Nat (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a)) (ihb : Eq Nat (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b)) => Eq.trans Nat (natMax (evalL v (substL s a)) (evalL v (substL s b))) (natMax (evalL (fun (n : Name) => evalL v (s n)) a) (evalL v (substL s b))) (natMax (evalL (fun (n : Name) => evalL v (s n)) a) (evalL (fun (n : Name) => evalL v (s n)) b)) (Eq.cong Nat Nat (fun (w : Nat) => natMax w (evalL v (substL s b))) (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a) iha) (Eq.cong Nat Nat (fun (w : Nat) => natMax (evalL (fun (n : Name) => evalL v (s n)) a) w) (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b) ihb)) (fun (a : Level) (b : Level) (iha : Eq Nat (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a)) (ihb : Eq Nat (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b)) => Eq.trans Nat (imaxNat (evalL v (substL s a)) (evalL v (substL s b))) (imaxNat (evalL (fun (n : Name) => evalL v (s n)) a) (evalL v (substL s b))) (imaxNat (evalL (fun (n : Name) => evalL v (s n)) a) (evalL (fun (n : Name) => evalL v (s n)) b)) (Eq.cong Nat Nat (fun (w : Nat) => imaxNat w (evalL v (substL s b))) (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a) iha) (Eq.cong Nat Nat (fun (w : Nat) => imaxNat (evalL (fun (n : Name) => evalL v (s n)) a) w) (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b) ihb)) (fun (n : Name) => Eq.refl Nat (evalL v (s n))) l",
            "evalL v (substL s l) = evalL (fun n => evalL v (s n)) l — level substitution reindexes valuations (Level.rec; zero/param rfl, succ cong, max/imax two-cong chains). THE substitution-evaluation theorem of the universe-polymorphism rung. UnivPoly rung.",
        )?;
        // ── Stability of the semantic order/equivalence under substitution — the
        //    instantiation-soundness core (this is where naive syntactic
        //    monotonicity dies on imax; the semantic route composes valuations).
        self.add_recursive_def(
            "def levelLeq_subst_stable (s : Name -> Level) (a : Level) (b : Level) (h : levelLeqSem a b) : levelLeqSem (substL s a) (substL s b) := fun (v : Name -> Nat) => Eq.substType Nat (fun (x : Nat) => Le x (evalL v (substL s b))) (evalL (fun (n : Name) => evalL v (s n)) a) (evalL v (substL s a)) (Eq.symm Nat (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a) (evalL_substL v s a)) (Eq.substType Nat (fun (y : Nat) => Le (evalL (fun (n : Name) => evalL v (s n)) a) y) (evalL (fun (n : Name) => evalL v (s n)) b) (evalL v (substL s b)) (Eq.symm Nat (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b) (evalL_substL v s b)) (h (fun (n : Name) => evalL v (s n))))",
            "levelLeqSem a b -> levelLeqSem (substL s a) (substL s b) — the semantic order is stable under level substitution (h at the composed valuation, transported along evalL_substL twice). Instantiation soundness for the level order. UnivPoly rung.",
        )?;
        self.add_recursive_def(
            "def levelEq_subst_stable (s : Name -> Level) (a : Level) (b : Level) (h : levelEqSem a b) : levelEqSem (substL s a) (substL s b) := fun (v : Name -> Nat) => Eq.trans Nat (evalL v (substL s a)) (evalL (fun (n : Name) => evalL v (s n)) a) (evalL v (substL s b)) (evalL_substL v s a) (Eq.trans Nat (evalL (fun (n : Name) => evalL v (s n)) a) (evalL (fun (n : Name) => evalL v (s n)) b) (evalL v (substL s b)) (h (fun (n : Name) => evalL v (s n))) (Eq.symm Nat (evalL v (substL s b)) (evalL (fun (n : Name) => evalL v (s n)) b) (evalL_substL v s b)))",
            "levelEqSem a b -> levelEqSem (substL s a) (substL s b) — semantic level equivalence is stable under substitution (Eq.trans chain through the composed valuation). UnivPoly rung.",
        )?;

        // ── Brick A2: the const-instantiation layer (guide §3). mapLL (Level-list
        //    map — mapLT is KExpr-only), substL composition, positional lookup
        //    list_getD (defaulting Level.zero out of range), paramSubst (the
        //    substitution a const's level list induces), instL (KExpr level
        //    instantiation, over the FULL 9-ctor KExpr — let_/proj/lit arms are
        //    homomorphic, absent from the 6-ctor guide), instLevels (the spec
        //    shape of the kernel's instantiate_level_params in infer_const).
        self.add_recursive_def(
            "def mapLL (f : Level -> Level) (l : ListType Level) : ListType Level := ListType.rec Level (fun (_ : ListType Level) => ListType Level) (ListType.nil Level) (fun (x : Level) (rest : ListType Level) (ih : ListType Level) => ListType.cons Level (f x) ih) l",
            "mapLL f l: map over a Level list (the Level companion of mapLT). UnivPoly rung A2.",
        )?;
        self.add_recursive_def(
            "def substL_substL (s : Name -> Level) (t : Name -> Level) (l : Level) : Eq Level (substL s (substL t l)) (substL (fun (n : Name) => substL s (t n)) l) := Level.rec (fun (l0 : Level) => Eq Level (substL s (substL t l0)) (substL (fun (n : Name) => substL s (t n)) l0)) (Eq.refl Level Level.zero) (fun (l0 : Level) (ih : Eq Level (substL s (substL t l0)) (substL (fun (n : Name) => substL s (t n)) l0)) => Eq.cong Level Level (fun (w : Level) => Level.succ w) (substL s (substL t l0)) (substL (fun (n : Name) => substL s (t n)) l0) ih) (fun (a : Level) (b : Level) (iha : Eq Level (substL s (substL t a)) (substL (fun (n : Name) => substL s (t n)) a)) (ihb : Eq Level (substL s (substL t b)) (substL (fun (n : Name) => substL s (t n)) b)) => Eq.trans Level (Level.max (substL s (substL t a)) (substL s (substL t b))) (Level.max (substL (fun (n : Name) => substL s (t n)) a) (substL s (substL t b))) (Level.max (substL (fun (n : Name) => substL s (t n)) a) (substL (fun (n : Name) => substL s (t n)) b)) (Eq.cong Level Level (fun (w : Level) => Level.max w (substL s (substL t b))) (substL s (substL t a)) (substL (fun (n : Name) => substL s (t n)) a) iha) (Eq.cong Level Level (fun (w : Level) => Level.max (substL (fun (n : Name) => substL s (t n)) a) w) (substL s (substL t b)) (substL (fun (n : Name) => substL s (t n)) b) ihb)) (fun (a : Level) (b : Level) (iha : Eq Level (substL s (substL t a)) (substL (fun (n : Name) => substL s (t n)) a)) (ihb : Eq Level (substL s (substL t b)) (substL (fun (n : Name) => substL s (t n)) b)) => Eq.trans Level (Level.imax (substL s (substL t a)) (substL s (substL t b))) (Level.imax (substL (fun (n : Name) => substL s (t n)) a) (substL s (substL t b))) (Level.imax (substL (fun (n : Name) => substL s (t n)) a) (substL (fun (n : Name) => substL s (t n)) b)) (Eq.cong Level Level (fun (w : Level) => Level.imax w (substL s (substL t b))) (substL s (substL t a)) (substL (fun (n : Name) => substL s (t n)) a) iha) (Eq.cong Level Level (fun (w : Level) => Level.imax (substL (fun (n : Name) => substL s (t n)) a) w) (substL s (substL t b)) (substL (fun (n : Name) => substL s (t n)) b) ihb)) (fun (n : Name) => Eq.refl Level (substL s (t n))) l",
            "substL s (substL t l) = substL (substL s . t) l — level substitution composes (Level.rec; zero/param rfl, succ cong, max/imax two-cong chains). UnivPoly rung A2.",
        )?;
        self.add_recursive_def(
            "def list_getD (l : ListType Level) (i : Nat) : Level := ListType.rec Level (fun (_ : ListType Level) => Nat -> Level) (fun (i0 : Nat) => Level.zero) (fun (x : Level) (rest : ListType Level) (ih : Nat -> Level) => fun (i0 : Nat) => Nat.rec (fun (_ : Nat) => Level) x (fun (i1 : Nat) (_ : Level) => ih i1) i0) l i",
            "list_getD l i: positional Level-list lookup defaulting to zero out of range (unreachable for well-formed consts — the typing rule pins the length). UnivPoly rung A2.",
        )?;
        // nameIdx: position of a name in a decl's level-param name list (none if
        // absent). The spec Level.param carries Name (not the guide's positional
        // Nat), so the instantiation substitution matches the kernel's
        // instantiate_level_params: look the param name up in the decl's
        // param-name list, take the corresponding level from us, else leave the
        // param untouched.
        self.add_recursive_def(
            "def nameIdx (names : ListType Name) (n : Name) : OptionType Nat := ListType.rec Name (fun (_ : ListType Name) => OptionType Nat) (OptionType.none Nat) (fun (x : Name) (rest : ListType Name) (ih : OptionType Nat) => Bool.rec (fun (_ : Bool) => OptionType Nat) (OptionType.rec Nat (fun (_ : OptionType Nat) => OptionType Nat) (OptionType.none Nat) (fun (i : Nat) => OptionType.some Nat (Nat.succ i)) ih) (OptionType.some Nat Nat.zero) (name_eqb n x)) names",
            "nameIdx names n: position of n in a param-name list (Bool.rec on name_eqb; hit -> some 0, miss -> succ-mapped tail lookup). UnivPoly rung A2.",
        )?;
        self.add_recursive_def(
            "def paramSubstN (names : ListType Name) (us : ListType Level) (n : Name) : Level := OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n) (fun (i : Nat) => list_getD us i) (nameIdx names n)",
            "paramSubstN names us: the level substitution a const's level list induces — param n -> us[position of n in names], unknown params untouched (the kernel's instantiate_level_params semantics at spec shape). UnivPoly rung A2.",
        )?;
        // instL: KExpr level instantiation — substL every sort level and every
        // const level-list entry; homomorphic on all 9 constructors (let_/proj/
        // lit arms are the clean-verify extension beyond the 6-ctor guide).
        self.add_recursive_def(
            "def instL (s : Name -> Level) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (u : Level) => KExpr.sort (substL s u)) (fun (i : Nat) => KExpr.bvar i) (fun (f : KExpr) (a : KExpr) (ihf : KExpr) (iha : KExpr) => KExpr.app ihf iha) (fun (A : KExpr) (b : KExpr) (ihA : KExpr) (ihb : KExpr) => KExpr.lam ihA ihb) (fun (A : KExpr) (B : KExpr) (ihA : KExpr) (ihB : KExpr) => KExpr.pi ihA ihB) (fun (n : Name) (us : ListType Level) => KExpr.const n (mapLL (substL s) us)) (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : KExpr) (ihv : KExpr) (ihb : KExpr) => KExpr.let_ ihA ihv ihb) (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : KExpr) => KExpr.proj sn i ihsub) (fun (v : Nat) => KExpr.lit v) e",
            "instL s e: level instantiation over the FULL 9-ctor KExpr (substL on sorts and const level lists, homomorphic elsewhere; bvar/lit untouched). The spec shape of the kernel's level instantiation. UnivPoly rung A2.",
        )?;
        self.add_recursive_def(
            "def instLevels (names : ListType Name) (T : KExpr) (us : ListType Level) : KExpr := instL (paramSubstN names us) T",
            "instLevels names T us: instantiate a declared level-schematic type at a const's level list (the kernel's type.instantiate_level_params(decl.params, us) at spec shape). UnivPoly rung A2.",
        )?;

        // ── sort_injectivity (canonical-cond guide port, re-homed here because it
        // needs kexpr_sort_inj which registers after pi_injectivity_def_eq's stage):
        // DefEq (sort u)(sort v) -> u = v. Same 3-way confluence route as
        // pi_never_defeq_sort — def_eq_joinable strips DefEq to a common reduct, the
        // sort-tower par_cd_sort_injectivity pins it, kexpr_sort_inj drops KExpr->Level.
        // Levels inert (no level-defeq) so the conclusion is syntactic Eq Level.
        // Zero axiom_deps; the 8 i-args project RedEnvFaithful the_red_env inline.
        self.add_recursive_def(
            "def sort_injectivity (hf : RedEnvFaithful the_red_env) (u : Level) (v : Level) (h : DefEq (KExpr.sort u) (KExpr.sort v)) : Eq Level u v := Eq.cong KExpr Level (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => Level) (fun (k : Level) => k) (fun (_ : Nat) => u) (fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => u) (fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => u) (fun (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) => u) (fun (_ : Name) (_ : ListType Level) => u) (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Level) (_ : Level) (_ : Level) => u) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Level) => u) (fun (_ : Nat) => u) e) (KExpr.sort u) (KExpr.sort v) (par_cd_sort_injectivity the_red_env u v (def_eq_joinable (redenv_faithful_i1 the_red_env hf) (redenv_faithful_i2 the_red_env hf) (redenv_faithful_i3 the_red_env hf) (redenv_faithful_i4 the_red_env hf) (redenv_faithful_i5 the_red_env hf) (redenv_faithful_i6 the_red_env hf) (redenv_faithful_i7 the_red_env hf) (redenv_faithful_i8 the_red_env hf) (KExpr.sort u) (KExpr.sort v) h))",
            "sort_injectivity: DefEq (sort u)(sort v) -> u = v via def_eq_joinable -> par_cd_sort_injectivity (Eq KExpr) then an inlined KExpr.rec level-projector + Eq.cong (kexpr_sort_inj is staged later, so inlined). Carries RedEnvFaithful the_red_env; zero axiom_deps. Canonical-cond guide port.",
        )?;

        // ── CUMULATIVITY (Sort subtyping) Phase 1 — ported from the cumulativity
        // guide, reusing the landed semantic Level machinery. Sort cumulativity is
        // the universe-subtyping the real kernel's is_le implements (Sort u accepted
        // where Sort v expected when u <= v). Phase 2 (cumul_transitive) is deferred
        // (needs leSub inversion lemmas not yet in-spec). leSub/HasType are Type-
        // valued judgment inductives (matching the Typing/TypingCtxConv idiom); the
        // semantic order levelLeqSem is COMPLETE for a <= max a b (levelLeq_max_left)
        // where the conservative syntactic level_leb is not.
        self.add_recursive_def(
            "def levelLeqSem_refl (a : Level) : levelLeqSem a a := fun (v : Name -> Nat) => Le.refl (evalL v a)",
            "levelLeqSem_refl: the semantic level order is reflexive (Le.refl pointwise). UnivPoly cumulativity.",
        )?;
        self.add_recursive_def(
            "def levelLeqSem_trans (a : Level) (b : Level) (c : Level) (h1 : levelLeqSem a b) (h2 : levelLeqSem b c) : levelLeqSem a c := fun (v : Name -> Nat) => le_trans (evalL v a) (evalL v b) (evalL v c) (h1 v) (h2 v)",
            "levelLeqSem_trans: the semantic level order is transitive (le_trans pointwise). UnivPoly cumulativity.",
        )?;
        self.add_inductive(
            "inductive leSub : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), leSub e e\n| sortCumul : forall (u : Level) (v : Level), levelLeqSem u v -> leSub (KExpr.sort u) (KExpr.sort v)\n| pi : forall (A1 : KExpr) (A2 : KExpr) (B1 : KExpr) (B2 : KExpr), leSub A2 A1 -> leSub B1 B2 -> leSub (KExpr.pi A1 B1) (KExpr.pi A2 B2)",
            "leSub a b: the cumulative subtyping order (refl; Sort u <= Sort v when levelLeqSem u v; pi contravariant-domain/covariant-codomain). The order is_le implements. UnivPoly cumulativity.",
        )?;
        self.add_inductive(
            "inductive HasType : KExpr -> KExpr -> Type\n| sort : forall (u : Level), HasType (KExpr.sort u) (KExpr.sort (Level.succ u))\n| pi : forall (A : KExpr) (B : KExpr) (u : Level) (v : Level), HasType A (KExpr.sort u) -> HasType B (KExpr.sort v) -> HasType (KExpr.pi A B) (KExpr.sort (Level.imax u v))\n| sub : forall (e : KExpr) (T1 : KExpr) (T2 : KExpr), HasType e T1 -> leSub T1 T2 -> HasType e T2",
            "HasType e T: a context-free typing judgment WITH the cumulative subsumption rule (sub: e:T1, T1<=T2 => e:T2) — the typing entry point of is_le. UnivPoly cumulativity.",
        )?;
        self.add_recursive_def(
            "def cumul_sort_sound (u : Level) (w : Level) : AndType (HasType (KExpr.sort u) (KExpr.sort (Level.succ u))) (leSub (KExpr.sort u) (KExpr.sort (Level.max u w))) := AndType.intro (HasType (KExpr.sort u) (KExpr.sort (Level.succ u))) (leSub (KExpr.sort u) (KExpr.sort (Level.max u w))) (HasType.sort u) (leSub.sortCumul u (Level.max u w) (levelLeq_max_left u w))",
            "cumul_sort_sound u w: the sort-cumulativity base — Sort u : Sort (succ u) AND Sort u <= Sort (max u w) (via levelLeq_max_left). UnivPoly cumulativity target (a).",
        )?;
        self.add_recursive_def(
            "def cumul_pi_sound (e : KExpr) (A1 : KExpr) (A2 : KExpr) (B1 : KExpr) (B2 : KExpr) (he : HasType e (KExpr.pi A1 B1)) (hA : leSub A2 A1) (hB : leSub B1 B2) : HasType e (KExpr.pi A2 B2) := HasType.sub e (KExpr.pi A1 B1) (KExpr.pi A2 B2) he (leSub.pi A1 A2 B1 B2 hA hB)",
            "cumul_pi_sound: pi subtyping soundness (contravariant domain, covariant codomain) — e : pi A1 B1, A2<=A1, B1<=B2 => e : pi A2 B2. UnivPoly cumulativity target (b).",
        )?;

        // ── UnivPoly typing Phase 1: instL / level-instantiation commutation
        // lemmas (complete proof terms ported from the univ-poly2 guide). These are
        // the load-bearing facts for typing_level_subst (the rung theorem, deferred
        // with TypingP). All KExpr.rec/ListType.rec inductions, zero axioms.
        self.add_recursive_def(
            "def instL_lift_bvar_at (s : Name -> Level) (i : Nat) (c : Nat) (am : Nat) : Eq KExpr (instL s (lift_bvar_at i c am)) (lift_bvar_at i c am) := Nat.rec (fun (k : Nat) => Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i am)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i am)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (Eq.refl KExpr (KExpr.bvar (Nat.add i am))) (fun (k : Nat) (_ : Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i am)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i am)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) => Eq.refl KExpr (KExpr.bvar i)) (Nat.sub c i)",
            "instL_lift_bvar_at: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_lift_at (s : Name -> Level) (e : KExpr) (c : Nat) (am : Nat) : Eq KExpr (instL s (lift_at e c am)) (lift_at (instL s e) c am) := KExpr.rec (fun (e0 : KExpr) => forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at e0 c am)) (lift_at (instL s e0) c am)) (fun (u : Level) (c : Nat) (am : Nat) => Eq.refl KExpr (KExpr.sort (substL s u))) (fun (i : Nat) (c : Nat) (am : Nat) => instL_lift_bvar_at s i c am) (fun (f : KExpr) (a : KExpr) (ihf : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at f c am)) (lift_at (instL s f) c am)) (iha : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at a c am)) (lift_at (instL s a) c am)) (c : Nat) (am : Nat) => Eq.trans KExpr (KExpr.app (instL s (lift_at f c am)) (instL s (lift_at a c am))) (KExpr.app (lift_at (instL s f) c am) (instL s (lift_at a c am))) (KExpr.app (lift_at (instL s f) c am) (lift_at (instL s a) c am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (instL s (lift_at a c am))) (instL s (lift_at f c am)) (lift_at (instL s f) c am) (ihf c am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (lift_at (instL s f) c am) w) (instL s (lift_at a c am)) (lift_at (instL s a) c am) (iha c am))) (fun (A : KExpr) (b : KExpr) (ihA : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at A c am)) (lift_at (instL s A) c am)) (ihb : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at b c am)) (lift_at (instL s b) c am)) (c : Nat) (am : Nat) => Eq.trans KExpr (KExpr.lam (instL s (lift_at A c am)) (instL s (lift_at b (Nat.succ c) am))) (KExpr.lam (lift_at (instL s A) c am) (instL s (lift_at b (Nat.succ c) am))) (KExpr.lam (lift_at (instL s A) c am) (lift_at (instL s b) (Nat.succ c) am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (instL s (lift_at b (Nat.succ c) am))) (instL s (lift_at A c am)) (lift_at (instL s A) c am) (ihA c am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (lift_at (instL s A) c am) w) (instL s (lift_at b (Nat.succ c) am)) (lift_at (instL s b) (Nat.succ c) am) (ihb (Nat.succ c) am))) (fun (A : KExpr) (b : KExpr) (ihA : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at A c am)) (lift_at (instL s A) c am)) (ihb : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at b c am)) (lift_at (instL s b) c am)) (c : Nat) (am : Nat) => Eq.trans KExpr (KExpr.pi (instL s (lift_at A c am)) (instL s (lift_at b (Nat.succ c) am))) (KExpr.pi (lift_at (instL s A) c am) (instL s (lift_at b (Nat.succ c) am))) (KExpr.pi (lift_at (instL s A) c am) (lift_at (instL s b) (Nat.succ c) am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (instL s (lift_at b (Nat.succ c) am))) (instL s (lift_at A c am)) (lift_at (instL s A) c am) (ihA c am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (lift_at (instL s A) c am) w) (instL s (lift_at b (Nat.succ c) am)) (lift_at (instL s b) (Nat.succ c) am) (ihb (Nat.succ c) am))) (fun (n : Name) (us : ListType Level) (c : Nat) (am : Nat) => Eq.refl KExpr (KExpr.const n (mapLL (substL s) us))) (fun (ty : KExpr) (vv : KExpr) (bb : KExpr) (ihty : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at ty c am)) (lift_at (instL s ty) c am)) (ihv : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at vv c am)) (lift_at (instL s vv) c am)) (ihb : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at bb c am)) (lift_at (instL s bb) c am)) (c : Nat) (am : Nat) => Eq.trans KExpr (KExpr.let_ (instL s (lift_at ty c am)) (instL s (lift_at vv c am)) (instL s (lift_at bb (Nat.succ c) am))) (KExpr.let_ (lift_at (instL s ty) c am) (instL s (lift_at vv c am)) (instL s (lift_at bb (Nat.succ c) am))) (KExpr.let_ (lift_at (instL s ty) c am) (lift_at (instL s vv) c am) (lift_at (instL s bb) (Nat.succ c) am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (instL s (lift_at vv c am)) (instL s (lift_at bb (Nat.succ c) am))) (instL s (lift_at ty c am)) (lift_at (instL s ty) c am) (ihty c am)) (Eq.trans KExpr (KExpr.let_ (lift_at (instL s ty) c am) (instL s (lift_at vv c am)) (instL s (lift_at bb (Nat.succ c) am))) (KExpr.let_ (lift_at (instL s ty) c am) (lift_at (instL s vv) c am) (instL s (lift_at bb (Nat.succ c) am))) (KExpr.let_ (lift_at (instL s ty) c am) (lift_at (instL s vv) c am) (lift_at (instL s bb) (Nat.succ c) am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (lift_at (instL s ty) c am) w (instL s (lift_at bb (Nat.succ c) am))) (instL s (lift_at vv c am)) (lift_at (instL s vv) c am) (ihv c am)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (lift_at (instL s ty) c am) (lift_at (instL s vv) c am) w) (instL s (lift_at bb (Nat.succ c) am)) (lift_at (instL s bb) (Nat.succ c) am) (ihb (Nat.succ c) am)))) (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : forall (c : Nat) (am : Nat), Eq KExpr (instL s (lift_at sub c am)) (lift_at (instL s sub) c am)) (c : Nat) (am : Nat) => Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj sn i w) (instL s (lift_at sub c am)) (lift_at (instL s sub) c am) (ihsub c am)) (fun (v : Nat) (c : Nat) (am : Nat) => Eq.refl KExpr (KExpr.lit v)) e c am",
            "instL_lift_at: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_lift (s : Name -> Level) (e : KExpr) (am : Nat) : Eq KExpr (instL s (lift e am)) (lift (instL s e) am) := instL_lift_at s e Nat.zero am",
            "instL_lift: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_instantiate_bvar_geq (s : Name -> Level) (i : Nat) (d : Nat) (val : KExpr) : Eq KExpr (instL s (instantiate_bvar_geq i d val)) (instantiate_bvar_geq i d (instL s val)) := Nat.rec (fun (k : Nat) => Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (lift_at val Nat.zero d) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) (Nat.rec (fun (_ : Nat) => KExpr) (lift_at (instL s val) Nat.zero d) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) (instL_lift_at s val Nat.zero d) (fun (k : Nat) (_ : Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (lift_at val Nat.zero d) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) (Nat.rec (fun (_ : Nat) => KExpr) (lift_at (instL s val) Nat.zero d) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub i (Nat.succ Nat.zero))) k)) => Eq.refl KExpr (KExpr.bvar (Nat.sub i (Nat.succ Nat.zero)))) (Nat.sub i d)",
            "instL_instantiate_bvar_geq: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_instantiate_bvar_at (s : Name -> Level) (i : Nat) (d : Nat) (val : KExpr) : Eq KExpr (instL s (instantiate_bvar_at i d val)) (instantiate_bvar_at i d (instL s val)) := Nat.rec (fun (k : Nat) => Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d val) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d (instL s val)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (instL_instantiate_bvar_geq s i d val) (fun (k : Nat) (_ : Eq KExpr (instL s (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d val) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) (Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq i d (instL s val)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) => Eq.refl KExpr (KExpr.bvar i)) (Nat.sub d i)",
            "instL_instantiate_bvar_at: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_instantiate_at (s : Name -> Level) (b : KExpr) (val : KExpr) (d : Nat) : Eq KExpr (instL s (instantiate_at b val d)) (instantiate_at (instL s b) (instL s val) d) := KExpr.rec (fun (b0 : KExpr) => forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at b0 val d)) (instantiate_at (instL s b0) (instL s val) d)) (fun (u : Level) (val : KExpr) (d : Nat) => Eq.refl KExpr (KExpr.sort (substL s u))) (fun (i : Nat) (val : KExpr) (d : Nat) => instL_instantiate_bvar_at s i d val) (fun (f : KExpr) (a : KExpr) (ihf : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at f val d)) (instantiate_at (instL s f) (instL s val) d)) (iha : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at a val d)) (instantiate_at (instL s a) (instL s val) d)) (val : KExpr) (d : Nat) => Eq.trans KExpr (KExpr.app (instL s (instantiate_at f val d)) (instL s (instantiate_at a val d))) (KExpr.app (instantiate_at (instL s f) (instL s val) d) (instL s (instantiate_at a val d))) (KExpr.app (instantiate_at (instL s f) (instL s val) d) (instantiate_at (instL s a) (instL s val) d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (instL s (instantiate_at a val d))) (instL s (instantiate_at f val d)) (instantiate_at (instL s f) (instL s val) d) (ihf val d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (instantiate_at (instL s f) (instL s val) d) w) (instL s (instantiate_at a val d)) (instantiate_at (instL s a) (instL s val) d) (iha val d))) (fun (A : KExpr) (bb : KExpr) (ihA : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at A val d)) (instantiate_at (instL s A) (instL s val) d)) (ihb : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at bb val d)) (instantiate_at (instL s bb) (instL s val) d)) (val : KExpr) (d : Nat) => Eq.trans KExpr (KExpr.lam (instL s (instantiate_at A val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.lam (instantiate_at (instL s A) (instL s val) d) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.lam (instantiate_at (instL s A) (instL s val) d) (instantiate_at (instL s bb) (instL s val) (Nat.succ d))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (instL s (instantiate_at bb val (Nat.succ d)))) (instL s (instantiate_at A val d)) (instantiate_at (instL s A) (instL s val) d) (ihA val d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (instantiate_at (instL s A) (instL s val) d) w) (instL s (instantiate_at bb val (Nat.succ d))) (instantiate_at (instL s bb) (instL s val) (Nat.succ d)) (ihb val (Nat.succ d)))) (fun (A : KExpr) (bb : KExpr) (ihA : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at A val d)) (instantiate_at (instL s A) (instL s val) d)) (ihb : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at bb val d)) (instantiate_at (instL s bb) (instL s val) d)) (val : KExpr) (d : Nat) => Eq.trans KExpr (KExpr.pi (instL s (instantiate_at A val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.pi (instantiate_at (instL s A) (instL s val) d) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.pi (instantiate_at (instL s A) (instL s val) d) (instantiate_at (instL s bb) (instL s val) (Nat.succ d))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (instL s (instantiate_at bb val (Nat.succ d)))) (instL s (instantiate_at A val d)) (instantiate_at (instL s A) (instL s val) d) (ihA val d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (instantiate_at (instL s A) (instL s val) d) w) (instL s (instantiate_at bb val (Nat.succ d))) (instantiate_at (instL s bb) (instL s val) (Nat.succ d)) (ihb val (Nat.succ d)))) (fun (n : Name) (us : ListType Level) (val : KExpr) (d : Nat) => Eq.refl KExpr (KExpr.const n (mapLL (substL s) us))) (fun (ty : KExpr) (vv : KExpr) (bb : KExpr) (ihty : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at ty val d)) (instantiate_at (instL s ty) (instL s val) d)) (ihv : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at vv val d)) (instantiate_at (instL s vv) (instL s val) d)) (ihb : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at bb val d)) (instantiate_at (instL s bb) (instL s val) d)) (val : KExpr) (d : Nat) => Eq.trans KExpr (KExpr.let_ (instL s (instantiate_at ty val d)) (instL s (instantiate_at vv val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instL s (instantiate_at vv val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instantiate_at (instL s vv) (instL s val) d) (instantiate_at (instL s bb) (instL s val) (Nat.succ d))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (instL s (instantiate_at vv val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (instL s (instantiate_at ty val d)) (instantiate_at (instL s ty) (instL s val) d) (ihty val d)) (Eq.trans KExpr (KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instL s (instantiate_at vv val d)) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instantiate_at (instL s vv) (instL s val) d) (instL s (instantiate_at bb val (Nat.succ d)))) (KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instantiate_at (instL s vv) (instL s val) d) (instantiate_at (instL s bb) (instL s val) (Nat.succ d))) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) w (instL s (instantiate_at bb val (Nat.succ d)))) (instL s (instantiate_at vv val d)) (instantiate_at (instL s vv) (instL s val) d) (ihv val d)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (instantiate_at (instL s ty) (instL s val) d) (instantiate_at (instL s vv) (instL s val) d) w) (instL s (instantiate_at bb val (Nat.succ d))) (instantiate_at (instL s bb) (instL s val) (Nat.succ d)) (ihb val (Nat.succ d))))) (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : forall (val : KExpr) (d : Nat), Eq KExpr (instL s (instantiate_at sub val d)) (instantiate_at (instL s sub) (instL s val) d)) (val : KExpr) (d : Nat) => Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj sn i w) (instL s (instantiate_at sub val d)) (instantiate_at (instL s sub) (instL s val) d) (ihsub val d)) (fun (v : Nat) (val : KExpr) (d : Nat) => Eq.refl KExpr (KExpr.lit v)) b val d",
            "instL_instantiate_at: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_instantiate (s : Name -> Level) (b : KExpr) (val : KExpr) : Eq KExpr (instL s (instantiate b val)) (instantiate (instL s b) (instL s val)) := instL_instantiate_at s b val Nat.zero",
            "instL_instantiate: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def mapLL_mapLL (s : Name -> Level) (t : Name -> Level) (us : ListType Level) : Eq (ListType Level) (mapLL (substL s) (mapLL (substL t) us)) (mapLL (substL (fun (n : Name) => substL s (t n))) us) := ListType.rec Level (fun (u0 : ListType Level) => Eq (ListType Level) (mapLL (substL s) (mapLL (substL t) u0)) (mapLL (substL (fun (n : Name) => substL s (t n))) u0)) (Eq.refl (ListType Level) (ListType.nil Level)) (fun (x : Level) (rest : ListType Level) (ih : Eq (ListType Level) (mapLL (substL s) (mapLL (substL t) rest)) (mapLL (substL (fun (n : Name) => substL s (t n))) rest)) => Eq.trans (ListType Level) (ListType.cons Level (substL s (substL t x)) (mapLL (substL s) (mapLL (substL t) rest))) (ListType.cons Level (substL (fun (n : Name) => substL s (t n)) x) (mapLL (substL s) (mapLL (substL t) rest))) (ListType.cons Level (substL (fun (n : Name) => substL s (t n)) x) (mapLL (substL (fun (n : Name) => substL s (t n))) rest)) (Eq.cong Level (ListType Level) (fun (w : Level) => ListType.cons Level w (mapLL (substL s) (mapLL (substL t) rest))) (substL s (substL t x)) (substL (fun (n : Name) => substL s (t n)) x) (substL_substL s t x)) (Eq.cong (ListType Level) (ListType Level) (fun (w : ListType Level) => ListType.cons Level (substL (fun (n : Name) => substL s (t n)) x) w) (mapLL (substL s) (mapLL (substL t) rest)) (mapLL (substL (fun (n : Name) => substL s (t n))) rest) ih)) us",
            "mapLL_mapLL: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def list_getD_mapLL (s : Name -> Level) (us : ListType Level) (i : Nat) : Eq Level (list_getD (mapLL (substL s) us) i) (substL s (list_getD us i)) := ListType.rec Level (fun (u0 : ListType Level) => forall (i : Nat), Eq Level (list_getD (mapLL (substL s) u0) i) (substL s (list_getD u0 i))) (fun (i : Nat) => Eq.refl Level Level.zero) (fun (x : Level) (rest : ListType Level) (ih : forall (i : Nat), Eq Level (list_getD (mapLL (substL s) rest) i) (substL s (list_getD rest i))) => fun (i : Nat) => Nat.rec (fun (j : Nat) => Eq Level (list_getD (mapLL (substL s) (ListType.cons Level x rest)) j) (substL s (list_getD (ListType.cons Level x rest) j))) (Eq.refl Level (substL s x)) (fun (j : Nat) (_ : Eq Level (list_getD (mapLL (substL s) (ListType.cons Level x rest)) j) (substL s (list_getD (ListType.cons Level x rest) j))) => ih j) i) us i",
            "list_getD_mapLL: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;
        self.add_recursive_def(
            "def instL_instL (s : Name -> Level) (t : Name -> Level) (e : KExpr) : Eq KExpr (instL s (instL t e)) (instL (fun (nm : Name) => substL s (t nm)) e) := KExpr.rec (fun (e0 : KExpr) => Eq KExpr (instL s (instL t e0)) (instL (fun (nm : Name) => substL s (t nm)) e0)) (fun (u : Level) => Eq.cong Level KExpr (fun (w : Level) => KExpr.sort w) (substL s (substL t u)) (substL (fun (nm : Name) => substL s (t nm)) u) (substL_substL s t u)) (fun (i : Nat) => Eq.refl KExpr (KExpr.bvar i)) (fun (f : KExpr) (a : KExpr) (ihf : Eq KExpr (instL s (instL t f)) (instL (fun (nm : Name) => substL s (t nm)) f)) (iha : Eq KExpr (instL s (instL t a)) (instL (fun (nm : Name) => substL s (t nm)) a)) => Eq.trans KExpr (KExpr.app (instL s (instL t f)) (instL s (instL t a))) (KExpr.app (instL (fun (nm : Name) => substL s (t nm)) f) (instL s (instL t a))) (KExpr.app (instL (fun (nm : Name) => substL s (t nm)) f) (instL (fun (nm : Name) => substL s (t nm)) a)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w (instL s (instL t a))) (instL s (instL t f)) (instL (fun (nm : Name) => substL s (t nm)) f) ihf) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app (instL (fun (nm : Name) => substL s (t nm)) f) w) (instL s (instL t a)) (instL (fun (nm : Name) => substL s (t nm)) a) iha)) (fun (A : KExpr) (bb : KExpr) (ihA : Eq KExpr (instL s (instL t A)) (instL (fun (nm : Name) => substL s (t nm)) A)) (ihb : Eq KExpr (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb)) => Eq.trans KExpr (KExpr.lam (instL s (instL t A)) (instL s (instL t bb))) (KExpr.lam (instL (fun (nm : Name) => substL s (t nm)) A) (instL s (instL t bb))) (KExpr.lam (instL (fun (nm : Name) => substL s (t nm)) A) (instL (fun (nm : Name) => substL s (t nm)) bb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam w (instL s (instL t bb))) (instL s (instL t A)) (instL (fun (nm : Name) => substL s (t nm)) A) ihA) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.lam (instL (fun (nm : Name) => substL s (t nm)) A) w) (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb) ihb)) (fun (A : KExpr) (bb : KExpr) (ihA : Eq KExpr (instL s (instL t A)) (instL (fun (nm : Name) => substL s (t nm)) A)) (ihb : Eq KExpr (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb)) => Eq.trans KExpr (KExpr.pi (instL s (instL t A)) (instL s (instL t bb))) (KExpr.pi (instL (fun (nm : Name) => substL s (t nm)) A) (instL s (instL t bb))) (KExpr.pi (instL (fun (nm : Name) => substL s (t nm)) A) (instL (fun (nm : Name) => substL s (t nm)) bb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi w (instL s (instL t bb))) (instL s (instL t A)) (instL (fun (nm : Name) => substL s (t nm)) A) ihA) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.pi (instL (fun (nm : Name) => substL s (t nm)) A) w) (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb) ihb)) (fun (n : Name) (us : ListType Level) => Eq.cong (ListType Level) KExpr (fun (w : ListType Level) => KExpr.const n w) (mapLL (substL s) (mapLL (substL t) us)) (mapLL (substL (fun (nm : Name) => substL s (t nm))) us) (mapLL_mapLL s t us)) (fun (ty : KExpr) (vv : KExpr) (bb : KExpr) (ihty : Eq KExpr (instL s (instL t ty)) (instL (fun (nm : Name) => substL s (t nm)) ty)) (ihv : Eq KExpr (instL s (instL t vv)) (instL (fun (nm : Name) => substL s (t nm)) vv)) (ihb : Eq KExpr (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb)) => Eq.trans KExpr (KExpr.let_ (instL s (instL t ty)) (instL s (instL t vv)) (instL s (instL t bb))) (KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL s (instL t vv)) (instL s (instL t bb))) (KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL (fun (nm : Name) => substL s (t nm)) vv) (instL (fun (nm : Name) => substL s (t nm)) bb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ w (instL s (instL t vv)) (instL s (instL t bb))) (instL s (instL t ty)) (instL (fun (nm : Name) => substL s (t nm)) ty) ihty) (Eq.trans KExpr (KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL s (instL t vv)) (instL s (instL t bb))) (KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL (fun (nm : Name) => substL s (t nm)) vv) (instL s (instL t bb))) (KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL (fun (nm : Name) => substL s (t nm)) vv) (instL (fun (nm : Name) => substL s (t nm)) bb)) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) w (instL s (instL t bb))) (instL s (instL t vv)) (instL (fun (nm : Name) => substL s (t nm)) vv) ihv) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.let_ (instL (fun (nm : Name) => substL s (t nm)) ty) (instL (fun (nm : Name) => substL s (t nm)) vv) w) (instL s (instL t bb)) (instL (fun (nm : Name) => substL s (t nm)) bb) ihb))) (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : Eq KExpr (instL s (instL t sub)) (instL (fun (nm : Name) => substL s (t nm)) sub)) => Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.proj sn i w) (instL s (instL t sub)) (instL (fun (nm : Name) => substL s (t nm)) sub) ihsub) (fun (v : Nat) => Eq.refl KExpr (KExpr.lit v)) e",
            "instL_instL: instL/level-instantiation commutation lemma (univ-poly2 guide, DerivedProved). UnivPoly typing.",
        )?;

        Ok(())
    }
}

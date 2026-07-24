// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! REAL-ENV DISCHARGE — Bricks R0 + R1 (the church_rosser_whnf / def_eq_to_eq
//! retirement metatheory becoming UNCONDITIONAL).
//!
//! Both false axioms are deleted; every retirement proof is conditional on the
//! carried bundle `RedEnvFaithful env` (eight faithful RecEnv/DefEnv interfaces
//! i1..i8), never discharged over the explicit TOY `the_red_env`. This module
//! begins the honest discharge by modelling a FAITHFUL kernel-environment shape
//! `faithful_red_env` and proving the three cheapest faithful interfaces over it
//! — the pure NAME-disjointness obligations i2/i7/i8 — as real `DerivedProved`
//! terms with ZERO domain axioms (no masquerade).
//!
//! ## Brick R0 — the faithful env model
//!
//! `faithful_red_env = RedEnv.mk faithful_rec_env faithful_def_env`, a value-ful
//! `def` (lowers to `Declaration::Definition`, ratchet-clean) modelling a real
//! single-constructor inductive's recursor PLUS a real definition:
//!  - `faithful_rec_env`: one recursor `REC` with NON-degenerate metadata
//!    `RecMeta.mk 0 1 1 0 true` (0 params, 1 motive, 1 minor, 0 indices,
//!    major-after-minors) — the major premise sits at spine position 2, NOT 0,
//!    so `iota_reduct` genuinely exercises the param/motive/minor-skipping spine
//!    logic — and a rule for constructor `CTOR` whose rhs is a CLOSED lambda
//!    template `λ(sort 0). sort 0` (a real pre-built reduct lambda, not the toy's
//!    bare `sort 0`).
//!  - `faithful_def_env`: one definition `DEF` unfolding to a CLOSED lambda value.
//!
//! Genuinely more faithful than `the_red_env` (toy): non-degenerate recursor
//! metadata (major NOT at arg 0), a closed-lambda rule rhs, and a closed-lambda
//! def value — modelling the shape of a real kernel recursor reduction, not a
//! single trivial `RECNAME CNAME -> sort 0` fire. NON-VACUOUS: the two witnesses
//! below show iota AND delta genuinely fire on it.
//!
//! ## Brick R1 — the three name-disjointness interfaces over R0
//!
//! Names are disjoint BY CONSTRUCTION (`REC`/`CTOR`/`DEF` are `str anonymous {0,1,2}`,
//! distinct numerals), so every cross `name_eqb` reduces to `false` and every
//! same-slot `name_eqb` to `true` by pure computation. The proofs invert the
//! `some`-lookup hypothesis (`opt_pick_some_inv` / `opt_bind_some_inv`), recover
//! the matched name via decidable-equality soundness (`name_eqb_eq`), and
//! transport the conclusion onto the now-concrete name, where the cross-slot
//! lookup computes to `none` (`Eq.refl`):
//!  - i2 `RecEnvCtorNoRecMeta (red_rec faithful_red_env)` — a constructor name is
//!    not a recursor name (`recmeta_for ... CTOR = none`).
//!  - i7 `RecEnvDefEnvDisjoint faithful_red_env` — a definition name is not a
//!    recursor name (`recmeta_for ... DEF = none`).
//!  - i8 `RecEnvCtorNoDefVal faithful_red_env` — a constructor name is not a
//!    definition name (`defval_for ... CTOR = none`).
//!
//! The decidable-equality soundness tower (`name_eqb_eq` and its Bool/Nat
//! inversion leaves) is confluence-independent and would otherwise live only in
//! the un-bundled `kexpr_beq_sound` test stage; it is registered here (all
//! `DerivedProved`, zero axiom_deps) so the discharge is self-contained in the
//! full core spec.
//!
//! ## Anti-masquerade
//!
//! ZERO new axioms. Every obligation is a real `DerivedProved` term (Name
//! decidable-equality + structural transport). No FoundationalRule/axiom asserts
//! i2/i7/i8; the R0 model is non-vacuous (iota + delta fire); no
//! sorry/add_decl_unchecked. Later bricks (R2-R5) discharge i1/i3/i4/i5/i6 and
//! assemble `RedEnvFaithful faithful_red_env`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// The three disjoint env name slots (distinct `str anonymous k` numerals).
const REC: &str = "(Name.str Name.anonymous Nat.zero)";
const CTOR: &str = "(Name.str Name.anonymous (Nat.succ Nat.zero))";
const DEFN: &str = "(Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero)))";
// The single recursor rule and its singleton rule list (CTOR, 0 fields, closed-lambda rhs).
const RULE: &str = "(RecRule.mk (Name.str Name.anonymous (Nat.succ Nat.zero)) Nat.zero \
                    (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)))";
const RULES: &str = "(RecRules.cons (RecRule.mk (Name.str Name.anonymous (Nat.succ Nat.zero)) \
                     Nat.zero (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero))) RecRules.nil)";
// The closed-lambda template shared by the recursor rule rhs (= recrule_rhs RULE)
// and the definition value: `λ(sort 0). sort 0`. Closed (no free bvars), so fixed
// by both `instantiate_at` and `lift_at`, and binder-headed (kapp_fn = itself,
// kexpr_const_name = none) so it never re-resolves to an iota redex.
const LAM: &str = "(KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero))";

impl Specification {
    /// A `DerivedProved`, zero-axiom-dep `SpecDefinition` (local mirror of the
    /// `kexpr_beq_sound` helper, which is private to that un-bundled module).
    fn fre_eq_lemma(
        name: &str,
        type_src: &str,
        value_src: &str,
        description: &str,
        deps: &[&str],
    ) -> SpecDefinition {
        SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: description.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(deps.iter().map(|s| (*s).to_string()).collect()),
            axiom_deps: HashSet::new(),
        }
    }

    /// Register Bricks R0 + R1 of the real-env discharge.
    pub(super) fn add_faithful_red_env(&mut self) -> Result<(), SpecError> {
        self.add_decidable_name_eq()?;
        self.add_opt_pick_some_inv()?;
        self.add_faithful_red_env_model()?;
        self.add_faithful_red_env_recrule_inv()?;
        self.add_faithful_red_env_obligations()?;
        Ok(())
    }

    /// The Bool/Nat/Name decidable-equality soundness tower culminating in
    /// `name_eqb_eq : name_eqb a b = true -> a = b`. All confluence-independent,
    /// `DerivedProved`, zero axiom_deps; the substrate (foundation +
    /// `nat_eqb`/`name_eqb`/`nat_is_zero`) is registered in earlier bundle stages.
    ///
    /// This is the SINGLE canonical registration site of the tower
    /// (`bool_false_ne_true` … `name_eqb_eq`). The un-bundled
    /// `kexpr_beq_sound.rs` consumes these names but no longer registers its
    /// own copy — this stage is in the Substitution bundle, so a second
    /// registration is a kernel duplicate-declaration error. `pub(super)` so
    /// that module's minimal (bundle-free) test builder can call it directly.
    pub(super) fn add_decidable_name_eq(&mut self) -> Result<(), SpecError> {
        self.add_definition(Self::fre_eq_lemma(
            "bool_false_ne_true",
            "forall (C : Prop), Eq Bool Bool.false Bool.true -> C",
            "fun (C : Prop) (h : Eq Bool Bool.false Bool.true) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType Bool \
             (fun (z : Bool) => Bool.rec (fun (_ : Bool) => Type) Nat Empty z) \
             Bool.false Bool.true h Nat.zero)",
            "Bool no-confusion: Eq false true is absurd (CPS into any Prop). DerivedProved, zero axiom_deps.",
            &["Bool.rec", "Empty", "Empty.rec", "Eq.substType"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_zero_ne_succ_beq",
            "forall (a : Nat) (C : Prop), Eq Nat Nat.zero (Nat.succ a) -> C",
            "fun (a : Nat) (C : Prop) (h : Eq Nat Nat.zero (Nat.succ a)) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType Nat \
             (fun (z : Nat) => Nat.rec (fun (_ : Nat) => Type) Nat (fun (_ : Nat) (_ : Type) => Empty) z) \
             Nat.zero (Nat.succ a) h Nat.zero)",
            "Nat no-confusion: Eq 0 (succ a) is absurd (CPS into any Prop). DerivedProved, zero axiom_deps.",
            &["Nat.rec", "Empty", "Empty.rec", "Eq.substType"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_is_zero_eq",
            "forall (n : Nat), Eq Bool (nat_is_zero n) Bool.true -> Eq Nat n Nat.zero",
            "fun (n : Nat) => Nat.rec \
             (fun (z : Nat) => Eq Bool (nat_is_zero z) Bool.true -> Eq Nat z Nat.zero) \
             (fun (_ : Eq Bool (nat_is_zero Nat.zero) Bool.true) => Eq.refl Nat Nat.zero) \
             (fun (k : Nat) (_ih : Eq Bool (nat_is_zero k) Bool.true -> Eq Nat k Nat.zero) => \
             fun (h : Eq Bool (nat_is_zero (Nat.succ k)) Bool.true) => \
             bool_false_ne_true (Eq Nat (Nat.succ k) Nat.zero) h) \
             n",
            "nat_is_zero inversion: nat_is_zero n = true -> n = 0. DerivedProved, zero axiom_deps.",
            &["Nat.rec", "Eq.refl", "bool_false_ne_true", "nat_is_zero"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "band_eq_true_left",
            "forall (p : Bool) (q : Bool), Eq Bool (Bool.and p q) Bool.true -> Eq Bool p Bool.true",
            "fun (p : Bool) (q : Bool) => Bool.rec \
             (fun (zp : Bool) => Eq Bool (Bool.and zp q) Bool.true -> Eq Bool zp Bool.true) \
             (fun (h : Eq Bool (Bool.and Bool.false q) Bool.true) => \
             bool_false_ne_true (Eq Bool Bool.false Bool.true) h) \
             (fun (_ : Eq Bool (Bool.and Bool.true q) Bool.true) => Eq.refl Bool Bool.true) \
             p",
            "Bool.and inversion (left): Bool.and p q = true -> p = true. DerivedProved, zero axiom_deps.",
            &["Bool.rec", "Eq.refl", "bool_false_ne_true", "Bool.and"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "band_eq_true_right",
            "forall (p : Bool) (q : Bool), Eq Bool (Bool.and p q) Bool.true -> Eq Bool q Bool.true",
            "fun (p : Bool) (q : Bool) => Bool.rec \
             (fun (zp : Bool) => Eq Bool (Bool.and zp q) Bool.true -> Eq Bool q Bool.true) \
             (fun (h : Eq Bool (Bool.and Bool.false q) Bool.true) => \
             bool_false_ne_true (Eq Bool q Bool.true) h) \
             (fun (h : Eq Bool (Bool.and Bool.true q) Bool.true) => h) \
             p",
            "Bool.and inversion (right): Bool.and p q = true -> q = true. DerivedProved, zero axiom_deps.",
            &["Bool.rec", "bool_false_ne_true", "Bool.and"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_add_eq_zero_right",
            "forall (x : Nat) (y : Nat), Eq Nat (Nat.add x y) Nat.zero -> Eq Nat y Nat.zero",
            "fun (x : Nat) (y : Nat) => Nat.rec \
             (fun (z : Nat) => Eq Nat (Nat.add x z) Nat.zero -> Eq Nat z Nat.zero) \
             (fun (_ : Eq Nat (Nat.add x Nat.zero) Nat.zero) => Eq.refl Nat Nat.zero) \
             (fun (yp : Nat) (_ih : Eq Nat (Nat.add x yp) Nat.zero -> Eq Nat yp Nat.zero) => \
             fun (h : Eq Nat (Nat.add x (Nat.succ yp)) Nat.zero) => \
             nat_zero_ne_succ_beq (Nat.add x yp) (Eq Nat (Nat.succ yp) Nat.zero) \
             (Eq.symm Nat (Nat.add x (Nat.succ yp)) Nat.zero h)) \
             y",
            "Nat.add = 0 inversion (right): x + y = 0 -> y = 0. DerivedProved, zero axiom_deps.",
            &[
                "Nat.rec",
                "Eq.refl",
                "Eq.symm",
                "nat_zero_ne_succ_beq",
                "Nat.add",
            ],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_add_eq_zero_left",
            "forall (x : Nat) (y : Nat), Eq Nat (Nat.add x y) Nat.zero -> Eq Nat x Nat.zero",
            "fun (x : Nat) (y : Nat) (h : Eq Nat (Nat.add x y) Nat.zero) => \
             Eq.substType Nat \
             (fun (z : Nat) => Eq Nat (Nat.add x z) Nat.zero) \
             y Nat.zero (nat_add_eq_zero_right x y h) h",
            "Nat.add = 0 inversion (left): x + y = 0 -> x = 0. DerivedProved, zero axiom_deps.",
            &["Eq.substType", "nat_add_eq_zero_right", "Nat.add"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_sub_eq_zero_antisymm",
            "forall (a : Nat) (b : Nat), \
             Eq Nat (Nat.sub a b) Nat.zero -> Eq Nat (Nat.sub b a) Nat.zero -> Eq Nat a b",
            "fun (a : Nat) => Nat.rec \
             (fun (za : Nat) => forall (b : Nat), \
             Eq Nat (Nat.sub za b) Nat.zero -> Eq Nat (Nat.sub b za) Nat.zero -> Eq Nat za b) \
             (fun (b : Nat) => Nat.rec \
             (fun (zb : Nat) => Eq Nat (Nat.sub Nat.zero zb) Nat.zero -> Eq Nat (Nat.sub zb Nat.zero) Nat.zero -> Eq Nat Nat.zero zb) \
             (fun (_ : Eq Nat (Nat.sub Nat.zero Nat.zero) Nat.zero) (_ : Eq Nat (Nat.sub Nat.zero Nat.zero) Nat.zero) => Eq.refl Nat Nat.zero) \
             (fun (bp : Nat) (_ihb : Eq Nat (Nat.sub Nat.zero bp) Nat.zero -> Eq Nat (Nat.sub bp Nat.zero) Nat.zero -> Eq Nat Nat.zero bp) => \
             fun (_h1 : Eq Nat (Nat.sub Nat.zero (Nat.succ bp)) Nat.zero) \
             (h2 : Eq Nat (Nat.sub (Nat.succ bp) Nat.zero) Nat.zero) => \
             nat_zero_ne_succ_beq bp (Eq Nat Nat.zero (Nat.succ bp)) (Eq.symm Nat (Nat.sub (Nat.succ bp) Nat.zero) Nat.zero h2)) \
             b) \
             (fun (ap : Nat) (ih : forall (b : Nat), Eq Nat (Nat.sub ap b) Nat.zero -> Eq Nat (Nat.sub b ap) Nat.zero -> Eq Nat ap b) => \
             fun (b : Nat) => Nat.rec \
             (fun (zb : Nat) => Eq Nat (Nat.sub (Nat.succ ap) zb) Nat.zero -> Eq Nat (Nat.sub zb (Nat.succ ap)) Nat.zero -> Eq Nat (Nat.succ ap) zb) \
             (fun (h1 : Eq Nat (Nat.sub (Nat.succ ap) Nat.zero) Nat.zero) (_h2 : Eq Nat (Nat.sub Nat.zero (Nat.succ ap)) Nat.zero) => \
             nat_zero_ne_succ_beq ap (Eq Nat (Nat.succ ap) Nat.zero) (Eq.symm Nat (Nat.sub (Nat.succ ap) Nat.zero) Nat.zero h1)) \
             (fun (bp : Nat) (_ihb : Eq Nat (Nat.sub (Nat.succ ap) bp) Nat.zero -> Eq Nat (Nat.sub bp (Nat.succ ap)) Nat.zero -> Eq Nat (Nat.succ ap) bp) => \
             fun (h1 : Eq Nat (Nat.sub (Nat.succ ap) (Nat.succ bp)) Nat.zero) \
             (h2 : Eq Nat (Nat.sub (Nat.succ bp) (Nat.succ ap)) Nat.zero) => \
             Eq.cong Nat Nat Nat.succ ap bp \
             (ih bp \
             (Eq.trans Nat (Nat.sub ap bp) (Nat.sub (Nat.succ ap) (Nat.succ bp)) Nat.zero \
             (Eq.symm Nat (Nat.sub (Nat.succ ap) (Nat.succ bp)) (Nat.sub ap bp) (nat_sub_succ_succ ap bp)) h1) \
             (Eq.trans Nat (Nat.sub bp ap) (Nat.sub (Nat.succ bp) (Nat.succ ap)) Nat.zero \
             (Eq.symm Nat (Nat.sub (Nat.succ bp) (Nat.succ ap)) (Nat.sub bp ap) (nat_sub_succ_succ bp ap)) h2))) \
             b) \
             a",
            "<=-antisymmetry of truncated subtraction: a-b=0 -> b-a=0 -> a=b. DerivedProved, zero axiom_deps.",
            &[
                "Nat.rec",
                "Eq.refl",
                "Eq.symm",
                "Eq.trans",
                "Eq.cong",
                "nat_zero_ne_succ_beq",
                "nat_sub_succ_succ",
                "Nat.sub",
            ],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "nat_eqb_eq",
            "forall (a : Nat) (b : Nat), Eq Bool (nat_eqb a b) Bool.true -> Eq Nat a b",
            "fun (a : Nat) (b : Nat) (h : Eq Bool (nat_eqb a b) Bool.true) => \
             nat_sub_eq_zero_antisymm a b \
             (nat_add_eq_zero_left (Nat.sub a b) (Nat.sub b a) \
             (nat_is_zero_eq (Nat.add (Nat.sub a b) (Nat.sub b a)) h)) \
             (nat_add_eq_zero_right (Nat.sub a b) (Nat.sub b a) \
             (nat_is_zero_eq (Nat.add (Nat.sub a b) (Nat.sub b a)) h))",
            "nat_eqb inversion: nat_eqb a b = true -> a = b. DerivedProved, zero axiom_deps.",
            &[
                "nat_eqb",
                "nat_is_zero_eq",
                "nat_add_eq_zero_left",
                "nat_add_eq_zero_right",
                "nat_sub_eq_zero_antisymm",
            ],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "name_eqb_str_str",
            "forall (p : Name) (q : Name) (m : Nat) (n : Nat), \
             Eq Bool (name_eqb (Name.str p m) (Name.str q n)) \
             (Bool.and (name_eqb p q) (nat_eqb m n))",
            "fun (p : Name) (q : Name) (m : Nat) (n : Nat) => \
             Eq.refl Bool (name_eqb (Name.str p m) (Name.str q n))",
            "name_eqb str/str computation (definitional, presents Bool.and form). DerivedProved, zero axiom_deps.",
            &["Eq.refl", "name_eqb"],
        ))?;

        self.add_definition(Self::fre_eq_lemma(
            "name_eqb_eq",
            "forall (a : Name) (b : Name), Eq Bool (name_eqb a b) Bool.true -> Eq Name a b",
            "fun (a : Name) => Name.rec \
             (fun (za : Name) => forall (b : Name), Eq Bool (name_eqb za b) Bool.true -> Eq Name za b) \
             (fun (b : Name) => Name.rec \
             (fun (zb : Name) => Eq Bool (name_eqb Name.anonymous zb) Bool.true -> Eq Name Name.anonymous zb) \
             (fun (_ : Eq Bool (name_eqb Name.anonymous Name.anonymous) Bool.true) => Eq.refl Name Name.anonymous) \
             (fun (q : Name) (n : Nat) (_ihb : Eq Bool (name_eqb Name.anonymous q) Bool.true -> Eq Name Name.anonymous q) => \
             fun (h : Eq Bool (name_eqb Name.anonymous (Name.str q n)) Bool.true) => \
             bool_false_ne_true (Eq Name Name.anonymous (Name.str q n)) h) \
             b) \
             (fun (p : Name) (m : Nat) (ih : forall (b : Name), Eq Bool (name_eqb p b) Bool.true -> Eq Name p b) => \
             fun (b : Name) => Name.rec \
             (fun (zb : Name) => Eq Bool (name_eqb (Name.str p m) zb) Bool.true -> Eq Name (Name.str p m) zb) \
             (fun (h : Eq Bool (name_eqb (Name.str p m) Name.anonymous) Bool.true) => \
             bool_false_ne_true (Eq Name (Name.str p m) Name.anonymous) h) \
             (fun (q : Name) (n : Nat) (_ihb : Eq Bool (name_eqb (Name.str p m) q) Bool.true -> Eq Name (Name.str p m) q) => \
             fun (h : Eq Bool (name_eqb (Name.str p m) (Name.str q n)) Bool.true) => \
             (fun (hx : Eq Bool (name_eqb p q) Bool.true) (hy : Eq Bool (nat_eqb m n) Bool.true) => \
             (fun (hpq : Eq Name p q) (hmn : Eq Nat m n) => \
             Eq.trans Name (Name.str p m) (Name.str q m) (Name.str q n) \
             (Eq.cong Name Name (fun (w : Name) => Name.str w m) p q hpq) \
             (Eq.cong Nat Name (fun (j : Nat) => Name.str q j) m n hmn)) \
             (ih q hx) (nat_eqb_eq m n hy)) \
             (band_eq_true_left (name_eqb p q) (nat_eqb m n) \
             (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (name_eqb (Name.str p m) (Name.str q n)) (Bool.and (name_eqb p q) (nat_eqb m n)) \
             (name_eqb_str_str p q m n) h)) \
             (band_eq_true_right (name_eqb p q) (nat_eqb m n) \
             (Eq.substType Bool (fun (x : Bool) => Eq Bool x Bool.true) \
             (name_eqb (Name.str p m) (Name.str q n)) (Bool.and (name_eqb p q) (nat_eqb m n)) \
             (name_eqb_str_str p q m n) h))) \
             b) \
             a",
            "name_eqb inversion: name_eqb a b = true -> a = b. Double Name.rec; the str/str case splits \
             the conjunction and inverts the Nat tag (nat_eqb_eq). DerivedProved, zero axiom_deps.",
            &[
                "Name.rec",
                "Eq.refl",
                "Eq.trans",
                "Eq.cong",
                "Eq.substType",
                "bool_false_ne_true",
                "band_eq_true_left",
                "band_eq_true_right",
                "nat_eqb_eq",
                "name_eqb_str_str",
                "name_eqb",
            ],
        ))?;

        Ok(())
    }

    /// `opt_pick_some_inv`: CPS inversion of the lookup branch helper `opt_pick`.
    /// `opt_pick b x cont = some y` either fired (`b = true`, `x = y`) or fell
    /// through (`b = false`, `cont = some y`). By `Bool.rec` on `b`.
    fn add_opt_pick_some_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "opt_pick_some_inv".to_string(),
            type_src: concat!(
                "forall (alpha : Type) (b : Bool) (x : alpha) (cont : OptionType alpha) (y : alpha) (C : Prop), ",
                "Eq (OptionType alpha) (opt_pick alpha b x cont) (OptionType.some alpha y) -> ",
                "(Eq Bool b Bool.true -> Eq alpha x y -> C) -> ",
                "(Eq Bool b Bool.false -> Eq (OptionType alpha) cont (OptionType.some alpha y) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (alpha : Type) (b : Bool) (x : alpha) (cont : OptionType alpha) (y : alpha) (C : Prop) ",
                    "(h : Eq (OptionType alpha) (opt_pick alpha b x cont) (OptionType.some alpha y)) ",
                    "(kt : Eq Bool b Bool.true -> Eq alpha x y -> C) ",
                    "(kf : Eq Bool b Bool.false -> Eq (OptionType alpha) cont (OptionType.some alpha y) -> C) => ",
                    "Bool.rec ",
                    "(fun (z : Bool) => ",
                    "Eq (OptionType alpha) (opt_pick alpha z x cont) (OptionType.some alpha y) -> ",
                    "(Eq Bool z Bool.true -> Eq alpha x y -> C) -> ",
                    "(Eq Bool z Bool.false -> Eq (OptionType alpha) cont (OptionType.some alpha y) -> C) -> C) ",
                    "(fun (h0 : Eq (OptionType alpha) (opt_pick alpha Bool.false x cont) (OptionType.some alpha y)) ",
                    "(_kt0 : Eq Bool Bool.false Bool.true -> Eq alpha x y -> C) ",
                    "(kf0 : Eq Bool Bool.false Bool.false -> Eq (OptionType alpha) cont (OptionType.some alpha y) -> C) => ",
                    "kf0 (Eq.refl Bool Bool.false) h0) ",
                    "(fun (h0 : Eq (OptionType alpha) (opt_pick alpha Bool.true x cont) (OptionType.some alpha y)) ",
                    "(kt0 : Eq Bool Bool.true Bool.true -> Eq alpha x y -> C) ",
                    "(_kf0 : Eq Bool Bool.true Bool.false -> Eq (OptionType alpha) cont (OptionType.some alpha y) -> C) => ",
                    "kt0 (Eq.refl Bool Bool.true) (option_some_inj alpha x y h0)) ",
                    "b h kt kf"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "CPS inversion of opt_pick: opt_pick b x cont = some y splits into the fire case ",
                "(b = true, x = y via option_some_inj) and the fall-through case (b = false, cont = some y), ",
                "by Bool.rec on b. DerivedProved, zero axiom_deps. Part of the real-env discharge (R1)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_pick".to_string(),
                "Bool.rec".to_string(),
                "Eq.refl".to_string(),
                "option_some_inj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick R0: the faithful env model + the two non-vacuity (iota/delta fire)
    /// witnesses.
    fn add_faithful_red_env_model(&mut self) -> Result<(), SpecError> {
        // faithful_rec_env: one recursor REC, non-degenerate RecMeta (0 params,
        // 1 motive, 1 minor, 0 indices, major-after-minors), one rule for CTOR
        // (0 fields) with a CLOSED-LAMBDA rhs.
        self.add_recursive_def(
            &format!(
                "def faithful_rec_env : RecEnv := RecEnv.addRec RecEnv.empty ({REC}) \
                 (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true) \
                 ({RULES})"
            ),
            "Faithful recursor environment (real-env discharge R0): one recursor REC modelling a \
             single-constructor inductive's recursor — NON-degenerate metadata (1 motive, 1 minor, \
             major-after-minors) so the major sits at spine position 2, and a rule for constructor \
             CTOR with a closed-lambda reduct template. Value-ful Definition (ratchet-clean).",
        )?;

        self.add_recursive_def(
            &format!(
                "def faithful_def_env : DefEnv := DefEnv.addDef DefEnv.empty ({DEFN}) \
                 (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero))"
            ),
            "Faithful definition environment (real-env discharge R0): one definition DEF unfolding to a \
             closed-lambda value. Value-ful Definition (ratchet-clean).",
        )?;

        self.add_recursive_def(
            "def faithful_red_env : RedEnv := RedEnv.mk faithful_rec_env faithful_def_env",
            "Faithful combined reduction environment (real-env discharge R0): RedEnv.mk of the faithful \
             recursor + definition envs, modelling a real kernel-environment shape (NOT the toy \
             the_red_env). Non-vacuous (iota + delta fire — see the two witnesses). The env over which \
             i2/i7/i8 are honestly discharged.",
        )?;

        // Non-vacuity (iota fires): REC applied to [motive, minor, (CTOR)] with the
        // major (CTOR, no fields) at position params+motives+minors = 2 reduces by
        // iota to (rhs motive minor). Pure computation; ZERO axiom_deps.
        self.add_definition(SpecDefinition {
            name: "faithful_red_env_iota_nonvacuous".to_string(),
            type_src: format!(
                "iota_step (red_rec faithful_red_env) \
                 (KExpr.app (KExpr.app (KExpr.app (KExpr.const ({REC}) (ListType.nil Level)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.const ({CTOR}) (ListType.nil Level))) \
                 (KExpr.app (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero))"
            ),
            value_src: Some(
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)))".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness (R0): faithful_red_env admits a real iota step — the recursor REC \
                          applied to [motive, minor, (CTOR)] reduces by iota_reduct (major at spine position 2, \
                          via the non-degenerate metadata) to (rhs applied to motive then minor). Proof by refl \
                          on the computational iota_reduct; zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "faithful_red_env".to_string(),
                "iota_step".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Non-vacuity (delta fires): the const DEF unfolds by delta to its def value.
        self.add_definition(SpecDefinition {
            name: "faithful_red_env_delta_nonvacuous".to_string(),
            type_src: format!(
                "delta_step (red_def faithful_red_env) \
                 (KExpr.const ({DEFN}) (ListType.nil Level)) \
                 (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero))"
            ),
            value_src: Some(
                "Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)))".to_string(),
            ),
            is_axiom: false,
            description: "Non-vacuity witness (R0): faithful_red_env admits a real delta step — the definition \
                          DEF unfolds to its closed-lambda value. Proof by refl on the computational delta_reduct; \
                          zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "faithful_red_env".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The shared recrule_for inverter for the R0 model: a successful
    /// `recrule_for (red_rec faithful_red_env) recname cname` lookup forces
    /// `cname = CTOR` (the single constructor). Consumed by i2 and i8.
    fn add_faithful_red_env_recrule_inv(&mut self) -> Result<(), SpecError> {
        // recrule_for env r c is definitionally
        //   opt_bind RecRules RecRule (recrules_for env r) (fun rules => recrule_in_rules rules c),
        // so opt_bind_some_inv recovers the rule list; opt_pick_some_inv then peels
        // the recursor-name match (recrules_for) and the constructor-name match
        // (recrule_in_rules over the singleton list), and name_eqb_eq concludes.
        let value = format!(
            "fun (recname : Name) (cname : Name) (rule : RecRule) \
             (h : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for (red_rec faithful_red_env) recname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule (Eq Name ({CTOR}) cname) h \
             (fun (w : RecRules) \
             (hw : Eq (OptionType RecRules) (recrules_for (red_rec faithful_red_env) recname) (OptionType.some RecRules w)) \
             (hfw : Eq (OptionType RecRule) (recrule_in_rules w cname) (OptionType.some RecRule rule)) => \
             opt_pick_some_inv RecRules (name_eqb ({REC}) recname) ({RULES}) (OptionType.none RecRules) w (Eq Name ({CTOR}) cname) hw \
             (fun (_ht : Eq Bool (name_eqb ({REC}) recname) Bool.true) (hval : Eq RecRules ({RULES}) w) => \
             opt_pick_some_inv RecRule (name_eqb ({CTOR}) cname) ({RULE}) (OptionType.none RecRule) rule (Eq Name ({CTOR}) cname) \
             (Eq.substType RecRules (fun (ww : RecRules) => Eq (OptionType RecRule) (recrule_in_rules ww cname) (OptionType.some RecRule rule)) \
             w ({RULES}) (Eq.symm RecRules ({RULES}) w hval) hfw) \
             (fun (htc : Eq Bool (name_eqb ({CTOR}) cname) Bool.true) (_hr : Eq RecRule ({RULE}) rule) => name_eqb_eq ({CTOR}) cname htc) \
             (fun (_hfc : Eq Bool (name_eqb ({CTOR}) cname) Bool.false) (hn : Eq (OptionType RecRule) (OptionType.none RecRule) (OptionType.some RecRule rule)) => \
             option_none_ne_some RecRule rule (Eq Name ({CTOR}) cname) hn)) \
             (fun (_hf : Eq Bool (name_eqb ({REC}) recname) Bool.false) (hn : Eq (OptionType RecRules) (OptionType.none RecRules) (OptionType.some RecRules w)) => \
             option_none_ne_some RecRules w (Eq Name ({CTOR}) cname) hn))"
        );
        self.add_definition(SpecDefinition {
            name: "fre_cname_eq_ctor".to_string(),
            type_src: format!(
                "forall (recname : Name) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule) -> \
                 Eq Name ({CTOR}) cname"
            ),
            value_src: Some(value),
            is_axiom: false,
            description: "Real-env discharge (R1): a successful recrule_for lookup over faithful_red_env forces \
                          the constructor name to be CTOR (the single rule). Inverts opt_bind/opt_pick by-name \
                          lookups and concludes by name_eqb_eq. The shared inverter i2/i8 consume. DerivedProved, \
                          zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "recrule_for".to_string(),
                "recrules_for".to_string(),
                "recrule_in_rules".to_string(),
                "opt_bind_some_inv".to_string(),
                "opt_pick_some_inv".to_string(),
                "name_eqb".to_string(),
                "name_eqb_eq".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "red_rec".to_string(),
                "faithful_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick R1: the three name-disjointness interface witnesses over R0
    /// (i2 RecEnvCtorNoRecMeta, i7 RecEnvDefEnvDisjoint, i8 RecEnvCtorNoDefVal).
    fn add_faithful_red_env_obligations(&mut self) -> Result<(), SpecError> {
        // i2: a constructor name is not a recursor name. Recover cname = CTOR
        // (fre_cname_eq_ctor), transport recmeta_for ... CTOR (= none by
        // computation, since name_eqb REC CTOR = false) onto cname.
        self.add_definition(SpecDefinition {
            name: "faithful_rec_env_ctor_no_recmeta".to_string(),
            type_src: "RecEnvCtorNoRecMeta (red_rec faithful_red_env)".to_string(),
            value_src: Some(format!(
                "RecEnvCtorNoRecMeta.mk (red_rec faithful_red_env) \
                 (fun (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr) \
                 (_hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (hrule : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule)) => \
                 Eq.substType Name \
                 (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) n) (OptionType.none RecMeta)) \
                 ({CTOR}) cname (fre_cname_eq_ctor recname cname rule hrule) \
                 (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)))"
            )),
            is_axiom: false,
            description: "Real-env discharge i2 (RecEnvCtorNoRecMeta over faithful_red_env): a constructor name \
                          of a recursor rule carries no recursor metadata. A constructor and a recursor occupy \
                          disjoint name slots BY CONSTRUCTION (REC /= CTOR), so recmeta_for ... CTOR computes to \
                          none; recover cname = CTOR (fre_cname_eq_ctor) and transport. DerivedProved, zero \
                          axiom_deps — honestly discharged, NOT carried."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvCtorNoRecMeta.mk".to_string(),
                "fre_cname_eq_ctor".to_string(),
                "recmeta_for".to_string(),
                "recrule_for".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "red_rec".to_string(),
                "faithful_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // i7: a definition name is not a recursor name. Invert the def-value
        // lookup (opt_pick_some_inv) to get name_eqb DEF dname = true, recover
        // dname = DEF (name_eqb_eq), transport recmeta_for ... DEF (= none).
        self.add_definition(SpecDefinition {
            name: "faithful_red_env_defenv_disjoint".to_string(),
            type_src: "RecEnvDefEnvDisjoint faithful_red_env".to_string(),
            value_src: Some(format!(
                "RecEnvDefEnvDisjoint.mk faithful_red_env \
                 (fun (dname : Name) (val : KExpr) \
                 (h : Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) dname) (OptionType.some KExpr val)) => \
                 opt_pick_some_inv KExpr (name_eqb ({DEFN}) dname) \
                 (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (OptionType.none KExpr) val \
                 (Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) dname) (OptionType.none RecMeta)) h \
                 (fun (htrue : Eq Bool (name_eqb ({DEFN}) dname) Bool.true) (_hv : Eq KExpr (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) val) => \
                 Eq.substType Name \
                 (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) n) (OptionType.none RecMeta)) \
                 ({DEFN}) dname (name_eqb_eq ({DEFN}) dname htrue) \
                 (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))) \
                 (fun (_hfalse : Eq Bool (name_eqb ({DEFN}) dname) Bool.false) (hn : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr val)) => \
                 option_none_ne_some KExpr val (Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) dname) (OptionType.none RecMeta)) hn))"
            )),
            is_axiom: false,
            description: "Real-env discharge i7 (RecEnvDefEnvDisjoint over faithful_red_env): a definition name \
                          carries no recursor metadata. A definition and a recursor occupy disjoint name slots BY \
                          CONSTRUCTION (DEF /= REC), so recmeta_for ... DEF computes to none; invert the def-value \
                          lookup, recover dname = DEF (name_eqb_eq), transport. DerivedProved, zero axiom_deps — \
                          honestly discharged, NOT carried."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvDefEnvDisjoint".to_string(),
                "RecEnvDefEnvDisjoint.mk".to_string(),
                "opt_pick_some_inv".to_string(),
                "name_eqb".to_string(),
                "name_eqb_eq".to_string(),
                "option_none_ne_some".to_string(),
                "defval_for".to_string(),
                "recmeta_for".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "faithful_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // i8: a constructor name is not a definition name. Recover cname = CTOR
        // (fre_cname_eq_ctor), transport defval_for ... CTOR (= none, since
        // name_eqb DEF CTOR = false) onto cname.
        self.add_definition(SpecDefinition {
            name: "faithful_red_env_ctor_no_defval".to_string(),
            type_src: "RecEnvCtorNoDefVal faithful_red_env".to_string(),
            value_src: Some(format!(
                "RecEnvCtorNoDefVal.mk faithful_red_env \
                 (fun (recname : Name) (cname : Name) (rule : RecRule) (major : KExpr) \
                 (_hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (hrule : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule)) => \
                 Eq.substType Name \
                 (fun (n : Name) => Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) n) (OptionType.none KExpr)) \
                 ({CTOR}) cname (fre_cname_eq_ctor recname cname rule hrule) \
                 (Eq.refl (OptionType KExpr) (OptionType.none KExpr)))"
            )),
            is_axiom: false,
            description: "Real-env discharge i8 (RecEnvCtorNoDefVal over faithful_red_env): a constructor name of \
                          a recursor rule carries no def value. A constructor and a definition occupy disjoint \
                          name slots BY CONSTRUCTION (CTOR /= DEF), so defval_for ... CTOR computes to none; \
                          recover cname = CTOR (fre_cname_eq_ctor) and transport. DerivedProved, zero axiom_deps \
                          — honestly discharged, NOT carried."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "RecEnvCtorNoDefVal".to_string(),
                "RecEnvCtorNoDefVal.mk".to_string(),
                "fre_cname_eq_ctor".to_string(),
                "defval_for".to_string(),
                "recrule_for".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "faithful_red_env".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Bricks R2 + R3 + R4 of the real-env discharge: the remaining FIVE faithful
    /// interfaces over `faithful_red_env` (i1 RecEnvReductNotRedex, i3 RecEnvClosed,
    /// i4 RecEnvLiftClosed, i5 DefEnvClosed, i6 DefEnvLiftClosed) plus the full
    /// `RedEnvFaithful faithful_red_env` bundle assembled from all eight witnesses.
    ///
    /// Registered as a LATER stage than `add_faithful_red_env` because the bundle
    /// type `RedEnvFaithful` / its constructor `RedEnvFaithful.mk` are registered by
    /// `add_par_reduces_cd_sound` (stage 66), AFTER the R0/R1 stage (64). Every
    /// interface witness only depends on machinery available by stage 64, but the
    /// assembly needs `RedEnvFaithful.mk`. ALL DerivedProved, ZERO axiom_deps.
    ///
    /// ## R2 — the four closure obligations (i3/i4/i5/i6)
    ///
    /// The rule rhs (`recrule_rhs RULE`) and the def value are both the CLOSED
    /// lambda template `LAM = λ(sort 0). sort 0`. Closed by construction, so
    /// `instantiate_at LAM _ _` and `lift_at LAM _ _` both COMPUTE back to `LAM`
    /// (the sort arms are identities, the binder arm recurses into closed sorts).
    /// i3/i4 recover `rule = RULE` from a successful `recrule_for` lookup
    /// (`fre_rule_eq_rule`, the sibling of `fre_cname_eq_ctor`) then transport an
    /// `Eq.refl`; i5/i6 invert the single `defval_for` slot (`opt_pick_some_inv`,
    /// the i7 pattern) to pin `defval = LAM` then transport an `Eq.refl`.
    ///
    /// ## R3 — the reduct-not-redex obligation (i1)
    ///
    /// `iota_reduct_some_inv` decomposes a fired redex `iota_reduct env e = some r`
    /// into its five witnesses + the reduct equation `some REDUCT = some r`, where
    /// `REDUCT = apply_spine extras (apply_spine fields (apply_spine prefix
    /// (recrule_rhs rule)))`. The head of `REDUCT` is `kapp_fn (recrule_rhs rule)`
    /// (apply_spine only adds app nodes ON TOP, which `kapp_fn` strips —
    /// `kapp_fn_apply_spine`), and `rule = RULE` forces `recrule_rhs rule = LAM`,
    /// whose head is the binder `LAM` itself with `kexpr_const_name = none`. So
    /// `iota_reduct env REDUCT` short-circuits at its first `opt_bind`
    /// (`iota_reduct_head_none`), and transporting along `REDUCT = r`
    /// (`option_some_inj`) yields `iota_reduct env r = none`.
    pub(super) fn add_faithful_red_env_bundle(&mut self) -> Result<(), SpecError> {
        self.add_faithful_red_env_rule_inv()?;
        self.add_faithful_red_env_closure_obligations()?;
        self.add_faithful_red_env_reduct_not_redex()?;
        self.add_faithful_red_env_assemble()?;
        Ok(())
    }

    /// R2 helper: `fre_rule_eq_rule` — a successful `recrule_for` lookup over
    /// `faithful_red_env` forces the rule to be the single `RULE`. The sibling of
    /// `fre_cname_eq_ctor` (same opt_bind/opt_pick inversion tower), but the
    /// constructor-name match returns the RULE-value equation directly instead of
    /// passing it through `name_eqb_eq`.
    fn add_faithful_red_env_rule_inv(&mut self) -> Result<(), SpecError> {
        let value = format!(
            "fun (recname : Name) (cname : Name) (rule : RecRule) \
             (h : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule)) => \
             opt_bind_some_inv RecRules RecRule (recrules_for (red_rec faithful_red_env) recname) \
             (fun (rules : RecRules) => recrule_in_rules rules cname) rule (Eq RecRule ({RULE}) rule) h \
             (fun (w : RecRules) \
             (hw : Eq (OptionType RecRules) (recrules_for (red_rec faithful_red_env) recname) (OptionType.some RecRules w)) \
             (hfw : Eq (OptionType RecRule) (recrule_in_rules w cname) (OptionType.some RecRule rule)) => \
             opt_pick_some_inv RecRules (name_eqb ({REC}) recname) ({RULES}) (OptionType.none RecRules) w (Eq RecRule ({RULE}) rule) hw \
             (fun (_ht : Eq Bool (name_eqb ({REC}) recname) Bool.true) (hval : Eq RecRules ({RULES}) w) => \
             opt_pick_some_inv RecRule (name_eqb ({CTOR}) cname) ({RULE}) (OptionType.none RecRule) rule (Eq RecRule ({RULE}) rule) \
             (Eq.substType RecRules (fun (ww : RecRules) => Eq (OptionType RecRule) (recrule_in_rules ww cname) (OptionType.some RecRule rule)) \
             w ({RULES}) (Eq.symm RecRules ({RULES}) w hval) hfw) \
             (fun (_htc : Eq Bool (name_eqb ({CTOR}) cname) Bool.true) (hr : Eq RecRule ({RULE}) rule) => hr) \
             (fun (_hfc : Eq Bool (name_eqb ({CTOR}) cname) Bool.false) (hn : Eq (OptionType RecRule) (OptionType.none RecRule) (OptionType.some RecRule rule)) => \
             option_none_ne_some RecRule rule (Eq RecRule ({RULE}) rule) hn)) \
             (fun (_hf : Eq Bool (name_eqb ({REC}) recname) Bool.false) (hn : Eq (OptionType RecRules) (OptionType.none RecRules) (OptionType.some RecRules w)) => \
             option_none_ne_some RecRules w (Eq RecRule ({RULE}) rule) hn))"
        );
        self.add_definition(Self::fre_eq_lemma(
            "fre_rule_eq_rule",
            &format!(
                "forall (recname : Name) (cname : Name) (rule : RecRule), \
                 Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule) -> \
                 Eq RecRule ({RULE}) rule"
            ),
            &value,
            "Real-env discharge (R2): a successful recrule_for lookup over faithful_red_env forces the \
             rule to be the single RULE. Sibling of fre_cname_eq_ctor; the constructor-name match returns \
             the RULE-value equation directly. The shared inverter i3/i4 (and i1) consume to pin \
             recrule_rhs rule = LAM. DerivedProved, zero axiom_deps.",
            &[
                "recrule_for",
                "recrules_for",
                "recrule_in_rules",
                "opt_bind_some_inv",
                "opt_pick_some_inv",
                "name_eqb",
                "option_none_ne_some",
                "Eq.substType",
                "Eq.symm",
                "red_rec",
                "faithful_red_env",
            ],
        ))?;
        Ok(())
    }

    /// R2: the four closure interfaces over `faithful_red_env`
    /// (i3 RecEnvClosed, i4 RecEnvLiftClosed, i5 DefEnvClosed, i6 DefEnvLiftClosed).
    fn add_faithful_red_env_closure_obligations(&mut self) -> Result<(), SpecError> {
        // i3 RecEnvClosed: every looked-up rule's rhs is instantiate_at-invariant.
        // Recover rule = RULE (fre_rule_eq_rule), recrule_rhs RULE = LAM is closed,
        // so instantiate_at (recrule_rhs RULE) val depth computes back to it (Eq.refl).
        self.add_definition(Self::fre_eq_lemma(
            "faithful_rec_env_closed",
            "RecEnvClosed (red_rec faithful_red_env)",
            &format!(
                "RecEnvClosed.mk (red_rec faithful_red_env) \
                 (fun (rname : Name) (cname : Name) (rule : RecRule) (val : KExpr) (depth : Nat) \
                 (hlk : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) rname cname) (OptionType.some RecRule rule)) => \
                 Eq.substType RecRule \
                 (fun (rr : RecRule) => Eq KExpr (instantiate_at (recrule_rhs rr) val depth) (recrule_rhs rr)) \
                 ({RULE}) rule (fre_rule_eq_rule rname cname rule hlk) \
                 (Eq.refl KExpr (recrule_rhs ({RULE}))))"
            ),
            "Real-env discharge i3 (RecEnvClosed over faithful_red_env): every looked-up rule's rhs is \
             instantiate_at-invariant. The single rule's rhs is the CLOSED lambda LAM, so substitution \
             leaves it fixed by computation; recover rule = RULE (fre_rule_eq_rule) and transport Eq.refl. \
             DerivedProved, zero axiom_deps — honestly discharged, NOT carried.",
            &[
                "RecEnvClosed",
                "RecEnvClosed.mk",
                "fre_rule_eq_rule",
                "recrule_for",
                "recrule_rhs",
                "instantiate_at",
                "Eq.substType",
                "Eq.refl",
                "red_rec",
                "faithful_red_env",
            ],
        ))?;

        // i4 RecEnvLiftClosed: the lift analogue — recrule_rhs RULE = LAM is fixed
        // by lift_at as well (closed term, no free bvars).
        self.add_definition(Self::fre_eq_lemma(
            "faithful_rec_env_lift_closed",
            "RecEnvLiftClosed (red_rec faithful_red_env)",
            &format!(
                "RecEnvLiftClosed.mk (red_rec faithful_red_env) \
                 (fun (rname : Name) (cname : Name) (rule : RecRule) (cutoff : Nat) (amount : Nat) \
                 (hlk : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) rname cname) (OptionType.some RecRule rule)) => \
                 Eq.substType RecRule \
                 (fun (rr : RecRule) => Eq KExpr (lift_at (recrule_rhs rr) cutoff amount) (recrule_rhs rr)) \
                 ({RULE}) rule (fre_rule_eq_rule rname cname rule hlk) \
                 (Eq.refl KExpr (recrule_rhs ({RULE}))))"
            ),
            "Real-env discharge i4 (RecEnvLiftClosed over faithful_red_env): every looked-up rule's rhs is \
             lift_at-invariant. The single rule's rhs is the CLOSED lambda LAM, so lifting leaves it fixed \
             by computation; recover rule = RULE (fre_rule_eq_rule) and transport Eq.refl. DerivedProved, \
             zero axiom_deps — honestly discharged, NOT carried.",
            &[
                "RecEnvLiftClosed",
                "RecEnvLiftClosed.mk",
                "fre_rule_eq_rule",
                "recrule_for",
                "recrule_rhs",
                "lift_at",
                "Eq.substType",
                "Eq.refl",
                "red_rec",
                "faithful_red_env",
            ],
        ))?;

        // i5 DefEnvClosed: every looked-up def value is instantiate_at-invariant.
        // Invert the single defval_for slot (opt_pick_some_inv, the i7 pattern) to
        // pin defval = LAM (closed), then transport Eq.refl.
        self.add_definition(Self::fre_eq_lemma(
            "faithful_def_env_closed",
            "DefEnvClosed (red_def faithful_red_env)",
            &format!(
                "DefEnvClosed.mk (red_def faithful_red_env) \
                 (fun (dname : Name) (defval : KExpr) (subval : KExpr) (depth : Nat) \
                 (h : Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) dname) (OptionType.some KExpr defval)) => \
                 opt_pick_some_inv KExpr (name_eqb ({DEFN}) dname) {LAM} (OptionType.none KExpr) defval \
                 (Eq KExpr (instantiate_at defval subval depth) defval) h \
                 (fun (_htrue : Eq Bool (name_eqb ({DEFN}) dname) Bool.true) (hv : Eq KExpr {LAM} defval) => \
                 Eq.substType KExpr (fun (dv : KExpr) => Eq KExpr (instantiate_at dv subval depth) dv) \
                 {LAM} defval hv (Eq.refl KExpr {LAM})) \
                 (fun (_hfalse : Eq Bool (name_eqb ({DEFN}) dname) Bool.false) (hn : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr defval)) => \
                 option_none_ne_some KExpr defval (Eq KExpr (instantiate_at defval subval depth) defval) hn))"
            ),
            "Real-env discharge i5 (DefEnvClosed over faithful_red_env): every looked-up def value is \
             instantiate_at-invariant. The single definition unfolds to the CLOSED lambda LAM, so \
             substitution leaves it fixed by computation; invert the def-value lookup (opt_pick_some_inv), \
             pin defval = LAM, transport Eq.refl. DerivedProved, zero axiom_deps — honestly discharged, \
             NOT carried.",
            &[
                "DefEnvClosed",
                "DefEnvClosed.mk",
                "opt_pick_some_inv",
                "name_eqb",
                "option_none_ne_some",
                "defval_for",
                "instantiate_at",
                "Eq.substType",
                "Eq.refl",
                "red_def",
                "faithful_red_env",
            ],
        ))?;

        // i6 DefEnvLiftClosed: the lift analogue of i5.
        self.add_definition(Self::fre_eq_lemma(
            "faithful_def_env_lift_closed",
            "DefEnvLiftClosed (red_def faithful_red_env)",
            &format!(
                "DefEnvLiftClosed.mk (red_def faithful_red_env) \
                 (fun (dname : Name) (defval : KExpr) (cutoff : Nat) (amount : Nat) \
                 (h : Eq (OptionType KExpr) (defval_for (red_def faithful_red_env) dname) (OptionType.some KExpr defval)) => \
                 opt_pick_some_inv KExpr (name_eqb ({DEFN}) dname) {LAM} (OptionType.none KExpr) defval \
                 (Eq KExpr (lift_at defval cutoff amount) defval) h \
                 (fun (_htrue : Eq Bool (name_eqb ({DEFN}) dname) Bool.true) (hv : Eq KExpr {LAM} defval) => \
                 Eq.substType KExpr (fun (dv : KExpr) => Eq KExpr (lift_at dv cutoff amount) dv) \
                 {LAM} defval hv (Eq.refl KExpr {LAM})) \
                 (fun (_hfalse : Eq Bool (name_eqb ({DEFN}) dname) Bool.false) (hn : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr defval)) => \
                 option_none_ne_some KExpr defval (Eq KExpr (lift_at defval cutoff amount) defval) hn))"
            ),
            "Real-env discharge i6 (DefEnvLiftClosed over faithful_red_env): every looked-up def value is \
             lift_at-invariant. The single definition unfolds to the CLOSED lambda LAM, so lifting leaves \
             it fixed by computation; invert the def-value lookup (opt_pick_some_inv), pin defval = LAM, \
             transport Eq.refl. DerivedProved, zero axiom_deps — honestly discharged, NOT carried.",
            &[
                "DefEnvLiftClosed",
                "DefEnvLiftClosed.mk",
                "opt_pick_some_inv",
                "name_eqb",
                "option_none_ne_some",
                "defval_for",
                "lift_at",
                "Eq.substType",
                "Eq.refl",
                "red_def",
                "faithful_red_env",
            ],
        ))?;

        Ok(())
    }

    /// R3: i1 RecEnvReductNotRedex over `faithful_red_env`, plus its two reusable
    /// helper lemmas `kapp_fn_apply_spine` and `iota_reduct_head_none`.
    fn add_faithful_red_env_reduct_not_redex(&mut self) -> Result<(), SpecError> {
        // kapp_fn_apply_spine: apply_spine only adds app nodes ON TOP of the head,
        // which kapp_fn strips, so the spine head is invariant under apply_spine.
        // Induction on the arg list (ListType.rec): nil = refl; cons threads the IH
        // through (app h x) then collapses via kapp_fn_app.
        self.add_definition(Self::fre_eq_lemma(
            "kapp_fn_apply_spine",
            "forall (args : ListType KExpr) (h : KExpr), Eq KExpr (kapp_fn (apply_spine args h)) (kapp_fn h)",
            "fun (args : ListType KExpr) => \
             ListType.rec KExpr \
             (fun (l : ListType KExpr) => forall (h : KExpr), Eq KExpr (kapp_fn (apply_spine l h)) (kapp_fn h)) \
             (fun (h : KExpr) => Eq.refl KExpr (kapp_fn h)) \
             (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (h : KExpr), Eq KExpr (kapp_fn (apply_spine rest h)) (kapp_fn h)) => \
             fun (h : KExpr) => Eq.trans KExpr \
             (kapp_fn (apply_spine rest (KExpr.app h x))) (kapp_fn (KExpr.app h x)) (kapp_fn h) \
             (ih (KExpr.app h x)) (kapp_fn_app h x)) \
             args",
            "The head of an application spine is invariant under apply_spine: kapp_fn (apply_spine args h) \
             = kapp_fn h. apply_spine only adds app nodes on top of h, which kapp_fn strips. By induction \
             on the arg list (kapp_fn_app collapses the cons step). DerivedProved, zero axiom_deps.",
            &[
                "ListType.rec",
                "apply_spine",
                "kapp_fn",
                "kapp_fn_app",
                "Eq.refl",
                "Eq.trans",
            ],
        ))?;

        // iota_reduct_head_none: if the spine head of x carries no const name, the
        // FIRST opt_bind of iota_reduct short-circuits to none. Eq.cong on the
        // outer opt_bind's option argument; the none-substituted opt_bind computes
        // to none. CONT is iota_reduct's continuation verbatim (e := x).
        let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
        let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
        let reduct_x = format!(
            "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args x)) \
             (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) \
             (apply_spine (list_take {prefix_n} (kapp_args x)) (recrule_rhs rule))))"
        );
        let cont_x = format!(
            "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) \
             (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args x))) \
             (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) \
             (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) \
             (fun (rule : RecRule) => OptionType.some KExpr {reduct_x})))))"
        );
        self.add_definition(Self::fre_eq_lemma(
            "iota_reduct_head_none",
            "forall (env : RecEnv) (x : KExpr), \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.none Name) -> \
             Eq (OptionType KExpr) (iota_reduct env x) (OptionType.none KExpr)",
            &format!(
                "fun (env : RecEnv) (x : KExpr) \
                 (hn : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.none Name)) => \
                 Eq.cong (OptionType Name) (OptionType KExpr) \
                 (fun (o : OptionType Name) => opt_bind Name KExpr o {cont_x}) \
                 (kexpr_const_name (kapp_fn x)) (OptionType.none Name) hn"
            ),
            "If the spine head of x carries no const name (kexpr_const_name (kapp_fn x) = none), then \
             iota_reduct env x = none: its outermost opt_bind short-circuits on the none head lookup. \
             Eq.cong on the head-lookup argument of iota_reduct's first opt_bind; the none-substituted \
             opt_bind computes to none. DerivedProved, zero axiom_deps.",
            &[
                "iota_reduct",
                "opt_bind",
                "kexpr_const_name",
                "kapp_fn",
                "Eq.cong",
            ],
        ))?;

        // i1 RecEnvReductNotRedex: an iota reduct of faithful_red_env is never itself
        // a top iota redex. Invert the fired redex (iota_reduct_some_inv) to expose
        // REDUCT = apply_spine .. (recrule_rhs rule); rule = RULE (fre_rule_eq_rule)
        // gives recrule_rhs rule = LAM (binder-headed, kexpr_const_name = none); the
        // apply_spine layers don't change the head (kapp_fn_apply_spine x3), so the
        // reduct's head carries no const name and iota_reduct REDUCT = none
        // (iota_reduct_head_none); transport REDUCT = r (option_some_inj).
        let extras_e = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
        let fields_e = "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
        let prefix_e = format!("(list_take {prefix_n} (kapp_args e))");
        let inner3 = format!("(apply_spine {prefix_e} (recrule_rhs rule))");
        let inner2 = format!("(apply_spine {fields_e} {inner3})");
        let reduct_e = format!("(apply_spine {extras_e} {inner2})");
        // kapp_fn REDUCT = kapp_fn (recrule_rhs rule) (strip the three apply_spine layers).
        let kfreduct_eq = format!(
            "(Eq.trans KExpr (kapp_fn {reduct_e}) (kapp_fn {inner2}) (kapp_fn (recrule_rhs rule)) \
             (kapp_fn_apply_spine {extras_e} {inner2}) \
             (Eq.trans KExpr (kapp_fn {inner2}) (kapp_fn {inner3}) (kapp_fn (recrule_rhs rule)) \
             (kapp_fn_apply_spine {fields_e} {inner3}) \
             (kapp_fn_apply_spine {prefix_e} (recrule_rhs rule))))"
        );
        // kexpr_const_name (kapp_fn (recrule_rhs rule)) = none, via rule = RULE.
        let head_for_rhs = format!(
            "(Eq.substType RecRule \
             (fun (rr : RecRule) => Eq (OptionType Name) (kexpr_const_name (kapp_fn (recrule_rhs rr))) (OptionType.none Name)) \
             ({RULE}) rule (fre_rule_eq_rule recname cname rule h5) \
             (Eq.refl (OptionType Name) (OptionType.none Name)))"
        );
        // kexpr_const_name (kapp_fn REDUCT) = none.
        let head_none = format!(
            "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {reduct_e})) \
             (kexpr_const_name (kapp_fn (recrule_rhs rule))) (OptionType.none Name) \
             (Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn {reduct_e}) (kapp_fn (recrule_rhs rule)) {kfreduct_eq}) \
             {head_for_rhs})"
        );
        let proof_for_reduct =
            format!("(iota_reduct_head_none (red_rec faithful_red_env) {reduct_e} {head_none})");
        let i1_value = format!(
            "RecEnvReductNotRedex.mk (red_rec faithful_red_env) \
             (fun (e : KExpr) (r : KExpr) (hyp : Eq (OptionType KExpr) (iota_reduct (red_rec faithful_red_env) e) (OptionType.some KExpr r)) => \
             iota_reduct_some_inv (red_rec faithful_red_env) e r \
             (Eq (OptionType KExpr) (iota_reduct (red_rec faithful_red_env) r) (OptionType.none KExpr)) hyp \
             (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec faithful_red_env) recname) (OptionType.some RecMeta meta)) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (h5 : Eq (OptionType RecRule) (recrule_for (red_rec faithful_red_env) recname cname) (OptionType.some RecRule rule)) \
             (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_e}) (OptionType.some KExpr r)) => \
             Eq.substType KExpr \
             (fun (x : KExpr) => Eq (OptionType KExpr) (iota_reduct (red_rec faithful_red_env) x) (OptionType.none KExpr)) \
             {reduct_e} r (option_some_inj KExpr {reduct_e} r h5r) \
             {proof_for_reduct}))"
        );
        self.add_definition(Self::fre_eq_lemma(
            "faithful_red_env_reduct_not_redex",
            "RecEnvReductNotRedex (red_rec faithful_red_env)",
            &i1_value,
            "Real-env discharge i1 (RecEnvReductNotRedex over faithful_red_env): an iota reduct is never \
             itself a top iota redex. Invert the fired redex (iota_reduct_some_inv) to expose REDUCT = \
             apply_spine .. (recrule_rhs rule); rule = RULE (fre_rule_eq_rule) forces recrule_rhs rule = \
             LAM (binder-headed, kexpr_const_name = none); the apply_spine layers leave the head fixed \
             (kapp_fn_apply_spine), so iota_reduct REDUCT short-circuits to none (iota_reduct_head_none); \
             transport REDUCT = r (option_some_inj). DerivedProved, zero axiom_deps — honestly discharged, \
             NOT carried.",
            &[
                "RecEnvReductNotRedex",
                "RecEnvReductNotRedex.mk",
                "iota_reduct_some_inv",
                "iota_reduct_head_none",
                "kapp_fn_apply_spine",
                "fre_rule_eq_rule",
                "option_some_inj",
                "iota_reduct",
                "kexpr_const_name",
                "kapp_fn",
                "recrule_rhs",
                "recrule_for",
                "Eq.substType",
                "Eq.trans",
                "Eq.cong",
                "Eq.refl",
                "red_rec",
                "faithful_red_env",
            ],
        ))?;

        Ok(())
    }

    /// R4: assemble the full bundle `RedEnvFaithful faithful_red_env` from all eight
    /// honestly-discharged interface witnesses (i1..i8), via `RedEnvFaithful.mk`.
    fn add_faithful_red_env_assemble(&mut self) -> Result<(), SpecError> {
        self.add_definition(Self::fre_eq_lemma(
            "faithful_red_env_faithful",
            "RedEnvFaithful faithful_red_env",
            "RedEnvFaithful.mk faithful_red_env \
             faithful_red_env_reduct_not_redex \
             faithful_rec_env_ctor_no_recmeta \
             faithful_rec_env_closed \
             faithful_rec_env_lift_closed \
             faithful_def_env_closed \
             faithful_def_env_lift_closed \
             faithful_red_env_defenv_disjoint \
             faithful_red_env_ctor_no_defval",
            "Real-env discharge R4: the FULL RedEnvFaithful bundle over faithful_red_env, assembled by \
             RedEnvFaithful.mk from all eight honestly-discharged interface witnesses (i1 \
             RecEnvReductNotRedex, i2 RecEnvCtorNoRecMeta, i3 RecEnvClosed, i4 RecEnvLiftClosed, i5 \
             DefEnvClosed, i6 DefEnvLiftClosed, i7 RecEnvDefEnvDisjoint, i8 RecEnvCtorNoDefVal) — every \
             one a real DerivedProved term, NONE asserted/carried. The church_rosser_whnf / def_eq_to_eq \
             retirement metatheory becomes UNCONDITIONAL on this concrete faithful env. DerivedProved, \
             zero axiom_deps; faithful_red_env is non-vacuous (iota + delta fire).",
            &[
                "RedEnvFaithful",
                "RedEnvFaithful.mk",
                "faithful_red_env",
                "faithful_red_env_reduct_not_redex",
                "faithful_rec_env_ctor_no_recmeta",
                "faithful_rec_env_closed",
                "faithful_rec_env_lift_closed",
                "faithful_def_env_closed",
                "faithful_def_env_lift_closed",
                "faithful_red_env_defenv_disjoint",
                "faithful_red_env_ctor_no_defval",
            ],
        ))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::build_spec_with_stack;

    /// R0 + R1 green gate: the faithful env model, its two non-vacuity witnesses,
    /// and the three obligation witnesses all register and kernel-type-check in
    /// the full core spec.
    #[test]
    fn test_faithful_red_env_discharge_type_checks_in_full_spec() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_rec_env",
            "faithful_def_env",
            "faithful_red_env",
            "faithful_red_env_iota_nonvacuous",
            "faithful_red_env_delta_nonvacuous",
            "fre_cname_eq_ctor",
            "name_eqb_eq",
            "opt_pick_some_inv",
            "faithful_rec_env_ctor_no_recmeta",
            "faithful_red_env_defenv_disjoint",
            "faithful_red_env_ctor_no_defval",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "full core spec should register {name}"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }

    /// The three obligations are real DerivedProved terms (NOT axioms, NOT carried
    /// hypotheses): is_axiom == false, DerivedProved, empty axiom_deps.
    #[test]
    fn test_faithful_red_env_obligations_are_derived_proved_zero_axioms() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_rec_env_ctor_no_recmeta",
            "faithful_red_env_defenv_disjoint",
            "faithful_red_env_ctor_no_defval",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should exist"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            assert!(
                def.value_src.is_some(),
                "{name} must carry a constructive proof term"
            );
        }
    }

    /// The R0 model is non-vacuous: iota AND delta genuinely fire on it.
    #[test]
    fn test_faithful_red_env_is_non_vacuous() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_red_env_iota_nonvacuous",
            "faithful_red_env_delta_nonvacuous",
        ] {
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} (non-vacuity witness) must type-check: {e:?}"));
        }
    }

    /// R2 + R3 green gate: the FIVE remaining interface witnesses (i1/i3/i4/i5/i6)
    /// and their two helper lemmas register and kernel-type-check in the full spec.
    #[test]
    fn test_faithful_red_env_bundle_interfaces_type_check_in_full_spec() {
        let spec = build_spec_with_stack();
        for name in [
            "fre_rule_eq_rule",
            "kapp_fn_apply_spine",
            "iota_reduct_head_none",
            "faithful_red_env_reduct_not_redex",
            "faithful_rec_env_closed",
            "faithful_rec_env_lift_closed",
            "faithful_def_env_closed",
            "faithful_def_env_lift_closed",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "full core spec should register {name}"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }

    /// R4 capstone: the full `RedEnvFaithful faithful_red_env` bundle assembles from
    /// REAL witnesses — it type-checks, is a DerivedProved term (NOT an axiom, NOT a
    /// carried hypothesis), and carries zero axiom_deps. So do all five interface
    /// witnesses it bundles (i1/i3/i4/i5/i6). No masquerade.
    #[test]
    fn test_faithful_red_env_faithful_bundle_is_derived_proved_zero_axioms() {
        let spec = build_spec_with_stack();
        for name in [
            "faithful_red_env_reduct_not_redex",
            "faithful_rec_env_closed",
            "faithful_rec_env_lift_closed",
            "faithful_def_env_closed",
            "faithful_def_env_lift_closed",
            "faithful_red_env_faithful",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .unwrap_or_else(|| panic!("{name} should exist"));
            assert!(!def.is_axiom, "{name} must not be an axiom (no masquerade)");
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} must carry zero axiom_deps: {:?}",
                def.axiom_deps
            );
            assert!(
                def.value_src.is_some(),
                "{name} must carry a constructive proof term"
            );
            spec.verify_definition(name)
                .unwrap_or_else(|e| panic!("{name} should elaborate and type-check: {e:?}"));
        }
    }
}

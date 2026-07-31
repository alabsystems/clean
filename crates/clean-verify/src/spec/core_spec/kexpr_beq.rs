// Copyright 2026 Andrew Yates.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
//! Decidable syntactic equality on the reflected `KExpr` model.
//!
//! Greenfield self-verification beachhead: a genuine structural boolean
//! equality `kexpr_beq : KExpr -> KExpr -> Bool` over the 9 constructors of the
//! reflected kernel-expression model (sort, bvar, app, lam, pi, const, let_,
//! proj, lit), plus
//! the reflexivity metatheorem `kexpr_beq_refl : forall e, kexpr_beq e e = true`
//! proved constructively by `KExpr.rec` induction.
//!
//! This is the substrate for the decidability-of-definitional-equality
//! milestone. It is **confluence-independent**: it references only the pure
//! syntactic model (`KExpr`, `Nat`, `Name`, `Level`, `ListType`) plus the
//! foundational `Eq` rules and boolean equality helpers (`nat_eqb`, `name_eqb`
//! from `rec_env`). It does NOT touch any `par_reduces`/`iota`/`whnf`/`DefEq`
//! declaration.
//!
//! Substrate reused (registered earlier in the bundle):
//! - `nat_eqb`, `nat_is_zero` (rec_env): boolean Nat equality.
//! - `name_eqb` (rec_env): boolean Name equality.
//! - `nat_sub_self` (foundation_types): `n - n = 0` (constructive).
//! - `Bool.and`, `Bool.true`, `Bool.false` (kernel init_bool surface).
//! - `Eq.refl`, `Eq.cong`, `Eq.trans` (foundation Eq rules).
//!
//! New substrate built here (all DerivedProved, foundational closure):
//! - `level_eqb` / `ulist_eqb` : boolean equality for universe params.
//! - `kexpr_beq` : the structural boolean equality (reducible Definition).
//! - `*_eqb_refl` reflexivity lemmas, culminating in `kexpr_beq_refl`.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register decidable syntactic equality on `KExpr` and its reflexivity
    /// metatheorem.
    ///
    /// Depends only on the foundation types + `expr_model` (KExpr) + `rec_env`
    /// (`nat_eqb`/`name_eqb`) stages. Purely additive; nothing in the active
    /// confluence lane is referenced or modified.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    /// The two Level primitives `kexpr_beq` shares with `add_env_extensions`.
    ///
    /// Split out so `add_kexpr_beq_core` can be wired into the LIVE stage list
    /// after `add_env_extensions` (stage 101) without double-registering them —
    /// the kernel rejects the second `add_decl` for a name. `level_eqb` is
    /// byte-identical to env_extensions' copy and `level_is_zero` is
    /// alpha-equivalent (`Level.param n` vs `... p`), so the semantics agree and
    /// this is a dedupe, not a conflict.
    ///
    /// The `#[cfg(test)]` spec builders in this file and in `kexpr_beq_sound.rs`
    /// build a MINIMAL substrate without `env_extensions`, so they still need
    /// these: they call `add_kexpr_beq`, which is prims + core.
    pub(super) fn add_kexpr_beq_prims(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def level_eqb (a : Level) (b : Level) : Bool := ",
                "Level.rec (fun (_ : Level) => Level -> Bool) ",
                // a = zero
                "(fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.true ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                // a = succ ap  (ih_ap : Level -> Bool)
                "(fun (ap : Level) (ih_ap : Level -> Bool) => fun (y : Level) => ",
                "Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => ih_ap yp) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                // a = max al ar  (ih_al ih_ar : Level -> Bool)
                "(fun (al : Level) (ar : Level) (ih_al : Level -> Bool) (ih_ar : Level -> Bool) => ",
                "fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                // a = imax al ar  (ih_al ih_ar : Level -> Bool)
                "(fun (al : Level) (ar : Level) (ih_al : Level -> Bool) (ih_ar : Level -> Bool) => ",
                "fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) ",
                "(fun (yn : Name) => Bool.false) y) ",
                // a = param am  (compare Names via name_eqb)
                "(fun (am : Name) => fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => name_eqb am yn) y) ",
                "a b",
            ),
            "Boolean equality on universe levels (Level = zero|succ|max|imax|param Name). \
             Two-level Level.rec dispatch (no nested match); param compares Names via name_eqb. \
             Const-arm substrate for kexpr_beq. Confluence-independent.",
        )?;
        self.add_recursive_def(
            concat!(
                "def level_is_zero (l : Level) : Bool := match l with ",
                "| Level.zero => Bool.true ",
                "| Level.succ p => Bool.false ",
                "| Level.max l1 l2 => Bool.and (level_is_zero l1) (level_is_zero l2) ",
                "| Level.imax l1 l2 => level_is_zero l2 ",
                "| Level.param n => Bool.false",
            ),
            "Level::is_zero (definitely-zero classifier): zero=true, succ/param=false, \
             max both-sides, imax the second side (impredicative collapse). \
             Mirrors clean-kernel level/mod.rs:367-374. Confluence-independent.",
        )?;
        Ok(())
    }

    /// Prims + core. Used by the `#[cfg(test)]` minimal-substrate builders; the
    /// live bundle wires `add_kexpr_beq_core` alone (env_extensions already
    /// supplies the prims).
    pub(super) fn add_kexpr_beq(&mut self) -> Result<(), SpecError> {
        self.add_kexpr_beq_prims()?;
        self.add_kexpr_beq_core()
    }

    pub(super) fn add_kexpr_beq_core(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Universe-parameter equality (const-arm substrate).
        // =========================================================

        // level_eqb: boolean equality on universe levels.
        // Level = zero | succ Level | max Level Level | imax Level Level | param Name.
        // Outer recursion on the first level via Level.rec's IH (motive
        // `Level -> Bool`); inner dispatch on the second via Level.rec. The
        // binary constructors (max/imax) conjoin the two recursive-field IHs
        // applied to the matching inner fields; `param` compares its Name via
        // `name_eqb`. Same two-level-recursor shape as `name_eqb` (rec_env), no
        // nested match, no self-recursion. Every Level.rec carries the 5th
        // (param) minor after the promotion of Level to the real kernel algebra.

        // =========================================================
        // THE REAL LEVEL ALGEBRA (increment #2 — mirrors
        // clean-kernel/src/level/mod.rs). Smart constructors + classifiers,
        // ADDED alongside the Nat machinery (nothing consumes them yet; the
        // sort:Nat->Level flip is a later batch). All reducible defs.
        // =========================================================

        // level_is_zero (level/mod.rs:367-374): definitely zero. A `param` might
        // be 0 at runtime so it is NOT definitely zero; `max` is zero iff both
        // sides are; `imax(_, l2)` is zero iff l2 is (impredicative collapse).

        // level_is_nonzero (level/mod.rs:382-389): definitely > 0. A `param`
        // might be 0 so it is NOT definitely nonzero; `max` is nonzero if either
        // side is; `imax(_, l2)` is nonzero iff l2 is (then imax reduces to max).
        self.add_recursive_def(
            concat!(
                "def level_is_nonzero (l : Level) : Bool := match l with ",
                "| Level.zero => Bool.false ",
                "| Level.succ p => Bool.true ",
                "| Level.max l1 l2 => Bool.or (level_is_nonzero l1) (level_is_nonzero l2) ",
                "| Level.imax l1 l2 => level_is_nonzero l2 ",
                "| Level.param n => Bool.false",
            ),
            "Level::is_nonzero (definitely-nonzero classifier): zero/param=false, succ=true, \
             max either-side, imax the second side. Mirrors clean-kernel level/mod.rs:382-389. \
             Confluence-independent.",
        )?;

        // level_max smart constructor (level/mod.rs:281-310): max(l,l)=l,
        // max(0,l)=l, max(l,0)=l, else a stuck Max node. The production is_geq
        // subsumption fast-path is omitted (as the kernel itself omits it under
        // cfg(kani); soundness-neutral — less-simplified stuck nodes only).
        // Encoded as nested Bool.rec on the three guards (unambiguous, reduces).
        self.add_recursive_def(
            concat!(
                "def level_max (l1 : Level) (l2 : Level) : Level := ",
                "Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) (Level.max l1 l2) l1 (level_is_zero l2)) ",
                "l2 (level_is_zero l1)) ",
                "l1 (level_eqb l1 l2)",
            ),
            "Level::max smart constructor: max(l,l)=l, max(0,l)=l, max(l,0)=l, else stuck Max. \
             Mirrors clean-kernel level/mod.rs:281-310 (is_geq fast-path omitted, soundness-neutral). \
             Confluence-independent.",
        )?;

        // level_imax smart constructor (level/mod.rs:324-350) — all five arms in
        // the kernel's order: (1) imax(l,0)=0 [l2 definitely zero]; (2)
        // imax(l,l')=max(l,l') [l2 definitely nonzero — the RECURSIVE is_nonzero,
        // Lean-4 parity, not a syntactic succ]; (3) imax(0,l)=l; (4) imax(1,l)=l
        // [is_one via level_eqb l1 (succ zero)]; (5) imax(l,l)=l; else a stuck
        // IMax node. Encoded as nested Bool.rec on the five guards.
        self.add_recursive_def(
            concat!(
                "def level_imax (l1 : Level) (l2 : Level) : Level := ",
                "Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) ",
                "(Bool.rec (fun (_ : Bool) => Level) (Level.imax l1 l2) l1 (level_eqb l1 l2)) ",
                "l2 (level_eqb l1 (Level.succ Level.zero))) ",
                "l2 (level_is_zero l1)) ",
                "(level_max l1 l2) (level_is_nonzero l2)) ",
                "Level.zero (level_is_zero l2)",
            ),
            "Level::imax smart constructor (the impredicative universe-max): imax(l,0)=0, \
             imax(l,l')=max(l,l') when l2 definitely-nonzero (recursive is_nonzero, Lean-4 parity), \
             imax(0,l)=l, imax(1,l)=l, imax(l,l)=l, else stuck IMax. Mirrors clean-kernel \
             level/mod.rs:324-350. The smart ctor B2's pi rule will consume. Confluence-independent.",
        )?;

        // §2b'' — the algebra COMPUTES (validation by Eq.refl / kernel reduction).
        // These non-vacuity witnesses kernel-check ONLY because level_imax
        // genuinely reduces per-arm; a masquerade would not reduce.

        // Impredicativity: imax(l, 0) = 0 (arm 1, mod.rs:325-328).
        self.add_definition(SpecDefinition {
            name: "level_imax_impredicative_zero".to_string(),
            type_src: "forall (u : Level), Eq Level (level_imax u Level.zero) Level.zero"
                .to_string(),
            value_src: Some("fun (u : Level) => Eq.refl Level Level.zero".to_string()),
            is_axiom: false,
            description: "level_imax u 0 = 0 (impredicative collapse, arm 1). Kernel-checked by \
                          reduction. Non-vacuity witness for level_imax."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "level_imax".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // imax(0, param n) = param n (arm 3, mod.rs:337-339): a param is neither
        // definitely zero nor definitely nonzero, so arms 1-2 fall through.
        self.add_definition(SpecDefinition {
            name: "level_imax_zero_param".to_string(),
            type_src: concat!(
                "forall (n : Name), ",
                "Eq Level (level_imax Level.zero (Level.param n)) (Level.param n)"
            )
            .to_string(),
            value_src: Some("fun (n : Name) => Eq.refl Level (Level.param n)".to_string()),
            is_axiom: false,
            description: "level_imax 0 (param n) = param n (arm 3). Kernel-checked by reduction. \
                          Non-vacuity witness for level_imax."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "level_imax".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Lean-4-parity is_one arm: imax(1, param n) = param n (arm 4, mod.rs:341-344).
        self.add_definition(SpecDefinition {
            name: "level_imax_one_param".to_string(),
            type_src: concat!(
                "forall (n : Name), ",
                "Eq Level (level_imax (Level.succ Level.zero) (Level.param n)) (Level.param n)"
            )
            .to_string(),
            value_src: Some("fun (n : Name) => Eq.refl Level (Level.param n)".to_string()),
            is_axiom: false,
            description: "level_imax 1 (param n) = param n (arm 4, is_one parity). Kernel-checked \
                          by reduction. Non-vacuity witness for level_imax."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "level_imax".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Definitely-nonzero right side reduces to the smart max, which sticks:
        // imax(param m, 1) = max(param m, 1) (arm 2 -> stuck Max).
        self.add_definition(SpecDefinition {
            name: "level_imax_param_one_stuck".to_string(),
            type_src: concat!(
                "forall (m : Name), ",
                "Eq Level (level_imax (Level.param m) (Level.succ Level.zero)) ",
                "(Level.max (Level.param m) (Level.succ Level.zero))"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (m : Name) => ",
                    "Eq.refl Level (Level.max (Level.param m) (Level.succ Level.zero))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "level_imax (param m) 1 = max (param m) 1 (arm 2 -> stuck Max: 1 is \
                          definitely nonzero, param m sticks). Kernel-checked by reduction. \
                          Non-vacuity witness for level_imax + level_max."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "level_imax".to_string(),
                "level_max".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ulist_eqb: boolean equality on ListType Level (universe parameter
        // lists). Recursion on the first list via ListType.rec's IH (motive
        // `ListType Level -> Bool`); inner dispatch on the second via
        // ListType.rec. cons/cons conjoins head equality (level_eqb) with the
        // recursive tail IH; nil/nil is true, length mismatch is false.
        self.add_recursive_def(
            concat!(
                "def ulist_eqb (xs : ListType Level) (ys : ListType Level) : Bool := ",
                "ListType.rec Level (fun (_ : ListType Level) => ListType Level -> Bool) ",
                // xs = nil
                "(fun (w : ListType Level) => ListType.rec Level (fun (_ : ListType Level) => Bool) ",
                "Bool.true ",
                "(fun (wh : Level) (wt : ListType Level) (_ : Bool) => Bool.false) w) ",
                // xs = cons xh xt  (ih_xt : ListType Level -> Bool)
                "(fun (xh : Level) (xt : ListType Level) (ih_xt : ListType Level -> Bool) => ",
                "fun (w : ListType Level) => ListType.rec Level (fun (_ : ListType Level) => Bool) ",
                "Bool.false ",
                "(fun (wh : Level) (wt : ListType Level) (_ : Bool) => Bool.and (level_eqb xh wh) (ih_xt wt)) w) ",
                "xs ys",
            ),
            "Boolean equality on universe-parameter lists (ListType Level). \
             Two-level ListType.rec dispatch. Const-arm substrate for kexpr_beq. \
             Confluence-independent.",
        )?;

        // =========================================================
        // kexpr_beq: structural boolean equality on KExpr.
        // =========================================================
        //
        // Outer KExpr.rec on the first expression (motive `KExpr -> Bool`),
        // inner KExpr.rec dispatch on the second. Each constructor compares its
        // payload: sort/bvar via nat_eqb; app/lam/pi conjoin the two
        // recursive-subterm IHs (Bool.and) applied to the matching inner
        // subterms; const conjoins name_eqb on the Name with ulist_eqb on the
        // universe params. All cross-constructor pairs are false. This is a
        // GENUINE syntactic equality: distinct constructors and distinct
        // payloads yield false (see the kexpr_beq_distinct_* witnesses below).
        //
        // Same two-level-recursor shape as name_eqb/level_eqb: no nested match,
        // no self-recursion, no `decide`/`native_decide`.
        self.add_recursive_def(
            concat!(
                "def kexpr_beq (a : KExpr) (b : KExpr) : Bool := ",
                "KExpr.rec (fun (_ : KExpr) => KExpr -> Bool) ",
                // a = sort n
                "(fun (n : Level) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => level_eqb n m) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = bvar i
                "(fun (i : Nat) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => nat_eqb i j) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = app f a1  (ih_f ih_a : KExpr -> Bool)
                "(fun (f : KExpr) (a1 : KExpr) (ih_f : KExpr -> Bool) (ih_a : KExpr -> Bool) => ",
                "fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_f g) (ih_a c)) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = lam ty1 b1  (ih_ty ih_b : KExpr -> Bool)
                "(fun (ty1 : KExpr) (b1 : KExpr) (ih_ty : KExpr -> Bool) (ih_b : KExpr -> Bool) => ",
                "fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_ty t) (ih_b d)) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = pi ty1 b1  (ih_ty ih_b : KExpr -> Bool)
                "(fun (ty1 : KExpr) (b1 : KExpr) (ih_ty : KExpr -> Bool) (ih_b : KExpr -> Bool) => ",
                "fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_ty t) (ih_b d)) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = const n1 us1
                "(fun (n1 : Name) (us1 : ListType Level) => fun (y : KExpr) => ",
                "KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (n2 : Name) (us2 : ListType Level) => Bool.and (name_eqb n1 n2) (ulist_eqb us1 us2)) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = let_ lt lv lb  (ih_lt ih_lv ih_lb : KExpr -> Bool)
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (ih_lt : KExpr -> Bool) (ih_lv : KExpr -> Bool) (ih_lb : KExpr -> Bool) => ",
                "fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (wt : KExpr) (wv : KExpr) (wb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.and (ih_lt wt) (Bool.and (ih_lv wv) (ih_lb wb))) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = proj ps pidx psub (ih_sub : KExpr -> Bool) — the sole matching
                // inner arm compares name + index + sub (recursively via ih_sub).
                "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (ih_sub : KExpr -> Bool) => ",
                "fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.and (name_eqb ps qs) (Bool.and (nat_eqb pidx qi) (ih_sub qsub))) ",
                "(fun (w : Nat) => Bool.false) y) ",
                // a = lit v — matching inner arm compares the literal value.
                "(fun (v : Nat) => fun (y : KExpr) => KExpr.rec (fun (_ : KExpr) => Bool) ",
                "(fun (m : Level) => Bool.false) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (g : KExpr) (c : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : KExpr) (d : KExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (nm : Name) (us : ListType Level) => Bool.false) ",
                "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (qs : Name) (qi : Nat) (qsub : KExpr) (_ : Bool) => Bool.false) ",
                "(fun (w : Nat) => nat_eqb v w) y) ",
                "a b",
            ),
            "Structural boolean equality on KExpr (sort|bvar|app|lam|pi|const|let_|proj|lit). \
             Two-level KExpr.rec dispatch: sort via level_eqb, bvar via nat_eqb, app/lam/pi via \
             Bool.and of subterm equalities, const via name_eqb + ulist_eqb, let_ via \
             the triple Bool.and of its ty/val/body subterm equalities, proj via name/index/subterm, \
             and lit via nat_eqb. \
             A genuine syntactic equality; the substrate for decidability of \
             definitional equality. Confluence-independent.",
        )?;

        // =========================================================
        // Reflexivity lemmas (bottom-up), culminating in kexpr_beq_refl.
        // =========================================================

        // nat_eqb_refl: nat_eqb n n = true.
        //
        // nat_eqb n n = nat_is_zero (Nat.add (Nat.sub n n) (Nat.sub n n)).
        // Transport `nat_sub_self n : Nat.sub n n = 0` through the function
        // `fun s => nat_is_zero (Nat.add s s)`: at s = 0 the body is
        // `nat_is_zero (Nat.add 0 0)`, and `Nat.add x 0` reduces to `x` (the
        // zero arm of Nat.add), so it is definitionally `nat_is_zero 0 = true`.
        // Thus a single Eq.cong delivers `Eq Bool (nat_eqb n n) true` up to defeq.
        self.add_definition_if_absent(SpecDefinition {
            name: "nat_eqb_refl".to_string(),
            type_src: "forall (n : Nat), Eq Bool (nat_eqb n n) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => ",
                    "Eq.cong Nat Bool ",
                    "(fun (s : Nat) => nat_is_zero (Nat.add s s)) ",
                    "(Nat.sub n n) Nat.zero ",
                    "(nat_sub_self n)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "nat_eqb n n = true. DerivedProved via Eq.cong transport of nat_sub_self \
                          through nat_is_zero (Nat.add s s). Foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "nat_sub_self".to_string(),
                "nat_is_zero".to_string(),
                "nat_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // name_eqb_refl: name_eqb m m = true, by Name.rec induction.
        // Name = anonymous | str Name Nat.
        // - anonymous: name_eqb anonymous anonymous = true by Eq.refl.
        // - str p k: name_eqb (str p k) (str p k) = Bool.and (name_eqb p p) (nat_eqb k k).
        //   IH gives `name_eqb p p = true`; nat_eqb_refl gives `nat_eqb k k = true`.
        //   Transport: rewrite `name_eqb p p` to true (Eq.cong with
        //   `fun bp => Bool.and bp (nat_eqb k k)`) lands at
        //   `Bool.and Bool.true (nat_eqb k k)`, which reduces to `nat_eqb k k`
        //   (zero arm of Bool.and / Bool.rec on true), then nat_eqb_refl k closes it.
        self.add_definition_structural_if_absent(SpecDefinition {
            name: "name_eqb_refl".to_string(),
            type_src: "forall (m : Name), Eq Bool (name_eqb m m) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (m : Name) => Name.rec ",
                    "(fun (z : Name) => Eq Bool (name_eqb z z) Bool.true) ",
                    // anonymous case
                    "(Eq.refl Bool Bool.true) ",
                    // str p k case: ih : name_eqb p p = true
                    "(fun (p : Name) (k : Nat) (ih : Eq Bool (name_eqb p p) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(name_eqb (Name.str p k) (Name.str p k)) ",
                    "(Bool.and Bool.true (nat_eqb k k)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bp : Bool) => Bool.and bp (nat_eqb k k)) ",
                    "(name_eqb p p) Bool.true ih) ",
                    "(nat_eqb_refl k)) ",
                    "m",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "name_eqb m m = true, by Name.rec induction + nat_eqb_refl. Bool.and true \
                          b reduces to b. DerivedProved, foundational closure."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Name.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "nat_eqb_refl".to_string(),
                "name_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // level_eqb_refl: level_eqb a a = true, by Level.rec induction.
        // Level = zero | succ Level | max Level Level | imax Level Level.
        // - zero: Eq.refl.
        // - succ p: level_eqb (succ p) (succ p) = level_eqb p p; IH closes.
        // - max l r / imax l r: = Bool.and (level_eqb l l) (level_eqb r r).
        //   Chain two Eq.cong transports (rewrite left IH then the residual
        //   `Bool.and true (level_eqb r r)` reduces to `level_eqb r r`, closed
        //   by the right IH).
        self.add_definition_structural(SpecDefinition {
            name: "level_eqb_refl".to_string(),
            type_src: "forall (a : Level), Eq Bool (level_eqb a a) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Level) => Level.rec ",
                    "(fun (z : Level) => Eq Bool (level_eqb z z) Bool.true) ",
                    // zero
                    "(Eq.refl Bool Bool.true) ",
                    // succ p : ih : level_eqb p p = true
                    "(fun (p : Level) (ih : Eq Bool (level_eqb p p) Bool.true) => ih) ",
                    // max l r : ih_l, ih_r
                    "(fun (l : Level) (r : Level) ",
                    "(ih_l : Eq Bool (level_eqb l l) Bool.true) ",
                    "(ih_r : Eq Bool (level_eqb r r) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(level_eqb (Level.max l r) (Level.max l r)) ",
                    "(Bool.and Bool.true (level_eqb r r)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bl : Bool) => Bool.and bl (level_eqb r r)) ",
                    "(level_eqb l l) Bool.true ih_l) ",
                    "ih_r) ",
                    // imax l r : ih_l, ih_r
                    "(fun (l : Level) (r : Level) ",
                    "(ih_l : Eq Bool (level_eqb l l) Bool.true) ",
                    "(ih_r : Eq Bool (level_eqb r r) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(level_eqb (Level.imax l r) (Level.imax l r)) ",
                    "(Bool.and Bool.true (level_eqb r r)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bl : Bool) => Bool.and bl (level_eqb r r)) ",
                    "(level_eqb l l) Bool.true ih_l) ",
                    "ih_r) ",
                    // param am : level_eqb (param am)(param am) = name_eqb am am;
                    // closed by name_eqb_refl am.
                    "(fun (am : Name) => name_eqb_refl am) ",
                    "a",
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "level_eqb a a = true, by Level.rec induction. DerivedProved, foundational \
                          closure."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Level.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "level_eqb".to_string(),
                "name_eqb_refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ulist_eqb_refl: ulist_eqb xs xs = true, by ListType.rec induction.
        // - nil: Eq.refl.
        // - cons h t: ulist_eqb (cons h t) (cons h t) = Bool.and (level_eqb h h) (ulist_eqb t t).
        //   Rewrite the head via level_eqb_refl (Eq.cong), residual
        //   `Bool.and true (ulist_eqb t t)` reduces to `ulist_eqb t t`, closed by IH.
        self.add_definition_structural(SpecDefinition {
            name: "ulist_eqb_refl".to_string(),
            type_src: "forall (xs : ListType Level), Eq Bool (ulist_eqb xs xs) Bool.true"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType Level) => ListType.rec Level ",
                    "(fun (z : ListType Level) => Eq Bool (ulist_eqb z z) Bool.true) ",
                    // nil
                    "(Eq.refl Bool Bool.true) ",
                    // cons h t : ih : ulist_eqb t t = true
                    "(fun (h : Level) (t : ListType Level) (ih : Eq Bool (ulist_eqb t t) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(ulist_eqb (ListType.cons Level h t) (ListType.cons Level h t)) ",
                    "(Bool.and Bool.true (ulist_eqb t t)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bh : Bool) => Bool.and bh (ulist_eqb t t)) ",
                    "(level_eqb h h) Bool.true (level_eqb_refl h)) ",
                    "ih) ",
                    "xs",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "ulist_eqb xs xs = true, by ListType.rec induction + level_eqb_refl. \
                          DerivedProved, foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ListType.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "level_eqb_refl".to_string(),
                "ulist_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kexpr_beq_refl: forall e, kexpr_beq e e = true. THE deliverable.
        //
        // By KExpr.rec induction on e (motive `fun z => kexpr_beq z z = true`):
        // - sort n  : kexpr_beq (sort n) (sort n) = level_eqb n n; level_eqb_refl n.
        // - bvar i  : = nat_eqb i i; nat_eqb_refl i.
        // - app f a : = Bool.and (kexpr_beq f f) (kexpr_beq a a); chain two
        //             transports (rewrite left IH, residual Bool.and true _
        //             reduces, close with right IH). Same for lam, pi.
        // - const n us : = Bool.and (name_eqb n n) (ulist_eqb us us); rewrite
        //             name via name_eqb_refl, residual reduces, close with
        //             ulist_eqb_refl.
        self.add_definition_structural(SpecDefinition {
            name: "kexpr_beq_refl".to_string(),
            type_src: "forall (e : KExpr), Eq Bool (kexpr_beq e e) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) => KExpr.rec ",
                    "(fun (z : KExpr) => Eq Bool (kexpr_beq z z) Bool.true) ",
                    // sort n
                    "(fun (n : Level) => level_eqb_refl n) ",
                    // bvar i
                    "(fun (i : Nat) => nat_eqb_refl i) ",
                    // app f a : ih_f, ih_a
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ih_f : Eq Bool (kexpr_beq f f) Bool.true) ",
                    "(ih_a : Eq Bool (kexpr_beq a a) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.app f a) (KExpr.app f a)) ",
                    "(Bool.and Bool.true (kexpr_beq a a)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bf : Bool) => Bool.and bf (kexpr_beq a a)) ",
                    "(kexpr_beq f f) Bool.true ih_f) ",
                    "ih_a) ",
                    // lam ty b : ih_ty, ih_b
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ih_ty : Eq Bool (kexpr_beq ty ty) Bool.true) ",
                    "(ih_b : Eq Bool (kexpr_beq b b) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.lam ty b) (KExpr.lam ty b)) ",
                    "(Bool.and Bool.true (kexpr_beq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (kexpr_beq b b)) ",
                    "(kexpr_beq ty ty) Bool.true ih_ty) ",
                    "ih_b) ",
                    // pi ty b : ih_ty, ih_b
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ih_ty : Eq Bool (kexpr_beq ty ty) Bool.true) ",
                    "(ih_b : Eq Bool (kexpr_beq b b) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.pi ty b) (KExpr.pi ty b)) ",
                    "(Bool.and Bool.true (kexpr_beq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (kexpr_beq b b)) ",
                    "(kexpr_beq ty ty) Bool.true ih_ty) ",
                    "ih_b) ",
                    // const n us
                    "(fun (n : Name) (us : ListType Level) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.const n us) (KExpr.const n us)) ",
                    "(Bool.and Bool.true (ulist_eqb us us)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bn : Bool) => Bool.and bn (ulist_eqb us us)) ",
                    "(name_eqb n n) Bool.true (name_eqb_refl n)) ",
                    "(ulist_eqb_refl us)) ",
                    // let_ lt lv lb : ih_lt, ih_lv, ih_lb (triple conjunction, nested Bool.and)
                    "(fun (lt : KExpr) (lv : KExpr) (lb : KExpr) ",
                    "(ih_lt : Eq Bool (kexpr_beq lt lt) Bool.true) ",
                    "(ih_lv : Eq Bool (kexpr_beq lv lv) Bool.true) ",
                    "(ih_lb : Eq Bool (kexpr_beq lb lb) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.let_ lt lv lb) (KExpr.let_ lt lv lb)) ",
                    "(Bool.and Bool.true (Bool.and (kexpr_beq lv lv) (kexpr_beq lb lb))) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (Bool.and (kexpr_beq lv lv) (kexpr_beq lb lb))) ",
                    "(kexpr_beq lt lt) Bool.true ih_lt) ",
                    "(Eq.trans Bool ",
                    "(Bool.and (kexpr_beq lv lv) (kexpr_beq lb lb)) ",
                    "(Bool.and Bool.true (kexpr_beq lb lb)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bv : Bool) => Bool.and bv (kexpr_beq lb lb)) ",
                    "(kexpr_beq lv lv) Bool.true ih_lv) ",
                    "ih_lb)) ",
                    // proj s i sub : = Bool.and (name_eqb s s) (Bool.and (nat_eqb i i)
                    // (kexpr_beq sub sub)); rewrite name then nat, close with ih_sub.
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : Eq Bool (kexpr_beq sub sub) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(kexpr_beq (KExpr.proj s i sub) (KExpr.proj s i sub)) ",
                    "(Bool.and Bool.true (Bool.and (nat_eqb i i) (kexpr_beq sub sub))) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bn : Bool) => Bool.and bn (Bool.and (nat_eqb i i) (kexpr_beq sub sub))) ",
                    "(name_eqb s s) Bool.true (name_eqb_refl s)) ",
                    "(Eq.trans Bool ",
                    "(Bool.and (nat_eqb i i) (kexpr_beq sub sub)) ",
                    "(Bool.and Bool.true (kexpr_beq sub sub)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bi : Bool) => Bool.and bi (kexpr_beq sub sub)) ",
                    "(nat_eqb i i) Bool.true (nat_eqb_refl i)) ",
                    "ih_sub)) ",
                    // lit v : = nat_eqb v v; nat_eqb_refl v.
                    "(fun (v : Nat) => nat_eqb_refl v) ",
                    "e",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "kexpr_beq e e = true for all KExpr e, by KExpr.rec structural induction \
                          over the 9 constructors. The reflexivity metatheorem for decidable \
                          syntactic equality. DerivedProved, foundational closure. \
                          Confluence-independent."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "kexpr_beq".to_string(),
                "nat_eqb_refl".to_string(),
                "level_eqb_refl".to_string(),
                "name_eqb_refl".to_string(),
                "ulist_eqb_refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Non-vacuity witnesses (masquerade guard): kexpr_beq is NOT
        // constantly-true. These kernel-check ONLY because kexpr_beq genuinely
        // reduces to `false` on distinct expressions.
        // =========================================================

        // sort 0 vs bvar 0 : different constructors -> false.
        self.add_definition(SpecDefinition {
            name: "kexpr_beq_distinct_sort_bvar_false".to_string(),
            type_src:
                "Eq Bool (kexpr_beq (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) Bool.false"
                    .to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "kexpr_beq (sort 0) (bvar 0) = false: distinct constructors compare unequal. \
                          Non-vacuity witness (kexpr_beq is not constantly-true). Kernel-checked by \
                          reduction."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["kexpr_beq".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // app (bvar 0) (bvar 0) vs lam (bvar 0) (bvar 0) : different constructors -> false.
        self.add_definition(SpecDefinition {
            name: "kexpr_beq_distinct_app_lam_false".to_string(),
            type_src: concat!(
                "Eq Bool (kexpr_beq ",
                "(KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)) ",
                "(KExpr.lam (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))) Bool.false",
            )
            .to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description:
                "kexpr_beq (app ..) (lam ..) = false: distinct constructors with identical \
                          payloads still compare unequal. Non-vacuity witness. Kernel-checked by \
                          reduction."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kexpr_beq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // bvar 0 vs bvar 1 : same constructor, different payload -> false.
        self.add_definition(SpecDefinition {
            name: "kexpr_beq_distinct_bvar_index_false".to_string(),
            type_src:
                "Eq Bool (kexpr_beq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))) Bool.false"
                    .to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "kexpr_beq (bvar 0) (bvar 1) = false: same constructor, distinct de Bruijn \
                          index compares unequal (genuine payload comparison, not just constructor \
                          tag). Non-vacuity witness. Kernel-checked by reduction."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["kexpr_beq".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;

    /// Build a spec with foundation + KExpr model + rec_env substrate, then
    /// register the kexpr_beq decls on top. Uses the Substitution bundle which
    /// already includes add_foundation_types, add_expr_model, and add_rec_env —
    /// exactly the substrate kexpr_beq needs — without wiring into the shared
    /// stage list (zero collision with the active confluence lane).
    fn build_kexpr_beq_spec() -> Specification {
        let mut spec = Specification::new_substitution_test_spec()
            .expect("substitution-test spec (foundation + expr_model + rec_env) should build");
        spec.add_kexpr_beq()
            .expect("kexpr_beq decls should elaborate and kernel-check");
        spec
    }

    /// Every kexpr_beq declaration registers, kernel-checks, and the proofs are
    /// DerivedProved with an empty (foundational) axiom closure. The fact that
    /// `add_kexpr_beq` returned Ok already means each proof term passed
    /// `env.add_decl` full kernel type-checking.
    #[test]
    fn test_kexpr_beq_decls_kernel_check_and_proved() {
        let spec = build_kexpr_beq_spec();
        let defs = spec.definitions();

        // Functions (reducible Definitions) are present.
        for name in [
            "level_eqb",
            "level_is_zero",
            "level_is_nonzero",
            "level_max",
            "level_imax",
            "ulist_eqb",
            "kexpr_beq",
        ] {
            assert!(
                defs.contains_key(name),
                "function {name} should be registered"
            );
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "function {name} should be in the kernel environment"
            );
        }

        // Reflexivity lemmas + THE deliverable are DerivedProved with empty
        // domain/helper axiom closure (foundational).
        for name in [
            "nat_eqb_refl",
            "name_eqb_refl",
            "level_eqb_refl",
            "ulist_eqb_refl",
            "kexpr_beq_refl",
            "level_imax_impredicative_zero",
            "level_imax_zero_param",
            "level_imax_one_param",
            "level_imax_param_one_stuck",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("lemma {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "lemma {name} must be DerivedProved (constructive proof)"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "lemma {name} must have empty axiom closure (foundational), got {:?}",
                def.axiom_deps
            );
            assert!(!def.is_axiom, "lemma {name} must not be an axiom");
        }
    }

    /// The deliverable theorem `kexpr_beq_refl : forall e, kexpr_beq e e = true`
    /// is registered as a Theorem (Prop-typed) carrying a real proof value, with
    /// the literal statement shape required.
    #[test]
    fn test_kexpr_beq_refl_is_theorem_with_proof() {
        let spec = build_kexpr_beq_spec();
        let def = spec
            .definitions()
            .get("kexpr_beq_refl")
            .expect("kexpr_beq_refl should be registered");
        assert!(
            def.elaborated_value.is_some(),
            "kexpr_beq_refl must carry a proof term"
        );
        assert!(
            def.type_src.contains("kexpr_beq e e") && def.type_src.contains("Bool.true"),
            "kexpr_beq_refl must literally state kexpr_beq e e = true, got: {}",
            def.type_src
        );
        // Prop-typed valued definitions are registered as kernel Theorems,
        // carrying the kernel-checked proof value.
        let decl = spec
            .env()
            .get_const(&clean_kernel::Name::from_string("kexpr_beq_refl"))
            .expect("kexpr_beq_refl should be in the kernel environment");
        assert_eq!(
            decl.kind,
            clean_kernel::ConstantKind::Theorem,
            "kexpr_beq_refl should be a kernel Theorem"
        );
        assert!(
            decl.value.is_some(),
            "kexpr_beq_refl Theorem should carry its proof value"
        );
    }

    /// Non-vacuity / masquerade guard: kexpr_beq is a GENUINE structural
    /// equality, not constantly-true. The three `*_false` witnesses only
    /// kernel-checked (i.e. `add_kexpr_beq` only returned Ok) because kexpr_beq
    /// actually reduces to `false` on distinct expressions:
    ///   - distinct constructors (sort vs bvar; app vs lam)
    ///   - same constructor, distinct payload (bvar 0 vs bvar 1)
    #[test]
    fn test_kexpr_beq_non_vacuous_false_on_distinct() {
        let spec = build_kexpr_beq_spec();
        let defs = spec.definitions();
        for name in [
            "kexpr_beq_distinct_sort_bvar_false",
            "kexpr_beq_distinct_app_lam_false",
            "kexpr_beq_distinct_bvar_index_false",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("non-vacuity witness {name} should be registered"));
            assert!(
                def.type_src.contains("Bool.false"),
                "witness {name} must assert the result is false"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "witness {name} must be DerivedProved"
            );
            // The witness is in the kernel env => its Eq.refl Bool false proof
            // kernel-checked => kexpr_beq genuinely reduced the distinct pair to
            // false. This is the masquerade guard.
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "witness {name} should be in the kernel environment (proof checked)"
            );
        }
    }
}

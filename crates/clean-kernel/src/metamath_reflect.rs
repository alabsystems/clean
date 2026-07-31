// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computational Metamath verifier — *proof by reflection*.
//!
//! # Why this exists
//!
//! Metamath proofs are checked by string substitution over symbol sequences.
//! The Mathverse import (`clean-mathverse`) replays them in *Rust*, which makes
//! that Rust checker TRUSTED — so imported theorems can only ever reach
//! `CertificateReplayed` / `SourceVerified`, never `KernelVerified`. The earlier
//! string-reflection encoding is rejected outright by the kernel (it is data,
//! not a checkable proposition).
//!
//! This module is the first brick of a genuine kernel-level Metamath checker,
//! built the same way as [`crate::resolution_check`]: the verifier's primitive
//! operations are registered as **reducible kernel `Definition`s** over kernel
//! *data*, and a concrete Metamath fact is certified by an `Eq`/`Eq.refl` term
//! that the kernel discharges by *evaluating* those definitions (β/δ/ι/native
//! reduction). The kernel genuinely re-runs the substitution; a tampered
//! statement reduces to a different value and the certificate fails to
//! type-check (see the litmus tests).
//!
//! # Encoding
//!
//! * A Metamath *symbol* is a `Nat` (an interned constant/variable id).
//! * A Metamath *expression* (the math string after the typecode, or including
//!   it) is a `List Nat`.
//!
//! # What is registered here
//!
//! All reducible `Definition`s; axiom closure ⊆ `FOUNDATIONAL_AXIOMS` (none are
//! axioms — they are built from `List.rec`/`Bool.rec`/`Nat.beq`):
//!
//!   * `Clean.MM.append : List Nat → List Nat → List Nat` — list concatenation.
//!   * `Clean.MM.iteList : Bool → List Nat → List Nat → List Nat` — list-valued
//!     `if`.
//!   * `Clean.MM.subst1 : Nat → List Nat → List Nat → List Nat` — substitute a
//!     single variable (`v`) by an expression (`r`) throughout an expression.
//!   * `Clean.MM.applySubst : (Nat → List Nat) → List Nat → List Nat` — apply a
//!     SIMULTANEOUS substitution `σ` (the genuine Metamath proof-step
//!     substitution; `σ` for a step is a nested-`iteList` lambda built by
//!     [`subst_fn`]).
//!   * `Clean.MM.listBeq : List Nat → List Nat → Bool` — structural list
//!     equality (the final-stack / hypothesis-match check).
//!
//! # Verification approaches (both demonstrated in the tests)
//!
//! 1. **Reflection** — certify a substitution result directly with `Eq.refl`
//!    over `applySubst`/`subst1` (the kernel reduces the substitution). A
//!    tampered target reduces to a different value and the cert is rejected.
//! 2. **Derivation terms** — postulate each Metamath assertion as a SCHEMATIC
//!    axiom `Π (σ : Nat → List Nat), Provable (applySubst σ …)` and PROVE each
//!    `$p` theorem with a derivation term applying them; the kernel checks the
//!    term, reducing `applySubst` to confirm the substituted hypotheses match.
//!    The complete propositional theorem `a1i` is verified this way (its axiom
//!    closure is exactly Metamath's postulates `{Provable, ax-1, ax-mp}`).
//!
//! Later milestones add the data-driven RPN stack-machine fold, `$d`
//! enforcement, and a `subst`-soundness metatheorem (mirroring
//! [`crate::resolution_soundness`]), plus the importer that emits these
//! certificates for real `set.mm` theorems.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{BinderInfo, Declaration, EnvError, Environment, Expr, Level};

/// Names of the declarations the Metamath reflection layer registers.
pub mod names {
    /// `Clean.MM.append : List Nat → List Nat → List Nat`.
    pub const APPEND: &str = "Clean.MM.append";
    /// `Clean.MM.iteList : Bool → List Nat → List Nat → List Nat`.
    pub const ITE_LIST: &str = "Clean.MM.iteList";
    /// `Clean.MM.subst1 : Nat → List Nat → List Nat → List Nat`.
    pub const SUBST1: &str = "Clean.MM.subst1";
    /// `Clean.MM.applySubst : (Nat → List Nat) → List Nat → List Nat`.
    pub const APPLY_SUBST: &str = "Clean.MM.applySubst";
    /// `Clean.MM.listBeq : List Nat → List Nat → Bool`.
    pub const LIST_BEQ: &str = "Clean.MM.listBeq";
    /// `Clean.MM.append_assoc` — append associativity.
    pub const APPEND_ASSOC: &str = "Clean.MM.append_assoc";
    /// `Clean.MM.applySubst_append` — `applySubst` distributes over `append`.
    pub const APPLYSUBST_APPEND: &str = "Clean.MM.applySubst_append";
    /// `Clean.MM.applySubst_compose` — substitution composition.
    pub const APPLYSUBST_COMPOSE: &str = "Clean.MM.applySubst_compose";
    /// `Clean.MM.memNat : Nat → List Nat → Bool` — code membership in a list.
    pub const MEM_NAT: &str = "Clean.MM.memNat";
    /// `Clean.MM.isVar : Nat → Nat → Bool` — O(1) range-coded variable test
    /// `isVar K n := (1 ≤ n) ∧ (n < K)`. Equivalent to `memNat n var_universe` because
    /// the importer interns all variables first, so variable codes fill `[1,K)`
    /// and constants are `≥ K`; that contiguity is kernel-verified per import by
    /// `mm.__vu_contig`. Reduces in one native `Nat.blt` step instead of a
    /// `~7496`-element `List.rec` scan.
    pub const IS_VAR: &str = "Clean.MM.isVar";
    /// `Clean.MM.listDisjoint : List Nat → List Nat → Bool` — no shared element.
    pub const LIST_DISJOINT: &str = "Clean.MM.listDisjoint";
    /// `Clean.MM.varsOf : List Nat → List Nat → List Nat` — filter a form to the
    /// codes that are variables (members of the explicit variable-code list).
    pub const VARS_OF: &str = "Clean.MM.varsOf";
    /// `Clean.MM.disjPair : List Nat → (Nat → List Nat) → Nat → Nat → Bool` —
    /// `$d x y` under a substitution: the variable-sets of `σ x` and `σ y` share
    /// no variable. The DV-soundness primitive (M12).
    pub const DISJ_PAIR: &str = "Clean.MM.disjPair";
    /// `Clean.MM.applySubstV : List Nat → (Nat → List Nat) → List Nat → List Nat`
    /// — substitution that fixes CONSTANTS by construction (substitutes only
    /// `var_universe` members). Makes `varsOf`/distribution lemmas TRUE for any σ.
    pub const APPLY_SUBST_V: &str = "Clean.MM.applySubstV";
    /// `Clean.MM.varsOf_append` — `varsOf` distributes over `append`.
    pub const VARSOF_APPEND: &str = "Clean.MM.varsOf_append";
    /// `Clean.MM.applySubstV_append` — `applySubstV` distributes over `append`.
    pub const APPLYSUBSTV_APPEND: &str = "Clean.MM.applySubstV_append";
    /// `Clean.MM.append_nil_right` — `append xs [] = xs`.
    pub const APPEND_NIL_RIGHT: &str = "Clean.MM.append_nil_right";
    /// `Clean.MM.varsOf_singleton` — `varsOf vars [h] = iteList (memNat h vars) [h] []`.
    pub const VARSOF_SINGLETON: &str = "Clean.MM.varsOf_singleton";
    /// `Clean.MM.applySubstV_singleton` — `applySubstV vars σ [h] = iteList (memNat h vars) (σ h) [h]`.
    pub const APPLYSUBSTV_SINGLETON: &str = "Clean.MM.applySubstV_singleton";
    /// `Clean.MM.varsOf_applySubstV_head` — the per-head identity (convoy):
    /// `varsOf vars (iteList (memNat h vars) (σ h) [h])
    ///    = applySubstV vars (λv. varsOf vars (σ v)) (iteList (memNat h vars) [h] [])`.
    pub const VARSOF_APPLYSUBSTV_HEAD: &str = "Clean.MM.varsOf_applySubstV_head";
    /// `Clean.MM.varsOf_applySubstV` — THE keystone distribution lemma:
    /// `varsOf vars (applySubstV vars σ e)
    ///    = applySubstV vars (λv. varsOf vars (σ v)) (varsOf vars e)`.
    pub const VARSOF_APPLYSUBSTV: &str = "Clean.MM.varsOf_applySubstV";
    /// `Clean.MM.applySubstV_compose_head` — per-head identity for compose.
    pub const APPLYSUBSTV_COMPOSE_HEAD: &str = "Clean.MM.applySubstV_compose_head";
    /// `Clean.MM.applySubstV_compose` — the reuse-bridge composition lemma:
    /// `applySubstV vars σ1 (applySubstV vars σ2 e)
    ///    = applySubstV vars (λv. applySubstV vars σ1 (σ2 v)) e`.
    pub const APPLYSUBSTV_COMPOSE: &str = "Clean.MM.applySubstV_compose";
    /// `Clean.MM.bor_assoc` — `or (or a b) c = or a (or b c)`.
    pub const BOR_ASSOC: &str = "Clean.MM.bor_assoc";
    /// `Clean.MM.band_assoc` — `and (and a b) c = and a (and b c)`.
    pub const BAND_ASSOC: &str = "Clean.MM.band_assoc";
    /// `Clean.MM.bnot_or` — de Morgan: `not (or a b) = and (not a) (not b)`.
    pub const BNOT_OR: &str = "Clean.MM.bnot_or";
    /// `Clean.MM.memNat_append` — `memNat x (append ys zs) = or (memNat x ys) (memNat x zs)`.
    pub const MEMNAT_APPEND: &str = "Clean.MM.memNat_append";
    /// `Clean.MM.band_comm` — `and a b = and b a`.
    pub const BAND_COMM: &str = "Clean.MM.band_comm";
    /// `Clean.MM.listDisjoint_append` — `listDisjoint xs (append ys zs)
    ///   = and (listDisjoint xs ys) (listDisjoint xs zs)`.
    pub const LISTDISJOINT_APPEND: &str = "Clean.MM.listDisjoint_append";
    /// `Clean.MM.listDisjoint_append_left` — `listDisjoint (append xs ys) zs
    ///   = and (listDisjoint xs zs) (listDisjoint ys zs)`. The LEFT-argument
    /// distribution (the keystone gives `varsOf (σ·)` append-trees on both sides
    /// of a compound `$d`, and the left one needs this to decompose).
    pub const LISTDISJOINT_APPEND_LEFT: &str = "Clean.MM.listDisjoint_append_left";
    /// `Clean.MM.listDisjoint_nil_right` — `∀ xs, listDisjoint xs [] = true`.
    /// `listDisjoint` recurses on its FIRST arg, so an empty SECOND arg is stuck on
    /// a symbolic first arg; this discharges the innermost `append … []` leaf.
    pub const LISTDISJOINT_NIL_RIGHT: &str = "Clean.MM.listDisjoint_nil_right";
}

// ── small Expr helpers ────────────────────────────────────────────────────────

fn nat_ty() -> Expr {
    // Cached: `nat_ty()` is called once per token of every encoded form (~50k
    // forms), and each `Expr::const_str` mints a fresh `Name` allocation. Caching
    // the `Const("Nat")` leaf and cloning it shares the Name storage across all
    // calls (Arc refcount bump) and skips the per-call string allocation.
    // SOUNDNESS: returns a value-identical `Const("Nat")`.
    thread_local! {
        static NAT: Expr = Expr::const_str("Nat");
    }
    NAT.with(Expr::clone)
}
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [x, y])
}
fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}
fn bnot(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), x)
}
fn nat_beq(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [x, y])
}
fn nat_blt(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.blt"), [x, y])
}
fn nat_ble(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [x, y])
}

/// Peel an application spine `f a1 a2 … an` into `(f, [a1,…,an])`.
fn mm_app_spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut head = e;
    let mut sp: Vec<&Expr> = Vec::new();
    while let crate::expr::ExprKind::App(f, a) = head.kind() {
        sp.push(a.as_ref());
        head = f.as_ref();
    }
    sp.reverse();
    (head, sp)
}

/// Native reducer for `Clean.MM.memNat n xs` on GROUND arguments.
///
/// Returns the membership `Bool` directly instead of letting the kernel unfold
/// the O(V≈7496) `List.rec` scan (the inner loop of `applySubstV`/`varsOf`/
/// `disjPair` on every form head — the verifier's super-linear hot path). Fires
/// ONLY when `n` is a `Nat` literal and `xs` is a fully-ground `List Nat` literal
/// (a `List.cons`/`List.nil` spine of `Nat` literals); otherwise returns `None`
/// and the definitional `List.rec` reduction is used unchanged.
///
/// SOUNDNESS: computes exactly `memNat`'s definitional result (list membership).
/// memNat's definition and every lemma proven against it are UNCHANGED and stay
/// build-checked — the lemma proofs reason about `memNat` on SYMBOLIC arguments,
/// where this reducer returns `None` and the definition is used. This reducer
/// only speeds up the GROUND evaluations during proof-checking, and its
/// correctness is pinned by the byte-identical verified-set test + the unit test
/// below (a wrong result there fails the test).
/// Extract a `u64` from a small `Nat` literal `Expr`, else `None`.
fn mm_nat_lit_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        crate::expr::ExprKind::Lit(crate::expr::Literal::Nat(crate::expr::BigNat::Small(v))) => {
            Some(*v)
        }
        _ => None,
    }
}

fn reduce_mm_memnat(args: &[&Expr]) -> Option<Expr> {
    use crate::expr::ExprKind;
    use std::sync::LazyLock;
    static LIST_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.cons"));
    static LIST_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.nil"));
    if args.len() != 2 {
        return None;
    }
    let n = mm_nat_lit_val(args[0])?;
    let mut cur: &Expr = args[1];
    loop {
        let (head, sp) = mm_app_spine(cur);
        let ExprKind::Const(name, _) = head.kind() else {
            return None; // not a ground list constructor — fall back to the definition
        };
        if *name == *LIST_NIL {
            return Some(bfalse()); // reached nil without a match
        }
        if *name == *LIST_CONS && sp.len() == 3 {
            // `@List.cons.{0} Nat h t` → sp = [Nat, h, t]
            let h = mm_nat_lit_val(sp[1])?;
            if h == n {
                return Some(btrue());
            }
            cur = sp[2];
        } else {
            return None;
        }
    }
}
/// `isVar K n` — the O(1) range-coded variable test (`Nat.blt n K`).
#[cfg(test)]
fn is_var_app(k: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::IS_VAR), [k, n])
}
/// `List Nat`.
fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat_ty(),
    )
}
/// `List α` for a given element type.
fn list_ty_of(elem: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        elem.clone(),
    )
}
/// `@List.nil.{0} α`.
fn list_nil(elem: Expr) -> Expr {
    thread_local! {
        static NIL: Expr = Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]);
    }
    Expr::app(NIL.with(Expr::clone), elem)
}
/// `@List.cons.{0} α h t`.
fn list_cons(elem: Expr, h: Expr, t: Expr) -> Expr {
    // Cached `Const("List.cons")` leaf: built once per token of every form; the
    // cached clone shares its Name storage and skips a fresh allocation.
    // SOUNDNESS: value-identical `Const("List.cons", {0})`.
    thread_local! {
        static CONS: Expr = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);
    }
    Expr::apps(CONS.with(Expr::clone), [elem, h, t])
}
/// `@List.rec.{1,0} α (motive := fun _ => result_ty) nil_case cons_case major`
/// for a *closed* (non-dependent) `result_ty`.
fn list_rec(elem: Expr, result_ty: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let motive = Expr::lam(BinderInfo::Default, list_ty_of(&elem), result_ty);
    Expr::apps(rec, [elem, motive, nil_case, cons_case, major])
}

/// Build the `List Nat` value `[a0, a1, …]` as nested `List.cons`.
fn nat_list_lit(items: &[u64]) -> Expr {
    let mut e = list_nil(nat_ty());
    for &x in items.iter().rev() {
        e = list_cons(nat_ty(), Expr::nat_lit(x), e);
    }
    e
}

/// Cached `nat_list_lit` for the variable universe `vu`.
///
/// The universe is identical for every assertion in a database (see
/// `MMAssertion::var_universe`), yet the schematic type of every declaration
/// embeds it via `applySubstV vu σ …`. Building its ~2,163-node `List Nat`
/// literal fresh per declaration duplicates ~345 KB across ~50,000
/// declarations (~16 GB resident at full set.mm) — the dominant env footprint.
///
/// Memoizing it so every declaration's type shares ONE `Arc` body collapses
/// that to a single copy (env ~16 GB → ~1–3 GB), which is what lets the full
/// sweep run on a small machine.
///
/// SOUNDNESS: returns an `Expr` value-identical to `nat_list_lit(universe)` —
/// pure structural sharing of a closed subterm (the σ-abstraction in
/// `EnvDeclBuilder::finish` leaves closed subterms unchanged), so every
/// registered type stays byte-identical and the verified set is unchanged.
/// Keyed on the universe, so a different database rebuilds correctly. The cache
/// is thread-local — each verifier worker/thread is independent — so there is
/// no locking and no cross-worker interference.
fn var_universe_lit(universe: &[u64]) -> Expr {
    thread_local! {
        static VU_CACHE: std::cell::RefCell<Option<(Vec<u64>, Expr)>> =
            const { std::cell::RefCell::new(None) };
    }
    VU_CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if let Some((u, e)) = c.as_ref() {
            if u.as_slice() == universe {
                return e.clone();
            }
        }
        let e = nat_list_lit(universe);
        *c = Some((universe.to_vec(), e.clone()));
        e
    })
}

// ── helpers for the inductive lemma proofs (everything over `List Nat : Sort 1`) ──

/// `Clean.MM.append a b`.
fn append2(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPEND), [a, b])
}
/// `Clean.MM.applySubst s e`.
fn applysubst2(s: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPLY_SUBST), [s, e])
}
/// `Clean.MM.iteList c thenL elseL`.
fn ite_list_app(c: Expr, then_l: Expr, else_l: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::ITE_LIST), [c, then_l, else_l])
}
/// `Clean.MM.memNat n xs`.
fn mem_nat_app(n: Expr, xs: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::MEM_NAT), [n, xs])
}
/// `Clean.MM.listDisjoint xs ys`.
fn list_disjoint_app(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::LIST_DISJOINT), [xs, ys])
}
/// `Clean.MM.varsOf vars e`.
fn vars_of_app(vars: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::VARS_OF), [vars, e])
}
/// `Clean.MM.applySubstV vars σ e`.
fn apply_subst_v_app(vars: Expr, sig: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPLY_SUBST_V), [vars, sig, e])
}
/// `Clean.MM.disjPair vars s x y` (x, y as Nat literals).
fn disjpair_app(vars: Expr, s: Expr, x: u64, y: u64) -> Expr {
    Expr::apps(
        Expr::const_str(names::DISJ_PAIR),
        [vars, s, Expr::nat_lit(x), Expr::nat_lit(y)],
    )
}
/// `@Eq.{1} Bool x y`.
fn eq_bool_t(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty(), x, y],
    )
}
/// `@Eq.{1} (List Nat) x y`.
fn eq_list_t(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_nat(), x, y],
    )
}
/// `@Eq.refl.{1} Bool v`.
fn eq_refl_bool_t(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}
/// `@List.cons.{0} Nat h : List Nat → List Nat` (prepend `h`).
fn cons_h_fn(h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [nat_ty(), h],
    )
}
/// `@congrArg.{1,1} (List Nat) (List Nat) a1 a2 f h : Eq (f a1) (f a2)`.
fn congr_arg_list(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [list_nat(), list_nat(), a1, a2, f, h],
    )
}
/// `@congrArg.{1,1} (List Nat) Bool a1 a2 f h : Eq (f a1) (f a2)` for `f : List Nat → Bool`.
fn congr_arg_list_bool(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [list_nat(), bool_ty(), a1, a2, f, h],
    )
}
/// `@congrArg.{1,1} Bool (List Nat) a1 a2 f h : Eq (f a1) (f a2)` for `f : Bool → List Nat`.
fn congr_arg_bool_list(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [bool_ty(), list_nat(), a1, a2, f, h],
    )
}
/// `@Eq.refl.{1} Bool v`.
fn eq_refl_bool_e(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), v],
    )
}
/// `@congrArg.{1,1} Bool Bool a1 a2 f h : Eq (f a1) (f a2)` for `f : Bool → Bool`.
fn congr_arg_bool_bool(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [bool_ty(), bool_ty(), a1, a2, f, h],
    )
}
/// `@Eq.trans.{1} Bool a b c h1 h2 : Eq a c`.
fn eq_trans_bool(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), a, b, c, h1, h2],
    )
}
/// `@Eq.symm.{1} Bool a b h : Eq b a`.
fn eq_symm_bool(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty(), a, b, h],
    )
}
/// Proof of `(P∧Q)∧(S∧T) = (P∧S)∧(Q∧T)` via `band_assoc`/`band_comm`. Realigns the
/// `listDisjoint_append` cons-case grouping.
fn band4_rearrange(p: &Expr, q: &Expr, s: &Expr, t: &Expr) -> Expr {
    let basc =
        |a: Expr, b: Expr, c: Expr| Expr::apps(Expr::const_str(names::BAND_ASSOC), [a, b, c]);
    let bcomm = |a: Expr, b: Expr| Expr::apps(Expr::const_str(names::BAND_COMM), [a, b]);
    let p_fn = Expr::lam(
        BinderInfo::Default,
        bool_ty(),
        band(p.clone(), Expr::bvar(0)),
    );
    let xt_fn = Expr::lam(
        BinderInfo::Default,
        bool_ty(),
        band(Expr::bvar(0), t.clone()),
    );
    let (pp, qq, ss, tt) = (p.clone(), q.clone(), s.clone(), t.clone());
    let st = band(ss.clone(), tt.clone());
    let qt = band(qq.clone(), tt.clone());
    let qs = band(qq.clone(), ss.clone());
    let sq = band(ss.clone(), qq.clone());
    let a0 = band(band(pp.clone(), qq.clone()), st.clone());
    let a1 = band(pp.clone(), band(qq.clone(), st.clone()));
    let a2 = band(pp.clone(), band(qs.clone(), tt.clone()));
    let a3 = band(pp.clone(), band(sq.clone(), tt.clone()));
    let a4 = band(pp.clone(), band(ss.clone(), qt.clone()));
    let a5 = band(band(pp.clone(), ss.clone()), qt.clone());
    let t1 = basc(pp.clone(), qq.clone(), st.clone());
    let t2 = congr_arg_bool_bool(
        band(qq.clone(), st.clone()),
        band(qs.clone(), tt.clone()),
        p_fn.clone(),
        eq_symm_bool(
            band(qs.clone(), tt.clone()),
            band(qq.clone(), st.clone()),
            basc(qq.clone(), ss.clone(), tt.clone()),
        ),
    );
    let t3 = congr_arg_bool_bool(
        band(qs.clone(), tt.clone()),
        band(sq.clone(), tt.clone()),
        p_fn.clone(),
        congr_arg_bool_bool(qs.clone(), sq.clone(), xt_fn, bcomm(qq.clone(), ss.clone())),
    );
    let t4 = congr_arg_bool_bool(
        band(sq.clone(), tt.clone()),
        band(ss.clone(), qt.clone()),
        p_fn,
        basc(ss.clone(), qq.clone(), tt.clone()),
    );
    let t5 = eq_symm_bool(
        a5.clone(),
        a4.clone(),
        basc(pp.clone(), ss.clone(), qt.clone()),
    );
    let tail = eq_trans_bool(a3.clone(), a4.clone(), a5.clone(), t4, t5);
    let tail = eq_trans_bool(a2.clone(), a3, a5.clone(), t3, tail);
    let tail = eq_trans_bool(a1.clone(), a2, a5.clone(), t2, tail);
    eq_trans_bool(a0, a1, a5, t1, tail)
}
/// `@Eq.symm.{1} (List Nat) a b h : Eq b a`.
fn eq_symm_list(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [list_nat(), a, b, h],
    )
}
/// `@Eq.trans.{1} (List Nat) a b c h1 h2 : Eq a c`.
fn eq_trans_list(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [list_nat(), a, b, c, h1, h2],
    )
}
/// `@List.rec.{0,0} Nat motive nil_case cons_case major` — induction into `Prop`.
fn list_rec_prop(motive: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::zero(), Level::zero()],
        ),
        [nat_ty(), motive, nil_case, cons_case, major],
    )
}
/// The substitution-map type `Nat → List Nat`.
fn subst_ty() -> Expr {
    Expr::arrow(nat_ty(), list_nat())
}
/// `Clean.MM.append x : List Nat → List Nat` (partial application — "prepend x").
fn append_fn(x: Expr) -> Expr {
    Expr::app(Expr::const_str(names::APPEND), x)
}
/// `Clean.MM.append_assoc x y z`.
fn append_assoc_app(x: Expr, y: Expr, z: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPEND_ASSOC), [x, y, z])
}
/// `Clean.MM.applySubst_append s xs ys`.
fn applysubst_append_app(s: Expr, xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPLYSUBST_APPEND), [s, xs, ys])
}

impl Environment {
    /// Register the computational Metamath checker layer (reflection backend).
    ///
    /// Idempotent. Requires `Bool`, `Nat`, `List`, `Eq`, `Nat.beq`; initializes
    /// them if absent. All registered ops are reducible `Definition`s with axiom
    /// closure ⊆ `FOUNDATIONAL_AXIOMS`.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_metamath_reflect(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::SUBST1)).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_nat()?;
        self.init_list()?;
        self.init_nat_cmp()?; // Nat.beq

        self.register_append()?;
        self.register_ite_list()?;
        self.register_subst1()?;
        self.register_apply_subst()?;
        self.register_list_beq()?;
        self.register_subst_lemmas()?;
        self.register_dv_predicates()?;
        // Fast path: compute `memNat` on ground args natively (O(V) native scan
        // instead of the kernel unfolding a ~7496-element List.rec). The memNat
        // Definition + all its lemmas are unchanged and stay build-checked; this
        // only speeds up ground evaluation during proof-checking.
        self.register_native_reducer(Name::from_string(names::MEM_NAT), reduce_mm_memnat);
        self.register_vars_subst_lemmas()?;
        Ok(())
    }

    /// Register the constant-fixing substitution `applySubstV` and the
    /// append-distribution lemmas `varsOf_append` / `applySubstV_append` (M13) —
    /// the kernel-verified keystones toward schematic `$d`/dummy-variable theorem
    /// reuse. `applySubstV vars σ e` substitutes ONLY `vars` members, fixing
    /// constants by construction; the two lemmas are `Theorem`s proved by `List.rec`
    /// induction (zero new axioms — the per-head `iteList (memNat h vars) …` term is
    /// carried OPAQUELY, mirroring `applySubst_append`, so no `Bool.rec` split on the
    /// stuck membership test is needed). Proved via a 3-strategy worktree swarm.
    fn register_vars_subst_lemmas(&mut self) -> Result<(), EnvError> {
        self.register_apply_subst_v()?;
        self.register_varsof_append()?;
        self.register_applysubstv_append()?;
        self.register_append_nil_right()?;
        self.register_singletons()?;
        self.register_head_identity()?;
        self.register_varsof_applysubstv()?;
        self.register_applysubstv_compose_head()?;
        self.register_applysubstv_compose()?;
        self.register_bool_algebra()?;
        self.register_memnat_append()?;
        self.register_band_comm()?;
        self.register_listdisjoint_append()?;
        self.register_listdisjoint_nil_right()?;
        self.register_listdisjoint_append_left()?;
        Ok(())
    }

    /// `∀ a b, and a b = and b a` — `Bool.rec` on `a`, each branch an inner
    /// `Bool.rec` on `b` (both leaves `refl`).
    fn register_band_comm(&mut self) -> Result<(), EnvError> {
        let bt = bool_ty();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bt.clone());
            let (b_id, bb) = b.fresh_local(bt.clone());
            let goal = eq_bool_t(band(a.clone(), bb.clone()), band(bb.clone(), a.clone()));
            let t = b.mk_pi(b_id, BinderInfo::Default, bt.clone(), goal);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, bt.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bt.clone());
            let (b_id, bb) = b.fresh_local(bt.clone());
            let motive_a = {
                let mut mc = EnvDeclBuilder::child_of(&b);
                let (av_id, av) = mc.fresh_local(bt.clone());
                let m = eq_bool_t(band(av.clone(), bb.clone()), band(bb.clone(), av.clone()));
                mc.finish_child(mc.mk_lam(av_id, BinderInfo::Default, bt.clone(), m))
            };
            // inner Bool.rec on `bb` for a given outer constant (false/true).
            let inner = |bb: &Expr, motive_body: &dyn Fn(&Expr) -> Expr, f0: Expr, f1: Expr| {
                let mut ic = EnvDeclBuilder::new();
                let (bv_id, bv) = ic.fresh_local(bool_ty());
                let m =
                    ic.finish(ic.mk_lam(bv_id, BinderInfo::Default, bool_ty(), motive_body(&bv)));
                Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                    [m, f0, f1, bb.clone()],
                )
            };
            // false branch: and false b = false; need Eq false (and b false).
            let false_case = inner(
                &bb,
                &|bv| eq_bool_t(bfalse(), band(bv.clone(), bfalse())),
                eq_refl_bool_e(bfalse()),
                eq_refl_bool_e(bfalse()),
            );
            // true branch: and true b = b; need Eq b (and b true).
            let true_case = inner(
                &bb,
                &|bv| eq_bool_t(bv.clone(), band(bv.clone(), btrue())),
                eq_refl_bool_e(bfalse()),
                eq_refl_bool_e(btrue()),
            );
            let recur = Expr::apps(
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                [motive_a, false_case, true_case, a.clone()],
            );
            let r = b.mk_lam(b_id, BinderInfo::Default, bt.clone(), recur);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, bt.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::BAND_COMM),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ xs ys zs, listDisjoint xs (append ys zs)
    ///   = and (listDisjoint xs ys) (listDisjoint xs zs)`. `List.rec` on `xs`;
    /// cons-case: rewrite `bnot (memNat h (append ys zs))` to `and P Q` (via
    /// `memNat_append` + de-Morgan), apply the IH, then re-arrange
    /// `(P&Q)&(S&T) = (P&S)&(Q&T)` with `band_assoc`/`band_comm`.
    fn register_listdisjoint_append(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let bt = bool_ty();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let goal = eq_bool_t(
                list_disjoint_app(xs.clone(), append2(ys.clone(), zs.clone())),
                band(
                    list_disjoint_app(xs.clone(), ys.clone()),
                    list_disjoint_app(xs.clone(), zs.clone()),
                ),
            );
            let t = b.mk_pi(zs_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let w = append2(ys.clone(), zs.clone());
            let goal_of = |u: &Expr| {
                eq_bool_t(
                    list_disjoint_app(u.clone(), w.clone()),
                    band(
                        list_disjoint_app(u.clone(), ys.clone()),
                        list_disjoint_app(u.clone(), zs.clone()),
                    ),
                )
            };
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (u_id, u) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(u_id, BinderInfo::Default, ln.clone(), goal_of(&u)))
            };
            let nil_case = eq_refl_bool_e(btrue());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let p = bnot(mem_nat_app(h.clone(), ys.clone()));
                let q = bnot(mem_nat_app(h.clone(), zs.clone()));
                let s = list_disjoint_app(t.clone(), ys.clone());
                let tt = list_disjoint_app(t.clone(), zs.clone());
                let mem_w = mem_nat_app(h.clone(), w.clone());
                let bnot_mem_w = bnot(mem_w.clone());
                let ld_t_w = list_disjoint_app(t.clone(), w.clone());
                // L = and (bnot (memNat h W)) (listDisjoint t W)
                let l = band(bnot_mem_w.clone(), ld_t_w.clone());
                let pq = band(p.clone(), q.clone());
                let st = band(s.clone(), tt.clone());
                let r_final = band(band(p.clone(), s.clone()), band(q.clone(), tt.clone()));
                let ih_ty = goal_of(&t);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());

                // e_pq : bnot (memNat h W) = and P Q
                let bnot_fn = Expr::lam(BinderInfo::Default, bt.clone(), bnot(Expr::bvar(0)));
                let memapp = Expr::apps(
                    Expr::const_str(names::MEMNAT_APPEND),
                    [h.clone(), ys.clone(), zs.clone()],
                );
                let bor_mem = bor(
                    mem_nat_app(h.clone(), ys.clone()),
                    mem_nat_app(h.clone(), zs.clone()),
                );
                let cong_bnot =
                    congr_arg_bool_bool(mem_w.clone(), bor_mem.clone(), bnot_fn, memapp);
                let demorgan = Expr::apps(
                    Expr::const_str(names::BNOT_OR),
                    [
                        mem_nat_app(h.clone(), ys.clone()),
                        mem_nat_app(h.clone(), zs.clone()),
                        bfalse(),
                    ],
                );
                let e_pq = eq_trans_bool(
                    bnot_mem_w.clone(),
                    bnot(bor_mem),
                    pq.clone(),
                    cong_bnot,
                    demorgan,
                );
                // r1 : L = and (P&Q) (listDisjoint t W)
                let f_left = Expr::lam(
                    BinderInfo::Default,
                    bt.clone(),
                    band(Expr::bvar(0), ld_t_w.clone()),
                );
                let r1 = congr_arg_bool_bool(bnot_mem_w.clone(), pq.clone(), f_left, e_pq);
                let l2 = band(pq.clone(), ld_t_w.clone());
                // r2 : and (P&Q) (listDisjoint t W) = and (P&Q) (S&T)
                let f_right = Expr::lam(
                    BinderInfo::Default,
                    bt.clone(),
                    band(pq.clone(), Expr::bvar(0)),
                );
                let r2 = congr_arg_bool_bool(ld_t_w.clone(), st.clone(), f_right, ih);
                let l3 = band(pq.clone(), st.clone());
                // r3 : (P&Q)&(S&T) = (P&S)&(Q&T)  — the 4-element rearrangement.
                let r3 = band4_rearrange(&p, &q, &s, &tt);
                // chain L = l2 = l3 = r_final
                let tail = eq_trans_bool(l2.clone(), l3.clone(), r_final.clone(), r2, r3);
                let body = eq_trans_bool(l, l2, r_final, r1, tail);
                let rr = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let rr = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), rr);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), rr))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(zs_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::LISTDISJOINT_APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ xs, listDisjoint xs [] = true`. `List.rec` on `xs`: the cons-case body
    /// reduces (`bnot (memNat h []) ≡ true`, `band true X ≡ X`) so the IH discharges
    /// it directly.
    fn register_listdisjoint_nil_right(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let nil = list_nil(nat_ty());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let goal = eq_bool_t(list_disjoint_app(xs.clone(), nil.clone()), btrue());
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), goal))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let goal_of = |u: &Expr| eq_bool_t(list_disjoint_app(u.clone(), nil.clone()), btrue());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (u_id, u) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(u_id, BinderInfo::Default, ln.clone(), goal_of(&u)))
            };
            let nil_case = eq_refl_bool_e(btrue());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let ih_ty = goal_of(&t);
                // body : listDisjoint (h::t) [] = true ; LHS reduces to listDisjoint t [],
                // so the IH (listDisjoint t [] = true) is accepted up to def-eq.
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, ih);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), rec))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::LISTDISJOINT_NIL_RIGHT),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ xs ys zs, listDisjoint (append xs ys) zs
    ///   = and (listDisjoint xs zs) (listDisjoint ys zs)`. `List.rec` on `xs`;
    /// cons-case re-associates the `band` via `band_assoc` (symm).
    fn register_listdisjoint_append_left(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let bt = bool_ty();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let goal = eq_bool_t(
                list_disjoint_app(append2(xs.clone(), ys.clone()), zs.clone()),
                band(
                    list_disjoint_app(xs.clone(), zs.clone()),
                    list_disjoint_app(ys.clone(), zs.clone()),
                ),
            );
            let t = b.mk_pi(zs_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let ld_ys_zs = list_disjoint_app(ys.clone(), zs.clone());
            let goal_of = |u: &Expr| {
                eq_bool_t(
                    list_disjoint_app(append2(u.clone(), ys.clone()), zs.clone()),
                    band(list_disjoint_app(u.clone(), zs.clone()), ld_ys_zs.clone()),
                )
            };
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (u_id, u) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(u_id, BinderInfo::Default, ln.clone(), goal_of(&u)))
            };
            // nil: listDisjoint (append [] ys) zs ≡ listDisjoint ys zs ; RHS
            // band (listDisjoint [] zs) (listDisjoint ys zs) ≡ band true (…) ≡ (…).
            let nil_case = eq_refl_bool_e(ld_ys_zs.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let p0 = bnot(mem_nat_app(h.clone(), zs.clone()));
                let ld_t_app = list_disjoint_app(append2(t.clone(), ys.clone()), zs.clone());
                let ld_t_zs = list_disjoint_app(t.clone(), zs.clone());
                let ih_ty = goal_of(&t);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // LHS ≡ band p0 (listDisjoint (append t ys) zs).
                // step1 : band p0 ld_t_app = band p0 (band ld_t_zs ld_ys_zs)  [congrArg (band p0) ih]
                let band_p0 = Expr::lam(
                    BinderInfo::Default,
                    bt.clone(),
                    band(p0.clone(), Expr::bvar(0)),
                );
                let step1 = congr_arg_bool_bool(
                    ld_t_app.clone(),
                    band(ld_t_zs.clone(), ld_ys_zs.clone()),
                    band_p0,
                    ih,
                );
                // step2 : band p0 (band ld_t_zs ld_ys_zs) = band (band p0 ld_t_zs) ld_ys_zs
                //         = symm(band_assoc p0 ld_t_zs ld_ys_zs)
                let assoc = Expr::apps(
                    Expr::const_str(names::BAND_ASSOC),
                    [p0.clone(), ld_t_zs.clone(), ld_ys_zs.clone()],
                );
                let lhs_assoc = band(band(p0.clone(), ld_t_zs.clone()), ld_ys_zs.clone());
                let rhs_assoc = band(p0.clone(), band(ld_t_zs.clone(), ld_ys_zs.clone()));
                let step2 = eq_symm_bool(lhs_assoc.clone(), rhs_assoc.clone(), assoc);
                // body : band p0 ld_t_app = band (band p0 ld_t_zs) ld_ys_zs.
                // RHS ≡ band (listDisjoint (h::t) zs) ld_ys_zs (since listDisjoint (h::t) zs
                // ≡ band p0 ld_t_zs), matching goal_of(h::t).
                let body = eq_trans_bool(
                    band(p0.clone(), ld_t_app.clone()),
                    rhs_assoc,
                    lhs_assoc,
                    step1,
                    step2,
                );
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(zs_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::LISTDISJOINT_APPEND_LEFT),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ x ys zs, memNat x (append ys zs) = or (memNat x ys) (memNat x zs)`.
    /// `List.rec` on `ys`; cons-case uses the IH + `bor_assoc` to re-associate.
    fn register_memnat_append(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let bt = bool_ty();
        let _nil = list_nil(nat_ty());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat_ty());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let goal = eq_bool_t(
                mem_nat_app(x.clone(), append2(ys.clone(), zs.clone())),
                bor(
                    mem_nat_app(x.clone(), ys.clone()),
                    mem_nat_app(x.clone(), zs.clone()),
                ),
            );
            let t = b.mk_pi(zs_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, nat_ty(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat_ty());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let mem_z = mem_nat_app(x.clone(), zs.clone());
            let goal_of = |w: &Expr| {
                eq_bool_t(
                    mem_nat_app(x.clone(), append2(w.clone(), zs.clone())),
                    bor(mem_nat_app(x.clone(), w.clone()), mem_z.clone()),
                )
            };
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), goal_of(&w)))
            };
            // nil: memNat x (append [] zs) = memNat x zs ≡ or (memNat x []) (memNat x zs).
            let nil_case = eq_refl_bool_e(mem_z.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let beq = nat_beq(x.clone(), h.clone()); // A
                let mem_t = mem_nat_app(x.clone(), t.clone()); // B
                                                               // L = memNat x (append (h::t) zs) ≡ or A (memNat x (append t zs))
                let mem_app_t = mem_nat_app(x.clone(), append2(t.clone(), zs.clone()));
                let l = bor(beq.clone(), mem_app_t.clone());
                // R = or (memNat x (h::t)) (memNat x zs) ≡ or (or A B) C
                let r = bor(bor(beq.clone(), mem_t.clone()), mem_z.clone());
                let ih_ty = goal_of(&t);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // s1 : or A (memNat x (append t zs)) = or A (or B C)   (congrArg (or A) ih)
                let or_a = Expr::lam(
                    BinderInfo::Default,
                    bt.clone(),
                    bor(beq.clone(), Expr::bvar(0)),
                );
                let or_abc = bor(beq.clone(), bor(mem_t.clone(), mem_z.clone()));
                let s1 =
                    congr_arg_bool_bool(mem_app_t, bor(mem_t.clone(), mem_z.clone()), or_a, ih);
                // s2 : or (or A B) C = or A (or B C)   (bor_assoc A B C)
                let s2 = Expr::apps(
                    Expr::const_str(names::BOR_ASSOC),
                    [beq.clone(), mem_t.clone(), mem_z.clone()],
                );
                let s2sym = eq_symm_bool(r.clone(), or_abc.clone(), s2);
                let body = eq_trans_bool(l, or_abc, r, s1, s2sym);
                let rr = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let rr = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), rr);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), rr))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, ys.clone());
            let r = b.mk_lam(zs_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, nat_ty(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::MEMNAT_APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// Bool-algebra lemmas needed for the `$d`-discharge chain (`listDisjoint_append`
    /// etc.): `bor_assoc`, `band_assoc`, de-Morgan `bnot_or`. Each is a `Bool.rec`
    /// on the first argument where BOTH branches close by `Eq.refl` (the Bool ops
    /// iota-reduce once the head is a constructor).
    fn register_bool_algebra(&mut self) -> Result<(), EnvError> {
        let bt = bool_ty();
        // A 3-ary Bool lemma proved by Bool.rec on `a`, both branches refl.
        let reg3 = |this: &mut Self,
                    name: &str,
                    body: &dyn Fn(&Expr, &Expr, &Expr) -> Expr,
                    false_val: &dyn Fn(&Expr, &Expr) -> Expr,
                    true_val: &dyn Fn(&Expr, &Expr) -> Expr|
         -> Result<(), EnvError> {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bt.clone());
                let (b_id, bb) = b.fresh_local(bt.clone());
                let (c_id, cc) = b.fresh_local(bt.clone());
                let goal = body(&a, &bb, &cc);
                let t = b.mk_pi(c_id, BinderInfo::Default, bt.clone(), goal);
                let t = b.mk_pi(b_id, BinderInfo::Default, bt.clone(), t);
                b.finish(b.mk_pi(a_id, BinderInfo::Default, bt.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(bt.clone());
                let (b_id, bb) = b.fresh_local(bt.clone());
                let (c_id, cc) = b.fresh_local(bt.clone());
                let motive = {
                    let mut mc = EnvDeclBuilder::child_of(&b);
                    let (av_id, av) = mc.fresh_local(bt.clone());
                    let m = body(&av, &bb, &cc);
                    mc.finish_child(mc.mk_lam(av_id, BinderInfo::Default, bt.clone(), m))
                };
                let recur = Expr::apps(
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                    [
                        motive,
                        eq_refl_bool_e(false_val(&bb, &cc)),
                        eq_refl_bool_e(true_val(&bb, &cc)),
                        a.clone(),
                    ],
                );
                let r = b.mk_lam(c_id, BinderInfo::Default, bt.clone(), recur);
                let r = b.mk_lam(b_id, BinderInfo::Default, bt.clone(), r);
                b.finish(b.mk_lam(a_id, BinderInfo::Default, bt.clone(), r))
            };
            this.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: ty,
                value: val,
            })
        };
        // bor_assoc : or (or a b) c = or a (or b c)
        reg3(
            self,
            names::BOR_ASSOC,
            &|a, b, c| {
                eq_bool_t(
                    bor(bor(a.clone(), b.clone()), c.clone()),
                    bor(a.clone(), bor(b.clone(), c.clone())),
                )
            },
            &|b, c| bor(b.clone(), c.clone()),
            &|_b, _c| btrue(),
        )?;
        // band_assoc : and (and a b) c = and a (and b c)
        reg3(
            self,
            names::BAND_ASSOC,
            &|a, b, c| {
                eq_bool_t(
                    band(band(a.clone(), b.clone()), c.clone()),
                    band(a.clone(), band(b.clone(), c.clone())),
                )
            },
            &|_b, _c| bfalse(),
            &|b, c| band(b.clone(), c.clone()),
        )?;
        // bnot_or : not (or a b) = and (not a) (not b)  (the third arg `c` is unused)
        reg3(
            self,
            names::BNOT_OR,
            &|a, b, _c| {
                eq_bool_t(
                    bnot(bor(a.clone(), b.clone())),
                    band(bnot(a.clone()), bnot(b.clone())),
                )
            },
            &|b, _c| bnot(b.clone()),
            &|_b, _c| bfalse(),
        )?;
        Ok(())
    }

    /// Per-head identity for `applySubstV_compose`, by the same convoy as
    /// `head_identity` (b=true closes by `Eq.refl`; b=false rewrites the inner
    /// `memNat` through the equation + `applySubstV_singleton`).
    fn register_applysubstv_compose_head(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let single = |h: &Expr| list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
        let _nil = list_nil(nat_ty());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (h_id, h) = b.fresh_local(nat_ty());
            let c = mem_nat_app(h.clone(), vars.clone());
            let lhs = apply_subst_v_app(
                vars.clone(),
                s1.clone(),
                ite_list_app(c.clone(), Expr::app(s2.clone(), h.clone()), single(&h)),
            );
            let rhs = ite_list_app(
                c.clone(),
                apply_subst_v_app(vars.clone(), s1.clone(), Expr::app(s2.clone(), h.clone())),
                single(&h),
            );
            let goal = eq_list_nat(lhs, rhs);
            let t = b.mk_pi(h_id, BinderInfo::Default, nat_ty(), goal);
            let t = b.mk_pi(s2_id, BinderInfo::Default, st.clone(), t);
            let t = b.mk_pi(s1_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (h_id, h) = b.fresh_local(nat_ty());
            let c = mem_nat_app(h.clone(), vars.clone());
            let single_h = single(&h);
            let s2_h = Expr::app(s2.clone(), h.clone());
            let s1_h = Expr::app(s1.clone(), h.clone());
            let comp_h = apply_subst_v_app(vars.clone(), s1.clone(), s2_h.clone());
            let goal_of = |bv: &Expr| {
                eq_list_nat(
                    apply_subst_v_app(
                        vars.clone(),
                        s1.clone(),
                        ite_list_app(bv.clone(), s2_h.clone(), single_h.clone()),
                    ),
                    ite_list_app(bv.clone(), comp_h.clone(), single_h.clone()),
                )
            };
            let motive = {
                let mut mc = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = mc.fresh_local(bool_ty());
                let body = Expr::arrow(eq_bool_t(c.clone(), bb.clone()), goal_of(&bb));
                mc.finish_child(mc.mk_lam(bb_id, BinderInfo::Default, bool_ty(), body))
            };
            // true: both sides reduce to applySubstV vars s1 (s2 h) — refl.
            let true_case = {
                let mut tc = EnvDeclBuilder::child_of(&b);
                let (eq_id, _eqv) = tc.fresh_local(eq_bool_t(c.clone(), btrue()));
                let body = eq_refl_list_nat(comp_h.clone());
                tc.finish_child(tc.mk_lam(
                    eq_id,
                    BinderInfo::Default,
                    eq_bool_t(c.clone(), btrue()),
                    body,
                ))
            };
            // false: applySubstV vars s1 [h] = [h] via singleton + eq.
            let false_case = {
                let mut fc = EnvDeclBuilder::child_of(&b);
                let (eq_id, eqv) = fc.fresh_local(eq_bool_t(c.clone(), bfalse()));
                let sing = Expr::apps(
                    Expr::const_str(names::APPLYSUBSTV_SINGLETON),
                    [vars.clone(), s1.clone(), h.clone()],
                );
                let rw_fn = Expr::lam(
                    BinderInfo::Default,
                    bool_ty(),
                    ite_list_app(Expr::bvar(0), s1_h.clone(), single_h.clone()),
                );
                let rw = congr_arg_bool_list(c.clone(), bfalse(), rw_fn, eqv.clone());
                let asv = apply_subst_v_app(vars.clone(), s1.clone(), single_h.clone());
                let ite_c = ite_list_app(c.clone(), s1_h.clone(), single_h.clone());
                let ite_false = ite_list_app(bfalse(), s1_h.clone(), single_h.clone());
                let body = eq_trans_list(asv, ite_c, ite_false, sing, rw);
                fc.finish_child(fc.mk_lam(
                    eq_id,
                    BinderInfo::Default,
                    eq_bool_t(c.clone(), bfalse()),
                    body,
                ))
            };
            let recur = Expr::apps(
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                [
                    motive,
                    false_case,
                    true_case,
                    c.clone(),
                    eq_refl_bool_e(c.clone()),
                ],
            );
            let r = b.mk_lam(h_id, BinderInfo::Default, nat_ty(), recur);
            let r = b.mk_lam(s2_id, BinderInfo::Default, st.clone(), r);
            let r = b.mk_lam(s1_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPLYSUBSTV_COMPOSE_HEAD),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ vars σ1 σ2 e, applySubstV vars σ1 (applySubstV vars σ2 e)
    ///   = applySubstV vars (λv. applySubstV vars σ1 (σ2 v)) e` — the reuse bridge
    /// (analogue of `applySubst_compose`). `List.rec` on `e`; cons-case composes
    /// `applySubstV_append` + `applySubstV_compose_head` + the IH.
    fn register_applysubstv_compose(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let single = |h: &Expr| list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
        let nil = list_nil(nat_ty());
        // comp = λ v, applySubstV vars σ1 (σ2 v)
        let comp = |vars: &Expr, s1: &Expr, s2: &Expr| {
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                apply_subst_v_app(
                    vars.clone(),
                    s1.clone(),
                    Expr::app(s2.clone(), Expr::bvar(0)),
                ),
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                apply_subst_v_app(
                    vars.clone(),
                    s1.clone(),
                    apply_subst_v_app(vars.clone(), s2.clone(), e.clone()),
                ),
                apply_subst_v_app(vars.clone(), comp(&vars, &s1, &s2), e.clone()),
            );
            let t = b.mk_pi(e_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(s2_id, BinderInfo::Default, st.clone(), t);
            let t = b.mk_pi(s1_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let comp_e = comp(&vars, &s1, &s2);
            let dist = |w: &Expr| {
                eq_list_nat(
                    apply_subst_v_app(
                        vars.clone(),
                        s1.clone(),
                        apply_subst_v_app(vars.clone(), s2.clone(), w.clone()),
                    ),
                    apply_subst_v_app(vars.clone(), comp_e.clone(), w.clone()),
                )
            };
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), dist(&w)))
            };
            let nil_case = eq_refl_list_nat(nil.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let cc = mem_nat_app(h.clone(), vars.clone());
                let s2_h = Expr::app(s2.clone(), h.clone());
                let single_h = single(&h);
                // X = iteList c (σ2 h)[h] ; Y = applySubstV vars σ2 t
                let big_x = ite_list_app(cc.clone(), s2_h.clone(), single_h.clone());
                let big_y = apply_subst_v_app(vars.clone(), s2.clone(), t.clone());
                let s1_x = apply_subst_v_app(vars.clone(), s1.clone(), big_x.clone());
                let s1_y = apply_subst_v_app(vars.clone(), s1.clone(), big_y.clone());
                // head: applySubstV vars s1 X = iteList c (comp h) [h]
                let comp_h = apply_subst_v_app(vars.clone(), s1.clone(), s2_h.clone());
                let ite_comp = ite_list_app(cc.clone(), comp_h.clone(), single_h.clone());
                let comp_t = apply_subst_v_app(vars.clone(), comp_e.clone(), t.clone());
                let app_x = append2(s1_x.clone(), s1_y.clone());
                let app_ct = append2(ite_comp.clone(), s1_y.clone());
                let app_cc = append2(ite_comp.clone(), comp_t.clone());
                let cons_ht = list_cons(nat_ty(), h.clone(), t.clone());
                let lhs_cons = apply_subst_v_app(
                    vars.clone(),
                    s1.clone(),
                    apply_subst_v_app(vars.clone(), s2.clone(), cons_ht.clone()),
                );
                let rhs_cons = apply_subst_v_app(vars.clone(), comp_e.clone(), cons_ht.clone());
                let ih_ty = dist(&t);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());

                // c1 : lhs_cons = app_x   (applySubstV_append vars s1 X Y)
                let c1 = Expr::apps(
                    Expr::const_str(names::APPLYSUBSTV_APPEND),
                    [vars.clone(), s1.clone(), big_x.clone(), big_y.clone()],
                );
                // hd : s1_x = ite_comp   (compose head)
                let hd = Expr::apps(
                    Expr::const_str(names::APPLYSUBSTV_COMPOSE_HEAD),
                    [vars.clone(), s1.clone(), s2.clone(), h.clone()],
                );
                // c2 : app_x = app_ct   (congrArg (λa. append a s1_y) hd)
                let f_a = Expr::lam(
                    BinderInfo::Default,
                    ln.clone(),
                    append2(Expr::bvar(0), s1_y.clone()),
                );
                let c2 = congr_arg_list(s1_x.clone(), ite_comp.clone(), f_a, hd);
                // c3 : app_ct = app_cc   (congrArg (append ite_comp) ih).
                // app_cc ≡ rhs_cons def-eq: applySubstV comp (h::t) iota-reduces to
                // append (iteList c (comp h) [h]) (applySubstV comp t) = app_cc.
                let _ = &rhs_cons;
                let c3 = congr_arg_list(
                    s1_y.clone(),
                    comp_t.clone(),
                    append_fn(ite_comp.clone()),
                    ih,
                );
                let tail2 = eq_trans_list(app_x.clone(), app_ct, app_cc.clone(), c2, c3);
                let body = eq_trans_list(lhs_cons, app_x, app_cc.clone(), c1, tail2);

                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, e.clone());
            let r = b.mk_lam(e_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(s2_id, BinderInfo::Default, st.clone(), r);
            let r = b.mk_lam(s1_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPLYSUBSTV_COMPOSE),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// THE keystone: `∀ vars σ e, varsOf vars (applySubstV vars σ e)
    ///   = applySubstV vars (λv. varsOf vars (σ v)) (varsOf vars e)`.
    /// `List.rec` induction on `e`; the cons-case composes `varsOf_append` (LHS),
    /// `applySubstV_append` (RHS), the per-head convoy identity, and the IH via a
    /// congruent `append` chain. This is the lemma that lets a `$d`/dummy theorem's
    /// guard hypothesis discharge step obligations through `applySubst_compose` —
    /// i.e. the unlock for schematic reuse of predicate-logic theorems.
    fn register_varsof_applysubstv(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let single = |h: &Expr| list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
        let nil = list_nil(nat_ty());
        let phi = |vars: &Expr, s: &Expr| {
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                vars_of_app(vars.clone(), Expr::app(s.clone(), Expr::bvar(0))),
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                vars_of_app(
                    vars.clone(),
                    apply_subst_v_app(vars.clone(), s.clone(), e.clone()),
                ),
                apply_subst_v_app(
                    vars.clone(),
                    phi(&vars, &s),
                    vars_of_app(vars.clone(), e.clone()),
                ),
            );
            let t = b.mk_pi(e_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(s_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let phi_e = phi(&vars, &s);
            let dist = |w: &Expr| {
                eq_list_nat(
                    vars_of_app(
                        vars.clone(),
                        apply_subst_v_app(vars.clone(), s.clone(), w.clone()),
                    ),
                    apply_subst_v_app(
                        vars.clone(),
                        phi_e.clone(),
                        vars_of_app(vars.clone(), w.clone()),
                    ),
                )
            };
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), dist(&w)))
            };
            // nil: both sides reduce to [].
            let nil_case = eq_refl_list_nat(nil.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let cc = mem_nat_app(h.clone(), vars.clone());
                let sig_h = Expr::app(s.clone(), h.clone());
                let single_h = single(&h);
                // X = iteList c (σ h) [h] ;  Y = applySubstV vars σ t
                let big_x = ite_list_app(cc.clone(), sig_h.clone(), single_h.clone());
                let big_y = apply_subst_v_app(vars.clone(), s.clone(), t.clone());
                // U = iteList c [h] [] ;  V = varsOf vars t
                let big_u = ite_list_app(cc.clone(), single_h.clone(), nil.clone());
                let big_v = vars_of_app(vars.clone(), t.clone());
                let v_x = vars_of_app(vars.clone(), big_x.clone());
                let v_y = vars_of_app(vars.clone(), big_y.clone());
                let a_u = apply_subst_v_app(vars.clone(), phi_e.clone(), big_u.clone());
                let a_v = apply_subst_v_app(vars.clone(), phi_e.clone(), big_v.clone());
                let app_xy = append2(v_x.clone(), v_y.clone());
                let app_uy = append2(a_u.clone(), v_y.clone());
                let app_uv = append2(a_u.clone(), a_v.clone());
                let cons_ht = list_cons(nat_ty(), h.clone(), t.clone());
                let lhs_cons = vars_of_app(
                    vars.clone(),
                    apply_subst_v_app(vars.clone(), s.clone(), cons_ht.clone()),
                );
                let rhs_cons = apply_subst_v_app(
                    vars.clone(),
                    phi_e.clone(),
                    vars_of_app(vars.clone(), cons_ht.clone()),
                );
                let ih_ty = dist(&t);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());

                // c1 : lhs_cons = app_xy   (varsOf_append vars X Y)
                let c1 = Expr::apps(
                    Expr::const_str(names::VARSOF_APPEND),
                    [vars.clone(), big_x.clone(), big_y.clone()],
                );
                // hd : v_x = a_u   (head identity)
                let hd = Expr::apps(
                    Expr::const_str(names::VARSOF_APPLYSUBSTV_HEAD),
                    [vars.clone(), s.clone(), h.clone()],
                );
                // c2 : app_xy = app_uy   (congrArg (λa. append a v_y) hd)
                let f_a = Expr::lam(
                    BinderInfo::Default,
                    ln.clone(),
                    append2(Expr::bvar(0), v_y.clone()),
                );
                let c2 = congr_arg_list(v_x.clone(), a_u.clone(), f_a, hd);
                // c3 : app_uy = app_uv   (congrArg (append a_u) ih)
                let c3 = congr_arg_list(v_y.clone(), a_v.clone(), append_fn(a_u.clone()), ih);
                // c4 : applySubstV φ (append U V) = app_uv  (applySubstV_append vars φ U V)
                let c4 = Expr::apps(
                    Expr::const_str(names::APPLYSUBSTV_APPEND),
                    [vars.clone(), phi_e.clone(), big_u.clone(), big_v.clone()],
                );
                let asv_app_uv = apply_subst_v_app(
                    vars.clone(),
                    phi_e.clone(),
                    append2(big_u.clone(), big_v.clone()),
                );
                let c4sym = eq_symm_list(asv_app_uv.clone(), app_uv.clone(), c4);
                // chain: lhs_cons →(c1) app_xy →(c2) app_uy →(c3) app_uv →(c4sym) rhs_cons
                let tail3 =
                    eq_trans_list(app_uy.clone(), app_uv.clone(), rhs_cons.clone(), c3, c4sym);
                let tail2 = eq_trans_list(app_xy.clone(), app_uy, rhs_cons.clone(), c2, tail3);
                let body = eq_trans_list(lhs_cons, app_xy, rhs_cons, c1, tail2);

                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, e.clone());
            let r = b.mk_lam(e_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(s_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::VARSOF_APPLYSUBSTV),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// The per-head identity for the full `varsOf`-distribution lemma, proved by the
    /// CONVOY pattern: `aux : ∀ b, memNat h vars = b → goal[b]`, applied at the
    /// identity `Eq.refl (memNat h vars)`. The `Bool.rec` on `b` exposes the
    /// equation so each branch can rewrite the INNER `memNat h vars` (inside the
    /// singleton expansions) through it — dissolving the stuck-inner-`memNat`
    /// obstacle that blocks a naïve case split.
    fn register_head_identity(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let single = |h: &Expr| list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
        let nil = list_nil(nat_ty());
        // φ = λ v, varsOf vars (σ v)
        let phi = |vars: &Expr, s: &Expr| {
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                vars_of_app(vars.clone(), Expr::app(s.clone(), Expr::bvar(0))),
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (h_id, h) = b.fresh_local(nat_ty());
            let c = mem_nat_app(h.clone(), vars.clone());
            let lhs = vars_of_app(
                vars.clone(),
                ite_list_app(c.clone(), Expr::app(s.clone(), h.clone()), single(&h)),
            );
            let rhs = apply_subst_v_app(
                vars.clone(),
                phi(&vars, &s),
                ite_list_app(c.clone(), single(&h), nil.clone()),
            );
            let goal = eq_list_nat(lhs, rhs);
            let t = b.mk_pi(h_id, BinderInfo::Default, nat_ty(), goal);
            let t = b.mk_pi(s_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (h_id, h) = b.fresh_local(nat_ty());
            let c = mem_nat_app(h.clone(), vars.clone());
            let phi_e = phi(&vars, &s);
            let single_h = single(&h);
            let sig_h = Expr::app(s.clone(), h.clone());
            let phi_h = Expr::app(phi_e.clone(), h.clone());
            let vsig = vars_of_app(vars.clone(), sig_h.clone());

            // goal(b) used in the motive
            let goal_of = |bv: &Expr| {
                eq_list_nat(
                    vars_of_app(
                        vars.clone(),
                        ite_list_app(bv.clone(), sig_h.clone(), single_h.clone()),
                    ),
                    apply_subst_v_app(
                        vars.clone(),
                        phi_e.clone(),
                        ite_list_app(bv.clone(), single_h.clone(), nil.clone()),
                    ),
                )
            };
            // motive = λ b, (Eq Bool c b) → goal(b)
            let motive = {
                let mut mc = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = mc.fresh_local(bool_ty());
                let body = Expr::arrow(eq_bool_t(c.clone(), bb.clone()), goal_of(&bb));
                mc.finish_child(mc.mk_lam(bb_id, BinderInfo::Default, bool_ty(), body))
            };
            // true case: λ (eq : Eq Bool c true), Eq.symm … (Eq.trans sing rw)
            let true_case = {
                let mut tc = EnvDeclBuilder::child_of(&b);
                let (eq_id, eqv) = tc.fresh_local(eq_bool_t(c.clone(), btrue()));
                let sing = Expr::apps(
                    Expr::const_str(names::APPLYSUBSTV_SINGLETON),
                    [vars.clone(), phi_e.clone(), h.clone()],
                );
                let rw_fn = Expr::lam(
                    BinderInfo::Default,
                    bool_ty(),
                    ite_list_app(Expr::bvar(0), phi_h.clone(), single_h.clone()),
                );
                let rw = congr_arg_bool_list(c.clone(), btrue(), rw_fn, eqv.clone());
                let asv = apply_subst_v_app(vars.clone(), phi_e.clone(), single_h.clone());
                let ite_c = ite_list_app(c.clone(), phi_h.clone(), single_h.clone());
                let ite_true = ite_list_app(btrue(), phi_h.clone(), single_h.clone());
                let trans = eq_trans_list(asv.clone(), ite_c, ite_true, sing, rw);
                let body = eq_symm_list(asv, vsig.clone(), trans);
                tc.finish_child(tc.mk_lam(
                    eq_id,
                    BinderInfo::Default,
                    eq_bool_t(c.clone(), btrue()),
                    body,
                ))
            };
            // false case: λ (eq : Eq Bool c false), Eq.trans sing_f rw_f
            let false_case = {
                let mut fc = EnvDeclBuilder::child_of(&b);
                let (eq_id, eqv) = fc.fresh_local(eq_bool_t(c.clone(), bfalse()));
                let sing_f = Expr::apps(
                    Expr::const_str(names::VARSOF_SINGLETON),
                    [vars.clone(), h.clone()],
                );
                let rw_fn = Expr::lam(
                    BinderInfo::Default,
                    bool_ty(),
                    ite_list_app(Expr::bvar(0), single_h.clone(), nil.clone()),
                );
                let rw = congr_arg_bool_list(c.clone(), bfalse(), rw_fn, eqv.clone());
                let vsingle = vars_of_app(vars.clone(), single_h.clone());
                let ite_c = ite_list_app(c.clone(), single_h.clone(), nil.clone());
                let ite_false = ite_list_app(bfalse(), single_h.clone(), nil.clone());
                let body = eq_trans_list(vsingle, ite_c, ite_false, sing_f, rw);
                fc.finish_child(fc.mk_lam(
                    eq_id,
                    BinderInfo::Default,
                    eq_bool_t(c.clone(), bfalse()),
                    body,
                ))
            };
            // Bool.rec.{0} motive false_case true_case c (Eq.refl Bool c)
            let recur = Expr::apps(
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                [
                    motive,
                    false_case,
                    true_case,
                    c.clone(),
                    eq_refl_bool_e(c.clone()),
                ],
            );
            let r = b.mk_lam(h_id, BinderInfo::Default, nat_ty(), recur);
            let r = b.mk_lam(s_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::VARSOF_APPLYSUBSTV_HEAD),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// The `varsOf`/`applySubstV` SINGLETON lemmas. `varsOf vars [h]` reduces (iota)
    /// to `append (iteList (memNat h vars) [h] []) (varsOf vars [])` and
    /// `varsOf vars [] = []`, so it is DEF-EQ to `append X []`; thus
    /// `append_nil_right X : Eq (append X []) X` already has the goal type (the
    /// kernel reduces the LHS). Same for `applySubstV vars σ [h]`. No induction.
    fn register_singletons(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let nil = || list_nil(nat_ty());
        let single = |h: &Expr| list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
        let anr = |x: Expr| Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), x);
        // varsOf_singleton : ∀ vars h, varsOf vars [h] = iteList (memNat h vars) [h] []
        {
            let mk_ty = |b: &mut EnvDeclBuilder| {
                let (vars_id, vars) = b.fresh_local(ln.clone());
                let (h_id, h) = b.fresh_local(nat_ty());
                let x = ite_list_app(mem_nat_app(h.clone(), vars.clone()), single(&h), nil());
                let goal = eq_list_nat(vars_of_app(vars.clone(), single(&h)), x);
                (vars_id, h_id, goal)
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, h_id, goal) = mk_ty(&mut b);
                let t = b.mk_pi(h_id, BinderInfo::Default, nat_ty(), goal);
                b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, vars) = b.fresh_local(ln.clone());
                let (h_id, h) = b.fresh_local(nat_ty());
                let x = ite_list_app(mem_nat_app(h.clone(), vars.clone()), single(&h), nil());
                let body = anr(x);
                let r = b.mk_lam(h_id, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(names::VARSOF_SINGLETON),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        // applySubstV_singleton : ∀ vars σ h, applySubstV vars σ [h] = iteList (memNat h vars) (σ h) [h]
        {
            let st = subst_ty();
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, vars) = b.fresh_local(ln.clone());
                let (s_id, s) = b.fresh_local(st.clone());
                let (h_id, h) = b.fresh_local(nat_ty());
                let x = ite_list_app(
                    mem_nat_app(h.clone(), vars.clone()),
                    Expr::app(s.clone(), h.clone()),
                    single(&h),
                );
                let goal = eq_list_nat(apply_subst_v_app(vars.clone(), s.clone(), single(&h)), x);
                let t = b.mk_pi(h_id, BinderInfo::Default, nat_ty(), goal);
                let t = b.mk_pi(s_id, BinderInfo::Default, st.clone(), t);
                b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, vars) = b.fresh_local(ln.clone());
                let (s_id, s) = b.fresh_local(st.clone());
                let (h_id, h) = b.fresh_local(nat_ty());
                let x = ite_list_app(
                    mem_nat_app(h.clone(), vars.clone()),
                    Expr::app(s.clone(), h.clone()),
                    single(&h),
                );
                let body = anr(x);
                let r = b.mk_lam(h_id, BinderInfo::Default, nat_ty(), body);
                let r = b.mk_lam(s_id, BinderInfo::Default, st.clone(), r);
                b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
            };
            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(names::APPLYSUBSTV_SINGLETON),
                level_params: vec![],
                type_: ty,
                value: val,
            })?;
        }
        Ok(())
    }

    /// `∀ xs, append xs [] = xs` — proved by `List.rec` induction (nil → refl;
    /// cons h t ih → congrArg (List.cons h) ih). A foundational step toward the
    /// `varsOf`/`applySubstV` SINGLETON lemmas (`f vars [h] = iteList (memNat h
    /// vars) … []`) that close the head-case of the full distribution lemma.
    fn register_append_nil_right(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let nil = list_nil(nat_ty());
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(append2(xs.clone(), nil.clone()), xs.clone());
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), goal))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(append2(w.clone(), nil.clone()), w.clone());
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            // nil: append [] [] = [] reduces to [], so Eq.refl [].
            let nil_case = eq_refl_list_nat(nil.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let ih_ty = eq_list_nat(append2(t.clone(), nil.clone()), t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // f = List.cons.{0} Nat h : List Nat → List Nat
                let cons_h = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [nat_ty(), h.clone()],
                );
                // congrArg (cons h) ih : Eq (h :: append t []) (h :: t)
                let body = congr_arg_list(append2(t.clone(), nil.clone()), t.clone(), cons_h, ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), rec))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPEND_NIL_RIGHT),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `applySubstV vars σ e := List.rec [] (fun h _ ih => append (iteList (memNat
    /// h vars) (σ h) [h]) ih) e` — substitutes a symbol only if it is a variable.
    fn register_apply_subst_v(&mut self) -> Result<(), EnvError> {
        let st = subst_ty();
        let ty = Expr::arrow(
            list_nat(),
            Expr::arrow(st.clone(), Expr::arrow(list_nat(), list_nat())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(list_nat());
            let (sig_id, sig) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(list_nat());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, _t) = c.fresh_local(list_nat());
                let (ih_id, ih) = c.fresh_local(list_nat());
                let single_h = list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
                let chosen = ite_list_app(
                    mem_nat_app(h.clone(), vars.clone()),
                    Expr::app(sig.clone(), h.clone()),
                    single_h,
                );
                let body = append2(chosen, ih.clone());
                let rr = c.mk_lam(ih_id, BinderInfo::Default, list_nat(), body);
                let rr = c.mk_lam(t_id, BinderInfo::Default, list_nat(), rr);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), rr))
            };
            let rec = list_rec(
                nat_ty(),
                list_nat(),
                list_nil(nat_ty()),
                cons_case,
                e.clone(),
            );
            let r = b.mk_lam(e_id, BinderInfo::Default, list_nat(), rec);
            let r = b.mk_lam(sig_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, list_nat(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::APPLY_SUBST_V),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `∀ vars xs ys, varsOf vars (append xs ys) = append (varsOf vars xs) (varsOf vars ys)`.
    fn register_varsof_append(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                vars_of_app(vars.clone(), append2(xs.clone(), ys.clone())),
                append2(
                    vars_of_app(vars.clone(), xs.clone()),
                    vars_of_app(vars.clone(), ys.clone()),
                ),
            );
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(
                    vars_of_app(vars.clone(), append2(w.clone(), ys.clone())),
                    append2(
                        vars_of_app(vars.clone(), w.clone()),
                        vars_of_app(vars.clone(), ys.clone()),
                    ),
                );
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            let nil_case = eq_refl_list_nat(vars_of_app(vars.clone(), ys.clone()));
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let single_h = list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
                let gh = ite_list_app(
                    mem_nat_app(h.clone(), vars.clone()),
                    single_h,
                    list_nil(nat_ty()),
                );
                let vo_t = vars_of_app(vars.clone(), t.clone());
                let vo_ys = vars_of_app(vars.clone(), ys.clone());
                let vo_append_t_ys = vars_of_app(vars.clone(), append2(t.clone(), ys.clone()));
                let ih_ty =
                    eq_list_nat(vo_append_t_ys.clone(), append2(vo_t.clone(), vo_ys.clone()));
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let term_a = append2(gh.clone(), vo_append_t_ys.clone());
                let term_b = append2(gh.clone(), append2(vo_t.clone(), vo_ys.clone()));
                let term_c = append2(append2(gh.clone(), vo_t.clone()), vo_ys.clone());
                let h1 = congr_arg_list(
                    vo_append_t_ys,
                    append2(vo_t.clone(), vo_ys.clone()),
                    append_fn(gh.clone()),
                    ih,
                );
                let h2 = eq_symm_list(
                    term_c.clone(),
                    term_b.clone(),
                    append_assoc_app(gh, vo_t, vo_ys),
                );
                let body = eq_trans_list(term_a, term_b, term_c, h1, h2);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::VARSOF_APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ vars σ xs ys, applySubstV vars σ (append xs ys)
    ///   = append (applySubstV vars σ xs) (applySubstV vars σ ys)`.
    fn register_applysubstv_append(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                apply_subst_v_app(vars.clone(), s.clone(), append2(xs.clone(), ys.clone())),
                append2(
                    apply_subst_v_app(vars.clone(), s.clone(), xs.clone()),
                    apply_subst_v_app(vars.clone(), s.clone(), ys.clone()),
                ),
            );
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t);
            let t = b.mk_pi(s_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(vars_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (vars_id, vars) = b.fresh_local(ln.clone());
            let (s_id, s) = b.fresh_local(st.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(
                    apply_subst_v_app(vars.clone(), s.clone(), append2(w.clone(), ys.clone())),
                    append2(
                        apply_subst_v_app(vars.clone(), s.clone(), w.clone()),
                        apply_subst_v_app(vars.clone(), s.clone(), ys.clone()),
                    ),
                );
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            let nil_case = eq_refl_list_nat(apply_subst_v_app(vars.clone(), s.clone(), ys.clone()));
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let single_h = list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
                let gh = ite_list_app(
                    mem_nat_app(h.clone(), vars.clone()),
                    Expr::app(s.clone(), h.clone()),
                    single_h,
                );
                let sub_t = apply_subst_v_app(vars.clone(), s.clone(), t.clone());
                let sub_ys = apply_subst_v_app(vars.clone(), s.clone(), ys.clone());
                let sub_append_t_ys =
                    apply_subst_v_app(vars.clone(), s.clone(), append2(t.clone(), ys.clone()));
                let ih_ty = eq_list_nat(
                    sub_append_t_ys.clone(),
                    append2(sub_t.clone(), sub_ys.clone()),
                );
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let term_a = append2(gh.clone(), sub_append_t_ys.clone());
                let term_b = append2(gh.clone(), append2(sub_t.clone(), sub_ys.clone()));
                let term_c = append2(append2(gh.clone(), sub_t.clone()), sub_ys.clone());
                let h1 = congr_arg_list(
                    sub_append_t_ys,
                    append2(sub_t.clone(), sub_ys.clone()),
                    append_fn(gh.clone()),
                    ih,
                );
                let h2 = eq_symm_list(
                    term_c.clone(),
                    term_b.clone(),
                    append_assoc_app(gh, sub_t, sub_ys),
                );
                let body = eq_trans_list(term_a, term_b, term_c, h1, h2);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r);
            let r = b.mk_lam(s_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(vars_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPLYSUBSTV_APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// Register the disjoint-variable (`$d`) soundness predicates (M12):
    /// `memNat`, `listDisjoint`, `varsOf`, `disjPair` — all reducible `Definition`s
    /// built from `List.rec`/`Bool`/`Nat.beq` (no new axioms). The kernel reduces
    /// `disjPair vars σ x y` on ground data to `Bool.true`/`Bool.false`, so a
    /// `$d`-violating instance makes a guard `Eq Bool (disjPair …) Bool.true`
    /// uninhabitable and `add_decl` rejects it.
    fn register_dv_predicates(&mut self) -> Result<(), EnvError> {
        // memNat n xs := List.rec false (fun h _ ih => Bool.or (Nat.beq n h) ih) xs
        {
            let ty = Expr::arrow(nat_ty(), Expr::arrow(list_nat(), bool_ty()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_ty());
                let (xs_id, xs) = b.fresh_local(list_nat());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(nat_ty());
                    let (t_id, _t) = c.fresh_local(list_nat());
                    let (ih_id, ih) = c.fresh_local(bool_ty());
                    let body = bor(nat_beq(n.clone(), h.clone()), ih.clone());
                    let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_nat(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
                };
                let rec = list_rec(nat_ty(), bool_ty(), bfalse(), cons_case, xs.clone());
                let inner = b.mk_lam(xs_id, BinderInfo::Default, list_nat(), rec);
                b.finish(b.mk_lam(n_id, BinderInfo::Default, nat_ty(), inner))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::MEM_NAT),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        // isVar K n := Bool.and (Nat.ble 1 n) (Nat.blt n K)  — O(1) range-coded
        // membership "1 ≤ n < K". Variable codes occupy [1,K) (the interner starts
        // at 1, so 0 is never a code and every constant/typecode is ≥ K), so this is
        // equivalent to `memNat n var_universe` under the kernel-checked
        // `mm.__vu_contig` bridge. The lower bound is needed so the bridge holds for
        // ALL n (incl. 0), not just real codes. Both Nat.ble/Nat.blt reduce natively.
        {
            let ty = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), bool_ty()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (k_id, k) = b.fresh_local(nat_ty());
                let (n_id, n) = b.fresh_local(nat_ty());
                let body = band(
                    nat_ble(Expr::nat_lit(1), n.clone()),
                    nat_blt(n.clone(), k.clone()),
                );
                let inner = b.mk_lam(n_id, BinderInfo::Default, nat_ty(), body);
                b.finish(b.mk_lam(k_id, BinderInfo::Default, nat_ty(), inner))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::IS_VAR),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        // listDisjoint xs ys := List.rec true (fun h _ ih => Bool.and (Bool.not (memNat h ys)) ih) xs
        {
            let ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), bool_ty()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (xs_id, xs) = b.fresh_local(list_nat());
                let (ys_id, ys) = b.fresh_local(list_nat());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(nat_ty());
                    let (t_id, _t) = c.fresh_local(list_nat());
                    let (ih_id, ih) = c.fresh_local(bool_ty());
                    let body = band(bnot(mem_nat_app(h.clone(), ys.clone())), ih.clone());
                    let r = c.mk_lam(ih_id, BinderInfo::Default, bool_ty(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_nat(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
                };
                let rec = list_rec(nat_ty(), bool_ty(), btrue(), cons_case, xs.clone());
                let inner = b.mk_lam(ys_id, BinderInfo::Default, list_nat(), rec);
                b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_nat(), inner))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::LIST_DISJOINT),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        // varsOf vars e := List.rec [] (fun h _ ih => append (iteList (memNat h vars) [h] []) ih) e
        {
            let ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat()));
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, vars) = b.fresh_local(list_nat());
                let (e_id, e) = b.fresh_local(list_nat());
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(nat_ty());
                    let (t_id, _t) = c.fresh_local(list_nat());
                    let (ih_id, ih) = c.fresh_local(list_nat());
                    let keep = ite_list_app(
                        mem_nat_app(h.clone(), vars.clone()),
                        list_cons(nat_ty(), h.clone(), list_nil(nat_ty())),
                        list_nil(nat_ty()),
                    );
                    let body = append2(keep, ih.clone());
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_nat(), body);
                    let r = c.mk_lam(t_id, BinderInfo::Default, list_nat(), r);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
                };
                let rec = list_rec(
                    nat_ty(),
                    list_nat(),
                    list_nil(nat_ty()),
                    cons_case,
                    e.clone(),
                );
                let inner = b.mk_lam(e_id, BinderInfo::Default, list_nat(), rec);
                b.finish(b.mk_lam(vars_id, BinderInfo::Default, list_nat(), inner))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::VARS_OF),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        // disjPair vars s x y := listDisjoint (varsOf vars (s x)) (varsOf vars (s y))
        {
            let ty = Expr::arrow(
                list_nat(),
                Expr::arrow(
                    subst_ty(),
                    Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), bool_ty())),
                ),
            );
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (vars_id, vars) = b.fresh_local(list_nat());
                let (s_id, s) = b.fresh_local(subst_ty());
                let (x_id, x) = b.fresh_local(nat_ty());
                let (y_id, y) = b.fresh_local(nat_ty());
                let vx = vars_of_app(vars.clone(), Expr::app(s.clone(), x.clone()));
                let vy = vars_of_app(vars.clone(), Expr::app(s.clone(), y.clone()));
                let body = list_disjoint_app(vx, vy);
                let r = b.mk_lam(y_id, BinderInfo::Default, nat_ty(), body);
                let r = b.mk_lam(x_id, BinderInfo::Default, nat_ty(), r);
                let r = b.mk_lam(s_id, BinderInfo::Default, subst_ty(), r);
                b.finish(b.mk_lam(vars_id, BinderInfo::Default, list_nat(), r))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(names::DISJ_PAIR),
                level_params: vec![],
                type_: ty,
                value: val,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── append ────────────────────────────────────────────────────────────────

    /// `append xs ys := List.rec ys (fun h _ ih => List.cons h ih) xs`.
    fn register_append(&mut self) -> Result<(), EnvError> {
        let ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_nat());
            let (ys_id, ys) = b.fresh_local(list_nat());
            // cons_case : fun (h : Nat) (t : List Nat) (ih : List Nat) => List.cons h ih
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, _t) = c.fresh_local(list_nat());
                let (ih_id, ih) = c.fresh_local(list_nat());
                let body = list_cons(nat_ty(), h.clone(), ih.clone());
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_nat(), body);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_nat(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec(nat_ty(), list_nat(), ys.clone(), cons_case, xs.clone());
            let inner = b.mk_lam(ys_id, BinderInfo::Default, list_nat(), rec);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_nat(), inner))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── iteList ─────────────────────────────────────────────────────────────────

    /// `iteList c thenL elseL := Bool.rec (motive := fun _ => List Nat) elseL thenL c`.
    fn register_ite_list(&mut self) -> Result<(), EnvError> {
        let ty = Expr::arrow(
            bool_ty(),
            Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(bool_ty());
            let (then_id, then_l) = b.fresh_local(list_nat());
            let (else_id, else_l) = b.fresh_local(list_nat());
            // Bool.rec.{1} (motive := fun _ : Bool => List Nat) elseL thenL c
            // (Bool constructor order is false, true, so the false-case comes first.)
            let motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
            let bool_rec = Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            );
            let body = Expr::apps(
                bool_rec,
                [motive, else_l.clone(), then_l.clone(), c.clone()],
            );
            let r = b.mk_lam(else_id, BinderInfo::Default, list_nat(), body);
            let r = b.mk_lam(then_id, BinderInfo::Default, list_nat(), r);
            b.finish(b.mk_lam(c_id, BinderInfo::Default, bool_ty(), r))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::ITE_LIST),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── subst1 ──────────────────────────────────────────────────────────────────

    /// `subst1 v r e` replaces every occurrence of variable symbol `v` in `e`
    /// with the expression `r`:
    /// `List.rec [] (fun h _ ih => append (iteList (Nat.beq h v) r [h]) ih) e`.
    fn register_subst1(&mut self) -> Result<(), EnvError> {
        let ty = Expr::arrow(
            nat_ty(),
            Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(nat_ty());
            let (r_id, r) = b.fresh_local(list_nat());
            let (e_id, e) = b.fresh_local(list_nat());
            // cons_case : fun (h : Nat) (t : List Nat) (ih : List Nat) =>
            //   append (iteList (Nat.beq h v) r [h]) ih
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, _t) = c.fresh_local(list_nat());
                let (ih_id, ih) = c.fresh_local(list_nat());
                let single_h = list_cons(nat_ty(), h.clone(), list_nil(nat_ty()));
                let cond = nat_beq(h.clone(), v.clone());
                let chosen = Expr::apps(
                    Expr::const_str(names::ITE_LIST),
                    [cond, r.clone(), single_h],
                );
                let body = Expr::apps(Expr::const_str(names::APPEND), [chosen, ih.clone()]);
                let rr = c.mk_lam(ih_id, BinderInfo::Default, list_nat(), body);
                let rr = c.mk_lam(t_id, BinderInfo::Default, list_nat(), rr);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), rr))
            };
            let rec = list_rec(
                nat_ty(),
                list_nat(),
                list_nil(nat_ty()),
                cons_case,
                e.clone(),
            );
            let r3 = b.mk_lam(e_id, BinderInfo::Default, list_nat(), rec);
            let r2 = b.mk_lam(r_id, BinderInfo::Default, list_nat(), r3);
            b.finish(b.mk_lam(v_id, BinderInfo::Default, nat_ty(), r2))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::SUBST1),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── applySubst ──────────────────────────────────────────────────────────────

    /// `applySubst σ e` applies a SIMULTANEOUS substitution `σ : Nat → List Nat`
    /// to `e`, mapping each symbol independently and concatenating:
    /// `List.rec [] (fun h _ ih => append (σ h) ih) e`.
    ///
    /// This is the genuine Metamath proof-step substitution. The substitution
    /// map for one step is supplied by the caller as a concrete `Nat → List Nat`
    /// lambda (a nested `iteList` over the assertion's mandatory variables — see
    /// [`subst_fn`]); `σ s = [s]` for any non-variable symbol. Because every
    /// symbol is mapped from the SAME `σ`, distinct variables are replaced
    /// simultaneously (sequential `subst1` would not be sound when one
    /// replacement mentions another substituted variable).
    fn register_apply_subst(&mut self) -> Result<(), EnvError> {
        let subst_fn_ty = Expr::arrow(nat_ty(), list_nat());
        let ty = Expr::arrow(subst_fn_ty.clone(), Expr::arrow(list_nat(), list_nat()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (sig_id, sig) = b.fresh_local(subst_fn_ty.clone());
            let (e_id, e) = b.fresh_local(list_nat());
            // cons_case : fun (h : Nat) (t : List Nat) (ih : List Nat) =>
            //   append (σ h) ih
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, _t) = c.fresh_local(list_nat());
                let (ih_id, ih) = c.fresh_local(list_nat());
                let mapped = Expr::app(sig.clone(), h.clone());
                let body = Expr::apps(Expr::const_str(names::APPEND), [mapped, ih.clone()]);
                let rr = c.mk_lam(ih_id, BinderInfo::Default, list_nat(), body);
                let rr = c.mk_lam(t_id, BinderInfo::Default, list_nat(), rr);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), rr))
            };
            let rec = list_rec(
                nat_ty(),
                list_nat(),
                list_nil(nat_ty()),
                cons_case,
                e.clone(),
            );
            let inner = b.mk_lam(e_id, BinderInfo::Default, list_nat(), rec);
            b.finish(b.mk_lam(sig_id, BinderInfo::Default, subst_fn_ty, inner))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::APPLY_SUBST),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── listBeq ─────────────────────────────────────────────────────────────────

    /// `listBeq xs ys` — structural equality of two `List Nat`.
    ///
    /// Built as an outer `List.rec` on `xs` whose motive is `List Nat → Bool`:
    /// the nil case tests `ys` for emptiness; the cons case pops a head off `ys`
    /// (inner `List.rec`) and `&&`s `Nat.beq` of the heads with the recursive
    /// comparison of the tails.
    fn register_list_beq(&mut self) -> Result<(), EnvError> {
        let ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), bool_ty()));
        // Result of the outer recursion is the function type `List Nat → Bool`.
        let res_ty = Expr::arrow(list_nat(), bool_ty());
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(list_nat());

            // nil_case : fun (ys : List Nat) =>
            //   List.rec true (fun _ _ _ => false) ys      -- i.e. ys.isEmpty
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ys_id, ys) = c.fresh_local(list_nat());
                let inner_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h2_id, _h2) = d.fresh_local(nat_ty());
                    let (t2_id, _t2) = d.fresh_local(list_nat());
                    let (ih2_id, _ih2) = d.fresh_local(bool_ty());
                    let r = d.mk_lam(ih2_id, BinderInfo::Default, bool_ty(), bfalse());
                    let r = d.mk_lam(t2_id, BinderInfo::Default, list_nat(), r);
                    d.finish_child(d.mk_lam(h2_id, BinderInfo::Default, nat_ty(), r))
                };
                let is_empty = list_rec(nat_ty(), bool_ty(), btrue(), inner_cons, ys.clone());
                c.finish_child(c.mk_lam(ys_id, BinderInfo::Default, list_nat(), is_empty))
            };

            // cons_case : fun (h : Nat) (t : List Nat) (ih : List Nat → Bool) =>
            //   fun (ys : List Nat) =>
            //     List.rec false (fun h2 t2 _ => Bool.and (Nat.beq h h2) (ih t2)) ys
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, _t) = c.fresh_local(list_nat());
                let (ih_id, ih) = c.fresh_local(res_ty.clone());
                let (ys_id, ys) = c.fresh_local(list_nat());
                let inner_cons = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (h2_id, h2) = d.fresh_local(nat_ty());
                    let (t2_id, t2) = d.fresh_local(list_nat());
                    let (ih2_id, _ih2) = d.fresh_local(bool_ty());
                    let heads_eq = nat_beq(h.clone(), h2.clone());
                    let tails_eq = Expr::app(ih.clone(), t2.clone());
                    let body = band(heads_eq, tails_eq);
                    let r = d.mk_lam(ih2_id, BinderInfo::Default, bool_ty(), body);
                    let r = d.mk_lam(t2_id, BinderInfo::Default, list_nat(), r);
                    d.finish_child(d.mk_lam(h2_id, BinderInfo::Default, nat_ty(), r))
                };
                let cmp = list_rec(nat_ty(), bool_ty(), bfalse(), inner_cons, ys.clone());
                let body = c.mk_lam(ys_id, BinderInfo::Default, list_nat(), cmp);
                let r = c.mk_lam(ih_id, BinderInfo::Default, res_ty.clone(), body);
                let r = c.mk_lam(t_id, BinderInfo::Default, list_nat(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };

            // outer: fun xs => (List.rec nil_case cons_case xs)  -- yields List Nat → Bool
            let rec = list_rec(nat_ty(), res_ty.clone(), nil_case, cons_case, xs.clone());
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, list_nat(), rec))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIST_BEQ),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── inductive lemmas (the substitution-composition chain) ───────────────────

    /// Register `append_assoc`, `applySubst_append`, `applySubst_compose` — the
    /// chain that justifies substitution composition (needed for schematic lemma
    /// reuse). Each is a `Theorem` proved by `List.rec` induction; registering
    /// them runs the kernel type-checker, so a broken proof fails init.
    fn register_subst_lemmas(&mut self) -> Result<(), EnvError> {
        self.register_append_assoc()?;
        self.register_applysubst_append()?;
        self.register_applysubst_compose()?;
        Ok(())
    }

    /// `∀ xs ys zs, append (append xs ys) zs = append xs (append ys zs)`.
    fn register_append_assoc(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                append2(append2(xs.clone(), ys.clone()), zs.clone()),
                append2(xs.clone(), append2(ys.clone(), zs.clone())),
            );
            let t = b.mk_pi(zs_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let (zs_id, zs) = b.fresh_local(ln.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(
                    append2(append2(w.clone(), ys.clone()), zs.clone()),
                    append2(w.clone(), append2(ys.clone(), zs.clone())),
                );
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            let nil_case = eq_refl_list_nat(append2(ys.clone(), zs.clone()));
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let a1 = append2(append2(t.clone(), ys.clone()), zs.clone());
                let a2 = append2(t.clone(), append2(ys.clone(), zs.clone()));
                let ih_ty = eq_list_nat(a1.clone(), a2.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let body = congr_arg_list(a1, a2, cons_h_fn(h.clone()), ih);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(zs_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPEND_ASSOC),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ σ xs ys, applySubst σ (append xs ys) = append (applySubst σ xs) (applySubst σ ys)`.
    fn register_applysubst_append(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(st.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                applysubst2(s.clone(), append2(xs.clone(), ys.clone())),
                append2(
                    applysubst2(s.clone(), xs.clone()),
                    applysubst2(s.clone(), ys.clone()),
                ),
            );
            let t = b.mk_pi(ys_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(xs_id, BinderInfo::Default, ln.clone(), t);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, st.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(st.clone());
            let (xs_id, xs) = b.fresh_local(ln.clone());
            let (ys_id, ys) = b.fresh_local(ln.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(
                    applysubst2(s.clone(), append2(w.clone(), ys.clone())),
                    append2(
                        applysubst2(s.clone(), w.clone()),
                        applysubst2(s.clone(), ys.clone()),
                    ),
                );
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            let nil_case = eq_refl_list_nat(applysubst2(s.clone(), ys.clone()));
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let sh = Expr::app(s.clone(), h.clone()); // σ h
                let sub_t = applysubst2(s.clone(), t.clone()); // applySubst σ t
                let sub_ys = applysubst2(s.clone(), ys.clone()); // applySubst σ ys
                let sub_append_t_ys = applysubst2(s.clone(), append2(t.clone(), ys.clone()));
                let ih_ty = eq_list_nat(
                    sub_append_t_ys.clone(),
                    append2(sub_t.clone(), sub_ys.clone()),
                );
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // A = append (σ h) (applySubst σ (append t ys))
                let term_a = append2(sh.clone(), sub_append_t_ys);
                // Bm = append (σ h) (append (applySubst σ t) (applySubst σ ys))
                let term_b = append2(sh.clone(), append2(sub_t.clone(), sub_ys.clone()));
                // C = append (append (σ h) (applySubst σ t)) (applySubst σ ys)
                let term_c = append2(append2(sh.clone(), sub_t.clone()), sub_ys.clone());
                // h1 : Eq A Bm  = congrArg (append (σ h)) ih
                let h1 = congr_arg_list(
                    applysubst2(s.clone(), append2(t.clone(), ys.clone())),
                    append2(sub_t.clone(), sub_ys.clone()),
                    append_fn(sh.clone()),
                    ih,
                );
                // h2 : Eq Bm C = Eq.symm (append_assoc (σ h) (applySubst σ t) (applySubst σ ys))
                let h2 = eq_symm_list(
                    term_c.clone(),
                    term_b.clone(),
                    append_assoc_app(sh, sub_t, sub_ys),
                );
                let body = eq_trans_list(term_a, term_b, term_c, h1, h2);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, xs.clone());
            let r = b.mk_lam(ys_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(xs_id, BinderInfo::Default, ln.clone(), r);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, st.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPLYSUBST_APPEND),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }

    /// `∀ σ1 σ2 e, applySubst σ1 (applySubst σ2 e)
    ///            = applySubst (fun s => applySubst σ1 (σ2 s)) e`.
    fn register_applysubst_compose(&mut self) -> Result<(), EnvError> {
        let ln = list_nat();
        let st = subst_ty();
        // comp σ1 σ2 = fun (s : Nat) => applySubst σ1 (σ2 s).
        // Built with an explicit `bvar(0)` for the bound `s` (no nested
        // EnvDeclBuilder, which would collide FVar ids with the outer builder);
        // `s1`/`s2` are FVars that the outer builder abstracts later.
        let comp = |s1: &Expr, s2: &Expr| -> Expr {
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                applysubst2(s1.clone(), Expr::app(s2.clone(), Expr::bvar(0))),
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let goal = eq_list_nat(
                applysubst2(s1.clone(), applysubst2(s2.clone(), e.clone())),
                applysubst2(comp(&s1, &s2), e.clone()),
            );
            let t = b.mk_pi(e_id, BinderInfo::Default, ln.clone(), goal);
            let t = b.mk_pi(s2_id, BinderInfo::Default, st.clone(), t);
            b.finish(b.mk_pi(s1_id, BinderInfo::Default, st.clone(), t))
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (s1_id, s1) = b.fresh_local(st.clone());
            let (s2_id, s2) = b.fresh_local(st.clone());
            let (e_id, e) = b.fresh_local(ln.clone());
            let cmp = comp(&s1, &s2);
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(ln.clone());
                let body = eq_list_nat(
                    applysubst2(s1.clone(), applysubst2(s2.clone(), w.clone())),
                    applysubst2(cmp.clone(), w.clone()),
                );
                c.finish_child(c.mk_lam(w_id, BinderInfo::Default, ln.clone(), body))
            };
            let nil_case = eq_refl_list_nat(list_nil(nat_ty()));
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat_ty());
                let (t_id, t) = c.fresh_local(ln.clone());
                let s2h = Expr::app(s2.clone(), h.clone()); // σ2 h
                let sub2_t = applysubst2(s2.clone(), t.clone()); // applySubst σ2 t
                let s1_s2h = applysubst2(s1.clone(), s2h.clone()); // applySubst σ1 (σ2 h)
                let s1_sub2_t = applysubst2(s1.clone(), sub2_t.clone()); // applySubst σ1 (applySubst σ2 t)
                let comp_t = applysubst2(cmp.clone(), t.clone()); // applySubst comp t
                let ih_ty = eq_list_nat(s1_sub2_t.clone(), comp_t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // A = applySubst σ1 (append (σ2 h) (applySubst σ2 t))
                let term_a = applysubst2(s1.clone(), append2(s2h.clone(), sub2_t.clone()));
                // Bm = append (applySubst σ1 (σ2 h)) (applySubst σ1 (applySubst σ2 t))
                let term_b = append2(s1_s2h.clone(), s1_sub2_t.clone());
                // C = append (applySubst σ1 (σ2 h)) (applySubst comp t)
                let term_c = append2(s1_s2h.clone(), comp_t.clone());
                // h1 : Eq A Bm = applySubst_append σ1 (σ2 h) (applySubst σ2 t)
                let h1 = applysubst_append_app(s1.clone(), s2h.clone(), sub2_t.clone());
                // h2 : Eq Bm C = congrArg (append (applySubst σ1 (σ2 h))) ih
                let h2 = congr_arg_list(s1_sub2_t, comp_t, append_fn(s1_s2h), ih);
                let body = eq_trans_list(term_a, term_b, term_c, h1, h2);
                let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let r = c.mk_lam(t_id, BinderInfo::Default, ln.clone(), r);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat_ty(), r))
            };
            let rec = list_rec_prop(motive, nil_case, cons_case, e.clone());
            let r = b.mk_lam(e_id, BinderInfo::Default, ln.clone(), rec);
            let r = b.mk_lam(s2_id, BinderInfo::Default, st.clone(), r);
            b.finish(b.mk_lam(s1_id, BinderInfo::Default, st.clone(), r))
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string(names::APPLYSUBST_COMPOSE),
            level_params: vec![],
            type_: ty,
            value: val,
        })
    }
}

// ── public encode helpers (used by tests and the importer) ──────────────────────

/// `@Eq.{1} (List Nat) x y`.
pub fn eq_list_nat(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_nat(), x, y],
    )
}

/// `@Eq.refl.{1} (List Nat) v`.
pub fn eq_refl_list_nat(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [list_nat(), v],
    )
}

/// `Clean.MM.subst1 v r e` applied to literal data.
pub fn subst1_app(v: u64, r: &[u64], e: &[u64]) -> Expr {
    Expr::apps(
        Expr::const_str(names::SUBST1),
        [Expr::nat_lit(v), nat_list_lit(r), nat_list_lit(e)],
    )
}

/// `Clean.MM.listBeq xs ys` applied to literal data.
pub fn list_beq_app(xs: &[u64], ys: &[u64]) -> Expr {
    Expr::apps(
        Expr::const_str(names::LIST_BEQ),
        [nat_list_lit(xs), nat_list_lit(ys)],
    )
}

/// Build a concrete simultaneous-substitution map `σ : Nat → List Nat` for the
/// given variable→replacement `bindings`, as the lambda
/// `fun s => iteList (Nat.beq s v0) r0 (iteList (Nat.beq s v1) r1 … [s])`.
///
/// A symbol not bound by any pair maps to the singleton `[s]` (identity). This
/// is exactly one Metamath proof step's substitution; feed it to
/// [`apply_subst_app`].
pub fn subst_fn(bindings: &[(u64, &[u64])]) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(nat_ty());
    // default: [s]
    let mut body = list_cons(nat_ty(), s.clone(), list_nil(nat_ty()));
    for (v, r) in bindings.iter().rev() {
        let cond = nat_beq(s.clone(), Expr::nat_lit(*v));
        body = Expr::apps(
            Expr::const_str(names::ITE_LIST),
            [cond, nat_list_lit(r), body],
        );
    }
    b.finish(b.mk_lam(s_id, BinderInfo::Default, nat_ty(), body))
}

/// `Clean.MM.applySubst (subst_fn bindings) e` — the kernel term that applies a
/// simultaneous Metamath substitution to expression `e`.
pub fn apply_subst_app(bindings: &[(u64, &[u64])], e: &[u64]) -> Expr {
    Expr::apps(
        Expr::const_str(names::APPLY_SUBST),
        [subst_fn(bindings), nat_list_lit(e)],
    )
}

// ── importer core: structured Metamath → kernel certificate ─────────────────────

/// `Clean.MM.MMThm` — the Metamath provability predicate (`List Nat → Prop`); a
/// form's first symbol is its typecode (`wff`, `class`, `setvar`, `|-`).
pub const MMTHM: &str = "Clean.MM.MMThm";

/// `Clean.MM.MMThm form : Prop`.
fn mmthm_of(form: Expr) -> Expr {
    Expr::app(Expr::const_str(MMTHM), form)
}

/// A Metamath assertion (`$a`, or a `$p` reused as a lemma) for schematic
/// registration as `Π σ, MMThm(σ f_0) → … → MMThm(σ e_0) → … → MMThm(σ concl)`.
#[derive(Clone, Debug)]
pub struct MMAssertion {
    /// Kernel constant name (e.g. `mm.ax-mp`).
    pub name: String,
    /// Mandatory floating hypotheses as `(typecode, variable)` symbol codes.
    pub float_hyps: Vec<(u64, u64)>,
    /// Mandatory essential hypotheses as full forms (`[typecode, …]`).
    pub essential_hyps: Vec<Vec<u64>>,
    /// Conclusion as a full form (`[typecode, …]`).
    pub conclusion: Vec<u64>,
    /// Disjoint-variable (`$d`) frame as `(x, y)` variable-code pairs. When
    /// non-empty, the assertion is registered with one `disjPair` GUARD arrow per
    /// pair (after the σ binder, before the `MMThm` hyps), so the kernel itself
    /// enforces the side-condition (M12). Empty for `$d`-free assertions.
    pub disjoints: Vec<(u64, u64)>,
    /// The variable-code universe (the `$f`-float variables) used by `varsOf`/
    /// `disjPair` to classify which codes are variables. Same for every assertion
    /// in a database; carried per-assertion only to keep the registrar signature
    /// stable. Ignored when `disjoints` is empty.
    pub var_universe: Vec<u64>,
}

impl MMAssertion {
    /// Mandatory hypothesis forms in Π-argument order: floats (as `[tc, var]`)
    /// then essentials.
    fn hyp_forms(&self) -> Vec<Vec<u64>> {
        let mut v: Vec<Vec<u64>> = self
            .float_hyps
            .iter()
            .map(|&(tc, var)| vec![tc, var])
            .collect();
        v.extend(self.essential_hyps.iter().cloned());
        v
    }
}

/// A Metamath proof tree.
#[derive(Clone, Debug)]
pub enum MMProofTree {
    /// The current theorem's `i`-th hypothesis (floats then essentials).
    Hyp(usize),
    /// Apply `assertion` under `subst`; `args` are the sub-proofs for each
    /// mandatory hypothesis (floats then essentials, in order).
    Apply {
        /// Constant name of the applied assertion.
        assertion: String,
        /// Substitution: variable code → replacement form.
        subst: Vec<(u64, Vec<u64>)>,
        /// Sub-proofs, one per mandatory hypothesis.
        args: Vec<MMProofTree>,
    },
}

/// Register `MMThm` (idempotent) plus each assertion as a schematic `Axiom`.
///
/// # Errors
/// Propagates declaration / type-checking errors.
pub fn register_metamath_assertions(
    env: &mut Environment,
    assertions: &[MMAssertion],
) -> Result<(), EnvError> {
    env.init_metamath_reflect()?;
    if env.get_const(&Name::from_string(MMTHM)).is_none() {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(MMTHM),
            level_params: vec![],
            type_: Expr::arrow(list_nat(), Expr::prop()),
        })?;
    }
    for a in assertions {
        if env.get_const(&Name::from_string(&a.name)).is_some() {
            continue;
        }
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(subst_ty());
        // M13: `applySubstV` (the constant-fixing substitution) is the FAITHFUL
        // Metamath substitution — σ rewrites only the variable-universe tokens and
        // fixes constants — and is the encoding the keystone distribution lemmas
        // hold for. On the concrete (importer) σ it reduces to the same ground form
        // as the old `applySubst`, so the ground path is unchanged.
        let vu = var_universe_lit(&a.var_universe);
        let mut ty = mmthm_of(apply_subst_v_app(
            vu.clone(),
            s.clone(),
            nat_list_lit(&a.conclusion),
        ));
        for h in a.hyp_forms().iter().rev() {
            ty = Expr::arrow(
                mmthm_of(apply_subst_v_app(vu.clone(), s.clone(), nat_list_lit(h))),
                ty,
            );
        }
        // M12: one `disjPair … = true` GUARD arrow per `$d` pair, OUTSIDE the
        // MMThm hyps (so the conclusion is unreachable unless every $d holds).
        if !a.disjoints.is_empty() {
            for &(x, y) in a.disjoints.iter().rev() {
                let guard = eq_bool_t(disjpair_app(vu.clone(), s.clone(), x, y), btrue());
                ty = Expr::arrow(guard, ty);
            }
        }
        let ty = b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_ty(), ty));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&a.name),
            level_params: vec![],
            type_: ty,
        })?;
    }
    Ok(())
}

/// Register a `$f` floating-hypothesis axiom as the GROUND typing of one variable:
/// `mm.<name> : Π σ, MMThm([typecode, variable])`. The body deliberately IGNORES σ
/// (it is the constant ground form, NOT `applySubst σ`), so this is the SOUND fact
/// "this specific variable has this typecode" — it is the Metamath `$f` grammar
/// postulate. Registering it as `Π σ, MMThm(applySubst σ [tc,var])` would instead
/// claim `MMThm([tc, σ(var)])` for ALL σ — false for a type-incorrect σ (e.g.
/// `[wff, <a setvar>]`) and would pollute the `MMThm` trust base. Applied at any σ
/// (the importer uses the identity) it yields `MMThm([tc, var])`.
pub fn register_float_axiom(
    env: &mut Environment,
    name: &str,
    typecode: u64,
    variable: u64,
) -> Result<(), EnvError> {
    env.init_metamath_reflect()?;
    if env.get_const(&Name::from_string(MMTHM)).is_none() {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(MMTHM),
            level_params: vec![],
            type_: Expr::arrow(list_nat(), Expr::prop()),
        })?;
    }
    if env.get_const(&Name::from_string(name)).is_some() {
        return Ok(());
    }
    let mut b = EnvDeclBuilder::new();
    let (s_id, _s) = b.fresh_local(subst_ty());
    // GROUND body — independent of σ.
    let body = mmthm_of(nat_list_lit(&[typecode, variable]));
    let ty = b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_ty(), body));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
}

/// Build the derivation term for a proof tree given the theorem's hypothesis
/// FVars (floats then essentials).
fn build_derivation(
    tree: &MMProofTree,
    hyp_vars: &[Expr],
    guard_counts: &std::collections::HashMap<String, usize>,
) -> Expr {
    match tree {
        MMProofTree::Hyp(i) => hyp_vars[*i].clone(),
        MMProofTree::Apply {
            assertion,
            subst,
            args,
        } => {
            let bindings: Vec<(u64, &[u64])> =
                subst.iter().map(|(v, r)| (*v, r.as_slice())).collect();
            let mut term = Expr::app(Expr::const_str(assertion), subst_fn(&bindings));
            // M12: a `$d`-bearing assertion has one `disjPair … = true` GUARD arrow
            // per pair, BEFORE its MMThm hyps. On the ground path the obligation is
            // concrete, so each is discharged by `Eq.refl Bool.true`: the kernel
            // reduces `disjPair` on the (already-substituted) ground forms and only
            // lets it through when the disjointness genuinely holds.
            if let Some(&k) = guard_counts.get(assertion) {
                for _ in 0..k {
                    term = Expr::app(term, eq_refl_bool_t(btrue()));
                }
            }
            for arg in args {
                term = Expr::app(term, build_derivation(arg, hyp_vars, guard_counts));
            }
            term
        }
    }
}

/// Kernel-verify a Metamath theorem (GROUND form: its variables are fixed
/// symbols and its mandatory floating/essential hypotheses are lambda
/// parameters). The proof tree applies the registered schematic assertions at
/// concrete substitutions; the kernel checks the derivation, reducing
/// `applySubst` at each step. On success the theorem is added to `env`.
///
/// This handles any proof that applies registered assertions at concrete
/// substitutions over the theorem's own (fixed) symbols — i.e. no substitution
/// composition is needed (see [`names::APPLYSUBST_COMPOSE`] for the lemma that
/// will lift this to schematic, reusable theorems).
///
/// # Errors
/// Returns the kernel error if the derivation does not type-check — i.e. the
/// Metamath proof is invalid.
pub fn verify_metamath_theorem(
    env: &mut Environment,
    name: &str,
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    proof: &MMProofTree,
) -> Result<(), EnvError> {
    verify_metamath_theorem_guarded(
        env,
        name,
        float_hyps,
        essential_hyps,
        conclusion,
        proof,
        &std::collections::HashMap::new(),
    )
}

/// Like [`verify_metamath_theorem`], but discharges the `$d` GUARD arrows of any
/// `$d`-bearing assertion applied in `proof` (M12). `guard_counts` maps each such
/// assertion's kernel name to its number of `$d` pairs; each guard is discharged
/// by a ground `Eq.refl Bool.true`, so the kernel re-checks disjointness itself.
///
/// # Errors
/// Returns the kernel error if the derivation does not type-check (an invalid
/// proof, OR a `$d`-violating substitution whose `disjPair` reduces to `false`).
pub fn verify_metamath_theorem_guarded(
    env: &mut Environment,
    name: &str,
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    proof: &MMProofTree,
    guard_counts: &std::collections::HashMap<String, usize>,
) -> Result<(), EnvError> {
    let mut hyp_forms: Vec<Vec<u64>> = float_hyps.iter().map(|&(tc, var)| vec![tc, var]).collect();
    hyp_forms.extend(essential_hyps.iter().cloned());

    let mut b = EnvDeclBuilder::new();
    let mut hyp_ids = Vec::new();
    let mut hyp_vars = Vec::new();
    for h in &hyp_forms {
        let (id, v) = b.fresh_local(mmthm_of(nat_list_lit(h)));
        hyp_ids.push(id);
        hyp_vars.push(v);
    }

    let mut value = build_derivation(proof, &hyp_vars, guard_counts);
    for (id, h) in hyp_ids.iter().zip(hyp_forms.iter()).rev() {
        value = b.mk_lam(*id, BinderInfo::Default, mmthm_of(nat_list_lit(h)), value);
    }
    let value = b.finish(value);

    let mut ty = mmthm_of(nat_list_lit(conclusion));
    for h in hyp_forms.iter().rev() {
        ty = Expr::arrow(mmthm_of(nat_list_lit(h)), ty);
    }

    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
    })
}

// ── Schematic reuse (M11) ───────────────────────────────────────────────────
//
// The GROUND `verify_metamath_theorem` inlines a reused theorem's whole proof
// tree, producing terms that grow with the proof's transitive size — slow to
// check and a trigger for the deep-term def-eq pathology. The SCHEMATIC path
// instead registers each theorem as
//   `mm.T : Π σ, MMThm(applySubst σ H₀) → … → MMThm(applySubst σ C)`
// and reuses it by APPLYING the registered constant at the call-site σ, so every
// derivation term stays small (one application per proof step, no inlining). The
// bridge is `applySubst_compose` (M5): applying `mm.X` at `comp σ σₙ` yields a
// type def-eq (via the lemma) to `applySubst σ (applySubst σₙ ·)`, cast with
// `Eq.mp`/`Eq.mpr` over `MMThm`.

/// The `MMThm` predicate as a function `List Nat → Prop`.
fn mmthm_fn() -> Expr {
    Expr::const_str(MMTHM)
}

/// `@congrArg.{1,1} (List Nat) Prop a1 a2 MMThm h : (MMThm a1) = (MMThm a2)`.
fn congr_arg_mmthm(a1: Expr, a2: Expr, h: Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [list_nat(), Expr::prop(), a1, a2, mmthm_fn(), h],
    )
}

/// `@Eq.mp.{0} (MMThm a1) (MMThm a2) h term : MMThm a2` — cast a proof of
/// `MMThm a1` forward along `h : (MMThm a1) = (MMThm a2)`.
fn eq_mp_mmthm(a1: Expr, a2: Expr, h: Expr, term: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
        [mmthm_of(a1), mmthm_of(a2), h, term],
    )
}

/// `@Eq.mpr.{0} (MMThm a1) (MMThm a2) h term : MMThm a1` — cast a proof of
/// `MMThm a2` backward along `h : (MMThm a1) = (MMThm a2)`.
fn eq_mpr_mmthm(a1: Expr, a2: Expr, h: Expr, term: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [mmthm_of(a1), mmthm_of(a2), h, term],
    )
}

/// `Clean.MM.applySubst_compose s1 s2 e
///    : applySubst s1 (applySubst s2 e) = applySubst (comp s1 s2) e`.
#[cfg(test)]
fn applysubst_compose_app(s1: Expr, s2: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPLYSUBST_COMPOSE), [s1, s2, e])
}
/// `applySubstV_compose vu s1 s2 e`.
fn applysubstv_compose_app(vu: Expr, s1: Expr, s2: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::APPLYSUBSTV_COMPOSE), [vu, s1, s2, e])
}

/// `comp s1 s2 = fun (s : Nat) => applySubst s1 (s2 s)` — the substitution whose
/// `applySubst` equals `applySubst s1 ∘ applySubst s2` (per `applySubst_compose`).
#[cfg(test)]
fn comp_subst(s1: &Expr, s2: &Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        applysubst2(s1.clone(), Expr::app(s2.clone(), Expr::bvar(0))),
    )
}

/// `comp_v vu s1 s2 = λ k, applySubstV vu s1 (s2 k)` — the constant-fixing
/// composition. The compound-`$d` discharge needs this: with `applySubstV` (which
/// fixes constants), the keystone `varsOf_applySubstV` applies, so `varsOf vu
/// ((comp_v σ σn) b)` for a COMPOUND `σn b` distributes to the variables of `σn b`.
fn comp_subst_v(vu: &Expr, s1: &Expr, s2: &Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        apply_subst_v_app(vu.clone(), s1.clone(), Expr::app(s2.clone(), Expr::bvar(0))),
    )
}

/// Per-assertion signature needed to build schematic reuse: hypothesis forms
/// (Π-argument order) and conclusion form.
type AssertionSig = (Vec<Vec<u64>>, Vec<u64>);

/// Build a SCHEMATIC derivation term of type `MMThm(applySubst σ G)` where `G`
/// is the ground form `tree` proves. `sigma` is the outer schematic σ (an FVar);
/// `hyp_vars` are the theorem's hypothesis FVars; `sigs` maps each reused
/// assertion's kernel name to its `(hyp_forms, conclusion)`.
/// `R(v) = varsOf vu (σ v)` — the variable-set of `σ`'s image of variable `v`.
fn ld_chunk(vu: &Expr, sigma: &Expr, v: u64) -> Expr {
    vars_of_app(vu.clone(), Expr::app(sigma.clone(), Expr::nat_lit(v)))
}

/// The append-tree `append R(v0) (append R(v1) (… (append R(v_{k-1}) [])))` — the
/// def-eq normal form of `applySubstV vu (λk. varsOf vu (σ k)) [v0,…,v_{k-1}]`, the
/// keystone RHS for a compound `$d` image whose in-universe variables are `vs`.
fn ld_tree(vu: &Expr, sigma: &Expr, vs: &[u64]) -> Expr {
    let mut acc = list_nil(nat_ty());
    for &v in vs.iter().rev() {
        acc = append2(ld_chunk(vu, sigma, v), acc);
    }
    acc
}

/// Proof of `listDisjoint R(a0) (ld_tree vb) = true`, decomposing the RIGHT tree
/// via `listDisjoint_append` and discharging each leaf `listDisjoint R(a0) R(bj)`
/// (≡ `disjPair vu σ a0 bj`) from the theorem's guard hyps. `None` if a guard pair
/// is absent (e.g. a variable shared across the two images — a `$d` violation).
fn prove_right_disjoint(
    vu: &Expr,
    sigma: &Expr,
    a0: u64,
    vb: &[u64],
    dv_hyps: &hashbrown::HashMap<(u64, u64), Expr>,
) -> Option<Expr> {
    let r0 = ld_chunk(vu, sigma, a0);
    match vb.split_first() {
        None => Some(Expr::app(
            Expr::const_str(names::LISTDISJOINT_NIL_RIGHT),
            r0,
        )),
        Some((&b0, rest)) => {
            let s0 = ld_chunk(vu, sigma, b0);
            let rest_tree = ld_tree(vu, sigma, rest);
            let ld_r0_s0 = list_disjoint_app(r0.clone(), s0.clone());
            let ld_r0_rest = list_disjoint_app(r0.clone(), rest_tree.clone());
            // ldr : listDisjoint r0 (append s0 rest) = band (ld r0 s0) (ld r0 rest)
            let ldr = Expr::apps(
                Expr::const_str(names::LISTDISJOINT_APPEND),
                [r0.clone(), s0.clone(), rest_tree.clone()],
            );
            // leaf : ld r0 s0 = true  (≡ disjPair vu σ a0 b0 = true)
            let leaf = dv_hyps.get(&(a0, b0))?.clone();
            let prest = prove_right_disjoint(vu, sigma, a0, rest, dv_hyps)?;
            let f = Expr::lam(
                BinderInfo::Default,
                bool_ty(),
                band(Expr::bvar(0), ld_r0_rest.clone()),
            );
            let e2 = congr_arg_bool_bool(ld_r0_s0.clone(), btrue(), f, leaf);
            let tail = eq_trans_bool(
                band(ld_r0_s0.clone(), ld_r0_rest.clone()),
                band(btrue(), ld_r0_rest.clone()),
                btrue(),
                e2,
                prest,
            );
            Some(eq_trans_bool(
                list_disjoint_app(r0, append2(s0, rest_tree)),
                band(ld_r0_s0, ld_r0_rest),
                btrue(),
                ldr,
                tail,
            ))
        }
    }
}

/// Proof of `listDisjoint (ld_tree va) (ld_tree vb) = true`, decomposing the LEFT
/// tree via `listDisjoint_append_left` and delegating each row to
/// [`prove_right_disjoint`]. `None` if any cross-pair guard is absent.
fn prove_left_disjoint(
    vu: &Expr,
    sigma: &Expr,
    va: &[u64],
    vb: &[u64],
    dv_hyps: &hashbrown::HashMap<(u64, u64), Expr>,
) -> Option<Expr> {
    let vb_tree = ld_tree(vu, sigma, vb);
    match va.split_first() {
        None => Some(eq_refl_bool_e(btrue())),
        Some((&a0, rest)) => {
            let r0 = ld_chunk(vu, sigma, a0);
            let rest_tree = ld_tree(vu, sigma, rest);
            let ld_r0_vb = list_disjoint_app(r0.clone(), vb_tree.clone());
            let ld_rest_vb = list_disjoint_app(rest_tree.clone(), vb_tree.clone());
            // ldl : listDisjoint (append r0 rest) vb = band (ld r0 vb) (ld rest vb)
            let ldl = Expr::apps(
                Expr::const_str(names::LISTDISJOINT_APPEND_LEFT),
                [r0.clone(), rest_tree.clone(), vb_tree.clone()],
            );
            let p0 = prove_right_disjoint(vu, sigma, a0, vb, dv_hyps)?;
            let prest = prove_left_disjoint(vu, sigma, rest, vb, dv_hyps)?;
            let f = Expr::lam(
                BinderInfo::Default,
                bool_ty(),
                band(Expr::bvar(0), ld_rest_vb.clone()),
            );
            let e2 = congr_arg_bool_bool(ld_r0_vb.clone(), btrue(), f, p0);
            let tail = eq_trans_bool(
                band(ld_r0_vb.clone(), ld_rest_vb.clone()),
                band(btrue(), ld_rest_vb.clone()),
                btrue(),
                e2,
                prest,
            );
            Some(eq_trans_bool(
                list_disjoint_app(append2(r0, rest_tree), vb_tree.clone()),
                band(ld_r0_vb, ld_rest_vb),
                btrue(),
                ldl,
                tail,
            ))
        }
    }
}

/// Discharge a GENERAL (compound) `$d` obligation for assertion-pair `(a, b)` at a
/// reuse step. `image_a`/`image_b` are the FULL token images `σn a`/`σn b`;
/// `vu_set` classifies which tokens are variables. Returns a proof of
/// `disjPair vu (comp_v vu σ σn) a b = true` (or `None` if some cross-pair guard is
/// missing — e.g. a variable shared between the two images, a `$d` violation —
/// in which case the caller skips, never falsely accepts).
///
/// The keystone `varsOf_applySubstV` casts each side `varsOf vu (applySubstV vu σ
/// image)` to the append-tree of `varsOf vu (σ vᵢ)` over the image's variables;
/// `listDisjoint` then decomposes (left + right) into pairwise `disjPair vu σ vᵢ
/// wⱼ`, each a guard hypothesis.
#[allow(clippy::too_many_arguments)]
/// Cast a σ-IGNORED dummy float `mm.<dfloat> : Π σ, MMThm([tc,d])` up to the
/// schematically-required `MMThm(applySubstV vu σ [tc,d])`, using the σ-fixes-d
/// guard hypothesis `fix_d : applySubstV vu σ [d] = [d]`. Sound because
/// `applySubstV vu σ [tc,d] ≡ append [tc] (applySubstV vu σ [d])` (the constant
/// `tc ∉ vu` is fixed) and `[tc,d] ≡ append [tc] [d]`, so `congrArg (append [tc])
/// fix_d` bridges them. (See `test.dummyFloatCast`.)
fn dummy_float_cast(
    vu: &Expr,
    sigma: &Expr,
    float_const: Expr,
    tc: u64,
    d: u64,
    fix_d: Expr,
) -> Expr {
    let tc1 = nat_list_lit(&[tc]);
    let d1 = nat_list_lit(&[d]);
    let tcd = nat_list_lit(&[tc, d]);
    // f = λ e:List Nat, append [tc] e
    let f = Expr::lam(BinderInfo::Default, list_nat(), append2(tc1, Expr::bvar(0)));
    let lhs = apply_subst_v_app(vu.clone(), sigma.clone(), tcd.clone());
    let hform = congr_arg_list(
        apply_subst_v_app(vu.clone(), sigma.clone(), d1.clone()),
        d1,
        f,
        fix_d,
    );
    let h_mmthm = congr_arg_mmthm(lhs.clone(), tcd.clone(), hform);
    let float_app = Expr::app(float_const, sigma.clone());
    eq_mpr_mmthm(lhs, tcd, h_mmthm, float_app)
}

/// Discharge a REUSED dummy-theorem's σ-fixes-d guard at a call site: its
/// registered guard `applySubstV vu (comp_v σ σn) [d] = [d]` reduces (σn fixes the
/// dummy: `σn(d) = [d]`) to `append (applySubstV vu σ [d]) []`, closed by
/// `append_nil_right` then the CURRENT theorem's own propagated fix-d guard
/// `fix_d`. (See `test.dummyTransitiveFixDischarge`.)
fn dummy_fix_discharge(vu: &Expr, sigma: &Expr, sn: &Expr, d: u64, fix_d: Expr) -> Expr {
    let d1 = nat_list_lit(&[d]);
    let comp = comp_subst_v(vu, sigma, sn);
    let mid = apply_subst_v_app(vu.clone(), sigma.clone(), d1.clone());
    let lhs = apply_subst_v_app(vu.clone(), comp, d1.clone());
    let anr = Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), mid.clone());
    eq_trans_list(lhs, mid, d1, anr, fix_d)
}

fn disjpair_discharge(
    vu: &Expr,
    vu_set: &hashbrown::HashSet<u64>,
    sigma: &Expr,
    sn: &Expr,
    a: u64,
    b: u64,
    image_a: &[u64],
    image_b: &[u64],
    dv_hyps: &hashbrown::HashMap<(u64, u64), Expr>,
) -> Option<Expr> {
    let va: Vec<u64> = image_a
        .iter()
        .copied()
        .filter(|t| vu_set.contains(t))
        .collect();
    let vb: Vec<u64> = image_b
        .iter()
        .copied()
        .filter(|t| vu_set.contains(t))
        .collect();

    let comp = comp_subst_v(vu, sigma, sn);
    let ea = nat_list_lit(image_a);
    let eb = nat_list_lit(image_b);
    let va_tree = ld_tree(vu, sigma, &va);
    let vb_tree = ld_tree(vu, sigma, &vb);

    // LA = varsOf vu (applySubstV vu σ image) ; def-eq to varsOf vu (comp_v a).
    let la = vars_of_app(
        vu.clone(),
        apply_subst_v_app(vu.clone(), sigma.clone(), ea.clone()),
    );
    let lb = vars_of_app(
        vu.clone(),
        apply_subst_v_app(vu.clone(), sigma.clone(), eb.clone()),
    );
    // keystone: LA = applySubstV vu φ (varsOf vu image) ≡ va_tree (def-eq).
    let cast_a = Expr::apps(
        Expr::const_str(names::VARSOF_APPLYSUBSTV),
        [vu.clone(), sigma.clone(), ea],
    );
    let cast_b = Expr::apps(
        Expr::const_str(names::VARSOF_APPLYSUBSTV),
        [vu.clone(), sigma.clone(), eb],
    );
    let f_left = Expr::lam(
        BinderInfo::Default,
        list_nat(),
        list_disjoint_app(Expr::bvar(0), lb.clone()),
    );
    let step_a = congr_arg_list_bool(la.clone(), va_tree.clone(), f_left, cast_a);
    let f_right = Expr::lam(
        BinderInfo::Default,
        list_nat(),
        list_disjoint_app(va_tree.clone(), Expr::bvar(0)),
    );
    let step_b = congr_arg_list_bool(lb.clone(), vb_tree.clone(), f_right, cast_b);
    let bridge = eq_trans_bool(
        list_disjoint_app(la.clone(), lb.clone()),
        list_disjoint_app(va_tree.clone(), lb),
        list_disjoint_app(va_tree.clone(), vb_tree.clone()),
        step_a,
        step_b,
    );
    let core = prove_left_disjoint(vu, sigma, &va, &vb, dv_hyps)?;
    Some(eq_trans_bool(
        disjpair_app(vu.clone(), comp, a, b),
        list_disjoint_app(va_tree, vb_tree),
        btrue(),
        bridge,
        core,
    ))
}

/// `$d` context threaded through schematic derivation: the variable universe, the
/// guard frame of each guarded assertion (name → `$d` pairs), and the current
/// theorem's guard hypotheses keyed by ordered `(x,y)` pair.
struct DvCtx<'a> {
    vu: &'a Expr,
    vu_set: &'a hashbrown::HashSet<u64>,
    guards: &'a hashbrown::HashMap<String, Vec<(u64, u64)>>,
    dv_hyps: &'a hashbrown::HashMap<(u64, u64), Expr>,
    /// Per-dummy `applySubstV vu σ [d] = [d]` hypothesis FVars (this theorem's
    /// transitive dummy frame). Used to cast dummy float leaves and to discharge a
    /// reused dummy-theorem's fix-d guards.
    fix_hyps: &'a hashbrown::HashMap<u64, Expr>,
    /// Names of the `$f` float-AXIOMS (σ-ignored `Π σ, MMThm([tc,d])`); an `Apply`
    /// of one is a dummy float leaf, cast via `dummy_float_cast`.
    float_names: &'a hashbrown::HashSet<String>,
    /// Per reusable assertion, its transitive fix-d dummy frame (in registration
    /// order) — the σ-fixes-d guard arrows it carries, discharged on reuse.
    fix_guards: &'a hashbrown::HashMap<String, Vec<u64>>,
}

fn build_schematic_derivation(
    tree: &MMProofTree,
    sigma: &Expr,
    hyp_vars: &[Expr],
    sigs: &hashbrown::HashMap<String, AssertionSig>,
    dv: &DvCtx<'_>,
) -> Option<Expr> {
    match tree {
        MMProofTree::Hyp(i) => Some(hyp_vars.get(*i)?.clone()),
        MMProofTree::Apply {
            assertion,
            subst,
            args,
        } => {
            // M13-dummy: a `$f` float-AXIOM leaf types a DUMMY/work variable `d`. Its
            // σ-ignored `MMThm([tc,d])` is cast up to `MMThm(applySubstV vu σ [tc,d])`
            // via this theorem's σ-fixes-d guard. (No guards/args of its own.)
            if dv.float_names.contains(assertion) {
                let (_, c) = sigs.get(assertion)?;
                if c.len() != 2 {
                    return None;
                }
                let (tc, d) = (c[0], c[1]);
                let fix_d = dv.fix_hyps.get(&d)?.clone();
                return Some(dummy_float_cast(
                    dv.vu,
                    sigma,
                    Expr::const_str(assertion),
                    tc,
                    d,
                    fix_d,
                ));
            }
            let (x_hyps, x_concl) = sigs.get(assertion)?;
            if args.len() != x_hyps.len() {
                return None;
            }
            let bindings: Vec<(u64, &[u64])> =
                subst.iter().map(|(v, r)| (*v, r.as_slice())).collect();
            let sn = subst_fn(&bindings); // subst_fn σₙ (concrete)
            let comp = comp_subst_v(dv.vu, sigma, &sn); // comp_v σ σₙ (constant-fixing)

            // mm.X (comp_v σ σₙ) [fix_disch…] [guard_disch…] [cast_arg₀ …]
            let mut term = Expr::app(Expr::const_str(assertion), comp.clone());
            // M13-dummy: FIRST discharge a reused dummy-theorem's σ-fixes-d guards
            // (registered BEFORE its `$d` guards). Each reduces, via σn(d)=[d] +
            // append_nil_right, to this theorem's own propagated fix-d hyp.
            if let Some(dummies) = dv.fix_guards.get(assertion) {
                for &d in dummies {
                    let fix_d = dv.fix_hyps.get(&d)?.clone();
                    term = Expr::app(term, dummy_fix_discharge(dv.vu, sigma, &sn, d, fix_d));
                }
            }
            // M13: discharge the assertion's `$d` GUARD arrows from the current
            // theorem's guard hypotheses. The GENERAL (compound) discharge handles
            // arbitrary multi-variable images via the keystone + listDisjoint
            // distribution; an absent cross-pair guard (e.g. a shared variable, a
            // `$d` violation) returns None so the caller skips — never accepts.
            if let Some(pairs) = dv.guards.get(assertion) {
                for &(a, b) in pairs {
                    let image_a: Vec<u64> = subst
                        .iter()
                        .find(|(v, _)| *v == a)
                        .map(|(_, r)| r.clone())
                        .unwrap_or_else(|| vec![a]);
                    let image_b: Vec<u64> = subst
                        .iter()
                        .find(|(v, _)| *v == b)
                        .map(|(_, r)| r.clone())
                        .unwrap_or_else(|| vec![b]);
                    let disch = disjpair_discharge(
                        dv.vu, dv.vu_set, sigma, &sn, a, b, &image_a, &image_b, dv.dv_hyps,
                    )?;
                    term = Expr::app(term, disch);
                }
            }
            for (arg, x_h) in args.iter().zip(x_hyps.iter()) {
                let sub = build_schematic_derivation(arg, sigma, hyp_vars, sigs, dv)?;
                let xh = nat_list_lit(x_h);
                // L = applySubstV vu σ (applySubstV vu σₙ X_Hᵢ);  R = applySubstV vu (comp_v σ σₙ) X_Hᵢ
                let l = apply_subst_v_app(
                    dv.vu.clone(),
                    sigma.clone(),
                    apply_subst_v_app(dv.vu.clone(), sn.clone(), xh.clone()),
                );
                let r = apply_subst_v_app(dv.vu.clone(), comp.clone(), xh.clone());
                let h = congr_arg_mmthm(
                    l.clone(),
                    r.clone(),
                    applysubstv_compose_app(dv.vu.clone(), sigma.clone(), sn.clone(), xh),
                );
                term = Expr::app(term, eq_mp_mmthm(l, r, h, sub));
            }
            // Cast the result back: term : MMThm(applySubstV vu (comp_v σ σₙ) X_C);
            // want MMThm(applySubstV vu σ (applySubstV vu σₙ X_C)) ≡ MMThm(applySubstV vu σ G).
            let xc = nat_list_lit(x_concl);
            let l = apply_subst_v_app(
                dv.vu.clone(),
                sigma.clone(),
                apply_subst_v_app(dv.vu.clone(), sn.clone(), xc.clone()),
            );
            let r = apply_subst_v_app(dv.vu.clone(), comp.clone(), xc.clone());
            let h = congr_arg_mmthm(
                l.clone(),
                r.clone(),
                applysubstv_compose_app(dv.vu.clone(), sigma.clone(), sn, xc),
            );
            Some(eq_mpr_mmthm(l, r, h, term))
        }
    }
}

/// Build the SCHEMATIC-`$d` registration TYPE of a theorem WITHOUT its proof:
/// `Π σ, (σ-fixes-d …) → (disjPair … = true …) → MMThm(applySubstV vu σ H₀) → … →
/// MMThm(applySubstV vu σ C)`. This is exactly the `ty` that
/// [`verify_metamath_theorem_schematic_dv`] registers on success — it depends ONLY
/// on the frame (`float_hyps`/`essential_hyps`/`conclusion`), the `$d` frame
/// (`disjoints`), the dummy frame (`fix_dummies`), and the variable universe — and
/// NOT on the proof tree. The two-pass PASS-1 uses it to register the type CHEAPLY
/// (no embedding derivation), and the full verifier reuses it so the registered
/// type is byte-identical on both paths.
fn schematic_dv_type(
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    disjoints: &[(u64, u64)],
    var_universe: &[u64],
    fix_dummies: &[u64],
) -> Expr {
    let mut hyp_forms: Vec<Vec<u64>> = float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
    hyp_forms.extend(essential_hyps.iter().cloned());

    // Guard pairs in BOTH orders (a step may need either), deduped — identical to
    // the ordering `verify_metamath_theorem_schematic_dv` produces.
    let mut guard_pairs: Vec<(u64, u64)> = Vec::new();
    {
        let mut seen: hashbrown::HashSet<(u64, u64)> = hashbrown::HashSet::new();
        for &(x, y) in disjoints {
            for p in [(x, y), (y, x)] {
                if seen.insert(p) {
                    guard_pairs.push(p);
                }
            }
        }
    }
    let vu = var_universe_lit(var_universe);
    let guard_ty =
        |p: (u64, u64), s: &Expr| eq_bool_t(disjpair_app(vu.clone(), s.clone(), p.0, p.1), btrue());
    let hyp_ty =
        |h: &[u64], s: &Expr| mmthm_of(apply_subst_v_app(vu.clone(), s.clone(), nat_list_lit(h)));
    let fix_ty = |d: u64, s: &Expr| {
        let d1 = nat_list_lit(&[d]);
        eq_list_t(apply_subst_v_app(vu.clone(), s.clone(), d1.clone()), d1)
    };

    let mut tb = EnvDeclBuilder::new();
    let (s_id, s) = tb.fresh_local(subst_ty());
    let mut t = mmthm_of(apply_subst_v_app(
        vu.clone(),
        s.clone(),
        nat_list_lit(conclusion),
    ));
    for h in hyp_forms.iter().rev() {
        t = Expr::arrow(hyp_ty(h, &s), t);
    }
    for &p in guard_pairs.iter().rev() {
        t = Expr::arrow(guard_ty(p, &s), t);
    }
    for &d in fix_dummies.iter().rev() {
        t = Expr::arrow(fix_ty(d, &s), t);
    }
    tb.finish(tb.mk_pi(s_id, BinderInfo::Default, subst_ty(), t))
}

/// Two-pass PASS-1 LIGHT registration: register ONLY a theorem's schematic-`$d`
/// TYPE, skipping the (expensive) embedding derivation [`build_schematic_derivation`]
/// that the full verifier builds and pass-1 then immediately throws away. The type
/// is produced by the shared [`schematic_dv_type`] helper, so it is byte-identical
/// to the type the full path registers on success.
///
/// Registration goes through the SAME `Environment::add_decl` path the existing
/// pass-1 uses: a `Declaration::Theorem` whose proof `value` is a throwaway
/// placeholder. Under [`set_mm_axiom_only`] (asserted ON — this is a PASS-1-only
/// entry point) `add_decl` drops the placeholder UNEXAMINED and registers the type
/// as an axiom (`add_decl_unchecked`), so no new unchecked call site is introduced
/// and the result is bit-for-bit what full pass-1 registers. Returns the kernel
/// error only if the flag is OFF (a misuse — the placeholder would then be checked).
///
/// SOUNDNESS: sound ONLY inside the Metamath two-pass, where pass-2 RE-VERIFIES
/// every in-range proof against this type and ONLY pass-2-verified, dependency-
/// closure-gated theorems are exported. Skipping the proof-term BUILD here is no
/// weaker than the existing pass-1, which already drops that term unchecked; we just
/// avoid constructing it. An ill-formed type would make a reusing proof FAIL pass-2
/// and the gate DROP it — never a false accept. Validated by count-equivalence
/// (two-pass+gate == sequential).
///
/// The caller passes the theorem's actual `$d` frame (`disjoints`) and dummy frame
/// (`fix_dummies`) so the registered SCHEMATIC type matches what the full
/// schematic-`$d` path registers on SUCCESS. The one divergence is a theorem whose
/// full path would FAIL schematic-`$d` and FALL BACK to the GROUND (non-reusable)
/// type: this light path still registers the schematic type, but that only ever
/// makes a reusing proof FAIL-CLOSED (skip) in pass-2 — the same outcome the
/// sequential verifier produces for a ground (non-reusable) theorem — so
/// count-equivalence is preserved. A wrong type only loses verifications (caught by
/// count-equivalence), never falsely accepts.
///
/// # Errors
/// Returns `EnvError` if `set_mm_axiom_only` is not ON (misuse) or `add_decl` fails.
#[allow(clippy::too_many_arguments)]
pub fn register_metamath_theorem_type_light(
    env: &mut Environment,
    name: &str,
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    disjoints: &[(u64, u64)],
    var_universe: &[u64],
    fix_dummies: &[u64],
) -> Result<(), EnvError> {
    let ty = schematic_dv_type(
        float_hyps,
        essential_hyps,
        conclusion,
        disjoints,
        var_universe,
        fix_dummies,
    );
    // Throwaway placeholder proof value: `add_decl` under `set_mm_axiom_only` drops
    // it WITHOUT inspecting it (it converts the Theorem to an unchecked Axiom). A
    // bare `Sort 0` is the cheapest well-formed Expr; it is never type-checked here.
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value: Expr::sort(Level::zero()),
    })
}

/// Kernel-verify a Metamath theorem in SCHEMATIC form and register it as
/// `mm.<name> : Π σ, MMThm(applySubst σ H₀) → … → MMThm(applySubst σ C)`, so later
/// theorems can REUSE it by application (no proof-tree inlining). `sigs` provides
/// the `(hyp_forms, conclusion)` of every assertion the proof applies (the `$a`
/// axioms and earlier schematic `$p` theorems).
///
/// # Errors
/// Returns the kernel error if the schematic derivation does not type-check.
#[allow(clippy::too_many_arguments)]
pub fn verify_metamath_theorem_schematic(
    env: &mut Environment,
    name: &str,
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    proof: &MMProofTree,
    sigs: &hashbrown::HashMap<String, AssertionSig>,
    var_universe: &[u64],
) -> Result<(), EnvError> {
    verify_metamath_theorem_schematic_dv(
        env,
        name,
        float_hyps,
        essential_hyps,
        conclusion,
        proof,
        sigs,
        &[],
        var_universe,
        &hashbrown::HashMap::new(),
        &[],
        &hashbrown::HashSet::new(),
        &hashbrown::HashMap::new(),
    )
}

/// Like [`verify_metamath_theorem_schematic`] but with `$d` (disjoint-variable)
/// support: `disjoints` is the theorem's `$d` frame, `var_universe` the variable
/// codes, and `guards` the `$d` frame of every guarded assertion the proof applies.
/// The theorem is registered as `Π σ, (disjPair vu σ xᵢ yᵢ = true …) → MMThm(…) →
/// … → C`; each guarded assertion's step obligation is discharged from these guard
/// hypotheses by the GENERAL (compound) keystone discharge — arbitrary
/// multi-variable images, constants fixed — returning `None` (caller skips) only if
/// a needed cross-pair guard is absent. With empty `disjoints` this is identical to
/// the `$d`-free path, so the existing schematic theorems are unaffected.
#[allow(clippy::too_many_arguments)]
pub fn verify_metamath_theorem_schematic_dv(
    env: &mut Environment,
    name: &str,
    float_hyps: &[(u64, u64)],
    essential_hyps: &[Vec<u64>],
    conclusion: &[u64],
    proof: &MMProofTree,
    sigs: &hashbrown::HashMap<String, AssertionSig>,
    disjoints: &[(u64, u64)],
    var_universe: &[u64],
    guards: &hashbrown::HashMap<String, Vec<(u64, u64)>>,
    fix_dummies: &[u64],
    float_names: &hashbrown::HashSet<String>,
    fix_guards: &hashbrown::HashMap<String, Vec<u64>>,
) -> Result<(), EnvError> {
    let mut hyp_forms: Vec<Vec<u64>> = float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
    hyp_forms.extend(essential_hyps.iter().cloned());

    // Guard pairs in BOTH orders (a step may need either), deduped.
    let mut guard_pairs: Vec<(u64, u64)> = Vec::new();
    {
        let mut seen: hashbrown::HashSet<(u64, u64)> = hashbrown::HashSet::new();
        for &(x, y) in disjoints {
            for p in [(x, y), (y, x)] {
                if seen.insert(p) {
                    guard_pairs.push(p);
                }
            }
        }
    }
    let vu = var_universe_lit(var_universe);
    let vu_set: hashbrown::HashSet<u64> = var_universe.iter().copied().collect();
    let guard_ty =
        |p: (u64, u64), s: &Expr| eq_bool_t(disjpair_app(vu.clone(), s.clone(), p.0, p.1), btrue());
    let hyp_ty =
        |h: &[u64], s: &Expr| mmthm_of(apply_subst_v_app(vu.clone(), s.clone(), nat_list_lit(h)));
    // M13-dummy: σ-fixes-d guard `applySubstV vu σ [d] = [d]` for each transitive dummy.
    let fix_ty = |d: u64, s: &Expr| {
        let d1 = nat_list_lit(&[d]);
        eq_list_t(apply_subst_v_app(vu.clone(), s.clone(), d1.clone()), d1)
    };

    let mut b = EnvDeclBuilder::new();
    let (sigma_id, sigma) = b.fresh_local(subst_ty());
    // σ-fixes-d guard FVars (OUTERMOST: registered before the `$d`/MMThm arrows).
    let mut fix_ids = Vec::new();
    let mut fix_hyps: hashbrown::HashMap<u64, Expr> = hashbrown::HashMap::new();
    for &d in fix_dummies {
        let (id, v) = b.fresh_local(fix_ty(d, &sigma));
        fix_ids.push(id);
        fix_hyps.insert(d, v);
    }
    // `$d` guard hypothesis FVars (before the MMThm hyps)
    let mut guard_ids = Vec::new();
    let mut dv_hyps: hashbrown::HashMap<(u64, u64), Expr> = hashbrown::HashMap::new();
    for &p in &guard_pairs {
        let (id, v) = b.fresh_local(guard_ty(p, &sigma));
        guard_ids.push(id);
        dv_hyps.insert(p, v);
    }
    // MMThm hypothesis FVars
    let mut hyp_ids = Vec::new();
    let mut hyp_vars = Vec::new();
    for h in &hyp_forms {
        let (id, v) = b.fresh_local(hyp_ty(h, &sigma));
        hyp_ids.push(id);
        hyp_vars.push(v);
    }

    let dv = DvCtx {
        vu: &vu,
        vu_set: &vu_set,
        guards,
        dv_hyps: &dv_hyps,
        fix_hyps: &fix_hyps,
        float_names,
        fix_guards,
    };
    let body =
        build_schematic_derivation(proof, &sigma, &hyp_vars, sigs, &dv).ok_or_else(|| {
            EnvError::InvalidDeclarationShape {
                init: "verify_metamath_theorem_schematic",
                decl: Name::from_string(name),
                detail: "proof references an unknown assertion, bad arity, or a \
                         $d obligation with a missing cross-pair guard",
            }
        })?;

    let mut value = body;
    for (id, h) in hyp_ids.iter().zip(hyp_forms.iter()).rev() {
        value = b.mk_lam(*id, BinderInfo::Default, hyp_ty(h, &sigma), value);
    }
    for (id, &p) in guard_ids.iter().zip(guard_pairs.iter()).rev() {
        value = b.mk_lam(*id, BinderInfo::Default, guard_ty(p, &sigma), value);
    }
    for (id, &d) in fix_ids.iter().zip(fix_dummies.iter()).rev() {
        value = b.mk_lam(*id, BinderInfo::Default, fix_ty(d, &sigma), value);
    }
    value = b.mk_lam(sigma_id, BinderInfo::Default, subst_ty(), value);
    let value = b.finish(value);

    // Π σ, (guards) → MMThm(applySubst σ H₀) → … → MMThm(applySubst σ C).
    // Built by the SHARED helper so the type is byte-identical to the one the
    // two-pass PASS-1 light path (`register_metamath_theorem_type_light`) registers.
    let ty = schematic_dv_type(
        float_hyps,
        essential_hyps,
        conclusion,
        disjoints,
        var_universe,
        fix_dummies,
    );

    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
    })
}

#[cfg(test)]
#[path = "metamath_reflect_tests.rs"]
mod tests;

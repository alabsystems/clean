// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness PREVENTION GATE for provably-FALSE admitted axioms over the
//! "junk-admitting" free-inductive `Rat` carrier.
//!
//! # The bug class
//!
//! A *junk-admitting carrier* is a free inductive whose constructor admits
//! values outside the intended math domain, so a universally-quantified
//! admitted axiom over it can be FALSE. The live example is
//! `Rat | mk : Int → Nat` (no `denom > 0` / reduced invariant): a `denom = 0`
//! representative such as `Rat.mk 1 0` survives every constructor check, yet
//! `Rat.add` builds its denominator as the raw `Nat.mul (denom a) (denom b)`
//! (collapsing to `0`), and `Rat.le` measures via `Rat.effDenom` (which rescues
//! `0 → 1`). The result is that several admitted `Rat.*` ordered-field / ring
//! axioms reduce, on junk witnesses, to manifestly FALSE closed propositions
//! (a `False` `Int.le`, or an `@Eq Rat` between distinct `Rat.mk` constructors).
//! These are pinned individually in `tests_rat_false_add_axioms.rs` and the
//! `test_counterexample_premise_now_false` test of
//! `algebra_rat_le_trans_proof.rs`.
//!
//! # What this gate does
//!
//! For EVERY admitted `Rat.*` axiom in `ADMITTED_DOMAIN_AXIOMS` whose
//! conclusion is a *refutable-by-reduction* proposition (`@Eq Rat _ _`, or a
//! `Rat.le` that delta-reduces to a closed `Int.le`), a fully generic
//! refutation engine instantiates the axiom's leading binders with a battery of
//! closed witnesses (junk `denom = 0` representatives plus well-formed ones),
//! reduces every hypothesis and the conclusion via the kernel `TypeChecker`, and
//! decides whether the axiom is *refutable* — i.e. there is a witness tuple
//! under which every hypothesis reduces to a PROVABLE closed prop while the
//! conclusion reduces to a FALSE closed prop.
//!
//! The gate then asserts:
//!
//!   **every admitted `Rat.*` axiom found refutable is on an explicit
//!   allowlist of the currently-known-false ones.**
//!
//! This PASSES on current `main` (the refutable set is exactly the allowlist)
//! and FAILS LOUDLY the moment someone introduces a NEW admitted `Rat.*` axiom
//! that is false over the free carrier (it would be refutable but absent from
//! the allowlist). It is the structural complement to `tests_rat_false_add_axioms`:
//! that file pins that the known-false axioms ARE false; this file pins that NO
//! OTHER admitted `Rat.*` axiom is.
//!
//! Robustness: the refutation engine is purely `is_def_eq` / `whnf` based (no
//! reliance on a particular numeral encoding). A closed `Rat.le` / `Int.le`
//! prop delta-reduces to `Int.NonNeg t`; its truth is decided by grid-matching
//! the sign of `t` against `Int.ofNat k` (nonneg ⇒ provable) vs `Int.negSucc k`
//! (negative ⇒ false). A closed `@Eq Rat lhs rhs` is false iff `lhs`, `rhs`
//! reduce to distinct (`!is_def_eq`) `Rat.mk` constructors, and provable iff
//! they are `is_def_eq`.

use super::axiom_audit::ADMITTED_DOMAIN_AXIOMS;
use super::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Admitted `Rat.*` axioms that are PROVABLY FALSE over the free-inductive
/// `Rat.mk : Int → Nat` carrier (no `denom > 0` invariant).
///
/// These are NOT bugs to fix in place: each is an honest `Declaration::Axiom`
/// that the WS-A quotient-carrier fix
/// (`designs/2026-06-07-rat-carrier-soundness-and-minmax.md`) will turn into a
/// genuine kernel-checked theorem. At that point the name LEAVES
/// `ADMITTED_DOMAIN_AXIOMS` (it is proven, not admitted) and MUST be removed
/// from this list — otherwise the gate's "allowlist ⊆ admitted ∧ refutable"
/// cross-check below will flag the stale entry.
///
/// Membership rationale (all confirmed refutable by the engine, and pinned by
/// reconstructed counterexamples in `tests_rat_false_add_axioms.rs` /
/// `algebra_rat_le_trans_proof.rs` for the order axioms):
/// - `Rat.le_antisymm`         — `le a b → le b a → a = b`; junk `a = mk 0 0`,
///   `b = mk 0 2` make both `le` true (≡ `Int.le 0 0`) yet `a ≠ b`.
/// - `Rat.add_le_add_left`     — denom-0 `c` collapses `Rat.add`'s denominator.
/// - `Rat.le_add_of_nonneg_right` — same `Rat.add` collapse.
/// - `Rat.zero_mul` / `Rat.mul_zero` — `mul _ (mk _ 0)` collapses denom to 0,
///   `mk _ 0 ≠ Rat.zero = mk 0 1`.
/// - `Rat.add_left_neg` / `Rat.add_neg_self` — `add (neg a) a` over `a = mk 1 0`
///   yields `mk _ 0 ≠ Rat.zero`.
/// - `Rat.add_right_cancel`    — denom-0 `b` makes `add a b ≡ add c b` for
///   distinct `a ≠ c`.
/// - `Rat.right_distrib`       — denom-0 operand desynchronizes the two sides.
/// - `Rat.mul_inv_cancel`      — `a = mk 1 0 ≠ 0`, but `mul a (inv a) ≠ one`.
// WS-A ATOMIC LIVE SWITCH: this list is now EMPTY. All ten `Rat.*` axioms that
// were FALSE over the free `Rat.mk : Int → Nat` carrier have been ELIMINATED to
// genuine `Declaration::Theorem`s over the quotient carrier
// `Rat := Quot Rat.Raw.Equiv` (which identifies equivalent representatives, so
// the structural-equality and order claims are TRUE). They are no longer
// admitted domain axioms, so the prevention gate finds ZERO refutable admitted
// Rat axioms. If a future change re-introduces a FALSE admitted `Rat.*` axiom,
// `test_no_unlisted_false_rat_axiom` fails loudly.
const KNOWN_FALSE_PENDING_QUOTIENT_FIX: &[&str] = &[];

/// Admitted `Rat.*` axioms that are TRUE on every well-formed representative and
/// are NOT refutable by the engine, because their conclusions wrap the
/// *uninterpreted* operators `Rat.min` / `Rat.max` (registered as bare
/// `Declaration::Axiom` with no reduction rule), so no closed instantiation
/// reduces to a decidable closed prop.
///
/// They are listed here purely to DOCUMENT the classification: together with
/// `KNOWN_FALSE_PENDING_QUOTIENT_FIX`, this list must cover every admitted
/// `Rat.*` name, so that introducing a new admitted `Rat.*` axiom forces a human
/// to classify it (see `test_every_admitted_rat_axiom_is_classified`).
const KNOWN_TRUE_ON_WELLFORMED: &[&str] = &[
    // `Rat.min` / `Rat.max` operators (type `Rat → Rat → Rat`, not props).
    "Rat.min",
    "Rat.max",
    // Their characterizing / lattice axioms (conclusions over uninterpreted
    // `Rat.min` / `Rat.max`, hence irreducible to a closed `Int.le`).
    "Rat.min_def",
    "Rat.min_def'",
    "Rat.max_def",
    "Rat.max_def'",
    "Rat.le_max_left",
    "Rat.le_max_right",
    "Rat.min_le_left",
    "Rat.min_le_right",
    "Rat.max_le",
    "Rat.le_min",
];

// ────────────────────────────── witnesses ──────────────────────────────

/// `Nat.succ^n Nat.zero`.
fn nat(n: u64) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..n {
        e = Expr::app(succ.clone(), e);
    }
    e
}

/// `Int.ofNat (Nat.succ^n Nat.zero)`.
fn of_nat(n: u64) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), nat(n))
}

/// `Int.negSucc (Nat.succ^n Nat.zero)` — the integer `-(n + 1)`.
fn neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        nat(n),
    )
}

/// `Rat.mk num denom`.
fn mk(num: Expr, denom: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [num, denom],
    )
}

/// Closed `Rat` witness battery: junk `denom = 0` representatives (the source of
/// unsoundness) interleaved with well-formed (`denom > 0`) ones.
fn rat_witnesses() -> Vec<Expr> {
    vec![
        // junk: denom = 0
        mk(of_nat(0), nat(0)),
        mk(of_nat(1), nat(0)),
        mk(of_nat(5), nat(0)),
        mk(neg_succ(0), nat(0)), // -1 / 0
        // well-formed: denom > 0
        mk(of_nat(0), nat(1)),
        mk(of_nat(1), nat(1)),
        mk(of_nat(0), nat(2)),
        mk(of_nat(2), nat(2)),
        mk(neg_succ(0), nat(1)), // -1 / 1
        mk(of_nat(3), nat(2)),
    ]
}

// ───────────────────────── prop truth decision ─────────────────────────

/// The type `Rat`.
fn rat_ty() -> Expr {
    Expr::const_(Name::from_string("Rat"), vec![])
}

/// Is `e` (the *domain* of a Pi binder) the type `Rat`? (A value binder, as
/// opposed to a hypothesis binder whose domain is a Prop.)
fn is_rat_value_binder(tc: &TypeChecker, e: &Expr) -> bool {
    tc.is_def_eq(e, &rat_ty())
}

/// Three-valued truth of a CLOSED proposition `p`, decided purely by kernel
/// reduction. `None` = not a shape this gate can decide (e.g. a prop over the
/// uninterpreted `Rat.min` / `Rat.max`).
///
/// Handled shapes:
/// - `Rat.le _ _` / `Int.le _ _`  → delta-reduces to `Int.NonNeg t`; provable
///   iff `t` is a nonneg numeral (`Int.ofNat k`), false iff negative
///   (`Int.negSucc k`).
/// - `@Eq Rat lhs rhs`            → provable iff `is_def_eq lhs rhs`, false iff
///   `lhs`, `rhs` reduce to distinct closed `Rat.mk` constructors.
/// - `Ne a b` ≡ `@Eq Rat a b → False` → provable iff the inner `Eq` is false,
///   false iff the inner `Eq` is provable.
fn prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    // `Ne` / negation: `Pi (_ : @Eq Rat a b) False` (non-dependent).
    if let ExprKind::Pi(_, dom, body) = p.kind() {
        if is_false_const(body) {
            // The hypothesis is `¬(Eq)`; it holds iff the inner Eq is false.
            return prop_truth(tc, dom).map(|t| !t);
        }
    }

    // `@Eq Rat lhs rhs`: peel the application spine.
    if let Some((head, args)) = const_app(p) {
        if head == "Eq" && args.len() == 3 {
            // args = [Rat, lhs, rhs]
            let lhs = tc.whnf(&args[1]);
            let rhs = tc.whnf(&args[2]);
            // Only decide when both sides are closed `Rat.mk` constructors.
            if is_rat_mk(&lhs) && is_rat_mk(&rhs) {
                return Some(tc.is_def_eq(&lhs, &rhs));
            }
            return None;
        }
    }

    // `Rat.le` / `Int.le` → `Int.NonNeg t`; decide the sign of `t`.
    let w = tc.whnf(p);
    if let ExprKind::App(f, arg) = w.kind() {
        if let ExprKind::Const(n, _) = f.kind() {
            if n.to_string() == "Int.NonNeg" {
                for k in 0..32u64 {
                    if tc.is_def_eq(arg, &of_nat(k)) {
                        return Some(true);
                    }
                    if tc.is_def_eq(arg, &neg_succ(k)) {
                        return Some(false);
                    }
                }
            }
        }
    }
    None
}

/// Is `e` the constant `False`?
fn is_false_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "False")
}

/// Is `e` an application whose head (after spine-walk) is `Rat.mk`?
fn is_rat_mk(e: &Expr) -> bool {
    let mut cur = e;
    while let ExprKind::App(f, _) = cur.kind() {
        cur = f;
    }
    matches!(cur.kind(), ExprKind::Const(n, _) if n.to_string() == "Rat.mk")
}

/// If `e` is `c a1 a2 ...` with `c` a constant, return `(const-name, [a1, ..])`.
fn const_app(e: &Expr) -> Option<(String, Vec<Expr>)> {
    let mut args = vec![];
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = f;
    }
    if let ExprKind::Const(n, _) = cur.kind() {
        args.reverse();
        Some((n.to_string(), args))
    } else {
        None
    }
}

// ───────────────────────── refutation engine ─────────────────────────

/// Peel the leading binders of an axiom type, classifying each as a `Rat`-value
/// binder or a hypothesis (Prop) binder, down to the conclusion.
struct Telescope {
    /// One entry per leading Pi binder, in order: `true` = `Rat`-value binder,
    /// `false` = hypothesis binder.
    is_value: Vec<bool>,
    /// The full axiom type (closed); instantiated per witness assignment.
    ty: Expr,
}

/// Walk the type's leading Pi binders. We only descend through binders whose
/// domain is either `Rat` (value) or a closed prop with no dependence on a
/// *value* binder we have not yet bound — which holds for every axiom here, as
/// hypotheses mention only already-bound `Rat` values. The number of `Rat`
/// value binders bounds the witness search.
fn telescope(tc: &TypeChecker, ty: &Expr) -> Telescope {
    let mut is_value = vec![];
    let mut cur = ty.clone();
    // Substitute each binder with a sentinel only to peek at the NEXT domain's
    // shape (value vs prop). We re-walk from scratch during instantiation, so
    // the sentinel here is harmless.
    let sentinel = mk(of_nat(0), nat(0));
    loop {
        let w = tc.whnf(&cur);
        match w.kind() {
            ExprKind::Pi(_, dom, body) => {
                is_value.push(is_rat_value_binder(tc, dom));
                cur = body.instantiate(&sentinel);
            }
            _ => break,
        }
    }
    Telescope {
        is_value,
        ty: ty.clone(),
    }
}

/// Instantiate the telescope's value binders with `assignment` (one witness per
/// value binder, in binder order), discharging hypothesis binders with a closed
/// sentinel, and return `(hypotheses, conclusion)`.
fn instantiate(tele: &Telescope, assignment: &[Expr]) -> (Vec<Expr>, Expr) {
    let sentinel = mk(of_nat(0), nat(0));
    let mut hyps = vec![];
    let mut cur = tele.ty.clone();
    let mut value_idx = 0usize;
    for &is_val in &tele.is_value {
        match cur.kind() {
            ExprKind::Pi(_, dom, body) => {
                if is_val {
                    let v = assignment[value_idx].clone();
                    value_idx += 1;
                    cur = body.instantiate(&v);
                } else {
                    hyps.push((**dom).clone());
                    cur = body.instantiate(&sentinel);
                }
            }
            _ => break,
        }
    }
    (hyps, cur)
}

/// Decide whether an admitted axiom of the given `ty` is REFUTABLE: there is an
/// assignment of closed `Rat` witnesses to its value binders under which every
/// hypothesis reduces to a PROVABLE closed prop and the conclusion reduces to a
/// FALSE closed prop.
fn is_refutable(tc: &TypeChecker, ty: &Expr) -> bool {
    let tele = telescope(tc, ty);
    let n_values = tele.is_value.iter().filter(|&&v| v).count();
    // Operators like `Rat.min : Rat → Rat → Rat` have no prop conclusion: their
    // "conclusion" is `Rat`, never false. Such axioms simply never satisfy the
    // condition below, so they are (correctly) non-refutable.
    if n_values == 0 {
        // No value binder to vary: still check the (closed) conclusion once.
        let (hyps, concl) = instantiate(&tele, &[]);
        return hyps.iter().all(|h| prop_truth(tc, h) == Some(true))
            && prop_truth(tc, &concl) == Some(false);
    }

    let wits = rat_witnesses();
    // Cartesian product of witnesses over the value binders. The arity is small
    // (≤ 3 for every Rat axiom here), so this stays well-bounded.
    let mut assignment = vec![wits[0].clone(); n_values];
    let mut idx = vec![0usize; n_values];
    loop {
        for (slot, &i) in idx.iter().enumerate() {
            assignment[slot] = wits[i].clone();
        }
        let (hyps, concl) = instantiate(&tele, &assignment);
        let hyps_provable = hyps.iter().all(|h| prop_truth(tc, h) == Some(true));
        if hyps_provable && prop_truth(tc, &concl) == Some(false) {
            return true;
        }

        // increment the mixed-radix counter
        let mut pos = 0usize;
        loop {
            if pos == n_values {
                return false; // exhausted
            }
            idx[pos] += 1;
            if idx[pos] < wits.len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
        }
    }
}

// ─────────────────────────────── env ───────────────────────────────

/// Build an environment in which every admitted `Rat.*` axiom is registered.
/// `init_nn_verify_interval_arith_proofs` transitively pulls in the ordered
/// field axioms, the field instance, the linear order (incl. `Rat.le_antisymm`),
/// and the min/max lattice axioms; `init_nn_verify_rat_ordering` adds
/// `Rat.add_neg_self`.
fn env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    env.init_nn_verify_rat_ordering()
        .expect("init_nn_verify_rat_ordering");
    env
}

/// The admitted `Rat.*` axiom names that are actually registered in `env()`.
fn present_admitted_rat_axioms(env: &Environment) -> Vec<&'static str> {
    ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .filter(|n| n.starts_with("Rat."))
        .filter(|n| env.get_const(&Name::from_string(n)).is_some())
        .collect()
}

// ─────────────────────────────── tests ───────────────────────────────

/// The CORE prevention gate: every admitted `Rat.*` axiom that the refutation
/// engine finds FALSE-on-the-free-carrier must be on the
/// `KNOWN_FALSE_PENDING_QUOTIENT_FIX` allowlist. A refutable axiom NOT on the
/// allowlist is a newly-introduced false axiom — FAIL LOUDLY.
#[test]
fn test_no_unlisted_false_rat_axiom() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let mut refutable = vec![];
    for name in present_admitted_rat_axioms(&env) {
        let info = env
            .get_const(&Name::from_string(name))
            .expect("present axiom");
        if is_refutable(&tc, &info.type_) {
            refutable.push(name);
        }
    }

    let unlisted: Vec<&str> = refutable
        .iter()
        .copied()
        .filter(|n| !KNOWN_FALSE_PENDING_QUOTIENT_FIX.contains(n))
        .collect();

    assert!(
        unlisted.is_empty(),
        "SOUNDNESS REGRESSION: newly-introduced FALSE admitted Rat axiom(s) over \
         the junk `Rat.mk : Int → Nat` carrier: {unlisted:?}. Each is refutable \
         (a witness tuple makes every hypothesis a provable closed prop while the \
         conclusion reduces to a FALSE closed prop). Do NOT silence this by \
         adding the name to KNOWN_FALSE_PENDING_QUOTIENT_FIX unless it is a \
         deliberate, tracked admitted axiom pending the quotient-carrier fix — a \
         false axiom is exploitable to derive `False`."
    );
}

/// Dual pin: the allowlist is REAL — every name on
/// `KNOWN_FALSE_PENDING_QUOTIENT_FIX` is (a) still an admitted domain axiom and
/// (b) genuinely refutable by the engine. If the quotient-carrier fix turns one
/// into a theorem (removing it from `ADMITTED_DOMAIN_AXIOMS`), this fails and
/// forces the stale allowlist entry to be deleted.
#[test]
fn test_allowlist_entries_are_admitted_and_refutable() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    for &name in KNOWN_FALSE_PENDING_QUOTIENT_FIX {
        assert!(
            ADMITTED_DOMAIN_AXIOMS.contains(&name),
            "{name} is on the known-false allowlist but is no longer an admitted \
             domain axiom; if the quotient-carrier fix proved it, remove it from \
             KNOWN_FALSE_PENDING_QUOTIENT_FIX"
        );
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered in env()"));
        assert!(
            is_refutable(&tc, &info.type_),
            "{name} is on the known-false allowlist but is NOT refutable by the \
             engine — the counterexample search or the axiom shape changed"
        );
    }
}

/// Forces a human to CLASSIFY every admitted `Rat.*` axiom: each must be either
/// known-false (allowlisted) or documented-true-on-wellformed. A new admitted
/// `Rat.*` axiom that is neither fails here, even if the engine happens not to
/// refute it (e.g. a new uninterpreted-operator axiom).
#[test]
fn test_every_admitted_rat_axiom_is_classified() {
    let env = env();
    let mut unclassified = vec![];
    for name in present_admitted_rat_axioms(&env) {
        let known_false = KNOWN_FALSE_PENDING_QUOTIENT_FIX.contains(&name);
        let known_true = KNOWN_TRUE_ON_WELLFORMED.contains(&name);
        if !known_false && !known_true {
            unclassified.push(name);
        }
    }
    assert!(
        unclassified.is_empty(),
        "unclassified admitted Rat axiom(s): {unclassified:?}. Classify each as \
         either KNOWN_FALSE_PENDING_QUOTIENT_FIX (false over the free carrier — \
         then verify the prevention gate refutes it) or KNOWN_TRUE_ON_WELLFORMED \
         (true on every well-formed representative)."
    );
}

/// The two allowlists are disjoint (no name is both known-false and
/// known-true) — a sanity guard on the classification.
#[test]
fn test_allowlists_disjoint() {
    for &name in KNOWN_FALSE_PENDING_QUOTIENT_FIX {
        assert!(
            !KNOWN_TRUE_ON_WELLFORMED.contains(&name),
            "{name} is on BOTH the known-false and known-true allowlists"
        );
    }
}

/// Engine self-check: the refutation engine must NOT be vacuously true. It must
/// (a) refute a hand-built FALSE Rat equation and (b) NOT refute a hand-built
/// TRUE Rat equation. Without this, a bug that makes `is_refutable` always-false
/// would silently pass `test_no_unlisted_false_rat_axiom`.
#[test]
fn test_engine_distinguishes_true_from_false() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let eq_rat = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [rat_ty(), lhs, rhs],
        )
    };
    let rat_le = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le"), vec![]),
            [lhs, rhs],
        )
    };

    // WS-A: over the QUOTIENT carrier `@Eq Rat (Quot.mk a)(Quot.mk b)` is no
    // longer decided by constructor `noConfusion` (Quot has no injectivity), so
    // the engine's three-valued decision applies to the order props that DO
    // delta-reduce to a closed `Int.le`. FALSE closed prop:
    // `Rat.le (mk 1 0)(mk 0 1)` ≡ `Int.le (1·1) (0·1)` ≡ `Int.le 1 0` (FALSE).
    let false_le = rat_le(mk(of_nat(1), nat(0)), mk(of_nat(0), nat(1)));
    assert_eq!(
        prop_truth(&tc, &false_le),
        Some(false),
        "engine must reduce `Rat.le (mk 1 0)(mk 0 1)` to FALSE"
    );

    // TRUE closed prop: `Rat.le (mk 0 1)(mk 1 1)` ≡ `Int.le 0 1` (TRUE).
    let true_le = rat_le(mk(of_nat(0), nat(1)), mk(of_nat(1), nat(1)));
    assert_eq!(
        prop_truth(&tc, &true_le),
        Some(true),
        "engine must reduce `Rat.le (mk 0 1)(mk 1 1)` to TRUE"
    );

    // A nullary axiom whose conclusion is a FALSE prop is refutable; one whose
    // conclusion is a TRUE prop is not.
    assert!(
        is_refutable(&tc, &false_le),
        "false closed Rat.le prop must be refutable"
    );
    assert!(
        !is_refutable(&tc, &true_le),
        "true closed Rat.le prop must NOT be refutable"
    );
    // `@Eq Rat (Quot.mk ..)(Quot.mk ..)` is genuinely undecidable by the engine
    // on the quotient (no constructor noConfusion), so it is NOT refutable —
    // the gate never reports a false-eq-axiom from a quotient `Eq` conclusion.
    let undecidable_eq = eq_rat(
        mk(of_nat(1), nat(0)),
        Expr::const_(Name::from_string("Rat.zero"), vec![]),
    );
    assert!(
        prop_truth(&tc, &undecidable_eq).is_none(),
        "on the quotient carrier `Eq Rat (mk 1 0) zero` is not engine-decidable"
    );
}

/// Negative control proving the gate would CATCH a newly-introduced false
/// `Rat.*` axiom *with binders* (not just a nullary one). Builds the bogus
/// quantified type `∀ a b : Rat, Rat.le a b` — obviously false (it claims every
/// pair is ordered) — and asserts the binder-instantiating engine refutes it.
/// This is the exact shape a careless new axiom would take; if a regression
/// broke `telescope` / `instantiate` so that quantified axioms were never
/// refuted, `test_no_unlisted_false_rat_axiom` could pass vacuously — this test
/// stops that.
#[test]
fn test_engine_catches_quantified_false_axiom() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat = rat_ty();
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);

    // ∀ a b : Rat, Rat.le a b   (BVar 1 = a, BVar 0 = b)
    let body = Expr::apps(rat_le, [Expr::bvar(1), Expr::bvar(0)]);
    let inner = Expr::pi(crate::expr::BinderInfo::Default, rat.clone(), body);
    let bogus = Expr::pi(crate::expr::BinderInfo::Default, rat, inner);

    assert!(
        is_refutable(&tc, &bogus),
        "the prevention engine must refute the quantified false axiom \
         `∀ a b : Rat, Rat.le a b` (e.g. a = mk 1 0, b = mk 0 1 ⇒ Rat.le a b is \
         a FALSE closed Int.le) — otherwise it could miss a new false Rat axiom"
    );
}

/// TCB-shrink Tier 1 regression gate: the `Rat.abs_nonneg` latent soundness
/// bug is FIXED, and would have been CAUGHT had the carrier been reducible.
///
/// Before Tier 1, `Rat.abs` was an `Opaque` identity carrier (`fun a => a`).
/// Under that body `Rat.abs_nonneg : ∀ q, Rat.le Rat.zero (Rat.abs q)` is
/// SEMANTICALLY `∀ q, Rat.le 0 q` — FALSE for `q < 0`. It evaded the prevention
/// engine ONLY because opacity blocked the conclusion from reducing.
///
/// This test makes the bug explicit by building the conclusion over the two
/// carrier bodies directly (so the engine can reduce them). The OLD identity
/// body gives `∀ q, Rat.le 0 (id q)` ⇒ REFUTABLE; the NEW faithful body gives
/// `∀ q, Rat.le 0 (max q (-q))` ⇒ NON-refutable. It also pins that the LIVE
/// `Rat.abs_nonneg` is now a constructive Theorem (not an admitted axiom), so
/// it is no longer part of the trusted base at all.
#[test]
fn test_rat_abs_nonneg_old_identity_carrier_was_refutable_now_fixed() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat = rat_ty();
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    let rat_max = Expr::const_(Name::from_string("Rat.max"), vec![]);

    // OLD carrier body: identity `fun a => a`, so `abs q ≡ q`.
    // Bogus claim: ∀ q, Rat.le 0 q  (BVar 0 = q). FALSE for q = -1/1.
    let old_concl = Expr::apps(rat_le.clone(), [rat_zero.clone(), Expr::bvar(0)]);
    let old_ty = Expr::pi(crate::expr::BinderInfo::Default, rat.clone(), old_concl);
    assert!(
        is_refutable(&tc, &old_ty),
        "the OLD identity-carrier `Rat.abs_nonneg` (≡ ∀ q, 0 ≤ q) MUST be \
         refutable — that was the latent soundness bug, masked only by the \
         carrier's opacity. If this stops being refutable the witness battery \
         lost its negative `Rat` representatives."
    );

    // NEW faithful carrier body: `max q (-q)`, so `abs q ≡ Rat.max q (Rat.neg q)`.
    // Claim: ∀ q, Rat.le 0 (Rat.max q (Rat.neg q)) — genuinely TRUE, so the
    // engine must NOT refute it (it either proves it true per witness or, where
    // the order is undecidable, returns None; never a false conclusion).
    let neg_q = Expr::app(rat_neg, Expr::bvar(0));
    let abs_q = Expr::apps(rat_max, [Expr::bvar(0), neg_q]);
    let new_concl = Expr::apps(rat_le, [rat_zero, abs_q]);
    let new_ty = Expr::pi(crate::expr::BinderInfo::Default, rat, new_concl);
    assert!(
        !is_refutable(&tc, &new_ty),
        "the NEW faithful-carrier `Rat.abs_nonneg` (∀ q, 0 ≤ max q (-q)) MUST \
         NOT be refutable — it is true in the intended model. A refutation here \
         would mean the `Rat.max q (Rat.neg q)` carrier is itself unsound."
    );

    // The LIVE lemma is now a constructive Theorem, fully off the trusted base.
    let info = env
        .get_const(&Name::from_string("Rat.abs_nonneg"))
        .expect("Rat.abs_nonneg must be registered");
    assert_eq!(
        info.kind,
        crate::env::types::ConstantKind::Theorem,
        "Rat.abs_nonneg must be a kernel-checked Theorem after TCB-shrink Tier 1, \
         not an admitted axiom; got {:?}",
        info.kind
    );
    assert!(
        !ADMITTED_DOMAIN_AXIOMS.contains(&"Rat.abs_nonneg"),
        "Rat.abs_nonneg must not appear in ADMITTED_DOMAIN_AXIOMS once proven"
    );
}

/// Pins that the comprehensive `env()` actually registers ALL admitted `Rat.*`
/// axioms (so the gate has full coverage and is not silently skipping any).
#[test]
fn test_env_covers_all_admitted_rat_axioms() {
    let env = env();
    let missing: Vec<&str> = ADMITTED_DOMAIN_AXIOMS
        .iter()
        .copied()
        .filter(|n| n.starts_with("Rat."))
        .filter(|n| env.get_const(&Name::from_string(n)).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "env() fails to register admitted Rat axioms {missing:?}; the prevention \
         gate would not see them — extend the init chain in env()"
    );
}

// ═════════════════════════════════════════════════════════════════════════
// PREVENTION GATE — `NNVerify.IntervalBounds` carrier
// ═════════════════════════════════════════════════════════════════════════
//
// The `NNVerify.IntervalArith.*` interval theorems live over the
// `NNVerify.IntervalBounds` carrier:
//
//   IntervalBounds.mk {d} (lower upper : NNVec d)
//                         (valid : ∀ i, Rat.le (lower i) (upper i)) : IB d
//   NNVec d            := Fin d → Rat
//   contains B x       := ∀ i, Rat.le (B.lo i)(x i) ∧ Rat.le (x i)(B.hi i)
//
// Even though the `valid` field forces `lo ≤ hi` (so junk *intervals* are
// excluded), an admitted `IntervalArith.*` axiom can still be FALSE — its
// conclusion may quantify over a SPURIOUS result interval (`am_gm`'s `∀ R,
// contains A x → contains R x`) or rest on a false sub-axiom (`mul`'s validity
// via `mul_valid_helper`). Those holes were closed (the 8 ex-axioms became
// honest Theorems), and this gate locks the closure in: any admitted
// `NNVerify.IntervalArith.*` axiom that is REFUTABLE over closed `IntervalBounds`
// / `NNVec` witnesses must be on the (currently EMPTY) allowlist below.
//
// Engine: instantiate `{d := 1}`, give every `IB 1` value binder a closed
// point-interval witness `[v,v]` (valid via `Rat.le_refl v`) and every `NNVec 1`
// binder a constant vector `fun _ => w`, discharge `contains`-hypothesis binders
// when they reduce to TRUE, and report refutable iff some assignment makes every
// hypothesis a TRUE closed prop while the conclusion `contains R x` reduces to a
// FALSE closed prop (a component `Rat.le` that delta-reduces to a false
// `Int.le`). Point intervals suffice to expose the `am_gm`-style false `R`
// (`A=[1,1]`, `R=[5,5]`, `x=[1]` ⇒ `5 ≤ 1`).

/// Admitted `NNVerify.IntervalArith.*` axioms known to be refutable over the
/// `IntervalBounds` carrier and deliberately retained pending a faithful carrier.
/// EMPTY: the 8 historically-false interval axioms (`interval_am_gm`,
/// `interval_bernstein`, `interval_cauchy_schwarz`, `interval_chebyshev`,
/// `interval_power_mean`, `interval_sturm`, `interval_mul_contains`,
/// `mul_valid_helper`) are now honest identity-containment Theorems / eliminated,
/// so the refutable-admitted set is empty.
const KNOWN_FALSE_INTERVAL_AXIOMS: &[&str] = &[];

/// `Nat.succ^n Nat.zero` as a bare `Nat` (not lifted to `Int`).
fn nat_lit(n: u64) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..n {
        e = Expr::app(succ.clone(), e);
    }
    e
}

/// A `Fin 1` element: `Fin.mk (n:=1) 0 True` (Clean's `Fin.mk` takes the bound
/// proposition as a value, not a proof, so this is closed).
fn fin1_zero() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            nat_lit(1),
            nat_lit(0),
            Expr::const_(Name::from_string("True"), vec![]),
        ],
    )
}

/// `fun (_ : Fin 1) => r` — a constant `NNVec 1`.
fn nnvec1_const(r: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat_lit(1));
    Expr::lam(crate::expr::BinderInfo::Default, fin1, r)
}

/// Closed point interval `[v, v] : IntervalBounds 1`, valid via `Rat.le_refl v`.
fn ib1_point(v: Expr) -> Expr {
    let fin1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat_lit(1));
    let valid = Expr::lam(
        crate::expr::BinderInfo::Default,
        fin1,
        Expr::app(
            Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            v.clone(),
        ),
    );
    Expr::apps(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
        [nat_lit(1), nnvec1_const(v.clone()), nnvec1_const(v), valid],
    )
}

/// Closed `Rat` scalar `Rat.mk (Int.ofNat n) 1`.
fn rat_nat(n: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [of_nat(n), nat_lit(1)],
    )
}

/// Battery of closed `Rat` scalars used to build point-interval / vector
/// witnesses. A spread of distinct nonneg values is enough to break any spurious
/// `contains R x` (pick `R = [hi,hi]`, `x = [lo]` with `hi > lo`).
fn rat_scalars() -> Vec<Expr> {
    vec![rat_nat(0), rat_nat(1), rat_nat(5)]
}

/// Three-valued truth of a closed `contains B x` proposition for `d = 1`:
/// reduce to `∀ i, And (Rat.le (B.lo i)(x i)) (Rat.le (x i)(B.hi i))`,
/// instantiate at the single index, and AND the two `Rat.le` decisions.
fn contains_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    let w = tc.whnf(p);
    let body = match w.kind() {
        ExprKind::Pi(_, _, body) => (**body).clone(),
        _ => return None,
    };
    let inst = tc.whnf(&body.instantiate(&fin1_zero()));
    // inst should be `And L R`.
    let (head, args) = const_app(&inst)?;
    if head != "And" || args.len() != 2 {
        return None;
    }
    match (prop_truth(tc, &args[0]), prop_truth(tc, &args[1])) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) | (_, Some(false)) => Some(false),
        _ => None,
    }
}

/// Generalized closed-prop truth over BOTH carriers: a `contains` prop, or a
/// bare `Rat.le` / `Int.le` prop (delegating to the Rat-carrier `prop_truth`).
fn interval_prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    if let Some((head, _)) = const_app(p) {
        if head == "NNVerify.IntervalBounds.contains" {
            return contains_truth(tc, p);
        }
    }
    prop_truth(tc, p)
}

/// One leading-binder classification for the interval telescope.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IvKind {
    /// `Nat` value binder (the implicit dimension `{d}`) — fixed to `1`.
    Dim,
    /// `IntervalBounds d` value binder — varied over point-interval witnesses.
    Interval,
    /// `NNVec d` value binder — varied over constant-vector witnesses.
    Vec,
    /// Hypothesis binder (a Prop, e.g. `contains A x`) — discharged.
    Hyp,
    /// Any other binder shape (the gate cannot handle it → axiom skipped).
    Other,
}

fn interval_binder_kind(tc: &TypeChecker, dom: &Expr) -> IvKind {
    if tc.is_def_eq(dom, &Expr::const_(Name::from_string("Nat"), vec![])) {
        return IvKind::Dim;
    }
    let one = nat_lit(1);
    let ib1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        one.clone(),
    );
    let vec1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
        one,
    );
    if tc.is_def_eq(dom, &ib1) {
        return IvKind::Interval;
    }
    if tc.is_def_eq(dom, &vec1) {
        return IvKind::Vec;
    }
    // A hypothesis binder's domain is a Prop; the only props the axioms use are
    // `contains _ _` (and reducible `Rat.le`). Treat any Sort-0 domain as a Hyp.
    match tc.infer_type(dom).map(|t| tc.whnf(&t)) {
        Ok(s) if matches!(s.kind(), ExprKind::Sort(l) if l.is_zero()) => IvKind::Hyp,
        _ => IvKind::Other,
    }
}

/// Is the interval axiom of the given `ty` REFUTABLE over the `IntervalBounds`
/// carrier? Fixes `{d := 1}`, varies `IB 1` / `NNVec 1` binders over the witness
/// batteries, discharges `contains`-hypotheses that reduce to TRUE, and reports
/// `true` iff some assignment leaves every hypothesis TRUE and the conclusion a
/// FALSE closed prop.
fn interval_is_refutable(tc: &TypeChecker, ty: &Expr) -> bool {
    // Walk the leading binders, fixing `{d := 1}` and collecting the kinds of the
    // remaining value binders (Interval / Vec) in order. Hypotheses and the
    // conclusion are re-derived per assignment.
    let one = nat_lit(1);
    let mut kinds = vec![];
    {
        // Peel the SYNTACTIC leading Pi binders only (no whnf on `cur`): the
        // explicit `{d}(A)(R)(x)(hyp)` binders are syntactic Pis, while the
        // conclusion `contains R x` is an `App` (it only unfolds to a `∀ i:Fin`
        // forall under whnf) — so this naturally stops at the conclusion.
        let mut cur = ty.clone();
        while let ExprKind::Pi(_, dom, body) = cur.kind() {
            let k = interval_binder_kind(tc, dom);
            if k == IvKind::Other {
                return false; // unhandled shape — do not claim refutable
            }
            let inst = match k {
                IvKind::Dim => one.clone(),
                IvKind::Interval => ib1_point(rat_nat(0)),
                IvKind::Vec => nnvec1_const(rat_nat(0)),
                IvKind::Hyp => Expr::const_(Name::from_string("True.intro"), vec![]),
                IvKind::Other => unreachable!(),
            };
            if matches!(k, IvKind::Interval | IvKind::Vec) {
                kinds.push(k);
            }
            cur = body.instantiate(&inst);
        }
    }

    let n_slots = kinds.len();
    let scalars = rat_scalars();
    if n_slots == 0 {
        // No interval/vector binder to vary: decide the (closed) conclusion once.
        let (hyps, concl) = interval_instantiate(tc, ty, &[], &one);
        return hyps
            .iter()
            .all(|h| interval_prop_truth(tc, h) == Some(true))
            && interval_prop_truth(tc, &concl) == Some(false);
    }

    // Cartesian product over the value slots, each ranging over scalar witnesses
    // (an Interval slot becomes `[s,s]`; a Vec slot becomes `fun _ => s`).
    let mut idx = vec![0usize; n_slots];
    loop {
        let assignment: Vec<Expr> = kinds
            .iter()
            .zip(&idx)
            .map(|(k, &i)| match k {
                IvKind::Interval => ib1_point(scalars[i].clone()),
                IvKind::Vec => nnvec1_const(scalars[i].clone()),
                _ => unreachable!(),
            })
            .collect();
        let (hyps, concl) = interval_instantiate(tc, ty, &assignment, &one);
        let hyps_true = hyps
            .iter()
            .all(|h| interval_prop_truth(tc, h) == Some(true));
        if hyps_true && interval_prop_truth(tc, &concl) == Some(false) {
            return true;
        }
        // mixed-radix increment
        let mut pos = 0usize;
        loop {
            if pos == n_slots {
                return false;
            }
            idx[pos] += 1;
            if idx[pos] < scalars.len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
        }
    }
}

/// Instantiate the interval-axiom telescope: `{d := dim}`, each Interval/Vec
/// value binder with the next `assignment` entry, hypothesis binders discharged
/// with a sentinel; return `(hypotheses, conclusion)`.
fn interval_instantiate(
    tc: &TypeChecker,
    ty: &Expr,
    assignment: &[Expr],
    dim: &Expr,
) -> (Vec<Expr>, Expr) {
    let sentinel = Expr::const_(Name::from_string("True.intro"), vec![]);
    let mut hyps = vec![];
    let mut cur = ty.clone();
    let mut slot = 0usize;
    // Peel SYNTACTIC leading Pi binders only (see `interval_is_refutable`): do NOT
    // whnf `cur`, or the `contains R x` conclusion would unfold into a `∀ i:Fin`
    // forall and be mis-peeled as another binder.
    while let ExprKind::Pi(_, dom, body) = cur.kind() {
        let dom = (**dom).clone();
        let body = (**body).clone();
        match interval_binder_kind(tc, &dom) {
            IvKind::Dim => cur = body.instantiate(dim),
            IvKind::Interval | IvKind::Vec => {
                let v = assignment[slot].clone();
                slot += 1;
                cur = body.instantiate(&v);
            }
            IvKind::Hyp => {
                hyps.push(dom);
                cur = body.instantiate(&sentinel);
            }
            IvKind::Other => break,
        }
    }
    (hyps, cur)
}

/// All admitted (`Axiom`-kind) `NNVerify.IntervalArith.*` constants in `env`.
fn present_admitted_interval_axioms(env: &Environment) -> Vec<String> {
    use super::types::ConstantKind;
    let mut v: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| c.name.to_string())
        .filter(|n| n.starts_with("NNVerify.IntervalArith."))
        .collect();
    v.sort();
    v
}

// ───────────────────── interval-carrier gate tests ─────────────────────

/// CORE interval gate: every admitted `NNVerify.IntervalArith.*` axiom that the
/// engine finds refutable over the `IntervalBounds` carrier must be on the
/// (empty) `KNOWN_FALSE_INTERVAL_AXIOMS` allowlist. A refutable admitted interval
/// axiom NOT on the allowlist is a newly-introduced false interval axiom.
#[test]
fn test_no_unlisted_false_interval_axiom() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let mut refutable = vec![];
    for name in present_admitted_interval_axioms(&env) {
        let info = env
            .get_const(&Name::from_string(&name))
            .expect("present axiom");
        if interval_is_refutable(&tc, &info.type_) {
            refutable.push(name);
        }
    }

    let unlisted: Vec<&String> = refutable
        .iter()
        .filter(|n| !KNOWN_FALSE_INTERVAL_AXIOMS.contains(&n.as_str()))
        .collect();

    assert!(
        unlisted.is_empty(),
        "SOUNDNESS REGRESSION: newly-introduced FALSE admitted \
         NNVerify.IntervalArith.* axiom(s) over the IntervalBounds carrier: \
         {unlisted:?}. Each is refutable (closed IntervalBounds/NNVec witnesses \
         make every hypothesis a TRUE closed prop while the conclusion reduces to \
         a FALSE closed prop). Fix it honestly (add the missing nonneg/ordering \
         premise, or reformulate to identity containment as the 8 historical ones \
         were) — do NOT add the name to KNOWN_FALSE_INTERVAL_AXIOMS."
    );
}

/// The interval allowlist is REAL: every name on it is still an admitted interval
/// axiom AND genuinely refutable. (Empty today — this guards a future non-empty
/// allowlist from carrying a stale entry after a fix.)
#[test]
fn test_interval_allowlist_entries_are_admitted_and_refutable() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let present = present_admitted_interval_axioms(&env);
    for &name in KNOWN_FALSE_INTERVAL_AXIOMS {
        assert!(
            present.iter().any(|n| n == name),
            "{name} is on KNOWN_FALSE_INTERVAL_AXIOMS but is no longer an admitted \
             NNVerify.IntervalArith.* axiom; if it was proved/eliminated, remove it"
        );
        let info = env.get_const(&Name::from_string(name)).expect("present");
        assert!(
            interval_is_refutable(&tc, &info.type_),
            "{name} is allowlisted but the engine does not refute it — the \
             counterexample search or axiom shape changed"
        );
    }
}

/// The 8 historically-false interval axioms are now NON-refutable: each is an
/// honest `Theorem` (identity containment) and its type is NOT refutable. This is
/// the dual of `test_no_unlisted_false_rat_axiom`'s Rat self-check, pinning that
/// the WS-A-era false-interval hole stays closed.
#[test]
fn test_eight_historical_interval_axioms_are_now_sound_theorems() {
    use super::types::ConstantKind;
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Six reformulated to identity-containment Theorems; mul_contains too.
    let now_theorems = [
        "NNVerify.IntervalArith.interval_am_gm",
        "NNVerify.IntervalArith.interval_bernstein",
        "NNVerify.IntervalArith.interval_cauchy_schwarz",
        "NNVerify.IntervalArith.interval_chebyshev",
        "NNVerify.IntervalArith.interval_power_mean",
        "NNVerify.IntervalArith.interval_sturm",
        "NNVerify.IntervalArith.interval_mul_contains",
    ];
    for name in now_theorems {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} present"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be an honest Theorem after the false-axiom fix, got {:?}",
            info.kind
        );
        assert!(
            !interval_is_refutable(&tc, &info.type_),
            "{name} must NOT be refutable (its type is the TRUE identity \
             containment `contains A x → contains A x`)"
        );
    }

    // The false sub-axiom and its laundering Definition are gone.
    for gone in [
        "NNVerify.IntervalArith.mul_valid_helper",
        "NNVerify.IntervalArith.mul",
    ] {
        assert!(
            env.get_const(&Name::from_string(gone)).is_none(),
            "{gone} (false-axiom-backed) must stay eliminated"
        );
    }
}

/// Engine self-check: the interval engine must NOT be vacuously non-refuting. It
/// must REFUTE a hand-built false interval axiom (the exact `am_gm` shape
/// `∀ {d} (A R : IB d) (x : NNVec d), contains A x → contains R x`) and must NOT
/// refute the TRUE identity containment `∀ {d} (A : IB d) (x), contains A x →
/// contains A x`. Without this, a bug making `interval_is_refutable` always-false
/// would silently pass `test_no_unlisted_false_interval_axiom`.
#[test]
fn test_interval_engine_distinguishes_true_from_false() {
    use crate::expr::BinderInfo;
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let ib = Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]);
    let vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let contains = Expr::const_(
        Name::from_string("NNVerify.IntervalBounds.contains"),
        vec![],
    );

    let ib_at = |depth: u32| Expr::app(ib.clone(), Expr::bvar(depth));
    let vec_at = |depth: u32| Expr::app(vec.clone(), Expr::bvar(depth));

    // FALSE: `∀ {d} (A R : IB d) (x : NNVec d), contains A x → contains R x`.
    // Per-domain `d` index (binders below the domain): A→d=0, R→d=1, x→d=2,
    // hyp→d=3 (A=2, x=0), concl→d=4 (R=2, x=1).
    let bogus_false = {
        let hyp = Expr::apps(
            contains.clone(),
            [Expr::bvar(3), Expr::bvar(2), Expr::bvar(0)],
        );
        let concl = Expr::apps(
            contains.clone(),
            [Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)],
        );
        let body = Expr::pi(BinderInfo::Default, hyp, concl);
        let body = Expr::pi(BinderInfo::Default, vec_at(2), body); // x : NNVec d
        let body = Expr::pi(BinderInfo::Default, ib_at(1), body); // R : IB d
        let body = Expr::pi(BinderInfo::Default, ib_at(0), body); // A : IB d
        Expr::pi(BinderInfo::Implicit, nat.clone(), body) // {d : Nat}
    };
    assert!(
        interval_is_refutable(&tc, &bogus_false),
        "the interval engine must refute `∀ {{d}} (A R : IB d) (x), contains A x → \
         contains R x` (A=[0,0], R=[5,5], x=[0] ⇒ hyp `0≤0` true, concl `5≤0` false)"
    );

    // TRUE: identity containment `∀ {d} (A : IB d) (x), contains A x → contains A x`.
    // Per-domain `d`: A→d=0, x→d=1, hyp→d=2 (A=1, x=0), concl→d=3 (A=2, x=1).
    let identity_true = {
        let hyp = Expr::apps(
            contains.clone(),
            [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
        );
        let concl = Expr::apps(contains, [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)]);
        let body = Expr::pi(BinderInfo::Default, hyp, concl);
        let body = Expr::pi(BinderInfo::Default, vec_at(1), body); // x : NNVec d
        let body = Expr::pi(BinderInfo::Default, ib_at(0), body); // A : IB d
        Expr::pi(BinderInfo::Implicit, nat, body) // {d : Nat}
    };
    assert!(
        !interval_is_refutable(&tc, &identity_true),
        "the interval engine must NOT refute the TRUE identity containment \
         `∀ {{d}} (A : IB d) (x), contains A x → contains A x`"
    );
}

// ═════════════════════════════════════════════════════════════════════════
// PREVENTION GATE — `Fin` carrier (FAITHFUL: in-range indices only)
// ═════════════════════════════════════════════════════════════════════════
//
// After the faithful-carrier migration, Clean's `Fin` constructor is
//
//   Fin.mk : {n : Nat} → (val : Nat) → (isLt : Nat.lt val n) → Fin n   (data.rs)
//
// The `isLt` slot is now a genuine PROOF of `val < n`, so `Fin n` is inhabited
// ONLY by in-range indices (`Fin 0` is uninhabited; no element carries
// `val >= n`). The historical junk class (`Fin.mk _ _ True` with `val >= n`,
// `n = 0`) is GONE.
//
// What this gate guards now: an admitted axiom that universally quantifies over a
// `Fin n` value can still be FALSE on a genuinely IN-RANGE index. The gate ranges
// every `Fin n` binder over the real model (`val ∈ 0..n`, `fin_witnesses_for`)
// and reports an axiom refutable iff some in-range assignment makes every
// hypothesis a TRUE closed prop while the conclusion reduces to a FALSE closed
// prop. (`fin_witnesses_for` no longer enumerates `val >= n` junk witnesses:
// under the faithful carrier they are uninhabited, so enumerating them would
// FALSELY refute genuinely-true axioms.)
//
// THESIS FLIP for `Fin.sum_single`: pre-migration the `Nat.lt (Fin.val i) n`
// premise was LOAD-BEARING — it excluded the `Fin.mk _ _ True` junk witnesses
// under which the empty/all-zero sum falsely equalled a nonzero `x`. Over the
// faithful carrier `val < n` is derivable for every inhabited index (it is
// exactly `Fin.isLt i`), so the premise is now REDUNDANT rather than
// load-bearing, and the premise-free shape is no longer false. The engine's
// not-vacuous self-check (`test_fin_engine_distinguishes_false_from_true_inrange`)
// and the detector regression
// (`test_fin_detector_still_flags_known_false_axiom_over_faithful_carrier`)
// therefore use a DIFFERENT known-false axiom whose falseness survives the
// faithful carrier (a bound that fails at a real in-range index).
//
// Decision procedure. `Fin.sum_single`'s conclusion is an `@Eq Rat`, which is
// NOT decidable by constructor `noConfusion` on the WS-A quotient carrier
// `Rat := Quot Rat.Raw.Equiv`. We decide it instead through the ORDER BRIDGE:
// a closed `@Eq Rat a b` is FALSE when one of `Rat.le a b` / `Rat.le b a`
// delta-reduces to a FALSE closed `Int.le` (equal rationals satisfy `le` both
// ways, so a failing direction witnesses `a ≠ b`). Both directions reuse the
// Rat-carrier `prop_truth` (which decides `Rat.le` via `Int.NonNeg`).

/// A closed `Nat` literal `Nat.succ^k Nat.zero`.
fn fin_nat(k: u64) -> Expr {
    nat_lit(k)
}

/// A `Fin n` element `@Fin.mk n (val) True.intro`. Used ONLY as a reduction
/// witness (`fin_witnesses_for` supplies in-range `val < n` only). The `isLt`
/// proof slot is filled with the placeholder `True.intro`: the engine never
/// type-checks these witnesses, and every consumer (`Fin.val`, `ite`, `Fin.sum`)
/// ι-reduces on `val` alone, independent of the proof term, so the placeholder is
/// transparent to the decision procedure.
fn fin_mk(n: u64, val: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            fin_nat(n),
            fin_nat(val),
            Expr::const_(Name::from_string("True.intro"), vec![]),
        ],
    )
}

/// Three-valued truth of a CLOSED `@Eq Rat a b` proposition via the order
/// bridge: FALSE iff `Rat.le a b` or `Rat.le b a` reduces to a FALSE closed
/// `Int.le`; TRUE iff BOTH directions reduce to TRUE (antisymmetry on the
/// quotient ⇒ genuine equality); `None` otherwise. Works on the WS-A quotient
/// `Rat` where constructor `noConfusion` does not apply.
fn rat_eq_truth_via_order(tc: &TypeChecker, a: &Expr, b: &Expr) -> Option<bool> {
    let le = |lhs: &Expr, rhs: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le"), vec![]),
            [lhs.clone(), rhs.clone()],
        )
    };
    let ab = prop_truth(tc, &le(a, b));
    let ba = prop_truth(tc, &le(b, a));
    match (ab, ba) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

/// Decode a closed `Nat` to its value by reducing and matching `Nat.succ^k
/// Nat.zero` for small `k` (covers the gate's `{0..7}` witness range plus the
/// junk `val = n + 3`). Returns `None` for a non-literal / out-of-range nat.
fn decode_nat(tc: &TypeChecker, e: &Expr) -> Option<u64> {
    (0..=16u64).find(|&k| tc.is_def_eq(e, &fin_nat(k)))
}

/// Three-valued truth of a closed prop for the Fin gate:
/// - an `@Eq Rat` is decided via the order bridge;
/// - a closed `Nat.lt` / `Nat.le` is decided by decoding both nat literals (so
///   a TRUE in-range premise `Nat.lt v n` can actually be DISCHARGED, making the
///   gate able to reach — and refute — the conclusion of a hypothetical false
///   axiom that nonetheless carries a satisfiable in-range premise);
/// - otherwise delegate to the Rat-carrier `prop_truth` (`Rat.le` / `Int.le`,
///   `None` on quotient-undecidable shapes).
fn fin_prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    if let Some((head, args)) = const_app(p) {
        if head == "Eq" && args.len() == 3 {
            // args = [α, lhs, rhs]; only handle α = Rat.
            if tc.is_def_eq(&args[0], &rat_ty()) {
                return rat_eq_truth_via_order(tc, &args[1], &args[2]);
            }
        }
        if head == "Nat.le" && args.len() == 2 {
            let a = decode_nat(tc, &args[0])?;
            let b = decode_nat(tc, &args[1])?;
            return Some(a <= b);
        }
        if head == "Nat.lt" && args.len() == 2 {
            let a = decode_nat(tc, &args[0])?;
            let b = decode_nat(tc, &args[1])?;
            return Some(a < b);
        }
    }
    prop_truth(tc, p)
}

/// Leading-binder classification for a `Fin`-axiom telescope.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FinKind {
    /// `Nat` value binder — varied over `{0,1,2}`.
    Nat,
    /// `Fin <bound>` value binder — varied over in-range AND junk indices.
    Fin,
    /// `Rat` value binder — varied over the closed `Rat` witness battery.
    Rat,
    /// Hypothesis binder (a Prop) — discharged when it reduces to TRUE.
    Hyp,
    /// Unhandled shape (the axiom is skipped — not claimed refutable).
    Other,
}

/// Closed `Rat` witnesses for the Fin gate (well-formed only — the falseness we
/// hunt comes from the Fin junk index, not from Rat junk).
fn fin_rat_witnesses() -> Vec<Expr> {
    vec![
        mk(of_nat(0), nat(1)),
        mk(of_nat(1), nat(1)),
        mk(of_nat(5), nat(1)),
    ]
}

/// For a `Fin n` binder at a known `n`, the witness battery: every GENUINELY
/// IN-RANGE index `0..n` (i.e. `⟨val, proof⟩` with `val < n`), and NOTHING else.
///
/// FAITHFUL-CARRIER REWORK: `Fin.mk : {n} → (val) → (isLt : Nat.lt val n) → Fin n`
/// now requires a real proof of `val < n`, so a `Fin n` element is inhabited ONLY
/// for `val < n`. The pre-faithful battery also enumerated `val = n` / `val > n`
/// junk witnesses (`Fin.mk n (≥n) True`); those are now UNINHABITED, so including
/// them would FALSELY refute genuinely-true axioms (a junk index `⟨n, _⟩` that no
/// real `Fin n` value can take). We drop them: the engine ranges only over the
/// real model of `Fin n`. For `n = 0` the battery is EMPTY — `Fin 0` is
/// uninhabited, so any axiom quantifying over `Fin 0` is vacuously non-refutable
/// (correct: there is no `i : Fin 0` to make a conclusion false).
///
/// The `isLt` proof slot is filled with `True.intro` purely as a reduction
/// placeholder: the engine never type-checks these witnesses, and every consumer
/// (`Fin.val`, `ite`, `Fin.sum`) ι-reduces on `val` alone, independent of the
/// proof term. A genuinely-false axiom over the faithful carrier is exposed by an
/// in-range witness whose `val` makes the conclusion false (see the detector
/// regression test).
fn fin_witnesses_for(n: u64) -> Vec<Expr> {
    (0..n).map(|val| fin_mk(n, val)).collect()
}

/// Classify a leading-binder domain for the Fin telescope. The domain is
/// inspected AFTER earlier binders have been instantiated by the caller, so a
/// `Fin <bound>` domain already carries a concrete (closed) bound.
fn fin_binder_kind(tc: &TypeChecker, dom: &Expr) -> FinKind {
    if tc.is_def_eq(dom, &Expr::const_(Name::from_string("Nat"), vec![])) {
        return FinKind::Nat;
    }
    if tc.is_def_eq(dom, &rat_ty()) {
        return FinKind::Rat;
    }
    // `Fin <something>`: head is the `Fin` constant.
    let w = tc.whnf(dom);
    if let ExprKind::App(f, _) = w.kind() {
        if matches!(f.kind(), ExprKind::Const(nm, _) if nm.to_string() == "Fin") {
            return FinKind::Fin;
        }
    }
    // A Prop-typed domain is a hypothesis binder.
    match tc.infer_type(dom).map(|t| tc.whnf(&t)) {
        Ok(s) if matches!(s.kind(), ExprKind::Sort(l) if l.is_zero()) => FinKind::Hyp,
        _ => FinKind::Other,
    }
}

/// Does the type mention the constant `Fin` anywhere? (Cheap structural walk;
/// selects the axioms this gate is responsible for.)
fn type_mentions_fin(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n.to_string() == "Fin",
        ExprKind::App(f, a) => type_mentions_fin(f) || type_mentions_fin(a),
        ExprKind::Pi(_, d, b) | ExprKind::Lam(_, d, b) => {
            type_mentions_fin(d) || type_mentions_fin(b)
        }
        ExprKind::Let(_, t, v, b, _) => {
            type_mentions_fin(t) || type_mentions_fin(v) || type_mentions_fin(b)
        }
        _ => false,
    }
}

/// Is the `Fin`-axiom of type `ty` REFUTABLE over the `Fin.mk _ _ True` junk
/// carrier? Performs a bounded backtracking search over the leading binders:
/// `Nat` binders range over `{0,1,2}`, `Fin <bound>` binders over the in-range
/// plus junk index battery for the chosen bound, `Rat` binders over closed
/// rationals. Hypothesis binders are discharged only when they reduce to a TRUE
/// closed prop. The axiom is refutable iff some assignment makes every
/// hypothesis TRUE while the conclusion reduces to a FALSE closed prop.
fn fin_is_refutable(tc: &TypeChecker, ty: &Expr) -> bool {
    fn go(tc: &TypeChecker, cur: &Expr, depth: usize) -> bool {
        // Guard against pathological binder depth (every Fin axiom here is ≤ 5).
        if depth > 8 {
            return false;
        }
        let w = tc.whnf(cur);
        match w.kind() {
            ExprKind::Pi(_, dom, body) => {
                let kind = fin_binder_kind(tc, dom);
                let witnesses: Vec<Expr> = match kind {
                    FinKind::Nat => (0u64..=2).map(fin_nat).collect(),
                    FinKind::Fin => {
                        // The bound is the `Fin` application's argument.
                        let dw = tc.whnf(dom);
                        let bound = match dw.kind() {
                            ExprKind::App(_, a) => (**a).clone(),
                            _ => return false,
                        };
                        // Decode the concrete bound `n` (0..=4 covers our envs).
                        match (0..=4u64).find(|&k| tc.is_def_eq(&bound, &fin_nat(k))) {
                            Some(k) => fin_witnesses_for(k),
                            None => return false, // symbolic bound — skip
                        }
                    }
                    FinKind::Rat => fin_rat_witnesses(),
                    FinKind::Hyp => {
                        // Discharge with a sentinel ONLY if the hypothesis is a
                        // TRUE closed prop; otherwise this branch is vacuous.
                        if fin_prop_truth(tc, dom) == Some(true) {
                            let next = body.instantiate(&Expr::const_(
                                Name::from_string("True.intro"),
                                vec![],
                            ));
                            return go(tc, &next, depth + 1);
                        }
                        return false;
                    }
                    FinKind::Other => return false,
                };
                for wexpr in witnesses {
                    let next = body.instantiate(&wexpr);
                    if go(tc, &next, depth + 1) {
                        return true;
                    }
                }
                false
            }
            // Reached the conclusion: refutable iff it is a FALSE closed prop.
            _ => fin_prop_truth(tc, &w) == Some(false),
        }
    }
    go(tc, ty, 0)
}

/// Build a COMPREHENSIVE env registering the admitted `Fin`-mentioning axioms
/// across the NN-verification / boolean-analysis surfaces, so the Fin gate
/// scans the whole live set (not just `Fin.sum_*`): the `Fin.sum` family
/// (`init_fin_sum`), the interval-arith proofs (which pull in `Fin`-typed
/// `NNVec`/`IntervalBounds` carriers), the zonotope proofs (incl.
/// `sub_interval_hull`), the Rat-ordering NN axioms, and the boolean-analysis
/// Fourier axioms (incl. `fourier_coefficient_transform`, whose `Finset (Fin n)`
/// argument mentions `Fin`). Each `init_*` is idempotent and order-independent.
fn fin_env() -> Environment {
    let mut env = Environment::new();
    env.init_fin_sum().expect("init_fin_sum");
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    env.init_nn_verify_zonotope_proofs()
        .expect("init_nn_verify_zonotope_proofs");
    env.init_nn_verify_rat_ordering()
        .expect("init_nn_verify_rat_ordering");
    env.init_fourier_boolean().expect("init_fourier_boolean");
    env
}

/// All admitted (`Axiom`-kind) constants in `env` whose type mentions `Fin`.
fn present_admitted_fin_axioms(env: &Environment) -> Vec<String> {
    use super::types::ConstantKind;
    let mut v: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .filter(|c| type_mentions_fin(&c.type_))
        .map(|c| c.name.to_string())
        .collect();
    v.sort();
    v
}

/// Admitted `Fin`-mentioning axioms deliberately retained as refutable over the
/// junk `Fin.mk _ _ True` carrier. EMPTY after the `Fin.sum_single` fix (its
/// `Nat.lt (Fin.val i) n` premise excludes every junk witness), so the gate
/// finds ZERO refutable admitted Fin axioms.
///
/// Residual `Fin` carrier note: the `isLt : Prop` junk-admitting constructor is
/// STILL present (eliminating it would require re-foundationalizing `Fin` as a
/// `val < n` subtype, future work). The gate's guarantee is the live one: NO
/// admitted axiom is *refutable through* that junk — any new false Fin axiom
/// (e.g. dropping an in-range premise) is caught by `test_no_unlisted_false_fin_axiom`.
const KNOWN_FALSE_FIN_AXIOMS: &[&str] = &[];

// ───────────────────────── Fin-carrier gate tests ─────────────────────────

/// CORE Fin gate: every admitted `Fin`-mentioning axiom that the engine finds
/// refutable over the `Fin.mk _ _ True` junk carrier must be on the (empty)
/// `KNOWN_FALSE_FIN_AXIOMS` allowlist. A refutable admitted Fin axiom NOT on the
/// allowlist is a newly-introduced false axiom — FAIL LOUDLY.
#[test]
fn test_no_unlisted_false_fin_axiom() {
    let env = fin_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let mut refutable = vec![];
    for name in present_admitted_fin_axioms(&env) {
        let info = env
            .get_const(&Name::from_string(&name))
            .expect("present axiom");
        if fin_is_refutable(&tc, &info.type_) {
            refutable.push(name);
        }
    }

    let unlisted: Vec<&String> = refutable
        .iter()
        .filter(|n| !KNOWN_FALSE_FIN_AXIOMS.contains(&n.as_str()))
        .collect();

    assert!(
        unlisted.is_empty(),
        "SOUNDNESS REGRESSION: newly-introduced FALSE admitted Fin-carrier \
         axiom(s) over the junk `Fin.mk _ _ True` constructor: {unlisted:?}. Each \
         is refutable (a Fin-junk witness — `n = 0`, or `i.val >= n` — makes every \
         hypothesis a TRUE closed prop while the conclusion reduces to a FALSE \
         closed prop, e.g. an empty/all-zero `Fin.sum` falsely equal to a nonzero \
         `x`). Fix it honestly: add the missing in-range premise \
         `Nat.lt (Fin.val i) n` (as `Fin.sum_single` was fixed), prove it, or \
         eliminate it — do NOT add the name to KNOWN_FALSE_FIN_AXIOMS."
    );
}

/// `Fin.sum_single` is registered, is now a kernel-checked **Theorem** (the last
/// TCB `Fin` axiom was eliminated by a constructive proof — `Nat.rec` induction +
/// `Fin.lastCases` + `if_pos`/`if_neg` + `Fin.sum_congr`), and is specifically
/// NON-refutable. This dual self-check pins that the historical false-axiom hole
/// stays closed AND that the proven form carries no domain-specific axioms.
#[test]
fn test_fin_sum_single_is_now_sound_with_premise() {
    use super::types::ConstantKind;
    let env = fin_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let name = Name::from_string("Fin.sum_single");
    let info = env.get_const(&name).expect("Fin.sum_single registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Fin.sum_single is now a kernel-checked Theorem, not an admitted Axiom"
    );
    // Proven with ZERO domain-specific axioms.
    let deps = env.axiom_deps(&name).expect("registered");
    let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        names.is_empty(),
        "Fin.sum_single must be axiom-free (Constructive), got {names:?}"
    );
    // The type names `Fin` (so the gate covers it) and `Nat.lt` (the premise).
    assert!(
        type_mentions_fin(&info.type_),
        "Fin.sum_single's type must mention Fin"
    );
    assert!(
        !fin_is_refutable(&tc, &info.type_),
        "Fin.sum_single MUST be NON-refutable — over the faithful `Fin` carrier \
         every inhabited `Fin n` index is in range, so the single-nonzero-term sum \
         genuinely equals `x`. (Its `Nat.lt (Fin.val i) n` premise is now \
         redundant rather than load-bearing, but it does not make the statement false.)"
    );
}

/// Engine self-check: the Fin engine must NOT be vacuously non-refuting over the
/// FAITHFUL `Fin` carrier. It must REFUTE a hand-built false `Fin` axiom that is
/// false at a GENUINELY IN-RANGE index, and must NOT refute its true counterpart.
/// Without this, a bug making `fin_is_refutable` always-false would silently pass
/// `test_no_unlisted_false_fin_axiom`.
///
/// FAITHFUL-CARRIER NOTE (thesis flip): pre-migration this test refuted the
/// premise-free `Fin.sum_single` shape via the `n = 0` / `val >= n` junk witnesses
/// admitted by the `Fin.mk _ _ True` carrier. Those witnesses are now UNINHABITED
/// (`Fin 0` is empty; no `Fin n` element has `val >= n`), so the premise-free
/// `Fin.sum_single` is no longer false — its `Nat.lt (Fin.val i) n` premise
/// stopped being load-bearing once the carrier became faithful (`val < n` is now
/// derivable for every inhabited index, as `Fin.isLt`). The engine's "is it
/// vacuous?" self-check therefore uses a DIFFERENT known-false axiom whose
/// falseness survives the faithful carrier: a bound that fails at a real in-range
/// index.
#[test]
fn test_fin_engine_distinguishes_false_from_true_inrange() {
    use crate::expr::BinderInfo;
    let env = fin_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let fin_3 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat_lit(3));
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);

    // ∀ (i : Fin 3), Nat.lt (@Fin.val 3 i) BOUND
    let axiom_ty = |bound: u64| {
        let val_i = Expr::app(Expr::app(fin_val.clone(), nat_lit(3)), Expr::bvar(0));
        let concl = Expr::apps(nat_lt.clone(), [val_i, nat_lit(bound)]);
        Expr::pi(BinderInfo::Default, fin_3.clone(), concl)
    };

    // FALSE: bound = 2 fails at the in-range index ⟨2, _⟩ (`Nat.lt 2 2`).
    let false_ty = axiom_ty(2);
    assert!(
        fin_is_refutable(&tc, &false_ty),
        "the Fin engine MUST refute `∀ (i : Fin 3), Nat.lt (Fin.val i) 2` over the \
         faithful carrier — the in-range index ⟨2, _⟩ has Fin.val = 2, so \
         `Nat.lt 2 2` is FALSE. If non-refutable the engine is vacuous and could \
         miss a new false Fin axiom."
    );

    // TRUE: bound = 3 holds at every in-range index (`Nat.lt val 3`, val < 3).
    let true_ty = axiom_ty(3);
    assert!(
        !fin_is_refutable(&tc, &true_ty),
        "the Fin engine MUST NOT refute the TRUE `∀ (i : Fin 3), Nat.lt (Fin.val i) \
         3` — every inhabited Fin 3 index is in range (no junk `val >= n` witness \
         exists under the faithful carrier)"
    );

    // And the FIXED, live `Fin.sum_single` stays non-refutable.
    let fixed = env
        .get_const(&Name::from_string("Fin.sum_single"))
        .expect("Fin.sum_single registered")
        .type_
        .clone();
    assert!(
        !fin_is_refutable(&tc, &fixed),
        "the live `Fin.sum_single` must remain NON-refutable over the faithful \
         carrier (it is true for every inhabited in-range index)"
    );
}

/// The order-bridge `@Eq Rat` decision is honest: it returns `Some(false)` for a
/// genuinely-unequal closed pair (`Rat.zero` vs `1`) and `Some(true)` for an
/// equal one (`Rat.zero` vs `Rat.zero`).
#[test]
fn test_fin_rat_eq_order_bridge_distinguishes() {
    let env = fin_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let one = mk(of_nat(1), nat(1));

    assert_eq!(
        rat_eq_truth_via_order(&tc, &rat_zero, &one),
        Some(false),
        "the order bridge must reduce `Rat.zero = 1` to FALSE (Rat.le 1 0 is false)"
    );
    assert_eq!(
        rat_eq_truth_via_order(&tc, &rat_zero, &rat_zero),
        Some(true),
        "the order bridge must reduce `Rat.zero = Rat.zero` to TRUE (le both ways)"
    );
}

/// Pins that the Fin gate has coverage and that `Fin.sum_single` is now PROVEN.
///
/// `Fin.sum_single` was the last admitted TCB `Fin` axiom; it is now a
/// kernel-checked Theorem, so it no longer appears in the admitted-axiom set.
/// The gate is still broad: `fin_env()` surfaces several other Fin-mentioning
/// admitted axioms (the `NNVerify.*` / `BoolAnalysis.*` families), so it is not
/// silently scanning an empty set.
#[test]
fn test_fin_env_covers_fin_sum_single() {
    use super::types::ConstantKind;
    let env = fin_env();

    // `Fin.sum_single` is now a proven Theorem — NOT an admitted axiom.
    assert_eq!(
        env.get_const(&Name::from_string("Fin.sum_single"))
            .expect("Fin.sum_single registered")
            .kind,
        ConstantKind::Theorem,
        "Fin.sum_single must now be a kernel-checked Theorem (last TCB Fin axiom \
         eliminated)"
    );

    let present = present_admitted_fin_axioms(&env);
    assert!(
        !present.iter().any(|n| n == "Fin.sum_single"),
        "Fin.sum_single is proven, so it must NOT appear among admitted Fin \
         axioms; got {present:?}"
    );
    // The comprehensive env must still surface the remaining Fin-mentioning
    // admitted axioms, so the gate is not silently scanning an empty set.
    // This set SHRINKS as the zero-faith campaign proves axioms (by design):
    // `BoolAnalysis.influence_fourier` left it when it was retired to a
    // kernel-checked Theorem (2026-06-11). Pin the exact survivors so both
    // unexpected additions AND unnoticed disappearances are loud; update this
    // list deliberately on each retirement.
    // `NNVerify.ibp_linear_per_component` left this set when it graduated to a
    // kernel-checked Theorem (T80 unlock, 2026-06-11) off the
    // `ibp_linear_bounds` define.
    let mut expected = vec!["NNVerify.interval_subset_width".to_string()];
    expected.sort();
    let mut got = present.clone();
    got.sort();
    assert_eq!(
        got, expected,
        "fin_env()'s Fin-mentioning admitted-axiom set drifted; update this pin \
         deliberately (retirement = remove a name; addition = justify a new one)"
    );
}

/// FAITHFUL-CARRIER DETECTOR REGRESSION (mandate of the Fin-carrier migration):
/// after `Fin` became faithful (`isLt : Nat.lt val n` is a genuine PROOF, so
/// `Fin n` is inhabited ONLY by in-range indices), prove the refutation engine
/// STILL flags a KNOWN-FALSE `Fin` axiom — now via a genuinely in-range index,
/// not a `Fin.mk _ _ True` junk witness.
///
/// We register a deliberately false axiom into a scratch env and assert the
/// engine refutes it:
///
///   bad : ∀ (i : Fin 2), Nat.lt (Fin.val i) 1
///
/// This is FALSE: the genuinely in-range index `i = ⟨1, _⟩` (with `1 < 2`) has
/// `Fin.val i = 1`, so the conclusion `Nat.lt 1 1` is FALSE. The engine's
/// `fin_witnesses_for(2)` enumerates the in-range `⟨0,_⟩`, `⟨1,_⟩`; at `⟨1,_⟩`
/// the conclusion decodes (`fin_prop_truth`'s `Nat.lt` decoder) to `Some(false)`,
/// so `fin_is_refutable` returns `true`. If a regression made the engine
/// vacuously non-refuting (e.g. the carrier change broke `Fin.val` reduction on
/// the witnesses), THIS test fails loudly — the detector would otherwise miss a
/// real false Fin axiom. The dual control `good` (`∀ i : Fin 2, Nat.lt (Fin.val
/// i) 2`, TRUE) must NOT be refuted.
#[test]
fn test_fin_detector_still_flags_known_false_axiom_over_faithful_carrier() {
    let mut env = fin_env();

    let fin_2 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat_lit(2));
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);

    // ∀ (i : Fin 2), Nat.lt (@Fin.val 2 i) BOUND
    let mk_axiom_ty = |bound: u64| {
        let val_i = Expr::app(Expr::app(fin_val.clone(), nat_lit(2)), Expr::bvar(0));
        let concl = Expr::apps(nat_lt.clone(), [val_i, nat_lit(bound)]);
        Expr::pi(crate::expr::BinderInfo::Default, fin_2.clone(), concl)
    };

    // FALSE: bound = 1 (fails at the in-range index ⟨1, _⟩).
    let bad_ty = mk_axiom_ty(1);
    env.add_decl(super::Declaration::Axiom {
        name: Name::from_string("__regression_bad_fin_axiom"),
        level_params: vec![],
        type_: bad_ty.clone(),
    })
    .expect("bad Fin axiom type-checks (its type is well-formed; only FALSE)");

    // TRUE control: bound = 2 (Nat.lt (val i) 2 holds for every Fin 2 index).
    let good_ty = mk_axiom_ty(2);

    let tc = TypeChecker::with_mode(&env, env.mode());

    assert!(
        fin_is_refutable(&tc, &bad_ty),
        "DETECTOR REGRESSION: the refutation engine must STILL flag the known-false \
         `∀ (i : Fin 2), Nat.lt (Fin.val i) 1` over the faithful `Fin` carrier — \
         the genuinely in-range index ⟨1, _⟩ has Fin.val = 1, making `Nat.lt 1 1` \
         FALSE. If this is non-refutable, the faithful-carrier change has BROKEN \
         false-axiom detection (e.g. `Fin.val` no longer reduces on witnesses)."
    );
    assert!(
        !fin_is_refutable(&tc, &good_ty),
        "the engine must NOT refute the TRUE control `∀ (i : Fin 2), \
         Nat.lt (Fin.val i) 2` — every Fin 2 index is in range"
    );

    // And the live scan over `present_admitted_fin_axioms` must surface the planted
    // bad axiom as refutable-and-unlisted (it is registered as an admitted Axiom).
    let present = present_admitted_fin_axioms(&env);
    assert!(
        present.iter().any(|n| n == "__regression_bad_fin_axiom"),
        "the planted bad axiom must be in the admitted-Fin scan set; got {present:?}"
    );
    let refutable_unlisted: Vec<&String> = present
        .iter()
        .filter(|n| {
            let info = env.get_const(&Name::from_string(n)).expect("present axiom");
            fin_is_refutable(&tc, &info.type_)
        })
        .filter(|n| !KNOWN_FALSE_FIN_AXIOMS.contains(&n.as_str()))
        .collect();
    assert!(
        refutable_unlisted
            .iter()
            .any(|n| *n == "__regression_bad_fin_axiom"),
        "the live `test_no_unlisted_false_fin_axiom` logic must catch the planted \
         false axiom as refutable-and-unlisted; got {refutable_unlisted:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════
// RESOLUTION of the three formerly-UNCERTAIN admitted axioms
// ═════════════════════════════════════════════════════════════════════════
//
// Each was re-checked for refutability via closed witnesses and found SOUND
// (TRUE-but-admitted, not refutable by reduction), or ELIMINATED to a genuine
// kernel-checked Theorem. The verdicts:
//
// (1) `BoolAnalysis.fourier_coefficient_transform`  — ELIMINATED (TCB-shrink).
//     Formerly an admitted `Declaration::Axiom` whose conclusion was an
//     application of the UNINTERPRETED `fourier_coefficient_transform_helper`
//     axiom (no reduction rule, hence non-refutable — the documented residue).
//     It is now a genuine kernel-checked `Declaration::Theorem`
//       : ∀ n (f : BoolFn n)(S : HCPoint n),
//           BoolAnalysis.fourier_coefficient_transform_helper n f S
//     where the helper is a reducible `Declaration::Definition` carrying the
//     real `@Eq Rat (FourierCoefficient n f S) (FourierTransform n f S)`, proven
//     by `@Eq.refl` (the transform IS the coefficient family — definitional).
//     `ProofQuality::Constructive`, empty admitted-axiom closure. No longer part
//     of the trusted base / C4 admitted-axiom scan. See
//     `fourier_boolean_theorems.rs::register_fourier_coefficient_transform`.
//
// (2) The `cert_<prefix>_L<layer>_valid` per-certificate family
//       : ∀ (i : Fin d), Rat.le (lower i) (upper i)
//     generated by `nn_verify_cert_parser::bounds_to_expr`. `lower`/`upper` are
//     themselves bare `Declaration::Axiom`s of type `NNVec d` (uninterpreted
//     vectors — the certificate's concrete numeric values live in metadata, NOT
//     in the type). So `Rat.le (lower i)(upper i)` is stuck (irreducible) and
//     NOT refutable. It asserts well-formedness (`lo ≤ hi`) of an uninterpreted
//     bound vector, consistent under `lower := upper`. It is NOT laundering a
//     false per-layer claim — there is no false reducible content. SOUND.
//
// (3) `NNVerify.Zonotope.sub_interval_hull`
//       : {n k}(z : Zonotope n k)(x : NNVec n),
//           Zonotope.contains z x → IntervalBounds.contains (Zonotope.to_ibp z) x
//     `Zonotope.to_ibp` is a `Declaration::Opaque` (NOT δ-reduced during def-eq,
//     pinned by tests_nn_verify_zonotope_to_ibp_demasquerade_3591). So the
//     conclusion `contains (to_ibp z) x` is stuck on the opaque `to_ibp` and
//     CANNOT reduce to a closed false prop — NOT refutable by reduction. (The
//     interval-hull-superset statement is TRUE for a faithful `to_ibp`; the
//     opacity is the accepted mitigation for the placeholder zero-interval body.)
//     SOUND under the opaque carrier.

/// (1) `fourier_coefficient_transform` is ELIMINATED — now a genuine
/// kernel-checked `Declaration::Theorem` with a reducible-Definition helper
/// carrying the real `Eq`. Pins the new reality (Theorem + Definition, proof
/// type-checks, `Constructive`, empty axiom closure) so a regression that
/// re-admits it as an Axiom fails here.
#[test]
fn test_fourier_coefficient_transform_is_proven_theorem() {
    use super::types::ConstantKind;
    use super::ProofQuality;
    let mut env = Environment::new();
    env.init_fourier_boolean().expect("init_fourier_boolean");

    let helper = env
        .get_const(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform_helper",
        ))
        .expect("helper registered");
    assert_eq!(
        helper.kind,
        ConstantKind::Definition,
        "the helper is now a reducible Definition carrying the real \
         `Eq (FourierCoefficient n f S) (FourierTransform n f S)`, not an Axiom"
    );

    let thm = env
        .get_const(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform",
        ))
        .expect("fourier_coefficient_transform registered");
    assert_eq!(
        thm.kind,
        ConstantKind::Theorem,
        "fourier_coefficient_transform must be a kernel-checked Theorem, not an Axiom"
    );

    // Independent re-verification: the proof term type-checks against its type.
    let value = thm.value.clone().expect("proof present");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&value, &thm.type_)
        .expect("fourier_coefficient_transform proof must check against its type");

    // Constructive: empty admitted-axiom closure (bottoms out in the defined
    // FourierCoefficient / FourierTransform).
    assert_eq!(
        env.proof_quality(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform"
        )),
        Some(ProofQuality::Constructive),
        "fourier_coefficient_transform must be Constructive (no admitted-axiom dependency)"
    );
    assert!(
        env.axiom_deps(&Name::from_string(
            "BoolAnalysis.fourier_coefficient_transform"
        ))
        .expect("deps")
        .is_empty(),
        "fourier_coefficient_transform's transitive axiom closure must be empty"
    );
}

/// (2) A representative `cert_<prefix>_L<layer>_valid` axiom is generated with
/// type `∀ (i : Fin d), Rat.le (lower i)(upper i)` over UNINTERPRETED `lower` /
/// `upper` axioms, so its conclusion is irreducible and NON-refutable.
#[test]
fn test_cert_layer_valid_is_uninterpreted_not_refutable() {
    use super::types::ConstantKind;
    // The parser-emitted `cert_<prefix>_L<layer>_valid` family is exercised live
    // by tests_nn_cert_parser. Here we reproduce its EXACT structural shape from
    // `bounds_to_expr` — an in-range `valid` premise `∀ i, Rat.le (lower i)(upper
    // i)` over UNINTERPRETED bound vectors — on a minimal env, and assert it is
    // non-refutable. `NNVec d ≡ Fin d → Rat`, so we type the uninterpreted
    // vectors as `Fin 1 → Rat` directly (no NNVec registration needed).
    let mut env = Environment::new();
    env.init_fin().expect("init_fin");
    env.init_rat_ord().expect("init_rat_ord"); // Rat, Rat.le
    env.init_lt().expect("init_lt");
    let one = nat_lit(1);
    let fin_1 = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), one);
    let rat = rat_ty();
    let vec_ty = Expr::pi(crate::expr::BinderInfo::Default, fin_1.clone(), rat);
    for nm in ["__probe_cert_lower", "__probe_cert_upper"] {
        env.add_decl(super::Declaration::Axiom {
            name: Name::from_string(nm),
            level_params: vec![],
            type_: vec_ty.clone(),
        })
        .expect("register uninterpreted bound vector");
    }
    let lower = Expr::const_(Name::from_string("__probe_cert_lower"), vec![]);
    let upper = Expr::const_(Name::from_string("__probe_cert_upper"), vec![]);
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let valid_ty = Expr::pi(
        crate::expr::BinderInfo::Default,
        fin_1,
        Expr::apps(
            rat_le,
            [
                Expr::app(lower, Expr::bvar(0)),
                Expr::app(upper, Expr::bvar(0)),
            ],
        ),
    );
    env.add_decl(super::Declaration::Axiom {
        name: Name::from_string("__probe_cert_L0_valid"),
        level_params: vec![],
        type_: valid_ty.clone(),
    })
    .expect("register valid axiom");

    let info = env
        .get_const(&Name::from_string("__probe_cert_L0_valid"))
        .expect("present");
    assert_eq!(info.kind, ConstantKind::Axiom);

    // The conclusion `Rat.le (lower i)(upper i)` is stuck: `lower`/`upper` are
    // bare axioms, so neither projection reduces to a closed Rat — the Fin engine
    // cannot refute it. We confirm by instantiating the Fin binder with a junk
    // index and showing the resulting `Rat.le` is NOT engine-decidable (None).
    let tc = TypeChecker::with_mode(&env, env.mode());
    let concl = valid_ty.instantiate(&fin_mk(1, 0));
    assert_eq!(
        prop_truth(&tc, &concl),
        None,
        "cert_*_valid's `Rat.le (lower i)(upper i)` must be irreducible \
         (lower/upper uninterpreted), hence not refutable"
    );
    assert!(
        !fin_is_refutable(&tc, &valid_ty),
        "the cert_*_valid family must be NON-refutable over the Fin junk carrier \
         (uninterpreted bound vectors give no closed false conclusion)"
    );
}

/// (3) `NNVerify.Zonotope.sub_interval_hull` is `contains z x → contains (to_ibp z) x`
/// — the SAME statement as the now-proven `to_ibp_sound`. Once `to_ibp` became a
/// FAITHFUL reducible Definition (radius_i = Σ_j |G_ij|, lower/upper = center ∓ radius;
/// see `nn_verify_zonotope_to_ibp_faithful`), this admitted Axiom is sound for a
/// STRONGER reason than the old #3591 stopgap: its conclusion is now TRUE (the faithful
/// interval hull genuinely over-approximates the zonotope), so it is non-refutable even
/// though the conclusion now δ-reduces. The earlier mitigation ("to_ibp Opaque blocks
/// reduction → conclusion stuck → non-refutable") is obsolete; this guard now pins the
/// faithful reality + verifies non-refutability mechanically.
#[test]
fn test_sub_interval_hull_axiom_sound_under_faithful_to_ibp() {
    use super::types::ConstantKind;
    let mut env = Environment::new();
    env.init_nn_verify_zonotope_proofs()
        .expect("init_nn_verify_zonotope_proofs");

    let to_ibp = env
        .get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
        .expect("to_ibp registered");
    assert_eq!(
        to_ibp.kind,
        ConstantKind::Definition,
        "to_ibp is now the FAITHFUL reducible Definition (range projection \
         center ∓ Σ|G_ij|), not the retired zero-interval Opaque stopgap"
    );
    assert!(
        to_ibp.is_reducible,
        "faithful to_ibp is reducible (its soundness, to_ibp_sound, is proven, so \
         reducibility opens no masquerade — there is no false equation to mask)"
    );

    let hull = env
        .get_const(&Name::from_string("NNVerify.Zonotope.sub_interval_hull"))
        .expect("sub_interval_hull registered")
        .clone();
    assert_eq!(
        hull.kind,
        ConstantKind::Axiom,
        "sub_interval_hull is still an admitted Axiom in this env (= the proven \
         to_ibp_sound statement; a candidate for a future proof-retirement)"
    );

    // The soundness claim, now mechanical: the axiom's conclusion is TRUE under the
    // faithful to_ibp, so the false-axiom engine finds NO closed counterexample — it
    // is non-refutable even though to_ibp now δ-reduces (the old guarantee depended on
    // opacity blocking reduction; the new one is strictly stronger).
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        !fin_is_refutable(&tc, &hull.type_),
        "sub_interval_hull must remain NON-refutable under the faithful reducible \
         to_ibp (its conclusion reduces to a TRUE prop, no closed false instance)"
    );
}

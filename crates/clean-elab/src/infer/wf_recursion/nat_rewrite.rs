// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying rewriting of `Nat` terms, for the truncated-subtraction
//! tiers of the decreasing cascade.
//!
//! Two things live here.
//!
//! * **Term constructors** for the foundational pieces every tier in
//!   [`super::sub_elim`] names — `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.lt`, the
//!   `Eq` plumbing (`Eq.refl`, `Eq.trans`, `Eq.mp`, `Eq.mpr`, `congrArg`), and
//!   the raw-spelling conversion described below.
//! * [`ElabCtx::normalize_nat`] — a bounded, bottom-up normalizer that returns
//!   BOTH the normalized term and a proof `e = e'`. Every rewrite it fires is a
//!   named, axiom-free prelude `Theorem`; there is no `sorry`, no tactic, and
//!   no admitted step, so the whole normalization is auditable in the emitted
//!   term.
//!
//! # Why "raw spelling" first
//!
//! `a + b` elaborates to `@HAdd.hAdd Nat Nat Nat instHAdd a b`, while every
//! prelude lemma is stated over `Nat.add`. The two are definitionally equal
//! (the instance unfolds), so this module converts a term to the raw spelling
//! once, up front ([`to_raw_nat`]), and justifies the conversion with a
//! re-typed `Eq.refl`: the kernel accepts it exactly when the two terms are
//! genuinely def-eq, which is the soundness gate. Everything downstream then
//! matches syntactically against one spelling instead of two, and the linear
//! machinery in `crate::tactic::arith_linarith_nat_eq` sees the same terms the
//! rewrites produced.
//!
//! # The rewrite set
//!
//! Each rule is `shape → replacement`, backed by the named theorem in the
//! second column. All are constructive and axiom-free.
//!
//! | shape | becomes | theorem |
//! |---|---|---|
//! | `x - 0` | `x` | `Nat.sub_zero` |
//! | `x - x` | `0` | `Nat.sub_self` |
//! | `(p + q) - p` | `q` | `Nat.ulpRound.add_sub_cancel_left` |
//! | `(p + q) - q` | `p` | `Nat.ulpRound.add_sub_self_right` |
//! | `x - (x + q)` | `0` | `Nat.ulpRound.sub_eq_zero_of_le` + `Nat.le_add_right` |
//! | `x - (p + x)` | `0` | the same, through `Nat.add_comm` |
//! | `x - y` with `h : x ≤ y` in scope | `0` | `Nat.ulpRound.sub_eq_zero_of_le` |
//! | `x + 0` | `x` | `Nat.add_zero` |
//! | `0 + x` | `x` | `Nat.zero_add` |
//!
//! A missing theorem makes the corresponding rule abstain (the term is left
//! alone) rather than emit a proof naming a constant the kernel would reject.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::ElabCtx;
use crate::tactic::nat_expr_eval::eval_nat_expr;

/// How many outer normalization sweeps a single term gets. Each sweep is
/// bottom-up and already reaches a local fixpoint per node; the outer bound
/// only stops a pathological rule interaction from running away.
const NORMALIZE_SWEEPS: u32 = 6;

/// Every constant the rewrites and the `Eq` plumbing name. A tier gated on
/// this list disengages wholesale in an environment that lacks a piece, rather
/// than emitting a term the kernel would reject.
pub(super) const REQUIRED_CONSTANTS: &[&str] = &[
    "Nat",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.lt",
    "Nat.le",
    "Nat.zero",
    "Nat.succ",
    "Nat.add_zero",
    "Nat.zero_add",
    "Nat.sub_zero",
    "Nat.add_comm",
    "Nat.le_add_right",
    "Nat.le_trans",
    "Nat.le_total",
    "Nat.add_lt_add_left",
    "Nat.ulpRound.sub_eq_zero_of_le",
    "Nat.ulpRound.sub_add_cancel",
    "Nat.ulpRound.add_sub_cancel_left",
    "Nat.ulpRound.add_sub_self_right",
    "Eq",
    "Eq.refl",
    "Eq.trans",
    "Eq.mp",
    "Eq.mpr",
    "Or",
    "Or.rec",
    "congrArg",
];

pub(super) fn cst(name: &'static str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn nat_ty() -> Expr {
    cst("Nat")
}

pub(super) fn nzero() -> Expr {
    cst("Nat.zero")
}

pub(super) fn nadd(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.add"), [x, y])
}

pub(super) fn nsub(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.sub"), [x, y])
}

pub(super) fn nmul(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.mul"), [x, y])
}

pub(super) fn nlt(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.lt"), [x, y])
}

pub(super) fn nle(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Nat.le"), [x, y])
}

/// `@Eq.{1} Nat lhs rhs`.
pub(super) fn nat_eq_ty(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat_ty(), lhs, rhs],
    )
}

/// `@Eq.refl.{1} Nat a`. Used both reflexively and — deliberately — RE-TYPED at
/// a definitionally-equal pair, which the kernel accepts iff the two really are
/// def-eq (the soundness gate for the spelling conversion).
pub(super) fn mk_refl(a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a],
    )
}

/// `@Eq.trans.{1} Nat a b c h1 h2 : a = c`.
pub(super) fn eq_trans(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty(), a, b, c, h1, h2],
    )
}

/// `@congrArg.{1,1} Nat Nat a₁ a₂ f h : f a₁ = f a₂` for `f : Nat → Nat`.
pub(super) fn congr_arg_nat(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        [nat_ty(), nat_ty(), a1, a2, f, h],
    )
}

/// `@congrArg.{1,1} Nat Prop a₁ a₂ f h : f a₁ = f a₂` for `f : Nat → Prop`.
pub(super) fn congr_arg_prop(a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        [nat_ty(), Expr::sort(Level::zero()), a1, a2, f, h],
    )
}

/// `@Eq.mp.{0} α β (h : α = β) (a : α) : β`.
pub(super) fn eq_mp(alpha: Expr, beta: Expr, h: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
        [alpha, beta, h, a],
    )
}

/// `@Eq.mpr.{0} α β (h : α = β) (b : β) : α`.
pub(super) fn eq_mpr(alpha: Expr, beta: Expr, h: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
        [alpha, beta, h, b],
    )
}

/// `fun (t : Nat) => body`, with `hole` abstracted into the binder.
pub(super) fn nat_lam(hole: FVarId, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat_ty(), body.abstract_fvar(hole))
}

/// Strip `MData` wrappers so a spine match sees the term itself.
pub(super) fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

/// The two operands of a `Nat` binary operation, in either spelling the
/// elaborator produces: the raw `Nat.<op> x y`, or the notation
/// `@H<Op>.h<op> α β γ inst x y`.
fn match_bin(e: &Expr, raw: &'static str, notation: &'static str) -> Option<(Expr, Expr)> {
    let e = strip_mdata(e);
    let ExprKind::Const(name, _) = strip_mdata(e.get_app_fn()).kind() else {
        return None;
    };
    let args = e.get_app_args();
    if name == &Name::from_string(raw) && args.len() == 2 {
        return Some((Expr::clone(args[0]), Expr::clone(args[1])));
    }
    if name == &Name::from_string(notation) && args.len() == 6 {
        return Some((Expr::clone(args[4]), Expr::clone(args[5])));
    }
    None
}

pub(super) fn match_add(e: &Expr) -> Option<(Expr, Expr)> {
    match_bin(e, "Nat.add", "HAdd.hAdd")
}

pub(super) fn match_sub(e: &Expr) -> Option<(Expr, Expr)> {
    match_bin(e, "Nat.sub", "HSub.hSub")
}

pub(super) fn match_mul(e: &Expr) -> Option<(Expr, Expr)> {
    match_bin(e, "Nat.mul", "HMul.hMul")
}

/// `true` when `e` is a spelling of the Nat literal `0`.
pub(super) fn is_zero(e: &Expr) -> bool {
    let e = strip_mdata(e);
    if matches!(e.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.zero")) {
        return true;
    }
    eval_nat_expr(e) == Some(0)
}

/// The SUBJECT `T` of a positivity statement `0 < T`, in every spelling the
/// elaborator and the prelude leave behind: `Nat.lt 0 T`, the typeclass
/// `@LT.lt Nat inst 0 T`, and the δ-unfolded `Nat.le (Nat.succ 0) T` /
/// `@LE.le Nat inst (Nat.succ 0) T`.
///
/// Used to find a positivity hypothesis whose subject is only LINEARLY equal to
/// the one a goal asks for (`0 < a + d` in scope, `0 < d + a` wanted). Reading
/// the subject is a search heuristic only — the transport that uses it is a
/// proved equality and the whole term is kernel-re-checked.
pub(super) fn match_positivity(ty: &Expr) -> Option<Expr> {
    let ty = strip_mdata(ty);
    let ExprKind::Const(name, _) = strip_mdata(ty.get_app_fn()).kind() else {
        return None;
    };
    let args = ty.get_app_args();
    let (lo, hi) = if name == &Name::from_string("Nat.lt") && args.len() == 2 {
        (Expr::clone(args[0]), Expr::clone(args[1]))
    } else if name == &Name::from_string("LT.lt") && args.len() == 4 {
        (Expr::clone(args[2]), Expr::clone(args[3]))
    } else if name == &Name::from_string("Nat.le") && args.len() == 2 {
        (peel_succ(args[0])?, Expr::clone(args[1]))
    } else if name == &Name::from_string("LE.le") && args.len() == 4 {
        (peel_succ(args[2])?, Expr::clone(args[3]))
    } else {
        return None;
    };
    is_zero(&lo).then_some(hi)
}

/// `Nat.succ t` → `t`.
fn peel_succ(e: &Expr) -> Option<Expr> {
    let e = strip_mdata(e);
    let ExprKind::App(f, a) = e.kind() else {
        return None;
    };
    matches!(strip_mdata(f).kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.succ"))
        .then(|| Expr::clone(a))
}

/// Rewrite every `+`/`-`/`*` node into its raw `Nat.*` spelling, leaving every
/// other node alone. The result is DEFINITIONALLY equal to the input (the
/// `instH*` instances unfold to the raw operations), which is why the caller
/// may justify the conversion with a re-typed [`mk_refl`].
///
/// This is a *presentation* change only. It cannot make a false goal provable:
/// the whole assembled term is re-checked against the ORIGINAL goal by
/// `super::decreasing::ElabCtx::recheck_decreasing_proof`, so a conversion that
/// was not actually def-eq is rejected there.
pub(super) fn to_raw_nat(e: &Expr) -> Expr {
    if let Some((x, y)) = match_add(e) {
        return nadd(to_raw_nat(&x), to_raw_nat(&y));
    }
    if let Some((x, y)) = match_sub(e) {
        return nsub(to_raw_nat(&x), to_raw_nat(&y));
    }
    if let Some((x, y)) = match_mul(e) {
        return nmul(to_raw_nat(&x), to_raw_nat(&y));
    }
    Expr::clone(strip_mdata(e))
}

impl ElabCtx<'_> {
    /// Normalize a RAW-spelled `Nat` term, returning `(e', pf)` with
    /// `pf : e = e'`. `pf` is a reflexivity proof when nothing fired.
    ///
    /// Bottom-up: children first (composed through `congrArg`), then the
    /// top-level rules, then a bounded re-sweep so a rule that became
    /// applicable after a child collapsed still fires.
    pub(super) fn normalize_nat(&self, e: &Expr, hole: FVarId) -> (Expr, Expr) {
        let mut current = e.clone();
        let mut proof = mk_refl(e.clone());
        for _ in 0..NORMALIZE_SWEEPS {
            let (next, step) = self.normalize_once(&current, hole);
            if next == current {
                break;
            }
            proof = eq_trans(e.clone(), current, next.clone(), proof, step);
            current = next;
        }
        (current, proof)
    }

    /// One bottom-up sweep: `(e', pf : e = e')`.
    fn normalize_once(&self, e: &Expr, hole: FVarId) -> (Expr, Expr) {
        // Children first.
        let (with_children, child_proof) = if let Some((x, y)) = match_add(e) {
            self.congr_bin(e, &x, &y, nadd, hole)
        } else if let Some((x, y)) = match_sub(e) {
            self.congr_bin(e, &x, &y, nsub, hole)
        } else if let Some((x, y)) = match_mul(e) {
            self.congr_bin(e, &x, &y, nmul, hole)
        } else {
            (e.clone(), mk_refl(e.clone()))
        };

        match self.top_rewrite(&with_children) {
            Some((rewritten, step)) => (
                rewritten.clone(),
                eq_trans(e.clone(), with_children, rewritten, child_proof, step),
            ),
            None => (with_children, child_proof),
        }
    }

    /// Normalize both operands of a binary node and compose the two
    /// `congrArg` steps.
    fn congr_bin(
        &self,
        whole: &Expr,
        x: &Expr,
        y: &Expr,
        build: fn(Expr, Expr) -> Expr,
        hole: FVarId,
    ) -> (Expr, Expr) {
        let (x2, px) = self.normalize_once(x, hole);
        let (y2, py) = self.normalize_once(y, hole);
        let mid = build(x2.clone(), y.clone());
        let out = build(x2.clone(), y2.clone());
        // `whole = mid`: rewrite the left operand. `whole` may still carry the
        // notation spelling; the explicit `a₁`/`a₂` arguments make the kernel
        // check that against `build(x, y)` up to def-eq, which is exactly the
        // spelling equivalence.
        let step_left = congr_arg_nat(
            x.clone(),
            x2.clone(),
            nat_lam(hole, build(Expr::fvar(hole), y.clone())),
            px,
        );
        let step_right = congr_arg_nat(
            y.clone(),
            y2,
            nat_lam(hole, build(x2, Expr::fvar(hole))),
            py,
        );
        (
            out.clone(),
            eq_trans(whole.clone(), mid, out, step_left, step_right),
        )
    }

    /// The top-level rewrite rules. `None` when no rule applies.
    fn top_rewrite(&self, e: &Expr) -> Option<(Expr, Expr)> {
        let named = |n: &str| {
            let name = Name::from_string(n);
            self.env
                .get_const(&name)
                .map(|_| Expr::const_(name, vec![]))
        };

        if let Some((x, y)) = match_sub(e) {
            // `x - 0 = x`
            if is_zero(&y) {
                if let Some(lemma) = named("Nat.sub_zero") {
                    return Some((x.clone(), Expr::app(lemma, x)));
                }
            }
            // `x - x = 0`
            if x == y {
                if let Some(lemma) = named("Nat.sub_self") {
                    return Some((nzero(), Expr::app(lemma, x)));
                }
            }
            // `(p + q) - p = q` and `(p + q) - q = p`
            if let Some((p, q)) = match_add(&x) {
                if p == y {
                    if let Some(lemma) = named("Nat.ulpRound.add_sub_cancel_left") {
                        return Some((q.clone(), Expr::apps(lemma, [p, q])));
                    }
                }
                if q == y {
                    if let Some(lemma) = named("Nat.ulpRound.add_sub_self_right") {
                        return Some((p.clone(), Expr::apps(lemma, [p, q])));
                    }
                }
            }
            // `x - y = 0` whenever `x ≤ y` is available.
            if let Some(le) = self.le_witness(&x, &y) {
                if let Some(lemma) = named("Nat.ulpRound.sub_eq_zero_of_le") {
                    return Some((nzero(), Expr::apps(lemma, [x, y, le])));
                }
            }
            return None;
        }

        if let Some((x, y)) = match_add(e) {
            if is_zero(&y) {
                if let Some(lemma) = named("Nat.add_zero") {
                    return Some((x.clone(), Expr::app(lemma, x)));
                }
            }
            if is_zero(&x) {
                if let Some(lemma) = named("Nat.zero_add") {
                    return Some((y.clone(), Expr::app(lemma, y)));
                }
            }
        }
        None
    }

    /// A proof of `Nat.le lo hi`, when one is available syntactically:
    ///
    /// * `hi` is `lo + q`  → `Nat.le_add_right lo q`;
    /// * `hi` is `p + lo`  → the same, transported along `Nat.add_comm`;
    /// * a hypothesis in scope whose type is def-eq to `Nat.le lo hi`.
    ///
    /// Deliberately syntactic and total: a wrong witness cannot slip through,
    /// because every term this feeds is re-checked against the goal.
    pub(super) fn le_witness(&self, lo: &Expr, hi: &Expr) -> Option<Expr> {
        let named = |n: &str| {
            let name = Name::from_string(n);
            self.env
                .get_const(&name)
                .map(|_| Expr::const_(name, vec![]))
        };
        if let Some((p, q)) = match_add(hi) {
            if &p == lo {
                if let Some(lemma) = named("Nat.le_add_right") {
                    return Some(Expr::apps(lemma, [lo.clone(), q]));
                }
            }
            if &q == lo {
                // `lo ≤ p + lo` from `lo ≤ lo + p` through `Nat.add_comm`.
                let (Some(lemma), Some(comm)) = (named("Nat.le_add_right"), named("Nat.add_comm"))
                else {
                    return None;
                };
                let hole = FVarId::new(u64::MAX - 7);
                let base = Expr::apps(lemma, [lo.clone(), p.clone()]);
                let swap = Expr::apps(comm, [lo.clone(), p.clone()]);
                let straight = nadd(lo.clone(), p.clone());
                let swapped = nadd(p, lo.clone());
                return Some(eq_mp(
                    nle(lo.clone(), straight.clone()),
                    nle(lo.clone(), swapped.clone()),
                    congr_arg_prop(
                        straight,
                        swapped,
                        nat_lam(hole, nle(lo.clone(), Expr::fvar(hole))),
                        swap,
                    ),
                    base,
                ));
            }
        }
        let goal = nle(lo.clone(), hi.clone());
        self.locals
            .iter()
            .find(|(_, _, ty)| self.is_def_eq(ty, &goal))
            .map(|(_, fvar, _)| Expr::fvar(*fvar))
    }
}

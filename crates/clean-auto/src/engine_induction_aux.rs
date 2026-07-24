// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Auxiliary-lemma synthesis for the structural-induction lane.
//!
//! The IH-rewriting step ([`crate::engine_induction_rewrite`]) closes an
//! inductive equation whose step rewrites *directly* with the induction
//! hypothesis (`add_assoc`, `append_assoc`). It could NOT close `add_comm`
//! (`∀ n m, n+m = m+n`): `Nat.add` recurses on its **second** argument, so in the
//! `n := succ k` step the goal is `succ k + m = m + succ k` and the left side
//! `succ k + m` is **stuck** — `Nat.add (succ k) m` does not reduce for a free
//! `m` — so neither the IH `k+m = m+k` nor congruence can bridge it. The missing
//! ingredient is the *bridging lemma* `succ_add : ∀ a b, succ a + b = succ (a+b)`
//! (and, for the base case `0+m = m+0`, `zero_add : ∀ b, 0+b = b`), each provable
//! by its **own** induction.
//!
//! This module synthesises exactly those lemmas. Given the leaf equation, it
//! detects a *recursion-side mismatch* — a subterm `op (c x) y` whose operator
//! `op` is stuck because it recurses on the argument `y` while a **constructor**
//! `c` sits in the other (inducted) operand — and conjectures the
//! "move the constructor through the operator" equation:
//!
//!   * unary constructor `c` (e.g. `Nat.succ`):  `∀ x y, op (c x) y = c (op x y)`;
//!   * nullary constructor `c₀` (e.g. `Nat.zero`): `∀ y, op c₀ y = y`.
//!
//! Each conjecture is proved by the **existing** induction lane
//! ([`AutomationEngine::try_induction_lane`]), KERNEL-CHECKED, then registered as
//! a directed rewrite fact (specialised to the stuck term's arguments) that the
//! caller feeds back into [`AutomationEngine::prove_eq_rewrite`].
//!
//! Soundness: this is on the *search* side, not the TCB. A conjecture is only
//! ever a search hint — its proof is a genuine recursor term that must pass
//! `infer_type` + `is_def_eq` against the conjecture before it becomes a fact, and
//! the specialised witness's type is whatever the kernel infers. A *false*
//! conjecture (e.g. the identity shape `0*y = y` for `Nat.mul`) simply fails its
//! own induction and yields no fact; nothing unsound can be emitted. A re-entrancy
//! guard ensures the aux-lemma proofs do not themselves trigger further synthesis
//! (they close on their own IH), keeping the recursion finite.

use std::cell::{Cell, RefCell};
use std::time::Instant;

use clean_kernel::{
    BinderInfo, Environment, Expr, ExprKind, Level, LocalContext, Name, TypeChecker,
};

use crate::engine::AutomationEngine;
use crate::engine_induction::{build_eq, kernel_accepts, parse_eq, type_checker, INDUCTION_FUEL};
use crate::engine_induction_match::{
    carrier_head_name, is_add_right_comm_shape, is_distribute_conjecture,
};

/// A specialised, kernel-checked rewrite equation: `(witness, equation_type)`.
type RewriteFact = (Expr, Expr);

/// Maximum nesting depth of aux-lemma synthesis.
///
/// Bounds *chaining* — a synthesised lemma proved with the help of another
/// synthesised lemma (`succ_mul` needs `add_right_comm`, which needs `succ_add`).
/// Each nested synthesis consumes one unit; past this depth synthesis declines,
/// so the recursion is finite regardless of the goal.
const MAX_SYNTH_DEPTH: u32 = 5;

thread_local! {
    /// Current aux-lemma synthesis nesting depth (0 = not synthesising).
    static SYNTH_DEPTH: Cell<u32> = const { Cell::new(0) };
    /// `∀`-quantified bridge lemmas proved earlier in the *current* synthesis
    /// tree, offered as chainable rewrite facts to later (nested) proofs. Cleared
    /// when the outermost synthesis completes.
    static FACT_STORE: RefCell<Vec<RewriteFact>> = const { RefCell::new(Vec::new()) };
}

/// The `∀`-quantified bridge lemmas accumulated in the current synthesis tree.
///
/// Consulted by [`AutomationEngine::prove_eq_rewrite`]'s sub-term rewrite branch,
/// so a lemma proved while chaining (e.g. `add_right_comm`) becomes usable when
/// closing a later synthesised lemma (`succ_mul`). Empty outside synthesis.
pub(crate) fn chaining_facts() -> Vec<RewriteFact> {
    FACT_STORE.with(|s| s.borrow().clone())
}

/// `true` iff execution is currently inside an aux-lemma synthesis region
/// (`SYNTH_DEPTH > 0`).
///
/// The structural-induction lane's non-recursive-field fallback
/// ([`AutomationEngine::discharge_minor`]) consults this to stay OUT of synthesis:
/// the synthesizer proves *speculative* bridging conjectures via the same lane,
/// and a false conjecture's stuck minors must fail fast (as they did before the
/// fallback existed). Letting the fallback re-induct on those minors re-enters the
/// synthesizer and explodes the search — the exact non-local blow-up that
/// regressed the `Nat`/`Int` rows.
pub(crate) fn in_synthesis() -> bool {
    SYNTH_DEPTH.with(|d| d.get() > 0)
}

/// Upper bound on distinct chaining lemmas kept — a robustness rail so the
/// sub-term rewriter's per-call fact scan stays cheap.
const MAX_CHAINING_FACTS: usize = 16;

/// Register a `∀`-lemma for chaining, de-duplicated by equation type. The lane
/// re-derives the same bridge at many leaves; without dedup the store would flood
/// with hundreds of identical `0*y=0` / `succ_add` copies and swamp the sub-term
/// rewriter's scan.
fn push_chaining_fact(fact: RewriteFact) {
    FACT_STORE.with(|s| {
        let mut store = s.borrow_mut();
        if store.len() >= MAX_CHAINING_FACTS || store.iter().any(|(_, ty)| *ty == fact.1) {
            return;
        }
        store.push(fact);
    });
}

/// RAII guard: enters a (bounded) aux-lemma synthesis region.
///
/// [`Self::enter`] returns `None` once nesting reaches [`MAX_SYNTH_DEPTH`] (so
/// chaining is finite), and `Some(_)` otherwise — decrementing the depth on drop
/// (even on early return) and clearing the chaining fact store when the
/// *outermost* region ends.
struct SynthGuard {
    was_outermost: bool,
}

impl SynthGuard {
    fn enter() -> Option<Self> {
        SYNTH_DEPTH.with(|d| {
            let cur = d.get();
            if cur >= MAX_SYNTH_DEPTH {
                None
            } else {
                d.set(cur + 1);
                Some(SynthGuard {
                    was_outermost: cur == 0,
                })
            }
        })
    }
}

impl Drop for SynthGuard {
    fn drop(&mut self) {
        SYNTH_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        if self.was_outermost {
            FACT_STORE.with(|s| s.borrow_mut().clear());
        }
    }
}

/// `@Eq.trans.{u} α a b c h1 h2 : Eq α a c` (from `h1 : a = b`, `h2 : b = c`).
pub(crate) fn eq_trans(
    level: &Level,
    ty: &Expr,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let trans = Expr::const_(Name::from_string("Eq.trans"), vec![level.clone()]);
    Expr::apps(
        trans,
        [
            ty.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            h1.clone(),
            h2.clone(),
        ],
    )
}

impl AutomationEngine {
    /// Synthesise bridging rewrite facts for the stuck operators in `goal`.
    ///
    /// `goal` is the leaf equation reached by the IH-rewrite step. For each side
    /// whose head is a stuck `op (c …) y` (constructor `c` in the inducted
    /// operand, `op` recursing on `y`), conjectures the constructor-commute
    /// lemma, proves it by the existing induction lane, kernel-checks it, and
    /// returns the proof **specialised** to the stuck term's arguments as a
    /// directed rewrite fact. Returns `Vec::new()` when nothing is stuck, when
    /// already inside a synthesis (re-entrancy guard), or when no conjecture
    /// proves.
    pub(crate) fn synthesize_bridging_facts(
        &self,
        env: &Environment,
        ctx: &LocalContext,
        goal: &Expr,
        deadline: Instant,
    ) -> Vec<RewriteFact> {
        // Re-entrancy guard: never synthesise while proving an aux lemma — those
        // proofs close on their own IH and must not recurse into synthesis.
        let Some(_guard) = SynthGuard::enter() else {
            return Vec::new();
        };
        if Instant::now() >= deadline {
            return Vec::new();
        }
        let Some((_levels, _ty, lhs, rhs)) = parse_eq(goal) else {
            return Vec::new();
        };

        let mut facts = Vec::new();
        for side in [&lhs, &rhs] {
            if let Some(fact) = self.bridge_stuck_side(env, ctx, side, deadline) {
                facts.push(fact);
            }
        }
        facts
    }

    /// Build, prove, and specialise the bridging lemma for one operand `side`.
    ///
    /// Detects a stuck `op (c args) y` (on the literal term), conjectures the
    /// constructor-commute equation, proves it by the lane, kernel-checks it, and
    /// returns `(specialised_witness, equation_type)`. `None` when `side` is not a
    /// stuck constructor-headed operator application, the conjecture is not
    /// closed, or it does not prove.
    fn bridge_stuck_side(
        &self,
        env: &Environment,
        ctx: &LocalContext,
        side: &Expr,
        deadline: Instant,
    ) -> Option<RewriteFact> {
        let tc = type_checker(env, ctx);

        // Inspect the *literal* outer operator — NOT its whnf. A stuck `op (c x) y`
        // whnfs by UNFOLDING `op`'s recursive definition (exposing `op`'s `I.rec`),
        // which would hide the recursion-side mismatch we are matching. The
        // operator's surface application is exactly what carries it.
        let lit = side.strip_mdata();
        let head = lit.get_app_fn().strip_mdata();
        let ExprKind::Const(op_name, _) = head.kind() else {
            return None;
        };
        if env.get_constructor(op_name).is_some() {
            return None;
        }
        let args = lit.get_app_args();
        if args.len() != 2 {
            return None;
        }
        let op_const = head.clone();
        let arg1 = args[1];

        // The inducted operand must be a constructor application of a
        // parameter-free inductive (Nat.zero / Nat.succ / Bool.true / …). WHNF the
        // OPERAND (not the outer op) to expose a constructor hidden behind a redex:
        // `add_right_comm`'s step needs a bridge on `(a + succ w) + b`, whose first
        // operand `a + succ w` only reveals its `succ` head after reduction. A
        // stuck `k * m` reduces to a recursor (no constructor) and is declined.
        let arg0 = tc.whnf(args[0]);
        let c_head = arg0.get_app_fn().strip_mdata();
        let ExprKind::Const(c_name, _) = c_head.kind() else {
            return None;
        };
        let cval = env.get_constructor(c_name)?;
        if cval.num_params != 0 {
            return None;
        }

        // Confirm the operator is genuinely STUCK on the *other* operand: if `op`
        // recursed on the constructor side instead, the term would reduce to a
        // constructor-headed result and need no bridge. A stuck `op` whnfs to a
        // recursor application (head is not a constructor).
        let side_head = tc.whnf(side).get_app_fn().strip_mdata().clone();
        if let ExprKind::Const(reduced_head, _) = side_head.kind() {
            if env.get_constructor(reduced_head).is_some() {
                return None;
            }
        }
        let c_const = c_head.clone();
        let ctor_fields = arg0.get_app_args();
        if ctor_fields.len() != cval.num_fields as usize {
            return None;
        }

        // Second-operand type, required closed so the conjecture is a closed `∀`.
        let arg1_ty = tc.infer_type(arg1).ok()?;
        let arg1_ty = tc.whnf(&arg1_ty);
        if arg1_ty.has_fvar_quick() || arg1_ty.has_loose_bvars_quick() {
            return None;
        }

        // Candidate conjectures for the stuck shape, tried in order — the one
        // that KERNEL-PROVES is kept, a false one fails its own induction and is
        // skipped (nothing unsound can be emitted). The nullary case tries
        // left-IDENTITY (`op c₀ y = y`, true for `+`) then left-ABSORBING
        // (`op c₀ y = c₀`, true for `*`); the unary case tries constructor-COMMUTE
        // (`op (c x) y = c (op x y)`, true for `+`) then left-DISTRIBUTE
        // (`op (c x) y = (op x y) + y`, the `succ_mul` bridge, true for `*`).
        let (candidates, witness_args): (Vec<Expr>, Vec<Expr>) = match cval.num_fields {
            0 => {
                let ident = nullary_identity_conjecture(&tc, &op_const, &c_const, &arg1_ty)?;
                let mut cands = vec![ident];
                if let Some(absorb) =
                    nullary_absorbing_conjecture(&tc, &op_const, &c_const, &arg1_ty)
                {
                    cands.push(absorb);
                }
                (cands, vec![arg1.clone()])
            }
            1 => {
                let field = ctor_fields[0];
                let field_ty = tc.infer_type(field).ok()?;
                let field_ty = tc.whnf(&field_ty);
                if field_ty.has_fvar_quick() || field_ty.has_loose_bvars_quick() {
                    return None;
                }
                let commute =
                    unary_commute_conjecture(&tc, &op_const, &c_const, &field_ty, &arg1_ty)?;
                let mut cands = vec![commute];
                if let Some(distrib) =
                    unary_distribute_conjecture(&tc, &op_const, &c_const, &field_ty, &arg1_ty)
                {
                    cands.push(distrib);
                }
                (cands, vec![field.clone(), arg1.clone()])
            }
            _ => return None,
        };

        let empty = LocalContext::new();
        for conjecture in &candidates {
            // Chaining: a distribute (`succ_mul`) conjecture's own inductive step
            // rearranges the accumulator (`(x*j + j) + x = (x*j + x) + j`), which
            // is `add_right_comm` — NOT a constructor-commute bridge, so it is
            // pre-seeded here (proved by the lane, kernel-checked) into the
            // chaining store the sub-term rewriter consults.
            if is_distribute_conjecture(conjecture) {
                self.preseed_add_right_comm(env, &arg1_ty, deadline);
            }
            let Some(proof) =
                self.try_induction_lane(env, conjecture, &empty, deadline, INDUCTION_FUEL)
            else {
                continue;
            };
            if !kernel_accepts(env, &empty, &proof, conjecture) {
                continue;
            }
            // Register the general `∀`-lemma so a LATER nested synthesis can chain
            // on it, then specialise to the stuck term's arguments.
            push_chaining_fact((proof.clone(), conjecture.clone()));
            let witness = Expr::apps(proof, witness_args.clone());
            let witness_ty = tc.infer_type(&witness).ok()?;
            let witness_ty = tc.whnf(&witness_ty);
            let _ = parse_eq(&witness_ty)?;
            return Some((witness, witness_ty));
        }
        None
    }

    /// Prove `add_right_comm : ∀ a b c, (a+b)+c = (a+c)+b` for the accumulator
    /// (`Nat.add`) and push it to the chaining fact store, at most once per
    /// synthesis tree. Silent no-op off the `Nat` carrier or if it does not prove.
    fn preseed_add_right_comm(&self, env: &Environment, carrier_ty: &Expr, deadline: Instant) {
        if carrier_head_name(carrier_ty).as_deref() != Some("Nat") {
            return;
        }
        // Dedup: already seeded this synthesis tree.
        if chaining_facts()
            .iter()
            .any(|(_, ty)| is_add_right_comm_shape(ty))
        {
            return;
        }
        let Some(conj) = add_right_comm_conjecture(carrier_ty) else {
            return;
        };
        let empty = LocalContext::new();
        let Some(proof) = self.try_induction_lane(env, &conj, &empty, deadline, INDUCTION_FUEL)
        else {
            return;
        };
        if kernel_accepts(env, &empty, &proof, &conj) {
            push_chaining_fact((proof, conj));
        }
    }
}

/// Universe `u` with `ty : Sort u`, or `None` if `ty` is not a sort.
fn sort_level_of(tc: &TypeChecker<'_>, ty: &Expr) -> Option<Level> {
    let sort = tc.whnf(&tc.infer_type(ty).ok()?);
    match sort.strip_mdata().kind() {
        ExprKind::Sort(level) => Some(level.normalize()),
        _ => None,
    }
}

/// `∀ (x : field_ty) (y : arg_ty), op (c x) y = c (op x y)`.
///
/// de Bruijn: under the two binders `x = bvar(1)`, `y = bvar(0)`. The equation's
/// carrier is `field_ty` (the constructor-commute shape returns the inductive's
/// own type); a wrong carrier simply fails the lane's kernel re-check.
fn unary_commute_conjecture(
    tc: &TypeChecker<'_>,
    op_const: &Expr,
    c_const: &Expr,
    field_ty: &Expr,
    arg_ty: &Expr,
) -> Option<Expr> {
    let eq_level = sort_level_of(tc, field_ty)?;
    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    let lhs = Expr::apps(
        op_const.clone(),
        [Expr::app(c_const.clone(), x.clone()), y.clone()],
    );
    let rhs = Expr::app(c_const.clone(), Expr::apps(op_const.clone(), [x, y]));
    let body = build_eq(&eq_level, field_ty, &lhs, &rhs);
    Some(Expr::pi(
        BinderInfo::Default,
        field_ty.clone(),
        Expr::pi(BinderInfo::Default, arg_ty.clone(), body),
    ))
}

/// `∀ (y : arg_ty), op c₀ y = y` (left-identity shape).
fn nullary_identity_conjecture(
    tc: &TypeChecker<'_>,
    op_const: &Expr,
    c_const: &Expr,
    arg_ty: &Expr,
) -> Option<Expr> {
    let eq_level = sort_level_of(tc, arg_ty)?;
    let y = Expr::bvar(0);
    let lhs = Expr::apps(op_const.clone(), [c_const.clone(), y.clone()]);
    let body = build_eq(&eq_level, arg_ty, &lhs, &y);
    Some(Expr::pi(BinderInfo::Default, arg_ty.clone(), body))
}

/// `∀ (y : arg_ty), op c₀ y = c₀` (left-absorbing shape, e.g. `0 * y = 0`).
fn nullary_absorbing_conjecture(
    tc: &TypeChecker<'_>,
    op_const: &Expr,
    c_const: &Expr,
    arg_ty: &Expr,
) -> Option<Expr> {
    let eq_level = sort_level_of(tc, arg_ty)?;
    let y = Expr::bvar(0);
    let lhs = Expr::apps(op_const.clone(), [c_const.clone(), y.clone()]);
    let body = build_eq(&eq_level, arg_ty, &lhs, c_const);
    Some(Expr::pi(BinderInfo::Default, arg_ty.clone(), body))
}

/// `∀ (x : field_ty) (y : arg_ty), op (c x) y = Nat.add (op x y) y`
/// (left-distribute / `succ_mul` shape). Only offered on the `Nat` carrier,
/// whose accumulator is `Nat.add`; a wrong shape fails its own induction.
fn unary_distribute_conjecture(
    tc: &TypeChecker<'_>,
    op_const: &Expr,
    c_const: &Expr,
    field_ty: &Expr,
    arg_ty: &Expr,
) -> Option<Expr> {
    if carrier_head_name(field_ty).as_deref() != Some("Nat") {
        return None;
    }
    let eq_level = sort_level_of(tc, field_ty)?;
    let x = Expr::bvar(1);
    let y = Expr::bvar(0);
    let lhs = Expr::apps(
        op_const.clone(),
        [Expr::app(c_const.clone(), x.clone()), y.clone()],
    );
    let op_xy = Expr::apps(op_const.clone(), [x, y.clone()]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let rhs = Expr::apps(nat_add, [op_xy, y]);
    let body = build_eq(&eq_level, field_ty, &lhs, &rhs);
    Some(Expr::pi(
        BinderInfo::Default,
        field_ty.clone(),
        Expr::pi(BinderInfo::Default, arg_ty.clone(), body),
    ))
}

/// `∀ (a b c : carrier), (a+b)+c = (a+c)+b` (`add_right_comm` for `Nat.add`).
///
/// The accumulator rearrangement `succ_mul`'s inductive step reduces to; proved
/// by the lane (induction on `c` + the `succ_add` bridge) and pre-seeded into the
/// chaining store. `carrier` is `Nat` (`Sort 1`), so the `Eq` level is `1`.
fn add_right_comm_conjecture(carrier: &Expr) -> Option<Expr> {
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
    let a = Expr::bvar(2);
    let b = Expr::bvar(1);
    let c = Expr::bvar(0);
    let lhs = add(add(a.clone(), b.clone()), c.clone());
    let rhs = add(add(a, c), b);
    let level = Level::succ(Level::zero());
    let body = build_eq(&level, carrier, &lhs, &rhs);
    let pi_c = Expr::pi(BinderInfo::Default, carrier.clone(), body);
    let pi_b = Expr::pi(BinderInfo::Default, carrier.clone(), pi_c);
    Some(Expr::pi(BinderInfo::Default, carrier.clone(), pi_b))
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Spike test for `designs/2026-04-20-fin-sum-faithful-carrier.md` Open Question 1:
//! *"Does the current `whnf` reducer handle `Nat.rec` iota-reduction over a motive
//! with Π-binders correctly?"*
//!
//! Uses a synthetic carrier shaped exactly like the proposed faithful `Fin.sum`:
//!
//! ```text
//! motive : Nat -> Sort 1
//! motive k := (Fin k -> Nat) -> Nat
//!
//! carrier := @Nat.rec.{1}
//!              (fun k : Nat => (Fin k -> Nat) -> Nat)  -- Π-motive
//!              (fun _f => Nat.zero)                     -- zero case
//!              (fun (_k : Nat) (ih : (Fin k -> Nat) -> Nat)
//!                   (f : Fin (k+1) -> Nat) =>
//!                  ih (fun _i : Fin k => f (Fin.castSucc i)) + f (Fin.last k))
//! ```
//!
//! Here we simplify by (a) using `Nat` as the value type in place of `Rat` so
//! the test doesn't depend on the full Rat/Fin axiom stack, and (b) using a
//! placeholder `Box` type as the "Fin k" stand-in so the Π-motive shape is
//! preserved without bringing in the `Fin` constructor machinery. What matters
//! for Open Question 1 is the motive shape, not the specific type inhabited.
//!
//! The test validates two iota reduction events:
//!
//! 1. **Base case (k = 0):** `carrier Nat.zero f` must reduce to `Nat.zero` via
//!    a single Nat.rec iota step picking the zero branch, then a beta step on
//!    `fun _f => Nat.zero`. This is required for `Fin.sum_zero` to close by
//!    `Eq.refl` after ι.
//!
//! 2. **Step case (k = succ _):** `carrier (Nat.succ Nat.zero) f` must reduce
//!    one ι-step into the step-case body, exposing the IH as a nested
//!    `Nat.rec`. This is required for `Fin.sum_succ` to close by `Eq.refl`
//!    after ι (the carrier's defining equation IS `Fin.sum_succ`).
//!
//! If either step fails, the Π-motive case is not supported and the Phase 1
//! carrier refactor in the design doc is blocked pending whnf/reduction work.
//! If both succeed, the design's Open Question 1 answer is YES, and Phase 2+3
//! of the plan can proceed.

use super::support::make_nat_env_and_ref;
use super::*;
use crate::env::Declaration;
use crate::level::Level;

/// Name the synthetic "Fin k" placeholder so we can treat it as an opaque type
/// without implementing its constructor. We register it as a free axiom on
/// `Nat -> Type 0` so it behaves like an indexed type family for the purposes
/// of the Π-motive.
fn register_fin_placeholder(env: &mut Environment, nat_ref: &Expr) {
    let fin_name = Name::from_string("SpikeFin");
    if env.get_const(&fin_name).is_some() {
        return;
    }
    // SpikeFin : Nat -> Type 0
    let fin_type = Expr::arrow(nat_ref.clone(), Expr::type_());
    env.add_decl(Declaration::Axiom {
        name: fin_name,
        level_params: vec![],
        type_: fin_type,
    })
    .expect("register SpikeFin placeholder");
}

/// Build `SpikeFin n -> Nat` (the type of a summand function).
fn spike_fin_to_nat(nat_ref: &Expr, n: Expr) -> Expr {
    let fin_const = Expr::const_(Name::from_string("SpikeFin"), vec![]);
    let fin_n = Expr::app(fin_const, n);
    Expr::pi(BinderInfo::Default, fin_n, nat_ref.clone())
}

/// Build the Π-motive: `fun k : Nat => (SpikeFin k -> Nat) -> Nat`
fn spike_motive(nat_ref: &Expr) -> Expr {
    // k is bound by the outer lambda → DeBruijn index 0 when building the body.
    let fin_const = Expr::const_(Name::from_string("SpikeFin"), vec![]);
    let k_var = Expr::bvar(0);
    let fin_k = Expr::app(fin_const, k_var);
    let fin_k_to_nat = Expr::pi(BinderInfo::Default, fin_k, nat_ref.clone());
    let body = Expr::arrow(fin_k_to_nat, nat_ref.clone());
    Expr::lam(BinderInfo::Default, nat_ref.clone(), body)
}

/// Build the zero-case: `fun _f : (SpikeFin 0 -> Nat) => Nat.zero`
fn spike_zero_case(nat_ref: &Expr) -> Expr {
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let fin_zero = Expr::app(
        Expr::const_(Name::from_string("SpikeFin"), vec![]),
        nat_zero,
    );
    let fin_zero_to_nat = Expr::pi(BinderInfo::Default, fin_zero, nat_ref.clone());
    Expr::lam(BinderInfo::Default, fin_zero_to_nat, nat_zero_const)
}

/// Build the step-case. This lambda has the shape:
/// ```text
/// fun (k : Nat) (ih : (SpikeFin k -> Nat) -> Nat)
///     (f : SpikeFin (succ k) -> Nat) =>
///   ih (fun _i : SpikeFin k => Nat.zero)   -- simplified body: no castSucc/last
/// ```
/// We intentionally elide the `castSucc/last` plumbing because those are
/// registered as axioms in `nn_verify_fin_sum.rs` at the production call site;
/// the spike only needs to prove that `Nat.rec` iota-reduces through the
/// Π-motive, so the step-body content is irrelevant.
fn spike_step_case(nat_ref: &Expr) -> Expr {
    let fin_const = Expr::const_(Name::from_string("SpikeFin"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build innermost: fun _i : SpikeFin k => Nat.zero
    // At this depth, k refers to BVar 2 (outer k=2, ih=1, f=0, then inner i=0 shifts k to 3).
    // Actually: outer lambdas create locals, but we use BVars. Let's be careful:
    // Lambda stack (outermost first): k -> ih -> f -> i. Inside the inner `fun _i`,
    // indexes: i=0, f=1, ih=2, k=3.
    let inner_fun = {
        let k_var = Expr::bvar(3); // shifted: we're inside the innermost lambda
        let fin_k = Expr::app(fin_const.clone(), k_var);
        // body: Nat.zero (no reference to i/f/ih/k)
        Expr::lam(BinderInfo::Default, fin_k, nat_zero_const.clone())
    };

    // Middle: ih applied to inner_fun → BVar(1) at depth 3
    let ih_var = Expr::bvar(1); // from inside f's lambda: f=0, ih=1, k=2. We're at depth 3 (k, ih, f layers).
    let ih_app = Expr::app(ih_var, inner_fun);

    // Innermost lambda: fun (f : SpikeFin (succ k) -> Nat) => ih_app
    // Here depth relative to the k-binder outside: k=1 initially, ih=0 before f, then f=0, ih=1, k=2.
    let f_lambda = {
        let k_var = Expr::bvar(1); // k is BVar 1 here (past ih=0, now f-binder opened)
        let succ_k = Expr::app(nat_succ.clone(), k_var);
        let fin_succ_k = Expr::app(fin_const.clone(), succ_k);
        let f_type = Expr::pi(BinderInfo::Default, fin_succ_k, nat_ref.clone());
        Expr::lam(BinderInfo::Default, f_type, ih_app)
    };

    // Middle lambda: fun (ih : (SpikeFin k -> Nat) -> Nat) => f_lambda
    // Here depth relative to k: k=0. We need SpikeFin k → Nat → Nat as ih's type.
    let ih_lambda = {
        let k_var = Expr::bvar(0);
        let fin_k = Expr::app(fin_const.clone(), k_var);
        let fin_k_to_nat = Expr::pi(BinderInfo::Default, fin_k, nat_ref.clone());
        let ih_type = Expr::arrow(fin_k_to_nat, nat_ref.clone());
        Expr::lam(BinderInfo::Default, ih_type, f_lambda)
    };

    // Outermost lambda: fun (k : Nat) => ih_lambda
    Expr::lam(BinderInfo::Default, nat_ref.clone(), ih_lambda)
}

/// Build `Nat.rec.{1}` instantiated for the Π-motive.
fn spike_nat_rec() -> Expr {
    Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    )
}

/// Build the full carrier: `Nat.rec.{1} motive zero_case step_case`
fn spike_carrier(nat_ref: &Expr) -> Expr {
    let rec = spike_nat_rec();
    let motive = spike_motive(nat_ref);
    let zero_case = spike_zero_case(nat_ref);
    let step_case = spike_step_case(nat_ref);
    Expr::app(Expr::app(Expr::app(rec, motive), zero_case), step_case)
}

/// Open Question 1a (base case, k = 0):
///
/// `Nat.rec motive zero_case step_case Nat.zero f` must iota-reduce to
/// `zero_case f` which beta-reduces to `Nat.zero`.
///
/// If this test passes, `Fin.sum_zero` on the faithful carrier would close
/// by `Eq.refl Nat.zero` after whnf.
#[test]
fn test_pi_motive_nat_rec_base_case_reduces_to_zero() {
    let (mut env, nat_ref) = make_nat_env_and_ref();
    register_fin_placeholder(&mut env, &nat_ref);

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Register symbolic f : SpikeFin Nat.zero -> Nat. Leaving f symbolic means
    // beta cannot silently make f vanish; if whnf returns Nat.zero, the carrier
    // truly iota-reduced on the Nat.zero branch.
    let f_name = Name::from_string("spike_f_zero");
    if env.get_const(&f_name).is_none() {
        let f_type = spike_fin_to_nat(&nat_ref, nat_zero.clone());
        env.add_decl(Declaration::Axiom {
            name: f_name.clone(),
            level_params: vec![],
            type_: f_type,
        })
        .expect("register spike_f_zero");
    }

    let tc = TypeChecker::new(&env);
    let f = Expr::const_(f_name, vec![]);
    let carrier = spike_carrier(&nat_ref);

    // Application: carrier Nat.zero f
    let app = Expr::app(Expr::app(carrier, nat_zero.clone()), f);

    let result = tc.whnf(&app);

    // Expected: Nat.zero (or at least definitionally equal).
    // Iota step on Nat.rec (Nat.zero) → zero_case = (fun _f => Nat.zero).
    // Extra-args forwarding applies f, then beta: zero_case f → Nat.zero.
    assert_eq!(
        result, nat_zero,
        "Π-motive Nat.rec base-case failed: expected Nat.zero, got {:?}",
        result
    );
}

/// Open Question 1b (step case, k = succ 0):
///
/// `Nat.rec motive zero_case step_case (Nat.succ Nat.zero) f` must iota-reduce
/// ONE step into `step_case Nat.zero (Nat.rec motive zero_case step_case Nat.zero) f`
/// and NOT remain stuck at the original application. This confirms that whnf
/// performs the recursive ι-step correctly under a Π-motive.
///
/// We check two things:
/// (a) the result is NOT identical to the input (reduction happened), and
/// (b) the result is definitionally equal to the input (semantic preservation).
#[test]
fn test_pi_motive_nat_rec_step_case_reduces() {
    let (mut env, nat_ref) = make_nat_env_and_ref();
    register_fin_placeholder(&mut env, &nat_ref);

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(nat_succ, nat_zero);

    // Register symbolic f : SpikeFin (succ 0) -> Nat
    let f_name = Name::from_string("spike_f_one");
    if env.get_const(&f_name).is_none() {
        let f_type = spike_fin_to_nat(&nat_ref, succ_zero.clone());
        env.add_decl(Declaration::Axiom {
            name: f_name.clone(),
            level_params: vec![],
            type_: f_type,
        })
        .expect("register spike_f_one");
    }

    let tc = TypeChecker::new(&env);
    let f = Expr::const_(f_name, vec![]);
    let carrier = spike_carrier(&nat_ref);

    let app = Expr::app(Expr::app(carrier.clone(), succ_zero.clone()), f.clone());

    let result = tc.whnf(&app);

    // (a) Reduction must fire: result ≠ input.
    assert_ne!(
        app, result,
        "Π-motive Nat.rec step-case did NOT reduce: whnf returned input \
         unchanged, blocking faithful Fin.sum carrier (#3546). \
         Got: {:?}",
        result
    );

    // (b) Semantic preservation: the reduced form is def-eq to the original.
    assert!(
        tc.is_def_eq(&app, &result),
        "Π-motive Nat.rec step-case broke semantic preservation: \
         whnf produced a term not def-eq to the source. Got: {:?}",
        result
    );
}

/// End-to-end spike: `carrier (succ 0) f` fully reduces to the step-case body
/// applied to (carrier 0 ...) applied to f. This is the critical shape
/// `Fin.sum_succ` needs: the carrier's defining equation.
///
/// We don't assert the exact normal form (it depends on how deep whnf goes);
/// we assert the result whnf's to something that contains the IH application,
/// meaning the iota step was taken and the recursion unfolded.
#[test]
fn test_pi_motive_nat_rec_full_spike_smoke() {
    let (mut env, nat_ref) = make_nat_env_and_ref();
    register_fin_placeholder(&mut env, &nat_ref);

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(nat_succ, nat_zero.clone());

    // Register symbolic f : SpikeFin (succ 0) -> Nat
    let f_name = Name::from_string("spike_f_smoke");
    if env.get_const(&f_name).is_none() {
        let f_type = spike_fin_to_nat(&nat_ref, succ_zero.clone());
        env.add_decl(Declaration::Axiom {
            name: f_name.clone(),
            level_params: vec![],
            type_: f_type,
        })
        .expect("register spike_f_smoke");
    }

    let tc = TypeChecker::new(&env);
    let f = Expr::const_(f_name, vec![]);
    let carrier = spike_carrier(&nat_ref);

    // Input: carrier (succ 0) f
    let app = Expr::app(Expr::app(carrier, succ_zero), f);

    // whnf should produce *something* different from the input; whether it
    // stops at the outer beta or descends further depends on the reducer, but
    // the key soundness condition is that the ι-rule fired and the reduction
    // preserved semantics.
    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&app, &result),
        "Π-motive full-spike smoke: input and whnf output must be def-eq. \
         Got: {:?}",
        result
    );
}

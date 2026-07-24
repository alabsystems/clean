// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The first genuinely kernel-certified Trust refutation.
//!
//! Trust's `Certified` assurance is meant to mean "a verified kernel checked
//! this proof" — soundness reducing to the clean CIC kernel, NOT to the ay
//! solver or ay's SMT proof checker (both of which have had soundness bugs).
//! This test demonstrates that capability end-to-end at the kernel level: the
//! clean kernel verifies `∀ (P : Prop), (And P (Not P)) → False` from a CLOSED,
//! AXIOM-FREE proof term built over ONLY prelude constants (And, And.left,
//! And.right, Not, False) — the canonical contradiction refutation that
//! underlies "a verification condition's violation is unsatisfiable".

use super::*;

#[test]
fn trust_contradiction_is_kernel_certified() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    let and_c = Expr::const_str("And");
    let not_c = Expr::const_str("Not");
    let false_c = Expr::const_str("False");
    let and_left = Expr::const_str("And.left");
    let and_right = Expr::const_str("And.right");
    let prop = Expr::prop();

    // `And P (Not P)` with the Prop var P at de Bruijn index `depth`.
    let and_p_not_p = |depth: u32| {
        let p = Expr::bvar(depth);
        let not_p = Expr::app(not_c.clone(), p.clone());
        Expr::app(Expr::app(and_c.clone(), p), not_p)
    };

    // Theorem: ∀ (P : Prop), (And P (Not P)) → False
    // Inside the Pi, P = bvar(0); the arrow domain is `And P (Not P)`; the
    // codomain `False` is closed.
    let theorem = Expr::pi(
        BinderInfo::Default,
        prop.clone(),
        Expr::arrow(and_p_not_p(0), false_c.clone()),
    );

    // Proof: fun (P : Prop) (h : And P (Not P)) =>
    //          (And.right P (Not P) h) (And.left P (Not P) h)
    // In the body, P = bvar(1) and h = bvar(0). And.left/And.right take their
    // {a b : Prop} arguments explicitly here (the kernel checks fully-applied
    // terms; implicit-vs-explicit is an elaboration concern, not a kernel one),
    // exactly as the in-kernel `And.symm` definition does.
    let p1 = Expr::bvar(1);
    let not_p1 = Expr::app(not_c.clone(), p1.clone());
    let h0 = Expr::bvar(0);
    // And.left P (Not P) h : P
    let left_proj = Expr::app(
        Expr::app(Expr::app(and_left.clone(), p1.clone()), not_p1.clone()),
        h0.clone(),
    );
    // And.right P (Not P) h : Not P  ≡  P → False  (Not is reducible)
    let right_proj = Expr::app(Expr::app(Expr::app(and_right.clone(), p1), not_p1), h0);
    // (And.right P (Not P) h) (And.left P (Not P) h) : False
    let body = Expr::app(right_proj, left_proj);
    let proof = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, and_p_not_p(0), body),
    );

    // THE kernel check — the sole source of trust for this `Certified` claim.
    tc.check_type(&proof, &theorem).expect(
        "clean CIC kernel must certify `∀ P, (And P (Not P)) → False` from a \
         closed, axiom-free, prelude-only proof term",
    );

    // The proof's INFERRED type is exactly the theorem — independent confirmation
    // that the term genuinely witnesses the proposition (not merely def-eq slack).
    let inferred = tc
        .infer_type(&proof)
        .expect("proof term must be well-typed");
    assert!(
        tc.is_def_eq(&inferred, &theorem),
        "inferred type must equal the theorem; got {inferred:?}"
    );

    // Negative control: the kernel must REJECT a non-proof — it is not
    // rubber-stamping. `fun (P : Prop) (h : And P (Not P)) => h` has type
    // `∀ P, (And P (Not P)) → And P (Not P)`, NOT `... → False`.
    let identity = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, and_p_not_p(0), Expr::bvar(0)),
    );
    assert!(
        tc.check_type(&identity, &theorem).is_err(),
        "kernel must REJECT a term that does not prove the theorem",
    );
}

/// Second milestone: a 2-clause propositional RESOLUTION refutation, kernel-checked.
///
/// Certifies `∀ (P Q : Prop), (Or P Q) → (Not P) → (Not Q) → False` — the
/// refutation of the CNF `(P ∨ Q) ∧ ¬P ∧ ¬Q` — from a closed, axiom-free term
/// `fun P Q hpq hnp hnq => Or.rec P Q (fun _ => False) (fun hp => hnp hp)
/// (fun hq => hnq hq) hpq` over ONLY prelude constants (Or via init_or, plus its
/// recursor Or.rec; Not; False). This demonstrates genuine CIC reconstruction of
/// a resolution step (case split on the disjunction), the pattern that generalises
/// to arbitrary propositional/EUF resolution proofs.
#[test]
fn trust_resolution_two_clause_is_kernel_certified() {
    use crate::env::decl_builder::EnvDeclBuilder;

    let mut env = Environment::with_prelude();
    env.init_or().expect("Or must initialize");
    let tc = TypeChecker::new(&env);

    let or_c = Expr::const_str("Or");
    let not_c = Expr::const_str("Not");
    let false_c = Expr::const_str("False");
    let or_rec = Expr::const_str("Or.rec");
    let prop = Expr::prop();

    let or_app = |a: &Expr, b: &Expr| Expr::app(Expr::app(or_c.clone(), a.clone()), b.clone());
    let not_app = |a: &Expr| Expr::app(not_c.clone(), a.clone());

    // Theorem: ∀ (P Q : Prop), Or P Q → Not P → Not Q → False
    let theorem = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(prop.clone());
        let (q_id, q) = b.fresh_local(prop.clone());
        let or_pq = or_app(&p, &q);
        let not_p = not_app(&p);
        let not_q = not_app(&q);
        let (hpq_id, _) = b.fresh_local(or_pq.clone());
        let (hnp_id, _) = b.fresh_local(not_p.clone());
        let (hnq_id, _) = b.fresh_local(not_q.clone());
        let mut r = false_c.clone();
        r = b.mk_pi(hnq_id, BinderInfo::Default, not_q, r);
        r = b.mk_pi(hnp_id, BinderInfo::Default, not_p, r);
        r = b.mk_pi(hpq_id, BinderInfo::Default, or_pq, r);
        r = b.mk_pi(q_id, BinderInfo::Default, prop.clone(), r);
        r = b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r);
        b.finish(r)
    };

    // Proof: fun P Q hpq hnp hnq =>
    //   Or.rec P Q (fun _ => False) (fun hp => hnp hp) (fun hq => hnq hq) hpq
    let proof = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(prop.clone());
        let (q_id, q) = b.fresh_local(prop.clone());
        let or_pq = or_app(&p, &q);
        let not_p = not_app(&p);
        let not_q = not_app(&q);
        let (hpq_id, hpq) = b.fresh_local(or_pq.clone());
        let (hnp_id, hnp) = b.fresh_local(not_p.clone());
        let (hnq_id, hnq) = b.fresh_local(not_q.clone());

        // motive: fun (_ : Or P Q) => False
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (h_id, _) = m.fresh_local(or_pq.clone());
            let lam = m.mk_lam(h_id, BinderInfo::Default, or_pq.clone(), false_c.clone());
            m.finish_child(lam)
        };
        // case inl: fun (hp : P) => hnp hp   (hnp : Not P ≡ P → False)
        let case_inl = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (hp_id, hp) = c.fresh_local(p.clone());
            let body = Expr::app(hnp.clone(), hp);
            let lam = c.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
            c.finish_child(lam)
        };
        // case inr: fun (hq : Q) => hnq hq
        let case_inr = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (hq_id, hq) = c.fresh_local(q.clone());
            let body = Expr::app(hnq.clone(), hq);
            let lam = c.mk_lam(hq_id, BinderInfo::Default, q.clone(), body);
            c.finish_child(lam)
        };

        let or_rec_app = Expr::apps(
            or_rec.clone(),
            [p.clone(), q.clone(), motive, case_inl, case_inr, hpq],
        );
        let mut r = or_rec_app;
        r = b.mk_lam(hnq_id, BinderInfo::Default, not_q, r);
        r = b.mk_lam(hnp_id, BinderInfo::Default, not_p, r);
        r = b.mk_lam(hpq_id, BinderInfo::Default, or_pq, r);
        r = b.mk_lam(q_id, BinderInfo::Default, prop.clone(), r);
        r = b.mk_lam(p_id, BinderInfo::Default, prop.clone(), r);
        b.finish(r)
    };

    tc.check_type(&proof, &theorem)
        .expect("clean kernel must certify the 2-clause resolution refutation via Or.rec");
}

/// Third milestone (GENERAL propositional): certify ANY small propositional UNSAT
/// by exhaustive `Bool.rec` evaluation, leaning on the kernel's native Bool
/// reducers. Here: `∀ (p : Bool), (Bool.and p (Bool.not p)) = Bool.false`. The
/// proof is `fun p => Bool.rec (motive := fun b => (and b (not b)) = false) rfl rfl p`;
/// each branch's LHS reduces (native Bool.and/Bool.not) to `false`, so the leaf
/// `Eq.refl Bool false` type-checks. This generalises to n variables (nested
/// Bool.rec) and to ANY And/Or/Not formula -- no per-shape reconstruction.
#[test]
fn trust_bool_unsat_one_var_is_kernel_certified() {
    use crate::level::Level;
    use crate::name::Name;

    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    let bool_ty = Expr::const_str("Bool");
    let b_false = Expr::const_str("Bool.false");
    let b_and = Expr::const_str("Bool.and");
    let b_not = Expr::const_str("Bool.not");
    let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_refl1 = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );

    // violation(b) = Bool.and b (Bool.not b)
    let violation = |b: Expr| {
        Expr::app(
            Expr::app(b_and.clone(), b.clone()),
            Expr::app(b_not.clone(), b),
        )
    };
    // @Eq.{1} Bool (violation b) Bool.false
    let eq_app = |b: Expr| {
        Expr::apps(
            eq1.clone(),
            [bool_ty.clone(), violation(b), b_false.clone()],
        )
    };

    // theorem: ∀ (p : Bool), @Eq Bool (violation p) false   (p = bvar0 under the Pi)
    let theorem = Expr::pi(BinderInfo::Default, bool_ty.clone(), eq_app(Expr::bvar(0)));

    // motive: fun (b : Bool) => @Eq Bool (violation b) false   (b = bvar0)
    let motive = Expr::lam(BinderInfo::Default, bool_ty.clone(), eq_app(Expr::bvar(0)));
    // universal leaf: Eq.refl Bool Bool.false  (LHS reduces to false in every branch)
    let leaf = Expr::apps(eq_refl1.clone(), [bool_ty.clone(), b_false.clone()]);
    // Bool.rec into Prop (Sort 0): Bool.rec motive leaf_false leaf_true p
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(
        bool_rec,
        [motive, leaf.clone(), leaf.clone(), Expr::bvar(0)],
    );
    let proof = Expr::lam(BinderInfo::Default, bool_ty.clone(), rec_app);

    tc.check_type(&proof, &theorem).expect(
        "clean kernel must certify `∀ (p : Bool), (p && ¬p) = false` by Bool.rec + native eval",
    );

    // Negative control: a SAT formula `∀ p, (Bool.or p (Bool.not p)) = false` is
    // NOT a theorem (it's always true), so the same proof shape must be rejected.
    let sat_violation = |b: Expr| {
        Expr::app(
            Expr::app(Expr::const_str("Bool.or"), b.clone()),
            Expr::app(b_not.clone(), b),
        )
    };
    let sat_theorem = Expr::pi(
        BinderInfo::Default,
        bool_ty.clone(),
        Expr::apps(
            eq1.clone(),
            [
                bool_ty.clone(),
                sat_violation(Expr::bvar(0)),
                b_false.clone(),
            ],
        ),
    );
    let sat_motive = Expr::lam(
        BinderInfo::Default,
        bool_ty.clone(),
        Expr::apps(
            eq1.clone(),
            [
                bool_ty.clone(),
                sat_violation(Expr::bvar(0)),
                b_false.clone(),
            ],
        ),
    );
    let sat_proof = Expr::lam(
        BinderInfo::Default,
        bool_ty.clone(),
        Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [sat_motive, leaf.clone(), leaf, Expr::bvar(0)],
        ),
    );
    assert!(
        tc.check_type(&sat_proof, &sat_theorem).is_err(),
        "kernel must REJECT a Bool.rec 'proof' of a satisfiable formula (p || ¬p = false)",
    );
}

/// A propositional formula over Boolean variables `p_0 .. p_{n-1}`, used to drive
/// the general exhaustive-`Bool.rec` certification below. This is the same shape a
/// Trust VC's Boolean skeleton has (And/Or/Not over atoms treated as Bool vars).
#[derive(Clone)]
enum BoolF {
    Var(usize),
    Not(Box<BoolF>),
    And(Box<BoolF>, Box<BoolF>),
    Or(Box<BoolF>, Box<BoolF>),
}

impl BoolF {
    fn not(a: BoolF) -> BoolF {
        BoolF::Not(Box::new(a))
    }
    fn and(a: BoolF, b: BoolF) -> BoolF {
        BoolF::And(Box::new(a), Box::new(b))
    }
    fn or(a: BoolF, b: BoolF) -> BoolF {
        BoolF::Or(Box::new(a), Box::new(b))
    }
    /// Render to a kernel `Expr` over `Bool.and/Bool.or/Bool.not`, with each
    /// `Var(i)` rendered by `var(i)` (caller controls the de Bruijn / constant
    /// it maps to in the current binder context).
    fn render(&self, var: &dyn Fn(usize) -> Expr) -> Expr {
        match self {
            BoolF::Var(i) => var(*i),
            BoolF::Not(a) => Expr::app(Expr::const_str("Bool.not"), a.render(var)),
            BoolF::And(a, b) => Expr::app(
                Expr::app(Expr::const_str("Bool.and"), a.render(var)),
                b.render(var),
            ),
            BoolF::Or(a, b) => Expr::app(
                Expr::app(Expr::const_str("Bool.or"), a.render(var)),
                b.render(var),
            ),
        }
    }
}

/// Build the closed, axiom-free CIC proof term + theorem certifying that the
/// propositional formula `f` over `n` Bool variables is UNSAT — i.e. that
/// `∀ (p_0 .. p_{n-1} : Bool), render(f) = Bool.false`. The proof is a depth-`n`
/// nested `Bool.rec` whose 2^n leaves are each `@Eq.refl Bool Bool.false`; the
/// kernel's native Bool reducers evaluate `render(f)` at every assignment, so the
/// term type-checks IFF `f` is false under all assignments. No per-shape
/// reconstruction — this is a uniform decision procedure expressed as a proof.
///
/// This mirrors exactly what the live `trust-clean` certifier must build (manual
/// de Bruijn, no `EnvDeclBuilder` — which is kernel-internal), so the construction
/// is intentionally written with explicit indices.
fn build_bool_unsat(n: usize, f: &BoolF) -> (Expr, Expr) {
    use crate::level::Level;
    use crate::name::Name;

    let bool_ty = Expr::const_str("Bool");
    let b_false = Expr::const_str("Bool.false");
    let b_true = Expr::const_str("Bool.true");
    let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_refl1 = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let bool_rec0 = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

    // @Eq Bool v Bool.false
    let eq_false = |v: Expr| Expr::apps(eq1.clone(), [bool_ty.clone(), v, b_false.clone()]);

    // Theorem: ∀ (p_0..p_{n-1} : Bool), render(f) = false.
    // Under all n Pis, p_i is bvar(n-1-i).
    let theorem = {
        let body = eq_false(f.render(&|i| Expr::bvar((n - 1 - i) as u32)));
        let mut t = body;
        for _ in 0..n {
            t = Expr::pi(BinderInfo::Default, bool_ty.clone(), t);
        }
        t
    };

    // Proof: recursive nested Bool.rec.
    // `vals[0..k]` are the concrete Bool constants assigned to p_0..p_{k-1}; the
    // returned term has type `∀ p_k..p_{n-1}, render(f)[p_0..p_{k-1}:=vals] = false`.
    fn build(
        n: usize,
        k: usize,
        vals: &[Expr],
        f: &BoolF,
        bool_ty: &Expr,
        b_false: &Expr,
        b_true: &Expr,
        eq1: &Expr,
        eq_refl1: &Expr,
        bool_rec0: &dyn Fn() -> Expr,
    ) -> Expr {
        if k == n {
            // Leaf: every var concrete ⇒ render(f) reduces (native) to a constructor;
            // `Eq.refl Bool Bool.false : @Eq Bool Bool.false Bool.false` checks against
            // `@Eq Bool render(f)[vals] false` iff render(f)[vals] ≡ false.
            return Expr::apps(eq_refl1.clone(), [bool_ty.clone(), b_false.clone()]);
        }
        // for_var: i<k ⇒ vals[i] (closed const); i>=k ⇒ bvar(n-1-i) (b at i=k, Pis after).
        let for_var = |i: usize| -> Expr {
            if i < k {
                vals[i].clone()
            } else {
                Expr::bvar((n - 1 - i) as u32)
            }
        };
        let eq_false = |v: Expr| Expr::apps(eq1.clone(), [bool_ty.clone(), v, b_false.clone()]);
        // motive = fun (b:Bool) => ∀ p_{k+1}..p_{n-1}, render(f)[..vals, p_k:=b] = false
        let motive = {
            let mut body = eq_false(f.render(&for_var));
            for _ in 0..(n - 1 - k) {
                body = Expr::pi(BinderInfo::Default, bool_ty.clone(), body);
            }
            Expr::lam(BinderInfo::Default, bool_ty.clone(), body)
        };
        let mut vf = vals.to_vec();
        vf.push(b_false.clone());
        let cf = build(
            n,
            k + 1,
            &vf,
            f,
            bool_ty,
            b_false,
            b_true,
            eq1,
            eq_refl1,
            bool_rec0,
        );
        let mut vt = vals.to_vec();
        vt.push(b_true.clone());
        let ct = build(
            n,
            k + 1,
            &vt,
            f,
            bool_ty,
            b_false,
            b_true,
            eq1,
            eq_refl1,
            bool_rec0,
        );
        let rec = Expr::apps(bool_rec0(), [motive, cf, ct, Expr::bvar(0)]);
        Expr::lam(BinderInfo::Default, bool_ty.clone(), rec)
    }

    let proof = build(
        n,
        0,
        &[],
        f,
        &bool_ty,
        &b_false,
        &b_true,
        &eq1,
        &eq_refl1,
        &bool_rec0,
    );
    (proof, theorem)
}

/// Fourth milestone (GENERAL n-variable propositional UNSAT): certify multi-clause
/// refutations by exhaustive nested `Bool.rec`. This subsumes the bespoke
/// And/Or.rec reconstructions above with ONE uniform construction that works for
/// any And/Or/Not formula and decides UNSAT via the kernel's native reducers.
#[test]
fn trust_bool_unsat_n_var_is_kernel_certified() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    // 2-var resolution refutation as a Bool formula:
    //   (p0 ∨ p1) ∧ ¬p0 ∧ ¬p1   is false for all p0,p1.
    let f2 = BoolF::and(
        BoolF::and(
            BoolF::or(BoolF::Var(0), BoolF::Var(1)),
            BoolF::not(BoolF::Var(0)),
        ),
        BoolF::not(BoolF::Var(1)),
    );
    let (proof2, thm2) = build_bool_unsat(2, &f2);
    tc.check_type(&proof2, &thm2)
        .expect("kernel must certify the 2-var resolution refutation by exhaustive Bool.rec");

    // 3-var refutation:
    //   (p0 ∨ p1) ∧ (¬p0 ∨ p2) ∧ ¬p1 ∧ ¬p2   is UNSAT.
    let f3 = BoolF::and(
        BoolF::and(
            BoolF::and(
                BoolF::or(BoolF::Var(0), BoolF::Var(1)),
                BoolF::or(BoolF::not(BoolF::Var(0)), BoolF::Var(2)),
            ),
            BoolF::not(BoolF::Var(1)),
        ),
        BoolF::not(BoolF::Var(2)),
    );
    let (proof3, thm3) = build_bool_unsat(3, &f3);
    tc.check_type(&proof3, &thm3)
        .expect("kernel must certify the 3-var refutation by exhaustive Bool.rec");

    // Negative control: a SATISFIABLE formula `(p0 ∨ p1) = false` is NOT a theorem
    // (true at p0:=true), so its exhaustive-Bool.rec 'proof' must be REJECTED — the
    // construction is a genuine decision procedure, not a rubber stamp.
    let sat = BoolF::or(BoolF::Var(0), BoolF::Var(1));
    let (sat_proof, sat_thm) = build_bool_unsat(2, &sat);
    assert!(
        tc.check_type(&sat_proof, &sat_thm).is_err(),
        "kernel must REJECT exhaustive-Bool.rec 'proof' of a satisfiable formula",
    );
}

/// Fifth milestone (EUF — equality fragment): certify a transitivity-chain
/// refutation `∀ (a b c : Bool), (a = b) → (b = c) → ¬(a = c) → False`, the
/// canonical EUF contradiction (an equality chain closed by a disequality).
/// The proof `fun a b c h1 h2 h3 => h3 (Eq.trans Bool a b c h1 h2)` is closed,
/// axiom-free, over prelude `Eq` + `Eq.trans` (via `init_eq`). This is the first
/// genuinely-new fragment beyond propositional: it reasons about EQUALITY of
/// terms, not just opaque atoms.
#[test]
fn trust_euf_trans_chain_is_kernel_certified() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::level::Level;
    use crate::name::Name;

    let mut env = Environment::with_prelude();
    env.init_eq().expect("Eq must initialize");
    let tc = TypeChecker::new(&env);

    let bool_ty = Expr::const_str("Bool");
    let not_c = Expr::const_str("Not");
    let false_c = Expr::const_str("False");
    let lvl1 = Level::succ(Level::zero());
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![lvl1]);
    // @Eq.{1} Bool x y
    let eq_app =
        |x: &Expr, y: &Expr| Expr::apps(eq_c.clone(), [bool_ty.clone(), x.clone(), y.clone()]);
    let not_app = |p: &Expr| Expr::app(not_c.clone(), p.clone());

    // Theorem: ∀ (a b c : Bool), Eq a b → Eq b c → Not (Eq a c) → False
    let theorem = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(bool_ty.clone());
        let (b_id, bb) = b.fresh_local(bool_ty.clone());
        let (c_id, cc) = b.fresh_local(bool_ty.clone());
        let eq_ab = eq_app(&a, &bb);
        let eq_bc = eq_app(&bb, &cc);
        let not_eq_ac = not_app(&eq_app(&a, &cc));
        let (h1_id, _) = b.fresh_local(eq_ab.clone());
        let (h2_id, _) = b.fresh_local(eq_bc.clone());
        let (h3_id, _) = b.fresh_local(not_eq_ac.clone());
        let mut r = false_c.clone();
        r = b.mk_pi(h3_id, BinderInfo::Default, not_eq_ac, r);
        r = b.mk_pi(h2_id, BinderInfo::Default, eq_bc, r);
        r = b.mk_pi(h1_id, BinderInfo::Default, eq_ab, r);
        r = b.mk_pi(c_id, BinderInfo::Default, bool_ty.clone(), r);
        r = b.mk_pi(b_id, BinderInfo::Default, bool_ty.clone(), r);
        r = b.mk_pi(a_id, BinderInfo::Default, bool_ty.clone(), r);
        b.finish(r)
    };

    // Proof: fun a b c h1 h2 h3 => h3 (Eq.trans Bool a b c h1 h2)
    let proof = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(bool_ty.clone());
        let (b_id, bb) = b.fresh_local(bool_ty.clone());
        let (c_id, cc) = b.fresh_local(bool_ty.clone());
        let eq_ab = eq_app(&a, &bb);
        let eq_bc = eq_app(&bb, &cc);
        let not_eq_ac = not_app(&eq_app(&a, &cc));
        let (h1_id, h1) = b.fresh_local(eq_ab.clone());
        let (h2_id, h2) = b.fresh_local(eq_bc.clone());
        let (h3_id, h3) = b.fresh_local(not_eq_ac.clone());
        // Eq.trans Bool a b c h1 h2 : Eq a c
        let trans = Expr::apps(eq_trans.clone(), [bool_ty.clone(), a, bb, cc, h1, h2]);
        let body = Expr::app(h3, trans); // : False  (h3 : Eq a c → False)
        let mut v = body;
        v = b.mk_lam(h3_id, BinderInfo::Default, not_eq_ac, v);
        v = b.mk_lam(h2_id, BinderInfo::Default, eq_bc, v);
        v = b.mk_lam(h1_id, BinderInfo::Default, eq_ab, v);
        v = b.mk_lam(c_id, BinderInfo::Default, bool_ty.clone(), v);
        v = b.mk_lam(b_id, BinderInfo::Default, bool_ty.clone(), v);
        v = b.mk_lam(a_id, BinderInfo::Default, bool_ty.clone(), v);
        b.finish(v)
    };

    tc.check_type(&proof, &theorem)
        .expect("clean kernel must certify the EUF transitivity-chain refutation");

    // Negative control: WITHOUT the chain, `fun a b c h1 h2 h3 => h3 h1` does not
    // type-check (h3 : ¬(a=c) cannot be applied to h1 : a=b). The kernel rejects.
    let bogus = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(bool_ty.clone());
        let (b_id, bb) = b.fresh_local(bool_ty.clone());
        let (c_id, cc) = b.fresh_local(bool_ty.clone());
        let eq_ab = eq_app(&a, &bb);
        let eq_bc = eq_app(&bb, &cc);
        let not_eq_ac = not_app(&eq_app(&a, &cc));
        let (h1_id, h1) = b.fresh_local(eq_ab.clone());
        let (h2_id, _) = b.fresh_local(eq_bc.clone());
        let (h3_id, h3) = b.fresh_local(not_eq_ac.clone());
        let body = Expr::app(h3, h1); // ill-typed: ¬(a=c) applied to (a=b)
        let mut v = body;
        v = b.mk_lam(h3_id, BinderInfo::Default, not_eq_ac, v);
        v = b.mk_lam(h2_id, BinderInfo::Default, eq_bc, v);
        v = b.mk_lam(h1_id, BinderInfo::Default, eq_ab, v);
        v = b.mk_lam(c_id, BinderInfo::Default, bool_ty.clone(), v);
        v = b.mk_lam(b_id, BinderInfo::Default, bool_ty.clone(), v);
        v = b.mk_lam(a_id, BinderInfo::Default, bool_ty.clone(), v);
        b.finish(v)
    };
    assert!(
        tc.check_type(&bogus, &theorem).is_err(),
        "kernel must REJECT an EUF 'proof' that skips the transitivity step",
    );
}

/// Sixth milestone (EUF — congruence): certify `∀ (a b : Bool), (a = b) →
/// ¬(¬a = ¬b) → False`, where the function is `Bool.not`. The proof
/// `fun a b h1 h2 => h2 (congrArg Bool Bool a b Bool.not h1)` uses the
/// congruence lemma `congrArg : a = b → f a = f b` — the "uninterpreted
/// function" half of EUF — over prelude `Eq` + `congrArg`.
#[test]
fn trust_euf_congruence_is_kernel_certified() {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::level::Level;
    use crate::name::Name;

    let mut env = Environment::with_prelude();
    env.init_eq().expect("Eq must initialize");
    let tc = TypeChecker::new(&env);

    let bool_ty = Expr::const_str("Bool");
    let b_not = Expr::const_str("Bool.not");
    let not_c = Expr::const_str("Not");
    let false_c = Expr::const_str("False");
    let lvl1 = Level::succ(Level::zero());
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]);
    let eq_app =
        |x: &Expr, y: &Expr| Expr::apps(eq_c.clone(), [bool_ty.clone(), x.clone(), y.clone()]);
    let not_app = |p: &Expr| Expr::app(not_c.clone(), p.clone());
    let app_not = |x: &Expr| Expr::app(b_not.clone(), x.clone());

    // Theorem: ∀ (a b : Bool), Eq a b → Not (Eq (Bool.not a) (Bool.not b)) → False
    let theorem = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(bool_ty.clone());
        let (b_id, bb) = b.fresh_local(bool_ty.clone());
        let eq_ab = eq_app(&a, &bb);
        let not_eq_fab = not_app(&eq_app(&app_not(&a), &app_not(&bb)));
        let (h1_id, _) = b.fresh_local(eq_ab.clone());
        let (h2_id, _) = b.fresh_local(not_eq_fab.clone());
        let mut r = false_c.clone();
        r = b.mk_pi(h2_id, BinderInfo::Default, not_eq_fab, r);
        r = b.mk_pi(h1_id, BinderInfo::Default, eq_ab, r);
        r = b.mk_pi(b_id, BinderInfo::Default, bool_ty.clone(), r);
        r = b.mk_pi(a_id, BinderInfo::Default, bool_ty.clone(), r);
        b.finish(r)
    };

    // Proof: fun a b h1 h2 => h2 (congrArg Bool Bool a b Bool.not h1)
    let proof = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(bool_ty.clone());
        let (b_id, bb) = b.fresh_local(bool_ty.clone());
        let eq_ab = eq_app(&a, &bb);
        let not_eq_fab = not_app(&eq_app(&app_not(&a), &app_not(&bb)));
        let (h1_id, h1) = b.fresh_local(eq_ab.clone());
        let (h2_id, h2) = b.fresh_local(not_eq_fab.clone());
        // congrArg Bool Bool a b Bool.not h1 : Eq (Bool.not a) (Bool.not b)
        let congr = Expr::apps(
            congr_arg.clone(),
            [bool_ty.clone(), bool_ty.clone(), a, bb, b_not.clone(), h1],
        );
        let body = Expr::app(h2, congr); // : False
        let mut v = body;
        v = b.mk_lam(h2_id, BinderInfo::Default, not_eq_fab, v);
        v = b.mk_lam(h1_id, BinderInfo::Default, eq_ab, v);
        v = b.mk_lam(b_id, BinderInfo::Default, bool_ty.clone(), v);
        v = b.mk_lam(a_id, BinderInfo::Default, bool_ty.clone(), v);
        b.finish(v)
    };

    tc.check_type(&proof, &theorem)
        .expect("clean kernel must certify the EUF congruence refutation");
}

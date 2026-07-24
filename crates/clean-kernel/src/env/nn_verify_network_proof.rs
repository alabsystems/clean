// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T71: `network_cert_sound` — whole-network certificate chaining proof.
//!
//! Given N per-layer certificates where each consecutive pair satisfies
//! `subset`, proves the first bound is a subset of the last via structural
//! induction on `intermediates` using T70 (`entailment_transitivity`).
//!
//! Part of #3220, #3242, #3265.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for T71 proof construction.
struct T71Consts {
    nat: Expr,
    ib: Expr,
    ib_subset: Expr,
    and: Expr,
    and_left: Expr,
    and_right: Expr,
    list: Expr,
    list_rec_type0: Expr, // @{1, 0}: motive → Type 0 (for chainSubsetBetween defn)
    list_rec_prop: Expr,  // @{0, 0}: motive → Prop (for network_cert_sound proof)
    t70: Expr,            // entailment_transitivity
    prop: Expr,
}

impl T71Consts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            list: Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            list_rec_type0: Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            list_rec_prop: Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), Level::zero()],
            ),
            t70: Expr::const_(
                Name::from_string("NNVerify.entailment_transitivity"),
                vec![],
            ),
            prop: Expr::sort(Level::zero()),
        }
    }

    /// Build `IntervalBounds.subset @d b1 b2`.
    fn subset(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }

    /// Build `And a b`.
    fn and_(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), a), b)
    }

    /// Build `And.left @a @b h`.
    fn and_left_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_left.clone(), a), b), h)
    }

    /// Build `And.right @a @b h`.
    fn and_right_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.and_right.clone(), a), b), h)
    }

    /// Build `IntervalBounds d` (the type).
    fn ib_d(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    /// Build `List (IntervalBounds d)`.
    fn list_ib_d(&self, d: &Expr) -> Expr {
        Expr::app(self.list.clone(), self.ib_d(d))
    }

    /// Build `chainSubsetBetween @d bf intermediates bl`.
    fn chain_subset_between(&self, d: &Expr, bf: &Expr, intermediates: &Expr, bl: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("NNVerify.chainSubsetBetween"), vec![]),
                        d.clone(),
                    ),
                    bf.clone(),
                ),
                intermediates.clone(),
            ),
            bl.clone(),
        )
    }

    /// Build `entailment_transitivity @d bf b_mid bl h_sub_fb h_sub_bl`.
    fn apply_t70(
        &self,
        d: &Expr,
        bf: &Expr,
        b_mid: &Expr,
        bl: &Expr,
        h_sub_fb: Expr,
        h_sub_bl: Expr,
    ) -> Expr {
        Expr::apps(
            self.t70.clone(),
            [
                d.clone(),
                bf.clone(),
                b_mid.clone(),
                bl.clone(),
                h_sub_fb,
                h_sub_bl,
            ],
        )
    }
}

// ── chainSubsetBetween definition ──────────────────────────────────────

/// Type: `{d : Nat} → IB d → List (IB d) → IB d → Prop`.
fn build_chain_subset_between_type(c: &T71Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_d(&d);
    let list_ib_d = c.list_ib_d(&d);
    let (bf_id, _bf) = b.fresh_local(ib_d.clone());
    let (ints_id, _ints) = b.fresh_local(list_ib_d.clone());
    let (bl_id, _bl) = b.fresh_local(ib_d.clone());
    let e = b.mk_pi(bl_id, BinderInfo::Default, ib_d.clone(), c.prop.clone());
    let e = b.mk_pi(ints_id, BinderInfo::Default, list_ib_d, e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

/// Value: threads "current bound" via `List.rec @{1, 0}` with motive `fun _ => IB d → Prop`.
/// `IB d → Prop : Type 0` (imax(1,1)=1), so u_1 = 1.
fn build_chain_subset_between_value(c: &T71Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_d(&d);
    let list_ib_d = c.list_ib_d(&d);
    let (bf_id, bf) = b.fresh_local(ib_d.clone());
    let (ints_id, ints) = b.fresh_local(list_ib_d.clone());
    let (bl_id, bl) = b.fresh_local(ib_d.clone());

    // Motive: fun (_ : List (IB d)) => IB d → Prop
    // IB d → Prop : Type 0 (since Prop : Sort 1, imax(1,1)=1)
    // So motive type: List (IB d) → Type 0, requiring u_1 = 1.
    let ib_d_to_prop = Expr::arrow(ib_d.clone(), c.prop.clone());
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(list_ib_d.clone());
        let r = ch.mk_lam(
            m_id,
            BinderInfo::Default,
            list_ib_d.clone(),
            ib_d_to_prop.clone(),
        );
        ch.finish_child(r)
    };

    // Nil case: fun (b_cur : IB d) => subset b_cur bl
    // Type: IB d → Prop = motive []
    let nil_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (cur_id, cur) = ch.fresh_local(ib_d.clone());
        let r = ch.mk_lam(
            cur_id,
            BinderInfo::Default,
            ib_d.clone(),
            c.subset(&d, &cur, &bl),
        );
        ch.finish_child(r)
    };

    // Cons case: fun (head : IB d) (tail : List (IB d)) (ih : IB d → Prop)
    //              (b_cur : IB d) => And (subset b_cur head) (ih head)
    // ih has type motive tail = IB d → Prop.
    // Body And (subset b_cur head) (ih head) : Prop = (motive (head::tail)) b_cur.
    let cons_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (head_id, head) = ch.fresh_local(ib_d.clone());
        let (tail_id, _tail) = ch.fresh_local(list_ib_d.clone());
        let (ih_id, ih) = ch.fresh_local(ib_d_to_prop.clone());
        let (cur_id, cur) = ch.fresh_local(ib_d.clone());
        let body = c.and_(c.subset(&d, &cur, &head), Expr::app(ih, head.clone()));
        let r = ch.mk_lam(cur_id, BinderInfo::Default, ib_d.clone(), body);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ib_d_to_prop, r);
        let r = ch.mk_lam(tail_id, BinderInfo::Default, list_ib_d.clone(), r);
        let r = ch.mk_lam(head_id, BinderInfo::Default, ib_d.clone(), r);
        ch.finish_child(r)
    };

    // (List.rec @{1, 0} @(IB d) motive nil_case cons_case intermediates) bf
    let rec_result = Expr::apps(
        c.list_rec_type0.clone(),
        [ib_d.clone(), motive, nil_case, cons_case, ints],
    );
    let body = Expr::app(rec_result, bf);

    let e = b.mk_lam(bl_id, BinderInfo::Default, ib_d.clone(), body);
    let e = b.mk_lam(ints_id, BinderInfo::Default, list_ib_d, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

// ── network_cert_sound theorem ─────────────────────────────────────────

/// Type: `{d} → (bf bl : IB d) → (ints : List (IB d)) → csb d bf ints bl → subset bf bl`.
fn build_network_cert_sound_type(c: &T71Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_d(&d);
    let list_ib_d = c.list_ib_d(&d);
    let (bf_id, bf) = b.fresh_local(ib_d.clone());
    let (bl_id, bl) = b.fresh_local(ib_d.clone());
    let (ints_id, ints) = b.fresh_local(list_ib_d.clone());

    let chain_hyp = c.chain_subset_between(&d, &bf, &ints, &bl);
    let conclusion = c.subset(&d, &bf, &bl);

    let (h_id, _h) = b.fresh_local(chain_hyp.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, chain_hyp, conclusion);
    let e = b.mk_pi(ints_id, BinderInfo::Default, list_ib_d, e);
    let e = b.mk_pi(bl_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

/// Cons case: decompose `And (subset b_cur head) (csb head tail bl)`, apply IH + T70.
fn build_proof_cons_case(
    c: &T71Consts,
    parent: &EnvDeclBuilder,
    d: &Expr,
    bl: &Expr,
    ib_d: &Expr,
    list_ib_d: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (head_id, head) = ch.fresh_local(ib_d.clone());
    let (tail_id, tail) = ch.fresh_local(list_ib_d.clone());

    // IH type: ∀ (b_cur : IB d), csb d b_cur tail bl → subset b_cur bl
    let ih_type = {
        let (ih_cur_id, ih_cur) = ch.fresh_local(ib_d.clone());
        let chain_ih = c.chain_subset_between(d, &ih_cur, &tail, bl);
        let sub_ih = c.subset(d, &ih_cur, bl);
        let (ih_h_id, _) = ch.fresh_local(chain_ih.clone());
        let inner = ch.mk_pi(ih_h_id, BinderInfo::Default, chain_ih, sub_ih);
        ch.mk_pi(ih_cur_id, BinderInfo::Default, ib_d.clone(), inner)
    };
    let (ih_id, ih) = ch.fresh_local(ih_type.clone());
    let (cur_id, cur) = ch.fresh_local(ib_d.clone());

    // h : And (subset b_cur head) (csb d head tail bl)
    let sub_cur_head = c.subset(d, &cur, &head);
    let chain_head_tail_bl = c.chain_subset_between(d, &head, &tail, bl);
    let h_type = c.and_(sub_cur_head.clone(), chain_head_tail_bl.clone());
    let (h_id, h) = ch.fresh_local(h_type.clone());

    let h_left = c.and_left_app(sub_cur_head.clone(), chain_head_tail_bl.clone(), h.clone());
    let h_right = c.and_right_app(sub_cur_head, chain_head_tail_bl, h);
    let ih_applied = Expr::app(Expr::app(ih, head.clone()), h_right);
    let proof = c.apply_t70(d, &cur, &head, bl, h_left, ih_applied);

    let r = ch.mk_lam(h_id, BinderInfo::Default, h_type, proof);
    let r = ch.mk_lam(cur_id, BinderInfo::Default, ib_d.clone(), r);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
    let r = ch.mk_lam(tail_id, BinderInfo::Default, list_ib_d.clone(), r);
    let r = ch.mk_lam(head_id, BinderInfo::Default, ib_d.clone(), r);
    ch.finish_child(r)
}

/// Proof via `List.rec @{0, 0}` with motive `fun ints => ∀ b_cur, csb d b_cur ints bl →
/// subset b_cur bl`. Universally quantifying `b_cur` gives the IH the right shape.
fn build_network_cert_sound_proof(c: &T71Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = c.ib_d(&d);
    let list_ib_d = c.list_ib_d(&d);
    let (bf_id, bf) = b.fresh_local(ib_d.clone());
    let (bl_id, bl) = b.fresh_local(ib_d.clone());
    let (ints_id, ints) = b.fresh_local(list_ib_d.clone());

    // Motive: fun ints => ∀ (b_cur : IB d), csb d b_cur ints bl → subset b_cur bl
    // Body in Prop via imax(1,0)=0, so u_1 = 0.
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, m_ints) = ch.fresh_local(list_ib_d.clone());
        let (cur_id, cur) = ch.fresh_local(ib_d.clone());
        let chain_hyp = c.chain_subset_between(&d, &cur, &m_ints, &bl);
        let (h_id, _) = ch.fresh_local(chain_hyp.clone());
        let inner = ch.mk_pi(
            h_id,
            BinderInfo::Default,
            chain_hyp,
            c.subset(&d, &cur, &bl),
        );
        let body = ch.mk_pi(cur_id, BinderInfo::Default, ib_d.clone(), inner);
        let r = ch.mk_lam(m_id, BinderInfo::Default, list_ib_d.clone(), body);
        ch.finish_child(r)
    };

    // Nil case: fun b_cur h => h  (csb reduces to subset b_cur bl)
    let nil_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (cur_id, cur) = ch.fresh_local(ib_d.clone());
        let sub_cur_bl = c.subset(&d, &cur, &bl);
        let (h_id, h) = ch.fresh_local(sub_cur_bl.clone());
        let r = ch.mk_lam(h_id, BinderInfo::Default, sub_cur_bl, h);
        let r = ch.mk_lam(cur_id, BinderInfo::Default, ib_d.clone(), r);
        ch.finish_child(r)
    };

    let cons_case = build_proof_cons_case(c, &b, &d, &bl, &ib_d, &list_ib_d);

    // (List.rec @{0, 0} @(IB d) motive nil_case cons_case intermediates) bf
    let rec_result = Expr::apps(
        c.list_rec_prop.clone(),
        [ib_d.clone(), motive, nil_case, cons_case, ints],
    );
    let body = Expr::app(rec_result, bf);

    let e = b.mk_lam(ints_id, BinderInfo::Default, list_ib_d, body);
    let e = b.mk_lam(bl_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

// ── Environment registration ───────────────────────────────────────────

impl Environment {
    /// Initialize T71 (network_cert_sound) and supporting definitions.
    ///
    /// Depends on: `init_nn_verify_proofs()` (T70), `init_list()`, `init_and()`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `chainSubsetBetween` and `network_cert_sound` registered
    /// ENSURES: Idempotent
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_network_proof(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_network_proof_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_nn_verify_proofs()?;
        self.init_list()?;
        self.init_and()?;

        let c = T71Consts::new();
        self.register_chain_subset_between(&c)?;
        self.register_network_cert_sound(&c)?;

        self.nn_verify_network_proof_init = true;
        Ok(())
    }

    /// Register `chainSubsetBetween` as a reducible definition.
    fn register_chain_subset_between(&mut self, c: &T71Consts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.chainSubsetBetween"),
            level_params: vec![],
            type_: build_chain_subset_between_type(c),
            value: build_chain_subset_between_value(c),
            is_reducible: true,
        })
    }

    /// Register T71: `network_cert_sound` theorem.
    fn register_network_cert_sound(&mut self, c: &T71Consts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.network_cert_sound"),
            level_params: vec![],
            type_: build_network_cert_sound_type(c),
            value: build_network_cert_sound_proof(c),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::ExprKind;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_network_proof()
            .expect("init_nn_verify_network_proof should succeed");
        env
    }

    #[test]
    fn test_chain_subset_between_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.chainSubsetBetween"))
                .is_some(),
            "chainSubsetBetween should be registered"
        );
    }

    #[test]
    fn test_chain_subset_between_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let csb = env
            .get_const(&Name::from_string("NNVerify.chainSubsetBetween"))
            .expect("chainSubsetBetween should exist");
        assert!(csb.value.is_some(), "should have a definition value");
        let val = csb.value.as_ref().unwrap();
        let inferred = tc
            .infer_type(val)
            .expect("definition value should type-check");
        assert!(
            tc.is_def_eq(&inferred, &csb.type_),
            "inferred type should match declared type"
        );
    }

    #[test]
    fn test_network_cert_sound_registered_and_is_theorem() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.network_cert_sound"))
            .expect("network_cert_sound should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "should have a proof term");
        assert!(
            !info.sorry_summary().has_sorry,
            "proof should not use sorry"
        );
    }

    #[test]
    fn test_network_cert_sound_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let thm = env
            .get_const(&Name::from_string("NNVerify.network_cert_sound"))
            .expect("network_cert_sound should exist");
        let _ = tc
            .infer_sort(&thm.type_)
            .expect("type should live in a sort");
        assert!(
            matches!(thm.type_.kind(), ExprKind::Pi(..)),
            "type should be a Pi"
        );
        let proof = thm.value.as_ref().unwrap();
        let inferred = tc.infer_type(proof).expect("proof should type-check");
        assert!(
            tc.is_def_eq(&inferred, &thm.type_),
            "inferred type should match declared"
        );
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_network_proof().expect("first init");
        env.init_nn_verify_network_proof().expect("second init");
    }
}

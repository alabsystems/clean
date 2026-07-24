// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **S6 assemble** ring identity of the
//! `hc24_core` operator induction.
//!
//! S6 of the worked chain folds the three IH-bounded legs `P, 2R, Q` (each
//! `≤ 8^n·SG²`, `≤ 2·8^n·SG·SH`, `≤ 8^n·SH²`) into the closed product form
//! `8^n·(SG+SH)²`. This file registers the pure-`Rat` ring identity that
//! collapse needs, for a free scalar `p` (instantiated at `p := 8^n`) and free
//! `sg, sh` (the two square-sums `SG, SH`):
//!
//! ```text
//! BoolAnalysis.hc24Assemble : ∀ (p sg sh : Rat),
//!   @Eq Rat
//!     (Rat.add (Rat.mul p (Rat.mul sg sg))
//!              (Rat.add (Rat.mul (1+1) (Rat.mul p (Rat.mul sg sh)))
//!                       (Rat.mul p (Rat.mul sh sh))))
//!     (Rat.mul p (Rat.mul (Rat.add sg sh) (Rat.add sg sh)))
//! ```
//!
//! i.e. `p·sg² + (2·(p·(sg·sh)) + p·sh²) = p·(sg+sh)²`. The right-associated LHS
//! matches the `add_le_add`-chained shape `P + (2R + Q)` the step produces.
//!
//! ## Proof route (RHS → LHS, then `Eq.symm`)
//!
//! 1. `Rat.add_sq_regroup sg sh : (sg+sh)·(sg+sh) = (sg·sg + sh·sh) + (1+1)·(sg·sh)`.
//! 2. `cong_right` under `p·_` lifts it to `p·(sg+sh)² = p·E` (E = the regroup RHS).
//! 3. `Rat.left_distrib` splits `p·E = p·(sg²+sh²) + p·((1+1)·(sg·sh))`.
//! 4. `Rat.left_distrib` on the first summand: `p·(sg²+sh²) = p·sg² + p·sh²`.
//! 5. The cross summand `p·((1+1)·(sg·sh)) = (1+1)·(p·(sg·sh))` via
//!    `mul_assoc⁻¹ → mul_comm → mul_assoc` (pull `p` past the `(1+1)` scalar).
//! 6. Re-associate `(p·sg² + p·sh²) + (1+1)·(p·(sg·sh))` into the right-assoc
//!    target `p·sg² + ((1+1)·(p·(sg·sh)) + p·sh²)` via `add_assoc` / `add_comm`.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `Rat.add_sq_regroup` (itself Constructive) and the `Rat` ring
//! surface (`left_distrib`, `mul_assoc`, `mul_comm`, `add_assoc`, `add_comm`,
//! `congrArg`, `Eq.*`).

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// `Rat.add_sq_regroup X Y : (X+Y)·(X+Y) = (X·X + Y·Y) + (1+1)·(X·Y)`.
fn add_sq_regroup(x: &Expr, y: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
        [x.clone(), y.clone()],
    )
}

/// Build `p·((1+1)·X) = (1+1)·(p·X)` for free `p`, `X` (X := sg·sh).
///
///   `p·(2·X) = (p·2)·X`     [symm (mul_assoc p 2 X)]
///   `(p·2)·X = (2·p)·X`     [cong_left (·X) (mul_comm p 2)]
///   `(2·p)·X = 2·(p·X)`     [mul_assoc 2 p X]
fn pull_scalar(c: &RingConsts, parent: &EnvDeclBuilder, p: &Expr, x: &Expr) -> Expr {
    let two = c.two();
    let mul_c = c.mul_const();
    let two_x = c.mul(two.clone(), x.clone()); // 2·X
    let lhs_p2x = c.mul(p.clone(), two_x.clone()); // p·(2·X)
    let p_two = c.mul(p.clone(), two.clone()); // p·2
    let two_p = c.mul(two.clone(), p.clone()); // 2·p
    let p2_x = c.mul(p_two.clone(), x.clone()); // (p·2)·X
    let two_p_x = c.mul(two_p.clone(), x.clone()); // (2·p)·X
    let px = c.mul(p.clone(), x.clone()); // p·X
    let two_px = c.mul(two.clone(), px.clone()); // 2·(p·X)

    // s1 : p·(2·X) = (p·2)·X   [symm of mul_assoc p 2 X : (p·2)·X = p·(2·X)]
    let ma = c.massoc(p.clone(), two.clone(), x.clone());
    let s1 = c.symm(p2_x.clone(), lhs_p2x.clone(), ma);
    // s2 : (p·2)·X = (2·p)·X   [cong_left (·X) of mul_comm p 2 : p·2 = 2·p]
    let hcomm = c.mcomm(p.clone(), two.clone());
    let s2 = c.cong_left(
        parent,
        &mul_c,
        p_two.clone(),
        two_p.clone(),
        x.clone(),
        hcomm,
    );
    // s3 : (2·p)·X = 2·(p·X)   [mul_assoc 2 p X]
    let s3 = c.massoc(two.clone(), p.clone(), x.clone());

    let t1 = c.trans(lhs_p2x.clone(), p2_x.clone(), two_p_x.clone(), s1, s2);
    c.trans(lhs_p2x, two_p_x, two_px, t1, s3)
}

/// Build the type + proof of `BoolAnalysis.hc24Assemble`.
fn build_hc24_assemble(c: &RingConsts) -> (Expr, Expr) {
    // lhs(p,sg,sh) := p·sg² + ((1+1)·(p·(sg·sh)) + p·sh²)
    let lhs_of = |p: &Expr, sg: &Expr, sh: &Expr| -> Expr {
        let p_sg2 = c.mul(p.clone(), c.mul(sg.clone(), sg.clone()));
        let p_sh2 = c.mul(p.clone(), c.mul(sh.clone(), sh.clone()));
        let p_sgsh = c.mul(p.clone(), c.mul(sg.clone(), sh.clone()));
        let two_p_sgsh = c.mul(c.two(), p_sgsh);
        c.add(p_sg2, c.add(two_p_sgsh, p_sh2))
    };
    // rhs(p,sg,sh) := p·((sg+sh)·(sg+sh))
    let rhs_of = |p: &Expr, sg: &Expr, sh: &Expr| -> Expr {
        let s = c.add(sg.clone(), sh.clone());
        c.mul(p.clone(), c.mul(s.clone(), s))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.rat());
        let (sg_id, sg) = b.fresh_local(c.rat());
        let (sh_id, sh) = b.fresh_local(c.rat());
        let body = c.eq(lhs_of(&p, &sg, &sh), rhs_of(&p, &sg, &sh));
        let e = b.mk_pi(sh_id, BinderInfo::Default, c.rat(), body);
        let e = b.mk_pi(sg_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(p_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.rat());
        let (sg_id, sg) = b.fresh_local(c.rat());
        let (sh_id, sh) = b.fresh_local(c.rat());

        let two = c.two();
        let add_c = c.add_const();
        let mul_c = c.mul_const();

        let sg2 = c.mul(sg.clone(), sg.clone());
        let sh2 = c.mul(sh.clone(), sh.clone());
        let sgsh = c.mul(sg.clone(), sh.clone());
        let s = c.add(sg.clone(), sh.clone());
        let ss = c.mul(s.clone(), s.clone()); // (sg+sh)²

        // E := (sg²+sh²) + 2·(sg·sh)   [add_sq_regroup RHS]
        let sg2_sh2 = c.add(sg2.clone(), sh2.clone());
        let two_sgsh = c.mul(two.clone(), sgsh.clone());
        let e_expr = c.add(sg2_sh2.clone(), two_sgsh.clone());

        let rhs = c.mul(p.clone(), ss.clone()); // p·(sg+sh)²
        let p_e = c.mul(p.clone(), e_expr.clone()); // p·E

        // step1 : p·(sg+sh)² = p·E   [cong_right (p·_) of add_sq_regroup sg sh]
        let hreg = add_sq_regroup(&sg, &sh);
        let step1 = c.cong_right(&b, &mul_c, ss.clone(), e_expr.clone(), p.clone(), hreg);

        // step2 : p·E = p·(sg²+sh²) + p·(2·(sg·sh))   [left_distrib p (sg²+sh²) (2·(sg·sh))]
        let p_sg2sh2 = c.mul(p.clone(), sg2_sh2.clone()); // p·(sg²+sh²)
        let p_two_sgsh = c.mul(p.clone(), two_sgsh.clone()); // p·(2·(sg·sh))
        let step2 = c.ldist(p.clone(), sg2_sh2.clone(), two_sgsh.clone());
        let mid2 = c.add(p_sg2sh2.clone(), p_two_sgsh.clone());

        // step3a : p·(sg²+sh²) = p·sg² + p·sh²   [left_distrib p sg² sh²]
        let p_sg2 = c.mul(p.clone(), sg2.clone());
        let p_sh2 = c.mul(p.clone(), sh2.clone());
        let p_sg2_p_sh2 = c.add(p_sg2.clone(), p_sh2.clone());
        let h3a = c.ldist(p.clone(), sg2.clone(), sh2.clone());
        // lift over fixed `+ p·(2·(sg·sh))`
        let step3 = c.cong_left(
            &b,
            &add_c,
            p_sg2sh2.clone(),
            p_sg2_p_sh2.clone(),
            p_two_sgsh.clone(),
            h3a,
        );
        let mid3 = c.add(p_sg2_p_sh2.clone(), p_two_sgsh.clone());

        // step4 : p·(2·(sg·sh)) = 2·(p·(sg·sh))   [pull_scalar], lift over fixed left
        let p_sgsh = c.mul(p.clone(), sgsh.clone());
        let two_p_sgsh = c.mul(two.clone(), p_sgsh.clone());
        let h4 = pull_scalar(c, &b, &p, &sgsh);
        let step4 = c.cong_right(
            &b,
            &add_c,
            p_two_sgsh.clone(),
            two_p_sgsh.clone(),
            p_sg2_p_sh2.clone(),
            h4,
        );
        let mid4 = c.add(p_sg2_p_sh2.clone(), two_p_sgsh.clone());

        // Now reshape `(p·sg² + p·sh²) + 2·(p·(sg·sh))` into the right-assoc
        // target `p·sg² + (2·(p·(sg·sh)) + p·sh²)`.
        // step5 : (p·sg² + p·sh²) + Z = p·sg² + (p·sh² + Z)   [add_assoc]
        let z = two_p_sgsh.clone(); // 2·(p·(sg·sh))
        let step5 = c.aassoc(p_sg2.clone(), p_sh2.clone(), z.clone());
        let mid5 = c.add(p_sg2.clone(), c.add(p_sh2.clone(), z.clone()));
        // step6 : p·sh² + Z = Z + p·sh²   [add_comm], lift over fixed `p·sg² + _`
        let h6 = c.acomm(p_sh2.clone(), z.clone());
        let zp_sh2 = c.add(z.clone(), p_sh2.clone());
        let step6 = c.cong_right(
            &b,
            &add_c,
            c.add(p_sh2.clone(), z.clone()),
            zp_sh2.clone(),
            p_sg2.clone(),
            h6,
        );
        let target = c.add(p_sg2.clone(), zp_sh2.clone());

        // Chain rhs → target:
        // rhs = p·E (step1) = mid2 (step2) = mid3 (step3) = mid4 (step4)
        //     = mid5 (step5) = target (step6)
        let c1 = c.trans(rhs.clone(), p_e.clone(), mid2.clone(), step1, step2);
        let c2 = c.trans(rhs.clone(), mid2.clone(), mid3.clone(), c1, step3);
        let c3 = c.trans(rhs.clone(), mid3.clone(), mid4.clone(), c2, step4);
        let c4 = c.trans(rhs.clone(), mid4.clone(), mid5.clone(), c3, step5);
        let rhs_eq_target = c.trans(rhs.clone(), mid5.clone(), target.clone(), c4, step6);

        // The lemma states `target = rhs`, so take symm.
        let proof = c.symm(rhs.clone(), target.clone(), rhs_eq_target);

        let e = b.mk_lam(sh_id, BinderInfo::Default, c.rat(), proof);
        let e = b.mk_lam(sg_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

impl Environment {
    /// Register `BoolAnalysis.hc24Assemble` — the S6 assemble ring identity
    /// `p·sg² + (2·(p·(sg·sh)) + p·sh²) = p·(sg+sh)²`. Idempotent; axiom-free.
    pub(crate) fn register_hc24_assemble(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_fourth_power()?; // Rat.add_sq_regroup

        let name = Name::from_string("BoolAnalysis.hc24Assemble");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = RingConsts::new();
        let (type_, value) = build_hc24_assemble(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc24_assemble_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_hc24_assemble().expect("register");
        env.register_hc24_assemble().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc24Assemble");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc24Assemble proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive assembly proof of
//! `Int.add_assoc : ∀ a b c : Int, Eq Int ((a + b) + c) (a + (b + c))`.
//!
//! This top-level proof performs the remaining nested case split with
//! `Int.rec` and `Nat.rec`, then dispatches each leaf to the checked
//! zero/sign branch theorems registered for #3604.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct IntAddAssocConsts {
    int_type: Expr,
    nat_type: Expr,
    nat_succ: Expr,
    int_add: Expr,
    int_of_nat: Expr,
    int_neg_succ: Expr,
    int_rec: Expr,
    nat_rec: Expr,
    eq_const: Expr,
    assoc_zero_left: Expr,
    assoc_zero_middle: Expr,
    assoc_zero_right: Expr,
    assoc_of_nat: Expr,
    assoc_ofnat_succ_ofnat_negsucc: Expr,
    assoc_ofnat_succ_negsucc_ofnat_succ: Expr,
    assoc_ofnat_succ_negsucc_negsucc: Expr,
    assoc_negsucc_ofnat_succ_ofnat_succ: Expr,
    assoc_negsucc_ofnat_succ_negsucc: Expr,
    assoc_negsucc_negsucc_negsucc: Expr,
    assoc_negsucc_negsucc_ofnat_succ: Expr,
}

impl IntAddAssocConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            int_type: Expr::const_(Name::from_string("Int"), vec![]),
            nat_type: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            int_add: Expr::const_(Name::from_string("Int.add"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_neg_succ: Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            int_rec: Expr::const_(Name::from_string("Int.rec"), vec![Level::zero()]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1]),
            assoc_zero_left: Expr::const_(Name::from_string("Int.add_assoc_zero_left"), vec![]),
            assoc_zero_middle: Expr::const_(Name::from_string("Int.add_assoc_zero_middle"), vec![]),
            assoc_zero_right: Expr::const_(Name::from_string("Int.add_assoc_zero_right"), vec![]),
            assoc_of_nat: Expr::const_(Name::from_string("Int.add_assoc_ofNat"), vec![]),
            assoc_ofnat_succ_ofnat_negsucc: Expr::const_(
                Name::from_string("Int.add_assoc_ofNat_succ_ofNat_negSucc"),
                vec![],
            ),
            assoc_ofnat_succ_negsucc_ofnat_succ: Expr::const_(
                Name::from_string("Int.add_assoc_ofNat_succ_negSucc_ofNat_succ"),
                vec![],
            ),
            assoc_ofnat_succ_negsucc_negsucc: Expr::const_(
                Name::from_string("Int.add_assoc_ofNat_succ_negSucc_negSucc"),
                vec![],
            ),
            assoc_negsucc_ofnat_succ_ofnat_succ: Expr::const_(
                Name::from_string("Int.add_assoc_negSucc_ofNat_succ_ofNat_succ"),
                vec![],
            ),
            assoc_negsucc_ofnat_succ_negsucc: Expr::const_(
                Name::from_string("Int.add_assoc_negSucc_ofNat_succ_negSucc"),
                vec![],
            ),
            assoc_negsucc_negsucc_negsucc: Expr::const_(
                Name::from_string("Int.add_assoc_negSucc_negSucc_negSucc"),
                vec![],
            ),
            assoc_negsucc_negsucc_ofnat_succ: Expr::const_(
                Name::from_string("Int.add_assoc_negSucc_negSucc_ofNat_succ"),
                vec![],
            ),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }

    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_of_nat.clone(), n)
    }

    fn neg_succ(&self, n: Expr) -> Expr {
        Expr::app(self.int_neg_succ.clone(), n)
    }

    fn add_int(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(self.int_add.clone(), lhs), rhs)
    }

    fn assoc_prop(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        let ab = self.add_int(a.clone(), b.clone());
        let bc = self.add_int(b, c.clone());
        let lhs = self.add_int(ab, c);
        let rhs = self.add_int(a, bc);
        Expr::apps(self.eq_const.clone(), [self.int_type.clone(), lhs, rhs])
    }
}

fn build_int_add_assoc_type(c: &IntAddAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let concl = c.assoc_prop(a, bv, cv);
    let ty_raw = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    let ty_raw = b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    let ty_raw = b.mk_pi(a_id, BinderInfo::Default, c.int_type.clone(), ty_raw);
    b.finish(ty_raw)
}

fn forall_bc_assoc(c: &IntAddAssocConsts, b: &mut EnvDeclBuilder, a: Expr) -> Expr {
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let concl = c.assoc_prop(a, bv, cv);
    let ty = b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl);
    b.mk_pi(b_id, BinderInfo::Default, c.int_type.clone(), ty)
}

fn forall_c_assoc(c: &IntAddAssocConsts, b: &mut EnvDeclBuilder, a: Expr, bv: Expr) -> Expr {
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let concl = c.assoc_prop(a, bv, cv);
    b.mk_pi(c_id, BinderInfo::Default, c.int_type.clone(), concl)
}

fn nat_motive_for_a(c: &IntAddAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let body = forall_bc_assoc(c, &mut mb, c.of_nat(t));
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

fn int_motive_for_b(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.int_type.clone());
    let body = forall_c_assoc(c, &mut mb, a, t);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

fn nat_motive_for_b(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let body = forall_c_assoc(c, &mut mb, a, c.of_nat(t));
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

fn int_motive_for_c(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, a: Expr, bv: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.int_type.clone());
    let body = c.assoc_prop(a, bv, t);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

fn nat_motive_for_c(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, a: Expr, bv: Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.nat_type.clone());
    let body = c.assoc_prop(a, bv, c.of_nat(t));
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat_type.clone(), body);
    mb.finish_child(lam)
}

fn int_motive_for_a(c: &IntAddAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(c.int_type.clone());
    let body = forall_bc_assoc(c, &mut mb, t);
    let lam = mb.mk_lam(t_id, BinderInfo::Default, c.int_type.clone(), body);
    mb.finish_child(lam)
}

fn zero_left_case(c: &IntAddAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (b_id, bv) = cb.fresh_local(c.int_type.clone());
    let (c_id, cv) = cb.fresh_local(c.int_type.clone());
    let proof = Expr::apps(c.assoc_zero_left.clone(), [bv, cv]);
    let lam_c = cb.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    let lam_b = cb.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), lam_c);
    cb.finish_child(lam_b)
}

fn zero_middle_case(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, a: Expr) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (c_id, cv) = cb.fresh_local(c.int_type.clone());
    let proof = Expr::apps(c.assoc_zero_middle.clone(), [a, cv]);
    let lam = cb.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), proof);
    cb.finish_child(lam)
}

fn zero_right_proof(c: &IntAddAssocConsts, a: Expr, bv: Expr) -> Expr {
    Expr::apps(c.assoc_zero_right.clone(), [a, bv])
}

fn build_c_case_pos_pos(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = cb.fresh_local(c.int_type.clone());
    let a = c.of_nat(c.succ(m.clone()));
    let bv = c.of_nat(c.succ(n.clone()));

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_c(c, &nb, a.clone(), bv.clone());
        let base = zero_right_proof(c, a.clone(), bv.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = c.assoc_prop(a.clone(), bv.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = Expr::apps(
                c.assoc_of_nat.clone(),
                [c.succ(m.clone()), c.succ(n.clone()), c.succ(p)],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let proof = Expr::apps(c.assoc_ofnat_succ_ofnat_negsucc.clone(), [m, c.succ(n), k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_c(c, &cb, a, bv);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, z]);
    let lam = cb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    cb.finish_child(lam)
}

fn build_c_case_pos_neg(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = cb.fresh_local(c.int_type.clone());
    let a = c.of_nat(c.succ(m.clone()));
    let bv = c.neg_succ(n.clone());

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_c(c, &nb, a.clone(), bv.clone());
        let base = zero_right_proof(c, a.clone(), bv.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = c.assoc_prop(a.clone(), bv.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = Expr::apps(
                c.assoc_ofnat_succ_negsucc_ofnat_succ.clone(),
                [m.clone(), n.clone(), p],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let proof = Expr::apps(c.assoc_ofnat_succ_negsucc_negsucc.clone(), [m, n, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_c(c, &cb, a, bv);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, z]);
    let lam = cb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    cb.finish_child(lam)
}

fn build_c_case_neg_pos(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = cb.fresh_local(c.int_type.clone());
    let a = c.neg_succ(m.clone());
    let bv = c.of_nat(c.succ(n.clone()));

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_c(c, &nb, a.clone(), bv.clone());
        let base = zero_right_proof(c, a.clone(), bv.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = c.assoc_prop(a.clone(), bv.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = Expr::apps(
                c.assoc_negsucc_ofnat_succ_ofnat_succ.clone(),
                [m.clone(), n.clone(), p],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let proof = Expr::apps(c.assoc_negsucc_ofnat_succ_negsucc.clone(), [m, n, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_c(c, &cb, a, bv);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, z]);
    let lam = cb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    cb.finish_child(lam)
}

fn build_c_case_neg_neg(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr, n: Expr) -> Expr {
    let mut cb = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = cb.fresh_local(c.int_type.clone());
    let a = c.neg_succ(m.clone());
    let bv = c.neg_succ(n.clone());

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_c(c, &nb, a.clone(), bv.clone());
        let base = zero_right_proof(c, a.clone(), bv.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = c.assoc_prop(a.clone(), bv.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = Expr::apps(
                c.assoc_negsucc_negsucc_ofnat_succ.clone(),
                [m.clone(), n.clone(), p],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&cb);
        let (k_id, k) = nb.fresh_local(c.nat_type.clone());
        let proof = Expr::apps(c.assoc_negsucc_negsucc_negsucc.clone(), [m, n, k]);
        let lam = nb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_c(c, &cb, a, bv);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, z]);
    let lam = cb.mk_lam(z_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    cb.finish_child(lam)
}

fn build_b_case_pos(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = bb.fresh_local(c.int_type.clone());
    let a = c.of_nat(c.succ(m.clone()));

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&bb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_b(c, &nb, a.clone());
        let base = zero_middle_case(c, &nb, a.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = forall_c_assoc(c, &mut sb, a.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = build_c_case_pos_pos(c, &sb, m.clone(), p);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&bb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let proof = build_c_case_pos_neg(c, &nb, m, n);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_b(c, &bb, a);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, y]);
    let lam = bb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    bb.finish_child(lam)
}

fn build_b_case_neg(c: &IntAddAssocConsts, parent: &EnvDeclBuilder, m: Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (y_id, y) = bb.fresh_local(c.int_type.clone());
    let a = c.neg_succ(m.clone());

    let ofnat_case = {
        let mut nb = EnvDeclBuilder::child_of(&bb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let motive = nat_motive_for_b(c, &nb, a.clone());
        let base = zero_middle_case(c, &nb, a.clone());
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&nb);
            let (p_id, p) = sb.fresh_local(c.nat_type.clone());
            let ih_ty = forall_c_assoc(c, &mut sb, a.clone(), c.of_nat(p.clone()));
            let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
            let proof = build_c_case_neg_pos(c, &sb, m.clone(), p);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let lam_p = sb.mk_lam(p_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
            sb.finish_child(lam_p)
        };
        let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n]);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
        nb.finish_child(lam)
    };

    let negsucc_case = {
        let mut nb = EnvDeclBuilder::child_of(&bb);
        let (n_id, n) = nb.fresh_local(c.nat_type.clone());
        let proof = build_c_case_neg_neg(c, &nb, m, n);
        let lam = nb.mk_lam(n_id, BinderInfo::Default, c.nat_type.clone(), proof);
        nb.finish_child(lam)
    };

    let motive = int_motive_for_b(c, &bb, a);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, y]);
    let lam = bb.mk_lam(y_id, BinderInfo::Default, c.int_type.clone(), rec_app);
    bb.finish_child(lam)
}

fn build_a_ofnat_case(c: &IntAddAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ab = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = ab.fresh_local(c.nat_type.clone());
    let motive = nat_motive_for_a(c, &ab);
    let base = zero_left_case(c, &ab);
    let step = {
        let mut sb = EnvDeclBuilder::child_of(&ab);
        let (k_id, k) = sb.fresh_local(c.nat_type.clone());
        let ih_ty = forall_bc_assoc(c, &mut sb, c.of_nat(k.clone()));
        let (ih_id, _ih) = sb.fresh_local(ih_ty.clone());
        let proof = build_b_case_pos(c, &sb, k);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat_type.clone(), lam_ih);
        sb.finish_child(lam_k)
    };
    let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, m]);
    let lam = ab.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), rec_app);
    ab.finish_child(lam)
}

fn build_a_negsucc_case(c: &IntAddAssocConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ab = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = ab.fresh_local(c.nat_type.clone());
    let proof = build_b_case_neg(c, &ab, m);
    let lam = ab.mk_lam(m_id, BinderInfo::Default, c.nat_type.clone(), proof);
    ab.finish_child(lam)
}

fn build_int_add_assoc_value(c: &IntAddAssocConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.int_type.clone());
    let (b_id, bv) = b.fresh_local(c.int_type.clone());
    let (c_id, cv) = b.fresh_local(c.int_type.clone());
    let motive = int_motive_for_a(c, &b);
    let ofnat_case = build_a_ofnat_case(c, &b);
    let negsucc_case = build_a_negsucc_case(c, &b);
    let rec_app = Expr::apps(c.int_rec.clone(), [motive, ofnat_case, negsucc_case, a]);
    let body = Expr::app(Expr::app(rec_app, bv), cv);
    let val_raw = b.mk_lam(c_id, BinderInfo::Default, c.int_type.clone(), body);
    let val_raw = b.mk_lam(b_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    let val_raw = b.mk_lam(a_id, BinderInfo::Default, c.int_type.clone(), val_raw);
    b.finish(val_raw)
}

impl Environment {
    /// Register `Int.add_assoc` as a kernel-checked theorem.
    pub(crate) fn register_int_add_assoc_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Int.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_int_arith()?;
        self.init_nat()?;
        self.init_eq()?;
        self.register_int_add_assoc_zero_left_proof()?;
        self.register_int_add_assoc_zero_middle_proof()?;
        self.register_int_add_assoc_zero_right_proof()?;
        self.register_int_add_assoc_ofnat_proof()?;
        self.register_int_add_assoc_ofnat_succ_ofnat_negsucc_proof()?;
        self.register_int_add_assoc_ofnat_succ_negsucc_ofnat_succ_proof()?;
        self.register_int_add_assoc_ofnat_succ_negsucc_negsucc_proof()?;
        self.register_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof()?;
        self.register_int_add_assoc_negsucc_ofnat_succ_negsucc_proof()?;
        self.register_int_add_assoc_negsucc_negsucc_negsucc_proof()?;
        self.register_int_add_assoc_negsucc_negsucc_ofnat_succ_proof()?;

        let c = IntAddAssocConsts::new();
        let type_ = build_int_add_assoc_type(&c);
        let value = build_int_add_assoc_value(&c);

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
    use crate::expr::ExprKind;

    #[test]
    fn test_int_add_assoc_registered_as_theorem() {
        let mut env = Environment::new();
        env.register_int_add_assoc_proof()
            .expect("first registration");
        env.register_int_add_assoc_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("Int.add_assoc"))
            .expect("Int.add_assoc should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "Theorem must retain its proof value");
    }

    #[test]
    fn test_int_add_assoc_axiom_closure_is_empty() {
        let mut env = Environment::new();
        env.init_int_arith_lemmas()
            .expect("Int arithmetic lemmas should initialize");

        let quality = env
            .proof_quality(&Name::from_string("Int.add_assoc"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "Int.add_assoc must be Constructive, got {:?}",
            quality
        );
    }

    #[test]
    fn test_int_add_assoc_proof_uses_int_rec() {
        let c = IntAddAssocConsts::new();
        let value = build_int_add_assoc_value(&c);
        let mut current = &value;
        for _ in 0..3 {
            match current.kind() {
                ExprKind::Lam(_, _, body) => current = body.as_ref(),
                k => panic!("expected outer lambda, got {:?}", k),
            }
        }
        let mut head = current;
        while let ExprKind::App(f, _) = head.kind() {
            head = f.as_ref();
        }
        match head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "Int.rec",
                "Int.add_assoc proof root must dispatch through Int.rec"
            ),
            k => panic!("expected Const(Int.rec, ..), got {:?}", k),
        }
    }
}

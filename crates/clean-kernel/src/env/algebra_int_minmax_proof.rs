// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Genuine, kernel-checked elimination of the opaque `Int.min` / `Int.max`
//! axioms and their characterizing `Int.min_def` / `Int.max_def` axioms.
//!
//! `Int.min` / `Int.max` were registered as bodyless `Declaration::Axiom`s. They
//! have a perfectly computable definition via a boolean `Int.le` decision, so we
//! give them reducible `Declaration::Definition` bodies and prove the
//! characterizing equations as `Declaration::Theorem`s.
//!
//! Foundation (new reducible Definitions):
//! - `Int.isNonNeg i := @Int.rec (fun _ => Bool) (fun _ => true) (fun _ => false) i`
//!   — `true` on `ofNat _`, `false` on `negSucc _`.
//! - `Int.ble a b := Int.isNonNeg (Int.sub b a)`.
//!
//! Reflection: `Int.ble_eq_true_of_le : Int.le a b → Int.ble a b = true`, proven
//! by `@Int.NonNeg.rec.{0}` on `h : Int.le a b ≡ Int.NonNeg (Int.sub b a)` — the
//! minor (at the `Int.NonNeg.mk n` constructor, index `ofNat n`) is `Eq.refl true`
//! because `Int.isNonNeg (ofNat n) ≡ true`.
//!
//! Definitions: `Int.min a b := Bool.rec b a (Int.ble a b)` (a if `a ≤ b` else b),
//! `Int.max a b := Bool.rec a b (Int.ble a b)` (b if `a ≤ b` else a).
//!
//! `Int.min_def : Int.le a b → Int.min a b = a` and
//! `Int.max_def : Int.le a b → Int.max a b = b` follow by transporting
//! `Eq.refl` across `Int.ble_eq_true_of_le` (which collapses the `Bool.rec`).
//!
//! All delegates (`Int.rec`, `Bool.rec`, `Int.NonNeg.rec`/`.mk`, `Eq.*`) are
//! kernel machinery or foundational, so every registered theorem is
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct MinMaxConsts {
    int: Expr,
    bool_t: Expr,
    bool_true: Expr,
    bool_false: Expr,
    nat: Expr,
    int_rec_1: Expr,
    bool_rec_1: Expr,
    nonneg_rec_0: Expr,
    #[cfg(test)]
    int_of_nat: Expr,
    int_sub: Expr,
    int_le: Expr,
    int_nonneg: Expr,
    is_nonneg: Expr,
    ble: Expr,
    ble_eq_true: Expr,
    int_min: Expr,
    int_max: Expr,
    eq_c: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
}

impl MinMaxConsts {
    fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        Self {
            int: Expr::const_(Name::from_string("Int"), vec![]),
            bool_t: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            // motive into Bool / Int : Sort 1.
            int_rec_1: Expr::const_(Name::from_string("Int.rec"), vec![t1.clone()]),
            bool_rec_1: Expr::const_(Name::from_string("Bool.rec"), vec![t1.clone()]),
            // NonNeg : Prop, eliminate into a Prop motive.
            nonneg_rec_0: Expr::const_(Name::from_string("Int.NonNeg.rec"), vec![]),
            #[cfg(test)]
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_sub: Expr::const_(Name::from_string("Int.sub"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_nonneg: Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
            is_nonneg: Expr::const_(Name::from_string("Int.isNonNeg"), vec![]),
            ble: Expr::const_(Name::from_string("Int.ble"), vec![]),
            ble_eq_true: Expr::const_(Name::from_string("Int.ble_eq_true_of_le"), vec![]),
            int_min: Expr::const_(Name::from_string("Int.min"), vec![]),
            int_max: Expr::const_(Name::from_string("Int.max"), vec![]),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![t1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![t1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1]),
        }
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_sub.clone(), [a, b])
    }
    fn ble_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.ble.clone(), [a, b])
    }
    /// `Eq <ty> x y`.
    fn eq(&self, ty: Expr, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [ty, x, y])
    }
    /// `@Bool.rec.{1} (fun _ => Int) f t scrut`.
    fn bool_rec_int(&self, f: Expr, t: Expr, scrut: Expr) -> Expr {
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(self.bool_t.clone());
            let body = self.int.clone();
            let e = b.mk_lam(x_id, BinderInfo::Default, self.bool_t.clone(), body);
            b.finish(e)
        };
        Expr::apps(self.bool_rec_1.clone(), [motive, f, t, scrut])
    }
}

impl Environment {
    /// Register `Int.isNonNeg`, `Int.ble`, `Int.ble_eq_true_of_le`, the
    /// `Int.min` / `Int.max` Definitions, and `Int.min_def` / `Int.max_def`
    /// Theorems — eliminating the opaque `Int.min` / `Int.max` / `Int.min_def` /
    /// `Int.max_def` axioms.
    pub(crate) fn register_int_minmax_proofs(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): Int-cluster content —
        // states/proves properties of the import-suppressed Clean-native Int
        // arithmetic stubs (see `init_int_arith`). Suppressed with them; the
        // genuine olean declarations import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_int_ord()?; // Int.le, Int.NonNeg(.mk/.rec), Int (with Int.rec)
        self.init_int_arith()?; // Int.sub, Int.neg, Int.add
        self.init_bool()?; // Bool, Bool.true/false, Bool.rec
        self.init_eq()?;

        let c = MinMaxConsts::new();

        // Int.isNonNeg : Int → Bool
        if self.get_const(&Name::from_string("Int.isNonNeg")).is_none() {
            let ty = Expr::pi(BinderInfo::Default, c.int.clone(), c.bool_t.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (i_id, i) = b.fresh_local(c.int.clone());
                let motive = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (x_id, _x) = ch.fresh_local(c.int.clone());
                    let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), c.bool_t.clone());
                    ch.finish_child(r)
                };
                let of_nat_case = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (n_id, _n) = ch.fresh_local(c.nat.clone());
                    let r = ch.mk_lam(
                        n_id,
                        BinderInfo::Default,
                        c.nat.clone(),
                        c.bool_true.clone(),
                    );
                    ch.finish_child(r)
                };
                let neg_succ_case = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (n_id, _n) = ch.fresh_local(c.nat.clone());
                    let r = ch.mk_lam(
                        n_id,
                        BinderInfo::Default,
                        c.nat.clone(),
                        c.bool_false.clone(),
                    );
                    ch.finish_child(r)
                };
                let body = Expr::apps(c.int_rec_1.clone(), [motive, of_nat_case, neg_succ_case, i]);
                let e = b.mk_lam(i_id, BinderInfo::Default, c.int.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.isNonNeg"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // Int.ble : Int → Int → Bool := fun a b => Int.isNonNeg (Int.sub b a)
        if self.get_const(&Name::from_string("Int.ble")).is_none() {
            let ty = Expr::pi(
                BinderInfo::Default,
                c.int.clone(),
                Expr::pi(BinderInfo::Default, c.int.clone(), c.bool_t.clone()),
            );
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(c.int.clone());
                let (bv_id, bv) = b.fresh_local(c.int.clone());
                let body = Expr::app(c.is_nonneg.clone(), c.sub(bv, a));
                let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.ble"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // Int.ble_eq_true_of_le : ∀ a b, Int.le a b → Eq Bool (Int.ble a b) Bool.true
        if self
            .get_const(&Name::from_string("Int.ble_eq_true_of_le"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(c.int.clone());
                let (bv_id, bv) = b.fresh_local(c.int.clone());
                let le_ab = Expr::apps(c.int_le.clone(), [a.clone(), bv.clone()]);
                let (h_id, _h) = b.fresh_local(le_ab.clone());
                let concl = c.eq(
                    c.bool_t.clone(),
                    c.ble_app(a.clone(), bv.clone()),
                    c.bool_true.clone(),
                );
                let e = b.mk_pi(h_id, BinderInfo::Default, le_ab, concl);
                let e = b.mk_pi(bv_id, BinderInfo::Default, c.int.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(c.int.clone());
                let (bv_id, bv) = b.fresh_local(c.int.clone());
                let le_ab = Expr::apps(c.int_le.clone(), [a.clone(), bv.clone()]);
                let (h_id, h) = b.fresh_local(le_ab.clone());
                // motive := fun (i : Int) (_ : NonNeg i) => Eq Bool (Int.isNonNeg i) true
                let motive = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (i_id, i) = ch.fresh_local(c.int.clone());
                    let nn_i = Expr::app(c.int_nonneg.clone(), i.clone());
                    let (p_id, _p) = ch.fresh_local(nn_i.clone());
                    let body = c.eq(
                        c.bool_t.clone(),
                        Expr::app(c.is_nonneg.clone(), i.clone()),
                        c.bool_true.clone(),
                    );
                    let r = ch.mk_lam(p_id, BinderInfo::Default, nn_i, body);
                    let r = ch.mk_lam(i_id, BinderInfo::Default, c.int.clone(), r);
                    ch.finish_child(r)
                };
                // minor := fun (n : Nat) => @Eq.refl Bool Bool.true
                let minor = {
                    let mut ch = EnvDeclBuilder::child_of(&b);
                    let (n_id, _n) = ch.fresh_local(c.nat.clone());
                    let refl_true =
                        Expr::apps(c.eq_refl.clone(), [c.bool_t.clone(), c.bool_true.clone()]);
                    let r = ch.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), refl_true);
                    ch.finish_child(r)
                };
                let index = c.sub(bv.clone(), a.clone()); // Int.sub b a
                let body = Expr::apps(c.nonneg_rec_0.clone(), [motive, minor, index, h]);
                let e = b.mk_lam(h_id, BinderInfo::Default, le_ab, body);
                let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Int.ble_eq_true_of_le"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        let int_min_max_type = Expr::pi(
            BinderInfo::Default,
            c.int.clone(),
            Expr::pi(BinderInfo::Default, c.int.clone(), c.int.clone()),
        );

        // Int.min a b := Bool.rec b a (Int.ble a b)   (a if a ≤ b, else b)
        if self.get_const(&Name::from_string("Int.min")).is_none() {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(c.int.clone());
                let (bv_id, bv) = b.fresh_local(c.int.clone());
                let body = c.bool_rec_int(bv.clone(), a.clone(), c.ble_app(a.clone(), bv.clone()));
                let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.min"),
                level_params: vec![],
                type_: int_min_max_type.clone(),
                value,
                is_reducible: true,
            })?;
        }

        // Int.max a b := Bool.rec a b (Int.ble a b)   (b if a ≤ b, else a)
        if self.get_const(&Name::from_string("Int.max")).is_none() {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (a_id, a) = b.fresh_local(c.int.clone());
                let (bv_id, bv) = b.fresh_local(c.int.clone());
                let body = c.bool_rec_int(a.clone(), bv.clone(), c.ble_app(a.clone(), bv.clone()));
                let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), body);
                let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.max"),
                level_params: vec![],
                type_: int_min_max_type,
                value,
                is_reducible: true,
            })?;
        }

        // Int.min_def : ∀ a b, Int.le a b → Eq Int (Int.min a b) a
        self.register_minmax_def(&c, "Int.min_def", true)?;
        // Int.max_def : ∀ a b, Int.le a b → Eq Int (Int.max a b) b
        self.register_minmax_def(&c, "Int.max_def", false)?;

        Ok(())
    }

    /// Shared builder for `Int.min_def` (`is_min = true`, conclusion `min a b = a`)
    /// and `Int.max_def` (`is_min = false`, conclusion `max a b = b`).
    fn register_minmax_def(
        &mut self,
        c: &MinMaxConsts,
        name: &str,
        is_min: bool,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let target = if is_min { &c.int_min } else { &c.int_max };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let le_ab = Expr::apps(c.int_le.clone(), [a.clone(), bv.clone()]);
            let (h_id, _h) = b.fresh_local(le_ab.clone());
            let lhs = Expr::apps(target.clone(), [a.clone(), bv.clone()]);
            let rhs = if is_min { a.clone() } else { bv.clone() };
            let concl = c.eq(c.int.clone(), lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, le_ab, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.int.clone());
            let (bv_id, bv) = b.fresh_local(c.int.clone());
            let le_ab = Expr::apps(c.int_le.clone(), [a.clone(), bv.clone()]);
            let (h_id, h) = b.fresh_local(le_ab.clone());

            // For min: Bool.rec b a x ; rhs a.  For max: Bool.rec a b x ; rhs b.
            let (f_case, t_case, rhs) = if is_min {
                (bv.clone(), a.clone(), a.clone())
            } else {
                (a.clone(), bv.clone(), bv.clone())
            };

            // motive := fun (x : Bool) => Eq Int (Bool.rec f_case t_case x) rhs
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.bool_t.clone());
                let lhs = c.bool_rec_int(f_case.clone(), t_case.clone(), x);
                let body = c.eq(c.int.clone(), lhs, rhs.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                ch.finish_child(r)
            };
            // h_true : Int.ble a b = true
            let h_true = Expr::apps(c.ble_eq_true.clone(), [a.clone(), bv.clone(), h]);
            // symm : true = Int.ble a b
            let h_symm = Expr::apps(
                c.eq_symm.clone(),
                [
                    c.bool_t.clone(),
                    c.ble_app(a.clone(), bv.clone()),
                    c.bool_true.clone(),
                    h_true,
                ],
            );
            // motive true = Eq Int (Bool.rec f_case t_case true) rhs ≡ Eq Int t_case rhs.
            // For min: t_case=a, rhs=a -> Eq.refl a. For max: t_case=b, rhs=b -> Eq.refl b.
            let refl = Expr::apps(c.eq_refl.clone(), [c.int.clone(), rhs.clone()]);
            // @Eq.subst.{1} Bool motive true (ble a b) h_symm refl : motive (ble a b)
            let body = Expr::apps(
                c.eq_subst.clone(),
                [
                    c.bool_t.clone(),
                    motive,
                    c.bool_true.clone(),
                    c.ble_app(a.clone(), bv.clone()),
                    h_symm,
                    refl,
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, le_ab, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.int.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.int.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_int_minmax_proofs()
            .expect("register_int_minmax_proofs");
        env
    }

    #[test]
    fn test_int_min_max_are_reducible_definitions() {
        let env = env();
        for name in ["Int.min", "Int.max", "Int.isNonNeg", "Int.ble"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a reducible Definition, got {:?}",
                info.kind
            );
            assert!(info.value.is_some(), "{name} must have a body");
        }
    }

    #[test]
    fn test_int_minmax_def_theorems_constructive() {
        let env = env();
        for name in ["Int.ble_eq_true_of_le", "Int.min_def", "Int.max_def"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, got {:?}",
                info.kind
            );
            let q = env
                .proof_quality(&Name::from_string(name))
                .expect("proof_quality");
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} must be Constructive, got {q:?}"
            );
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.register_int_minmax_proofs().expect("first");
        env.register_int_minmax_proofs().expect("second idempotent");
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `String.decEq : (a b : String) → Decidable (Eq a b)` — a real
//! kernel term (NO `sorry`, NO axiom) that RETIRES the former foundational
//! `String.decEq` representation axiom over the FAITHFUL `String` carrier
//! (`String.mk : List Char → String`, projection `String.data`, recursor
//! `String.rec`; see `init_string`).
//!
//! A `String` is a single-field structure wrapping a `List Char`, so equality on
//! `String` is decided by equality on the underlying `List Char`, dispatched
//! through the (axiom-free, recursive) `ListChar.decEq` (L1).
//!
//! # Proof shape
//!
//! Rather than rely on structure-eta to relate `String.mk a.data` to `a` (which
//! does not fire for *symbolic* `a`, since both `String.data a` and the eta
//! projection are stuck on an fvar), we destructure `a` and `b` with
//! `String.rec`, so both are *literally* `String.mk da` / `String.mk db` in the
//! leaf — the exact treatment `algebra_uint_dec_eq_proof.rs` gives the `Nat`
//! wrappers. Then:
//!
//! ```text
//! String.decEq : (a b : String) → Decidable (Eq a b) :=
//!   fun (a b : String) =>
//!     @String.rec.{1} (fun (_a : String) => Decidable (Eq String _a b))
//!       (fun (da : List Char) =>                          -- a ≡ String.mk da
//!          @String.rec.{1} (fun (_b : String) => Decidable (Eq String (String.mk da) _b))
//!            (fun (db : List Char) =>                      -- b ≡ String.mk db
//!               @Decidable.rec.{1} (Eq (List Char) da db)
//!                 (fun _ => Decidable (Eq String (String.mk da) (String.mk db)))
//!                 (fun (hne : Eq (List Char) da db → False) =>             -- isFalse
//!                    @Decidable.isFalse (Eq String (String.mk da) (String.mk db))
//!                      (fun (h : Eq String (String.mk da) (String.mk db)) =>
//!                         hne (@congrArg String (List Char) (String.mk da) (String.mk db)
//!                                String.data h)))
//!                 (fun (heq : Eq (List Char) da db) =>                     -- isTrue
//!                    @Decidable.isTrue (Eq String (String.mk da) (String.mk db))
//!                      (@congrArg (List Char) String da db String.mk heq))
//!                 (ListChar.decEq da db))
//!            b)
//!       a
//! ```
//!
//! - **isTrue**: `congrArg String.mk heq : Eq String (String.mk da) (String.mk db)`
//!   — *syntactically* the goal, no eta needed.
//! - **isFalse**: from `h : String.mk da = String.mk db` derive
//!   `congrArg String.data h : Eq (List Char) (String.data (String.mk da))
//!   (String.data (String.mk db))`; `String.data (String.mk d) ≡ d` (ι), so this
//!   is `Eq (List Char) da db` by def-eq, refuted by `hne`.
//!
//! # Axiom closure
//!
//! The term mentions only `Eq`, `String`, `String.mk`, `String.data`,
//! `String.rec`, `List`/`Char`, `ListChar.decEq`,
//! `Decidable`(`.rec`/`.isTrue`/`.isFalse`), `congrArg`, `False` — all
//! constructive (generated recursors / reducible definitions / the axiom-free
//! `ListChar.decEq`). So `env.axiom_deps("String.decEq")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the constructive `String.decEq` as a kernel-checked
    /// `Declaration::Definition` (retiring the representation axiom).
    ///
    /// # Contract
    ///
    /// REQUIRES: `String` (faithful carrier) + `String.mk`/`String.data`/
    ///           `String.rec`, `List`/`Char`, `ListChar.decEq`, `Eq`, `congrArg`,
    ///           `Decidable`(+ctors/rec), `False` (auto-initialized here).
    /// ENSURES: On success, `String.decEq` is a `Definition` whose value
    ///          type-checks at `(a b : String) → Decidable (Eq a b)` and whose
    ///          axiom closure is empty.
    /// ENSURES: Idempotent (returns early if `String.decEq` is already a
    ///          `Definition`).
    pub(crate) fn register_string_dec_eq_proof(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // String-cluster content over the import-suppressed v4.8 String/Char
        // shapes (see init_string). Suppressed with them.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self
            .get_const(&Name::from_string("String.decEq"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Definition)
        {
            return Ok(());
        }

        // Dependencies.
        self.init_eq()?;
        self.init_string()?; // faithful carrier + String.mk/String.data/String.rec
        self.init_true_false()?;
        self.init_decidable()?;
        self.register_list_char_dec_eq_proof()?; // L1 discriminant

        // ----- shared constants -----
        let type0 = Level::zero();
        let type1 = Level::succ(Level::zero());

        let char_c = Expr::const_(Name::from_string("Char"), vec![]);
        let list_char = Expr::app(
            Expr::const_(Name::from_string("List"), vec![type0.clone()]),
            char_c,
        );
        let string_c = Expr::const_(Name::from_string("String"), vec![]);
        let string_mk = Expr::const_(Name::from_string("String.mk"), vec![]);
        let string_data = Expr::const_(Name::from_string("String.data"), vec![]);
        // String.rec.{1}: eliminating the single-ctor structure into Sort 1
        // (the leaf produces a `Decidable … : Type 0 = Sort 1`).
        let string_rec = Expr::const_(Name::from_string("String.rec"), vec![type1.clone()]);

        let list_char_dec_eq = Expr::const_(Name::from_string("ListChar.decEq"), vec![]);

        // Eq.{1} on String and on List Char (both : Type 0 = Sort 1).
        let eq_str = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);
        let eq_lc = Expr::const_(Name::from_string("Eq"), vec![type1.clone()]);

        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![type1.clone()]);
        let congr_arg = Expr::const_(
            Name::from_string("congrArg"),
            vec![type1.clone(), type1.clone()],
        );
        let false_c = Expr::const_(Name::from_string("False"), vec![]);

        // ----- helper closures -----
        let mk = |d: Expr| Expr::app(string_mk.clone(), d);
        let eq_s = |l: Expr, r: Expr| Expr::apps(eq_str.clone(), [string_c.clone(), l, r]);
        let eq_l = |l: Expr, r: Expr| Expr::apps(eq_lc.clone(), [list_char.clone(), l, r]);
        let dec_eq_s = |l: Expr, r: Expr| Expr::app(dec.clone(), eq_s(l, r));

        // ----- Type: (a b : String) → Decidable (Eq a b) -----
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(string_c.clone());
            let (bv_id, bv) = b.fresh_local(string_c.clone());
            let concl = dec_eq_s(a.clone(), bv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, string_c.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, string_c.clone(), e);
            b.finish(e)
        };

        // ----- value -----
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(string_c.clone());
            let (bv_id, bv) = b.fresh_local(string_c.clone());

            // outer motive: fun (_a : String) => Decidable (Eq String _a b)
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ap_id, ap) = c.fresh_local(string_c.clone());
                c.finish_child(c.mk_lam(
                    ap_id,
                    BinderInfo::Default,
                    string_c.clone(),
                    dec_eq_s(ap, bv.clone()),
                ))
            };

            // a-minor: fun (da : List Char) => @String.rec.{1} <motive_b> <b-minor> b
            let a_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (da_id, da) = c.fresh_local(list_char.clone());
                let mk_da = mk(da.clone());

                // inner motive: fun (_b : String) => Decidable (Eq String (String.mk da) _b)
                let motive_b = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (bp_id, bp) = d.fresh_local(string_c.clone());
                    d.finish_child(d.mk_lam(
                        bp_id,
                        BinderInfo::Default,
                        string_c.clone(),
                        dec_eq_s(mk_da.clone(), bp),
                    ))
                };

                // b-minor: fun (db : List Char) => @Decidable.rec … (ListChar.decEq da db)
                let b_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (db_id, db) = d.fresh_local(list_char.clone());
                    let mk_db = mk(db.clone());

                    let p_lc = eq_l(da.clone(), db.clone()); // Eq (List Char) da db
                    let concl = dec_eq_s(mk_da.clone(), mk_db.clone());

                    // dec.rec motive: fun (_ : Decidable (Eq (List Char) da db)) => concl
                    let dmotive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (dsc_id, _dsc) = e.fresh_local(Expr::app(dec.clone(), p_lc.clone()));
                        e.finish_child(e.mk_lam(
                            dsc_id,
                            BinderInfo::Default,
                            Expr::app(dec.clone(), p_lc.clone()),
                            concl.clone(),
                        ))
                    };

                    // isFalse minor: fun (hne : Eq (List Char) da db → False) =>
                    //   @Decidable.isFalse concl
                    //     (fun (h : Eq String (mk da)(mk db)) =>
                    //        hne (@congrArg String (List Char) (mk da)(mk db) String.data h))
                    let is_false_min = {
                        let not_p = Expr::pi(BinderInfo::Default, p_lc.clone(), false_c.clone());
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hne_id, hne) = e.fresh_local(not_p.clone());
                        let eq_mk = eq_s(mk_da.clone(), mk_db.clone());
                        let disproof = {
                            let mut g = EnvDeclBuilder::child_of(&e);
                            let (h_id, h) = g.fresh_local(eq_mk.clone());
                            // congrArg String.data h
                            //   : Eq (List Char) (String.data (mk da)) (String.data (mk db))
                            //   ≡ Eq (List Char) da db  (ι on String.data (String.mk _))
                            let cong = Expr::apps(
                                congr_arg.clone(),
                                [
                                    string_c.clone(),
                                    list_char.clone(),
                                    mk_da.clone(),
                                    mk_db.clone(),
                                    string_data.clone(),
                                    h,
                                ],
                            );
                            let body = Expr::app(hne.clone(), cong);
                            g.finish_child(g.mk_lam(h_id, BinderInfo::Default, eq_mk.clone(), body))
                        };
                        let body = Expr::apps(is_false.clone(), [eq_mk, disproof]);
                        e.finish_child(e.mk_lam(hne_id, BinderInfo::Default, not_p, body))
                    };

                    // isTrue minor: fun (heq : Eq (List Char) da db) =>
                    //   @Decidable.isTrue concl
                    //     (@congrArg (List Char) String da db String.mk heq)
                    let is_true_min = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (heq_id, heq) = e.fresh_local(p_lc.clone());
                        let lifted = Expr::apps(
                            congr_arg.clone(),
                            [
                                list_char.clone(),
                                string_c.clone(),
                                da.clone(),
                                db.clone(),
                                string_mk.clone(),
                                heq,
                            ],
                        );
                        let body = Expr::apps(
                            is_true.clone(),
                            [eq_s(mk_da.clone(), mk_db.clone()), lifted],
                        );
                        e.finish_child(e.mk_lam(heq_id, BinderInfo::Default, p_lc.clone(), body))
                    };

                    let discriminant =
                        Expr::apps(list_char_dec_eq.clone(), [da.clone(), db.clone()]);
                    let rec_app = Expr::apps(
                        dec_rec.clone(),
                        [p_lc, dmotive, is_false_min, is_true_min, discriminant],
                    );
                    d.finish_child(d.mk_lam(db_id, BinderInfo::Default, list_char.clone(), rec_app))
                };

                let inner_rec = Expr::apps(string_rec.clone(), [motive_b, b_minor, bv.clone()]);
                c.finish_child(c.mk_lam(da_id, BinderInfo::Default, list_char.clone(), inner_rec))
            };

            let outer_rec = Expr::apps(string_rec.clone(), [motive_a, a_minor, a.clone()]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, string_c.clone(), outer_rec);
            let e = b.mk_lam(a_id, BinderInfo::Default, string_c.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.decEq"),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    /// `String.decEq` registers as a constructive `Definition` (NOT an `Axiom`),
    /// idempotently, and its declared type type-checks via `infer_type`.
    #[test]
    fn test_string_dec_eq_registered_and_type_checks() {
        let mut env = Environment::with_prelude();
        env.register_string_dec_eq_proof()
            .expect("first registration");
        env.register_string_dec_eq_proof()
            .expect("idempotent re-registration");

        let info = env
            .get_const(&Name::from_string("String.decEq"))
            .expect("String.decEq should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "String.decEq must be a computable Definition, not an Axiom"
        );
        assert!(info.value.is_some(), "Definition must retain its value");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("String.decEq"), vec![]))
            .expect("String.decEq should type-check");
    }

    /// Axiom closure is empty — the no-fake / no-axiom guard. (If the former
    /// representation axiom were still in the closure, it would appear here.)
    #[test]
    fn test_string_dec_eq_axiom_closure_empty() {
        let mut env = Environment::with_prelude();
        env.register_string_dec_eq_proof().unwrap();
        let deps = env
            .axiom_deps(&Name::from_string("String.decEq"))
            .expect("String.decEq is registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "String.decEq must have empty axiom closure, got {names:?}"
        );
    }

    /// The body genuinely destructures via `String.rec` and dispatches via
    /// `Decidable.rec` + `ListChar.decEq`, lifting via `congrArg` — guards
    /// against a degenerate / `sorry`-laden masquerade.
    #[test]
    fn test_string_dec_eq_uses_real_dispatch() {
        let mut env = Environment::with_prelude();
        env.register_string_dec_eq_proof().unwrap();
        let info = env.get_const(&Name::from_string("String.decEq")).unwrap();
        let value = info.value.as_ref().expect("Definition has value");

        fn mentions(e: &Expr, target: &str) -> bool {
            fn go(e: &Expr, target: &str, hit: &mut bool) {
                if *hit {
                    return;
                }
                match e.kind() {
                    ExprKind::Const(n, _) if n.to_string() == target => *hit = true,
                    ExprKind::App(f, a) => {
                        go(f, target, hit);
                        go(a, target, hit);
                    }
                    ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                        go(t, target, hit);
                        go(b, target, hit);
                    }
                    ExprKind::Let(_, t, v, b, _) => {
                        go(t, target, hit);
                        go(v, target, hit);
                        go(b, target, hit);
                    }
                    _ => {}
                }
            }
            let mut hit = false;
            go(e, target, &mut hit);
            hit
        }

        assert!(
            mentions(value, "String.rec"),
            "must destructure via String.rec"
        );
        assert!(
            mentions(value, "Decidable.rec"),
            "must dispatch via Decidable.rec"
        );
        assert!(
            mentions(value, "ListChar.decEq"),
            "must dispatch via ListChar.decEq"
        );
        assert!(mentions(value, "congrArg"), "must lift via congrArg");
        assert!(!mentions(value, "sorryAx"), "must not contain sorryAx");
    }
}

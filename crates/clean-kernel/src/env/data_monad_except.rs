// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w)`
//! with `throw` / `tryCatch` as its projections, and its instances for
//! `Except ε`, `ExceptT ε m` and `StateT σ m` (2026-09-28, prelude soundness
//! fix). `MonadExcept.throw` was an instance-less AXIOM `ε → m α` until then,
//! and proved `False` at `m := fun _ => Empty`
//! (`docs/issues/2026-09-28-prelude-pure-proves-false.md`).
//!
//! The instances are Clean-native FLATTENINGS of Lean's `MonadExceptOf` bridge
//! (`instMonadExceptOfMonadExceptOf`): Clean's prelude has no `MonadExceptOf`,
//! so each instance answers `MonadExcept ε M` directly, with the bodies Lean's
//! instances reduce to. Nothing here is an axiom.

use crate::env::data_monad_transformers::{open_monad, open_param_monad};
use crate::env::monad_term::{cst, lparam, type_at, Tele};
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w)`
    /// with `throw` / `tryCatch` projections, and the two flattened instances
    /// (module doc).
    pub(crate) fn init_monad_except_class(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        self.init_out_param()?;
        let (u, v, w) = (lparam("u"), lparam("v"), lparam("w"));
        let uvw = [u.clone(), v.clone(), w.clone()];
        let lps = ["u", "v", "w"];
        // Spelled as Lean's `.olean` serializes the class, so the import meets
        // a type-EQUAL name: `ε`'s binder is wrapped in `outParam` (the marker
        // the elaborator's out-param logic reads) and the sort is the
        // normalized `Sort (max (u+1) (v+2) (w+1))` Lean infers.
        let class_sort = Expr::sort(Level::max(
            Level::max(Level::succ(u.clone()), Level::succ(Level::succ(v.clone()))),
            Level::succ(w.clone()),
        ));
        let eps_ty = Expr::app(
            cst("outParam", &[Level::succ(Level::succ(u.clone()))]),
            type_at(&u),
        );
        let throw_ty = |t: &Tele, e: &Expr, m: &Expr| {
            let mut t2 = Tele::child(t);
            let a = t2.imp(type_at(&v));
            t2.pi(Expr::arrow(e.clone(), Expr::app(m.clone(), a)))
        };
        let try_catch_ty = |t: &Tele, e: &Expr, m: &Expr| {
            let mut t2 = Tele::child(t);
            let a = t2.imp(type_at(&v));
            let ma = Expr::app(m.clone(), a);
            t2.pi(Expr::arrow(
                ma.clone(),
                Expr::arrow(Expr::arrow(e.clone(), ma.clone()), ma),
            ))
        };
        let ctor_type = {
            let mut t = Tele::new();
            let e = t.imp(eps_ty.clone());
            let m = t.imp(Expr::arrow(type_at(&v), type_at(&w)));
            let th = throw_ty(&t, &e, &m);
            let tc = try_catch_ty(&t, &e, &m);
            let _ = t.arg(th);
            let _ = t.arg(tc);
            t.pi(Expr::apps(cst("MonadExcept", &uvw), [e, m]))
        };
        self.add_inductive(InductiveDecl {
            level_params: lps.iter().map(|p| Name::from_string(p)).collect(),
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("MonadExcept"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    eps_ty.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::arrow(type_at(&v), type_at(&w)),
                        class_sort,
                    ),
                ),
                constructors: vec![Constructor {
                    name: Name::from_string("MonadExcept.mk"),
                    type_: ctor_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("MonadExcept"),
            vec![Name::from_string("throw"), Name::from_string("tryCatch")],
        )?;
        self.register_class(KernelClassInfo {
            name: Name::from_string("MonadExcept"),
            num_params: 2,
            out_params: vec![0],
            semi_out_params: vec![],
        });
        for (proj, idx) in [("MonadExcept.throw", 0u32), ("MonadExcept.tryCatch", 1u32)] {
            self.add_tele_def(proj, &lps, true, |t| {
                let e = t.imp(eps_ty.clone());
                let m = t.imp(Expr::arrow(type_at(&v), type_at(&w)));
                let s = t.inst(Expr::apps(cst("MonadExcept", &uvw), [e.clone(), m.clone()]));
                let ty = if idx == 0 {
                    throw_ty(t, &e, &m)
                } else {
                    try_catch_ty(t, &e, &m)
                };
                (ty, Expr::proj(Name::from_string("MonadExcept"), idx, s))
            })?;
        }

        self.add_monad_except_instances()
    }

    fn add_monad_except_instances(&mut self) -> Result<(), EnvError> {
        let (u, v) = (lparam("u"), lparam("v"));
        // `Except.{u, a_lvl}`: the error universe is always `u`; the value
        // universe is the second level (Lean 4.8.0's two-universe `Except`).
        let except = |a_lvl: &Level, e: &Expr, a: &Expr| {
            Expr::apps(
                cst("Except", &[u.clone(), a_lvl.clone()]),
                [e.clone(), a.clone()],
            )
        };
        let ok = |a_lvl: &Level, e: &Expr, a: &Expr, x: Expr| {
            Expr::apps(
                cst("Except.ok", &[u.clone(), a_lvl.clone()]),
                [e.clone(), a.clone(), x],
            )
        };
        let error = |a_lvl: &Level, e: &Expr, a: &Expr, x: Expr| {
            Expr::apps(
                cst("Except.error", &[u.clone(), a_lvl.clone()]),
                [e.clone(), a.clone(), x],
            )
        };
        // `Except.casesOn r (motive := fun _ => res) on_error on_ok` over
        // `Except.{u, a_lvl} ε α`.
        let cases = |t: &Tele,
                     a_lvl: &Level,
                     e: &Expr,
                     a: &Expr,
                     res: Expr,
                     motive_lvl: Level,
                     r: Expr,
                     on_error: &dyn Fn(Expr) -> Expr,
                     on_ok: &dyn Fn(Expr) -> Expr| {
            let motive = {
                let mut t2 = Tele::child(t);
                let _ = t2.arg(except(a_lvl, e, a));
                t2.lam(res)
            };
            let err_minor = {
                let mut t2 = Tele::child(t);
                let x = t2.arg(e.clone());
                t2.lam(on_error(x))
            };
            let ok_minor = {
                let mut t2 = Tele::child(t);
                let x = t2.arg(a.clone());
                t2.lam(on_ok(x))
            };
            Expr::apps(
                cst("Except.casesOn", &[motive_lvl, u.clone(), a_lvl.clone()]),
                [e.clone(), a.clone(), motive, r, err_minor, ok_minor],
            )
        };

        // instMonadExceptExcept.{u, v} {ε : Type u}
        //   : MonadExcept.{u, v, max u v} ε (Except.{u, v} ε)
        {
            let mut t = Tele::new();
            let e = t.imp(type_at(&u));
            let carrier = Expr::app(cst("Except", &[u.clone(), v.clone()]), e.clone());
            let uv_max = Level::max(u.clone(), v.clone());
            let lv = [u.clone(), v.clone(), uv_max.clone()];
            let throw = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&v));
                let x = t2.arg(e.clone());
                t2.lam(error(&v, &e, &a, x))
            };
            let try_catch = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&v));
                let ma = t2.arg(except(&v, &e, &a));
                let h = t2.arg(Expr::arrow(e.clone(), except(&v, &e, &a)));
                let body = cases(
                    &t2,
                    &v,
                    &e,
                    &a,
                    except(&v, &e, &a),
                    Level::succ(uv_max.clone()),
                    ma,
                    &|x| Expr::app(h.clone(), x),
                    &|x| ok(&v, &e, &a, x),
                );
                t2.lam(body)
            };
            let ty = Expr::apps(cst("MonadExcept", &lv), [e.clone(), carrier.clone()]);
            let val = Expr::apps(
                cst("MonadExcept.mk", &lv),
                [e.clone(), carrier, throw, try_catch],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instMonadExceptExcept"),
                level_params: vec![Name::from_string("u"), Name::from_string("v")],
                type_: t.pi(ty),
                value: t.lam(val),
                is_reducible: true,
            })?;
        }

        // instMonadExceptExceptT {ε m} [Monad m] : MonadExcept ε (ExceptT ε m)
        {
            let uv = [u.clone(), v.clone()];
            let lv = [u.clone(), u.clone(), v.clone()];
            let mut t = Tele::new();
            let (e, m, mi) = open_param_monad(&mut t, &u, &v);
            let carrier = Expr::apps(cst("ExceptT", &uv), [e.clone(), m.clone()]);
            let mk = |a: &Expr, x: Expr| {
                Expr::apps(cst("ExceptT.mk", &uv), [e.clone(), m.clone(), a.clone(), x])
            };
            let run = |a: &Expr, x: Expr| {
                Expr::apps(
                    cst("ExceptT.run", &uv),
                    [e.clone(), m.clone(), a.clone(), x],
                )
            };
            let throw = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&u));
                let x = t2.arg(e.clone());
                t2.lam(mk(&a, mi.pure(except(&u, &e, &a), error(&u, &e, &a, x))))
            };
            let try_catch = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&u));
                let eta = Expr::apps(cst("ExceptT", &uv), [e.clone(), m.clone(), a.clone()]);
                let ma = t2.arg(eta.clone());
                let h = t2.arg(Expr::arrow(e.clone(), eta));
                let k = {
                    let mut t3 = Tele::child(&t2);
                    let r = t3.arg(except(&u, &e, &a));
                    let body = cases(
                        &t3,
                        &u,
                        &e,
                        &a,
                        Expr::app(m.clone(), except(&u, &e, &a)),
                        Level::succ(v.clone()),
                        r,
                        &|x| run(&a, Expr::app(h.clone(), x)),
                        &|x| mi.pure(except(&u, &e, &a), ok(&u, &e, &a, x)),
                    );
                    t3.lam(body)
                };
                t2.lam(mk(
                    &a,
                    mi.bind(except(&u, &e, &a), except(&u, &e, &a), run(&a, ma), k),
                ))
            };
            let ty = Expr::apps(cst("MonadExcept", &lv), [e.clone(), carrier.clone()]);
            let val = Expr::apps(
                cst("MonadExcept.mk", &lv),
                [e.clone(), carrier, throw, try_catch],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instMonadExceptExceptT"),
                level_params: vec![Name::from_string("u"), Name::from_string("v")],
                type_: t.pi(ty),
                value: t.lam(val),
                is_reducible: true,
            })?;
        }

        // instMonadExceptStateT {ε σ m} [Monad m] [MonadExcept ε m]
        //   : MonadExcept ε (StateT σ m)
        //   throw    := fun x s => bind (throw x) (fun a => pure (a, s))   (StateT.lift ∘ throw)
        //   tryCatch := fun x h s => tryCatch (x s) (fun e => h e s)
        // — the flattening of Lean's `StateT` `MonadExceptOf` lift
        // (`Init/Control/State.lean`), so `throw` / `try … catch` work in a
        // `StateT σ (Except ε)` do block (trust-ir's `Sem` shape).
        {
            self.init_state_t()?;
            let e_l = lparam("e");
            let uv = [u.clone(), v.clone()];
            let uu = [u.clone(), u.clone()];
            let umv = Level::max(u.clone(), v.clone());
            let inner_lv = [e_l.clone(), u.clone(), v.clone()];
            let outer_lv = [e_l.clone(), u.clone(), umv];
            let mut t = Tele::new();
            let e = t.imp(type_at(&e_l));
            let s = t.imp(type_at(&u));
            let (m, mi) = open_monad(&mut t, &u, &v);
            let inner = t.inst(Expr::apps(
                cst("MonadExcept", &inner_lv),
                [e.clone(), m.clone()],
            ));
            let carrier = Expr::apps(cst("StateT", &uv), [s.clone(), m.clone()]);
            let prod = |a: &Expr| Expr::apps(cst("Prod", &uu), [a.clone(), s.clone()]);
            let state_t = |a: &Expr| Expr::app(carrier.clone(), a.clone());
            let throw = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&u));
                let x = t2.arg(e.clone());
                let st = t2.arg(s.clone());
                let thrown = Expr::apps(
                    cst("MonadExcept.throw", &inner_lv),
                    [e.clone(), m.clone(), inner.clone(), a.clone(), x],
                );
                let k = {
                    let mut t3 = Tele::child(&t2);
                    let y = t3.arg(a.clone());
                    t3.lam(mi.pure(
                        prod(&a),
                        Expr::apps(cst("Prod.mk", &uu), [a.clone(), s.clone(), y, st]),
                    ))
                };
                t2.lam(mi.bind(a.clone(), prod(&a), thrown, k))
            };
            let try_catch = {
                let mut t2 = Tele::child(&t);
                let a = t2.imp(type_at(&u));
                let x = t2.arg(state_t(&a));
                let h = t2.arg(Expr::arrow(e.clone(), state_t(&a)));
                let st = t2.arg(s.clone());
                let handler = {
                    let mut t3 = Tele::child(&t2);
                    let err = t3.arg(e.clone());
                    t3.lam(Expr::apps(h, [err, st.clone()]))
                };
                t2.lam(Expr::apps(
                    cst("MonadExcept.tryCatch", &inner_lv),
                    [
                        e.clone(),
                        m.clone(),
                        inner.clone(),
                        prod(&a),
                        Expr::app(x, st),
                        handler,
                    ],
                ))
            };
            let ty = Expr::apps(cst("MonadExcept", &outer_lv), [e.clone(), carrier.clone()]);
            let val = Expr::apps(
                cst("MonadExcept.mk", &outer_lv),
                [e, carrier, throw, try_catch],
            );
            self.add_decl(Declaration::Definition {
                name: Name::from_string("instMonadExceptStateT"),
                level_params: vec![
                    Name::from_string("e"),
                    Name::from_string("u"),
                    Name::from_string("v"),
                ],
                type_: t.pi(ty),
                value: t.lam(val),
                is_reducible: true,
            })?;
        }

        for name in [
            "instMonadExceptExcept",
            "instMonadExceptExceptT",
            "instMonadExceptStateT",
        ] {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(name),
                class_name: Name::from_string("MonadExcept"),
                priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }
        Ok(())
    }
}

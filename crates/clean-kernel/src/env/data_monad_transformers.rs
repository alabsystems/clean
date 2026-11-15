// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `StateT` / `ExceptT` / `OptionT` operations and their `Monad` instances
//! (2026-09-28, prelude soundness fix).
//!
//! These replace instance-less axioms that proved `False`: `StateT.pure`,
//! `StateT.get`, `StateT.set`, `StateT.modify`, `StateT.modifyGet` (each
//! `{σ} → {m} → … → StateT σ m _`, and `StateT σ m α` unfolds to
//! `σ → m (α × σ)`, so each produced an `m _` for ANY `m`), `MonadExcept.throw`
//! (`ε → m α` for any `m`), and the `OptionT.fail` / `OptionT.run` pair over an
//! opaque `OptionT`. Every operation now takes `[Monad m]` exactly as Lean's
//! does (`Init/Control/State.lean`, `Except.lean`, `Option.lean`; signatures
//! read off pinned v4.30.0-rc2 with `#check`), `ExceptT` / `OptionT` are
//! Lean's definitions (`m (Except ε α)`, `m (Option α)`) with identity
//! `mk` / `run`. `MonadExcept` — Lean's class, with `throw` / `tryCatch` as
//! its projections — and its instances live in `data_monad_except.rs`.
//!
//! Nothing here is an axiom.

use crate::env::data_monad_classes::monad_inst;
use crate::env::monad_term::{cst, lparam, monad_kind, type_at, MonadInst, Tele};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// The `{σ/ε : Type u} {m : Type u → Type v} [inst : Monad m]` prefix most of
/// these share; returns `(first, m, MonadInst)`.
pub(super) fn open_param_monad(t: &mut Tele, u: &Level, v: &Level) -> (Expr, Expr, MonadInst) {
    let first = t.imp(type_at(u));
    let (m, mi) = open_monad(t, u, v);
    (first, m, mi)
}

/// `{m : Type u → Type v} [inst : Monad m]`.
pub(super) fn open_monad(t: &mut Tele, u: &Level, v: &Level) -> (Expr, MonadInst) {
    let m = t.imp(monad_kind(u, v));
    let inst = t.inst(Expr::app(cst("Monad", &[u.clone(), v.clone()]), m.clone()));
    let mi = monad_inst(u, v, &m, &inst);
    (m, mi)
}

impl Environment {
    /// Register `name : Π <tele>, ty := λ <tele>, val`, where `build` opens
    /// the telescope and returns `(ty, val)`.
    pub(super) fn add_tele_def(
        &mut self,
        name: &str,
        level_params: &[&str],
        reducible: bool,
        build: impl FnOnce(&mut Tele) -> (Expr, Expr),
    ) -> Result<(), EnvError> {
        let mut t = Tele::new();
        let (ty, val) = build(&mut t);
        self.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: level_params.iter().map(|p| Name::from_string(p)).collect(),
            type_: t.pi(ty),
            value: t.lam(val),
            is_reducible: reducible,
        })
    }

    /// The `StateT` operations and `StateT.instMonad` (`StateT` itself and
    /// `StateT.run` are registered by `init_state_t`).
    pub(crate) fn init_state_t_ops(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        let (u, v) = (lparam("u"), lparam("v"));
        let uv = [u.clone(), v.clone()];
        let uu = [u.clone(), u.clone()];
        let lps = ["u", "v"];
        let state_t = |s: &Expr, m: &Expr, a: &Expr| {
            Expr::apps(cst("StateT", &uv), [s.clone(), m.clone(), a.clone()])
        };
        let prod = |a: &Expr, b: &Expr| Expr::apps(cst("Prod", &uu), [a.clone(), b.clone()]);
        let pair = |a: &Expr, b: &Expr, x: Expr, y: Expr| {
            Expr::apps(cst("Prod.mk", &uu), [a.clone(), b.clone(), x, y])
        };
        let punit = cst("PUnit", &[Level::succ(u.clone())]);
        let punit_unit = cst("PUnit.unit", &[Level::succ(u.clone())]);

        // StateT.pure {σ m} [Monad m] {α} (a : α) : StateT σ m α := fun s => pure (a, s)
        self.add_tele_def("StateT.pure", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let x = t.arg(a.clone());
            let val = {
                let mut t2 = Tele::child(t);
                let st = t2.arg(s.clone());
                t2.lam(mi.pure(prod(&a, &s), pair(&a, &s, x, st)))
            };
            (state_t(&s, &m, &a), val)
        })?;

        // StateT.bind {σ m} [Monad m] {α β} (x : StateT σ m α) (f : α → StateT σ m β)
        //   : StateT σ m β := fun s => bind (x s) (fun p => f p.1 p.2)
        self.add_tele_def("StateT.bind", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let b = t.imp(type_at(&u));
            let x = t.arg(state_t(&s, &m, &a));
            let f = t.arg(Expr::arrow(a.clone(), state_t(&s, &m, &b)));
            let val = {
                let mut t2 = Tele::child(t);
                let st = t2.arg(s.clone());
                let k = {
                    let mut t3 = Tele::child(&t2);
                    let p = t3.arg(prod(&a, &s));
                    let fst = Expr::apps(cst("Prod.fst", &uu), [a.clone(), s.clone(), p.clone()]);
                    let snd = Expr::apps(cst("Prod.snd", &uu), [a.clone(), s.clone(), p]);
                    t3.lam(Expr::apps(f, [fst, snd]))
                };
                t2.lam(mi.bind(prod(&a, &s), prod(&b, &s), Expr::app(x, st), k))
            };
            (state_t(&s, &m, &b), val)
        })?;

        // StateT.get {σ m} [Monad m] : StateT σ m σ := fun s => pure (s, s)
        self.add_tele_def("StateT.get", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let val = {
                let mut t2 = Tele::child(t);
                let st = t2.arg(s.clone());
                t2.lam(mi.pure(prod(&s, &s), pair(&s, &s, st.clone(), st)))
            };
            (state_t(&s, &m, &s), val)
        })?;

        // StateT.set {σ m} [Monad m] (s' : σ) : StateT σ m PUnit := fun _ => pure (⟨⟩, s')
        self.add_tele_def("StateT.set", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let s_new = t.arg(s.clone());
            let val = {
                let mut t2 = Tele::child(t);
                let _ = t2.arg(s.clone());
                t2.lam(mi.pure(
                    prod(&punit, &s),
                    pair(&punit, &s, punit_unit.clone(), s_new),
                ))
            };
            (state_t(&s, &m, &punit), val)
        })?;

        // StateT.modify {σ m} [Monad m] (f : σ → σ) : StateT σ m PUnit
        //   := fun s => pure (⟨⟩, f s)          (Clean-native; Lean spells it
        //   through `MonadStateOf.modifyGet`)
        self.add_tele_def("StateT.modify", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let f = t.arg(Expr::arrow(s.clone(), s.clone()));
            let val = {
                let mut t2 = Tele::child(t);
                let st = t2.arg(s.clone());
                t2.lam(mi.pure(
                    prod(&punit, &s),
                    pair(&punit, &s, punit_unit.clone(), Expr::app(f, st)),
                ))
            };
            (state_t(&s, &m, &punit), val)
        })?;

        // StateT.modifyGet {σ m} [Monad m] {α} (f : σ → α × σ) : StateT σ m α
        //   := fun s => pure (f s)
        self.add_tele_def("StateT.modifyGet", &lps, true, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let f = t.arg(Expr::arrow(s.clone(), prod(&a, &s)));
            let val = {
                let mut t2 = Tele::child(t);
                let st = t2.arg(s.clone());
                t2.lam(mi.pure(prod(&a, &s), Expr::app(f, st)))
            };
            (state_t(&s, &m, &a), val)
        })?;

        // StateT.instMonad {σ m} [Monad m] : Monad (StateT σ m)
        let umv = Level::max(u.clone(), v.clone());
        self.add_monad_instance("StateT.instMonad", &lps, |t| {
            let (s, m, mi) = open_param_monad(t, &u, &v);
            let carrier = Expr::apps(cst("StateT", &uv), [s.clone(), m.clone()]);
            let lv = [u.clone(), umv.clone()];
            let ops = [s, m, mi.inst];
            let pure_i = Expr::apps(
                cst("Pure.mk", &lv),
                [
                    carrier.clone(),
                    Expr::apps(cst("StateT.pure", &uv), ops.clone()),
                ],
            );
            let bind_i = Expr::apps(
                cst("Bind.mk", &lv),
                [carrier.clone(), Expr::apps(cst("StateT.bind", &uv), ops)],
            );
            (u.clone(), umv.clone(), carrier, pure_i, bind_i)
        })
    }

    /// `ExceptT` (Lean's definition), `ExceptT.mk` / `ExceptT.run`, its
    /// `pure` / `bindCont` / `bind`, and `ExceptT.instMonad`.
    pub(crate) fn init_except_t_defs(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        let (u, v) = (lparam("u"), lparam("v"));
        let uv = [u.clone(), v.clone()];
        let lps = ["u", "v"];
        // `ExceptT` instantiates `Except` at `.{u, u}` (Lean 4.8.0:
        // `ExceptT ε m α := m (Except.{u, u} ε α)`).
        let uu = [u.clone(), u.clone()];
        let except = |e: &Expr, a: &Expr| Expr::apps(cst("Except", &uu), [e.clone(), a.clone()]);
        let except_t = |e: &Expr, m: &Expr, a: &Expr| {
            Expr::apps(cst("ExceptT", &uv), [e.clone(), m.clone(), a.clone()])
        };

        // def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v := m (Except ε α)
        self.add_tele_def("ExceptT", &lps, false, |t| {
            let e = t.arg(type_at(&u));
            let m = t.arg(monad_kind(&u, &v));
            let a = t.arg(type_at(&u));
            (type_at(&v), Expr::app(m, except(&e, &a)))
        })?;
        // ExceptT.mk {ε m α} (x : m (Except ε α)) : ExceptT ε m α := x
        self.add_tele_def("ExceptT.mk", &lps, true, |t| {
            let e = t.imp(type_at(&u));
            let m = t.imp(monad_kind(&u, &v));
            let a = t.imp(type_at(&u));
            let x = t.arg(Expr::app(m.clone(), except(&e, &a)));
            (except_t(&e, &m, &a), x)
        })?;
        // ExceptT.run {ε m α} (x : ExceptT ε m α) : m (Except ε α) := x
        self.add_tele_def("ExceptT.run", &lps, true, |t| {
            let e = t.imp(type_at(&u));
            let m = t.imp(monad_kind(&u, &v));
            let a = t.imp(type_at(&u));
            let x = t.arg(except_t(&e, &m, &a));
            (Expr::app(m, except(&e, &a)), x)
        })?;
        let mk = |e: &Expr, m: &Expr, a: &Expr, x: Expr| {
            Expr::apps(cst("ExceptT.mk", &uv), [e.clone(), m.clone(), a.clone(), x])
        };
        let ok = |e: &Expr, a: &Expr, x: Expr| {
            Expr::apps(cst("Except.ok", &uu), [e.clone(), a.clone(), x])
        };
        let error = |e: &Expr, a: &Expr, x: Expr| {
            Expr::apps(cst("Except.error", &uu), [e.clone(), a.clone(), x])
        };

        // ExceptT.pure {ε m} [Monad m] {α} (a : α) : ExceptT ε m α := mk (pure (ok a))
        self.add_tele_def("ExceptT.pure", &lps, true, |t| {
            let (e, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let x = t.arg(a.clone());
            let val = mk(&e, &m, &a, mi.pure(except(&e, &a), ok(&e, &a, x)));
            (except_t(&e, &m, &a), val)
        })?;

        // ExceptT.bindCont {ε m} [Monad m] {α β} (f : α → ExceptT ε m β)
        //   : Except ε α → m (Except ε β)
        //   | .ok a => f a | .error e => pure (.error e)
        self.add_tele_def("ExceptT.bindCont", &lps, true, |t| {
            let (e, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let b = t.imp(type_at(&u));
            let f = t.arg(Expr::arrow(a.clone(), except_t(&e, &m, &b)));
            let r = t.arg(except(&e, &a));
            let res = Expr::app(m.clone(), except(&e, &b));
            let motive = {
                let mut t2 = Tele::child(t);
                let _ = t2.arg(except(&e, &a));
                t2.lam(res.clone())
            };
            let on_error = {
                let mut t2 = Tele::child(t);
                let err = t2.arg(e.clone());
                t2.lam(mi.pure(except(&e, &b), error(&e, &b, err)))
            };
            let on_ok = {
                let mut t2 = Tele::child(t);
                let x = t2.arg(a.clone());
                t2.lam(Expr::app(f, x))
            };
            let val = Expr::apps(
                cst(
                    "Except.casesOn",
                    &[Level::succ(v.clone()), u.clone(), u.clone()],
                ),
                [e.clone(), a.clone(), motive, r, on_error, on_ok],
            );
            (res, val)
        })?;

        // ExceptT.bind {ε m} [Monad m] {α β} (ma : ExceptT ε m α) (f : α → ExceptT ε m β)
        //   : ExceptT ε m β := mk (bind ma (bindCont f))
        self.add_tele_def("ExceptT.bind", &lps, true, |t| {
            let (e, m, mi) = open_param_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let b = t.imp(type_at(&u));
            let ma = t.arg(except_t(&e, &m, &a));
            let f = t.arg(Expr::arrow(a.clone(), except_t(&e, &m, &b)));
            let cont = Expr::apps(
                cst("ExceptT.bindCont", &uv),
                [
                    e.clone(),
                    m.clone(),
                    mi.inst.clone(),
                    a.clone(),
                    b.clone(),
                    f,
                ],
            );
            let val = mk(
                &e,
                &m,
                &b,
                mi.bind(except(&e, &a), except(&e, &b), ma, cont),
            );
            (except_t(&e, &m, &b), val)
        })?;

        self.add_monad_instance("ExceptT.instMonad", &lps, |t| {
            let (e, m, mi) = open_param_monad(t, &u, &v);
            let carrier = Expr::apps(cst("ExceptT", &uv), [e.clone(), m.clone()]);
            let ops = [e, m, mi.inst];
            let pure_i = Expr::apps(
                cst("Pure.mk", &uv),
                [
                    carrier.clone(),
                    Expr::apps(cst("ExceptT.pure", &uv), ops.clone()),
                ],
            );
            let bind_i = Expr::apps(
                cst("Bind.mk", &uv),
                [carrier.clone(), Expr::apps(cst("ExceptT.bind", &uv), ops)],
            );
            (u.clone(), v.clone(), carrier, pure_i, bind_i)
        })
    }

    /// `Except.instMonad.{u, u_1} {ε : Type u} : Monad.{u_1, max u_1 u}
    /// (Except.{u, u_1} ε)` — Lean 4.8.0's universe telescope (`#check
    /// @Except.instMonad`); `pure := Except.ok`, `bind := Except.bind` (Lean's
    /// `Except.pure` / `Except.bind`).
    pub(crate) fn init_except_monad_instance(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        self.add_monad_instance("Except.instMonad", &["u", "u_1"], |t| {
            let (u, u1) = (lparam("u"), lparam("u_1"));
            let carrier_lvl = Level::max(u1.clone(), u.clone());
            let lv = [u1.clone(), carrier_lvl.clone()];
            let e = t.imp(type_at(&u));
            let carrier = Expr::app(cst("Except", &[u.clone(), u1.clone()]), e.clone());
            let pure_i = Expr::apps(
                cst("Pure.mk", &lv),
                [
                    carrier.clone(),
                    Expr::app(cst("Except.ok", &[u.clone(), u1.clone()]), e.clone()),
                ],
            );
            let bind_i = Expr::apps(
                cst("Bind.mk", &lv),
                [
                    carrier.clone(),
                    Expr::app(cst("Except.bind", &[u.clone(), u1.clone(), u1.clone()]), e),
                ],
            );
            (u1, carrier_lvl, carrier, pure_i, bind_i)
        })
    }

    /// `OptionT` (Lean's definition), `OptionT.mk` / `OptionT.run`, its
    /// `pure` / `bind` / `fail`, and `OptionT.instMonad`.
    pub(crate) fn init_option_t_defs(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        let (u, v) = (lparam("u"), lparam("v"));
        let uv = [u.clone(), v.clone()];
        let lps = ["u", "v"];
        let option = |a: &Expr| Expr::app(cst("Option", std::slice::from_ref(&u)), a.clone());
        let option_t = |m: &Expr, a: &Expr| Expr::apps(cst("OptionT", &uv), [m.clone(), a.clone()]);
        let mk = |m: &Expr, a: &Expr, x: Expr| {
            Expr::apps(cst("OptionT.mk", &uv), [m.clone(), a.clone(), x])
        };

        // def OptionT (m : Type u → Type v) (α : Type u) : Type v := m (Option α)
        self.add_tele_def("OptionT", &lps, false, |t| {
            let m = t.arg(monad_kind(&u, &v));
            let a = t.arg(type_at(&u));
            (type_at(&v), Expr::app(m, option(&a)))
        })?;
        self.add_tele_def("OptionT.mk", &lps, true, |t| {
            let m = t.imp(monad_kind(&u, &v));
            let a = t.imp(type_at(&u));
            let x = t.arg(Expr::app(m.clone(), option(&a)));
            (option_t(&m, &a), x)
        })?;
        self.add_tele_def("OptionT.run", &lps, true, |t| {
            let m = t.imp(monad_kind(&u, &v));
            let a = t.imp(type_at(&u));
            let x = t.arg(option_t(&m, &a));
            (Expr::app(m, option(&a)), x)
        })?;
        let some = |a: &Expr, x: Expr| {
            Expr::apps(cst("Option.some", std::slice::from_ref(&u)), [a.clone(), x])
        };
        let none = |a: &Expr| Expr::app(cst("Option.none", std::slice::from_ref(&u)), a.clone());

        // OptionT.pure {m} [Monad m] {α} (a : α) : OptionT m α := mk (pure (some a))
        self.add_tele_def("OptionT.pure", &lps, true, |t| {
            let (m, mi) = open_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let x = t.arg(a.clone());
            (
                option_t(&m, &a),
                mk(&m, &a, mi.pure(option(&a), some(&a, x))),
            )
        })?;
        // OptionT.fail {m} [Monad m] {α} : OptionT m α := mk (pure none)
        self.add_tele_def("OptionT.fail", &lps, true, |t| {
            let (m, mi) = open_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            (option_t(&m, &a), mk(&m, &a, mi.pure(option(&a), none(&a))))
        })?;
        // OptionT.bind {m} [Monad m] {α β} (x : OptionT m α) (f : α → OptionT m β)
        //   : OptionT m β := mk (bind x fun | none => pure none | some a => f a)
        self.add_tele_def("OptionT.bind", &lps, true, |t| {
            let (m, mi) = open_monad(t, &u, &v);
            let a = t.imp(type_at(&u));
            let b = t.imp(type_at(&u));
            let x = t.arg(option_t(&m, &a));
            let f = t.arg(Expr::arrow(a.clone(), option_t(&m, &b)));
            let res = Expr::app(m.clone(), option(&b));
            let k = {
                let mut t2 = Tele::child(t);
                let o = t2.arg(option(&a));
                let motive = {
                    let mut t3 = Tele::child(&t2);
                    let _ = t3.arg(option(&a));
                    t3.lam(res.clone())
                };
                let on_some = {
                    let mut t3 = Tele::child(&t2);
                    let y = t3.arg(a.clone());
                    t3.lam(Expr::app(f, y))
                };
                let cases = Expr::apps(
                    cst("Option.casesOn", &[Level::succ(v.clone()), u.clone()]),
                    [a.clone(), motive, o, mi.pure(option(&b), none(&b)), on_some],
                );
                t2.lam(cases)
            };
            (
                option_t(&m, &b),
                mk(&m, &b, mi.bind(option(&a), option(&b), x, k)),
            )
        })?;

        self.add_monad_instance("OptionT.instMonad", &lps, |t| {
            let (m, mi) = open_monad(t, &u, &v);
            let carrier = Expr::app(cst("OptionT", &uv), m.clone());
            let ops = [m, mi.inst];
            let pure_i = Expr::apps(
                cst("Pure.mk", &uv),
                [
                    carrier.clone(),
                    Expr::apps(cst("OptionT.pure", &uv), ops.clone()),
                ],
            );
            let bind_i = Expr::apps(
                cst("Bind.mk", &uv),
                [carrier.clone(), Expr::apps(cst("OptionT.bind", &uv), ops)],
            );
            (u.clone(), v.clone(), carrier, pure_i, bind_i)
        })
    }
}

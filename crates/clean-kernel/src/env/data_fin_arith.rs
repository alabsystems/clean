// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean-core `Fin n` arithmetic for the builtin prelude.
//!
//! ## Why this exists
//!
//! Before this module the builtin prelude had the `Fin` carrier, `Fin.val`,
//! `Fin.ofNat` and `instOfNatFin`, and NOTHING else Lean core gives `Fin n`:
//! no `Fin.add`, no `Add (Fin n)`. So `(3 : Fin 4) + 1` could
//! not be elaborated at `Fin 4`, and where the result type was still open (an
//! `if`/`match` branch) the elaborator found a `Nat` reading instead:
//!
//! ```text
//! theorem w1 : (if True then (3 : Fin 4) + 1 else 0) ≠ 0 := by decide
//! ```
//!
//! was ACCEPTED as `ite Nat True _ (↑(3 : Fin 4) + 1) 0 ≠ 0` (`4 ≠ 0`), while in
//! Lean the `if` is at `Fin 4`, `(3 : Fin 4) + 1 = 0`, and the statement is
//! FALSE. The kernel was sound; the certified proposition was not the one the
//! Lean source states. (The elaborator half of that defect — a heterogeneous
//! operator goal whose only open slot is its `outParam` being postponed rather
//! than failing — is fixed in `clean-elab`'s `infer/elab_app.rs`.)
//!
//! ## What is mirrored, and from where
//!
//! MEASURED from the Lean v4.8.0 `Init/Data/Fin/Basic.olean` (the
//! `leanprover/lean4:v4.8.0` release, the same line `Fin.ofNat` in `data.rs`
//! pins), decoded with Clean's own `.olean` reader; every name below is also in
//! `clean-elab/data/lean_core/init_constants_v4.8.0.txt`:
//!
//! | constant | type | value |
//! |---|---|---|
//! | `Fin.add` | `{n : Nat} → Fin n → Fin n → Fin n` | `⟨(a + b) % n, _⟩` |
//! | `Fin.sub` | same | `⟨(a + (n - b)) % n, _⟩` |
//! | `Fin.mul` | same | `⟨(a * b) % n, _⟩` |
//! | `Fin.div` | same | `⟨a / b, _⟩` |
//! | `Fin.mod` | same | `⟨a % b, _⟩` |
//! | `Fin.instAdd`/`instSub`/`instMul` | `{n : Nat} → Add (Fin n)` (…) | `⟨Fin.add⟩` (…) |
//!
//! Names and types are Lean's exactly. Values are Lean's with two
//! definitional-shape deviations, neither of which changes a value:
//!
//! * Lean compiles every binary op through the matcher `Fin.add.match_1` and
//!   an auxiliary bound lemma `Fin.<op>.proof_1` (via the private `Fin.mlt`).
//!   Here the matcher is δ-unfolded to the two nested `Fin.casesOn` it is
//!   defined as, and the bound proof is inlined. Declaring Lean's auxiliary
//!   names would add constants whose TYPES would be spelled with the
//!   prelude's bare `Nat.lt` (the `Fin.mk` field type here) where Lean spells
//!   `<` — a new `type_differing` row in `data/prelude_collision_census.json`.
//! * The bound proofs state `Nat.lt v n` (the prelude `Fin.mk` field type)
//!   where Lean states `v < n`; the two are definitionally equal.
//!
//! Lean v4.8.0 has NO `Neg (Fin n)` (neither `Fin.neg` nor `Fin.instNeg` is
//! in the v4.8.0 `Init` constant table), so none is added. INFERRED, not
//! measured: later Lean (v4.30) reorders `Fin.sub`'s sum to `((n - b) + a) %
//! n` for performance; the value is the same function.
//!
//! ## The one non-Lean spelling: `/` and `%`
//!
//! Lean reaches `a / b` and `a % b` on `Fin n` through `@instHDiv (Fin n)
//! Fin.instDiv` / `@instHMod (Fin n) Fin.instMod`, over the homogeneous `Div` /
//! `Mod` classes. The builtin prelude has NO `Div`/`Mod` class (measured: `@Div.div`
//! and `@Mod.mod` are unknown identifiers; see `clean-elab`'s
//! `hetero_bridge_seed.rs` for why `Div` was descoped), so the two ops are
//! registered the way the prelude registers every `Nat`/`UInt*` operator: a
//! direct `HDiv (Fin n) (Fin n) (Fin n)` / `HMod (Fin n) (Fin n) (Fin n)`
//! instance (`instHDivFin` / `instHModFin`, names Lean does not use, so no
//! collision) whose method IS `Fin.div` / `Fin.mod`. `+`, `-` and `*` use
//! Lean's own route: `Fin.instAdd`/`instSub`/`instMul` reached through the
//! `instHAdd`/`instHSub`/`instHMul` bridges, which gives Lean's exact term.
//!
//! ## Deliberately NOT added: the `Fin` order and the bitwise ops
//!
//! Lean v4.8.0 also has `instLTFin`/`instLEFin` with the deciders
//! `Fin.decLt`/`Fin.decLe`, and `Fin.land`/`lor`/`xor`/`shiftLeft`/
//! `shiftRight` with their instances. None is added here, and each refusal is
//! LOUD (`failed to synthesize LT (Fin 4)`, `… HOr (Fin 4) Nat ?N`), never a
//! `Nat` reading. The order was drafted and MEASURED to change terms it must
//! not: Clean's instance search matches up to δ-unfolding with a head-only
//! discrimination key, so `Fin.decLt` captured the `Decidable (a < b)` goal of
//! every `UInt*`/`USize` comparison — their `<` unfolds to a `Fin.val`
//! comparison through the `BitVec` carrier — and `decide (a < b)` over `UInt8`
//! elaborated through `Fin.decLt` instead of `instDecidableUInt8Lt`. That
//! needs a finer candidate key before the instances can land. The bitwise ops
//! need `Nat.land`/`Nat.lor`/`Nat.xor` values this module does not own.
//!
//! ## Decidable equality
//!
//! `instDecidableEqFin` (constructive, `algebra_fin_dec_eq_proof.rs`) was a
//! definition no instance table named, so `Decidable ((a : Fin n) = b)` had no
//! candidate and `decide` could not state a `Fin` equality. It is registered
//! here under `Decidable`, the same way `instDecidableNatLe` is, at the
//! priority Lean's v4.8.0 `.olean` serializes for it (1000, as for
//! `Fin.instAdd`/`instSub`/`instMul`).
//!
//! ## Lanes
//!
//! Import-verification mode (`suppress_lossy_structure_stubs`) withholds the
//! whole overlay, exactly like the `UInt` arithmetic overlay: the genuine Lean
//! declarations import through the checked path there (the prelude's
//! `Fin.ofNat` is withheld in that lane for the same reason).

use super::decl_builder::EnvDeclBuilder;
use super::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
    LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// A binary `Fin n` operation: its Lean name and how its `Nat` value is formed
/// from the two components `a`, `b` and the bound `n`.
#[derive(Clone, Copy)]
enum FinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl FinOp {
    const ALL: [FinOp; 5] = [FinOp::Add, FinOp::Sub, FinOp::Mul, FinOp::Div, FinOp::Mod];

    fn name(self) -> &'static str {
        match self {
            FinOp::Add => "Fin.add",
            FinOp::Sub => "Fin.sub",
            FinOp::Mul => "Fin.mul",
            FinOp::Div => "Fin.div",
            FinOp::Mod => "Fin.mod",
        }
    }
}

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@H<Op>.h<Op>.{0,0,0} Nat Nat Nat inst<H…>Nat a b` — the term Clean
/// elaborates `a + b` (…) to over `Nat`, so the values below read exactly as
/// the elaborator would produce them from Lean's source.
fn nat_binop(method: &str, inst: &str, a: Expr, b: Expr) -> Expr {
    let lz = vec![Level::zero(), Level::zero(), Level::zero()];
    let nat = k("Nat");
    Expr::apps(
        Expr::const_(Name::from_string(method), lz),
        [nat.clone(), nat.clone(), nat, k(inst), a, b],
    )
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    nat_binop("HAdd.hAdd", "instHAddNat", a, b)
}
fn nat_sub(a: Expr, b: Expr) -> Expr {
    nat_binop("HSub.hSub", "instHSubNat", a, b)
}
fn nat_mul(a: Expr, b: Expr) -> Expr {
    nat_binop("HMul.hMul", "instHMulNat", a, b)
}
fn nat_div(a: Expr, b: Expr) -> Expr {
    nat_binop("HDiv.hDiv", "instHDivNat", a, b)
}
fn nat_mod(a: Expr, b: Expr) -> Expr {
    nat_binop("HMod.hMod", "instHModNat", a, b)
}

/// `Nat.lt a b` — the prelude `Fin.mk` field type.
fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(k("Nat.lt"), [a, b])
}

impl Environment {
    /// Register Lean-core `Fin n` arithmetic (`Fin.add`/`sub`/`mul`/`div`/`mod`
    /// and their operator instances) and make `instDecidableEqFin` an
    /// instance.
    /// See the module docs for what is mirrored and the measured source.
    ///
    /// Idempotent: every declaration goes through
    /// `ensure_exact_checked_decl` and every registration through
    /// `ensure_exact_instance`, so a repeat call is a no-op and a conflicting
    /// pre-existing declaration fails closed. A no-op in import-verification
    /// mode.
    pub(crate) fn init_fin_arith(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Everything below is kernel-checked against these; each call is
        // idempotent.
        self.init_fin()?;
        self.init_add()?;
        self.init_sub()?;
        self.init_mul()?;
        self.init_hdiv()?;
        self.init_hmod()?;
        self.init_nat_hadd_inst()?;
        self.init_nat_hsub_inst()?;
        self.init_nat_hmul_inst()?;
        self.init_nat_hdiv_inst()?;
        self.init_nat_hmod_inst()?;
        self.init_nat_div_mod_lemmas()?; // Nat.mod_lt, Nat.div_add_mod
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.register_fin_dec_eq_proof()?; // instDecidableEqFin

        for op in FinOp::ALL {
            self.register_fin_binop(op)?;
        }
        self.register_fin_op_instances()?;
        self.register_fin_dec_eq_instance()?;
        Ok(())
    }

    /// `Fin.<op> : {n : Nat} → Fin n → Fin n → Fin n`, Lean v4.8.0's value
    /// with `Fin.add.match_1` δ-unfolded to its two `Fin.casesOn` and the
    /// bound lemma inlined.
    fn register_fin_binop(&mut self, op: FinOp) -> Result<(), EnvError> {
        let nat = k("Nat");
        let fin = k("Fin");
        let fin_mk = k("Fin.mk");
        let cases_on = Expr::const_(
            Name::from_string("Fin.casesOn"),
            vec![Level::succ(Level::zero())],
        );
        let fin_n = |n: &Expr| Expr::app(fin.clone(), n.clone());

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let r = Expr::pi(
                BinderInfo::Default,
                fin_n(&n),
                Expr::pi(BinderInfo::Default, fin_n(&n), fin_n(&n)),
            );
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(fin_n(&n));
            let (y_id, y) = b.fresh_local(fin_n(&n));
            let (a_id, a) = b.fresh_local(nat.clone());
            let (h1_id, h1) = b.fresh_local(nat_lt(a.clone(), n.clone()));
            let (bb_id, bb) = b.fresh_local(nat.clone());
            let (h2_id, _h2) = b.fresh_local(nat_lt(bb.clone(), n.clone()));
            // Non-dependent motive `fun (_ : Fin n) => Fin n`.
            let motive = {
                let (w_id, _w) = b.fresh_local(fin_n(&n));
                b.mk_lam(w_id, BinderInfo::Default, fin_n(&n), fin_n(&n))
            };
            let (val, bound) = Self::fin_binop_value_and_bound(op, &a, &h1, &bb, &n);
            let mk = Expr::apps(fin_mk.clone(), [n.clone(), val, bound]);
            let inner_minor = b.mk_lam(
                bb_id,
                BinderInfo::Default,
                nat.clone(),
                b.mk_lam(
                    h2_id,
                    BinderInfo::Default,
                    nat_lt(bb.clone(), n.clone()),
                    mk,
                ),
            );
            let inner = Expr::apps(
                cases_on.clone(),
                [n.clone(), motive.clone(), y.clone(), inner_minor],
            );
            let outer_minor = b.mk_lam(
                a_id,
                BinderInfo::Default,
                nat.clone(),
                b.mk_lam(
                    h1_id,
                    BinderInfo::Default,
                    nat_lt(a.clone(), n.clone()),
                    inner,
                ),
            );
            let body = Expr::apps(cases_on, [n.clone(), motive, x, outer_minor]);
            let r = b.mk_lam(y_id, BinderInfo::Default, fin_n(&n), body);
            let r = b.mk_lam(x_id, BinderInfo::Default, fin_n(&n), r);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat, r);
            b.finish(r)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string(op.name()),
            level_params: vec![],
            type_,
            value,
            // Lean: `Regular` hints (a plain `protected def`), not `@[reducible]`.
            is_reducible: false,
        })
    }

    /// The `Nat` value of `op` on components `a`, `b` at bound `n`, and a proof
    /// that it is `Nat.lt _ n`, given `h1 : Nat.lt a n`.
    fn fin_binop_value_and_bound(
        op: FinOp,
        a: &Expr,
        h1: &Expr,
        b: &Expr,
        n: &Expr,
    ) -> (Expr, Expr) {
        let zero = k("Nat.zero");
        // `Nat.lt_of_le_of_lt (x y z : Nat) : x ≤ y → y < z → x < z`.
        let lt_of_le_of_lt = |x: Expr, le: Expr| {
            Expr::apps(
                k("Nat.lt_of_le_of_lt"),
                [x, a.clone(), n.clone(), le, h1.clone()],
            )
        };
        // `0 < n` from `a < n`: `Nat.lt_of_le_of_lt 0 a n (Nat.zero_le a) h1`.
        let pos = lt_of_le_of_lt(zero, Expr::app(k("Nat.zero_le"), a.clone()));
        // `Nat.mod_lt (x y : Nat) : Nat.lt 0 y → Nat.lt (x % y) y`.
        let mod_lt = |x: Expr| Expr::apps(k("Nat.mod_lt"), [x, n.clone(), pos.clone()]);
        match op {
            FinOp::Add => {
                let s = nat_add(a.clone(), b.clone());
                (nat_mod(s.clone(), n.clone()), mod_lt(s))
            }
            FinOp::Sub => {
                let s = nat_add(a.clone(), nat_sub(n.clone(), b.clone()));
                (nat_mod(s.clone(), n.clone()), mod_lt(s))
            }
            FinOp::Mul => {
                let s = nat_mul(a.clone(), b.clone());
                (nat_mod(s.clone(), n.clone()), mod_lt(s))
            }
            FinOp::Div => {
                // `Nat.div_le_self (x y : Nat) : Nat.le (x / y) x`.
                let v = nat_div(a.clone(), b.clone());
                let le = Expr::apps(k("Nat.div_le_self"), [a.clone(), b.clone()]);
                (v.clone(), lt_of_le_of_lt(v, le))
            }
            FinOp::Mod => {
                // `a % b ≤ a`, which the prelude has no lemma for (Lean's is
                // `Nat.mod_le`; not declared here, see the module docs): from
                // `Nat.div_add_mod a b : (a / b) * b + a % b = a` and
                // `Nat.le_add_left (a % b) ((a / b) * b)`, transported along
                // the equation by `Eq.subst`.
                let v = nat_mod(a.clone(), b.clone());
                let raw_mod = Expr::apps(k("Nat.mod"), [a.clone(), b.clone()]);
                let raw_mul = Expr::apps(
                    k("Nat.mul"),
                    [Expr::apps(k("Nat.div"), [a.clone(), b.clone()]), b.clone()],
                );
                let lhs = Expr::apps(k("Nat.add"), [raw_mul.clone(), raw_mod.clone()]);
                let nat = k("Nat");
                let motive = Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::apps(k("Nat.le"), [raw_mod.clone(), Expr::bvar(0)]),
                );
                let le = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.subst"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [
                        nat,
                        motive,
                        lhs,
                        a.clone(),
                        Expr::apps(k("Nat.div_add_mod"), [a.clone(), b.clone()]),
                        Expr::apps(k("Nat.le_add_left"), [raw_mod, raw_mul]),
                    ],
                );
                (v.clone(), lt_of_le_of_lt(v, le))
            }
        }
    }

    /// `Fin.instAdd`/`instSub`/`instMul` (Lean's names and values) and the
    /// prelude-convention `instHDivFin`/`instHModFin` (see module docs).
    fn register_fin_op_instances(&mut self) -> Result<(), EnvError> {
        let nat = k("Nat");
        let fin = k("Fin");
        // (instance, class, class ctor, op, is_hetero)
        let rows: [(&str, &str, &str, &str, bool); 5] = [
            ("Fin.instAdd", "Add", "Add.mk", "Fin.add", false),
            ("Fin.instSub", "Sub", "Sub.mk", "Fin.sub", false),
            ("Fin.instMul", "Mul", "Mul.mk", "Fin.mul", false),
            ("instHDivFin", "HDiv", "HDiv.mk", "Fin.div", true),
            ("instHModFin", "HMod", "HMod.mk", "Fin.mod", true),
        ];
        for (inst, class, ctor, op, hetero) in rows {
            let levels = if hetero {
                vec![Level::zero(), Level::zero(), Level::zero()]
            } else {
                vec![Level::zero()]
            };
            let class_c = Expr::const_(Name::from_string(class), levels.clone());
            let ctor_c = Expr::const_(Name::from_string(ctor), levels);
            let carriers = |n: &Expr| -> Vec<Expr> {
                let fin_n = Expr::app(fin.clone(), n.clone());
                if hetero {
                    vec![fin_n.clone(), fin_n.clone(), fin_n]
                } else {
                    vec![fin_n]
                }
            };
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                let r = Expr::apps(class_c.clone(), carriers(&n));
                let r = b.mk_pi(n_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                let method = Expr::app(k(op), n.clone());
                let mut args = carriers(&n);
                args.push(method);
                let r = Expr::apps(ctor_c.clone(), args);
                let r = b.mk_lam(n_id, BinderInfo::Implicit, nat.clone(), r);
                b.finish(r)
            };
            self.ensure_exact_checked_decl(Declaration::Definition {
                name: Name::from_string(inst),
                level_params: vec![],
                type_,
                value,
                is_reducible: true,
            })?;
            self.ensure_exact_instance(KernelInstanceInfo {
                name: Name::from_string(inst),
                class_name: Name::from_string(class),
                // Lean's own instances are unannotated (1000); the two
                // prelude-convention operator instances follow the prelude's
                // `instH*Nat`/`instH*UInt*` rows (100).
                priority: if hetero {
                    DEFAULT_INSTANCE_PRIORITY
                } else {
                    LEAN_DEFAULT_INSTANCE_PRIORITY
                },
                type_: None,
                value: None,
            })?;
        }
        Ok(())
    }

    /// Register the existing constructive `instDecidableEqFin : {n : Nat} →
    /// (a b : Fin n) → Decidable (a = b)` under `Decidable`, so
    /// `Decidable ((a : Fin n) = b)` has a candidate.
    fn register_fin_dec_eq_instance(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("instDecidableEqFin");
        let Some(ty) = self.get_const(&name).map(|c| c.type_.clone()) else {
            return Err(EnvError::InitializationConflict {
                name,
                detail: "instDecidableEqFin must be registered before init_fin_arith".to_string(),
            });
        };
        self.ensure_exact_instance(KernelInstanceInfo {
            name: name.clone(),
            class_name: Name::from_string("Decidable"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: Some(ty),
            value: Some(Expr::const_(name, vec![])),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    const DEFS: [&str; 10] = [
        "Fin.add",
        "Fin.sub",
        "Fin.mul",
        "Fin.div",
        "Fin.mod",
        "Fin.instAdd",
        "Fin.instSub",
        "Fin.instMul",
        "instHDivFin",
        "instHModFin",
    ];

    /// Every added constant is a kernel-checked, axiom-free `Definition`, and
    /// a second `init_fin_arith` adds nothing — no declaration, no instance.
    #[test]
    fn fin_arith_is_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in DEFS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is in the builtin prelude"));
            assert_eq!(
                info.kind,
                super::super::types::ConstantKind::Definition,
                "{name} must be a computable Definition"
            );
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .expect("registered");
            assert!(deps.is_empty(), "{name} must be axiom-free, got {deps:?}");
        }
        for inst in [
            "Fin.instAdd",
            "Fin.instSub",
            "Fin.instMul",
            "instHDivFin",
            "instHModFin",
            "instDecidableEqFin",
        ] {
            assert!(
                env.is_instance(&Name::from_string(inst)),
                "{inst} is an instance"
            );
        }
        let (constants, instances) = (env.num_constants(), env.num_instances());
        env.init_fin_arith().expect("idempotent");
        assert_eq!(
            env.num_constants(),
            constants,
            "a repeat call adds no constant"
        );
        assert_eq!(
            env.num_instances(),
            instances,
            "a repeat call adds no instance"
        );
    }

    /// Lean v4.8.0's values: `(3 : Fin 4) + 1 = 0`, `1 - 2 = 3`, `3 * 3 = 1`,
    /// `3 / 2 = 1`, `3 % 2 = 1`, `3 / 0 = 0`, `3 % 0 = 3` — by kernel
    /// definitional unfolding of `Fin.val (Fin.<op> a b)`.
    #[test]
    fn fin_arith_values_are_leans() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let four = Expr::nat_lit(4);
        // `Fin.ofNat 3 v : Fin (Nat.succ 3)`, i.e. `(v : Fin 4)`.
        let lit = |v: u64| Expr::apps(k("Fin.ofNat"), [Expr::nat_lit(3), Expr::nat_lit(v)]);
        let val = |op: &str, a: u64, b: u64| {
            Expr::apps(
                k("Fin.val"),
                [
                    four.clone(),
                    Expr::apps(k(op), [four.clone(), lit(a), lit(b)]),
                ],
            )
        };
        for (op, a, b, want) in [
            ("Fin.add", 3, 1, 0),
            ("Fin.sub", 1, 2, 3),
            ("Fin.mul", 3, 3, 1),
            ("Fin.div", 3, 2, 1),
            ("Fin.mod", 3, 2, 1),
            ("Fin.div", 3, 0, 0),
            ("Fin.mod", 3, 0, 3),
        ] {
            assert!(
                tc.is_def_eq(&val(op, a, b), &Expr::nat_lit(want)),
                "{op} {a} {b} must be {want} in Fin 4"
            );
            assert!(
                !tc.is_def_eq(&val(op, a, b), &Expr::nat_lit(want + 1)),
                "{op} {a} {b} must not be {}",
                want + 1
            );
        }
    }

    /// The import-verification prelude withholds the overlay, so the genuine
    /// Lean declarations import through the checked path.
    #[test]
    fn import_prelude_withholds_fin_arith() {
        let env = Environment::try_with_prelude_for_import().expect("import prelude");
        for name in DEFS {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{name} must not be seeded in import mode"
            );
        }
    }
}

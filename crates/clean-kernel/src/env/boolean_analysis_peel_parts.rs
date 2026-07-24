// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the coordinate-peel `g`/`h` parts and the
//! reconstruction identity.
//!
//! For a function `F : HCPoint (n+1) → Rat`, the B7 hypercontractivity induction
//! peels the last coordinate: write `x = (x', xₙ) ` with `x' : HCPoint n` and the
//! last bit `b : Bool` (`xₙ = pm b`). The two restrictions to the `b = false` /
//! `b = true` halves are recombined through the un-normalized parts
//!
//! ```text
//! BoolAnalysis.gPart n F x := F (extendF n x) + F (extendT n x)       (= 2·g)
//! BoolAnalysis.hPart n F x := F (extendT n x) − F (extendF n x)       (= −2·h)
//! ```
//!
//! both reducible `Declaration::Definition`s over the peel extension maps
//! (`BoolAnalysis.extendF` / `extendT`, `boolean_analysis_peel.rs`).
//!
//! The reconstruction identity (the clean algebraic fact the `hc24` induction
//! consumes — `Bool.rec` case split on the peeled bit `b`):
//!
//! ```text
//! BoolAnalysis.peel_reconstruct :
//!   ∀ (n) (F : HCPoint (n+1) → Rat) (x : HCPoint n) (b : Bool),
//!     Rat.mul (F (extend_b n x)) 2
//!       = Rat.sub (gPart n F x) (Rat.mul (pm b) (hPart n F x))
//! ```
//!
//! where `extend_b = extendF` if `b = false`, `extendT` if `b = true`. At ρ = 1
//! this is the textbook peel step `F(x',b) = g(x') + xₙ·h(x')` doubled:
//!   - `b = false` (`pm false = +1`): `2·F(extendF) = gPart − hPart`
//!     `= (F₊ + F₋) − (F₋ − F₊) = 2·F₊`  ✓
//!   - `b = true`  (`pm true  = −1`): `2·F(extendT) = gPart + hPart`
//!     `= (F₊ + F₋) + (F₋ − F₊) = 2·F₋`  ✓
//!
//! The `Bool.rec` split lands a closed Rat ring identity in each branch (`pm b`
//! and `extend_b` both compute on the closed constructor), discharged by the
//! `RingConsts` add/sub/neg congruence chain. Constructive, empty domain-axiom
//! closure.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the peel `g`/`h` parts + reconstruction.
struct PeelPartsConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_mul: Expr,
    rat_two: Expr,
    hcpoint: Expr,
    extend_f: Expr,
    extend_t: Expr,
    g_part: Expr,
    h_part: Expr,
    pm: Expr,
}

impl PeelPartsConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_two: {
                // `Rat.mk (Int.ofNat 2) 1` — the rational constant `2`, the
                // un-normalized doubling factor.
                let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
                let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
                let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
                let nat_one = Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    nat_zero.clone(),
                );
                let two = Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    nat_one.clone(),
                );
                Expr::apps(rat_mk, [Expr::app(int_of_nat, two), nat_one])
            },
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            g_part: Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
            h_part: Expr::const_(Name::from_string("BoolAnalysis.hPart"), vec![]),
            pm: Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    /// `HCPoint (n+1) → Rat` — the type of the peeled function `F`.
    fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.hcpoint_of(&self.succ(n)),
            self.rat.clone(),
        )
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `F (extendF n x)`.
    fn f_ext_f(&self, f: &Expr, n: &Expr, x: &Expr) -> Expr {
        Expr::app(
            f.clone(),
            Expr::apps(self.extend_f.clone(), [n.clone(), x.clone()]),
        )
    }
    /// `F (extendT n x)`.
    fn f_ext_t(&self, f: &Expr, n: &Expr, x: &Expr) -> Expr {
        Expr::app(
            f.clone(),
            Expr::apps(self.extend_t.clone(), [n.clone(), x.clone()]),
        )
    }
    /// `gPart n F x`.
    fn g_of(&self, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.g_part.clone(), [n.clone(), f.clone(), x.clone()])
    }
    /// `hPart n F x`.
    fn h_of(&self, n: &Expr, f: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.h_part.clone(), [n.clone(), f.clone(), x.clone()])
    }
    /// `pm b`.
    fn pm_of(&self, b: &Expr) -> Expr {
        Expr::app(self.pm.clone(), b.clone())
    }
}

impl Environment {
    /// Initialize the coordinate-peel `g`/`h` parts and the reconstruction lemma.
    /// Idempotent; axiom-free.
    pub(crate) fn init_boolean_analysis_peel_parts(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_peel_parts_init {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_peel()?;
        self.init_boolean_analysis()?; // BoolAnalysis.pm
        self.init_boolean_analysis_ring_identities()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let c = PeelPartsConsts::new();
        self.register_g_part(&c)?;
        self.register_h_part(&c)?;
        self.register_peel_reconstruct(&c)?;

        self.boolean_analysis_peel_parts_init = true;
        Ok(())
    }

    /// Whether the peel parts have been initialized.
    pub(crate) fn has_boolean_analysis_peel_parts(&self) -> bool {
        self.boolean_analysis_peel_parts_init
    }

    /// `BoolAnalysis.gPart n F x := F (extendF n x) + F (extendT n x)`.
    fn register_g_part(&mut self, c: &PeelPartsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.gPart");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_part(c, true);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.hPart n F x := F (extendT n x) − F (extendF n x)`.
    fn register_h_part(&mut self, c: &PeelPartsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hPart");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_part(c, false);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `BoolAnalysis.peel_reconstruct :
    ///   ∀ n F x b, F (extend_b n x)·2 = gPart n F x − pm b · hPart n F x`.
    /// Kernel-checked, constructive. Idempotent.
    fn register_peel_reconstruct(&mut self, c: &PeelPartsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.peel_reconstruct");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_reconstruct(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + value of `gPart` (`is_g = true`) or `hPart` (`is_g = false`).
/// Both: `(n : Nat) → (F : HCPoint (n+1) → Rat) → (x : HCPoint n) → Rat`.
fn build_part(c: &PeelPartsConsts, is_g: bool) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, _f) = b.fresh_local(c.f_type(&n));
        let (x_id, _x) = b.fresh_local(c.hcpoint_of(&n));
        let e = b.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), c.rat.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let ff = c.f_ext_f(&f, &n, &x);
        let ft = c.f_ext_t(&f, &n, &x);
        let body = if is_g {
            c.add(ff, ft) // F(extF) + F(extT)
        } else {
            c.sub(ft, ff) // F(extT) − F(extF)
        };
        let e = b.mk_lam(x_id, BinderInfo::Default, c.hcpoint_of(&n), body);
        let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

/// Build the type + proof of `peel_reconstruct`.
fn build_reconstruct(c: &PeelPartsConsts) -> (Expr, Expr) {
    // The OUTER recursor eliminates into the `Eq` Prop goal ⇒ `Bool.rec.{0}`.
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let (bb_id, bv) = b.fresh_local(c.bool_.clone());
        // Use `extend_b` resolved through `Bool.rec` is unnecessary in the TYPE —
        // the statement quantifies over `b` and the LHS `F (extend_b n x)` is the
        // value `Bool.rec extendT extendF b`-applied. We state it with an explicit
        // `Bool.rec` selecting the extension map, so each branch's `Eq.refl`-grade
        // selection is definitional.
        let ext_b = bool_rec_extend(c, &bv);
        let lhs = c.mul(
            Expr::app(f.clone(), Expr::apps(ext_b, [n.clone(), x.clone()])),
            c.rat_two.clone(),
        );
        let rhs = c.sub(c.g_of(&n, &f, &x), c.mul(c.pm_of(&bv), c.h_of(&n, &f, &x)));
        let concl = eq_rat(c, lhs, rhs);
        let e = b.mk_pi(bb_id, BinderInfo::Default, c.bool_.clone(), concl);
        let e = b.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (f_id, f) = b.fresh_local(c.f_type(&n));
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let (bb_id, bv) = b.fresh_local(c.bool_.clone());

        // motive : fun (b : Bool) => F (extend_b n x)·2 = gPart − pm b · hPart
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (mb_id, mb) = m.fresh_local(c.bool_.clone());
            let ext_b = bool_rec_extend(c, &mb);
            let lhs = c.mul(
                Expr::app(f.clone(), Expr::apps(ext_b, [n.clone(), x.clone()])),
                c.rat_two.clone(),
            );
            let rhs = c.sub(c.g_of(&n, &f, &x), c.mul(c.pm_of(&mb), c.h_of(&n, &f, &x)));
            let body = eq_rat(c, lhs, rhs);
            m.finish_child(m.mk_lam(mb_id, BinderInfo::Default, c.bool_.clone(), body))
        };

        // Bool.rec minor premises (constructor order: false then true).
        // false branch: extend_b ≡ extendF, pm false ≡ 1.
        let false_minor = reconstruct_branch(c, &b, &n, &f, &x, false);
        // true branch: extend_b ≡ extendT, pm true ≡ −1.
        let true_minor = reconstruct_branch(c, &b, &n, &f, &x, true);

        // @Bool.rec.{1} motive false_minor true_minor b : motive b
        let rec = Expr::apps(
            bool_rec.clone(),
            [motive, false_minor, true_minor, bv.clone()],
        );

        let e = b.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), rec);
        let e = b.mk_lam(x_id, BinderInfo::Default, c.hcpoint_of(&n), e);
        let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

/// `@Bool.rec (fun _ => (n)→HCPoint n→HCPoint (n+1)) extendF extendT b` — the
/// extension map selected by the bit `b` (false → extendF, true → extendT).
fn bool_rec_extend(c: &PeelPartsConsts, b: &Expr) -> Expr {
    let bool_rec = Expr::const_(
        Name::from_string("Bool.rec"),
        vec![Level::succ(Level::zero())],
    );
    // motive: fun (_ : Bool) => (n : Nat) → HCPoint n → HCPoint (n+1)
    let extend_ty = {
        let mut d = EnvDeclBuilder::new();
        let (n_id, n) = d.fresh_local(c.nat.clone());
        let (x_id, _x) = d.fresh_local(c.hcpoint_of(&n));
        let concl = c.hcpoint_of(&c.succ(&n));
        let e = d.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), concl);
        let e = d.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        d.finish(e)
    };
    let motive = Expr::lam(BinderInfo::Default, c.bool_.clone(), extend_ty);
    Expr::apps(
        bool_rec,
        [motive, c.extend_f.clone(), c.extend_t.clone(), b.clone()],
    )
}

/// `@Eq.{1} Rat l r`.
fn eq_rat(c: &PeelPartsConsts, l: Expr, r: Expr) -> Expr {
    let eq1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::apps(eq1, [c.rat.clone(), l, r])
}

/// Proof term for one `Bool.rec` branch of `peel_reconstruct` (`use_true` picks
/// the `b = true` branch). After ι on `Bool.rec` (extend map) and δ on `pm`/`gPart`
/// /`hPart`, the goal is a closed Rat ring identity — false: `F₊·2 = (F₊+F₋) −
/// 1·(F₋−F₊)` (`pm false = 1`); true: `F₋·2 = (F₊+F₋) − (−1)·(F₋−F₊)` (`pm true =
/// −1`) — proved by the `RingConsts` add/sub/neg chain (see `branch_ring_proof`).
fn reconstruct_branch(
    c: &PeelPartsConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    x: &Expr,
    use_true: bool,
) -> Expr {
    // F₊ := F (extendF n x), F₋ := F (extendT n x).
    let f_plus = c.f_ext_f(f, n, x);
    let f_minus = c.f_ext_t(f, n, x);
    branch_ring_proof(parent, c, &f_plus, &f_minus, use_true)
}

/// The closed-Rat ring proof of one reconstruction branch, in terms of the two
/// leaf values `p := F₊` and `m := F₋`.
///
/// Goal after the `Bool.rec`/`pm`/part δ+ι reductions (the kernel checks the
/// branch term against the motive instance, which is **def-eq** to these closed
/// goals because `extend_b`, `pm b`, `gPart`, `hPart` all reduce):
///   - false: `p·2 = (p+m) − 1·(m−p)`
///   - true:  `m·2 = (p+m) − (−1)·(m−p)`
fn branch_ring_proof(
    parent: &EnvDeclBuilder,
    c: &PeelPartsConsts,
    p: &Expr,
    m: &Expr,
    use_true: bool,
) -> Expr {
    let rc = RingConsts::new();
    let two = c.rat_two.clone();
    let gpart = rc.add(p.clone(), m.clone()); // p + m  (= gPart, def-eq)
    let hpart = rc.sub(m.clone(), p.clone()); // m − p  (= hPart, def-eq)

    if use_true {
        // Goal: m·2 = (p+m) − (−1)·(m−p)
        let twice_m = rc.mul(m.clone(), two.clone());
        rc_recon_true(parent, &rc, c, p, m, &twice_m, &gpart, &hpart)
    } else {
        // Goal: p·2 = (p+m) − 1·(m−p)
        let twice_p = rc.mul(p.clone(), two.clone());
        rc_recon_false(parent, &rc, c, p, m, &twice_p, &gpart, &hpart)
    }
}

include!("boolean_analysis_peel_parts_ring.rs");

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_peel_parts()
            .expect("init_boolean_analysis_peel_parts should succeed");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_peel_parts().expect("first init");
        env.init_boolean_analysis_peel_parts()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_peel_parts());
    }

    #[test]
    fn test_parts_registered_as_definitions() {
        let env = env();
        for name in ["BoolAnalysis.gPart", "BoolAnalysis.hPart"] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition"
            );
        }
    }

    #[test]
    fn test_parts_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["BoolAnalysis.gPart", "BoolAnalysis.hPart"] {
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    #[test]
    fn test_peel_reconstruct_is_constructive_theorem() {
        let env = env();
        let name = Name::from_string("BoolAnalysis.peel_reconstruct");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("peel_reconstruct proof must check against its type");
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

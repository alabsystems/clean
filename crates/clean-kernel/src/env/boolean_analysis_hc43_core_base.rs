// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3, 4)` campaign — the **base case** `hc43_core_base` (n = 0) of
//! the `(4/3,4)`-hypercontractivity operator induction, plus the shared
//! `hc43_core` statement builder. The dual of `hc24_core_base`.
//!
//! The full induction target (built by [`hc43_core_concl`], reused by base and
//! step) — the un-normalised dual HC `Σ pow4(T_{ρ}F) ≤ 4ⁿ·norm43³`:
//!
//! ```text
//! BoolAnalysis.hc43_core :
//!   ∀ (ρ : Rat) (n : Nat) (F s r : HCPoint n → Rat)
//!     (hs : ∀ x, 0 ≤ s x) (hr : ∀ x, 0 ≤ r x) (hr1 : ∀ x, r x < 1)
//!     (hrecon : ∀ x, |F x| = ((s x · s x)· s x)· r x)
//!     (hnn : ∀ jx, 0 ≤ pow4 (noiseFn ρ n F jx))
//!     (h4n : 0 ≤ Rat.powNat 4 n),
//!     Rat.le (3·(ρ·ρ)) 1 →
//!     <two-point base h_tp> →
//!       NNReal.le
//!         (NNReal.finSum (2^n) (fun jx => NNReal.ofRat (pow4 (noiseFn ρ n F jx)) (hnn jx)))
//!         (NNReal.mul (NNReal.ofRat (Rat.powNat 4 n) h4n) (norm43_cubed n F s r hs))
//! ```
//!
//! with `pow4 x := (x·x)·(x·x)`, `4^n := Rat.powNat 4 n`, and `norm43_cubed n F s
//! r hs := ((norm43 …)·(norm43 …))·(norm43 …)` (the landed `4/3`-norm cube, with
//! the per-point scaling witnesses `(s, r, hs, hr, hr1, hrecon)` the RHS needs —
//! the witness bundle the MERGE agent's report flagged).
//!
//! ## Base case (`n = 0`) — pure carrier collapse + the `pow43Gen` cube identity
//!
//! `2^0 ≡ 1`, `powNat 4 0 ≡ 1`. The LHS `NNReal.finSum 1` collapses (via the
//! `NNReal.finSum_succ`/`_zero` recursion + `NNReal.zero_add`) to its single
//! point `NNReal.ofRat (pow4 (noiseFn ρ 0 F (last 0))) _`. Because `noiseFn ρ 0 F
//! (last 0) = F(dec)` (`noiseFn_zero_dim` + density ≡ 1 defeq + `Rat.mul_one`),
//! this lifts to `NNReal.ofRat (pow4 (F dec)) _`, syntactically `NNReal.ofRat
//! (((F dec·F dec)·(F dec·F dec))) _`. By `pow43Gen_cubed` at `|F dec|` (with the
//! carried witnesses `(s,r,hs,hr,hr1,hrecon)` at `dec`, giving `|F dec|⁴ =
//! pow43Gen-cube` and `|F dec|⁴ = (F dec)⁴` by `Rat.abs` evenness), this equals
//! `(pow43Gen |F dec| …)³`. The RHS `1 · norm43_cubed 0 = (Σ_1 pow43Gen)³`
//! collapses to the SAME single-point cube (via `norm43`'s `finSum_succ`/`_zero`
//! recursion, `NNReal.zero_add`, `NNReal.mul_comm`, and `NNReal.mul_one`). Both
//! sides are then the same `NNReal`, and the goal closes by `NNReal.le.refl`.
//!
//! Constructive, empty domain-axiom closure (leaves: the landed `NNReal.finSum_*`
//! / `norm43_card_zero` / `pow43Gen_cubed` / `noiseFn_zero_dim` / `Rat.*` /
//! `NNReal.le.refl` and the `Eq` built-ins). The two-point base `h_tp` is an
//! UNUSED explicit hypothesis at `n=0` (the base does not need it; the step does)
//! — it is threaded only to match `hc43_core`'s telescope.

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants + smart-constructors for the `hc43_core` statement and the
/// base-case proof.
pub(super) struct Hc43Consts {
    pub(super) o: HcBoundsConsts,
    pub(super) l1: Level,
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_le: Expr,
    pub(super) rat_lt: Expr,
    pub(super) rat_abs: Expr,
    pub(super) rat_abs_nonneg: Expr,
    pub(super) nat_pow: Expr,
    pub(super) nat_succ: Expr,
    pub(super) nat_zero: Expr,
    pub(super) two: Expr,
    pub(super) four: Expr,
    pub(super) fin: Expr,
    pub(super) fin_last: Expr,
    pub(super) fin_cast_succ: Expr,
    pub(super) pow_nat: Expr,
    pub(super) hcpoint: Expr,
    pub(super) hc_decode: Expr,
    pub(super) noise_fn: Expr,
    pub(super) nnreal: Expr,
    pub(super) nnreal_mul: Expr,
    pub(super) nnreal_add: Expr,
    pub(super) nnreal_le: Expr,
    pub(super) nnreal_of_rat: Expr,
    pub(super) nnreal_finsum: Expr,
    pub(super) pow43_gen: Expr,
    pub(super) norm43: Expr,
    pub(super) norm43_cubed: Expr,
}

impl Hc43Consts {
    pub(super) fn new() -> Self {
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let n1 = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), n1.clone());
        // 4 = succ^4 0
        let mut four = nat_zero.clone();
        for _ in 0..4 {
            four = Expr::app(nat_succ.clone(), four);
        }
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: HcBoundsConsts::new(),
            l1: Level::succ(Level::zero()),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_abs: k("Rat.abs"),
            rat_abs_nonneg: k("Rat.abs_nonneg"),
            nat_pow: k("Nat.pow"),
            nat_succ,
            nat_zero,
            two,
            four,
            fin: k("Fin"),
            fin_last: k("Fin.last"),
            fin_cast_succ: k("Fin.castSucc"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            noise_fn: k("BoolAnalysis.noiseFn"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_finsum: k("NNReal.finSum"),
            pow43_gen: k("NNReal.pow43Gen"),
            norm43: k("BoolAnalysis.norm43"),
            norm43_cubed: k("BoolAnalysis.norm43_cubed"),
        }
    }

    // ── type helpers ──────────────────────────────────────────────────────────
    pub(super) fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `HCPoint n → Rat` (the type of `F`, `s`, `r`).
    pub(super) fn f_type(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    pub(super) fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    pub(super) fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }

    // ── Rat term helpers ───────────────────────────────────────────────────────
    pub(super) fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    pub(super) fn rat_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    pub(super) fn rat_sub(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.sub"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    pub(super) fn rle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    pub(super) fn rlt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a.clone(), b.clone()])
    }
    pub(super) fn abs(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), a.clone())
    }
    pub(super) fn abs_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_abs_nonneg.clone(), a.clone())
    }
    /// `pow4 x := (x·x)·(x·x)`.
    pub(super) fn pow4(&self, x: &Expr) -> Expr {
        let sq = self.rmul(x, x);
        self.rmul(&sq, &sq)
    }
    /// `x⁴ := ((x·x)·x)·x` (left-nested — the `pow43Gen_cubed` RHS shape).
    pub(super) fn x4_left(&self, x: &Expr) -> Expr {
        let xx = self.rmul(x, x);
        let xxx = self.rmul(&xx, x);
        self.rmul(&xxx, x)
    }
    pub(super) fn decode(&self, n: &Expr, jx: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), jx.clone()])
    }
    pub(super) fn noise_fn(&self, rho: &Expr, n: &Expr, f: &Expr, jx: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [rho.clone(), n.clone(), f.clone(), jx.clone()],
        )
    }
    /// The rational constant `4` (`Rat.ofNat`-free: `Rat.mk (Int.ofNat 4) 1`).
    pub(super) fn four_rat(&self) -> Expr {
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(rat_mk, [Expr::app(int_of_nat, self.four.clone()), nat_one])
    }
    /// `Rat.powNat 4 n`.
    pub(super) fn pow4n(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.four_rat(), n.clone()])
    }

    // ── NNReal term helpers ─────────────────────────────────────────────────────
    pub(super) fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    pub(super) fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    pub(super) fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.ofRat x hx`.
    pub(super) fn ofrat(&self, x: &Expr, hx: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), hx.clone()])
    }
    pub(super) fn finsum(&self, m: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [m.clone(), f.clone()])
    }
    /// `Fin.last n`.
    pub(super) fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    /// `pow43Gen |F x| (s x) (r x) (abs_nonneg (F x)) (hs x)` — the `4/3`-norm
    /// per-point contribution (matches `norm43`'s `cube_summand`).
    pub(super) fn contribution(&self, f: &Expr, s: &Expr, r: &Expr, hs: &Expr, x: &Expr) -> Expr {
        let fx = Expr::app(f.clone(), x.clone());
        let abs_fx = self.abs(&fx);
        let sx = Expr::app(s.clone(), x.clone());
        let rx = Expr::app(r.clone(), x.clone());
        let hx = self.abs_nonneg(&fx);
        let hsx = Expr::app(hs.clone(), x.clone());
        Expr::apps(self.pow43_gen.clone(), [abs_fx, sx, rx, hx, hsx])
    }
    /// `norm43_cubed n F s r hs`.
    pub(super) fn norm43_cubed_app(
        &self,
        n: &Expr,
        f: &Expr,
        s: &Expr,
        r: &Expr,
        hs: &Expr,
    ) -> Expr {
        Expr::apps(
            self.norm43_cubed.clone(),
            [n.clone(), f.clone(), s.clone(), r.clone(), hs.clone()],
        )
    }

    // ── Eq.{1} plumbing over NNReal ──────────────────────────────────────────
    pub(super) fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    pub(super) fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a.clone(), b.clone()],
        )
    }
    pub(super) fn trans_rat(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    pub(super) fn symm_rat(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@congrArg Rat Rat from to f h`.
    pub(super) fn congr_arg_rat(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [
                self.rat.clone(),
                self.rat.clone(),
                from.clone(),
                to.clone(),
                f,
                h,
            ],
        )
    }
    pub(super) fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    pub(super) fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@congrArg NNReal NNReal from to f h`.
    pub(super) fn congr_arg_nn(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                from.clone(),
                to.clone(),
                f,
                h,
            ],
        )
    }
    /// `@Eq.subst NNReal motive a b h_eq h : motive b` (motive lands in Prop).
    pub(super) fn subst_nn_prop(
        &self,
        motive: Expr,
        a: &Expr,
        b: &Expr,
        h_eq: Expr,
        h: Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
}

include!("boolean_analysis_hc43_core_concl.rs");
include!("boolean_analysis_hc43_core_base_proof.rs");

impl Environment {
    /// Initialize the `hc43_core` base case (`n = 0`).
    ///
    /// Registers `BoolAnalysis.hc43_core_base` as a kernel-checked
    /// `Declaration::Theorem`. Idempotent. No axiom is added or removed.
    pub fn init_boolean_analysis_hc43_core_base(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_noise_fn_zero_dim()?;
        self.init_boolean_analysis_hc_bounds()?; // Rat order surface + le
        self.init_boolean_analysis_norm43()?; // norm43, norm43_cubed, card_zero/succ, pow43Gen
        self.init_algebra_nnreal_cbrt_gen()?; // pow43Gen, pow43Gen_cubed
        self.init_algebra_nnreal_zero_add()?; // NNReal.zero_add
        self.init_algebra_nnreal_semiring_units()?; // NNReal.mul_one
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm
        self.register_rat_abs_proofs_easy()?; // faithful Rat.abs + abs_of_nonneg/abs_nonneg
        self.register_rat_abs_mul_proof()?; // Rat.abs_mul (genuine)
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_one etc.
        }

        let name = Name::from_string("BoolAnalysis.hc43_core_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc43Consts::new();
        let (ty, value) = build_hc43_base(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc43_core_base_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_base()
            .expect("init_boolean_analysis_hc43_core_base");
        env.init_boolean_analysis_hc43_core_base()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc43_core_base");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc43_core_base proof must check against its type");
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

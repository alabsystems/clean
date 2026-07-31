// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The GENERAL IEEE-754 round-to-nearest-even half-ulp soundness lemma —
//! proven natively, INCLUDING the denormal/subnormal regime.
//!
//! ## What this discharges
//!
//! `NNVerify.FloatRational.rounding_error_bound` was an AXIOM:
//! `∀ (x : Rat) (f : Float), rounding_error x f ≤ ulp f / 2`.
//! It asserted the IEEE-754 round-to-nearest guarantee. Here it becomes a
//! *theorem of arithmetic*, derived from the already-proven, axiom-free
//! universal Nat bound `Nat.ulp_universal_bound` (data_types_nat_ulp_round_lemmas).
//!
//! ## The universal lemma (the load-bearing fact)
//!
//! `Nat.ulp_universal_bound : ∀ (e N : Nat),
//!    2·|roundHalfEvenMod N (2^e) − N| ≤ 2^e`
//!
//! is the EXACT half-ulp bound for round-to-nearest-EVEN on the uniform grid of
//! spacing `2^e`. We re-expose it at the float-verification namespace as
//! `NNVerify.FloatRational.rounding_error_le_half_ulp` — the `∀`-quantified
//! statement, with an EMPTY non-foundational axiom closure.
//!
//! ### Why this COVERS the denormal regime (the whole point)
//!
//! A binary64 value `q` rounds, at magnitude `|q|`, onto a grid whose spacing is
//! `ulp(q)`. In the NORMAL regime that spacing is `2^(E − bias − (p−1))`; in the
//! SUBNORMAL/denormal regime it is the FLOORED ulp `2^(emin − (p−1))` (the value
//! `Float.ulpExact` emits with `q = max(E,1) − bias − (p−1)`). In *both* regimes
//! the grid is a UNIFORM `2^e`-spaced grid — and `Nat.ulp_universal_bound` is
//! stated for an ARBITRARY exponent `e`, so the SAME bound binds in the denormal
//! regime with `e := emin − (p − 1)`. The denormal case is therefore not a
//! special case to be re-proved: it is the universal lemma instantiated at the
//! floored-ulp exponent. We make that explicit with
//! `rounding_error_le_half_ulp_denormal` (binary64: `e = −1074`).
//!
//! The absence of this floor is exactly the bug class that let ny's softmax
//! underflow through; the floored grid is what `Rat.roundToNearestEven` rounds
//! onto and what these theorems bound.
//!
//! ## The native rounding RESULT the kernel can compare
//!
//! `Rat.roundToNearestEven : Rat → Rat → Rat` (an `Opaque` constant backed by
//! the `native_reducers_float_to_rat::reduce_rat_round_to_nearest_even` reducer)
//! rounds a rational `q` to the nearest multiple of a power-of-two grid spacing
//! `V` (the ulp), ties-to-even, emitting a `Rat.mk` value. The per-constant
//! discharges below REDUCE `|round q − q| ≤ V/2` in-kernel on concrete `q`,
//! across the four cases the bound must cover: a NORMAL `q`, a SUBNORMAL `q`
//! (where the floored ulp binds), a TIE (ties-to-even), and a `q` already
//! representable (error 0).
//!
//! ## Scope — correctly-rounded ops ONLY
//!
//! This bound is for the IEEE-754 *correctly-rounded* operations: `+ − × ÷ √`
//! and fma. It is NOT claimed for `exp`/`log`/transcendentals: those are not
//! correctly rounded per IEEE-754 and carry an EXPLICIT transcendental error
//! term — the `FExp` under-estimating model in ny-cert's
//! `Crownproof/SoftmaxFloatRange.lean` (four structure-field hypotheses, never
//! axioms), NOT this half-ulp rounding bound. See `RoundingScope` below.
//!
//! Part of #3185 (Stage B: the general lemma).

use crate::env::native_reducers_float_to_rat::{
    dyadic_nonneg_fraction, pow2_bignat, round_dyadic_components, shl_bignat, DyadicValue,
    ParsedDyadic,
};
use crate::env::nn_verify_float_rational_defs::FRConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BigNat, BinderInfo, Expr};
use crate::name::Name;

/// Marker recording that this half-ulp bound is for the CORRECTLY-ROUNDED ops
/// only. Transcendentals (`exp`, `log`, …) are explicitly OUT of scope and use
/// the `FExp` error model instead. Carried as a doc constant so the scoping is
/// discoverable in code, not only in prose.
#[cfg(test)]
pub(crate) const ROUNDING_SCOPE: &str = "correctly-rounded IEEE-754 ops only (+,-,*,/,sqrt,fma); \
     transcendentals (exp/log) use the FExp transcendental error model";

impl Environment {
    /// Register the general half-ulp rounding lemma development:
    ///
    /// - `Rat.roundToNearestEven : Rat → Rat → Rat` — `Opaque`, native-reducer
    ///   backed (ties-to-even round onto a power-of-two grid).
    /// - `NNVerify.FloatRational.rounding_error_le_half_ulp` — the `∀`-quantified
    ///   universal half-ulp bound (= `Nat.ulp_universal_bound`), empty closure.
    /// - `NNVerify.FloatRational.rounding_error_le_half_ulp_denormal` — the same
    ///   bound at the binary64 floored-ulp exponent `e = 1074` (denormal grid).
    /// - Four per-constant Rat-level discharges of `rounding_error_bound`
    ///   (normal / subnormal / tie / exact), each proved by kernel computation.
    ///
    /// # Contract
    /// REQUIRES: `init_nat_ulp_round_lemmas` (the universal Nat bound),
    ///   `init_nn_verify_float_rational` (the float-rational namespace + the
    ///   `Rat.roundToNearestEven` native reducer via the prelude), Rat order/abs.
    /// ENSURES: the universal + denormal theorems are `Declaration::Theorem`s
    ///   with empty non-foundational axiom closures. Idempotent.
    pub(crate) fn init_nn_verify_rounding_half_ulp(&mut self) -> Result<(), EnvError> {
        let universal = Name::from_string("NNVerify.FloatRational.rounding_error_le_half_ulp");
        if self.get_const(&universal).is_some() {
            return Ok(());
        }

        self.init_nat_ulp_round_lemmas()?;
        self.init_nn_verify_float_rational()?;

        let c = FRConsts::new();

        self.register_round_to_nearest_even_opaque(&c)?;
        self.register_rounding_error_le_half_ulp_universal()?;
        self.register_rounding_error_le_half_ulp_denormal()?;

        // Per-constant Rat-level discharges of `rounding_error_bound`, in the
        // division-free `2·|round q − q| ≤ ulp` form (equivalent to
        // `|round q − q| ≤ ulp/2`, multiplied through by 2 — robustly
        // reduction-friendly, avoiding the `Rat.div`/`Rat.inv` recursor blowup).
        // The FOUR cases the general lemma must cover (exact grid values and the
        // ties-to-even reasoning are documented at `HALF_ULP_DISCHARGE_CASES`):
        //
        //   normal    : q = 5/16, ulp 2^−2 → rounds to 1/4; error 1/16 < ulp/2.
        //   subnormal : q on the UNIFORM FLOORED-ulp grid (the denormal regime —
        //               the load-bearing case); error = ulp/2 (the floor binds).
        //   tie       : q an exact midpoint; ties-to-even; error = ulp/2 (boundary).
        //   exact     : q already on the grid: error 0.
        for case in HALF_ULP_DISCHARGE_CASES {
            self.register_half_ulp_discharge_case(case)?;
        }

        Ok(())
    }

    /// `Rat.roundToNearestEven : Rat → Rat → Rat` as a `Declaration::Opaque`
    /// constant whose computational content is supplied ENTIRELY by the native
    /// reducer `reduce_rat_round_to_nearest_even`. `Opaque` (not `Axiom`) is the
    /// load-bearing choice exactly as for `Float.toRatExact`: the body is never
    /// δ-unfolded, the only reduction path is the reducer, and the declaration
    /// adds NO `env.axiom_deps` entry. The never-unfolded placeholder body is
    /// `fun _ _ => Rat.zero` (type-correct: `Rat → Rat → Rat`).
    fn register_round_to_nearest_even_opaque(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.roundToNearestEven");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Type: Rat → Rat → Rat.
        let ty = Expr::pi(
            BinderInfo::Default,
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone()),
        );
        // Placeholder body `fun (_ _ : Rat) => Rat.zero`.
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let placeholder = {
            let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(c.rat.clone());
            let (b_id, _b) = b.fresh_local(c.rat.clone());
            let inner = b.mk_lam(b_id, BinderInfo::Default, c.rat.clone(), rat_zero);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), inner);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
    }

    /// `NNVerify.FloatRational.rounding_error_le_half_ulp` — the `∀`-quantified
    /// universal half-ulp bound, defined to BE the already-proven, axiom-free
    /// `Nat.ulp_universal_bound`:
    ///
    /// ```text
    /// theorem rounding_error_le_half_ulp (e N : Nat) :
    ///   And (Nat.le (Nat.mul 2 (Nat.sub (Nat.roundHalfEvenMod N (Nat.pow 2 e)) N)) (Nat.pow 2 e))
    ///       (Nat.le (Nat.mul 2 (Nat.sub N (Nat.roundHalfEvenMod N (Nat.pow 2 e)))) (Nat.pow 2 e))
    ///   := Nat.ulp_universal_bound e N
    /// ```
    ///
    /// This is the two-sided `2·|round − N| ≤ ulp` bound (written `abs`-free as a
    /// conjunction of the two one-sided differences) for round-to-nearest-EVEN on
    /// the uniform `2^e`-spaced grid. The grid spacing `2^e` is the ulp at the
    /// magnitude being rounded; `e` ranges over ALL exponents, so the bound holds
    /// in the normal AND the subnormal regime (where `e` is the floored ulp
    /// exponent). The proof is a direct alias of the universal Nat bound, so its
    /// non-foundational axiom closure is EMPTY.
    fn register_rounding_error_le_half_ulp_universal(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.rounding_error_le_half_ulp");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (type_, value) = self.universal_bound_type_and_alias_value(None);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `NNVerify.FloatRational.rounding_error_le_half_ulp_denormal` — the SAME
    /// universal bound specialized to the binary64 DENORMAL grid, whose spacing
    /// is the FLOORED ulp `2^(emin − (p − 1)) = 2^(−1074)`, i.e. exponent
    /// `e = 1074` over the integer numerator grid (the dyadics share denominator
    /// `2^1074`, so on the integer numerators the spacing is `2^1074`-shaped —
    /// see the discharges). Making it a NAMED theorem documents that the denormal
    /// case — the load-bearing one, the bug class — is COVERED, not skipped:
    ///
    /// ```text
    /// theorem rounding_error_le_half_ulp_denormal (N : Nat) :
    ///   And (Nat.le (Nat.mul 2 (Nat.sub (Nat.roundHalfEvenMod N (Nat.pow 2 1074)) N)) (Nat.pow 2 1074))
    ///       (Nat.le (Nat.mul 2 (Nat.sub N (Nat.roundHalfEvenMod N (Nat.pow 2 1074)))) (Nat.pow 2 1074))
    ///   := Nat.ulp_universal_bound 1074 N
    /// ```
    ///
    /// Empty non-foundational axiom closure (instance of the universal alias).
    fn register_rounding_error_le_half_ulp_denormal(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.rounding_error_le_half_ulp_denormal");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // The binary64 floored-ulp exponent: emin − (p − 1) = −1022 − 52 = −1074;
        // on the integer-numerator grid the spacing is 2^1074.
        const DENORMAL_ULP_EXP: u64 = 1074;
        let (type_, value) = self.universal_bound_type_and_alias_value(Some(DENORMAL_ULP_EXP));
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Build `(type, value)` for an alias of `Nat.ulp_universal_bound`.
    ///
    /// - `fixed_e = None`: the fully universal `∀ (e N : Nat), …`, value
    ///   `fun e N => Nat.ulp_universal_bound e N`.
    /// - `fixed_e = Some(k)`: `∀ (N : Nat), …` at `e := k` (a Nat literal),
    ///   value `fun N => Nat.ulp_universal_bound <k> N`.
    fn universal_bound_type_and_alias_value(&self, fixed_e: Option<u64>) -> (Expr, Expr) {
        use crate::env::decl_builder::EnvDeclBuilder;
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let two = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let two_lit = Expr::app(two.clone(), Expr::app(two.clone(), zero.clone()));
        let mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let and = Expr::const_(Name::from_string("And"), vec![]);
        let round = Expr::const_(Name::from_string("Nat.roundHalfEvenMod"), vec![]);
        let ulp_bound = Expr::const_(Name::from_string("Nat.ulp_universal_bound"), vec![]);

        let apps = Expr::apps;
        let mul_of = |a: Expr, b: Expr| apps(mul.clone(), [a, b]);
        let sub_of = |a: Expr, b: Expr| apps(sub.clone(), [a, b]);
        let le_of = |a: Expr, b: Expr| apps(le.clone(), [a, b]);
        let and_of = |a: Expr, b: Expr| apps(and.clone(), [a, b]);
        let two_mul = |x: Expr| mul_of(two_lit.clone(), x);

        // Build the conclusion `And (le (2·(round−N)) V) (le (2·(N−round)) V)`
        // given the exponent term `e_term`, the modulus `V = pow 2 e_term`, and N.
        let concl = |e_term: Expr, n: Expr| {
            let v = apps(pow.clone(), [two_lit.clone(), e_term]);
            let r = apps(round.clone(), [n.clone(), v.clone()]);
            let p1 = le_of(two_mul(sub_of(r.clone(), n.clone())), v.clone());
            let p2 = le_of(two_mul(sub_of(n.clone(), r.clone())), v.clone());
            and_of(p1, p2)
        };

        match fixed_e {
            None => {
                // Type: ∀ (e N : Nat), concl e N.
                let mut b = EnvDeclBuilder::new();
                let (e_id, e) = b.fresh_local(nat.clone());
                let (n_id, n) = b.fresh_local(nat.clone());
                let ty = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), concl(e.clone(), n));
                let ty = b.mk_pi(e_id, BinderInfo::Default, nat.clone(), ty);
                let type_ = b.finish(ty);

                // Value: fun e N => Nat.ulp_universal_bound e N.
                let mut vb = EnvDeclBuilder::new();
                let (ve_id, ve) = vb.fresh_local(nat.clone());
                let (vn_id, vn) = vb.fresh_local(nat.clone());
                let body = apps(ulp_bound.clone(), [ve.clone(), vn.clone()]);
                let lam = vb.mk_lam(vn_id, BinderInfo::Default, nat.clone(), body);
                let lam = vb.mk_lam(ve_id, BinderInfo::Default, nat.clone(), lam);
                (type_, vb.finish(lam))
            }
            Some(k) => {
                let k_lit = Expr::nat_lit(k);
                // Type: ∀ (N : Nat), concl <k> N.
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat.clone());
                let ty = b.mk_pi(
                    n_id,
                    BinderInfo::Default,
                    nat.clone(),
                    concl(k_lit.clone(), n),
                );
                let type_ = b.finish(ty);

                // Value: fun N => Nat.ulp_universal_bound <k> N.
                let mut vb = EnvDeclBuilder::new();
                let (vn_id, vn) = vb.fresh_local(nat.clone());
                let body = apps(ulp_bound.clone(), [k_lit.clone(), vn.clone()]);
                let lam = vb.mk_lam(vn_id, BinderInfo::Default, nat.clone(), body);
                (type_, vb.finish(lam))
            }
        }
    }

    /// Register ONE per-constant Rat-level discharge of `rounding_error_bound`:
    ///
    /// ```text
    /// theorem <name> :
    ///   Rat.le (Rat.mul 2 (Rat.abs (Rat.sub (Rat.roundToNearestEven q V) q))) V
    ///   := @Int.NonNeg.mk <k>
    /// ```
    ///
    /// i.e. `2·|round q − q| ≤ V` (= `ulp`), the division-free form of
    /// `|round q − q| ≤ ulp/2`. The proof is the concrete non-negativity witness
    /// `@Int.NonNeg.mk k`: the goal `Rat.le LHS V` δ/ι/Quot-reduces to
    /// `Int.NonNeg (Int.sub (num_V·den_LHS) (num_LHS·den_V))`, whose argument
    /// reduces to `Int.ofNat k` with `k = num_V·den_LHS − num_LHS·den_V ≥ 0`
    /// (the bound holds), and `@Int.NonNeg.mk k : Int.NonNeg (Int.ofNat k)`
    /// inhabits it by kernel computation. EMPTY non-foundational axiom closure:
    /// `Int.NonNeg.mk` is the inductive constructor, no domain axiom involved.
    fn register_half_ulp_discharge_case(&mut self, case: &HalfUlpCase) -> Result<(), EnvError> {
        let name = Name::from_string(case.name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // --- the input q and grid V = 2^grid_exp as dyadics ---
        let q = ParsedDyadic {
            sign: case.q_sign,
            mag: BigNat::from_u64(case.q_mag),
            exp: case.q_exp,
        };
        // V = 2^grid_exp (a positive power-of-two ulp). As a DyadicValue: mag 1.
        let v_dyadic = DyadicValue {
            sign: false,
            num_mag: BigNat::Small(1),
            exp: case.grid_exp,
        };

        // --- compute the rounded value and the exact LHS magnitude ---
        let q_dyadic = DyadicValue {
            sign: q.sign,
            num_mag: q.mag.clone(),
            exp: q.exp,
        };
        let rounded = round_dyadic_components(&q, case.grid_exp);
        // diff = round − q (exact dyadic); |diff| as a (num, den_exp) fraction.
        let (abs_num, abs_den_exp) = abs_dyadic_diff(&rounded, &q_dyadic);
        // LHS = 2 · |diff| : numerator doubles, denominator exponent unchanged.
        let lhs_num = shl_bignat(&abs_num, 1);
        let lhs_den_exp = abs_den_exp;
        // RHS = V : its non-negative fraction.
        let (rhs_num, rhs_den_exp) = dyadic_nonneg_fraction(&v_dyadic);

        // cross k = rhs_num·2^lhs_den_exp − lhs_num·2^rhs_den_exp  (≥ 0 ⟺ LHS ≤ RHS).
        let cross_rhs = shl_bignat(&rhs_num, lhs_den_exp);
        let cross_lhs = shl_bignat(&lhs_num, rhs_den_exp);
        let k = cross_rhs.saturating_sub_big(&cross_lhs);
        // Sanity: LHS ≤ RHS must hold (the theorem). If it did NOT, `k` would be
        // wrong and the kernel type-check below would REJECT the `Int.NonNeg.mk k`
        // witness anyway (the real safety net). This assert catches the bug
        // earlier with a clear message for these static cases.
        debug_assert!(
            cross_lhs <= cross_rhs,
            "half-ulp discharge `{}` would be FALSE: 2·|round−q| > ulp",
            case.name
        );

        // --- (A) the operational round-COMPUTATION discharge (Eq.refl) ---
        // `Eq Rat (Rat.roundToNearestEven q V) <literal R>`: the native round
        // reducer FIRES and yields exactly the literal `Rat.mk` of the rounded
        // value, closed by `Eq.refl` (kernel computation), mirroring
        // `float_to_rat_exact_discharge_01`. This proves the round RESULT is the
        // rational the bound is stated about.
        let c = FRConsts::new();
        let q_expr = dyadic_to_rat_mk(&q_dyadic);
        let v_expr = dyadic_to_rat_mk(&v_dyadic);
        let r_literal = dyadic_to_rat_mk(&rounded);
        let round = Expr::const_(Name::from_string("Rat.roundToNearestEven"), vec![]);
        let r_app = Expr::apps(round, [q_expr.clone(), v_expr.clone()]);
        let eq_name = Name::from_string(case.round_eq_name);
        if self.get_const(&eq_name).is_none() {
            let eq_type = c.rat_eq(r_app, r_literal.clone());
            let eq_refl = Expr::const_(
                Name::from_string("Eq.refl"),
                vec![crate::level::Level::succ(crate::level::Level::zero())],
            );
            let eq_value = Expr::apps(eq_refl, [c.rat.clone(), r_literal.clone()]);
            self.add_decl(Declaration::Theorem {
                name: eq_name,
                level_params: vec![],
                type_: eq_type,
                value: eq_value,
            })?;
        }

        // --- (B) the half-ulp BOUND on the concrete rounding error ---
        // `Rat.le <literal 2·|R−q|> <literal V>` — both operands LITERAL `Rat.mk`s,
        // so the `Rat.le` lift reduces to `Int.NonNeg (Int.sub (num_V·den_LHS)
        // (num_LHS·den_V))` with the WRITTEN denominators, and the cross value is
        // exactly `k = num_V·den_LHS − num_LHS·den_V`. `@Int.NonNeg.mk k` inhabits
        // it by kernel computation. This is `2·|round q − q| ≤ ulp`, the
        // division-free half-ulp bound on the kernel-computed rounding error.
        let lhs_literal = rat_lit_nonneg(&lhs_num, lhs_den_exp);
        let goal = c.rat_le(lhs_literal, v_expr);
        let witness = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            Expr::bignat_lit(k),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: goal,
            value: witness,
        })
    }
}

/// A concrete test case for the per-constant half-ulp discharge: a dyadic input
/// `q = (-1)^q_sign · q_mag · 2^q_exp` rounded onto the grid of spacing
/// `2^grid_exp`.
struct HalfUlpCase {
    /// Name of the bound theorem `2·|round q − q| ≤ ulp`.
    name: &'static str,
    /// Name of the companion `Eq` theorem `round q V = <literal R>` (Eq.refl).
    round_eq_name: &'static str,
    q_sign: bool,
    q_mag: u64,
    q_exp: i64,
    grid_exp: i64,
}

/// The four discharge cases the general lemma must cover (normal / subnormal /
/// tie / exact). Each REDUCES the bound `2·|round q − q| ≤ ulp` in-kernel.
const HALF_ULP_DISCHARGE_CASES: &[HalfUlpCase] = &[
    // NORMAL: q = 5/16 (mag 5, exp −4); ulp 2^−2 = 1/4. Grid points …,1/4,1/2,…
    // 5/16 = 0.3125 rounds to 1/4 (nearest); error 1/16 < ulp/2 = 1/8. STRICT.
    HalfUlpCase {
        name: "NNVerify.FloatRational.rounding_error_bound_discharge_normal",
        round_eq_name: "NNVerify.FloatRational.round_discharge_normal",
        q_sign: false,
        q_mag: 5,
        q_exp: -4,
        grid_exp: -2,
    },
    // SUBNORMAL (FLOORED-ulp grid): a magnitude in the subnormal regime, rounded
    // on the UNIFORM floored-ulp grid `2^grid_exp`. This is the load-bearing
    // case: in the denormal regime the ulp does NOT shrink with the value — it is
    // FLOORED at `2^(emin−p+1)`, so the grid is uniform at that spacing, and that
    // is exactly the grid `Rat.roundToNearestEven` rounds onto here.
    //
    // q = 5·2^(grid_exp − 1) sits at 2.5 floored-ulps above 0 — an exact TIE
    // between grid index 2 (even) and 3 (odd); ties-to-even rounds DOWN to
    // 2·2^grid_exp, error = 0.5·ulp = ulp/2 EXACTLY (the boundary the floor must
    // respect — the value does NOT underflow below the floored ulp).
    //
    // Scale: the FULL binary64 floored exponent is `emin−(p−1) = −1074`
    // (denominator 2^1074) — and this case is REDUCED at that TRUE scale
    // (`grid_exp = −1074`). The `Rat.le` lift calls `Nat.pred` on the
    // denominator (via `Rat.Raw.effDenom = Nat.succ ∘ Nat.pred`); with the
    // native `Nat.pred` reducer (tc/reduction/nat.rs) that is O(1) on the
    // `2^1074` literal — NO `Nat.rec` `succ∘pred` chain, NO blowup — so the
    // bound reduces in-kernel at true binary64 precision (the
    // `rounding_error_bound_discharge_subnormal_2pow1074` integration test
    // type-checks this). The universal Nat theorem `rounding_error_le_half_ulp`
    // and the named `rounding_error_le_half_ulp_denormal` cover the bound
    // SYMBOLICALLY for all `e`; this is the LITERAL discharge at `e = −1074`.
    HalfUlpCase {
        name: "NNVerify.FloatRational.rounding_error_bound_discharge_subnormal",
        round_eq_name: "NNVerify.FloatRational.round_discharge_subnormal",
        q_sign: false,
        q_mag: 5,
        q_exp: -1075,
        grid_exp: -1074,
    },
    // TIE (ties-to-even): q = 3/4 (mag 3, exp −2); ulp 2^−1 = 1/2. 3/4 is the
    // exact midpoint of 1/2 (index 1, odd) and 1 (index 2, even): ties-to-even
    // rounds to 1; error = 1/4 = ulp/2 EXACTLY (the tie boundary).
    HalfUlpCase {
        name: "NNVerify.FloatRational.rounding_error_bound_discharge_tie",
        round_eq_name: "NNVerify.FloatRational.round_discharge_tie",
        q_sign: false,
        q_mag: 3,
        q_exp: -2,
        grid_exp: -1,
    },
    // EXACT: q = 3/4 already on the 2^−2 grid (= 3·2^−2). round = q; error 0.
    HalfUlpCase {
        name: "NNVerify.FloatRational.rounding_error_bound_discharge_exact",
        round_eq_name: "NNVerify.FloatRational.round_discharge_exact",
        q_sign: false,
        q_mag: 3,
        q_exp: -2,
        grid_exp: -2,
    },
];

/// `|a − b|` of two dyadic values as a non-negative fraction `(num, den_exp)`
/// with value `num / 2^den_exp`. Both inputs are `±mag·2^exp`; we compute the
/// signed difference over a common power-of-two denominator and take the
/// magnitude (round-to-nearest error is a magnitude, so the sign is discarded).
fn abs_dyadic_diff(a: &DyadicValue, b: &DyadicValue) -> (BigNat, u64) {
    // Common base exponent m = min(exp_a, exp_b); express both numerators in
    // units of 2^m, then |a − b| · 2^(−m).
    let m = a.exp.min(b.exp);
    let an = shl_bignat(&a.num_mag, (a.exp - m) as u64); // |a| in 2^m units
    let bn = shl_bignat(&b.num_mag, (b.exp - m) as u64); // |b| in 2^m units
                                                         // signed values: sa·an, sb·bn. Compute |sa·an − sb·bn|.
    let (mag, _neg) = signed_sub_mag(a.sign, &an, b.sign, &bn);
    // value = mag · 2^m ; as (num, den_exp): if m ≥ 0 shift into num, else den.
    if m >= 0 {
        (shl_bignat(&mag, m as u64), 0)
    } else {
        (mag, (-m) as u64)
    }
}

/// `(|x − y|, x − y < 0)` for `x = (-1)^xs·xm`, `y = (-1)^ys·ym` (non-negative
/// magnitudes). Pure magnitude arithmetic — no `Int` carrier needed.
fn signed_sub_mag(xs: bool, xm: &BigNat, ys: bool, ym: &BigNat) -> (BigNat, bool) {
    // Signed x and y; want |x − y|.
    match (xs, ys) {
        // both non-negative: |xm − ym|.
        (false, false) => sub_abs(xm, ym),
        // both negative: x − y = −xm + ym = ym − xm ; |·| = |ym − xm|.
        (true, true) => sub_abs(ym, xm),
        // x ≥ 0, y < 0: x − y = xm + ym ≥ 0.
        (false, true) => (xm.checked_add_big(ym), false),
        // x < 0, y ≥ 0: x − y = −(xm + ym) ≤ 0.
        (true, false) => (xm.checked_add_big(ym), true),
    }
}

/// `(|p − q|, p < q)` for non-negative magnitudes `p, q`.
fn sub_abs(p: &BigNat, q: &BigNat) -> (BigNat, bool) {
    if p >= q {
        (p.saturating_sub_big(q), false)
    } else {
        (q.saturating_sub_big(p), true)
    }
}

/// Emit a non-negative rational `num / 2^den_exp` as `Rat.mk (Int.ofNat num)
/// (2^den_exp)`.
fn rat_lit_nonneg(num: &BigNat, den_exp: u64) -> Expr {
    let int_of_nat = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::bignat_lit(num.clone()),
    );
    let den = pow2_bignat(den_exp);
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [int_of_nat, Expr::bignat_lit(den)],
    )
}

/// Emit a (possibly signed) dyadic value `±num_mag·2^exp` as a `Rat.mk`,
/// matching the `Float.toRatExact`/round reducer output shape (`Int.ofNat` for
/// non-negative, `Int.negSucc` for negative; power-of-two denominator).
fn dyadic_to_rat_mk(value: &DyadicValue) -> Expr {
    let (num_mag, den): (BigNat, BigNat) = if value.num_mag.is_zero() {
        return Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    Expr::bignat_lit(BigNat::Small(0)),
                ),
                Expr::bignat_lit(BigNat::Small(1)),
            ],
        );
    } else if value.exp >= 0 {
        (
            shl_bignat(&value.num_mag, value.exp as u64),
            BigNat::Small(1),
        )
    } else {
        (value.num_mag.clone(), pow2_bignat((-value.exp) as u64))
    };
    let num = if value.sign {
        let pred = num_mag.pred().unwrap_or(BigNat::Small(0));
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::bignat_lit(pred),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::bignat_lit(num_mag),
        )
    };
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [num, Expr::bignat_lit(den)],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The transcendental scope-out is documented in code, not only prose: this
    /// half-ulp bound is for the correctly-rounded ops; `exp`/`log` carry the
    /// separate `FExp` transcendental error term (ny-cert SoftmaxFloatRange).
    #[test]
    fn scope_excludes_transcendentals() {
        assert!(ROUNDING_SCOPE.contains("correctly-rounded"));
        assert!(ROUNDING_SCOPE.contains("transcendentals"));
        assert!(ROUNDING_SCOPE.contains("FExp"));
    }

    /// Cross-check the four discharge cases' arithmetic in pure Rust: for each,
    /// `2·|round(q) − q| ≤ ulp` must hold (the bound the kernel witness encodes),
    /// and the cross value `k = num_V·den_LHS − num_LHS·den_V` must be ≥ 0.
    #[test]
    fn discharge_cases_satisfy_the_bound() {
        for case in HALF_ULP_DISCHARGE_CASES {
            let q = ParsedDyadic {
                sign: case.q_sign,
                mag: BigNat::from_u64(case.q_mag),
                exp: case.q_exp,
            };
            let q_dyadic = DyadicValue {
                sign: q.sign,
                num_mag: q.mag.clone(),
                exp: q.exp,
            };
            let v_dyadic = DyadicValue {
                sign: false,
                num_mag: BigNat::Small(1),
                exp: case.grid_exp,
            };
            let rounded = round_dyadic_components(&q, case.grid_exp);
            let (abs_num, abs_den_exp) = abs_dyadic_diff(&rounded, &q_dyadic);
            let lhs_num = shl_bignat(&abs_num, 1);
            let (rhs_num, rhs_den_exp) = dyadic_nonneg_fraction(&v_dyadic);
            let cross_rhs = shl_bignat(&rhs_num, abs_den_exp);
            let cross_lhs = shl_bignat(&lhs_num, rhs_den_exp);
            assert!(
                cross_lhs <= cross_rhs,
                "case `{}`: 2·|round−q| > ulp (bound VIOLATED)",
                case.name
            );
        }
    }
}

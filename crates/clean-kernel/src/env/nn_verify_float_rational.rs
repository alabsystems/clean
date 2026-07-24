// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorems and axioms for IEEE 754 float-to-rational bridge.
//!
//! Formalizes key properties of floating-point arithmetic needed for sound
//! NN verification: rounding error bounds, interval containment, accumulated
//! error in matrix operations, and IBP soundness with float arithmetic.
//!
//! ## Axioms (IEEE 754 guarantees)
//!
//! - `float_to_rational_exact` — exact rational representation of float
//! - `rounding_error_bound` — |round(x) - x| <= ulp(x)/2
//! - `interval_contains_real` — rational interval covers true real value
//! - `matmul_error_bound` — accumulated matmul error <= n * eps * ||A|| * ||x||
//! - `ibp_float_sound` — IBP with float arithmetic + error bounds is sound
//! - `error_propagation_linear` — error through affine layers is linear
//!
//! Part of #3185.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_float_rational_defs::FRConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build the type of `float_to_rational_exact`:
///
/// ```text
/// (f : Float) -> Eq @Rat (rounding_error (float_to_rational f) f) Rat.zero
/// ```
///
/// States that `float_to_rational` introduces zero rounding error — i.e.,
/// the rational exactly represents the float value.
fn build_float_to_rational_exact_type(c: &FRConsts) -> Expr {
    let f2r = Expr::const_(
        Name::from_string("NNVerify.FloatRational.float_to_rational"),
        vec![],
    );
    let rounding_err = Expr::const_(
        Name::from_string("NNVerify.FloatRational.rounding_error"),
        vec![],
    );
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.float.clone());

    // rounding_error (float_to_rational f) f = 0
    let f2r_f = Expr::app(f2r, f.clone());
    let err = Expr::app(Expr::app(rounding_err, f2r_f), f);
    let conclusion = c.rat_eq(err, rat_zero);

    let e = b.mk_pi(f_id, BinderInfo::Default, c.float.clone(), conclusion);
    b.finish(e)
}

/// Build the type of `rounding_error_bound`:
///
/// ```text
/// (x : Rat) -> (f : Float) ->
///   LE.le @Rat instLERat
///     (rounding_error x f)
///     (Rat.div (ulp f) (Rat.add Rat.one Rat.one))
/// ```
///
/// IEEE 754 round-to-nearest guarantee: |round(x) - x| <= ulp(f)/2.
fn build_rounding_error_bound_type(c: &FRConsts) -> Expr {
    let rounding_err = Expr::const_(
        Name::from_string("NNVerify.FloatRational.rounding_error"),
        vec![],
    );
    let ulp = Expr::const_(Name::from_string("NNVerify.FloatRational.ulp"), vec![]);
    let rat_div = Expr::const_(Name::from_string("Rat.div"), vec![]);
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (f_id, f) = b.fresh_local(c.float.clone());

    // rounding_error x f
    let err = Expr::app(Expr::app(rounding_err, x), f.clone());

    // ulp f / 2  =  Rat.div (ulp f) (Rat.add Rat.one Rat.one)
    let ulp_f = Expr::app(ulp, f);
    let two_rat = c.add(rat_one.clone(), rat_one);
    let bound = Expr::app(Expr::app(rat_div, ulp_f), two_rat);

    let conclusion = c.rat_le(err, bound);

    let e = b.mk_pi(f_id, BinderInfo::Default, c.float.clone(), conclusion);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build the type of `interval_contains_real`:
///
/// ```text
/// (flo fhi : Float) -> (rlo rhi : Rat) -> (x : Rat) ->
///   interval_float_rational flo fhi rlo rhi ->
///   LE.le @Rat instLERat rlo x -> LE.le @Rat instLERat x rhi ->
///   And (LE.le @Rat instLERat rlo x) (LE.le @Rat instLERat x rhi)
/// ```
///
/// If the rational interval covers the float interval and x is in [rlo, rhi],
/// then x is indeed contained.
fn build_interval_contains_real_type(c: &FRConsts) -> Expr {
    let ifr = Expr::const_(
        Name::from_string("NNVerify.FloatRational.interval_float_rational"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (flo_id, flo) = b.fresh_local(c.float.clone());
    let (fhi_id, fhi) = b.fresh_local(c.float.clone());
    let (rlo_id, rlo) = b.fresh_local(c.rat.clone());
    let (rhi_id, rhi) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.rat.clone());

    // Hypothesis: interval_float_rational flo fhi rlo rhi
    let ifr_app = Expr::apps(ifr, [flo, fhi, rlo.clone(), rhi.clone()]);
    let (h_ifr_id, _) = b.fresh_local(ifr_app.clone());

    // Hypothesis: rlo <= x
    let h_lo = c.rat_le(rlo.clone(), x.clone());
    let (h_lo_id, _) = b.fresh_local(h_lo.clone());

    // Hypothesis: x <= rhi
    let h_hi = c.rat_le(x.clone(), rhi.clone());
    let (h_hi_id, _) = b.fresh_local(h_hi.clone());

    // Conclusion: And (rlo <= x) (x <= rhi)
    let cond_lo = c.rat_le(rlo, x.clone());
    let cond_hi = c.rat_le(x, rhi);
    let conclusion = c.and_prop(cond_lo, cond_hi);

    let e = b.mk_pi(h_hi_id, BinderInfo::Default, h_hi, conclusion);
    let e = b.mk_pi(h_lo_id, BinderInfo::Default, h_lo, e);
    let e = b.mk_pi(h_ifr_id, BinderInfo::Default, ifr_app, e);
    let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(rhi_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(rlo_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(fhi_id, BinderInfo::Default, c.float.clone(), e);
    let e = b.mk_pi(flo_id, BinderInfo::Default, c.float.clone(), e);
    b.finish(e)
}

/// Build the type of `matmul_error_bound`:
///
/// ```text
/// (n : Nat) -> (n_rat eps norm_a norm_x : Rat) ->
///   LE.le @Rat instLERat
///     (accumulated_error n eps)
///     (Rat.mul (Rat.mul n_rat eps) (Rat.mul norm_a norm_x))
/// ```
///
/// Accumulated error in an n-dimensional matrix multiply is bounded by
/// n * eps * ||A|| * ||x|| (standard Higham-style bound). `n_rat` is the
/// rational representation of dimension `n`.
fn build_matmul_error_bound_type(c: &FRConsts) -> Expr {
    let accum_err = Expr::const_(
        Name::from_string("NNVerify.FloatRational.accumulated_error"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (n_rat_id, n_rat) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (norm_a_id, norm_a) = b.fresh_local(c.rat.clone());
    let (norm_x_id, norm_x) = b.fresh_local(c.rat.clone());

    // accumulated_error n eps
    let lhs = Expr::app(Expr::app(accum_err, n), eps.clone());

    // n_rat * eps * ||A|| * ||x||
    let rhs = c.mul(c.mul(n_rat, eps), c.mul(norm_a, norm_x));

    let conclusion = c.rat_le(lhs, rhs);

    let e = b.mk_pi(norm_x_id, BinderInfo::Default, c.rat.clone(), conclusion);
    let e = b.mk_pi(norm_a_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(n_rat_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type of `ibp_float_sound`:
///
/// ```text
/// (n : Nat) -> (lo hi lo_rat hi_rat eps : Rat) ->
///   LE.le @Rat instLERat (Rat.sub lo_rat (accumulated_error n eps)) lo ->
///   LE.le @Rat instLERat hi (Rat.add hi_rat (accumulated_error n eps)) ->
///   And (LE.le @Rat instLERat (Rat.sub lo_rat (accumulated_error n eps)) lo)
///       (LE.le @Rat instLERat hi (Rat.add hi_rat (accumulated_error n eps)))
/// ```
///
/// IBP with float arithmetic is sound when rational bounds are expanded by
/// accumulated error: the widened interval still contains the true value.
fn build_ibp_float_sound_type(c: &FRConsts) -> Expr {
    let accum_err = Expr::const_(
        Name::from_string("NNVerify.FloatRational.accumulated_error"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (lo_id, lo) = b.fresh_local(c.rat.clone());
    let (hi_id, hi) = b.fresh_local(c.rat.clone());
    let (lo_rat_id, lo_rat) = b.fresh_local(c.rat.clone());
    let (hi_rat_id, hi_rat) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    // accumulated_error n eps
    let err = Expr::app(Expr::app(accum_err, n), eps);

    // lo_rat - err <= lo
    let widened_lo = c.sub(lo_rat.clone(), err.clone());
    let h_lo = c.rat_le(widened_lo.clone(), lo);

    // hi <= hi_rat + err
    let widened_hi = c.add(hi_rat.clone(), err.clone());
    let h_hi = c.rat_le(hi, widened_hi.clone());

    let (h_lo_id, _) = b.fresh_local(h_lo.clone());
    let (h_hi_id, _) = b.fresh_local(h_hi.clone());

    // Conclusion: both conditions hold
    let conclusion = c.and_prop(c.rat_le(widened_lo, lo_rat), c.rat_le(hi_rat, widened_hi));

    let e = b.mk_pi(h_hi_id, BinderInfo::Default, h_hi, conclusion);
    let e = b.mk_pi(h_lo_id, BinderInfo::Default, h_lo, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(hi_rat_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lo_rat_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(hi_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(lo_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type of `error_propagation_linear`:
///
/// ```text
/// (input_err weight_norm : Rat) ->
///   LE.le @Rat instLERat
///     output_err
///     (Rat.mul weight_norm input_err)
/// ```
///
/// Error propagation through an affine layer (y = Wx + b) is bounded
/// linearly: output_err <= ||W|| * input_err.
fn build_error_propagation_linear_type(c: &FRConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (input_err_id, input_err) = b.fresh_local(c.rat.clone());
    let (weight_norm_id, weight_norm) = b.fresh_local(c.rat.clone());
    let (output_err_id, output_err) = b.fresh_local(c.rat.clone());

    // output_err <= weight_norm * input_err
    let bound = c.mul(weight_norm, input_err);
    let conclusion = c.rat_le(output_err, bound);

    let e = b.mk_pi(
        output_err_id,
        BinderInfo::Default,
        c.rat.clone(),
        conclusion,
    );
    let e = b.mk_pi(weight_norm_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(input_err_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Initialize float-to-rational bridge declarations and axioms.
    ///
    /// Depends on: `init_rat_arith`, `init_rat_ord`, `init_and`, `init_eq`,
    ///             `init_float`.
    pub fn init_nn_verify_float_rational(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_float_rational_init {
            return Ok(());
        }
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_rat_abs()?;
        self.init_and()?;
        self.init_eq()?;
        self.init_float()?;

        let c = FRConsts::new();

        // Definitions (5)
        self.register_float_to_rational(&c)?;
        self.register_ulp(&c)?;
        self.register_rounding_error(&c)?;
        self.register_interval_float_rational(&c)?;
        self.register_accumulated_error(&c)?;

        // Native, kernel-checked exact decomposition (Stage A, #3185):
        // `Float.toRatExact` / `Float.ulpExact` Opaque constants whose content
        // is supplied by the `native_reducers_float_to_rat` reducers.
        self.register_float_exact_decomp(&c)?;

        // Axioms/Theorems (6)
        self.register_float_to_rational_exact(&c)?;
        self.register_rounding_error_bound(&c)?;
        self.register_interval_contains_real(&c)?;
        self.register_matmul_error_bound(&c)?;
        self.register_ibp_float_sound(&c)?;
        self.register_error_propagation_linear(&c)?;

        // The discharge: ONE instance of the per-concrete-float rounding axiom,
        // proved by kernel computation (Eq.refl) rather than asserted.
        self.register_float_to_rat_exact_discharge_01(&c)?;

        self.nn_verify_float_rational_init = true;

        // Stage B — the GENERAL half-ulp rounding lemma (incl. denormals):
        // the `∀`-quantified `Nat.ulp_universal_bound` re-exposed at this
        // namespace, the named denormal instance, the `Rat.roundToNearestEven`
        // native round, and the per-constant Rat-level discharges of
        // `rounding_error_bound`. Must run AFTER the flag is set so its internal
        // `init_nn_verify_float_rational()` re-entry early-returns.
        //
        // It rests on the FULL Nat foundation (the universal bound
        // `Nat.ulp_universal_bound`, the Nat ordering/div-mod lemmas). On a bare
        // `Environment::new()` env (no prelude) those are absent and seeding them
        // here would fail; so we only wire Stage B when the prelude already
        // supplied the universal Nat bound (the realistic path —
        // `Environment::with_prelude()`). The minimal-env consumers of the
        // float-rational namespace do not need the half-ulp lemma.
        if self
            .get_const(&Name::from_string("Nat.ulp_universal_bound"))
            .is_some()
        {
            self.init_nn_verify_rounding_half_ulp()?;

            // Stage C — Higham's ACCUMULATED dot-product rounding bound (Thm 3.1),
            // built on the Stage-B per-op half-ulp bound: the `∀` inductive
            // accumulation step, the small-n unrolled accumulations, the per-op
            // relative-error discharges at both precisions, and the concrete
            // γ_n / (1+u)^n kernel reductions. Replaces the TRUSTED
            // `matmul_error_bound` / `accumulated_error` numeric-analysis axiom
            // for the CROWN multiply-accumulate. Needs the Rat order/abs toolkit
            // (`Rat.abs_add_le`, `Rat.add_le_add`, `Rat.le_trans`), present in the
            // prelude alongside the universal Nat bound.
            self.init_nn_verify_dot_product_error()?;
        }

        Ok(())
    }

    fn register_float_to_rational_exact(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.float_to_rational_exact");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_float_to_rational_exact_type(c),
        })
    }

    /// Discharge ONE instance of the per-concrete-float exactness axiom by
    /// kernel COMPUTATION (not assertion):
    ///
    /// ```text
    /// theorem float_to_rat_exact_discharge_01 :
    ///   Eq Rat
    ///     (Float.toRatExact (Float.mk 4591870180066957722))   -- mk 0.1
    ///     (Rat.mk (Int.ofNat 7205759403792794) 72057594037927936)
    /// := @Eq.refl Rat (Rat.mk (Int.ofNat 7205759403792794) 72057594037927936)
    /// ```
    ///
    /// The right-hand side is the EXACT value of the binary64 nearest `0.1`:
    /// `0.1` is stored as `0x3FB999999999999A`, decomposing to
    /// `m = 7205759403792794`, `e = −56`, i.e. exactly
    /// `7205759403792794 / 2^56`
    /// (`= 0.1000000000000000055511151231257827021181583404541015625`).
    ///
    /// `Eq.refl Rat RHS` type-checks against the declared `Eq Rat LHS RHS`
    /// because the kernel reduces `LHS` — the opaque `Float.toRatExact` applied
    /// to `Float.mk <bits>` — through the native reducer to the *identical*
    /// `Rat.mk (Int.ofNat 7205759403792794) (2^56)`. So the equality is closed
    /// by definitional computation in the kernel, with an EMPTY non-foundational
    /// axiom closure (the only axioms reachable are the foundational
    /// `Eq`/`Quot` built-ins). This replaces the corresponding instance of the
    /// `float_to_rational_exact` axiom with a kernel-checked fact.
    fn register_float_to_rat_exact_discharge_01(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.float_to_rat_exact_discharge_01");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // The binary64 bit pattern of `0.1`.
        const F64_BITS_0_1: u64 = 0x3FB9_9999_9999_999A; // 4591870180066957722
                                                         // Exact value: 7205759403792794 / 2^56.
        const NUM_0_1: u64 = 7205759403792794;
        const DEN_0_1: u64 = 72057594037927936; // 2^56

        // LHS: Float.toRatExact (Float.mk <bits>)
        let float_mk = Expr::const_(Name::from_string("Float.mk"), vec![]);
        let to_rat_exact = Expr::const_(Name::from_string("Float.toRatExact"), vec![]);
        let lhs = Expr::app(
            to_rat_exact,
            Expr::app(float_mk, Expr::nat_lit(F64_BITS_0_1)),
        );

        // RHS: Rat.mk (Int.ofNat 7205759403792794) 72057594037927936
        let rat_mk = Expr::const_(Name::from_string("Rat.mk"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let rhs = Expr::apps(
            rat_mk,
            [
                Expr::app(int_of_nat, Expr::nat_lit(NUM_0_1)),
                Expr::nat_lit(DEN_0_1),
            ],
        );

        // Type: Eq @Rat lhs rhs
        let type_ = c.rat_eq(lhs, rhs.clone());

        // Proof: @Eq.refl.{1} Rat rhs  (kernel checks lhs ≡ rhs by computation).
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        let value = Expr::apps(eq_refl, [c.rat.clone(), rhs]);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    fn register_rounding_error_bound(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.rounding_error_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_rounding_error_bound_type(c),
        })
    }

    fn register_interval_contains_real(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.interval_contains_real");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_interval_contains_real_type(c),
        })
    }

    fn register_matmul_error_bound(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.matmul_error_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_matmul_error_bound_type(c),
        })
    }

    fn register_ibp_float_sound(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.ibp_float_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_ibp_float_sound_type(c),
        })
    }

    fn register_error_propagation_linear(&mut self, c: &FRConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.FloatRational.error_propagation_linear");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: build_error_propagation_linear_type(c),
        })
    }
}

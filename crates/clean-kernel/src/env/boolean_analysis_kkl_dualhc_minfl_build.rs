// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Support-count identity term builders. `include!`d into
// `boolean_analysis_kkl_dualhc_minfl.rs` — shares its `MinflConsts` and imports.
// Split out to keep each file under the 500-line convention. (Regular `//`
// comments: inner doc `//!` is not allowed at an `include!` site.)

impl MinflConsts {
    /// `0 < (2 : Rat)` := `@Int.NonNeg.mk 1` (the `Rat.lt` of `0 < mk(ofNat 2) 1`
    /// reduces to `Int.NonNeg (ofNat 1)`; byte-matches `PerCoordConsts::lit_pos`).
    fn two_pos(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_one(),
        )
    }
    /// `0 < Rat.powNat 2 n`.
    fn pow_two_pos(&self, n: &Expr) -> Expr {
        self.pow_pos_at(self.rat_two(), n, self.two_pos())
    }
}

impl Environment {
    /// `Rat.mul_natCast : ∀ a b : Nat,
    ///   Rat.mul (Rat.mk (Int.ofNat a) 1) (Rat.mk (Int.ofNat b) 1)
    ///     = Rat.mk (Int.ofNat (Nat.mul a b)) 1`.
    ///
    /// PROOF (one `Quot.sound`): the LHS ι-reduces to the quotient class of
    /// `Raw.mk (Int.mul (ofNat a)(ofNat b)) (Nat.mul 1 1)`; the RHS is the class
    /// of `Raw.mk (ofNat (Nat.mul a b)) 1`. Their `Rat.Raw.Equiv`
    /// (`num·ofNat effDenom = num·ofNat effDenom`) reduces to
    /// `ofNat (Nat.mul a b) · ofNat 1 = Int.mul (ofNat a)(ofNat b) · ofNat 1`,
    /// which is closed by `Eq.refl` since `Int.mul (ofNat a)(ofNat b) ≡
    /// ofNat (Nat.mul a b)` (def-eq, `Int.ofNat_mul`) and the effDenoms reduce to
    /// `ofNat 1`. Kernel-checked, `Constructive`, empty admitted-axiom closure
    /// (only `Quot.sound`, a FOUNDATIONAL axiom). Idempotent.
    pub fn register_rat_mul_natcast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat, Rat.mk, Quot machinery, Rat.Raw.*
        self.init_rat_arith()?; // live Rat.mul (Quot.lift)

        let c = MinflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: mul_natcast_type(&c),
            value: mul_natcast_value(&c),
        })
    }

    /// `Rat.powNat_two_eq_natCast : ∀ n : Nat,
    ///   Rat.powNat (Rat.mk (Int.ofNat 2) 1) n = Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`.
    ///
    /// `Nat.rec` on `n`, motive `λn. 2^n = mk(ofNat (Nat.pow 2 n)) 1`. Base `n=0`:
    /// both sides ≡ `mk(ofNat 1) 1` (`Rat.powNat _ 0 ≡ Rat.one ≡ mk(ofNat 1) 1`;
    /// `Nat.pow 2 0 ≡ 1`), closed by `Eq.refl`. Step `n+1`, ih
    /// `2^n = mk(ofNat (Nat.pow 2 n)) 1`: the goal ι-reduces to
    /// `2·2^n = mk(ofNat (Nat.mul (Nat.pow 2 n) 2)) 1` (powNat multiplies on the
    /// LEFT, Nat.pow on the RIGHT), via the chain
    ///
    /// ```text
    ///   2·2^n = 2·mk(ofNat(Nat.pow 2 n)) 1       congr (2·_) ih
    ///         = mk(ofNat 2) 1 · mk(ofNat(Nat.pow 2 n)) 1   (def-eq; 2 ≡ mk(ofNat 2) 1)
    ///         = mk(ofNat (Nat.mul 2 (Nat.pow 2 n))) 1      mul_natCast 2 (Nat.pow 2 n)
    ///         = mk(ofNat (Nat.mul (Nat.pow 2 n) 2)) 1      congr mk(ofNat ·) 1 (Nat.mul_comm)
    /// ```
    ///
    /// whose last term is the goal RHS (def-eq to `Nat.pow 2 (n+1)`).
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_rat_pow_nat_two_eq_natcast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_two_eq_natCast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat (+ powNat_succ def-eq)
        self.register_rat_mul_natcast()?; // the step's natCast multiplication
        self.register_nat_mul_comm_proof()?; // Nat.mul_comm (factor-order swap)

        let c = MinflConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: pow_two_natcast_type(&c),
            value: pow_two_natcast_value(&c),
        })
    }

    /// `Rat.powNat_eight_eq_two_cubed : ∀ n : Nat,
    ///   Rat.powNat 8 n = Rat.mul (Rat.powNat 2 n)
    ///                            (Rat.mul (Rat.powNat 2 n)(Rat.powNat 2 n))`,
    /// i.e. `8^n = (2^n)³` (= `2^n·(2^n·2^n)`). PROOF: `8 = 2·(2·2)` (two
    /// `mul_natCast` steps, since `Nat.mul 2 2 ≡ 4`, `Nat.mul 2 4 ≡ 8` def-eq),
    /// `congrArg (powNat · n)` lifts it, then `powNat_mul_base` twice distributes
    /// the power over the product base. Kernel-checked, `Constructive`, empty
    /// admitted-axiom closure. Idempotent.
    pub fn register_rat_pow_nat_eight_eq_two_cubed(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_eight_eq_two_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_mul_base()?; // powNat_mul_base
        self.register_rat_mul_natcast()?; // 8 = 2·(2·2) literal bridge

        let c = MinflConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: eight_cubed_type(&c),
            value: eight_cubed_value(&c),
        })
    }

    /// `BoolAnalysis.dualhc_m_pow2_eq_4pow_influence : ∀ n f i,
    ///   Rat.mul m (Rat.powNat 2 n)
    ///     = Rat.mul (Rat.mul (Rat.powNat 2 n)(Rat.powNat 2 n)) (Influence n f i)`,
    /// where `m := subsetSum n (fun x => (D_i f x · D_i f x)·(half·half))`.
    ///
    /// The support-count identity `m·2^n = (2^n)²·Inf_i` — the measure hypothesis
    /// `dualhc_per_coord` previously took on faith. See the module doc for the
    /// proof. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent.
    pub fn register_dualhc_m_pow2_eq_4pow_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_m_pow2_eq_4pow_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, ind, hcFlip, BoolFn, HCPoint, Influence, Expect
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_beq()?;
        self.register_subset_sum()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.inv (half spelling)
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_mul_base()?; // powNat_pos (positivity)
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;
        self.init_algebra_rat_inv_dyadic()?; // mul_inv_cancel, ne_zero_of_pos
        self.init_boolean_analysis_kkl_dualhc_step2()?; // dualhc_step2_m_eq_disagree_mass
        self.register_rat_pow_nat_two_eq_natcast()?; // the two-spellings bridge

        let c = MinflConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: m_pow2_type(&c),
            value: m_pow2_value(&c),
        })
    }
}

// ════════════ Rat.mul_natCast ════════════

fn mul_natcast_type(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bv_id, bv) = b.fresh_local(c.nat.clone());
    let lhs = c.mul(c.natcast(a.clone()), c.natcast(bv.clone()));
    let rhs = c.natcast(c.nmul(a.clone(), bv.clone()));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn mul_natcast_value(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bv_id, bv) = b.fresh_local(c.nat.clone());

    let of_a = c.of_nat(a.clone());
    let of_b = c.of_nat(bv.clone());
    let of_ab = c.of_nat(c.nmul(a.clone(), bv.clone())); // ofNat (Nat.mul a b)
    let int_mul = Expr::apps(c.nat_mul.clone(), []); // placeholder (unused)
    let _ = int_mul;

    // raw_l := Raw.mk (ofNat (Nat.mul a b)) 1            -- the RHS-target class
    // raw_r := Raw.mk (Int.mul (ofNat a)(ofNat b)) (Nat.mul 1 1)  -- the LHS class
    let one = c.nat_one();
    let imul_ab = {
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        Expr::apps(int_mul, [of_a.clone(), of_b.clone()])
    };
    let raw_l = c.raw_mk(of_ab.clone(), one.clone());
    let raw_r = c.raw_mk(imul_ab.clone(), c.nmul(one.clone(), one.clone()));

    // Equiv raw_l raw_r ≡ (ofNat (a·b))·ofNat 1 = (Int.mul (ofNat a)(ofNat b))·ofNat 1.
    // Both products are def-eq (ofNat (a·b) ≡ Int.mul (ofNat a)(ofNat b)), so the
    // Equiv class is inhabited by `Eq.refl` at the LHS product.
    let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
    let eq_lhs = Expr::apps(int_mul.clone(), [of_ab.clone(), c.of_nat(one.clone())]);
    let equiv = c.refl_int(eq_lhs.clone());
    let _ = c.eq_int(eq_lhs.clone(), eq_lhs); // documents the Equiv shape

    // Quot.sound raw_l raw_r equiv : Quot.mk raw_l = Quot.mk raw_r.
    //   Quot.mk raw_l ≡ mk(ofNat (a·b)) 1                 (RHS goal)
    //   Quot.mk raw_r ≡ Rat.mul (mk(ofNat a) 1)(mk(ofNat b) 1)  (LHS goal)
    let sound = c.quot_sound(raw_l.clone(), raw_r.clone(), equiv);

    let lhs_goal = c.mul(c.natcast(a.clone()), c.natcast(bv.clone()));
    let rhs_goal = c.natcast(c.nmul(a.clone(), bv.clone()));
    let quot_l = c.quot_mk(raw_l);
    let quot_r = c.quot_mk(raw_r);
    // sound : quot_l = quot_r ; retype to lhs_goal = rhs_goal via def-eq refls.
    //   to_l   : lhs_goal = quot_r   (lhs_goal ≡ quot_r)
    //   sound' : quot_r = quot_l     (symm sound)
    //   to_r   : quot_l = rhs_goal   (quot_l ≡ rhs_goal)
    let sound_sym = c.symm_rat(quot_l.clone(), quot_r.clone(), sound);
    let to_l = c.refl_rat(lhs_goal.clone()); // : lhs_goal = quot_r
    let to_r = c.refl_rat(rhs_goal.clone()); // : quot_l = rhs_goal
    let step1 = c.trans_rat(
        lhs_goal.clone(),
        quot_r.clone(),
        quot_l.clone(),
        to_l,
        sound_sym,
    );
    let proof = c.trans_rat(
        lhs_goal.clone(),
        quot_l.clone(),
        rhs_goal.clone(),
        step1,
        to_r,
    );

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), proof);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// ════════════ Rat.powNat_two_eq_natCast ════════════

fn pow_two_natcast_type(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let lhs = c.pow(c.rat_two(), &n);
    let rhs = c.natcast(c.nat_pow_of(c.nat_two(), &n));
    let concl = c.eq_rat(lhs, rhs);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

fn pow_two_natcast_value(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let two = c.rat_two();

    // motive : fun (k : Nat) => Rat.powNat 2 k = mk(ofNat (Nat.pow 2 k)) 1
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let body = c.eq_rat(
            c.pow(two.clone(), &k),
            c.natcast(c.nat_pow_of(c.nat_two(), &k)),
        );
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : Rat.powNat 2 0 = mk(ofNat (Nat.pow 2 0)) 1.
    //   LHS ≡ Rat.one ≡ mk(ofNat 1) 1 ; RHS ≡ mk(ofNat 1) 1 (Nat.pow 2 0 ≡ 1).
    let base = c.refl_rat(c.pow(two.clone(), &c.nat_zero));

    // succ_case : fun (k : Nat) (ih : 2^k = mk(ofNat (Nat.pow 2 k)) 1) =>
    //   <proof of 2^(k+1) = mk(ofNat (Nat.pow 2 (k+1))) 1>.
    let succ_case = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let pow2k = c.nat_pow_of(c.nat_two(), &k); // Nat.pow 2 k
        let ih_ty = c.eq_rat(c.pow(two.clone(), &k), c.natcast(pow2k.clone()));
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        let rpk = c.pow(two.clone(), &k); // 2^k
        let cast_pow2k = c.natcast(pow2k.clone()); // mk(ofNat (Nat.pow 2 k)) 1

        // goal LHS ≡ 2·2^k (Rat.powNat 2 (succ k) ι-reduces to Rat.mul 2 (2^k)).
        let two_rpk = c.mul(two.clone(), rpk.clone());
        // s1 : 2·2^k = 2·mk(ofNat (Nat.pow 2 k)) 1   congr (2·_) ih.
        let two_cast = c.mul(two.clone(), cast_pow2k.clone());
        let s1 = c.congr_l(&d, &two, rpk.clone(), cast_pow2k.clone(), ih);
        // 2·mk(ofNat (Nat.pow 2 k)) 1 ≡ mk(ofNat 2) 1 · mk(ofNat (Nat.pow 2 k)) 1
        //   (2 ≡ mk(ofNat 2) 1), so mul_natCast 2 (Nat.pow 2 k) applies directly.
        // s2 : mk(ofNat 2) 1 · mk(ofNat (Nat.pow 2 k)) 1
        //        = mk(ofNat (Nat.mul 2 (Nat.pow 2 k))) 1.
        let s2 = c.mul_natcast_at(c.nat_two(), pow2k.clone());
        let cast_2_pow2k = c.natcast(c.nmul(c.nat_two(), pow2k.clone())); // mk(ofNat (2·Nat.pow 2 k)) 1
                                                                          // s3 : mk(ofNat (Nat.mul 2 (Nat.pow 2 k))) 1
                                                                          //        = mk(ofNat (Nat.mul (Nat.pow 2 k) 2)) 1   congr (mk(ofNat ·) 1)(Nat.mul_comm 2 (Nat.pow 2 k)).
        let nmul_comm = Expr::apps(
            Expr::const_(Name::from_string("Nat.mul_comm"), vec![]),
            [c.nat_two(), pow2k.clone()],
        ); // : Nat.mul 2 (Nat.pow 2 k) = Nat.mul (Nat.pow 2 k) 2
        let cast_pow2k_2 = c.natcast(c.nmul(pow2k.clone(), c.nat_two())); // mk(ofNat (Nat.pow 2 k · 2)) 1
        let s3 = mk_natcast_congr(
            c,
            &d,
            c.nmul(c.nat_two(), pow2k.clone()),
            c.nmul(pow2k.clone(), c.nat_two()),
            nmul_comm,
        );

        // chain: 2·2^k = 2·cast = mk(ofNat 2)·cast = cast(2·pow2k) = cast(pow2k·2).
        // (`two_cast ≡ mk(ofNat 2)·cast` by def-eq, so s2 retypes against two_cast.)
        let mk2_cast = c.mul(c.natcast(c.nat_two()), cast_pow2k.clone());
        let _ = &mk2_cast; // def-eq to two_cast
        let ch = c.trans_rat(
            two_rpk.clone(),
            two_cast.clone(),
            cast_2_pow2k.clone(),
            s1,
            s2,
        );
        let proof = c.trans_rat(
            two_rpk.clone(),
            cast_2_pow2k.clone(),
            cast_pow2k_2.clone(),
            ch,
            s3,
        );
        // proof : 2·2^k = mk(ofNat (Nat.pow 2 k · 2)) 1, which is def-eq to the
        // goal RHS mk(ofNat (Nat.pow 2 (k+1))) 1 (Nat.pow 2 (succ k) ≡ Nat.mul (Nat.pow 2 k) 2).
        let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r))
    };

    let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, succ_case, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app))
}

/// `congrArg (fun (z : Nat) => mk(ofNat z) 1) h : mk(ofNat a) 1 = mk(ofNat b) 1`
/// for `h : Eq Nat a b`.
fn mk_natcast_congr(c: &MinflConsts, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
    let f = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.nat.clone());
        let body = c.natcast(z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body))
    };
    Expr::apps(
        c.congr_arg1.clone(),
        [c.nat.clone(), c.rat.clone(), a, bb, f, h],
    )
}

// ════════════ Rat.powNat_eight_eq_two_cubed ════════════

impl MinflConsts {
    /// `Rat.powNat_mul_base a b k : (a·b)^k = a^k·b^k`.
    fn pow_mul_base_at(&self, a: Expr, bb: Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_mul_base.clone(), [a, bb, k.clone()])
    }
    /// `congrArg (fun (z : Rat) => Rat.powNat z k) h : powNat a k = powNat b k`.
    fn congr_pow_base(
        &self,
        parent: &EnvDeclBuilder,
        k: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.pow(z, k);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, f, h],
        )
    }
}

fn eight_cubed_type(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let q = c.pow(c.lit(2), &n);
    let lhs = c.pow(c.lit(8), &n);
    let rhs = c.mul(q.clone(), c.mul(q.clone(), q));
    let concl = c.eq_rat(lhs, rhs);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
}

fn eight_cubed_value(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let two = c.lit(2);
    let four = c.lit(4);
    let eight = c.lit(8);
    let two_two = c.mul(two.clone(), two.clone()); // 2·2
    let two_four = c.mul(two.clone(), four.clone()); // 2·4
    let two_22 = c.mul(two.clone(), two_two.clone()); // 2·(2·2)

    // b8 : 2·(2·2) = 8.
    //   e1 : 2·2 = 4   (mul_natCast 2 2; Nat.mul 2 2 ≡ 4 def-eq).
    //   e2 : 2·(2·2) = 2·4   congr (2·_) e1.
    //   e3 : 2·4 = 8   (mul_natCast 2 4; Nat.mul 2 4 ≡ 8 def-eq).
    let e1 = c.mul_natcast_at(c.nat_lit(2), c.nat_lit(2)); // 2·2 = mk(ofNat (2·2)) 1 ≡ 4
    let e2 = c.congr_l(&b, &two, two_two.clone(), four.clone(), e1);
    let e3 = c.mul_natcast_at(c.nat_lit(2), c.nat_lit(4)); // 2·4 = mk(ofNat (2·4)) 1 ≡ 8
    let b8 = c.trans_rat(two_22.clone(), two_four.clone(), eight.clone(), e2, e3); // 2·(2·2) = 8
    let b8_sym = c.symm_rat(two_22.clone(), eight.clone(), b8); // 8 = 2·(2·2)

    // step_lift : 8^n = (2·(2·2))^n   congrArg (powNat · n) b8_sym.
    let q = c.pow(two.clone(), &n); // 2^n
    let pow_8n = c.pow(eight.clone(), &n);
    let pow_222n = c.pow(two_22.clone(), &n);
    let step_lift = c.congr_pow_base(&b, &n, eight.clone(), two_22.clone(), b8_sym);

    // step_mb1 : (2·(2·2))^n = 2^n·(2·2)^n   powNat_mul_base 2 (2·2) n.
    let pow_22n = c.pow(two_two.clone(), &n); // (2·2)^n
    let q_pow22n = c.mul(q.clone(), pow_22n.clone());
    let step_mb1 = c.pow_mul_base_at(two.clone(), two_two.clone(), &n);

    // step_mb2 : (2·2)^n = 2^n·2^n   powNat_mul_base 2 2 n ; lift under (2^n·_).
    let qq = c.mul(q.clone(), q.clone());
    let mb2 = c.pow_mul_base_at(two.clone(), two.clone(), &n); // (2·2)^n = 2^n·2^n
    let q_qq = c.mul(q.clone(), qq.clone());
    let step_mb2 = c.congr_l(&b, &q, pow_22n.clone(), qq.clone(), mb2);

    // chain: 8^n = (2·(2·2))^n = 2^n·(2·2)^n = 2^n·(2^n·2^n).
    let ch = c.trans_rat(
        pow_8n.clone(),
        pow_222n.clone(),
        q_pow22n.clone(),
        step_lift,
        step_mb1,
    );
    let proof = c.trans_rat(pow_8n.clone(), q_pow22n.clone(), q_qq.clone(), ch, step_mb2);

    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof))
}

include!("boolean_analysis_kkl_dualhc_minfl_minfl.rs");

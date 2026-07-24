// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// `BoolAnalysis.deriv_coeff_sq_eq` — the SQUARE of `#4`
// (`BoolAnalysis.deriv_coeff_eq`). `include!`d into
// `boolean_analysis_deriv_coeff.rs`; shares `DerivCoeffConsts` + imports.
//
// ```text
// BoolAnalysis.deriv_coeff_sq_eq :
//   ∀ (n : Nat) (b : HCPoint n → Rat) (S : HCPoint n) (i : Fin n),
//     @Eq Rat
//       (Rat.mul (Acoeff n (D_i b) S) (Acoeff n (D_i b) S))   -- A(D_i b,S)²
//       (Rat.mul (Rat.mul 4 (ind (S i)))                       -- (4·ind(S i))·A(b,S)²
//                (Rat.mul (Acoeff n b S) (Acoeff n b S)))
// ```
//
// Proof (`fs`-free; `ind := ind (S i)`, `A := A(b,S)`, `R2 := (2·ind)·A`):
// 1. `deriv_coeff_eq n b S i : A(D_i b,S) = R2`  (the landed `#4`).
// 2. `congrArg (·²) (1) : A(D_i b,S)² = R2²`.
// 3. `R2² = ((2·ind)·(2·ind))·(A·A)`            [mul_mul_mul_comm (2·ind) A (2·ind) A].
// 4. `(2·ind)·(2·ind) = (2·2)·(ind·ind)`        [mul_mul_mul_comm 2 ind 2 ind]
//      `= 4·(ind·ind)`                          [congrArg (·(ind·ind)) (2·2 = 4 by refl)]
//      `= 4·ind`                                [congrArg (4·) (ind_mul_self (S i))].
// 5. `((2·ind)·(2·ind))·(A·A) = (4·ind)·(A·A)`  [congrArg (·(A·A)) of (4)].
// 6. chain (2)·(3)·(5).
//
// Constructive, empty admitted-axiom closure.

impl DerivCoeffConsts {
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a, b, cc, d],
        )
    }
    /// `BoolAnalysis.ind_mul_self bit : (ind bit)·(ind bit) = ind bit`.
    fn ind_mul_self(&self, bit: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.ind_mul_self"), vec![]),
            bit,
        )
    }
    /// `@Eq.refl Rat x`.
    fn eq_refl(&self, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [self.rat.clone(), x],
        )
    }
}

fn deriv_coeff_sq_type(c: &DerivCoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let db = c.deriv(&b, &n, &bf, &i);
    let cap_a_d = c.acoeff(&b, &n, &db, &s); // A(D_i b, S)
    let lhs = c.mul(cap_a_d.clone(), cap_a_d); // A(D_i b,S)²

    let four = rat_numeral(4);
    let si = Expr::app(s.clone(), i.clone());
    let four_ind = c.mul(four, c.ind_(si)); // 4·ind(S i)
    let cap_a = c.acoeff(&b, &n, &bf, &s); // A(b,S)
    let a_sq = c.mul(cap_a.clone(), cap_a); // A(b,S)²
    let rhs = c.mul(four_ind, a_sq); // (4·ind)·A²
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(s_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn deriv_coeff_sq_value(c: &DerivCoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let si = Expr::app(s.clone(), i.clone());
    let ind = c.ind_(si.clone());
    let two = c.rat_two.clone();
    let four = rat_numeral(4);

    let db = c.deriv(&b, &n, &bf, &i);
    let lcap = c.acoeff(&b, &n, &db, &s); // A(D_i b, S) = L
    let cap_a = c.acoeff(&b, &n, &bf, &s); // A(b,S) = A
    let a_sq = c.mul(cap_a.clone(), cap_a.clone()); // A·A

    let two_ind = c.mul(two.clone(), ind.clone()); // 2·ind = R2's left factor
    let r2 = c.mul(two_ind.clone(), cap_a.clone()); // R2 := (2·ind)·A

    // (1) dc : L = R2   [deriv_coeff_eq n b S i]
    let dc = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.deriv_coeff_eq"), vec![]),
        [n.clone(), bf.clone(), s.clone(), i.clone()],
    );

    // (2) sq_eq : L·L = R2·R2   [congrArg (fun t => t·t) dc]
    let sq_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.mul(t.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let l_sq = c.mul(lcap.clone(), lcap.clone());
    let r2_sq = c.mul(r2.clone(), r2.clone());
    let sq_eq = c.congr(lcap.clone(), r2.clone(), sq_fn, dc);

    // (3) leg_mmmc : R2·R2 = ((2·ind)·(2·ind))·(A·A)
    //   = mul_mul_mul_comm (2·ind) A (2·ind) A
    let two_ind_sq = c.mul(two_ind.clone(), two_ind.clone()); // (2·ind)·(2·ind)
    let leg_mmmc = c.mmmc(
        two_ind.clone(),
        cap_a.clone(),
        two_ind.clone(),
        cap_a.clone(),
    );
    let mid3 = c.mul(two_ind_sq.clone(), a_sq.clone()); // ((2·ind)·(2·ind))·(A·A)

    // (4) inner : (2·ind)·(2·ind) = 4·ind
    //   4a: (2·ind)·(2·ind) = (2·2)·(ind·ind)   [mmmc 2 ind 2 ind]
    let two_two = c.mul(two.clone(), two.clone()); // 2·2
    let ind_ind = c.mul(ind.clone(), ind.clone()); // ind·ind
    let mmmc4 = c.mmmc(two.clone(), ind.clone(), two.clone(), ind.clone());
    let mid4a = c.mul(two_two.clone(), ind_ind.clone()); // (2·2)·(ind·ind)
                                                         //   4b: (2·2)·(ind·ind) = 4·(ind·ind)   [congrArg (·(ind·ind)) (2·2 = 4)]
                                                         //   2·2 = 4 by Eq.refl (numeral mul reduces to Rat.mk 4 1).
    let two_two_eq_four = c.eq_refl(four.clone()); // type-checked against 2·2 = 4
    let g_mulr_indind = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z.clone(), ind_ind.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let four_indind = c.mul(four.clone(), ind_ind.clone()); // 4·(ind·ind)
    let s4b = c.congr(
        two_two.clone(),
        four.clone(),
        g_mulr_indind,
        two_two_eq_four,
    );
    //   4c: 4·(ind·ind) = 4·ind   [congrArg (4·) (ind_mul_self (S i))]
    let four_ind = c.mul(four.clone(), ind.clone()); // 4·ind
    let ims = c.ind_mul_self(si.clone()); // (ind)·(ind) = ind
    let s4c = c.mul_left_congr(&b, &four, ind_ind.clone(), ind.clone(), ims);
    //   inner chain: (2·ind)² = (2·2)·(ind·ind) = 4·(ind·ind) = 4·ind
    let inner1 = c.trans(
        two_ind_sq.clone(),
        mid4a.clone(),
        four_indind.clone(),
        mmmc4,
        s4b,
    );
    let inner = c.trans(
        two_ind_sq.clone(),
        four_indind.clone(),
        four_ind.clone(),
        inner1,
        s4c,
    );

    // (5) outer : ((2·ind)·(2·ind))·(A·A) = (4·ind)·(A·A)   [congrArg (·(A·A)) inner]
    let g_mulr_asq = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z.clone(), a_sq.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rhs_final = c.mul(four_ind.clone(), a_sq.clone()); // (4·ind)·(A·A)
    let outer = c.congr(two_ind_sq.clone(), four_ind.clone(), g_mulr_asq, inner);

    // assemble: L·L = R2·R2 = ((2·ind)·(2·ind))·(A·A) = (4·ind)·(A·A)
    let c1 = c.trans(l_sq.clone(), r2_sq.clone(), mid3.clone(), sq_eq, leg_mmmc);
    let proof = c.trans(l_sq, mid3, rhs_final, c1, outer);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(s_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

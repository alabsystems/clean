// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Term builders for `boolean_analysis_hc_decode_surjective.rs` (include!d).
// Kept in a sibling file to honour the <=500-line module cap.

/// Shared atoms for the `hcDecode_surjective` construction.
#[cfg(test)]
struct SurjConsts {
    l0: Level,
    l1: Level,
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    two: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_last: Expr,
    fin_mk: Expr,
    fin_cast_succ: Expr,
    cast_add: Expr,
    add_nat: Expr,
    extend_f: Expr,
    extend_t: Expr,
    bool_false: Expr,
    bool_true: Expr,
    bool_cases: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_fun: Expr,
    funext: Expr,
    fin_last_cases: Expr,
    nat_rec0: Expr,
    exists_const: Expr,
    exists_intro: Expr,
    not_succ_le_zero: Expr,
    false_elim: Expr,
    zero_lt_succ: Expr,
}

#[cfg(test)]
impl SurjConsts {
    #[cfg(test)]
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat_succ = k("Nat.succ");
        let nat_zero = k("Nat.zero");
        let one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            l0: l0.clone(),
            l1: l1.clone(),
            nat: k("Nat"),
            bool_: k("Bool"),
            fin: k("Fin"),
            nat_succ,
            nat_zero,
            nat_pow: k("Nat.pow"),
            two,
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_last: k("Fin.last"),
            fin_mk: k("Fin.mk"),
            fin_cast_succ: k("Fin.castSucc"),
            cast_add: k("Fin.castAdd"),
            add_nat: k("Fin.addNat"),
            extend_f: k("BoolAnalysis.extendF"),
            extend_t: k("BoolAnalysis.extendT"),
            bool_false: k("Bool.false"),
            bool_true: k("Bool.true"),
            bool_cases: Expr::const_(Name::from_string("Bool.casesOn"), vec![l0.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_fun: Expr::const_(Name::from_string("congrFun"), vec![l1.clone(), l1.clone()]),
            funext: Expr::const_(Name::from_string("funext"), vec![l1.clone(), l1.clone()]),
            // Fin.lastCases.{0}: the proof motive `Eq Bool .. ..` lands in Prop = Sort 0.
            fin_last_cases: Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]),
            // Nat.rec.{0}: the surjectivity motive `∀ S, ∃ jS, ..` lands in Prop = Sort 0.
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            exists_const: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            not_succ_le_zero: k("Nat.not_succ_le_zero"),
            // False.elim.{0}: the goal `hcDecode 0 jS i = S i` is a Prop = Sort 0.
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]),
            zero_lt_succ: k("Nat.zero_lt_succ"),
        }
    }

    #[cfg(test)]
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    #[cfg(test)]
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    #[cfg(test)]
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    #[cfg(test)]
    fn islt(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_islt.clone(), [n.clone(), i.clone()])
    }
    #[cfg(test)]
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    #[cfg(test)]
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    #[cfg(test)]
    fn decode(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), k.clone()])
    }
    /// `@Eq Bool l r`.
    #[cfg(test)]
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_.clone(), l, r])
    }
    /// `@Eq (HCPoint n) l r`.
    #[cfg(test)]
    fn eq_point(&self, n: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.hcpoint_of(n), l, r])
    }
    #[cfg(test)]
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.bool_.clone(), a, b, cc, hab, hbc],
        )
    }
    #[cfg(test)]
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.bool_.clone(), a, b, h])
    }
    /// `Exists.{1} (Fin (2^n)) pred`.
    #[cfg(test)]
    fn exists_decode(&self, n: &Expr, pred: Expr) -> Expr {
        Expr::apps(
            self.exists_const.clone(),
            [self.fin_of(&self.pow2(n)), pred],
        )
    }
    /// The surjectivity predicate at level `n`: `fun (jS : Fin (2^n)) => hcDecode n jS = S`.
    #[cfg(test)]
    fn pred(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = d.fresh_local(self.fin_of(&self.pow2(n)));
        let body = self.eq_point(n, self.decode(n, &j), s.clone());
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, self.fin_of(&self.pow2(n)), body))
    }
    /// `∀ (S : HCPoint n), ∃ (jS : Fin (2^n)), hcDecode n jS = S`.
    #[cfg(test)]
    fn motive_body(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = d.fresh_local(self.hcpoint_of(n));
        let body = self.exists_decode(n, self.pred(&d, n, &s));
        d.finish_child(d.mk_pi(s_id, BinderInfo::Default, self.hcpoint_of(n), body))
    }
    /// `@Exists.intro.{1} (Fin (2^n)) pred witness proof : ∃ jS, hcDecode n jS = S`.
    #[cfg(test)]
    fn intro(&self, n: &Expr, pred: Expr, witness: Expr, proof: Expr) -> Expr {
        Expr::apps(
            self.exists_intro.clone(),
            [self.fin_of(&self.pow2(n)), pred, witness, proof],
        )
    }
}

/// Build `(type, value)` of `BoolAnalysis.hcDecode_surjective`.
#[cfg(test)]
fn build_surjective(c: &SurjConsts) -> (Expr, Expr) {
    // type: ∀ (n : Nat) (S : HCPoint n), ∃ jS, hcDecode n jS = S.
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let body = c.motive_body(&b, &n);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // value: fun (n : Nat) => @Nat.rec.{0} motive base step n.
    let value = {
        // motive : fun (m : Nat) => ∀ S, ∃ jS, hcDecode m jS = S.
        let motive = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let body = c.motive_body(&b, &m);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
        };
        let base = build_base(c);
        let step = build_step(c);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let rec = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n.clone()]);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec))
    };
    (type_, value)
}

/// base : ∀ (S : HCPoint 0), ∃ (jS : Fin (2^0)), hcDecode 0 jS = S.
#[cfg(test)]
fn build_base(c: &SurjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = c.nat_zero.clone();
    let p20 = c.pow2(&zero); // 2^0 ≡ 1 ≡ succ 0
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&zero));

    // witness jS := @Fin.mk (2^0) 0 (Nat.zero_lt_succ 0)   (2^0 ≡ succ 0 by ι).
    let zero_lt = Expr::app(c.zero_lt_succ.clone(), zero.clone());
    let witness = Expr::apps(c.fin_mk.clone(), [p20.clone(), zero.clone(), zero_lt]);

    // pointwise (vacuous over Fin 0): fun (i : Fin 0) =>
    //   @False.elim.{1} (hcDecode 0 jS i = S i)
    //     (Nat.not_succ_le_zero (val 0 i) (Fin.isLt 0 i))
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_of(&zero));
        let val0 = c.val(&zero, &i);
        let islt = c.islt(&zero, &i); // Nat.lt (val i) 0 ≡ Nat.le (succ (val i)) 0
        let false_pf = Expr::apps(c.not_succ_le_zero.clone(), [val0, islt]);
        let goal = c.eq_bool(
            Expr::app(c.decode(&zero, &witness), i.clone()),
            Expr::app(s.clone(), i.clone()),
        );
        let body = Expr::apps(c.false_elim.clone(), [goal, false_pf]);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&zero), body))
    };

    // funext (Fin 0) (fun _ => Bool) (hcDecode 0 jS) S pointwise : hcDecode 0 jS = S.
    let funext_motive = const_bool_motive(c, &b, &zero);
    let proof = Expr::apps(
        c.funext.clone(),
        [
            c.fin_of(&zero),
            funext_motive,
            c.decode(&zero, &witness),
            s.clone(),
            pointwise,
        ],
    );

    let intro = c.intro(&zero, c.pred(&b, &zero, &s), witness, proof);
    b.finish(b.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(&zero), intro))
}

/// `fun (_ : Fin n) => Bool`.
#[cfg(test)]
fn const_bool_motive(c: &SurjConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (u_id, _u) = d.fresh_local(c.fin_of(n));
    d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.fin_of(n), c.bool_.clone()))
}

include!("boolean_analysis_hc_decode_surjective_step.rs");

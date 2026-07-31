// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **decode↔extend bridges**: the reindexed
//! cube-half points produced by `hcSumSplit` ARE the coordinate-peel extensions
//! of the `n`-level decode.
//!
//! ```text
//! BoolAnalysis.hcDecode_castP_castAdd_extendF :
//!   ∀ (n : Nat) (k : Fin (2^n)),
//!     @Eq (HCPoint (n+1))
//!       (hcDecode (n+1) (castP (Fin.castAdd (2^n) (2^n) k)))   -- the LOW half point
//!       (extendF n (hcDecode n k))                             -- = decode k, top bit 0
//!
//! BoolAnalysis.hcDecode_castP_addNat_extendT :
//!   ∀ (n : Nat) (k : Fin (2^n)),
//!     @Eq (HCPoint (n+1))
//!       (hcDecode (n+1) (castP (Fin.addNat (2^n) (2^n) k)))    -- the HIGH half point
//!       (extendT n (hcDecode n k))                             -- = decode k, top bit 1
//! ```
//!
//! where `castP : Fin (2^n+2^n) → Fin (2^(n+1))` is the split's transport (built
//! from `(Nat.pow_two_succ n).symm`, exactly as `hcSumSplit` / the
//! `hcDecode_castP_*` corr lemmas use it).
//!
//! These are the FULL-point upgrade of the restriction lemmas
//! `hcDecode_restrict_castAdd` / `hcDecode_restrict_addNat` (which only pin the
//! first `n` coordinates): the bridges additionally pin the top coordinate
//! (`false` on the LOW half via `Nat.testBit_lt_pow`, `true` on the HIGH half via
//! `Nat.testBit_add_two_pow_self`), turning the half-block decode into a literal
//! `extendF` / `extendT` of the `n`-level decode. They are the index bridge the
//! operator peel `noiseFn_succ` needs to apply the density point-peel
//! (`noiseDensityW_point_peel_*`) coordinate-by-coordinate across each cube half.
//!
//! ## Proof route (per bridge)
//!
//! `funext` over `Fin (n+1)`, then `Fin.lastCases` on the coordinate `j`:
//!
//! - **`castSucc i` branch** — `congrFun (hcDecode_restrict_<half> n k) i` gives
//!   the LHS bit `= hcDecode n k i`; `Eq.symm (extend*_castSucc n (hcDecode n k)
//!   i)` flips it to `extend* n (hcDecode n k) (castSucc i)`. `Eq.trans` chains.
//! - **`last n` branch** — `hcDecode_castP_<half> n k (last n)` reads the top
//!   bit as `testBit <val> n` (`val (n+1) (last n) ≡ n` defeq); the value lemma
//!   (`testBit_lt_pow` LOW / `testBit_add_two_pow_self` HIGH) at `k.isLt`
//!   collapses it to `false` / `true`; `Eq.symm (extend*_last n (hcDecode n k))`
//!   flips it to `extend* n (hcDecode n k) (last n)`. `Eq.trans` chains.
//!
//! Both kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `hcDecode_restrict_*` / `hcDecode_castP_*` / `extend*_castSucc` /
//! `extend*_last` / `Nat.testBit_*` / `Fin.lastCases` / `funext` / `congrFun` /
//! `Eq.*`, all already constructive.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the decode↔extend bridges.
struct ExtendBridgeConsts {
    #[cfg(test)]
    l0: Level,
    l1: Level,
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_add: Expr,
    two: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_last: Expr,
    fin_cast_succ: Expr,
    cast_add: Expr,
    add_nat: Expr,
    pow_two_succ: Expr,
    eq_symm_nat: Expr,
    eq_ndrec_fin: Expr,
    hc_decode: Expr,
    hcpoint: Expr,
    extend_f: Expr,
    extend_t: Expr,
    funext: Expr,
    fin_last_cases: Expr,
    congr_fun: Expr,
    eq_trans_bool: Expr,
    eq_symm_bool: Expr,
}

impl ExtendBridgeConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            #[cfg(test)]
            l0: l0.clone(),
            l1: l1.clone(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            two,
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            eq_symm_nat: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            // funext.{u,v}: domain Fin (n+1) : Type 0 = Sort 1, codomain Bool : Sort 1.
            funext: Expr::const_(Name::from_string("funext"), vec![l1.clone(), l1.clone()]),
            // Fin.lastCases.{u}: motive `Eq Bool .. ..` lands in Prop = Sort 0.
            fin_last_cases: Expr::const_(Name::from_string("Fin.lastCases"), vec![l0.clone()]),
            // congrFun.{u,v}: f, g : Fin n → Bool, both Sort 1.
            congr_fun: Expr::const_(Name::from_string("congrFun"), vec![l1.clone(), l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm_bool: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, n: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), n.clone())
    }
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    /// `hcDecode m p` — the decode of cube index `p : Fin (2^m)` to `HCPoint m`.
    fn decode(&self, m: &Expr, p: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [m.clone(), p.clone()])
    }
    /// `castP n M := @Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) M (2^(n+1))
    ///                 (Eq.symm (Nat.pow_two_succ n))` — byte-for-byte the split
    /// transport used in `hcSumSplit` / `hcDecode_castP_*`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
        let p2n = self.pow2(n);
        let sum_pow = self.nadd(p2n.clone(), p2n);
        let p2sn = self.pow2(&self.succ(n));
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm_nat.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [self.nat.clone(), sum_pow, motive, mapped.clone(), p2sn, e],
        )
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    /// `@Eq.trans Bool a b c h1 h2`.
    fn trans_bool(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans_bool.clone(),
            [self.bool_.clone(), a, b, c, h1, h2],
        )
    }
    /// `@Eq.symm Bool a b h`.
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm_bool.clone(), [self.bool_.clone(), a, b, h])
    }
    /// `@Fin.isLt (2^n) k : Nat.lt (Fin.val (2^n) k) (2^n)`.
    fn islt(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.fin_islt.clone(), [self.pow2(n), k.clone()])
    }
}

/// Which cube half a bridge is about.
#[derive(Clone, Copy)]
enum Half {
    /// LOW block: `castP ∘ castAdd`, top bit `false`, extends via `extendF`.
    Low,
    /// HIGH block: `castP ∘ addNat`, top bit `true`, extends via `extendT`.
    High,
}

impl Environment {
    /// Initialize the two decode↔extend bridges. Idempotent; axiom-free.
    pub(crate) fn init_boolean_analysis_noise_extend_bridge(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_noise_extend_bridge_init {
            return Ok(());
        }
        self.init_eq()?;
        self.init_funext()?;
        self.register_hc_decode_split_theorems()?; // hcDecode_castP_* + hcDecode_restrict_*
        self.register_fin_last_cases()?;
        self.register_nat_testbit_lt_pow_proof()?; // LOW top bit = false
        self.register_nat_testbit_add_two_pow_proof()?; // HIGH top bit = true
        self.init_boolean_analysis_peel()?; // extendF / extendT
        self.init_boolean_analysis_peel_compute()?; // extend*_castSucc / extend*_last

        let c = ExtendBridgeConsts::new();
        for (half, name) in [
            (Half::Low, "BoolAnalysis.hcDecode_castP_castAdd_extendF"),
            (Half::High, "BoolAnalysis.hcDecode_castP_addNat_extendT"),
        ] {
            let name = Name::from_string(name);
            if self.get_const(&name).is_none() {
                let (ty, value) = build_bridge(&c, half);
                self.add_decl(Declaration::Theorem {
                    name,
                    level_params: vec![],
                    type_: ty,
                    value,
                })?;
            }
        }

        self.boolean_analysis_noise_extend_bridge_init = true;
        Ok(())
    }

    /// Whether the decode↔extend bridges have been initialized.
    #[cfg(test)]
    pub(crate) fn has_boolean_analysis_noise_extend_bridge(&self) -> bool {
        self.boolean_analysis_noise_extend_bridge_init
    }
}

impl Half {
    /// The index map constant (`Fin.castAdd` / `Fin.addNat`).
    fn idx_map<'a>(&self, c: &'a ExtendBridgeConsts) -> &'a Expr {
        match self {
            Half::Low => &c.cast_add,
            Half::High => &c.add_nat,
        }
    }
    /// The extension-map constant (`extendF` / `extendT`).
    fn extend<'a>(&self, c: &'a ExtendBridgeConsts) -> &'a Expr {
        match self {
            Half::Low => &c.extend_f,
            Half::High => &c.extend_t,
        }
    }
    /// The restriction-correspondence lemma name (LOW/HIGH).
    fn restrict_lemma(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.hcDecode_restrict_castAdd",
            Half::High => "BoolAnalysis.hcDecode_restrict_addNat",
        }
    }
    /// The bit-correspondence lemma name (LOW/HIGH).
    fn corr_lemma(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.hcDecode_castP_castAdd",
            Half::High => "BoolAnalysis.hcDecode_castP_addNat",
        }
    }
    /// The `extend*_castSucc` computation lemma name.
    fn ext_castsucc(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.extendF_castSucc",
            Half::High => "BoolAnalysis.extendT_castSucc",
        }
    }
    /// The `extend*_last` computation lemma name.
    fn ext_last(&self) -> &'static str {
        match self {
            Half::Low => "BoolAnalysis.extendF_last",
            Half::High => "BoolAnalysis.extendT_last",
        }
    }
}

/// Build the type + proof of one decode↔extend bridge.
fn build_bridge(c: &ExtendBridgeConsts, half: Half) -> (Expr, Expr) {
    (build_bridge_type(c, half), build_bridge_value(c, half))
}

/// `∀ n (k : Fin (2^n)), hcDecode (n+1) (castP (idx_map k)) = extend* n (hcDecode n k)`.
fn build_bridge_type(c: &ExtendBridgeConsts, half: Half) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p2n = c.pow2(&n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

    let mapped = Expr::apps(
        half.idx_map(c).clone(),
        [p2n.clone(), p2n.clone(), k.clone()],
    );
    let casted = c.cast_p(&b, &n, &mapped);
    let lhs = c.decode(&c.succ(&n), &casted);
    let dec_n_k = c.decode(&n, &k);
    let rhs = Expr::apps(half.extend(c).clone(), [n.clone(), dec_n_k]);

    let concl = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![c.l1.clone()]),
        [c.hcpoint_of(&c.succ(&n)), lhs, rhs],
    );
    let e = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Proof of one decode↔extend bridge: `funext` + `Fin.lastCases`.
fn build_bridge_value(c: &ExtendBridgeConsts, half: Half) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let p2n = c.pow2(&n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

    let mapped = Expr::apps(
        half.idx_map(c).clone(),
        [p2n.clone(), p2n.clone(), k.clone()],
    );
    let casted = c.cast_p(&b, &n, &mapped);
    let dec_n_k = c.decode(&n, &k);
    // lhs_fn : HCPoint (n+1) = hcDecode (n+1) (castP (idx_map k)).
    let lhs_fn = c.decode(&sn, &casted);
    // rhs_fn : HCPoint (n+1) = extend* n (hcDecode n k).
    let rhs_fn = Expr::apps(half.extend(c).clone(), [n.clone(), dec_n_k.clone()]);

    // pointwise via Fin.lastCases : ∀ (j : Fin (n+1)), lhs_fn j = rhs_fn j.
    // motive : fun (j : Fin (n+1)) => Eq Bool (lhs_fn j) (rhs_fn j).
    let lc_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&sn));
        let body = c.eq_bool(
            Expr::app(lhs_fn.clone(), j.clone()),
            Expr::app(rhs_fn.clone(), j.clone()),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&sn), body))
    };

    // ── last branch : lhs_fn (last n) = rhs_fn (last n).
    let last = c.last(&n);
    //   corr : lhs_fn (last n) = testBit <val> n   (hcDecode_castP_<half> n k (last n))
    let corr_last = Expr::apps(
        Expr::const_(Name::from_string(half.corr_lemma()), vec![]),
        [n.clone(), k.clone(), last.clone()],
    );
    //   <val> and the top-bit value lemma differ between halves.
    let (testbit_val, bit_value, top_bit) = match half {
        Half::Low => {
            // testBit (val k) n = false   via Nat.testBit_lt_pow n (val k) (k.isLt).
            let val_k = c.val(&p2n, &k);
            let tb = Expr::apps(c.testbit_const(), [val_k.clone(), c.val(&sn, &last)]);
            let bv = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_lt_pow"), vec![]),
                [n.clone(), val_k, c.islt(&n, &k)],
            );
            (tb, bv, c.bool_false())
        }
        Half::High => {
            // testBit (2^n + val k) n = true   via Nat.testBit_add_two_pow_self n (val k) (k.isLt).
            let val_k = c.val(&p2n, &k);
            let shifted = c.nadd(p2n.clone(), val_k.clone());
            let tb = Expr::apps(c.testbit_const(), [shifted, c.val(&sn, &last)]);
            let bv = Expr::apps(
                Expr::const_(Name::from_string("Nat.testBit_add_two_pow_self"), vec![]),
                [n.clone(), val_k, c.islt(&n, &k)],
            );
            (tb, bv, c.bool_true())
        }
    };
    //   ext_last : rhs_fn (last n) = top_bit   (extend*_last n (hcDecode n k)).
    let ext_last = Expr::apps(
        Expr::const_(Name::from_string(half.ext_last()), vec![]),
        [n.clone(), dec_n_k.clone()],
    );
    let rhs_at_last = Expr::app(rhs_fn.clone(), last.clone());
    let lhs_at_last = Expr::app(lhs_fn.clone(), last.clone());
    //   chain: lhs_fn(last) = testbit_val = top_bit = rhs_fn(last).
    let t_lo = c.trans_bool(
        lhs_at_last.clone(),
        testbit_val.clone(),
        top_bit.clone(),
        corr_last,
        bit_value,
    );
    let last_proof = c.trans_bool(
        lhs_at_last,
        top_bit.clone(),
        rhs_at_last.clone(),
        t_lo,
        c.symm_bool(rhs_at_last, top_bit, ext_last),
    );

    // ── castSucc branch : fun (i : Fin n) => lhs_fn (castSucc i) = rhs_fn (castSucc i).
    let cast_proof = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = d.fresh_local(c.fin_of(&n));
        let cs = c.cast_succ(&n, &i);
        //   restrict_eq : (fun i => lhs_fn (castSucc i)) = hcDecode n k   (function eq).
        let restrict_eq = Expr::apps(
            Expr::const_(Name::from_string(half.restrict_lemma()), vec![]),
            [n.clone(), k.clone()],
        );
        //   restricted_fn : the LHS of restrict_eq (fun i => lhs_fn (castSucc i)).
        let restricted_fn = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (i2_id, i2) = g.fresh_local(c.fin_of(&n));
            let body = Expr::app(lhs_fn.clone(), c.cast_succ(&n, &i2));
            g.finish_child(g.mk_lam(i2_id, BinderInfo::Default, c.fin_of(&n), body))
        };
        //   bit_eq : lhs_fn (castSucc i) = hcDecode n k i  via congrFun restrict_eq i.
        let bool_motive = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (u_id, _u) = g.fresh_local(c.fin_of(&n));
            g.finish_child(g.mk_lam(u_id, BinderInfo::Default, c.fin_of(&n), c.bool_.clone()))
        };
        let dec_at_i = Expr::app(dec_n_k.clone(), i.clone());
        let bit_eq = Expr::apps(
            c.congr_fun.clone(),
            [
                c.fin_of(&n),
                bool_motive,
                restricted_fn,
                dec_n_k.clone(),
                restrict_eq,
                i.clone(),
            ],
        );
        //   ext_cs : rhs_fn (castSucc i) = hcDecode n k i  (extend*_castSucc n (hcDecode n k) i).
        let ext_cs = Expr::apps(
            Expr::const_(Name::from_string(half.ext_castsucc()), vec![]),
            [n.clone(), dec_n_k.clone(), i.clone()],
        );
        let lhs_at_cs = Expr::app(lhs_fn.clone(), cs.clone());
        let rhs_at_cs = Expr::app(rhs_fn.clone(), cs);
        //   chain: lhs_fn(castSucc i) = hcDecode n k i = rhs_fn(castSucc i).
        let proof = c.trans_bool(
            lhs_at_cs.clone(),
            dec_at_i.clone(),
            rhs_at_cs.clone(),
            bit_eq,
            c.symm_bool(rhs_at_cs, dec_at_i, ext_cs),
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof))
    };

    // @Fin.lastCases n lc_motive last_proof cast_proof : ∀ j, lhs_fn j = rhs_fn j.
    let pointwise = Expr::apps(
        c.fin_last_cases.clone(),
        [n.clone(), lc_motive, last_proof, cast_proof],
    );

    // funext (Fin (n+1)) (fun _ => Bool) lhs_fn rhs_fn pointwise.
    let funext_motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (u_id, _u) = d.fresh_local(c.fin_of(&sn));
        d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.fin_of(&sn), c.bool_.clone()))
    };
    let proof = Expr::apps(
        c.funext.clone(),
        [c.fin_of(&sn), funext_motive, lhs_fn, rhs_fn, pointwise],
    );

    let e = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl ExtendBridgeConsts {
    fn testbit_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.testBit"), vec![])
    }
    fn bool_false(&self) -> Expr {
        Expr::const_(Name::from_string("Bool.false"), vec![])
    }
    fn bool_true(&self) -> Expr {
        Expr::const_(Name::from_string("Bool.true"), vec![])
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const BRIDGES: &[&str] = &[
        "BoolAnalysis.hcDecode_castP_castAdd_extendF",
        "BoolAnalysis.hcDecode_castP_addNat_extendT",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_extend_bridge()
            .expect("init_boolean_analysis_noise_extend_bridge");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_noise_extend_bridge()
            .expect("first init");
        env.init_boolean_analysis_noise_extend_bridge()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_noise_extend_bridge());
    }

    #[test]
    fn test_bridges_are_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name_str in BRIDGES {
            let name = Name::from_string(name_str);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{name_str} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name_str} is a Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name_str} proof must check: {e:?}"));
            let deps = env.axiom_deps(&name).expect("deps");
            let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name_str} must be axiom-free, got {dep_names:?}"
            );
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{name_str} must be Constructive"
            );
        }
    }
}

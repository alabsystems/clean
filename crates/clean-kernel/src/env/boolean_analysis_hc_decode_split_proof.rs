// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive `hcDecode`-correspondence lemmas through the off-diagonal cube
//! split — the pointwise bit identities the `E[χ_U] = 0` induction consumes.
//!
//! The off-diagonal split (`BoolAnalysis.hcSumSplit`) reindexes the `2^(n+1)`
//! cube sum into a LOW block (`castP ∘ castAdd`) and a HIGH block
//! (`castP ∘ addNat`), where `castP : Fin (2^n+2^n) → Fin (2^(n+1))` is the
//! `Eq.ndrec` transport along `e := (Nat.pow_two_succ n).symm`. This file pins
//! how `hcDecode` reads the bits of those reindexed points:
//!
//! - `Fin.val_castP_castAdd : ∀ (n : Nat) (k : Fin (2^n)),`
//!     `@Eq Nat (Fin.val (2^(n+1)) (castP (Fin.castAdd (2^n) (2^n) k))) (Fin.val (2^n) k)`
//!   — the LOW transport preserves the underlying value (`val (castAdd ..) ≡ val k`
//!     definitionally, and `castP` preserves it by `Fin.val_cast`, B1).
//!
//! - `Fin.val_castP_addNat : ∀ (n : Nat) (k : Fin (2^n)),`
//!     `@Eq Nat (Fin.val (2^(n+1)) (castP (Fin.addNat (2^n) (2^n) k)))`
//!     `        (Nat.add (2^n) (Fin.val (2^n) k))`
//!   — the HIGH transport shifts the value by `2^n` (`val (addNat ..) ≡ 2^n + val k`).
//!
//! - `BoolAnalysis.hcDecode_castP_castAdd : ∀ (n : Nat) (k : Fin (2^n)) (i : Fin (n+1)),`
//!     `@Eq Bool (BoolAnalysis.hcDecode (n+1) (castP (Fin.castAdd (2^n) (2^n) k)) i)`
//!     `         (Nat.testBit (Fin.val (2^n) k) (Fin.val (n+1) i))`
//!   — so the LOW point's `i`-th bit is the `i`-th bit of `k` directly. (This is
//!     where rung-4 `Nat.testBit_lt_pow` later collapses the high bit `i = n`.)
//!
//! - `BoolAnalysis.hcDecode_castP_addNat : ∀ (n : Nat) (k : Fin (2^n)) (i : Fin (n+1)),`
//!     `@Eq Bool (BoolAnalysis.hcDecode (n+1) (castP (Fin.addNat (2^n) (2^n) k)) i)`
//!     `         (Nat.testBit (Nat.add (2^n) (Fin.val (2^n) k)) (Fin.val (n+1) i))`
//!   — the HIGH point's `i`-th bit reads off `2^n + val k`. (Rung-4
//!     `Nat.testBit_add_two_pow_*` later splits this into the top bit `= true`
//!     and the low bits `= testBit (val k)`.)
//!
//! Each `hcDecode_*` is `congrArg (fun v => Nat.testBit v (Fin.val (n+1) i))` of
//! the corresponding `Fin.val_castP_*` (the `hcDecode (n+1) K i` defeq-unfolds to
//! `Nat.testBit (Fin.val (2^(n+1)) K) (Fin.val (n+1) i)`).
//!
//! All kernel-checked, `ProofQuality::Constructive` (empty admitted-axiom
//! closure): leaves are `Fin.val_cast` (B1) / `congrArg` / `Eq.*` built-ins.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct HcDecodeSplitConsts {
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    fin_val: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_pow: Expr,
    nat_testbit: Expr,
    two: Expr,
    hc_decode: Expr,
    cast_add: Expr,
    add_nat: Expr,
    pow_two_succ: Expr,
    fin_val_cast: Expr,
    // Eq.{1} over Nat ; congrArg ; Eq.symm.
    eq1: Expr,
    eq_symm: Expr,
    congr_arg: Expr,
    eq_ndrec_fin: Expr,
    // restriction-correspondence support: Fin.castSucc + funext.
    fin_cast_succ: Expr,
    funext: Expr,
    hcpoint: Expr,
    // HIGH-restriction support: Fin.isLt, testBit_add_two_pow_lo, Eq.trans over Bool.
    fin_islt: Expr,
    testbit_add_lo: Expr,
    eq_trans_bool: Expr,
}

impl HcDecodeSplitConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero);
        let two = Expr::app(nat_succ.clone(), one);
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            nat_succ,
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_testbit: Expr::const_(Name::from_string("Nat.testBit"), vec![]),
            two,
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            cast_add: Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
            add_nat: Expr::const_(Name::from_string("Fin.addNat"), vec![]),
            pow_two_succ: Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
            fin_val_cast: Expr::const_(Name::from_string("Fin.val_cast"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1.clone()]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            // funext.{u,v} : here both domain (Fin n) and codomain (Bool) are
            // in Type 0 = Sort 1, so u = v = 1.
            funext: Expr::const_(Name::from_string("funext"), vec![l1.clone(), l1.clone()]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            testbit_add_lo: Expr::const_(Name::from_string("Nat.testBit_add_two_pow_lo"), vec![]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two.clone(), n.clone()])
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    /// `@Fin.val n i`.
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    /// `@Eq Nat l r`.
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_.clone(), l, r])
    }
    /// `Nat.testBit v j`.
    fn testbit(&self, v: Expr, j: Expr) -> Expr {
        Expr::apps(self.nat_testbit.clone(), [v, j])
    }

    /// `castP n M := @Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) M (2^(n+1))
    ///                 (Eq.symm (Nat.pow_two_succ n))`, exactly the split's
    /// transport `cast_fin (2^n+2^n) (2^(n+1)) M (Eq.symm (pow_two_succ n))`.
    fn cast_p(&self, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> (Expr, Expr, Expr) {
        let p2n = self.pow2(n);
        let sum_pow = self.nadd(p2n.clone(), p2n.clone()); // 2^n + 2^n
        let p2sn = self.pow2(&self.succ(n.clone())); // 2^(n+1)
                                                     // e_fwd : 2^(n+1) = 2^n+2^n ; e : 2^n+2^n = 2^(n+1).
        let e_fwd = Expr::app(self.pow_two_succ.clone(), n.clone());
        let e = Expr::apps(
            self.eq_symm.clone(),
            [self.nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        let casted = Expr::apps(
            self.eq_ndrec_fin.clone(),
            [
                self.nat.clone(),
                sum_pow.clone(),
                motive,
                mapped.clone(),
                p2sn.clone(),
                e.clone(),
            ],
        );
        (casted, sum_pow, e)
    }

    /// `@Fin.val_cast (2^(n+1)) (2^n+2^n) M (Eq.symm (pow_two_succ n))`
    ///   : Eq Nat (Fin.val (2^(n+1)) (castP n M)) (Fin.val (2^n+2^n) M).
    fn val_cast_app(&self, n: &Expr, mapped: &Expr, sum_pow: &Expr, e: &Expr) -> Expr {
        let p2sn = self.pow2(&self.succ(n.clone()));
        Expr::apps(
            self.fin_val_cast.clone(),
            [p2sn, sum_pow.clone(), mapped.clone(), e.clone()],
        )
    }

    /// `@congrArg Nat Nat x y (fun v => Nat.testBit v j) h`.
    fn congr_testbit(&self, x: Expr, y: Expr, j: Expr, parent: &EnvDeclBuilder, h: Expr) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = mb.fresh_local(self.nat.clone());
            let body = self.testbit(v, j);
            mb.finish_child(mb.mk_lam(v_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.nat.clone(), self.bool_.clone(), x, y, f, h],
        )
    }
}

/// Build the `Fin.val_castP_*` value-equality lemma for an index map
/// (`Fin.castAdd` or `Fin.addNat`), with RHS `rhs_val(n, k)`.
fn build_val_castp<F>(c: &HcDecodeSplitConsts, idx_map: &Expr, rhs_val: F) -> (Expr, Expr)
where
    F: Fn(&HcDecodeSplitConsts, &Expr, &Expr) -> Expr,
{
    // type: ∀ (n : Nat) (k : Fin (2^n)),
    //   Eq Nat (Fin.val (2^(n+1)) (castP n (idx_map (2^n)(2^n) k))) (rhs_val n k).
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
        let (casted, _sum, _e) = c.cast_p(&b, &n, &mapped);
        let lhs = c.val(&c.pow2(&c.succ(n.clone())), &casted);
        let body = c.eq_nat(lhs, rhs_val(c, &n, &k));
        let r = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), body);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    // value: fun n k => Fin.val_cast (2^(n+1)) (2^n+2^n) (idx_map ..) (Eq.symm (pow_two_succ n)).
    //   B1's RHS `Fin.val (2^n+2^n) (idx_map ..)` is defeq to `rhs_val n k`
    //   (castAdd: ≡ Fin.val (2^n) k ; addNat: ≡ Nat.add (2^n) (Fin.val (2^n) k)).
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
        let (_casted, sum_pow, e) = c.cast_p(&b, &n, &mapped);
        let body = c.val_cast_app(&n, &mapped, &sum_pow, &e);
        let r = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    (type_, value)
}

/// Build a `hcDecode_castP_*` correspondence lemma for an index map, with the
/// testBit numerator `rhs_val(n, k)` (matching the `Fin.val_castP_*` RHS) and a
/// reference to the corresponding `Fin.val_castP_*` theorem `val_lemma`.
fn build_hc_decode_corr<F>(
    c: &HcDecodeSplitConsts,
    idx_map: &Expr,
    val_lemma_name: &str,
    rhs_val: F,
) -> (Expr, Expr)
where
    F: Fn(&HcDecodeSplitConsts, &Expr, &Expr) -> Expr,
{
    // type: ∀ (n : Nat) (k : Fin (2^n)) (i : Fin (n+1)),
    //   Eq Bool (hcDecode (n+1) (castP n (idx_map ..)) i)
    //           (Nat.testBit (rhs_val n k) (Fin.val (n+1) i)).
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let (i_id, i) = b.fresh_local(c.fin_of(&sn));
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
        let (casted, _sum, _e) = c.cast_p(&b, &n, &mapped);
        let decoded = Expr::apps(c.hc_decode.clone(), [sn.clone(), casted, i.clone()]);
        let rhs = c.testbit(rhs_val(c, &n, &k), c.val(&sn, &i));
        let body = c.eq_bool(decoded, rhs);
        let r = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&sn), body);
        let r = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), r);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    // value: fun n k i =>
    //   congrArg (fun v => Nat.testBit v (Fin.val (n+1) i)) (val_lemma n k)
    //   — hcDecode (n+1) K i ≡ Nat.testBit (Fin.val (2^(n+1)) K) (Fin.val (n+1) i),
    //     and val_lemma rewrites the first testBit arg to rhs_val n k.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let (i_id, i) = b.fresh_local(c.fin_of(&sn));
        let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
        let (casted, _sum, _e) = c.cast_p(&b, &n, &mapped);
        let lhs_val = c.val(&c.pow2(&sn), &casted); // Fin.val (2^(n+1)) (castP ..)
        let rhs_v = rhs_val(c, &n, &k);
        let val_lemma = Expr::apps(
            Expr::const_(Name::from_string(val_lemma_name), vec![]),
            [n.clone(), k.clone()],
        );
        let proof = c.congr_testbit(lhs_val, rhs_v, c.val(&sn, &i), &b, val_lemma);
        let r = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sn), proof);
        let r = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), r);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    (type_, value)
}

impl HcDecodeSplitConsts {
    /// `BoolAnalysis.HCPoint n` ≡ `Fin n → Bool`.
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    /// `@Fin.castSucc n i : Fin (n+1)`.
    fn cast_succ(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [n.clone(), i.clone()])
    }
    /// `fun (_ : Fin n) => Bool` — the constant codomain motive for `funext`.
    fn bool_motive(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (i_id, _i) = mb.fresh_local(self.fin_of(n));
        mb.finish_child(mb.mk_lam(
            i_id,
            BinderInfo::Default,
            self.fin_of(n),
            self.bool_.clone(),
        ))
    }
}

/// Build a restriction-correspondence lemma: the `(n+1)`-cube point obtained by
/// decoding a LOW/HIGH split index, RESTRICTED to its first `n` coordinates (via
/// `Fin.castSucc`), is exactly the `n`-cube point `hcDecode n k`. As a function
/// equality on `HCPoint n`:
///
/// ```text
/// ∀ (n : Nat) (k : Fin (2^n)),
///   @Eq (HCPoint n)
///       (fun (i : Fin n) => hcDecode (n+1) (castP (idx_map (2^n) (2^n) k)) (Fin.castSucc n i))
///       (hcDecode n k)
/// ```
///
/// Pointwise at `i`, `corr_lemma n k (castSucc n i)` has type
/// `hcDecode (n+1) (castP ..) (castSucc n i) = testBit (val k) (val (castSucc n i))`,
/// and `val (n+1) (castSucc n i) ≡ val n i` definitionally while
/// `hcDecode n k i ≡ testBit (val k) (val n i)` definitionally, so that term
/// proves the pointwise goal `restricted i = hcDecode n k i` by defeq. `funext`
/// lifts it to the function equality. (For the HIGH block the bit RHS reads off
/// `2^n + val k`; since we only restrict to coordinates `i < n`, the low bits of
/// `2^n + val k` agree with those of `val k` — but that low-bit agreement needs
/// `testBit_add_two_pow_lo`, NOT a pure defeq, so the HIGH restriction is built
/// separately by `build_hc_decode_restrict_hi`.)
fn build_hc_decode_restrict_lo(
    c: &HcDecodeSplitConsts,
    idx_map: &Expr,
    corr_lemma_name: &str,
) -> (Expr, Expr) {
    // restricted(n, k) := fun (i : Fin n) =>
    //   hcDecode (n+1) (castP (idx_map (2^n) (2^n) k)) (castSucc n i)
    let restricted =
        |c: &HcDecodeSplitConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let sn = c.succ(n.clone());
            let p2n = c.pow2(n);
            let (i_id, i) = b.fresh_local(c.fin_of(n));
            let mapped = Expr::apps(idx_map.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
            let (casted, _sum, _e) = c.cast_p(&b, n, &mapped);
            let decoded = Expr::apps(c.hc_decode.clone(), [sn, casted, c.cast_succ(n, &i)]);
            b.finish_child(b.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), decoded))
        };
    // rhs(n, k) := hcDecode n k.
    let rhs = |c: &HcDecodeSplitConsts, n: &Expr, k: &Expr| -> Expr {
        Expr::apps(c.hc_decode.clone(), [n.clone(), k.clone()])
    };

    // type: ∀ n (k : Fin (2^n)), @Eq (HCPoint n) (restricted n k) (hcDecode n k).
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let lhs = restricted(c, &b, &n, &k);
        let body = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [c.hcpoint_of(&n), lhs, rhs(c, &n, &k)],
        );
        let r = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), body);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    // value: fun n k =>
    //   funext (Fin n) (fun _ => Bool) (restricted n k) (hcDecode n k)
    //     (fun (i : Fin n) => corr_lemma n k (castSucc n i))
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(c.fin_of(&n));
            let body = Expr::apps(
                Expr::const_(Name::from_string(corr_lemma_name), vec![]),
                [n.clone(), k.clone(), c.cast_succ(&n, &i)],
            );
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), body))
        };

        let proof = Expr::apps(
            c.funext.clone(),
            [
                c.fin_of(&n),
                c.bool_motive(&b, &n),
                restricted(c, &b, &n, &k),
                rhs(c, &n, &k),
                pointwise,
            ],
        );
        let r = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), proof);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    (type_, value)
}

/// Build the HIGH restriction correspondence: restricting the decoded
/// high-block point (`castP ∘ addNat`) to its first `n` coordinates ALSO
/// recovers `hcDecode n k`. As a function equality on `HCPoint n`:
///
/// ```text
/// hcDecode_restrict_addNat : ∀ (n : Nat) (k : Fin (2^n)),
///   @Eq (HCPoint n)
///       (fun (i : Fin n) =>
///          hcDecode (n+1) (castP (Fin.addNat (2^n) (2^n) k)) (Fin.castSucc n i))
///       (hcDecode n k)
/// ```
///
/// Pointwise at `i`, the high point's `i`-th bit is `testBit (2^n + val k)
/// (val (castSucc n i))`; for `i < n` that low bit equals `testBit (val k)
/// (val i)` (= `hcDecode n k i`) by `Nat.testBit_add_two_pow_lo` — NOT a pure
/// defeq, so the proof is an `Eq.trans` of `hcDecode_castP_addNat n k
/// (castSucc n i)` and `testBit_add_two_pow_lo n (val k) (val i) (Fin.isLt k)
/// (Fin.isLt i)`, then `funext`. The bound hypotheses are exactly the Fin
/// witnesses `k.isLt : val k < 2^n` and `i.isLt : val i < n`.
fn build_hc_decode_restrict_hi(c: &HcDecodeSplitConsts) -> (Expr, Expr) {
    let restricted =
        |c: &HcDecodeSplitConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr| -> Expr {
            let mut b = EnvDeclBuilder::child_of(parent);
            let sn = c.succ(n.clone());
            let p2n = c.pow2(n);
            let (i_id, i) = b.fresh_local(c.fin_of(n));
            let mapped = Expr::apps(c.add_nat.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
            let (casted, _sum, _e) = c.cast_p(&b, n, &mapped);
            let decoded = Expr::apps(c.hc_decode.clone(), [sn, casted, c.cast_succ(n, &i)]);
            b.finish_child(b.mk_lam(i_id, BinderInfo::Default, c.fin_of(n), decoded))
        };
    let rhs = |c: &HcDecodeSplitConsts, n: &Expr, k: &Expr| -> Expr {
        Expr::apps(c.hc_decode.clone(), [n.clone(), k.clone()])
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
        let lhs = restricted(c, &b, &n, &k);
        let body = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [c.hcpoint_of(&n), lhs, rhs(c, &n, &k)],
        );
        let r = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), body);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let sn = c.succ(n.clone());
        let p2n = c.pow2(&n);
        let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

        // pointwise : fun (i : Fin n) => Eq.trans step_corr step_lo
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(c.fin_of(&n));
            let cs_i = c.cast_succ(&n, &i);
            let val_k = c.val(&p2n, &k);
            let val_i = c.val(&n, &i);

            // a := hcDecode (n+1) (castP (addNat k)) (castSucc n i)
            let a = {
                let mapped = Expr::apps(c.add_nat.clone(), [p2n.clone(), p2n.clone(), k.clone()]);
                let (casted, _s, _e) = c.cast_p(&d, &n, &mapped);
                Expr::apps(c.hc_decode.clone(), [sn.clone(), casted, cs_i.clone()])
            };
            // mid := testBit (2^n + val k) (val (n+1) (castSucc n i))
            //   ≡ testBit (2^n + val k) (val n i)  (val(castSucc)≡val, defeq)
            let mid = c.testbit(c.nadd(p2n.clone(), val_k.clone()), c.val(&sn, &cs_i));
            // mid' := testBit (2^n + val k) (val n i)  — the form testBit_add_two_pow_lo states.
            let mid_canon = c.testbit(c.nadd(p2n.clone(), val_k.clone()), val_i.clone());
            // rhs_bit := testBit (val k) (val n i) ≡ hcDecode n k i (defeq).
            let rhs_bit = c.testbit(val_k.clone(), val_i.clone());

            // step_corr : a = mid  (hcDecode_castP_addNat n k (castSucc n i))
            let step_corr = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.hcDecode_castP_addNat"),
                    vec![],
                ),
                [n.clone(), k.clone(), cs_i.clone()],
            );
            // h_k : Nat.lt (val k) (2^n)  := @Fin.isLt (2^n) k
            let h_k = Expr::apps(c.fin_islt.clone(), [p2n.clone(), k.clone()]);
            // h_i : Nat.lt (val i) n      := @Fin.isLt n i
            let h_i = Expr::apps(c.fin_islt.clone(), [n.clone(), i.clone()]);
            // step_lo : testBit (2^n + val k) (val i) = testBit (val k) (val i)
            // Binder order is (n) (k) (hk : lt k 2^n) (i) (hi : lt i n) — the
            // bound on k precedes the index i.
            let step_lo = Expr::apps(
                c.testbit_add_lo.clone(),
                [n.clone(), val_k.clone(), h_k, val_i.clone(), h_i],
            );

            // Eq.trans : a = mid_canon (= mid by defeq) and mid_canon = rhs_bit.
            // The kernel retypes `mid` ≡ `mid_canon` and `rhs_bit` ≡ `hcDecode n k i`.
            let body = Expr::apps(
                c.eq_trans_bool.clone(),
                [c.bool_.clone(), a, mid_canon, rhs_bit, step_corr, step_lo],
            );
            // silence unused `mid`: it documents the defeq target.
            let _ = mid;
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), body))
        };

        let proof = Expr::apps(
            c.funext.clone(),
            [
                c.fin_of(&n),
                c.bool_motive(&b, &n),
                restricted(c, &b, &n, &k),
                rhs(c, &n, &k),
                pointwise,
            ],
        );
        let r = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), proof);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };
    (type_, value)
}

impl Environment {
    /// Register the four `hcDecode`-correspondence lemmas (B2) as kernel-checked,
    /// constructive theorems. Idempotent.
    pub(crate) fn register_hc_decode_split_theorems(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_hc_sum_split_theorem()?; // brings Fin.val_cast (B1), castP deps, hcDecode

        let c = HcDecodeSplitConsts::new();

        // RHS-value builders: castAdd ⇒ Fin.val (2^n) k ; addNat ⇒ 2^n + Fin.val (2^n) k.
        // castAdd RHS: Fin.val (2^n) k.
        let rhs_lo = |c: &HcDecodeSplitConsts, n: &Expr, k: &Expr| -> Expr { c.val(&c.pow2(n), k) };
        // addNat RHS: Nat.add (2^n) (Fin.val (2^n) k).
        let rhs_hi = |c: &HcDecodeSplitConsts, n: &Expr, k: &Expr| -> Expr {
            c.nadd(c.pow2(n), c.val(&c.pow2(n), k))
        };

        if self
            .get_const(&Name::from_string("Fin.val_castP_castAdd"))
            .is_none()
        {
            let (type_, value) = build_val_castp(&c, &c.cast_add, rhs_lo);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.val_castP_castAdd"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        if self
            .get_const(&Name::from_string("Fin.val_castP_addNat"))
            .is_none()
        {
            let (type_, value) = build_val_castp(&c, &c.add_nat, rhs_hi);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("Fin.val_castP_addNat"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcDecode_castP_castAdd"))
            .is_none()
        {
            let (type_, value) =
                build_hc_decode_corr(&c, &c.cast_add, "Fin.val_castP_castAdd", rhs_lo);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcDecode_castP_castAdd"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcDecode_castP_addNat"))
            .is_none()
        {
            let (type_, value) =
                build_hc_decode_corr(&c, &c.add_nat, "Fin.val_castP_addNat", rhs_hi);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcDecode_castP_addNat"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        // LOW restriction correspondence: restricting the decoded low-block point
        // to its first n coordinates recovers `hcDecode n k` exactly (pure defeq
        // on the bit form + funext). This is the keystone that gives the two
        // half-sums of the off-diagonal split a COMMON `chi n` sub-sum.
        self.init_funext()?;
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcDecode_restrict_castAdd"))
            .is_none()
        {
            let (type_, value) =
                build_hc_decode_restrict_lo(&c, &c.cast_add, "BoolAnalysis.hcDecode_castP_castAdd");
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcDecode_restrict_castAdd"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        // HIGH restriction correspondence: the high-block point ALSO restricts to
        // `hcDecode n k` — but the low-bit agreement of `2^n + val k` with `val k`
        // is `Nat.testBit_add_two_pow_lo` (not defeq), discharged with the Fin
        // bound witnesses `k.isLt` / `i.isLt`.
        self.register_nat_testbit_add_two_pow_proof()?;
        if self
            .get_const(&Name::from_string("BoolAnalysis.hcDecode_restrict_addNat"))
            .is_none()
        {
            let (type_, value) = build_hc_decode_restrict_hi(&c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("BoolAnalysis.hcDecode_restrict_addNat"),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_hc_decode_split_theorems()
            .expect("register_hc_decode_split_theorems");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&Name::from_string(name)),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(name))
                .expect("deps")
                .is_empty(),
            "{name}'s transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_val_castp_castadd_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.val_castP_castAdd");
    }

    #[test]
    fn test_val_castp_addnat_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "Fin.val_castP_addNat");
    }

    #[test]
    fn test_hc_decode_castp_castadd_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.hcDecode_castP_castAdd");
    }

    #[test]
    fn test_hc_decode_castp_addnat_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.hcDecode_castP_addNat");
    }

    #[test]
    fn test_hc_decode_restrict_castadd_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.hcDecode_restrict_castAdd");
    }

    #[test]
    fn test_hc_decode_restrict_addnat_is_constructive_theorem() {
        let env = make_env();
        check_constructive(&env, "BoolAnalysis.hcDecode_restrict_addNat");
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Connective-commutation/forward and `subst`-elimination proof builders plus the
//! spine-argument accessors for the Isabelle Pure translator (`conn_forward_disj`,
//! `conn_comm_disj`/`conj`, `subst_elim_body`, `spine_terms`, `proof_spine_args`).
//! Moved verbatim from the original single-file `def_axioms` module; behaviour is
//! byte-identical.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaTerm};
use super::super::*;
/// `disj_forward` body: from `h : disj P Q ≡ ∀C.(P→C)→(Q→C)→C`, `f : P → R`,
/// `g : Q → S`, prove `disj R S ≡ ∀C.(R→C)→(S→C)→C` as
/// `fun (C:Prop)(hr:R→C)(hs:S→C) => h C (fun p => hr (f p)) (fun q => hs (g q))`.
/// `h`, `f`, `g` are the (closed-modulo-enclosing-binders) embedded hypothesis
/// terms; fresh fvars + `abstract_fvar` keep the de Bruijn bookkeeping correct.
#[allow(clippy::too_many_arguments)]
pub(crate) fn conn_forward_disj(
    h: &Expr,
    p: &Expr,
    q: &Expr,
    r: &Expr,
    s: &Expr,
    f: &Expr,
    g: &Expr,
) -> Expr {
    let fc = FVarId::new(0xC0AC_0001);
    let fhr = FVarId::new(0xC0AC_0002);
    let fhs = FVarId::new(0xC0AC_0003);
    let fp = FVarId::new(0xC0AC_0004);
    let fq = FVarId::new(0xC0AC_0005);
    let c = Expr::fvar(fc);
    let hr = Expr::fvar(fhr);
    let hs = Expr::fvar(fhs);
    // fun (p:P) => hr (f p) : C
    let hr_fp = Expr::app(hr.clone(), Expr::app(f.clone(), Expr::fvar(fp)));
    let case_p = Expr::lam(BinderInfo::Default, p.clone(), hr_fp.abstract_fvar(fp));
    // fun (q:Q) => hs (g q) : C
    let hs_gq = Expr::app(hs.clone(), Expr::app(g.clone(), Expr::fvar(fq)));
    let case_q = Expr::lam(BinderInfo::Default, q.clone(), hs_gq.abstract_fvar(fq));
    // h C case_p case_q : C
    let applied = Expr::apps(h.clone(), [c.clone(), case_p, case_q]);
    // fun (hs:S→C) => applied
    let l_hs = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(s.clone(), c.clone()),
        applied.abstract_fvar(fhs),
    );
    // fun (hr:R→C) => l_hs
    let l_hr = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(r.clone(), c.clone()),
        l_hs.abstract_fvar(fhr),
    );
    // fun (C:Prop) => l_hr
    Expr::lam(BinderInfo::Default, Expr::prop(), l_hr.abstract_fvar(fc))
}

/// `disj_comm` body: from `h : disj P Q ≡ ∀C.(P→C)→(Q→C)→C`, prove
/// `disj Q P ≡ ∀C.(Q→C)→(P→C)→C` as `fun (C:Prop)(hq:Q→C)(hp:P→C) => h C hp hq`.
/// `h` is the (closed) embedded hypothesis term; the binders are tracked by fresh
/// fvars and abstracted with `abstract_fvar`, so the de Bruijn bookkeeping is
/// automatic and composes correctly under the caller's enclosing binders.
pub(crate) fn conn_comm_disj(h: &Expr, p: &Expr, q: &Expr) -> Expr {
    let fc = FVarId::new(0xC0AA_0001);
    let fhq = FVarId::new(0xC0AA_0002);
    let fhp = FVarId::new(0xC0AA_0003);
    let c = Expr::fvar(fc);
    let hq = Expr::fvar(fhq);
    let hp = Expr::fvar(fhp);
    // h C hp hq : C
    let applied = Expr::apps(h.clone(), [c.clone(), hp.clone(), hq.clone()]);
    // fun (hp : P → C) => applied
    let l_hp = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(p.clone(), c.clone()),
        applied.abstract_fvar(fhp),
    );
    // fun (hq : Q → C) => l_hp
    let l_hq = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(q.clone(), c.clone()),
        l_hp.abstract_fvar(fhq),
    );
    // fun (C : Prop) => l_hq
    Expr::lam(BinderInfo::Default, Expr::prop(), l_hq.abstract_fvar(fc))
}

/// `conj_comm` body: from `h : conj P Q ≡ ∀C.(P→Q→C)→C`, prove
/// `conj Q P ≡ ∀C.(Q→P→C)→C` as
/// `fun (C:Prop)(k:Q→P→C) => h C (fun (p:P)(q:Q) => k q p)`. Fresh-fvar based, as
/// in [`conn_comm_disj`].
pub(crate) fn conn_comm_conj(h: &Expr, p: &Expr, q: &Expr) -> Expr {
    let fc = FVarId::new(0xC0AB_0001);
    let fk = FVarId::new(0xC0AB_0002);
    let fp = FVarId::new(0xC0AB_0003);
    let fq = FVarId::new(0xC0AB_0004);
    let c = Expr::fvar(fc);
    let k = Expr::fvar(fk);
    let pf = Expr::fvar(fp);
    let qf = Expr::fvar(fq);
    // inner: fun (p:P)(q:Q) => k q p
    let kqp = Expr::apps(k.clone(), [qf.clone(), pf.clone()]);
    let inner_q = Expr::lam(BinderInfo::Default, q.clone(), kqp.abstract_fvar(fq));
    let inner = Expr::lam(BinderInfo::Default, p.clone(), inner_q.abstract_fvar(fp));
    // h C inner : C
    let applied = Expr::apps(h.clone(), [c.clone(), inner]);
    // fun (k : Q → P → C) => applied
    let k_ty = Expr::arrow(q.clone(), Expr::arrow(p.clone(), c.clone()));
    let l_k = Expr::lam(BinderInfo::Default, k_ty, applied.abstract_fvar(fk));
    // fun (C : Prop) => l_k
    Expr::lam(BinderInfo::Default, Expr::prop(), l_k.abstract_fvar(fc))
}

/// Build the body of an equality-elimination (`subst`-shaped) rule from its
/// discharged premises: the conclusion `motive b` follows from a premise
/// `motive a` (same `motive`) plus an equation premise relating `a` and `b` in
/// either direction, via `@Eq.subst`. This is the embedded shape of HOL's derived
/// `subst` / `iffD1` / `iffD2` / `rev_iffD*` rules (e.g.
/// `(t = s) ⟹ P s ⟹ P t` or `(P = Q) ⟹ Q ⟹ P`), whose recorded proofs are
/// intricate def-raw chains; the statement alone determines a direct proof.
///
/// `premise_tys` are the embedded premise propositions under the `n` premise
/// binders (innermost premise = bvar 0). Returns `None` unless exactly one
/// matching `(motive a, equation)` pair exists. The kernel re-checks the
/// `@Eq.subst` against the embedded statement, so a wrong match is rejected.
pub(crate) fn subst_elim_body(premise_tys: &[Expr], concl_e: &Expr, n: usize) -> Option<Expr> {
    let bvar = |pos: usize| Expr::bvar((n - 1 - pos) as u32);

    // Equality **symmetry** (`sym`): the conclusion is an equation `@Eq α t s`
    // and some premise is the *swapped* equation `@Eq α s t` (same element type
    // `α`, operands transposed, `s ≠ t` so this is not the reflexive case the
    // conclusion-reflexivity arm already discharges). Then the conclusion follows
    // directly by `@Eq.symm α s t h` where `h : @Eq α s t` is that premise. This
    // is HOL's `sym` (`s = t ⟹ t = s`, under a leading sort-constraint premise
    // that embeds to a trivial `True` binder) — a very high fan-out equality rule
    // whose recorded proof reconstructs the `HOL.sym`/`equal_elim` congruence tower
    // and translates to a kernel-rejected term (the `expected=fun got=Eq | node=
    // AbsP` sort-abstraction wall). `Eq.symm` shares HOL types' single object
    // universe with `Prop` (`obj_level()`), so the same level serves both a genuine
    // object equation and a `Prop`-level one. Attempted before the application-motive
    // scan so a bare symmetry never mis-routes through it. The kernel re-checks the
    // `@Eq.symm` against the embedded statement, so a wrong match is rejected —
    // never miscounted.
    if let Some((alpha, t, s)) = eq_three_parts(concl_e) {
        for (pos_eq, eq_ty) in premise_tys.iter().enumerate() {
            let Some((beta, x, y)) = eq_three_parts(eq_ty) else {
                continue;
            };
            if beta == alpha && x == s && y == t && s != t {
                return Some(Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [alpha, s, t, bvar(pos_eq)],
                ));
            }
        }
    }

    // Identity-motive (`Prop`-level) elimination: the conclusion `C` is a bare
    // proposition, a premise `D` is a bare proposition, and an equation premise
    // relates `C` and `D` (`@Eq Prop C D` / `@Eq Prop D C`). Then `C` follows by
    // `@Eq.mp D C heq hD` (transporting `hD : D` along `D = C`). This is the shape
    // of HOL's `iffD1` / `iffD2` / `rev_iffD*` (`(Q = P) ⟹ Q ⟹ P`, where the
    // "motive" is the identity and the conclusion is not an application).
    for (pos_hd, hd_ty) in premise_tys.iter().enumerate() {
        for (pos_eq, eq_ty) in premise_tys.iter().enumerate() {
            if pos_eq == pos_hd {
                continue;
            }
            let Some((alpha, x, y)) = eq_three_parts(eq_ty) else {
                continue;
            };
            // Only the Prop-level identity case (`α = Prop`); otherwise the
            // application-motive branch below handles it.
            if !matches!(alpha.kind(), clean_kernel::expr::ExprKind::Sort(l) if *l == Level::zero())
            {
                continue;
            }
            // Need `heq : D = C` to transport `hD : D` to `C` via `Eq.mp`.
            let heq_dc = if x == *hd_ty && y == *concl_e {
                bvar(pos_eq) // `D = C`
            } else if x == *concl_e && y == *hd_ty {
                // `C = D` → symm → `D = C`.
                Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [alpha.clone(), concl_e.clone(), hd_ty.clone(), bvar(pos_eq)],
                )
            } else {
                continue;
            };
            // @Eq.mp D C heq_dc hD : C  (Eq.mp at Prop level → level 0).
            return Some(Expr::apps(
                Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                [hd_ty.clone(), concl_e.clone(), heq_dc, bvar(pos_hd)],
            ));
        }
    }

    // Application-motive elimination: conclusion `App(motive, b)`.
    let (motive, b) = app_parts(concl_e)?;
    // Find the `motive a` premise (same head `motive`, any argument `a`).
    for (pos_hpa, hpa_ty) in premise_tys.iter().enumerate() {
        let Some((m2, a)) = app_parts(hpa_ty) else {
            continue;
        };
        if m2 != motive || a == b {
            continue;
        }
        // Find an equation premise relating `a` and `b` (either direction).
        for (pos_eq, eq_ty) in premise_tys.iter().enumerate() {
            if pos_eq == pos_hpa {
                continue;
            }
            let Some((alpha, x, y)) = eq_three_parts(eq_ty) else {
                continue;
            };
            // We need `heq : a = b`. The premise is `x = y`; orient it.
            let heq_ab = if x == a && y == b {
                bvar(pos_eq) // already `a = b`
            } else if x == b && y == a {
                // `b = a` → symm → `a = b`.
                Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [alpha.clone(), b.clone(), a.clone(), bvar(pos_eq)],
                )
            } else {
                continue;
            };
            // @Eq.subst α motive a b heq_ab (motive a) : motive b
            return Some(Expr::apps(
                Expr::const_str_levels("Eq.subst", vec![obj_level()]),
                [alpha, motive, a, b, heq_ab, bvar(pos_hpa)],
            ));
        }
    }
    None
}

/// All term-typed arguments on a spine, in order.
pub(crate) fn spine_terms(spine: &[SpineArg]) -> Vec<&IsaTerm> {
    spine
        .iter()
        .filter_map(|a| match a {
            SpineArg::Term(t) => Some(t),
            SpineArg::Proof(_) => None,
        })
        .collect()
}

/// All proof-typed arguments on a spine, in order (the `IsaProof` nodes, for
/// expected-type-directed translation).
pub(crate) fn proof_spine_args(spine: &[SpineArg]) -> Vec<&IsaProof> {
    spine
        .iter()
        .filter_map(|a| match a {
            SpineArg::Proof(p) => Some(p),
            SpineArg::Term(_) => None,
        })
        .collect()
}

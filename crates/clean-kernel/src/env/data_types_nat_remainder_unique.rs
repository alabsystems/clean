// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Constructive uniqueness of bounded Euclidean remainders over the real Nat seed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::FVarId;
use crate::{BinderInfo, Expr, Level, Name};

const QUOTIENT_LE: &str = "Nat.divmodAux.quotient_le_of_bounded_remainder";
const REMAINDER_UNIQUE: &str = "Nat.divmodAux.remainder_unique";
const MOD_DECOMPOSITION: &str = "Nat.divmodAux.mod_eq_of_decomposition";

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn call(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat() -> Expr {
    c("Nat")
}
fn one_level() -> Level {
    Level::succ(Level::zero())
}
fn add(a: Expr, b: Expr) -> Expr {
    call("Nat.add", [a, b])
}
fn mul(a: Expr, b: Expr) -> Expr {
    call("Nat.mul", [a, b])
}
fn sum(n: Expr, q: Expr, r: Expr) -> Expr {
    add(mul(q, n), r)
}
fn le(a: Expr, b: Expr) -> Expr {
    call("Nat.le", [a, b])
}
fn lt(a: Expr, b: Expr) -> Expr {
    call("Nat.lt", [a, b])
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one_level()]),
        [nat(), a, b],
    )
}
fn symm(a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![one_level()]),
        [nat(), a, b, proof],
    )
}
fn trans(a: Expr, b: Expr, d: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![one_level()]),
        [nat(), a, b, d, first, second],
    )
}
fn lambda(parent: &EnvDeclBuilder, ty: Expr, body: impl FnOnce(Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (id, local) = b.fresh_local(ty.clone());
    let out = b.mk_lam(id, BinderInfo::Default, ty, body(local));
    b.finish_child(out)
}
fn subst(from: Expr, to: Expr, equality: Expr, motive: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![one_level()]),
        [nat(), motive, from, to, equality, proof],
    )
}
fn bind(b: &mut EnvDeclBuilder, params: &mut Vec<(FVarId, Expr)>, ty: Expr) -> Expr {
    let (id, local) = b.fresh_local(ty.clone());
    params.push((id, ty));
    local
}
fn close(
    name: &str,
    b: EnvDeclBuilder,
    params: Vec<(FVarId, Expr)>,
    mut ty: Expr,
    mut proof: Expr,
) -> Declaration {
    for (id, domain) in params.into_iter().rev() {
        ty = b.mk_pi(id, BinderInfo::Default, domain.clone(), ty);
        proof = b.mk_lam(id, BinderInfo::Default, domain, proof);
    }
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: b.finish(ty),
        value: b.finish(proof),
    }
}

// A bounded RIGHT remainder rules out a larger LEFT quotient, without a
// bound on the left remainder or an independently assumed positive modulus.
fn quotient_le() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let n = bind(&mut b, &mut params, nat());
    let q = bind(&mut b, &mut params, nat());
    let p = bind(&mut b, &mut params, nat());
    let r = bind(&mut b, &mut params, nat());
    let s = bind(&mut b, &mut params, nat());
    let hs = bind(&mut b, &mut params, lt(s.clone(), n.clone()));
    let a = sum(n.clone(), q.clone(), r.clone());
    let d = sum(n.clone(), p.clone(), s.clone());
    let he = bind(&mut b, &mut params, eq(a.clone(), d.clone()));
    let goal = le(q.clone(), p.clone());
    let left_prop = goal.clone();
    let right_prop = lt(p.clone(), q.clone());
    let or_type = call("Or", [left_prop.clone(), right_prop.clone()]);
    let motive = lambda(&b, or_type, |_| goal.clone());
    let left = lambda(&b, left_prop.clone(), |h| h);

    let mut rb = EnvDeclBuilder::child_of(&b);
    let (h_id, h) = rb.fresh_local(right_prop.clone());
    let pn = mul(p.clone(), n.clone());
    let qn = mul(q.clone(), n.clone());
    let succ_p = call("Nat.succ", [p.clone()]);
    let succ_pn = mul(succ_p.clone(), n.clone());
    let pn_plus_n = add(pn.clone(), n.clone());
    let n_plus_pn = add(n.clone(), pn.clone());
    let strict = call("Nat.add_lt_add_left", [s, n.clone(), hs, pn.clone()]);
    // The actual seed's succ_mul returns n + p*n, so the commutation is
    // explicit; no canonical-library orientation is assumed by conversion.
    let step_eq = trans(
        pn_plus_n.clone(),
        n_plus_pn.clone(),
        succ_pn.clone(),
        call("Nat.add_comm", [pn, n.clone()]),
        symm(
            succ_pn.clone(),
            n_plus_pn,
            call("Nat.succ_mul", [p.clone(), n.clone()]),
        ),
    );
    let strict = subst(
        pn_plus_n,
        succ_pn.clone(),
        step_eq,
        lambda(&rb, nat(), |x| lt(d.clone(), x)),
        strict,
    );
    let product_bound = call("Nat.mul_le_mul_right", [succ_p, q.clone(), n, h]);
    let strict = call(
        "Nat.lt_of_lt_of_le",
        [d.clone(), succ_pn, qn.clone(), strict, product_bound],
    );
    let sum_bound = call("Nat.le_add_right", [qn.clone(), r]);
    let strict = call(
        "Nat.lt_of_lt_of_le",
        [d.clone(), qn, a.clone(), strict, sum_bound],
    );
    let self_lt = subst(
        a,
        d.clone(),
        he,
        lambda(&rb, nat(), |x| lt(d.clone(), x)),
        strict,
    );
    let absurd = call("Nat.lt_irrefl", [d, self_lt]);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [goal.clone(), absurd],
    );
    let right = rb.mk_lam(h_id, BinderInfo::Default, right_prop.clone(), proof);
    let right = rb.finish_child(right);
    let major = call("Nat.le_or_lt", [q, p]);
    let proof = call(
        "Or.rec",
        [left_prop, right_prop, motive, left, right, major],
    );
    close(QUOTIENT_LE, b, params, goal, proof)
}

fn remainder_unique() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let n = bind(&mut b, &mut params, nat());
    let q = bind(&mut b, &mut params, nat());
    let p = bind(&mut b, &mut params, nat());
    let r = bind(&mut b, &mut params, nat());
    let s = bind(&mut b, &mut params, nat());
    let hr = bind(&mut b, &mut params, lt(r.clone(), n.clone()));
    let hs = bind(&mut b, &mut params, lt(s.clone(), n.clone()));
    let a = sum(n.clone(), q.clone(), r.clone());
    let d = sum(n.clone(), p.clone(), s.clone());
    let he = bind(&mut b, &mut params, eq(a.clone(), d.clone()));
    let forward = call(
        QUOTIENT_LE,
        [
            n.clone(),
            q.clone(),
            p.clone(),
            r.clone(),
            s.clone(),
            hs,
            he.clone(),
        ],
    );
    let backward = call(
        QUOTIENT_LE,
        [
            n.clone(),
            p.clone(),
            q.clone(),
            s.clone(),
            r.clone(),
            hr,
            symm(a.clone(), d.clone(), he.clone()),
        ],
    );
    let same_q = call("Nat.le_antisymm", [q.clone(), p.clone(), forward, backward]);
    let same_sum = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![one_level(), one_level()],
        ),
        [
            nat(),
            nat(),
            q.clone(),
            p,
            lambda(&b, nat(), |k| sum(n.clone(), k, s.clone())),
            same_q,
        ],
    );
    let q_sum_s = sum(n.clone(), q.clone(), s.clone());
    let aligned = trans(
        a,
        d.clone(),
        q_sum_s.clone(),
        he,
        symm(q_sum_s, d, same_sum),
    );
    let proof = call(
        "Nat.add_left_cancel",
        [mul(q, n), r.clone(), s.clone(), aligned],
    );
    close(REMAINDER_UNIQUE, b, params, eq(r, s), proof)
}

fn mod_decomposition() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let a = bind(&mut b, &mut params, nat());
    let n = bind(&mut b, &mut params, nat());
    let q = bind(&mut b, &mut params, nat());
    let r = bind(&mut b, &mut params, nat());
    let hr = bind(&mut b, &mut params, lt(r.clone(), n.clone()));
    let provided_sum = sum(n.clone(), q.clone(), r.clone());
    let he = bind(&mut b, &mut params, eq(provided_sum.clone(), a.clone()));
    let zero = c("Nat.zero");
    let positive = call(
        "Nat.lt_of_le_of_lt",
        [
            zero,
            r.clone(),
            n.clone(),
            call("Nat.zero_le", [r.clone()]),
            hr.clone(),
        ],
    );
    let quotient = call("Nat.div", [a.clone(), n.clone()]);
    let remainder = call("Nat.mod", [a.clone(), n.clone()]);
    let bound = call("Nat.mod_lt", [a.clone(), n.clone(), positive]);
    let actual_sum = sum(n.clone(), quotient.clone(), remainder.clone());
    let aligned = trans(
        actual_sum,
        a.clone(),
        provided_sum.clone(),
        call("Nat.div_add_mod", [a.clone(), n.clone()]),
        symm(provided_sum, a, he),
    );
    let proof = call(
        REMAINDER_UNIQUE,
        [
            n,
            quotient,
            q,
            remainder.clone(),
            r.clone(),
            bound,
            hr,
            aligned,
        ],
    );
    close(MOD_DECOMPOSITION, b, params, eq(remainder, r), proof)
}

// These functions construct ordinary equality proofs; the existing kernel
// checks every step before the canonical theorem is registered.
fn congr(
    b: &EnvDeclBuilder,
    from: Expr,
    to: Expr,
    proof: Expr,
    f: impl FnOnce(Expr) -> Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![one_level(), one_level()],
        ),
        [nat(), nat(), from, to, lambda(b, nat(), f), proof],
    )
}
fn remainder(a: Expr, n: Expr) -> Expr {
    call("Nat.mod", [a, n])
}
fn sum_interchange(b: &EnvDeclBuilder, x: Expr, y: Expr, z: Expr, w: Expr) -> Expr {
    let yz = add(y.clone(), z.clone());
    let zy = add(z.clone(), y.clone());
    let inner_start = add(y.clone(), add(z.clone(), w.clone()));
    let inner_mid = add(yz.clone(), w.clone());
    let inner_next = add(zy.clone(), w.clone());
    let inner_end = add(z.clone(), add(y.clone(), w.clone()));
    let inner = trans(
        inner_start.clone(),
        inner_mid.clone(),
        inner_next.clone(),
        symm(
            inner_mid.clone(),
            inner_start.clone(),
            call("Nat.add_assoc", [y.clone(), z.clone(), w.clone()]),
        ),
        congr(
            b,
            yz,
            zy,
            call("Nat.add_comm", [y.clone(), z.clone()]),
            |t| add(t, w.clone()),
        ),
    );
    let inner = trans(
        inner_start.clone(),
        inner_next,
        inner_end.clone(),
        inner,
        call("Nat.add_assoc", [z.clone(), y.clone(), w.clone()]),
    );
    let start = add(add(x.clone(), y.clone()), add(z.clone(), w.clone()));
    let mid = add(x.clone(), inner_start.clone());
    let next = add(x.clone(), inner_end.clone());
    let end = add(add(x.clone(), z.clone()), add(y.clone(), w.clone()));
    let first = call(
        "Nat.add_assoc",
        [x.clone(), y.clone(), add(z.clone(), w.clone())],
    );
    let second = congr(b, inner_start, inner_end, inner, |t| add(x.clone(), t));
    trans(
        start.clone(),
        next.clone(),
        end.clone(),
        trans(start, mid, next.clone(), first, second),
        symm(end, next, call("Nat.add_assoc", [x, z, add(y, w)])),
    )
}
fn add_mod_goal(a: Expr, d: Expr, n: Expr) -> Expr {
    eq(
        remainder(add(a.clone(), d.clone()), n.clone()),
        remainder(add(remainder(a, n.clone()), remainder(d, n.clone())), n),
    )
}
fn add_mod() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let a = bind(&mut b, &mut params, nat());
    let d = bind(&mut b, &mut params, nat());
    let n = bind(&mut b, &mut params, nat());
    let zero = c("Nat.zero");
    let total = add(a.clone(), d.clone());
    let za = remainder(a.clone(), zero.clone());
    let zd = remainder(d.clone(), zero.clone());
    let zsum = add(za.clone(), zd.clone());
    let zright = remainder(zsum.clone(), zero.clone());
    let amid = add(a.clone(), zd.clone());
    let zproof = trans(
        zsum.clone(),
        amid.clone(),
        total.clone(),
        congr(
            &b,
            za,
            a.clone(),
            call("Nat.divmodAux.mod_zero", [a.clone()]),
            |x| add(x, zd.clone()),
        ),
        congr(
            &b,
            zd,
            d.clone(),
            call("Nat.divmodAux.mod_zero", [d.clone()]),
            |x| add(a.clone(), x),
        ),
    );
    let zproof = trans(
        zright.clone(),
        zsum.clone(),
        total.clone(),
        call("Nat.divmodAux.mod_zero", [zsum]),
        zproof,
    );
    let base = trans(
        remainder(total.clone(), zero),
        total.clone(),
        zright.clone(),
        call("Nat.divmodAux.mod_zero", [total.clone()]),
        symm(zright, total.clone(), zproof),
    );
    let motive = lambda(&b, nat(), |m| add_mod_goal(a.clone(), d.clone(), m));
    let mut sb = EnvDeclBuilder::child_of(&b);
    let (k_id, k) = sb.fresh_local(nat());
    let ih_type = Expr::app(motive.clone(), k.clone());
    let (ih_id, _) = sb.fresh_local(ih_type.clone());
    let modulus = call("Nat.succ", [k.clone()]);
    let positive = call(
        "Nat.succ_le_succ",
        [c("Nat.zero"), k.clone(), call("Nat.zero_le", [k])],
    );
    let qa = call("Nat.div", [a.clone(), modulus.clone()]);
    let qd = call("Nat.div", [d.clone(), modulus.clone()]);
    let ra = remainder(a.clone(), modulus.clone());
    let rd = remainder(d.clone(), modulus.clone());
    let rs = add(ra.clone(), rd.clone());
    let qr = call("Nat.div", [rs.clone(), modulus.clone()]);
    let t = remainder(rs.clone(), modulus.clone());
    let qab = add(qa.clone(), qd.clone());
    let qnew = add(qab.clone(), qr.clone());
    let an = mul(qa.clone(), modulus.clone());
    let dn = mul(qd.clone(), modulus.clone());
    let rn = mul(qr.clone(), modulus.clone());
    let abn = mul(qab.clone(), modulus.clone());
    let terms = [
        add(mul(qnew.clone(), modulus.clone()), t.clone()),
        add(add(abn.clone(), rn.clone()), t.clone()),
        add(abn.clone(), add(rn.clone(), t.clone())),
        add(add(an.clone(), dn.clone()), add(rn.clone(), t.clone())),
        add(add(an.clone(), dn.clone()), rs.clone()),
        add(add(an.clone(), ra.clone()), add(dn.clone(), rd.clone())),
        add(a.clone(), add(dn.clone(), rd.clone())),
        total.clone(),
    ];
    let proofs = [
        congr(
            &sb,
            mul(qnew.clone(), modulus.clone()),
            add(abn.clone(), rn.clone()),
            call("Nat.right_distrib", [qab.clone(), qr, modulus.clone()]),
            |x| add(x, t.clone()),
        ),
        call("Nat.add_assoc", [abn.clone(), rn.clone(), t.clone()]),
        congr(
            &sb,
            abn,
            add(an.clone(), dn.clone()),
            call("Nat.right_distrib", [qa, qd, modulus.clone()]),
            |x| add(x, add(rn.clone(), t.clone())),
        ),
        congr(
            &sb,
            add(rn, t.clone()),
            rs.clone(),
            call("Nat.div_add_mod", [rs.clone(), modulus.clone()]),
            |x| add(add(an.clone(), dn.clone()), x),
        ),
        sum_interchange(&sb, an.clone(), dn.clone(), ra, rd.clone()),
        congr(
            &sb,
            add(an, remainder(a.clone(), modulus.clone())),
            a.clone(),
            call("Nat.div_add_mod", [a.clone(), modulus.clone()]),
            |x| add(x, add(dn.clone(), rd.clone())),
        ),
        congr(
            &sb,
            add(dn, rd),
            d.clone(),
            call("Nat.div_add_mod", [d.clone(), modulus.clone()]),
            |x| add(a.clone(), x),
        ),
    ];
    let mut reconstruction = proofs[0].clone();
    for i in 1..proofs.len() {
        reconstruction = trans(
            terms[0].clone(),
            terms[i].clone(),
            terms[i + 1].clone(),
            reconstruction,
            proofs[i].clone(),
        );
    }
    let bound = call("Nat.mod_lt", [rs, modulus.clone(), positive]);
    let proof = call(
        MOD_DECOMPOSITION,
        [total, modulus, qnew, t, bound, reconstruction],
    );
    let step = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, proof);
    let step = sb.mk_lam(k_id, BinderInfo::Default, nat(), step);
    let step = sb.finish_child(step);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, step, n.clone()],
    );
    close("Nat.add_mod", b, params, add_mod_goal(a, d, n), proof)
}

const MOD_MUL_LEFT: &str = "Nat.divmodAux.mod_mul_left";

fn mod_mul_left_goal(a: Expr, b: Expr, n: Expr) -> Expr {
    eq(
        remainder(mul(remainder(a.clone(), n.clone()), b.clone()), n.clone()),
        remainder(mul(a, b), n),
    )
}

// Induct on the multiplier, retaining both the actual seed's mul_succ
// orientation and the modulus-zero case. Every constructor is ordinary advice.
fn mod_mul_left() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let a = bind(&mut b, &mut params, nat());
    let multiplier = bind(&mut b, &mut params, nat());
    let n = bind(&mut b, &mut params, nat());
    let ra = remainder(a.clone(), n.clone());
    let zero = c("Nat.zero");
    let fzero = remainder(mul(ra.clone(), zero.clone()), n.clone());
    let gzero = remainder(mul(a.clone(), zero.clone()), n.clone());
    let middle = remainder(zero.clone(), n.clone());
    let base = trans(
        fzero,
        middle.clone(),
        gzero.clone(),
        congr(
            &b,
            mul(ra.clone(), zero.clone()),
            zero.clone(),
            call("Nat.mul_zero", [ra.clone()]),
            |x| remainder(x, n.clone()),
        ),
        symm(
            gzero,
            middle,
            congr(
                &b,
                mul(a.clone(), zero.clone()),
                zero,
                call("Nat.mul_zero", [a.clone()]),
                |x| remainder(x, n.clone()),
            ),
        ),
    );
    let motive = lambda(&b, nat(), |k| mod_mul_left_goal(a.clone(), k, n.clone()));
    let mut sb = EnvDeclBuilder::child_of(&b);
    let (k_id, k) = sb.fresh_local(nat());
    let ih_ty = Expr::app(motive.clone(), k.clone());
    let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
    let successor = call("Nat.succ", [k.clone()]);
    let reduced_product = mul(ra.clone(), k.clone());
    let original_product = mul(a.clone(), k.clone());
    let reduced_remainder = remainder(reduced_product.clone(), n.clone());
    let original_remainder = remainder(original_product.clone(), n.clone());
    let twice_ra = remainder(ra.clone(), n.clone());
    let terms = [
        remainder(mul(ra.clone(), successor.clone()), n.clone()),
        remainder(add(ra.clone(), reduced_product.clone()), n.clone()),
        remainder(add(twice_ra.clone(), reduced_remainder.clone()), n.clone()),
        remainder(add(ra.clone(), reduced_remainder.clone()), n.clone()),
        remainder(add(ra.clone(), original_remainder.clone()), n.clone()),
        remainder(add(a.clone(), original_product.clone()), n.clone()),
        remainder(mul(a.clone(), successor.clone()), n.clone()),
    ];
    let proofs = [
        congr(
            &sb,
            mul(ra.clone(), successor.clone()),
            add(ra.clone(), reduced_product.clone()),
            call("Nat.mul_succ", [ra.clone(), k.clone()]),
            |x| remainder(x, n.clone()),
        ),
        call("Nat.add_mod", [ra.clone(), reduced_product, n.clone()]),
        congr(
            &sb,
            twice_ra,
            ra.clone(),
            call("Nat.mod_mod", [a.clone(), n.clone()]),
            |x| remainder(add(x, reduced_remainder.clone()), n.clone()),
        ),
        congr(&sb, reduced_remainder, original_remainder, ih, |x| {
            remainder(add(ra.clone(), x), n.clone())
        }),
        symm(
            terms[5].clone(),
            terms[4].clone(),
            call(
                "Nat.add_mod",
                [a.clone(), original_product.clone(), n.clone()],
            ),
        ),
        symm(
            terms[6].clone(),
            terms[5].clone(),
            congr(
                &sb,
                mul(a.clone(), successor),
                add(a.clone(), original_product),
                call("Nat.mul_succ", [a.clone(), k]),
                |x| remainder(x, n.clone()),
            ),
        ),
    ];
    let mut proof = proofs[0].clone();
    for i in 1..proofs.len() {
        proof = trans(
            terms[0].clone(),
            terms[i].clone(),
            terms[i + 1].clone(),
            proof,
            proofs[i].clone(),
        );
    }
    let step = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
    let step = sb.mk_lam(k_id, BinderInfo::Default, nat(), step);
    let step = sb.finish_child(step);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, step, multiplier.clone()],
    );
    close(
        MOD_MUL_LEFT,
        b,
        params,
        mod_mul_left_goal(a, multiplier, n),
        proof,
    )
}

fn mul_mod() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let mut params = vec![];
    let a = bind(&mut b, &mut params, nat());
    let d = bind(&mut b, &mut params, nat());
    let n = bind(&mut b, &mut params, nat());
    let ra = remainder(a.clone(), n.clone());
    let rd = remainder(d.clone(), n.clone());
    let terms = [
        remainder(mul(a.clone(), d.clone()), n.clone()),
        remainder(mul(ra.clone(), d.clone()), n.clone()),
        remainder(mul(d.clone(), ra.clone()), n.clone()),
        remainder(mul(rd.clone(), ra.clone()), n.clone()),
        remainder(mul(ra.clone(), rd.clone()), n.clone()),
    ];
    let proofs = [
        symm(
            terms[1].clone(),
            terms[0].clone(),
            call(MOD_MUL_LEFT, [a, d.clone(), n.clone()]),
        ),
        congr(
            &b,
            mul(ra.clone(), d.clone()),
            mul(d.clone(), ra.clone()),
            call("Nat.mul_comm", [ra.clone(), d.clone()]),
            |x| remainder(x, n.clone()),
        ),
        symm(
            terms[3].clone(),
            terms[2].clone(),
            call(MOD_MUL_LEFT, [d, ra.clone(), n.clone()]),
        ),
        congr(
            &b,
            mul(rd.clone(), ra.clone()),
            mul(ra.clone(), rd.clone()),
            call("Nat.mul_comm", [rd, ra]),
            |x| remainder(x, n.clone()),
        ),
    ];
    let mut proof = proofs[0].clone();
    for i in 1..proofs.len() {
        proof = trans(
            terms[0].clone(),
            terms[i].clone(),
            terms[i + 1].clone(),
            proof,
            proofs[i].clone(),
        );
    }
    close(
        "Nat.mul_mod",
        b,
        params,
        eq(terms[0].clone(), terms[4].clone()),
        proof,
    )
}

impl Environment {
    pub(crate) fn register_nat_remainder_uniqueness(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat_floor_order_lemmas()?;
        self.register_nat_arith_order_proofs()?;
        self.register_nat_succ_mul_proof()?;
        self.register_nat_add_left_cancel_proof()?;
        self.ensure_exact_checked_decl(quotient_le())?;
        self.ensure_exact_checked_decl(remainder_unique())?;
        self.ensure_exact_checked_decl(mod_decomposition())?;
        self.register_nat_right_distrib_proof()?;
        self.ensure_exact_checked_decl(add_mod())?;
        self.register_nat_modular_identities()?;
        self.register_nat_mul_zero_proof()?;
        self.register_nat_mul_succ_proof()?;
        self.register_nat_mul_comm_proof()?;
        self.ensure_exact_checked_decl(mod_mul_left())?;
        self.ensure_exact_checked_decl(mul_mod())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;

    #[test]
    fn bounded_remainder_uniqueness_is_checked_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in [
            QUOTIENT_LE,
            REMAINDER_UNIQUE,
            MOD_DECOMPOSITION,
            "Nat.add_mod",
            MOD_MUL_LEFT,
            "Nat.mul_mod",
        ] {
            let name = Name::from_string(name);
            assert!(env
                .get_const(&name)
                .expect("actual checked theorem")
                .value
                .is_some());
            assert!(env
                .axiom_deps(&name)
                .expect("transitive closure")
                .is_empty());
        }
        let before = (env.num_constants(), env.num_instances());
        env.register_nat_remainder_uniqueness()
            .expect("repeat registration");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }

    #[test]
    fn bounded_remainder_uniqueness_preserves_checked_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        env.register_nat_remainder_uniqueness()
            .expect("import suppression");
        for name in [
            QUOTIENT_LE,
            REMAINDER_UNIQUE,
            MOD_DECOMPOSITION,
            "Nat.add_mod",
            MOD_MUL_LEFT,
            "Nat.mul_mod",
        ] {
            assert!(env.get_const(&Name::from_string(name)).is_none());
        }
    }

    #[test]
    fn reference_replays_universal_decompositions_and_refuses_a_changed_remainder() {
        let mut reference =
            ReferenceKernel::new(Environment::with_prelude()).expect("reference theory");
        for name in [
            QUOTIENT_LE,
            REMAINDER_UNIQUE,
            MOD_DECOMPOSITION,
            "Nat.add_mod",
            MOD_MUL_LEFT,
            "Nat.mul_mod",
        ] {
            let type_ = reference
                .environment()
                .get_const(&Name::from_string(name))
                .expect("actual universal statement")
                .type_
                .clone();
            let alias = Name::from_string(&format!("remainder_reference_{name}"));
            reference
                .add_checked(Declaration::Theorem {
                    name: alias.clone(),
                    level_params: vec![],
                    type_,
                    value: c(name),
                })
                .expect("actual proof closure replay");
            assert!(reference
                .environment()
                .axiom_deps(&alias)
                .expect("closure")
                .is_empty());
        }
        let mut b = EnvDeclBuilder::new();
        let mut params = vec![];
        let a = bind(&mut b, &mut params, nat());
        let n = bind(&mut b, &mut params, nat());
        let q = bind(&mut b, &mut params, nat());
        let r = bind(&mut b, &mut params, nat());
        let _ = bind(&mut b, &mut params, lt(r.clone(), n.clone()));
        let _ = bind(
            &mut b,
            &mut params,
            eq(sum(n.clone(), q, r.clone()), a.clone()),
        );
        let changed = eq(call("Nat.mod", [a, n]), call("Nat.succ", [r]));
        let Declaration::Theorem { type_, .. } = close("unused", b, params, changed, c("Nat.zero"))
        else {
            unreachable!()
        };
        let before = (
            reference.environment().num_constants(),
            reference.environment().num_instances(),
        );
        assert!(reference
            .add_checked(Declaration::Theorem {
                name: Name::from_string("remainder_extra_unit"),
                level_params: vec![],
                type_,
                // Exactly the same complete universal proof as the positive alias.
                value: c(MOD_DECOMPOSITION),
            })
            .is_err());
        assert!(reference
            .environment()
            .get_const(&Name::from_string("remainder_extra_unit"))
            .is_none());
        assert_eq!(
            (
                reference.environment().num_constants(),
                reference.environment().num_instances()
            ),
            before
        );
    }

    #[test]
    fn reference_refuses_changed_universal_mul_mod_with_original_proof() {
        let mut reference =
            ReferenceKernel::new(Environment::with_prelude()).expect("reference theory");
        let mut b = EnvDeclBuilder::new();
        let mut params = vec![];
        let a = bind(&mut b, &mut params, nat());
        let d = bind(&mut b, &mut params, nat());
        let n = bind(&mut b, &mut params, nat());
        let lhs = remainder(mul(a.clone(), d.clone()), n.clone());
        let rhs = remainder(mul(remainder(a, n.clone()), remainder(d, n.clone())), n);
        let changed = eq(lhs, call("Nat.succ", [rhs]));
        let Declaration::Theorem { type_, .. } = close("unused", b, params, changed, c("Nat.zero"))
        else {
            unreachable!()
        };
        let before = (
            reference.environment().num_constants(),
            reference.environment().num_instances(),
        );
        let name = Name::from_string("mul_mod_extra_unit");
        assert!(reference
            .add_checked(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_,
                value: c("Nat.mul_mod"),
            })
            .is_err());
        assert!(reference.environment().get_const(&name).is_none());
        assert_eq!(
            (
                reference.environment().num_constants(),
                reference.environment().num_instances()
            ),
            before
        );
    }
}

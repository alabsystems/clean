// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate CIC proofs for bounded wrapping subtraction. Pattern matching
//! only selects a proof term: the original source goal and complete proof
//! closure still pass the canonical strict certification audit.

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn v(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}
fn app2(name: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(c(name), [a, b])
}
fn add(a: Expr, b: Expr) -> Expr {
    app2("Nat.add", a, b)
}
fn sub(a: Expr, b: Expr) -> Expr {
    app2("Nat.sub", a, b)
}
fn succ(a: Expr) -> Expr {
    Expr::app(c("Nat.succ"), a)
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), a, b],
    )
}
fn lam(id: u64, ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(FVarId::new(id)))
}
fn pi(id: u64, ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body.abstract_fvar(FVarId::new(id)))
}
fn symm(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), a, b, h],
    )
}
fn trans(a: Expr, b: Expr, d: Expr, h: Expr, k: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Nat"), a, b, d, h, k],
    )
}
fn congr(f: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [c("Nat"), c("Nat"), a, b, f, h],
    )
}
fn le(a: Expr, b: Expr) -> Expr {
    app2("Nat.le", a, b)
}
fn goal(a: Expr, b: Expr, t: Expr) -> Expr {
    eq(add(a.clone(), sub(t.clone(), b.clone())), sub(add(a, t), b))
}

/// A closed proof of forall a b t, b <= t -> a+(t-b)=(a+t)-b.
///
/// Nat.le induction first derives its elimination principle into any Prop P:
/// (forall k, P (b+k)) -> P t. At t=b+k, commute b+k to k+b and
/// use add_assoc and add_sub_cancel on both sides. No subtraction axiom,
/// native reduction rule, or assumed UInt arithmetic bridge is introduced.
fn add_sub_of_le() -> Expr {
    let (a, b, t, h, p, all, k, x, ih) = (
        v(100),
        v(101),
        v(102),
        v(103),
        v(104),
        v(105),
        v(106),
        v(107),
        v(109),
    );
    let pred_ty = Expr::arrow(c("Nat"), Expr::prop());
    let all_ty = pi(
        106,
        c("Nat"),
        Expr::app(p.clone(), add(b.clone(), k.clone())),
    );
    let elimination = |at: Expr| {
        pi(
            104,
            pred_ty.clone(),
            pi(105, all_ty.clone(), Expr::app(p.clone(), at)),
        )
    };
    let motive = lam(
        102,
        c("Nat"),
        lam(103, le(b.clone(), t.clone()), elimination(t.clone())),
    );
    let base = lam(
        104,
        pred_ty.clone(),
        lam(
            105,
            all_ty.clone(),
            Expr::app(all.clone(), Expr::nat_lit(0u64)),
        ),
    );
    let shifted_p = lam(107, c("Nat"), Expr::app(p.clone(), succ(x.clone())));
    let shifted_all = lam(106, c("Nat"), Expr::app(all.clone(), succ(k.clone())));
    let step = lam(
        102,
        c("Nat"),
        lam(
            108,
            le(b.clone(), t.clone()),
            lam(
                109,
                elimination(t.clone()),
                lam(
                    104,
                    pred_ty,
                    lam(105, all_ty, Expr::apps(ih, [shifted_p, shifted_all])),
                ),
            ),
        ),
    );
    let eliminate = Expr::apps(
        c("Nat.le.rec"),
        [b.clone(), motive, base, step, t.clone(), h.clone()],
    );
    let actual_p = lam(102, c("Nat"), goal(a.clone(), b.clone(), t.clone()));
    let kb = add(k.clone(), b.clone());
    let bk = add(b.clone(), k.clone());
    let mid = add(a.clone(), k.clone());
    let left = add(a.clone(), sub(kb.clone(), b.clone()));
    let right = sub(add(a.clone(), kb.clone()), b.clone());
    let left_eq = congr(
        lam(107, c("Nat"), add(a.clone(), x.clone())),
        sub(kb.clone(), b.clone()),
        k.clone(),
        Expr::apps(c("Nat.add_sub_cancel"), [k.clone(), b.clone()]),
    );
    let assoc = Expr::apps(c("Nat.add_assoc"), [a.clone(), k.clone(), b.clone()]);
    let right_eq = trans(
        right.clone(),
        sub(add(mid.clone(), b.clone()), b.clone()),
        mid.clone(),
        congr(
            lam(107, c("Nat"), sub(x.clone(), b.clone())),
            add(a.clone(), kb.clone()),
            add(mid.clone(), b.clone()),
            symm(
                add(mid.clone(), b.clone()),
                add(a.clone(), kb.clone()),
                assoc,
            ),
        ),
        Expr::apps(c("Nat.add_sub_cancel"), [mid.clone(), b.clone()]),
    );
    let at_kb = trans(
        left,
        mid.clone(),
        right.clone(),
        left_eq,
        symm(right, mid, right_eq),
    );
    let commute = Expr::apps(c("Nat.add_comm"), [b.clone(), k.clone()]);
    let at_bk = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [
            c("Nat"),
            actual_p.clone(),
            kb.clone(),
            bk.clone(),
            symm(bk, kb, commute),
            at_kb,
        ],
    );
    let all_actual = lam(106, c("Nat"), at_bk);
    let proof = Expr::apps(eliminate, [actual_p, all_actual]);
    let proof = lam(103, le(b.clone(), t.clone()), proof);
    let proof = lam(102, c("Nat"), proof);
    let proof = lam(101, c("Nat"), proof);
    lam(100, c("Nat"), proof)
}

fn args_of<'a>(term: &'a Expr, name: &str, count: usize) -> Option<Vec<&'a Expr>> {
    let term = term.strip_mdata();
    let ExprKind::Const(head, levels) = term.get_app_fn().kind() else {
        return None;
    };
    if *head != Name::from_string(name) || !levels.is_empty() {
        return None;
    }
    let args = term.get_app_args();
    (args.len() == count).then(|| args.into_vec())
}

/// Select an actual Nat subtraction denotation whose subtrahend is the Nat
/// image of one genuine UInt parameter. Other shapes remain conversion-only.
pub(super) fn candidate(width: u32, params: &[Expr], rhs: &Expr) -> Option<Expr> {
    let modulus = crate::modulus(width);
    let wrap = args_of(rhs, "Nat.mod", 2)?;
    if wrap[1] != &modulus {
        return None;
    }
    let minus = args_of(wrap[0], "Nat.sub", 2)?;
    let plus = args_of(minus[0], "Nat.add", 2)?;
    if plus[1] != &modulus {
        return None;
    }
    let prefix = format!("UInt{width}");
    let decoded = args_of(minus[1], &format!("{prefix}.toNat"), 1)?;
    if !params.contains(decoded[0]) {
        return None;
    }
    let a = plus[0].clone();
    let b = minus[1].clone();
    let bitvec = Expr::app(c(&format!("{prefix}.toBitVec")), decoded[0].clone());
    let fin = Expr::apps(c("BitVec.toFin"), [Expr::nat_lit(u64::from(width)), bitvec]);
    let lt = Expr::proj(Name::from_string("Fin"), 1, fin);
    let bound = Expr::apps(c("Nat.le_of_lt"), [b.clone(), modulus.clone(), lt]);
    let equality = Expr::apps(
        add_sub_of_le(),
        [a.clone(), b.clone(), modulus.clone(), bound],
    );
    let old = add(a.clone(), sub(modulus.clone(), b.clone()));
    let new = sub(add(a, modulus.clone()), b);
    let reduce = lam(110, c("Nat"), app2("Nat.mod", v(110), modulus));
    Some(congr(reduce, old, new, equality))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_equation_subtraction_nat_bridge_kernel_checks_its_actual_bound() {
        let env = clean_kernel::Environment::with_prelude();
        let (a, b, t) = (v(100), v(101), v(102));
        let statement = pi(
            100,
            c("Nat"),
            pi(
                101,
                c("Nat"),
                pi(
                    102,
                    c("Nat"),
                    pi(103, le(b.clone(), t.clone()), goal(a, b, t)),
                ),
            ),
        );
        let proof = add_sub_of_le();
        let audit = env.audit_certification(&statement, &proof);
        assert!(
            audit.is_certified(),
            "the actual CIC induction proof must pass: {:?}",
            audit.issues
        );
        let invalid = Expr::apps(
            proof,
            [
                Expr::nat_lit(1u64),
                Expr::nat_lit(1u64),
                Expr::nat_lit(0u64),
                Expr::app(c("Nat.le.refl"), Expr::nat_lit(0u64)),
            ],
        );
        let bad = eq(Expr::nat_lit(1u64), Expr::nat_lit(0u64));
        assert!(
            !env.audit_certification(&bad, &invalid).is_certified(),
            "a missing subtraction bound cannot be supplied by status or reflexivity"
        );
    }
}

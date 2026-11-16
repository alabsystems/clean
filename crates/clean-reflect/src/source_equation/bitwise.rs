// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual CIC bounds for the canonical `Nat.bitwiseAux` definition, and
//! candidate source equations that remove only proved redundant UInt wraps.
//! Syntax selects proof search; the full original judgment remains audited.

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Literal, Name};

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn v(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}
fn lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn call(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn add(a: Expr, b: Expr) -> Expr {
    call("Nat.add", [a, b])
}
fn succ(a: Expr) -> Expr {
    Expr::app(c("Nat.succ"), a)
}
fn pow2(w: Expr) -> Expr {
    call("Nat.pow", [lit(2), w])
}
fn lt(a: Expr, b: Expr) -> Expr {
    call("Nat.lt", [a, b])
}
fn le(a: Expr, b: Expr) -> Expr {
    call("Nat.le", [a, b])
}
fn aux(f: Expr, k: Expr, a: Expr, b: Expr) -> Expr {
    call("Nat.bitwiseAux", [f, k, a, b])
}
fn lam(id: u64, ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(FVarId::new(id)))
}
fn pi(id: u64, ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body.abstract_fvar(FVarId::new(id)))
}
fn lambdas(bindings: &[(u64, Expr)], mut body: Expr) -> Expr {
    for (id, ty) in bindings.iter().rev() {
        body = lam(*id, ty.clone(), body);
    }
    body
}
fn pis(bindings: &[(u64, Expr)], mut body: Expr) -> Expr {
    for (id, ty) in bindings.iter().rev() {
        body = pi(*id, ty.clone(), body);
    }
    body
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}
fn refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, a],
    )
}
fn symm(ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, a, b, h],
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
fn congr(input: Expr, output: Expr, f: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [input, output, a, b, f, h],
    )
}
fn subst(ty: Expr, p: Expr, a: Expr, b: Expr, h: Expr, at: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, p, a, b, h, at],
    )
}
fn nat_rec(p: Expr, base: Expr, step: Expr, at: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [p, base, step, at],
    )
}
fn bool_rec(p: Expr, base: Expr, step: Expr, at: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [p, base, step, at],
    )
}
fn f_ty() -> Expr {
    Expr::arrow(c("Bool"), Expr::arrow(c("Bool"), c("Bool")))
}
fn ff(f: Expr) -> Expr {
    Expr::apps(f, [c("Bool.false"), c("Bool.false")])
}

/// forall w, 0 < 2^w, by Nat induction and the actual pow_two_succ theorem.
fn pow2_positive() -> Expr {
    let w = v(200);
    let p = pow2(w.clone());
    let pp = add(p.clone(), p.clone());
    let statement = |x| lt(lit(0), pow2(x));
    let step_bound = call(
        "Nat.lt_of_lt_of_le",
        [
            lit(0),
            p.clone(),
            pp.clone(),
            v(201),
            call("Nat.le_add_right", [p.clone(), p]),
        ],
    );
    let power = call("Nat.pow_two_succ", [w.clone()]);
    let step = subst(
        c("Nat"),
        lam(202, c("Nat"), lt(lit(0), v(202))),
        pp.clone(),
        pow2(succ(w.clone())),
        symm(c("Nat"), pow2(succ(w.clone())), pp, power),
        step_bound,
    );
    let proof = nat_rec(
        lam(200, c("Nat"), statement(w.clone())),
        call("Nat.zero_lt_succ", [lit(0)]),
        lambdas(&[(200, c("Nat")), (201, statement(w.clone()))], step),
        w.clone(),
    );
    lam(200, c("Nat"), proof)
}

/// For any f with f false false = false, bitwiseAux f k 0 0 = 0.
fn aux_zero(f: Expr, hf: Expr, at: Expr) -> Expr {
    let k = v(203);
    let prev = aux(f.clone(), k.clone(), lit(0), lit(0));
    let bit = ff(f.clone());
    let of_bit = Expr::app(c("Nat.ofBool"), bit.clone());
    let full = add(add(prev.clone(), prev.clone()), of_bit.clone());
    let drop_prev = congr(
        c("Nat"),
        c("Nat"),
        lam(205, c("Nat"), add(add(v(205), v(205)), of_bit.clone())),
        prev.clone(),
        lit(0),
        v(204),
    );
    let drop_bit = congr(
        c("Bool"),
        c("Nat"),
        c("Nat.ofBool"),
        bit,
        c("Bool.false"),
        hf,
    );
    let drop_prev = trans(
        full.clone(),
        add(lit(0), of_bit.clone()),
        of_bit.clone(),
        drop_prev,
        call("Nat.zero_add", [of_bit.clone()]),
    );
    let step = trans(full, of_bit, lit(0), drop_prev, drop_bit);
    nat_rec(
        lam(203, c("Nat"), eq(c("Nat"), prev.clone(), lit(0))),
        refl(c("Nat"), lit(0)),
        lambdas(&[(203, c("Nat")), (204, eq(c("Nat"), prev, lit(0)))], step),
        at,
    )
}

/// r < p -> (r+r)+ofBool bit < p+p. Both Boolean cases use genuine
/// Nat order proofs; the true case retains the full two-successor gap.
fn doubled_bit_bound(r: Expr, p: Expr, hr: Expr, bit: Expr) -> Expr {
    let rr = add(r.clone(), r.clone());
    let pp = add(p.clone(), p.clone());
    let goal = |q| lt(add(rr.clone(), Expr::app(c("Nat.ofBool"), q)), pp.clone());
    let false_case = call(
        "Nat.add_lt_add",
        [
            r.clone(),
            p.clone(),
            r.clone(),
            p.clone(),
            hr.clone(),
            hr.clone(),
        ],
    );
    let sr = succ(r.clone());
    let ss = add(sr.clone(), sr.clone());
    let hss = call(
        "Nat.add_le_add",
        [sr.clone(), p.clone(), sr, p.clone(), hr.clone(), hr],
    );
    let rewrite = congr(
        c("Nat"),
        c("Nat"),
        c("Nat.succ"),
        add(succ(r.clone()), r.clone()),
        succ(rr.clone()),
        call("Nat.succ_add", [r.clone(), r]),
    );
    let true_case = subst(
        c("Nat"),
        lam(206, c("Nat"), le(v(206), pp.clone())),
        ss,
        succ(succ(rr.clone())),
        rewrite,
        hss,
    );
    bool_rec(
        lam(207, c("Bool"), goal(v(207))),
        false_case,
        true_case,
        bit,
    )
}

fn bound_at(f: Expr, w: Expr) -> Expr {
    pis(
        &[
            (210, c("Nat")),
            (211, c("Nat")),
            (212, c("Nat")),
            (213, lt(v(211), pow2(w.clone()))),
            (214, lt(v(212), pow2(w.clone()))),
        ],
        lt(aux(f, v(210), v(211), v(212)), pow2(w)),
    )
}

/// forall f, f false false = false -> forall w k a b,
/// a < 2^w -> b < 2^w -> bitwiseAux f k a b < 2^w.
/// Induction on w, then cases on the genuine fuel fold. No alternative
/// bitwise definition, assumed bound, or native reducer is introduced.
fn aux_bound() -> Expr {
    let f = v(208);
    let hf = v(209);
    let w = v(215);
    let k = v(210);
    let a = v(211);
    let b = v(212);
    let half = pow2(w.clone());
    let full = pow2(succ(w.clone()));
    let args = |limit: Expr| {
        vec![
            (210, c("Nat")),
            (211, c("Nat")),
            (212, c("Nat")),
            (213, lt(a.clone(), limit.clone())),
            (214, lt(b.clone(), limit)),
        ]
    };

    // Width zero forces both inputs to zero. Transport the actual zero-fuel
    // theorem through those two equalities, retaining every bound assumption.
    let zero_eq = |x: Expr, h: Expr| {
        call(
            "Nat.le_antisymm",
            [
                x.clone(),
                lit(0),
                call("Nat.le_of_succ_le_succ", [x.clone(), lit(0), h]),
                call("Nat.zero_le", [x]),
            ],
        )
    };
    let ea = zero_eq(a.clone(), v(213));
    let eb = zero_eq(b.clone(), v(214));
    let z = aux_zero(f.clone(), hf.clone(), k.clone());
    let zero_lt = subst(
        c("Nat"),
        lam(216, c("Nat"), lt(v(216), lit(1))),
        lit(0),
        aux(f.clone(), k.clone(), lit(0), lit(0)),
        symm(
            c("Nat"),
            aux(f.clone(), k.clone(), lit(0), lit(0)),
            lit(0),
            z,
        ),
        call("Nat.zero_lt_succ", [lit(0)]),
    );
    let b_lt = subst(
        c("Nat"),
        lam(
            216,
            c("Nat"),
            lt(aux(f.clone(), k.clone(), lit(0), v(216)), lit(1)),
        ),
        lit(0),
        b.clone(),
        symm(c("Nat"), b.clone(), lit(0), eb),
        zero_lt,
    );
    let a_lt = subst(
        c("Nat"),
        lam(
            216,
            c("Nat"),
            lt(aux(f.clone(), k.clone(), v(216), b.clone()), lit(1)),
        ),
        lit(0),
        a.clone(),
        symm(c("Nat"), a.clone(), lit(0), ea),
        b_lt,
    );
    let base = lambdas(&args(lit(1)), a_lt);

    // At positive width, the canonical fold's successor-fuel result is
    // (r+r)+ofBool bit, with the real div2 input bounds fed to the width IH.
    let da = call("Nat.div2", [a.clone()]);
    let db = call("Nat.div2", [b.clone()]);
    let r = aux(f.clone(), k.clone(), da.clone(), db.clone());
    let ha = call(
        "Nat.div2_lt_of_lt_two_pow_succ",
        [w.clone(), a.clone(), v(213)],
    );
    let hb = call(
        "Nat.div2_lt_of_lt_two_pow_succ",
        [w.clone(), b.clone(), v(214)],
    );
    let hr = Expr::apps(v(217), [k.clone(), da, db, ha, hb]);
    let bit = Expr::apps(
        f.clone(),
        [
            call("Nat.testBit", [a.clone(), lit(0)]),
            call("Nat.testBit", [b.clone(), lit(0)]),
        ],
    );
    let doubled = doubled_bit_bound(r.clone(), half.clone(), hr, bit.clone());
    let value = add(add(r.clone(), r), Expr::app(c("Nat.ofBool"), bit));
    let pp = add(half.clone(), half);
    let step_bound = subst(
        c("Nat"),
        lam(216, c("Nat"), lt(value.clone(), v(216))),
        pp.clone(),
        full.clone(),
        symm(
            c("Nat"),
            full.clone(),
            pp,
            call("Nat.pow_two_succ", [w.clone()]),
        ),
        doubled,
    );
    // Fuel is only case-split; the recursive fuel IH is unused because the
    // outer width IH handles the smaller input values at that exact fuel.
    let fuel_motive = lam(
        210,
        c("Nat"),
        pis(
            &args(full.clone())[1..],
            lt(
                aux(f.clone(), k.clone(), a.clone(), b.clone()),
                full.clone(),
            ),
        ),
    );
    let fuel_zero = lambdas(
        &args(full.clone())[1..],
        Expr::app(pow2_positive(), succ(w.clone())),
    );
    let fuel_step = lambdas(
        &[
            (210, c("Nat")),
            (218, Expr::app(fuel_motive.clone(), k.clone())),
        ],
        lambdas(&args(full.clone())[1..], step_bound),
    );
    let step = lambdas(
        &[(215, c("Nat")), (217, bound_at(f.clone(), w.clone()))],
        lam(210, c("Nat"), nat_rec(fuel_motive, fuel_zero, fuel_step, k)),
    );
    let body = nat_rec(
        lam(215, c("Nat"), bound_at(f.clone(), w.clone())),
        base,
        step,
        w,
    );
    lambdas(
        &[
            (208, f_ty()),
            (209, eq(c("Bool"), ff(f), c("Bool.false"))),
            (215, c("Nat")),
        ],
        body,
    )
}

/// A closed CIC proof, not a conversion claim: forall a k,
/// Nat.shiftLeft a k = a * 2^k, by induction on the actual recurrences.
fn shift_left_mul_pow() -> Expr {
    let a = v(240);
    let k = v(241);
    let shifted = |n| call("Nat.shiftLeft", [a.clone(), n]);
    let product = |n| call("Nat.mul", [a.clone(), pow2(n)]);
    let statement = |n: Expr| eq(c("Nat"), shifted(n.clone()), product(n));
    let base = symm(
        c("Nat"),
        call("Nat.mul", [a.clone(), lit(1)]),
        a.clone(),
        call("Nat.mul_one", [a.clone()]),
    );
    let old = call("Nat.mul", [shifted(k.clone()), lit(2)]);
    let mid = call("Nat.mul", [product(k.clone()), lit(2)]);
    let final_ = call(
        "Nat.mul",
        [a.clone(), call("Nat.mul", [pow2(k.clone()), lit(2)])],
    );
    let lifted = congr(
        c("Nat"),
        c("Nat"),
        lam(243, c("Nat"), call("Nat.mul", [v(243), lit(2)])),
        shifted(k.clone()),
        product(k.clone()),
        v(242),
    );
    let step = trans(
        old,
        mid,
        final_,
        lifted,
        call("Nat.mul_assoc", [a.clone(), pow2(k.clone()), lit(2)]),
    );
    let induction = nat_rec(
        lam(241, c("Nat"), statement(k.clone())),
        base,
        lambdas(&[(241, c("Nat")), (242, statement(k.clone()))], step),
        k,
    );
    lambdas(&[(240, c("Nat")), (241, c("Nat"))], induction)
}

/// Propose an equivalent Nat goal using exact shifts for mul-by-pow2 nodes.
/// Every rewrite carries its CIC equality. The original source judgment is
/// still checked independently; this is proof search, never IR lowering.
fn exact_shift_model(rhs: &Expr, depth: usize) -> Option<(Expr, Expr, bool)> {
    if depth > 64 {
        return None;
    }
    for op in [
        "Nat.mod",
        "Nat.add",
        "Nat.mul",
        "Nat.div",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
    ] {
        let Some(args) = args_of(rhs, op, 2) else {
            continue;
        };
        let (left, left_proof, left_changed) = exact_shift_model(args[0], depth + 1)?;
        let (right, right_proof, right_changed) = exact_shift_model(args[1], depth + 1)?;
        let rebuilt = call(op, [left.clone(), right.clone()]);
        let mid = call(op, [args[0].clone(), right.clone()]);
        let first = congr(
            c("Nat"),
            c("Nat"),
            lam(244, c("Nat"), call(op, [v(244), right.clone()])),
            left.clone(),
            args[0].clone(),
            left_proof,
        );
        let second = congr(
            c("Nat"),
            c("Nat"),
            lam(244, c("Nat"), call(op, [args[0].clone(), v(244)])),
            right.clone(),
            args[1].clone(),
            right_proof,
        );
        let operands = trans(rebuilt.clone(), mid, rhs.clone(), first, second);
        if op == "Nat.mul" {
            if let Some(power) = args_of(&right, "Nat.pow", 2) {
                if *power[0] == lit(2) {
                    let shifted = call("Nat.shiftLeft", [left.clone(), power[1].clone()]);
                    let bridge = Expr::apps(shift_left_mul_pow(), [left, power[1].clone()]);
                    return Some((
                        shifted.clone(),
                        trans(shifted, rebuilt, rhs.clone(), bridge, operands),
                        true,
                    ));
                }
            }
        }
        return Some((rebuilt, operands, left_changed || right_changed));
    }
    Some((rhs.clone(), refl(c("Nat"), rhs.clone()), false))
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

struct Step {
    wrapped: Expr,
    proof: Expr,
    bound: Expr,
}

fn build(width: u32, params: &[Expr], rhs: &Expr, depth: usize) -> Option<Step> {
    if depth > 64 {
        return None;
    }
    let modulus = crate::modulus(width);
    let prefix = format!("UInt{width}");
    if let Some(decoded) = args_of(rhs, &format!("{prefix}.toNat"), 1) {
        if !params.contains(decoded[0]) {
            return None;
        }
        let bitvec = Expr::app(c(&format!("{prefix}.toBitVec")), decoded[0].clone());
        let fin = call("BitVec.toFin", [lit(u64::from(width)), bitvec]);
        return Some(Step {
            wrapped: rhs.clone(),
            proof: refl(c("Nat"), rhs.clone()),
            bound: Expr::proj(Name::from_string("Fin"), 1, fin),
        });
    }
    if let ExprKind::Lit(Literal::Nat(n)) = rhs.kind() {
        let ExprKind::Lit(Literal::Nat(m)) = modulus.kind() else {
            return None;
        };
        if n >= m {
            return None;
        }
        let pred = Expr::nat_lit_u128((1u128 << width) - 1);
        let positive = call("Nat.zero_lt_succ", [pred]);
        return Some(Step {
            wrapped: rhs.clone(),
            proof: refl(c("Nat"), rhs.clone()),
            bound: call("Nat.mod_lt", [rhs.clone(), modulus, positive]),
        });
    }
    if let Some(args) = args_of(rhs, "Nat.div", 2) {
        let numerator = build(width, params, args[0], depth + 1)?;
        let old = call("Nat.div", [numerator.wrapped.clone(), args[1].clone()]);
        let operands = congr(
            c("Nat"),
            c("Nat"),
            lam(220, c("Nat"), call("Nat.div", [v(220), args[1].clone()])),
            numerator.wrapped,
            args[0].clone(),
            numerator.proof,
        );
        // This canonical theorem also covers divisor zero. No assumed bound,
        // native shift semantics or shift-range license is introduced here.
        let bound = call(
            "Nat.lt_of_le_of_lt",
            [
                rhs.clone(),
                args[0].clone(),
                modulus.clone(),
                call("Nat.div_le_self", [args[0].clone(), args[1].clone()]),
                numerator.bound,
            ],
        );
        let wrapped = call("Nat.mod", [old.clone(), modulus.clone()]);
        let reduced = call("Nat.mod", [rhs.clone(), modulus.clone()]);
        let lifted = congr(
            c("Nat"),
            c("Nat"),
            lam(220, c("Nat"), call("Nat.mod", [v(220), modulus.clone()])),
            old,
            rhs.clone(),
            operands,
        );
        let identity = call("Nat.mod_eq_of_lt", [rhs.clone(), modulus, bound.clone()]);
        return Some(Step {
            wrapped: wrapped.clone(),
            proof: trans(wrapped, reduced, rhs.clone(), lifted, identity),
            bound,
        });
    }
    if let Some(wrap_args) = args_of(rhs, "Nat.mod", 2) {
        if wrap_args[1] != &modulus {
            return None;
        }
        if let Some(args) = args_of(wrap_args[0], "Nat.shiftLeft", 2) {
            let numerator = build(width, params, args[0], depth + 1)?;
            let old = call(
                "Nat.shiftLeft",
                [numerator.wrapped.clone(), args[1].clone()],
            );
            let raw = wrap_args[0].clone();
            let operands = congr(
                c("Nat"),
                c("Nat"),
                lam(
                    220,
                    c("Nat"),
                    call("Nat.shiftLeft", [v(220), args[1].clone()]),
                ),
                numerator.wrapped,
                args[0].clone(),
                numerator.proof,
            );
            let wrapped = call("Nat.mod", [old.clone(), modulus.clone()]);
            let proof = congr(
                c("Nat"),
                c("Nat"),
                lam(220, c("Nat"), call("Nat.mod", [v(220), modulus.clone()])),
                old,
                raw.clone(),
                operands,
            );
            let positive = call(
                "Nat.zero_lt_succ",
                [Expr::nat_lit_u128((1u128 << width) - 1)],
            );
            return Some(Step {
                wrapped,
                proof,
                bound: call("Nat.mod_lt", [raw, modulus, positive]),
            });
        }
        for op in ["Nat.add", "Nat.mul"] {
            let Some(args) = args_of(wrap_args[0], op, 2) else {
                continue;
            };
            let left = build(width, params, args[0], depth + 1)?;
            let right = build(width, params, args[1], depth + 1)?;
            let old = call(op, [left.wrapped.clone(), right.wrapped.clone()]);
            let mid = call(op, [args[0].clone(), right.wrapped.clone()]);
            let first = congr(
                c("Nat"),
                c("Nat"),
                lam(220, c("Nat"), call(op, [v(220), right.wrapped.clone()])),
                left.wrapped,
                args[0].clone(),
                left.proof,
            );
            let second = congr(
                c("Nat"),
                c("Nat"),
                lam(220, c("Nat"), call(op, [args[0].clone(), v(220)])),
                right.wrapped,
                args[1].clone(),
                right.proof,
            );
            let raw = wrap_args[0].clone();
            let operands = trans(old.clone(), mid, raw.clone(), first, second);
            let wrapped = call("Nat.mod", [old.clone(), modulus.clone()]);
            let proof = congr(
                c("Nat"),
                c("Nat"),
                lam(220, c("Nat"), call("Nat.mod", [v(220), modulus.clone()])),
                old,
                raw.clone(),
                operands,
            );
            let positive = call(
                "Nat.zero_lt_succ",
                [Expr::nat_lit_u128((1u128 << width) - 1)],
            );
            return Some(Step {
                wrapped,
                proof,
                bound: call("Nat.mod_lt", [raw, modulus, positive]),
            });
        }
    }
    for (op, bool_op) in [
        ("Nat.land", "Bool.and"),
        ("Nat.lor", "Bool.or"),
        ("Nat.xor", "Bool.xor"),
    ] {
        let Some(args) = args_of(rhs, op, 2) else {
            continue;
        };
        let left = build(width, params, args[0], depth + 1)?;
        let right = build(width, params, args[1], depth + 1)?;
        let old = call(op, [left.wrapped.clone(), right.wrapped.clone()]);
        let mid = call(op, [args[0].clone(), right.wrapped.clone()]);
        let first = congr(
            c("Nat"),
            c("Nat"),
            lam(220, c("Nat"), call(op, [v(220), right.wrapped.clone()])),
            left.wrapped,
            args[0].clone(),
            left.proof,
        );
        let second = congr(
            c("Nat"),
            c("Nat"),
            lam(220, c("Nat"), call(op, [args[0].clone(), v(220)])),
            right.wrapped,
            args[1].clone(),
            right.proof,
        );
        let operands = trans(old.clone(), mid, rhs.clone(), first, second);
        let bound = Expr::apps(
            aux_bound(),
            [
                c(bool_op),
                refl(c("Bool"), c("Bool.false")),
                lit(u64::from(width)),
                add(args[0].clone(), args[1].clone()),
                args[0].clone(),
                args[1].clone(),
                left.bound,
                right.bound,
            ],
        );
        let wrapped = call("Nat.mod", [old.clone(), modulus.clone()]);
        let reduced = call("Nat.mod", [rhs.clone(), modulus.clone()]);
        let wrapped_operands = congr(
            c("Nat"),
            c("Nat"),
            lam(220, c("Nat"), call("Nat.mod", [v(220), modulus.clone()])),
            old,
            rhs.clone(),
            operands,
        );
        let identity = call("Nat.mod_eq_of_lt", [rhs.clone(), modulus, bound.clone()]);
        return Some(Step {
            wrapped: wrapped.clone(),
            proof: trans(wrapped, reduced, rhs.clone(), wrapped_operands, identity),
            bound,
        });
    }
    None
}

pub(super) fn candidate(width: u32, params: &[Expr], rhs: &Expr) -> Option<Expr> {
    if args_of(rhs, "Nat.land", 2).is_none()
        && args_of(rhs, "Nat.lor", 2).is_none()
        && args_of(rhs, "Nat.xor", 2).is_none()
        && args_of(rhs, "Nat.mod", 2).is_none()
        && args_of(rhs, "Nat.div", 2).is_none()
    {
        return None;
    }
    Some(build(width, params, rhs, 0)?.proof)
}

pub(super) fn shifted_candidate(width: u32, params: &[Expr], rhs: &Expr) -> Option<Expr> {
    let (exact, bridge, changed) = exact_shift_model(rhs, 0)?;
    if !changed {
        return None;
    }
    let step = build(width, params, &exact, 0)?;
    Some(trans(step.wrapped, exact, rhs.clone(), step.proof, bridge))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_equation_shift_left_mul_pow_is_a_checked_universal_induction() {
        let mut env = clean_kernel::Environment::with_prelude();
        let a = v(240);
        let k = v(241);
        let shifted = call("Nat.shiftLeft", [a.clone(), k.clone()]);
        let statement = pis(
            &[(240, c("Nat")), (241, c("Nat"))],
            eq(
                c("Nat"),
                shifted.clone(),
                call("Nat.mul", [a.clone(), pow2(k.clone())]),
            ),
        );
        let proof = shift_left_mul_pow();
        let audit = env.audit_certification(&statement, &proof);
        assert!(audit.is_certified(), "actual induction: {:?}", audit.issues);
        let name = Name::from_string("SourceEquation.shiftLeftMulPow");
        env.add_decl(clean_kernel::Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof.clone(),
        })
        .expect("replay the closed universal induction");
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        let wrong = pis(
            &[(240, c("Nat")), (241, c("Nat"))],
            eq(c("Nat"), shifted, call("Nat.mul", [a, pow2(succ(k))])),
        );
        assert!(
            !env.audit_certification(&wrong, &proof).is_certified(),
            "the actual induction cannot prove the wrong exponent"
        );
    }

    #[test]
    fn source_equation_bitwise_bound_checks_the_actual_canonical_fold() {
        let env = clean_kernel::Environment::with_prelude();
        let statement = pis(
            &[
                (208, f_ty()),
                (209, eq(c("Bool"), ff(v(208)), c("Bool.false"))),
                (215, c("Nat")),
            ],
            bound_at(v(208), v(215)),
        );
        let audit = env.audit_certification(&statement, &aux_bound());
        assert!(
            audit.is_certified(),
            "actual fold bound: {:?}",
            audit.issues
        );
        let zero_bound = call("Nat.zero_lt_succ", [lit(0)]);
        for (f, hf, a, ha) in [
            (
                lambdas(&[(221, c("Bool")), (222, c("Bool"))], c("Bool.true")),
                refl(c("Bool"), c("Bool.false")),
                lit(0),
                zero_bound.clone(),
            ),
            (
                c("Bool.or"),
                refl(c("Bool"), c("Bool.false")),
                lit(1),
                zero_bound.clone(),
            ),
        ] {
            let invalid = Expr::apps(
                aux_bound(),
                [f, hf, lit(0), lit(1), a, lit(0), ha, zero_bound.clone()],
            );
            assert!(
                !env.audit_certification(&lt(lit(1), lit(1)), &invalid)
                    .is_certified(),
                "neither a false Boolean zero premise nor a false input bound proves 1 < 1"
            );
        }
    }

    #[test]
    fn source_equation_bitwise_supporting_arithmetic_is_kernel_checked() {
        let env = clean_kernel::Environment::with_prelude();
        let power_statement = pi(200, c("Nat"), lt(lit(0), pow2(v(200))));
        let f = v(208);
        let hf_type = eq(c("Bool"), ff(f.clone()), c("Bool.false"));
        let zero_statement = pis(
            &[(208, f_ty()), (209, hf_type.clone()), (203, c("Nat"))],
            eq(c("Nat"), aux(f.clone(), v(203), lit(0), lit(0)), lit(0)),
        );
        let zero_proof = lambdas(
            &[(208, f_ty()), (209, hf_type), (203, c("Nat"))],
            aux_zero(f, v(209), v(203)),
        );
        let bindings = [
            (223, c("Nat")),
            (224, c("Nat")),
            (225, lt(v(223), v(224))),
            (226, c("Bool")),
        ];
        let doubled_statement = pis(
            &bindings,
            lt(
                add(add(v(223), v(223)), Expr::app(c("Nat.ofBool"), v(226))),
                add(v(224), v(224)),
            ),
        );
        let doubled_proof = lambdas(&bindings, doubled_bit_bound(v(223), v(224), v(225), v(226)));
        for (label, statement, proof) in [
            ("power positivity", power_statement, pow2_positive()),
            ("zero inputs", zero_statement, zero_proof),
            ("doubled bit bound", doubled_statement, doubled_proof),
        ] {
            let audit = env.audit_certification(&statement, &proof);
            assert!(audit.is_certified(), "{label}: {:?}", audit.issues);
        }
    }
}

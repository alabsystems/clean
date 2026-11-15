// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Systematic instance generators for rule families whose conclusions are computed by the
//! checker, or whose side conditions depend on sorts, binder names or constants that mutation
//! of a few seeds rarely reaches.
//!
//! Where the conclusion is computed by the checker (bit-blasting circuits, `evaluate`, `forall_inst`
//! substitutions, ...), the generator leaves it open with `; @@fill hole` and lets the checker
//! supply its own term; the battery then judges that term. Everything else enumerates or samples
//! candidate conclusions, valid and invalid alike, and lets the checker decide.

use crate::model::Rng;
use crate::oracle::{Instance, FILL_MARKER};

fn inst(defs: String, proof: String) -> Instance {
    Instance { defs, proof }
}

fn fill(defs: String, hole_sort: &str, proof: String) -> Instance {
    Instance {
        defs: format!("{}\n(declare-const hole {})\n", defs, hole_sort),
        proof: format!("{}hole\n{}", FILL_MARKER, proof),
    }
}

fn bits(v: u64, w: usize) -> String {
    let mut s = String::from("#b");
    for i in (0..w).rev() {
        s.push(if (v >> i) & 1 == 1 { '1' } else { '0' });
    }
    s
}

fn bv_decls(w: usize) -> String {
    let mut d = String::new();
    for v in ["x", "y", "z"] {
        d.push_str(&format!("(declare-const {} (_ BitVec {}))\n", v, w));
    }
    for i in 0..w {
        d.push_str(&format!(
            "(declare-const a{} Bool)\n(declare-const b{} Bool)\n(declare-const c{} Bool)\n",
            i, i, i
        ));
    }
    d
}

fn bbterm(prefix: &str, w: usize) -> String {
    let mut s = String::from("(@bbterm");
    for i in 0..w {
        s.push_str(&format!(" {}{}", prefix, i));
    }
    s.push(')');
    s
}

/// Bit-blasting rules: every operator, widths 1..=4, over variables, bit terms and constants.
fn bitblast(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let binary = [
        ("bvand", "bitblast_and"),
        ("bvor", "bitblast_or"),
        ("bvxor", "bitblast_xor"),
        ("bvxnor", "bitblast_xnor"),
        ("bvadd", "bitblast_add"),
        ("bvmul", "bitblast_mult"),
        ("bvshl", "bitblast_shl"),
        ("bvlshr", "bitblast_lshr"),
        ("bvashr", "bitblast_ashr"),
        ("bvudiv", "bitblast_udiv"),
        ("bvurem", "bitblast_urem"),
    ];
    for w in 1..=4usize {
        let decls = bv_decls(w);
        let operands: Vec<String> = {
            let mut v = vec![
                "x".to_owned(),
                "y".to_owned(),
                bbterm("a", w),
                bbterm("b", w),
            ];
            for _ in 0..3 {
                v.push(bits(rng.next_u64() % (1 << w), w));
            }
            v
        };
        let bv = format!("(_ BitVec {})", w);
        for (op, rule) in binary {
            for l in &operands {
                for r in &operands {
                    out.push((
                        rule.into(),
                        fill(
                            decls.clone(),
                            &bv,
                            format!(
                                "(step t1 (cl (= ({} {} {}) hole)) :rule {})",
                                op, l, r, rule
                            ),
                        ),
                    ));
                }
            }
            if matches!(op, "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul") {
                out.push((
                    rule.into(),
                    fill(
                        decls.clone(),
                        &bv,
                        format!(
                            "(step t1 (cl (= ({} x {} z) hole)) :rule {})",
                            op,
                            bbterm("b", w),
                            rule
                        ),
                    ),
                ));
            }
        }
        for (op, rule) in [("bvult", "bitblast_ult"), ("bvslt", "bitblast_slt")] {
            for l in &operands {
                for r in &operands {
                    out.push((
                        rule.into(),
                        fill(
                            decls.clone(),
                            "Bool",
                            format!(
                                "(step t1 (cl (= ({} {} {}) hole)) :rule {})",
                                op, l, r, rule
                            ),
                        ),
                    ));
                }
            }
        }
        for l in &operands {
            out.push((
                "bitblast_not".into(),
                fill(
                    decls.clone(),
                    &bv,
                    format!("(step t1 (cl (= (bvnot {}) hole)) :rule bitblast_not)", l),
                ),
            ));
            out.push((
                "bitblast_neg".into(),
                fill(
                    decls.clone(),
                    &bv,
                    format!("(step t1 (cl (= (bvneg {}) hole)) :rule bitblast_neg)", l),
                ),
            ));
            out.push((
                "bitblast_var".into(),
                fill(
                    decls.clone(),
                    &bv,
                    format!("(step t1 (cl (= {} hole)) :rule bitblast_var)", l),
                ),
            ));
            for r in &operands {
                out.push((
                    "bitblast_equal".into(),
                    fill(
                        decls.clone(),
                        "Bool",
                        format!(
                            "(step t1 (cl (= (= {} {}) hole)) :rule bitblast_equal)",
                            l, r
                        ),
                    ),
                ));
                out.push((
                    "bitblast_comp".into(),
                    fill(
                        decls.clone(),
                        "(_ BitVec 1)",
                        format!(
                            "(step t1 (cl (= (bvcomp {} {}) hole)) :rule bitblast_comp)",
                            l, r
                        ),
                    ),
                ));
                out.push((
                    "bitblast_concat".into(),
                    fill(
                        format!("{}", decls),
                        &format!("(_ BitVec {})", 2 * w),
                        format!(
                            "(step t1 (cl (= (concat {} {}) hole)) :rule bitblast_concat)",
                            l, r
                        ),
                    ),
                ));
            }
            for k in 0..=2 {
                out.push(("bitblast_sign_extend".into(), fill(decls.clone(), &format!("(_ BitVec {})", w + k), format!("(step t1 (cl (= ((_ sign_extend {}) {}) hole)) :rule bitblast_sign_extend)", k, l))));
            }
            for i in 0..w {
                for j in 0..=i {
                    out.push(("bitblast_extract".into(), fill(decls.clone(), &format!("(_ BitVec {})", i - j + 1), format!("(step t1 (cl (= ((_ extract {} {}) {}) hole)) :rule bitblast_extract)", i, j, l))));
                }
            }
        }
        // Constants: the checker computes nothing, so enumerate every bit pattern.
        for v in 0..(1u64 << w) {
            for pattern in 0..(1u64 << w) {
                let bb: Vec<&str> = (0..w)
                    .map(|i| {
                        if (pattern >> i) & 1 == 1 {
                            "true"
                        } else {
                            "false"
                        }
                    })
                    .collect();
                out.push((
                    "bitblast_const".into(),
                    inst(
                        decls.clone(),
                        format!(
                            "(step t1 (cl (= {} (@bbterm {}))) :rule bitblast_const)",
                            bits(v, w),
                            bb.join(" ")
                        ),
                    ),
                ));
            }
        }
    }
}

/// `evaluate` over every ground operator application on small constants.
fn evaluate(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let defs = String::new();
    let bv_bin = [
        "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvmul", "bvsub", "bvudiv",
        "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
    ];
    let bv_cmp = [
        "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ];
    for w in 1..=4usize {
        let bv = format!("(_ BitVec {})", w);
        let all: Vec<u64> = (0..(1u64 << w)).collect();
        let pairs: Vec<(u64, u64)> = if w <= 3 {
            all.iter()
                .flat_map(|a| all.iter().map(move |b| (*a, *b)))
                .collect()
        } else {
            (0..40)
                .map(|_| (rng.next_u64() % 16, rng.next_u64() % 16))
                .collect()
        };
        for (a, b) in &pairs {
            for op in bv_bin {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &bv,
                        format!(
                            "(step t1 (cl (= ({} {} {}) hole)) :rule evaluate)",
                            op,
                            bits(*a, w),
                            bits(*b, w)
                        ),
                    ),
                ));
            }
            for op in bv_cmp {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        "Bool",
                        format!(
                            "(step t1 (cl (= ({} {} {}) hole)) :rule evaluate)",
                            op,
                            bits(*a, w),
                            bits(*b, w)
                        ),
                    ),
                ));
            }
            out.push((
                "evaluate".into(),
                fill(
                    defs.clone(),
                    "(_ BitVec 1)",
                    format!(
                        "(step t1 (cl (= (bvcomp {} {}) hole)) :rule evaluate)",
                        bits(*a, w),
                        bits(*b, w)
                    ),
                ),
            ));
            out.push((
                "evaluate".into(),
                fill(
                    defs.clone(),
                    &format!("(_ BitVec {})", 2 * w),
                    format!(
                        "(step t1 (cl (= (concat {} {}) hole)) :rule evaluate)",
                        bits(*a, w),
                        bits(*b, w)
                    ),
                ),
            ));
        }
        for a in &all {
            let c = bits(*a, w);
            for op in ["bvnot", "bvneg"] {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &bv,
                        format!("(step t1 (cl (= ({} {}) hole)) :rule evaluate)", op, c),
                    ),
                ));
            }
            for op in ["ubv_to_int", "sbv_to_int"] {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        "Int",
                        format!("(step t1 (cl (= ({} {}) hole)) :rule evaluate)", op, c),
                    ),
                ));
            }
            for k in 0..=2 {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &format!("(_ BitVec {})", w + k),
                        format!(
                            "(step t1 (cl (= ((_ zero_extend {}) {}) hole)) :rule evaluate)",
                            k, c
                        ),
                    ),
                ));
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &format!("(_ BitVec {})", w + k),
                        format!(
                            "(step t1 (cl (= ((_ sign_extend {}) {}) hole)) :rule evaluate)",
                            k, c
                        ),
                    ),
                ));
            }
            for k in 0..=w + 1 {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &bv,
                        format!(
                            "(step t1 (cl (= ((_ rotate_left {}) {}) hole)) :rule evaluate)",
                            k, c
                        ),
                    ),
                ));
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &bv,
                        format!(
                            "(step t1 (cl (= ((_ rotate_right {}) {}) hole)) :rule evaluate)",
                            k, c
                        ),
                    ),
                ));
            }
            for n in 1..=2 {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &format!("(_ BitVec {})", w * n),
                        format!(
                            "(step t1 (cl (= ((_ repeat {}) {}) hole)) :rule evaluate)",
                            n, c
                        ),
                    ),
                ));
            }
            for i in 0..w {
                for j in 0..=i {
                    out.push((
                        "evaluate".into(),
                        fill(
                            defs.clone(),
                            &format!("(_ BitVec {})", i - j + 1),
                            format!(
                                "(step t1 (cl (= ((_ extract {} {}) {}) hole)) :rule evaluate)",
                                i, j, c
                            ),
                        ),
                    ));
                }
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        "Bool",
                        format!(
                            "(step t1 (cl (= ((_ @bit_of {}) {}) hole)) :rule evaluate)",
                            i, c
                        ),
                    ),
                ));
            }
        }
        for n in -5i64..=5 {
            out.push((
                "evaluate".into(),
                fill(
                    defs.clone(),
                    &bv,
                    format!(
                        "(step t1 (cl (= ((_ int_to_bv {}) {}) hole)) :rule evaluate)",
                        w,
                        int(n)
                    ),
                ),
            ));
        }
    }
    let ints: Vec<i64> = (-4..=4).collect();
    for a in &ints {
        for b in &ints {
            for op in ["div", "mod", "+", "-", "*"] {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        "Int",
                        format!(
                            "(step t1 (cl (= ({} {} {}) hole)) :rule evaluate)",
                            op,
                            int(*a),
                            int(*b)
                        ),
                    ),
                ));
            }
            for op in ["<", "<=", ">", ">="] {
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        "Bool",
                        format!(
                            "(step t1 (cl (= ({} {} {}) hole)) :rule evaluate)",
                            op,
                            int(*a),
                            int(*b)
                        ),
                    ),
                ));
            }
            out.push((
                "evaluate".into(),
                fill(
                    defs.clone(),
                    "Real",
                    format!(
                        "(step t1 (cl (= (/ {} {}) hole)) :rule evaluate)",
                        real(*a),
                        real(*b)
                    ),
                ),
            ));
        }
        out.push((
            "evaluate".into(),
            fill(
                defs.clone(),
                "Int",
                format!("(step t1 (cl (= (abs {}) hole)) :rule evaluate)", int(*a)),
            ),
        ));
        out.push((
            "evaluate".into(),
            fill(
                defs.clone(),
                "Int",
                format!(
                    "(step t1 (cl (= (to_int (/ {} 2.0)) hole)) :rule evaluate)",
                    real(*a)
                ),
            ),
        ));
        out.push((
            "evaluate".into(),
            fill(
                defs.clone(),
                "Bool",
                format!(
                    "(step t1 (cl (= (is_int (/ {} 2.0)) hole)) :rule evaluate)",
                    real(*a)
                ),
            ),
        ));
    }
    // Int/Real mixing and equalities over constants.
    for (l, r) in [
        ("1", "1.0"),
        ("2", "1.0"),
        ("(- 1)", "(- 1.0)"),
        ("0", "0.0"),
    ] {
        out.push((
            "evaluate".into(),
            fill(
                defs.clone(),
                "Bool",
                format!("(step t1 (cl (= (= {} {}) hole)) :rule evaluate)", l, r),
            ),
        ));
    }
}

fn int(n: i64) -> String {
    if n < 0 {
        format!("(- {})", -n)
    } else {
        n.to_string()
    }
}

fn real(n: i64) -> String {
    if n < 0 {
        format!("(- {}.0)", -n)
    } else {
        format!("{}.0", n)
    }
}

/// Arithmetic simplifications over constants, including zero divisors and negative operands.
fn arith_simplify(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const n Int)\n(declare-const x Real)\n".to_owned();
    for a in -4i64..=4 {
        for b in -4i64..=4 {
            for r in -5i64..=5 {
                out.push((
                    "mod_simplify".into(),
                    inst(
                        defs.clone(),
                        format!(
                            "(step t1 (cl (= (mod {} {}) {})) :rule mod_simplify)",
                            int(a),
                            int(b),
                            int(r)
                        ),
                    ),
                ));
                out.push((
                    "div_simplify".into(),
                    inst(
                        defs.clone(),
                        format!(
                            "(step t1 (cl (= (div {} {}) {})) :rule div_simplify)",
                            int(a),
                            int(b),
                            int(r)
                        ),
                    ),
                ));
            }
        }
    }
    for t in ["n", "(+ n 1)", "0", "(- 1)", "2"] {
        for r in ["1", "0", "n"] {
            out.push((
                "div_simplify".into(),
                inst(
                    defs.clone(),
                    format!(
                        "(step t1 (cl (= (div {} {}) {})) :rule div_simplify)",
                        t, t, r
                    ),
                ),
            ));
        }
    }
    for t in ["x", "(+ x 1.0)", "0.0", "2.0"] {
        for r in ["1.0", "0.0", "x"] {
            out.push((
                "div_simplify".into(),
                inst(
                    defs.clone(),
                    format!(
                        "(step t1 (cl (= (/ {} {}) {})) :rule div_simplify)",
                        t, t, r
                    ),
                ),
            ));
        }
    }
}

/// Linear arithmetic lemmas over one or two variables of either sort.
fn linear_arithmetic(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let defs = "(declare-const i Int)\n(declare-const j Int)\n(declare-const r Real)\n(declare-const s Real)\n".to_owned();
    let int_atoms = [
        "i",
        "j",
        "(* 2 i)",
        "(- i j)",
        "(+ i j)",
        "(* 3 j)",
        "(* 0.5 i)",
    ];
    let real_atoms = ["r", "s", "(* 2.0 r)", "(- r s)", "(* 0.5 r)", "(+ r 1.0)"];
    let int_consts = ["0", "1", "2", "(- 1)", "3"];
    let real_consts = ["0.0", "0.5", "1.0", "(- 0.5)", "1.5", "2.0"];
    let ops = ["<", "<=", ">", ">=", "="];
    let coeffs = ["1", "2", "3", "0", "1.0", "0.5", "2.0", "(- 1)", "1.5"];
    for _ in 0..60_000 {
        let n = 1 + rng.below(3);
        let mut lits = Vec::new();
        for _ in 0..n {
            let use_real = rng.chance(50);
            let lhs = if use_real {
                rng.pick(&real_atoms)
            } else {
                rng.pick(&int_atoms)
            }
            .unwrap();
            let rhs = if use_real {
                rng.pick(&real_consts)
            } else {
                rng.pick(&int_consts)
            }
            .unwrap();
            let op = rng.pick(&ops).unwrap();
            let lit = format!("({} {} {})", op, lhs, rhs);
            lits.push(if rng.chance(50) || *op == "=" {
                format!("(not {})", lit)
            } else {
                lit
            });
        }
        let args: Vec<&str> = (0..n).map(|_| *rng.pick(&coeffs).unwrap()).collect();
        let clause = lits.join(" ");
        out.push((
            "la_generic".into(),
            inst(
                defs.clone(),
                format!(
                    "(step t1 (cl {}) :rule la_generic :args ({}))",
                    clause,
                    args.join(" ")
                ),
            ),
        ));
        let k = rng.below(n + 1);
        out.push((
            "bounded_farkas".into(),
            inst(
                defs.clone(),
                format!(
                    "(step t1 (cl {}) :rule bounded_farkas :args ({}))",
                    clause,
                    args[..k].join(" ")
                ),
            ),
        ));
        if n == 1 {
            out.push((
                "la_tautology".into(),
                inst(
                    defs.clone(),
                    format!("(step t1 (cl {}) :rule la_tautology)", clause),
                ),
            ));
        }
    }
}

/// `aci_simp` and `ac_simp` on terms with repeated arguments, nesting and identity elements.
fn aci(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let defs = "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const r Real)\n(declare-const x (_ BitVec 3))\n(declare-const y (_ BitVec 3))\n".to_owned();
    let families: [(&str, &[&str], &str); 10] = [
        ("and", &["p", "q", "true"], "true"),
        ("or", &["p", "q", "false"], "false"),
        ("+", &["i", "j", "0"], "0"),
        ("*", &["i", "j", "1"], "1"),
        ("bvadd", &["x", "y", "#b000"], "#b000"),
        ("bvmul", &["x", "y", "#b001"], "#b001"),
        ("bvxor", &["x", "y", "#b000"], "#b000"),
        ("bvand", &["x", "y", "#b111"], "#b111"),
        ("bvor", &["x", "y", "#b000"], "#b000"),
        ("concat", &["x", "y"], ""),
    ];
    for _ in 0..30_000 {
        let (op, atoms, _id) = families[rng.below(families.len())];
        let n = 2 + rng.below(3);
        let mut args: Vec<String> = Vec::new();
        for _ in 0..n {
            if rng.chance(25) {
                let a = rng.pick(atoms).unwrap();
                let b = rng.pick(atoms).unwrap();
                args.push(format!("({} {} {})", op, a, b));
            } else {
                args.push(rng.pick(atoms).unwrap().to_string());
            }
        }
        let lhs = format!("({} {})", op, args.join(" "));
        // Candidate right-hand sides: flattened, deduplicated, identity-free, permuted, dropped.
        let mut flat: Vec<String> = Vec::new();
        for a in &args {
            if let Some(inner) = a.strip_prefix(&format!("({} ", op)) {
                flat.extend(inner.trim_end_matches(')').split(' ').map(str::to_owned));
            } else {
                flat.push(a.clone());
            }
        }
        let mut dedup: Vec<String> = Vec::new();
        for a in &flat {
            if !dedup.contains(a) {
                dedup.push(a.clone());
            }
        }
        let mut candidates = vec![flat.clone(), dedup.clone()];
        let mut perm = flat.clone();
        if perm.len() > 1 {
            let (a, b) = (rng.below(perm.len()), rng.below(perm.len()));
            perm.swap(a, b);
        }
        candidates.push(perm);
        let mut dropped = flat.clone();
        if dropped.len() > 1 {
            dropped.remove(rng.below(dropped.len()));
        }
        candidates.push(dropped);
        for cand in candidates {
            let rhs = if cand.len() == 1 {
                cand[0].clone()
            } else {
                format!("({} {})", op, cand.join(" "))
            };
            out.push((
                "aci_simp".into(),
                inst(
                    defs.clone(),
                    format!("(step t1 (cl (= {} {})) :rule aci_simp)", lhs, rhs),
                ),
            ));
            if op == "and" || op == "or" {
                out.push((
                    "ac_simp".into(),
                    inst(
                        defs.clone(),
                        format!("(step t1 (cl (= {} {})) :rule ac_simp)", lhs, rhs),
                    ),
                ));
            }
        }
    }
}

/// `beta_equiv` with partial application and binder names that clash with free variables.
fn beta(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let defs = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n".to_owned();
    let names = ["x", "y", "z", "w"];
    let args_pool = ["x", "y", "z", "1", "(+ x 1)", "(* y 2)"];
    for _ in 0..8_000 {
        let k = 1 + rng.below(3);
        let mut binders: Vec<&str> = Vec::new();
        while binders.len() < k {
            let n = rng.pick(&names).unwrap();
            if !binders.contains(n) {
                binders.push(n);
            }
        }
        let body_atoms: Vec<&str> = binders.iter().copied().chain(["x", "y", "1"]).collect();
        let body = format!(
            "(+ {} (* 2 {}))",
            rng.pick(&body_atoms).unwrap(),
            rng.pick(&body_atoms).unwrap()
        );
        let applied = 1 + rng.below(k);
        let args: Vec<&str> = (0..applied)
            .map(|_| *rng.pick(&args_pool).unwrap())
            .collect();
        let lambda = format!(
            "(lambda ({}) {})",
            binders
                .iter()
                .map(|b| format!("({} Int)", b))
                .collect::<Vec<_>>()
                .join(" "),
            body
        );
        let lhs = format!("({} {})", lambda, args.join(" "));
        // Naive textual substitution (which captures) and the evaluator decides.
        let mut subst = body.clone();
        for (b, a) in binders.iter().zip(&args) {
            subst = subst_symbol(&subst, b, &format!("@@{}", a));
        }
        let subst = subst.replace("@@", "");
        let rest = &binders[applied..];
        let rhs = if rest.is_empty() {
            subst.clone()
        } else {
            format!(
                "(lambda ({}) {})",
                rest.iter()
                    .map(|b| format!("({} Int)", b))
                    .collect::<Vec<_>>()
                    .join(" "),
                subst
            )
        };
        out.push((
            "beta_equiv".into(),
            inst(
                defs.clone(),
                format!("(step t1 (cl (= {} {})) :rule beta_equiv)", lhs, rhs),
            ),
        ));
    }
}

fn subst_symbol(text: &str, name: &str, with: &str) -> String {
    let mut out = String::new();
    let mut token = String::new();
    let flush = |token: &mut String, out: &mut String| {
        if token == name {
            out.push_str(with);
        } else {
            out.push_str(token);
        }
        token.clear();
    };
    for c in text.chars() {
        if c.is_whitespace() || c == '(' || c == ')' {
            flush(&mut token, &mut out);
            out.push(c);
        } else {
            token.push(c);
        }
    }
    flush(&mut token, &mut out);
    out
}

/// Array extensionality with witness names that clash with free variables.
fn arrays(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x Int)\n(declare-const i Int)\n(declare-const v Int)\n(declare-const c (Array Int Int))\n(declare-const d (Array Int Int))\n(declare-fun g (Int) (Array Int Int))\n".to_owned();
    let pairs = [
        ("(store c x v)", "c"),
        ("(g x)", "d"),
        ("c", "d"),
        ("(store c i v)", "(store d x v)"),
    ];
    for (a, b) in pairs {
        for w in ["x", "i", "v", "k"] {
            let choice = format!(
                "(choice (({} Int)) (or (= {} {}) (not (= (select {} {}) (select {} {})))))",
                w, a, b, a, w, b, w
            );
            let proof = format!(
                "(assume h (not (= {} {})))\n(step t1 (cl (not (= (select {} {}) (select {} {})))) :rule arrays_ext :premises (h))",
                a, b, a, choice, b, choice
            );
            out.push(("arrays_ext".into(), inst(defs.clone(), proof)));
        }
    }
}

/// `assume` matching and `refl` go through `polyeq`/`alpha_equiv`, which identify syntactically
/// different terms. Pair terms that are equal, unequal, or equal only modulo a false rewrite.
fn polyeq(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const i Int)\n(declare-const j Int)\n(declare-const r Real)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const y Int)\n".to_owned();
    let terms = [
        "(- 5)",
        "5",
        "(- 5.0)",
        "5.0",
        "(/ 1 2)",
        "(/ 1 (- 2))",
        "(- (/ 1 2))",
        "(- 2.0)",
        "0.5",
        "(- r)",
        "r",
        "(+ i)",
        "i",
        "(- i)",
        "(* i)",
        "(- i j)",
        "(- (- i j))",
        "(+ i j 1)",
        "(+ (+ i j) 1)",
        "(- (- i j) 1)",
        "(- i j 1)",
        "(- i (- j 1))",
    ];
    for a in terms {
        for b in terms {
            out.push((
                "assume".into(),
                inst(
                    format!("{}(assert (= r {}))\n", defs, real_like(a)),
                    format!("(assume h (= r {}))", real_like(b)),
                ),
            ));
            out.push((
                "refl".into(),
                inst(
                    defs.clone(),
                    format!("(step t1 (cl (= {} {})) :rule refl)", a, b),
                ),
            ));
        }
    }
    let binder_pairs = [
        (
            "(and (= y 1) (forall ((y Int)) (= y 1)))",
            "(and (= 1 y) (forall ((z Int)) (= 1 y)))",
        ),
        (
            "(and (= y 1) (exists ((y Int)) (= y 1)))",
            "(and (= 1 y) (exists ((z Int)) (= 1 y)))",
        ),
        (
            "(or (= i j) (forall ((i Int)) (= i j)))",
            "(or (= j i) (forall ((k Int)) (= j i)))",
        ),
    ];
    for (a, b) in binder_pairs {
        out.push((
            "refl".into(),
            inst(
                defs.clone(),
                format!("(step t1 (cl (= {} {})) :rule refl)", a, b),
            ),
        ));
        out.push((
            "assume".into(),
            inst(
                format!("{}(assert {})\n", defs, a),
                format!("(assume h {})", b),
            ),
        ));
    }
}

fn real_like(t: &str) -> String {
    // Keep the pair well-sorted for `r`: integer literals are only used where Carcara accepts them.
    t.to_owned()
}

/// `forall_inst` with instantiation terms that clash with inner binders.
fn forall_inst(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x Int)\n(declare-const y Int)\n(declare-const y_renamed Int)\n(declare-fun P (Int Int) Bool)\n".to_owned();
    let bodies = [
        "(exists ((y Int)) (P y x))",
        "(forall ((y Int)) (P x y))",
        "(and (P x y) (exists ((x Int)) (P x y)))",
        "(exists ((y Int) (x Int)) (P y x))",
        "(exists ((y Int)) (and (P y x) (P y_renamed y)))",
        "(let ((y x)) (P y y))",
        "(let ((y y)) (P y x))",
        "(let ((z x) (y x)) (P z y))",
        "(exists ((y Int)) (let ((y_renamed y)) (P y_renamed x)))",
    ];
    for body in bodies {
        for t in ["y", "x", "(+ y 1)", "0", "y_renamed", "(+ y y_renamed)"] {
            let proof = format!(
                "(step t1 (cl (or (not (forall ((x Int)) {})) hole)) :rule forall_inst :args ({}))",
                body, t
            );
            out.push(("forall_inst".into(), fill(defs.clone(), "Bool", proof)));
        }
    }
}

/// Pseudo-Boolean ith-bit lemmas with arguments outside {0, 1} and a clashing choice variable.
fn pbblast(out: &mut Vec<(String, Instance)>) {
    let defs =
        "(declare-const x (_ BitVec 2))\n(declare-const z Int)\n(declare-const k Int)\n".to_owned();
    for (a, b) in [
        ("5", "0"),
        ("z", "0"),
        ("((_ @int_of 0) x)", "((_ @int_of 1) x)"),
        ("k", "z"),
        ("2", "2"),
    ] {
        out.push((
            "pbblast_bvand_ith_bit".into(),
            fill(defs.clone(), "Int", format!("(step t1 (cl (and (>= {a} hole) (>= {b} hole) (>= (+ hole 1) (+ {a} {b})))) :rule pbblast_bvand_ith_bit :args ({a} {b}))")),
        ));
        out.push((
            "pbblast_bvxor_ith_bit".into(),
            fill(defs.clone(), "Int", format!("(step t1 (cl (and (>= (+ {a} {b}) hole) (>= (+ hole {a}) {b}) (>= (+ hole {b}) {a}) (>= 2 (+ hole {a} {b})))) :rule pbblast_bvxor_ith_bit :args ({a} {b}))")),
        ));
    }
}

/// `qnt_cnf` where prenexing pulls a binder over a free occurrence of the same name.
fn qnt_cnf(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x Int)\n(declare-const y Int)\n".to_owned();
    let cases = [
        (
            "(forall ((y Int)) (or (forall ((x Int)) (= x 0)) (= x 1)))",
            "(forall ((x Int)) (or (= x 0) (= x 1)))",
        ),
        (
            "(forall ((y Int)) (or (forall ((x Int)) (= x y)) (= x 1)))",
            "(forall ((y Int) (x Int)) (or (= x y) (= x 1)))",
        ),
        (
            "(forall ((y Int)) (or (forall ((x Int)) (= x 0)) (forall ((x Int)) (= x 1))))",
            "(forall ((x Int)) (or (= x 0) (= x 1)))",
        ),
        (
            "(forall ((y Int)) (and (forall ((x Int)) (= x y)) (= x y)))",
            "(forall ((y Int) (x Int)) (= x y))",
        ),
    ];
    for (l, r) in cases {
        out.push((
            "qnt_cnf".into(),
            inst(
                defs.clone(),
                format!("(step t1 (cl (or (not {}) {})) :rule qnt_cnf)", l, r),
            ),
        ));
    }
}

/// `bitblast_extract` and `bitblast_concat` require the right-hand side to already be a bit term,
/// so the checker cannot fill it in; enumerate the correct bit lists and near misses instead.
fn bitblast_structural(out: &mut Vec<(String, Instance)>) {
    for w in 1..=3usize {
        let decls = bv_decls(w);
        let bits_of = |x: &str, k: usize| {
            if x == "x" {
                format!("((_ @bit_of {}) x)", k)
            } else {
                format!("a{}", k)
            }
        };
        for x in ["x", "(@bbterm a0 a1 a2)"] {
            let xs = if x == "x" {
                "x".to_owned()
            } else {
                bbterm("a", w)
            };
            let x_name = if x == "x" { "x" } else { "a" };
            for i in 0..w {
                for j in 0..=i {
                    let good: Vec<String> = (j..=i).map(|k| bits_of(x_name, k)).collect();
                    let mut reversed = good.clone();
                    reversed.reverse();
                    let shifted: Vec<String> =
                        (j..=i).map(|k| bits_of(x_name, (k + 1) % w)).collect();
                    for rhs in [good, reversed, shifted] {
                        out.push((
                            "bitblast_extract".into(),
                            inst(decls.clone(), format!("(step t1 (cl (= ((_ extract {} {}) {}) (@bbterm {}))) :rule bitblast_extract)", i, j, xs, rhs.join(" "))),
                        ));
                    }
                }
            }
        }
        let xbits: Vec<String> = (0..w).map(|k| format!("a{}", k)).collect();
        let ybits: Vec<String> = (0..w).map(|k| format!("b{}", k)).collect();
        for (l, r) in [
            (xbits.clone(), ybits.clone()),
            (ybits.clone(), xbits.clone()),
        ] {
            let rhs = [r.clone(), l.clone()].concat();
            let wrong = [l.clone(), r.clone()].concat();
            for bits in [rhs, wrong] {
                out.push((
                    "bitblast_concat".into(),
                    inst(decls.clone(), format!("(step t1 (cl (= (concat (@bbterm {}) (@bbterm {})) (@bbterm {}))) :rule bitblast_concat)", l.join(" "), r.join(" "), bits.join(" "))),
                ));
            }
        }
    }
}

/// Seeds that are mutated like Carcara's own rule tests: context-introducing subproofs whose inner
/// steps are checked rules (the upstream tests use `hole` there, which the oracle cannot judge).
pub fn mutation_seeds() -> Vec<(String, Instance)> {
    let defs = "(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-fun P (U) Bool)\n(declare-fun Q (U U) Bool)\n(declare-fun f (U) U)\n(declare-const p Bool)\n(declare-const q Bool)\n".to_owned();
    let seeds = [
        ("bind", "(anchor :step t1 :args ((y U) (:= (x U) y)))\n(step t1.t1 (cl (= (P x) (P y))) :rule refl)\n(step t1 (cl (= (forall ((x U)) (P x)) (forall ((y U)) (P y)))) :rule bind)"),
        ("bind", "(anchor :step t1 :args ((y U) (:= (x U) y)))\n(step t1.t1 (cl (= x y)) :rule refl)\n(step t1.t2 (cl (= (f x) (f y))) :rule cong :premises (t1.t1))\n(step t1.t3 (cl (= (P (f x)) (P (f y)))) :rule cong :premises (t1.t2))\n(step t1 (cl (= (exists ((x U)) (P (f x))) (exists ((y U)) (P (f y))))) :rule bind)"),
        ("bind", "(anchor :step t1 :args ((y U) (z U) (:= (x U) y) (:= (w U) z)))\n(step t1.t1 (cl (= (Q x w) (Q y z))) :rule refl)\n(step t1 (cl (= (forall ((x U) (w U)) (Q x w)) (forall ((y U) (z U)) (Q y z)))) :rule bind)"),
        ("onepoint", "(anchor :step t1 :args ((:= (x U) a)))\n(step t1.t1 (cl (= (=> (= x a) (P x)) (=> (= a a) (P a)))) :rule refl)\n(step t1 (cl (= (forall ((x U)) (=> (= x a) (P x))) (=> (= a a) (P a)))) :rule onepoint)"),
        ("onepoint", "(anchor :step t1 :args ((:= (x U) a)))\n(step t1.t1 (cl (= (and (= x a) (P x)) (and (= a a) (P a)))) :rule refl)\n(step t1 (cl (= (exists ((x U)) (and (= x a) (P x))) (and (= a a) (P a)))) :rule onepoint)"),
        ("onepoint", "(anchor :step t1 :args ((y U) (:= (x U) a)))\n(step t1.t1 (cl (= (or (not (= x a)) (Q x y)) (or (not (= a a)) (Q a y)))) :rule refl)\n(step t1 (cl (= (forall ((y U) (x U)) (or (not (= x a)) (Q x y))) (forall ((y U)) (or (not (= a a)) (Q a y))))) :rule onepoint)"),
        ("sko_ex", "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (P x)))))\n(step t1.t1 (cl (= (P x) (P (choice ((x U)) (P x))))) :rule refl)\n(step t1 (cl (= (exists ((x U)) (P x)) (P (choice ((x U)) (P x))))) :rule sko_ex)"),
        ("sko_ex", "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (exists ((y U)) (Q x y)))) (:= (y U) (choice ((y U)) (Q (choice ((x U)) (exists ((y U)) (Q x y))) y)))))\n(step t1.t1 (cl (= (Q x y) (Q (choice ((x U)) (exists ((y U)) (Q x y))) (choice ((y U)) (Q (choice ((x U)) (exists ((y U)) (Q x y))) y))))) :rule refl)\n(step t1 (cl (= (exists ((x U) (y U)) (Q x y)) (Q (choice ((x U)) (exists ((y U)) (Q x y))) (choice ((y U)) (Q (choice ((x U)) (exists ((y U)) (Q x y))) y))))) :rule sko_ex)"),
        ("sko_forall", "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (not (P x))))))\n(step t1.t1 (cl (= (P x) (P (choice ((x U)) (not (P x)))))) :rule refl)\n(step t1 (cl (= (forall ((x U)) (P x)) (P (choice ((x U)) (not (P x)))))) :rule sko_forall)"),
        ("let", "(anchor :step t1 :args ((:= (x U) a)))\n(step t1.t1 (cl (= (P x) (P a))) :rule refl)\n(step t1 (cl (= (let ((x a)) (P x)) (P a))) :rule let)"),
        ("let", "(assume h (= a b))\n(anchor :step t1 :args ((:= (x U) b)))\n(step t1.t1 (cl (= (Q x a) (Q b a))) :rule refl)\n(step t1 (cl (= (let ((x a)) (Q x a)) (Q b a))) :rule let :premises (h))"),
        ("subproof", "(anchor :step t1)\n(assume t1.h1 (and p q))\n(step t1.t2 (cl p) :rule and :premises (t1.h1) :args (0))\n(step t1 (cl (not (and p q)) p) :rule subproof :discharge (t1.h1))"),
        ("subproof", "(anchor :step t1)\n(assume t1.h1 (P a))\n(assume t1.h2 (not (P a)))\n(step t1.t3 (cl) :rule resolution :premises (t1.h1 t1.h2))\n(step t1 (cl (not (P a)) (not (not (P a))) false) :rule subproof :discharge (t1.h1 t1.h2))"),
        ("refl", "(anchor :step t1 :args ((y U) (:= (x U) y)))\n(step t1.t1 (cl (= (forall ((y U)) (Q x y)) (forall ((y U)) (Q y y)))) :rule refl)\n(step t1 (cl (= (exists ((x U)) (forall ((y U)) (Q x y))) (exists ((y U)) (forall ((y U)) (Q y y))))) :rule bind)"),
        ("forall_inst", "(step t1 (cl (or (not (forall ((x U) (y U)) (Q x y))) (Q a b))) :rule forall_inst :args (a b))"),
        ("qnt_rm_unused", "(step t1 (cl (= (forall ((x U) (y U)) (P x)) (forall ((x U)) (P x)))) :rule qnt_rm_unused)"),
        ("miniscope_split", "(step t1 (cl (= (forall ((x U) (y U)) (or (P x) (P y))) (or (forall ((x U)) (P x)) (forall ((y U)) (P y))))) :rule miniscope_split)"),
        ("qnt_join", "(step t1 (cl (= (forall ((x U)) (forall ((y U)) (Q x y))) (forall ((x U) (y U)) (Q x y)))) :rule qnt_join)"),
        ("ho_cong", "(declare-fun g (U) U)\n(step t1 (cl (= f f)) :rule refl)\n(step t2 (cl (= a a)) :rule refl)\n(step t3 (cl (= (f a) (f a))) :rule ho_cong :premises (t1 t2))"),
    ];
    seeds
        .iter()
        .map(|(family, proof)| {
            let (extra_defs, proof) = match proof.strip_prefix("(declare-fun g (U) U)\n") {
                Some(rest) => ("(declare-fun g (U) U)\n", rest),
                None => ("", *proof),
            };
            (
                family.to_string(),
                inst(format!("{}{}", defs, extra_defs), proof.to_owned()),
            )
        })
        .collect()
}

/// `poly_simp_rel`: the premise relates two scaled differences, the conclusion their relations.
fn poly_simp_rel(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const r Real)\n(declare-const s Real)\n(declare-const x (_ BitVec 3))\n(declare-const y (_ BitVec 3))\n(declare-const u (_ BitVec 3))\n(declare-const v (_ BitVec 3))\n".to_owned();
    let int_coeffs = ["1", "2", "(- 1)", "(- 2)", "0"];
    let real_coeffs = ["1.0", "2.0", "(- 1.0)", "(- 2.0)", "0.0", "0.5"];
    // (left difference, right difference, conclusion operands, coefficients)
    let shapes: [(&str, &str, (&str, &str, &str, &str), &[&str]); 2] = [
        ("(- i j)", "(- k l)", ("i", "j", "k", "l"), &int_coeffs),
        (
            "(to_real (- i j))",
            "(- r s)",
            ("i", "j", "r", "s"),
            &real_coeffs,
        ),
    ];
    for (l, r, (x1, x2, y1, y2), coeffs) in shapes {
        for c1 in coeffs {
            for c2 in coeffs {
                for op in ["<", "<=", "=", ">=", ">"] {
                    out.push((
                        "poly_simp_rel".into(),
                        inst(
                            defs.clone(),
                            format!(
                                "(assume h (= (* {c1} {l}) (* {c2} {r})))\n(step t1 (cl (= ({op} {x1} {x2}) ({op} {y1} {y2}))) :rule poly_simp_rel :premises (h))"
                            ),
                        ),
                    ));
                }
            }
        }
    }
    for c1 in ["#b001", "#b010", "#b011", "#b111"] {
        for c2 in ["#b001", "#b100", "#b101"] {
            out.push((
                "poly_simp_rel".into(),
                inst(
                    defs.clone(),
                    format!("(assume h (= (bvmul {c1} (bvsub x y)) (bvmul {c2} (bvsub u v))))\n(step t1 (cl (= (= x y) (= u v))) :rule poly_simp_rel :premises (h))"),
                ),
            ));
        }
    }
}

/// Added in Clean: the scalar modular rule's accepted and refused cases are
/// judged independently over every 3-bit assignment, including aliases that
/// are not syntactically identical. Default/upstream still refuses the new
/// non-reflexive cases; `--dialect clean` selects the explicit rule extension.
fn bv_offset_equality(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x (_ BitVec 3))(declare-const y (_ BitVec 3))";
    for a in [0, 1, 7] {
        for b in [0, 1, 7] {
            for first in [false, true] {
                let left = if first {
                    format!("(bvadd (_ bv{a} 3) x)")
                } else {
                    format!("(bvadd x (_ bv{a} 3))")
                };
                for base in ["x", "y"] {
                    let right = format!("(bvadd (_ bv{b} 3) {base})");
                    for target in [
                        "true".to_owned(),
                        "false".to_owned(),
                        format!("(= (_ bv{a} 3) (_ bv{b} 3))"),
                    ] {
                        out.push(("eq_simplify".into(), inst(defs.to_owned(), format!("(step t1 (cl (= (= {left} {right}) {target})) :rule eq_simplify)"))));
                    }
                }
            }
        }
    }
}

/// Added in Clean: a separate rule/capability for bounded offset spines.
/// Both claimed truth values and distinct opaque bases are judged by the
/// independent finite-model oracle; the old Clean dialect leaves this rule
/// unknown rather than widening immediate eq_simplify.
fn bv_offset_spines_v1(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x (_ BitVec 3))(declare-const y (_ BitVec 3))";
    for a in [0, 1, 7] {
        for b in [0, 1, 7] {
            for op in ["bvadd", "bvsub"] {
                let left = format!("({op} (bvadd (_ bv{a} 3) x) (_ bv{b} 3))");
                for base in ["x", "y"] {
                    for k in [0, 1, 7] {
                        let right = format!("(bvadd {base} (_ bv{k} 3))");
                        for truth in [false, true] {
                            out.push(("eq_simplify_bv_offset_spines".into(),inst(defs.to_owned(),format!("(step t1 (cl (= (= {left} {right}) {truth})) :rule eq_simplify_bv_offset_spines)"))));
                        }
                    }
                }
            }
        }
    }
}

/// Independently interpreted small-word reconstruction and causal wrong bases.
fn bv_reconstruct_v1(out: &mut Vec<(String, Instance)>) {
    fn permutations(xs: &mut [(usize, usize)], at: usize, results: &mut Vec<Vec<(usize, usize)>>) {
        if at == xs.len() {
            results.push(xs.to_vec());
            return;
        }
        for i in at..xs.len() {
            xs.swap(at, i);
            permutations(xs, at + 1, results);
            xs.swap(at, i);
        }
    }
    for width in 1..=5 {
        let defs =
            format!("(declare-const x (_ BitVec {width}))(declare-const y (_ BitVec {width}))");
        for cuts in 0..(1usize << (width - 1)) {
            let mut ranges = Vec::new();
            let mut low = 0;
            for high in 0..width {
                if high + 1 == width || cuts & (1 << high) != 0 {
                    ranges.push((low, high + 1 - low));
                    low = high + 1;
                }
            }
            let mut orders = Vec::new();
            permutations(&mut ranges, 0, &mut orders);
            for ranges in orders {
                let mut packed = None;
                for (low, span) in ranges {
                    let p = format!(
                        "((_ zero_extend {}) ((_ extract {} {low}) x))",
                        width - span,
                        low + span - 1
                    );
                    let p = if low == 0 {
                        p
                    } else {
                        format!("(bvshl {p} (_ bv{low} {width}))")
                    };
                    packed = Some(match packed {
                        None => p,
                        Some(first) => format!("(bvor {first} {p})"),
                    });
                }
                for word in ["x", "y"] {
                    out.push((
                        "bv_reconstruct_v1".into(),
                        inst(
                            defs.clone(),
                            format!(
                                "(step t1 (cl (= {} {word})) :rule bv_reconstruct_v1)",
                                packed.as_ref().unwrap()
                            ),
                        ),
                    ));
                }
            }
        }
    }
}

/// Binder scoping over *finite* sorts: alpha-equivalence, capture-avoiding substitution and the
/// `let` binding values.
///
/// The `polyeq`, `forall_inst` and `beta` generators above build their binders over `Int`, where
/// every quantifier the oracle meets evaluates to `Unknown` — which is why a whole family of
/// capture and binder-list defects survived them. Everything here is `Bool`-sorted, so the
/// evaluator decides each conclusion outright.
fn binder_scoping(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const x Bool)\n(declare-const y Bool)\n(declare-const z Bool)\n\
                (declare-const t Bool)\n(declare-const p Bool)\n(declare-const q Bool)\n\
                (declare-const a Bool)\n(declare-const y_renamed Bool)\n"
        .to_owned();

    // Alpha-equivalence: binder lists of different lengths, and `let` values, which SMT-LIB
    // evaluates in the enclosing scope because `let` binds in parallel.
    let terms = [
        "(forall ((x Bool)) (or x y))",
        "(forall ((x Bool) (y Bool)) (or x y))",
        "(forall ((w Bool)) (or w y))",
        "(exists ((x Bool)) (and x y))",
        "(exists ((x Bool) (y Bool)) (and x y))",
        "(exists ((w Bool)) (and w y))",
        "(let ((x true)) (and x y))",
        "(let ((x true) (y true)) (and x y))",
        "(let ((w true)) (and w y))",
        // `x` and `z` are declared constants, so under SMT-LIB's parallel `let` the value of `y`
        // is the *outer* `x` on the left and the *outer* `z` on the right
        "(let ((x true) (y x)) y)",
        "(let ((z true) (y z)) y)",
        "(let ((z true) (y x)) y)",
        "(let ((x true) (y z)) y)",
        "(forall ((y Bool)) (or y y_renamed))",
        "(forall ((y_renamed Bool)) (or y_renamed y_renamed))",
        "(forall ((y Bool) (y_renamed Bool)) (or y y_renamed))",
    ];
    for l in terms {
        for r in terms {
            out.push((
                "refl".into(),
                inst(
                    defs.clone(),
                    format!("(step t1 (cl (= {} {})) :rule refl)", l, r),
                ),
            ));
        }
    }

    // `forall_inst` and `beta_equiv`: the checker computes the instance, the battery judges it.
    // The bodies rebind the instantiation term's variables, mention a name that a `_renamed`
    // rename would collide with, and hide a variable in a `let` value.
    let bodies = [
        "(forall ((y Bool)) (or x y y_renamed))",
        "(exists ((y Bool)) (and (or x y) (or y_renamed y)))",
        "(let ((y x)) (= y x))",
        "(let ((y y)) (or y x))",
        "(let ((y x) (y_renamed y)) (= y y_renamed))",
        "(and (forall ((w Bool)) (or w (not w))) (let ((y x)) (= y x)))",
        "(exists ((y Bool)) (let ((y_renamed y)) (or y_renamed x)))",
        "(or x (forall ((y_renamed Bool)) (or y_renamed x)))",
        "(forall ((y Bool)) (forall ((y_renamed Bool)) (or x y y_renamed)))",
    ];
    for body in bodies {
        // The `let` arguments are what make the free variables of a *value* matter: the capture
        // analysis reads them off `free_vars`, which used to skip `let` values entirely
        for arg in [
            "y",
            "y_renamed",
            "a",
            "true",
            "(and y y_renamed)",
            "x",
            "(let ((w y)) w)",
            "(let ((w y_renamed)) (and w a))",
            "(let ((y y)) y)",
        ] {
            out.push((
                "forall_inst".into(),
                fill(
                    defs.clone(),
                    "Bool",
                    format!(
                        "(step t1 (cl (or (not (forall ((x Bool)) {})) hole)) \
                         :rule forall_inst :args ({}))",
                        body, arg
                    ),
                ),
            ));
            out.push((
                "beta_equiv".into(),
                fill(
                    defs.clone(),
                    "Bool",
                    format!(
                        "(step t1 (cl (= ((lambda ((x Bool)) {}) {}) hole)) :rule beta_equiv)",
                        body, arg
                    ),
                ),
            ));
        }
    }

    // `bind` over a `refl` that has to rename the anchor's bound variable.
    let bind_cases = [
        (
            "(exists ((y Bool)) (xor y y_renamed))",
            "(exists ((z Bool)) (xor z z))",
            "(forall ((x Bool)) (exists ((y Bool)) (xor y y_renamed)))",
            "(forall ((y Bool)) (exists ((z Bool)) (xor z z)))",
        ),
        (
            "(exists ((y Bool)) (xor y y_renamed))",
            "(exists ((z Bool)) (xor z y_renamed))",
            "(forall ((x Bool)) (exists ((y Bool)) (xor y y_renamed)))",
            "(forall ((y Bool)) (exists ((z Bool)) (xor z y_renamed)))",
        ),
        (
            "(let ((y x)) (= y x))",
            "(let ((y y)) (= y y))",
            "(forall ((x Bool)) (let ((y x)) (= y x)))",
            "(forall ((y Bool)) (let ((y y)) (= y y)))",
        ),
    ];
    for (inner_l, inner_r, outer_l, outer_r) in bind_cases {
        out.push((
            "bind".into(),
            inst(
                defs.clone(),
                format!(
                    "(anchor :step t1 :args ((y Bool) (:= (x Bool) y)))\n\
                     (step t1.t1 (cl (= {} {})) :rule refl)\n\
                     (step t1 (cl (= {} {})) :rule bind)",
                    inner_l, inner_r, outer_l, outer_r
                ),
            ),
        ));
    }
}

/// `onepoint` points read from under a binder that rebinds the eliminated variable, or that binds
/// a variable of the point's own term.
fn onepoint_scoping(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n\
                (declare-const z U)\n(declare-fun P (U) Bool)\n(declare-fun Q (U U) Bool)\n"
        .to_owned();
    let cases = [
        // The point sits under an `exists` that rebinds `x`
        (
            "(:= (x U) a)",
            "(=> (exists ((x U)) (= x a)) (P x))",
            "(=> (exists ((x U)) (= x a)) (P a))",
            "(forall ((x U)) (=> (exists ((x U)) (= x a)) (P x)))",
        ),
        (
            "(:= (x U) a)",
            "(and (exists ((x U)) (= x a)) (P x))",
            "(and (exists ((x U)) (= x a)) (P a))",
            "(exists ((x U)) (and (exists ((x U)) (= x a)) (P x)))",
        ),
        // The point's term is a variable the inner binder binds
        (
            "(:= (x U) z)",
            "(=> (exists ((z U)) (= x z)) (P x))",
            "(=> (exists ((z_renamed U)) (= z z_renamed)) (P z))",
            "(forall ((x U)) (=> (exists ((z U)) (= x z)) (P x)))",
        ),
        (
            "(:= (x U) z)",
            "(and (exists ((z U)) (= x z)) (P x))",
            "(and (exists ((z_renamed U)) (= z z_renamed)) (P z))",
            "(exists ((x U)) (and (exists ((z U)) (= x z)) (P x)))",
        ),
        // Sound controls: the nested binder shadows neither the point nor its term
        (
            "(:= (x U) a)",
            "(=> (and (= x a) (exists ((w U)) (P w))) (P x))",
            "(=> (and (= a a) (exists ((w U)) (P w))) (P a))",
            "(forall ((x U)) (=> (and (= x a) (exists ((w U)) (P w))) (P x)))",
        ),
        (
            "(:= (x U) a)",
            "(and (= x a) (exists ((w U)) (Q x w)))",
            "(and (= a a) (exists ((w U)) (Q a w)))",
            "(exists ((x U)) (and (= x a) (exists ((w U)) (Q x w))))",
        ),
    ];
    for (assign, body, exported, quantified) in cases {
        out.push((
            "onepoint".into(),
            inst(
                defs.clone(),
                format!(
                    "(anchor :step t1 :args ({}))\n\
                     (step t1.t1 (cl (= {} {})) :rule refl)\n\
                     (step t1 (cl (= {} {})) :rule onepoint)",
                    assign, body, exported, quantified, exported
                ),
            ),
        ));
    }
}

/// `string_decompose` at split points that the premise does not bound from below, and
/// `re_unfold_neg` over a word whose free variables the generated quantifier may capture.
fn strings_scoping(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const s String)\n(declare-const w String)\n(declare-const n Int)\n\
                (declare-const L Int)\n"
        .to_owned();
    let prefix = |t: &str, n: &str| format!("(str.substr {} 0 {})", t, n);
    let suffix_rem =
        |t: &str, n: &str| format!("(str.substr {} {} (- (str.len {}) {}))", t, n, t, n);

    for word in ["s", "(str.substr s 0 L)", "(str.++ s w)"] {
        for split in [
            "0",
            "1",
            "2",
            "(- 1)",
            "(- 2)",
            "n",
            "(- n)",
            "(str.len s)",
            "(- (str.len s) 1)",
            "(+ n 1)",
        ] {
            for rev in [false, true] {
                let at = if rev {
                    format!("(- (str.len {}) {})", word, split)
                } else {
                    split.to_owned()
                };
                let w1 = prefix(word, &at);
                let w2 = suffix_rem(word, &at);
                let measured = if rev { &w2 } else { &w1 };
                out.push((
                    "string_decompose".into(),
                    inst(
                        defs.clone(),
                        format!(
                            "(assume h (>= (str.len {}) {}))\n\
                             (step t1 (cl (and (= {} (str.++ {} {})) (= (str.len {}) {}))) \
                             :rule string_decompose :premises (h) :args ({}))",
                            word, split, word, w1, w2, measured, split, rev
                        ),
                    ),
                ));
            }
        }
    }

    // `re_unfold_neg` hard-codes the quantified length variable, so a word with a free variable of
    // that name has it captured.
    for word in ["s", "(str.substr s 0 L)", "(str.substr s L 1)"] {
        for (re, r1, r2) in [
            (
                r#"(re.++ (str.to_re "a") (str.to_re "b"))"#,
                r#"(str.to_re "a")"#,
                r#"(str.to_re "b")"#,
            ),
            (
                r#"(re.++ (str.to_re "a") (str.to_re ""))"#,
                r#"(str.to_re "a")"#,
                r#"(str.to_re "")"#,
            ),
        ] {
            for var in ["L", "M"] {
                let pref = format!("(str.substr {} 0 {})", word, var);
                let suff = format!(
                    "(str.substr {} {} (- (str.len {}) {}))",
                    word, var, word, var
                );
                out.push((
                    "re_unfold_neg".into(),
                    inst(
                        defs.clone(),
                        format!(
                            "(assume h (not (str.in_re {} {})))\n\
                             (step t1 (cl (forall (({} Int)) (or (< {} 0) \
                             (< (str.len {}) {}) (not (str.in_re {} {})) \
                             (not (str.in_re {} {}))))) :rule re_unfold_neg :premises (h))",
                            word, re, var, var, word, var, pref, r1, suff, r2
                        ),
                    ),
                ));
            }
        }
        for star in [r#"(re.* (str.to_re "a"))"#] {
            for var in ["L", "M"] {
                let pref = format!("(str.substr {} 0 {})", word, var);
                let suff = format!(
                    "(str.substr {} {} (- (str.len {}) {}))",
                    word, var, word, var
                );
                out.push((
                    "re_unfold_neg".into(),
                    inst(
                        defs.clone(),
                        format!(
                            "(assume h (not (str.in_re {} {})))\n\
                             (step t1 (cl (and (not (= {} \"\")) \
                             (forall (({} Int)) (or (<= {} 0) (< (str.len {}) {}) \
                             (not (str.in_re {} (str.to_re \"a\"))) \
                             (not (str.in_re {} {})))))) :rule re_unfold_neg :premises (h))",
                            word, star, word, var, var, word, var, pref, suff, star
                        ),
                    ),
                ));
            }
        }
    }

    // The positive unfoldings name the components of the decomposition with Skolem witnesses whose
    // defining formula quantifies the regular languages away, leaving the witness constrained only
    // to be a factor of the word. Over a *constant* word the oracle decides these outright,
    // because the conclusion then contradicts itself for every value the witness could take: the
    // equality forces `K` to be the middle factor while `(str.in_re K ...)` forces it to end with
    // the last one.
    let const_witness = |t: &str| {
        format!(
            r#"(choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= "{}" (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1))))"#,
            t
        )
    };
    out.push((
        "re_concat_unfold_pos".into(),
        inst(
            "(declare-const b RegLan)\n".to_owned(),
            format!(
                "(assume h (str.in_re \"abc\" (re.++ (str.to_re \"a\") b (str.to_re \"c\"))))\n\
                 (step t1 (cl (and (= \"abc\" (str.++ \"a\" {} \"c\")) (and (str.in_re {} (re.++ b (str.to_re \"c\"))) true))) :rule re_concat_unfold_pos :premises (h))",
                const_witness("abc"),
                const_witness("abc")
            ),
        ),
    ));
    out.push((
        "re_kleene_star_unfold_pos".into(),
        inst(
            String::new(),
            format!(
                "(assume h (str.in_re \"bb\" (re.* (str.to_re \"b\"))))\n\
                 (step t1 (cl (or (= \"bb\" \"\") (str.in_re \"bb\" (str.to_re \"b\")) (and (and (= \"bb\" (str.++ \"b\" {} \"b\")) (str.in_re {} (re.++ (re.* (str.to_re \"b\")) (str.to_re \"b\"))) true) (not (= \"b\" \"\")) (not (= \"b\" \"\"))))) :rule re_kleene_star_unfold_pos :premises (h))",
                const_witness("bb"),
                const_witness("bb")
            ),
        ),
    ));

    // The same shapes over a symbolic word, which the oracle cannot judge; these only exercise the
    // checker. Their rejection is pinned by `carcara/tests/rules/strings.rs` and by the end-to-end
    // fixtures in `crates/clean-auto/.../carcara_verify/soundness`.
    let witness = r#"(choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= s (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1))))"#;
    out.push((
        "re_concat_unfold_pos".into(),
        inst(
            defs.clone(),
            format!(
                "(assume h (str.in_re s (re.++ (str.to_re \"a\") (re.* (str.to_re \"b\")) (str.to_re \"c\"))))\n\
                 (step t1 (cl (and (= s (str.++ \"a\" {} \"c\")) (and (str.in_re {} (re.++ (re.* (str.to_re \"b\")) (str.to_re \"c\"))) true))) :rule re_concat_unfold_pos :premises (h))",
                witness, witness
            ),
        ),
    ));
    out.push((
        "re_concat_unfold_pos".into(),
        inst(
            defs.clone(),
            "(assume h (str.in_re s (re.++ (str.to_re \"a\") (str.to_re \"b\"))))\n\
             (step t1 (cl (= s (str.++ \"a\" \"b\"))) :rule re_concat_unfold_pos :premises (h))"
                .to_owned(),
        ),
    ));
    let kleene_witness = r#"(choice ((x String)) (exists ((k_0 String) (R_0 RegLan) (R_1 RegLan)) (and (= s (str.++ k_0 x)) (str.in_re k_0 R_0) (str.in_re x R_1))))"#;
    out.push((
        "re_kleene_star_unfold_pos".into(),
        inst(
            defs,
            format!(
                "(assume h (str.in_re s (re.* (str.to_re \"abc\"))))\n\
                 (step t1 (cl (or (= s \"\") (str.in_re s (str.to_re \"abc\")) (and (and (= s (str.++ \"abc\" {} \"abc\")) (str.in_re {} (re.++ (re.* (str.to_re \"abc\")) (str.to_re \"abc\"))) true) (not (= \"abc\" \"\")) (not (= \"abc\" \"\"))))) :rule re_kleene_star_unfold_pos :premises (h))",
                kleene_witness, kleene_witness
            ),
        ),
    ));
}

/// `evaluate` over bitvector literals written `(_ bv<n> <w>)` with `n` outside `[0, 2^w)`, which
/// SMT-LIB reads modulo `2^w`.
fn bv_literals(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-const u (_ BitVec 2))\n".to_owned();
    for w in [1usize, 2, 3] {
        let modulus = 1u64 << w;
        for n in [
            0u64,
            1,
            modulus - 1,
            modulus,
            modulus + 1,
            2 * modulus + 1,
            9,
        ] {
            for other in 0..modulus {
                let lit = format!("(_ bv{} {})", n, w);
                let rhs = bits(other, w);
                for op in ["=", "bvult", "bvule", "bvslt"] {
                    out.push((
                        "evaluate".into(),
                        fill(
                            defs.clone(),
                            "Bool",
                            format!(
                                "(step t1 (cl (= ({} {} {}) hole)) :rule evaluate)",
                                op, lit, rhs
                            ),
                        ),
                    ));
                }
                out.push((
                    "evaluate".into(),
                    fill(
                        defs.clone(),
                        &format!("(_ BitVec {})", w),
                        format!(
                            "(step t1 (cl (= (bvadd {} {}) hole)) :rule evaluate)",
                            lit, rhs
                        ),
                    ),
                ));
            }
        }
    }
}

/// Alpha-equivalence of a `let` nested inside another binder, where the `let` rebinds a variable
/// that its own values mention. The values are compared in the enclosing scope; an equality found
/// there must not be reused in the body, where the name means the `let`'s own variable. Each side
/// is named independently, so the same text in the body can denote the outer variable on one
/// side and the rebound one on the other.
fn binder_cache(out: &mut Vec<(String, Instance)>, rng: &mut Rng) {
    let defs = "(declare-const p Bool)\n(declare-const u Bool)\n(declare-const v Bool)\n\
                (declare-const z Bool)\n(declare-const w Bool)\n"
        .to_owned();

    // One side: the outer binder over `outer`, then `(let ((first V1) (w V2)) (op R1 R2))`,
    // where `V1`, `V2` are `outer` or its negation and `R1`, `R2` are names as written.
    #[allow(clippy::too_many_arguments)]
    fn side(
        kind: usize,
        outer: &str,
        first: &str,
        v1: bool,
        v2: bool,
        extra: bool,
        op: &str,
        r1: &str,
        r2: &str,
    ) -> String {
        let val = |neg: bool| {
            if neg {
                format!("(not {})", outer)
            } else {
                outer.to_owned()
            }
        };
        let extra_binding = if extra { " (k true)" } else { "" };
        let inner = format!(
            "(let (({} {}) (w {}){}) ({} {} {}))",
            first,
            val(v1),
            val(v2),
            extra_binding,
            op,
            r1,
            r2
        );
        match kind {
            0 => format!("(let (({} p)) {})", outer, inner),
            1 => format!("(forall (({} Bool)) {})", outer, inner),
            2 => format!("(exists (({} Bool)) {})", outer, inner),
            _ => format!("(forall ((q Bool)) (let (({} q)) {}))", outer, inner),
        }
    }

    // The counterexamples that were accepted, fixed so every run has them
    for kind in 0..3 {
        let op = if kind == 2 { "and" } else { "or" };
        let l = side(kind, "u", "u", true, false, false, op, "u", "w");
        let r = side(kind, "v", "z", true, false, false, op, "v", "w");
        out.push((
            "refl".into(),
            inst(
                defs.clone(),
                format!("(step t1 (cl (= {} {})) :rule refl)", l, r),
            ),
        ));
    }

    let outers = ["u", "v"];
    let firsts = ["u", "v", "z"];
    let refs = ["u", "v", "z", "w"];
    let ops = ["or", "and", "xor", "="];
    for _ in 0..6000 {
        let kind = rng.below(4);
        let (v1, v2, extra) = (rng.chance(50), rng.chance(50), rng.chance(30));
        let op = ops[rng.below(ops.len())];
        let pick_side = |rng: &mut Rng| {
            side(
                kind,
                outers[rng.below(2)],
                firsts[rng.below(3)],
                v1,
                v2,
                extra,
                op,
                refs[rng.below(4)],
                refs[rng.below(4)],
            )
        };
        let l = pick_side(rng);
        let r = pick_side(rng);
        out.push((
            "refl".into(),
            inst(
                defs.clone(),
                format!("(step t1 (cl (= {} {})) :rule refl)", l, r),
            ),
        ));
    }
}

/// Bit-vector terms of widths at and above `2^32`, over small values the independent evaluator
/// computes exactly without materializing `2^w`. Carcara cast widths to `u32`, reading a width of
/// `2^32 + k` as `k`, in its evaluator and in its parser.
fn bv_wide(out: &mut Vec<(String, Instance)>) {
    let defs = String::new();
    for w in [4294967296u64, 4294967297, 4294967298, 8589934593] {
        let small = |n: u64| format!("(_ bv{} {})", n, w);
        let zext = |b: &str| format!("((_ zero_extend {}) {})", w - 1, b);
        let sext = |b: &str| format!("((_ sign_extend {}) {})", w - 1, b);
        let cat = |b: &str| format!("(concat ((_ zero_extend {}) #b0) {})", w - 2, b);
        let atoms = [
            small(0),
            small(1),
            small(2),
            small(5),
            zext("#b1"),
            zext("#b0"),
            sext("#b0"),
            sext("#b1"),
            cat("#b1"),
            cat("#b0"),
        ];
        let mut bools = Vec::new();
        for (i, a) in atoms.iter().enumerate() {
            for b in atoms.iter().skip(i) {
                for op in ["=", "bvult", "bvule", "bvslt"] {
                    bools.push(format!("({} {} {})", op, a, b));
                }
            }
        }
        for a in &atoms[..4] {
            for b in &atoms[..4] {
                for op in [
                    "bvadd", "bvmul", "bvudiv", "bvurem", "bvsub", "bvor", "bvxor",
                ] {
                    for c in &atoms[..4] {
                        bools.push(format!("(= ({} {} {}) {})", op, a, b, c));
                    }
                }
            }
            bools.push(format!("(= ((_ extract 3 0) {}) #b0101)", a));
            bools.push(format!("(= ((_ extract {} {}) {}) #b0)", w - 1, w - 1, a));
            bools.push(format!("(= (ubv_to_int {}) 5)", a));
            bools.push(format!("(= (bvshl {} {}) {})", a, small(1), small(2)));
            bools.push(format!("(= (bvlshr {} {}) {})", a, small(1), small(0)));
        }
        for e in bools {
            for claimed in ["true", "false"] {
                out.push((
                    "evaluate".into(),
                    inst(
                        defs.clone(),
                        format!("(step t1 (cl (= {} {})) :rule evaluate)", e, claimed),
                    ),
                ));
            }
        }
        for a in [0u64, 1, 5, 7] {
            for b in [0u64, 1, 5, 7] {
                out.push((
                    "refl".into(),
                    inst(
                        defs.clone(),
                        format!("(step t1 (cl (= {} {})) :rule refl)", small(a), small(b)),
                    ),
                ));
            }
        }
    }
}

/// `dt_project`: every selector of a datatype (and an uninterpreted function of a selector's sort)
/// over constructor applications of that datatype and over a free constant, against candidate
/// values of the field sort, in both orientations; valid and invalid alike, for the checker to
/// decide. Then the attacks the checker must refuse: an anchor that rebinds a selector or a
/// constructor name (a complete refutation of a satisfiable problem), and a selector that a
/// `declare-fun` redeclares with the same sort.
fn datatypes(out: &mut Vec<(String, Instance)>) {
    let defs = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))\n\
                (declare-datatype E ((e0) (e1 (f1 Bool)) (e2 (g1 Bool) (g2 E))))\n\
                (declare-datatypes ((Tree 0) (Forest 0)) (((leaf (val Int)) (node (children Forest))) \
                ((fnil) (fcons (head Tree) (tail Forest)))))\n\
                (declare-fun h (P) Int)\n(declare-fun k (E) Bool)\n\
                (declare-const a Int)\n(declare-const b Int)\n(declare-const p Bool)\n\
                (declare-const q Bool)\n(declare-const x P)\n(declare-const y E)\n\
                (declare-const t Tree)\n(declare-const f Forest)\n"
        .to_owned();
    let apps: [(&str, &[&str]); 4] = [
        (
            "P",
            &[
                "(mk a b)",
                "(mk b a)",
                "(mk a a)",
                "(mk 1 2)",
                "(other a)",
                "(other 3)",
                "x",
            ],
        ),
        (
            "E",
            &["(e1 p)", "(e1 q)", "(e2 p e0)", "(e2 q (e1 p))", "e0", "y"],
        ),
        (
            "Tree",
            &["(leaf a)", "(leaf 2)", "(node f)", "(node fnil)", "t"],
        ),
        (
            "Forest",
            &["(fcons t f)", "(fcons (leaf a) fnil)", "fnil", "f"],
        ),
    ];
    let selectors = [
        ("P", "fst", "Int"),
        ("P", "snd", "Int"),
        ("P", "oth", "Int"),
        ("P", "h", "Int"),
        ("E", "f1", "Bool"),
        ("E", "g1", "Bool"),
        ("E", "g2", "E"),
        ("E", "k", "Bool"),
        ("Tree", "val", "Int"),
        ("Tree", "children", "Forest"),
        ("Forest", "head", "Tree"),
        ("Forest", "tail", "Forest"),
    ];
    let values: [(&str, &[&str]); 5] = [
        ("Int", &["a", "b", "1", "2", "3", "(+ a 1)"]),
        ("Bool", &["p", "q", "true", "false", "(not p)"]),
        ("E", &["e0", "(e1 p)", "y", "(e2 p e0)"]),
        ("Tree", &["t", "(leaf a)", "(node f)"]),
        ("Forest", &["f", "fnil", "(fcons t f)"]),
    ];
    for (datatype, selector, field) in selectors {
        let Some((_, terms)) = apps.iter().find(|(d, _)| *d == datatype) else {
            continue;
        };
        let Some((_, candidates)) = values.iter().find(|(s, _)| *s == field) else {
            continue;
        };
        for term in terms.iter() {
            for value in candidates.iter() {
                for lit in [
                    format!("(= ({} {}) {})", selector, term, value),
                    format!("(= {} ({} {}))", value, selector, term),
                ] {
                    out.push((
                        "dt_project".into(),
                        inst(
                            defs.clone(),
                            format!("(step t1 (cl {}) :rule dt_project)", lit),
                        ),
                    ));
                }
            }
        }
    }
    // An anchor that rebinds a selector or constructor name: inside it the name is a variable, so
    // `(snd (mk a b)) = b` does not hold, and the exported quantified statement is false.
    let pair = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))\n\
                (declare-const a Int)\n(declare-const b Int)\n";
    for (name, sort) in [
        ("snd", "(-> P Int)"),
        ("mk", "(-> Int Int P)"),
        ("z", "Int"),
    ] {
        let body = "(= (snd (mk a b)) b)";
        let quantified = format!("(forall (({} {})) {})", name, sort, body);
        out.push((
            "dt_project".into(),
            inst(
                format!("{}(assert (not {}))\n", pair, quantified),
                format!(
                    "(assume a0 (not {q}))\n\
                     (anchor :step t1 :args (({n} {s})))\n\
                     (step t1.t1 (cl {b}) :rule dt_project)\n\
                     (step t1.t2 (cl (= {b} (= b b))) :rule cong :premises (t1.t1))\n\
                     (step t1 (cl (= {q} (forall (({n} {s})) (= b b)))) :rule bind)\n\
                     (step t2 (cl (= (forall (({n} {s})) (= b b)) (= b b))) :rule qnt_rm_unused)\n\
                     (step t3 (cl (= {q} (= b b))) :rule trans :premises (t1 t2))\n\
                     (step t4 (cl (= b b)) :rule eq_reflexive)\n\
                     (step t5 (cl (not (= {q} (= b b))) {q} (not (= b b))) :rule equiv_pos1)\n\
                     (step t6 (cl) :rule resolution :premises (a0 t3 t4 t5))",
                    q = quantified,
                    n = name,
                    s = sort,
                    b = body
                ),
            ),
        ));
    }
    // A selector redeclared as an uninterpreted function of the same sort.
    for redeclaration in [
        "(declare-fun snd (P) Int)",
        "(declare-const snd (-> P Int))",
    ] {
        out.push((
            "dt_project".into(),
            inst(
                format!(
                    "{}{}\n(assert (not (= (snd (mk a b)) b)))\n",
                    pair, redeclaration
                ),
                "(assume a0 (not (= (snd (mk a b)) b)))\n\
                 (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)\n\
                 (step t2 (cl) :rule resolution :premises (a0 t1))"
                    .to_owned(),
            ),
        ));
    }
}

pub fn all(seed: u64) -> Vec<(String, Instance)> {
    let mut rng = Rng::new(seed ^ 0x5eed);
    let mut out = Vec::new();
    bitblast(&mut out, &mut rng);
    bitblast_structural(&mut out);
    evaluate(&mut out, &mut rng);
    arith_simplify(&mut out);
    linear_arithmetic(&mut out, &mut rng);
    aci(&mut out, &mut rng);
    beta(&mut out, &mut rng);
    arrays(&mut out);
    polyeq(&mut out);
    forall_inst(&mut out);
    pbblast(&mut out);
    qnt_cnf(&mut out);
    poly_simp_rel(&mut out);
    bv_offset_equality(&mut out);
    bv_offset_spines_v1(&mut out);
    bv_reconstruct_v1(&mut out);
    binder_scoping(&mut out);
    onepoint_scoping(&mut out);
    strings_scoping(&mut out);
    bv_literals(&mut out);
    binder_cache(&mut out, &mut rng);
    bv_wide(&mut out);
    datatypes(&mut out);
    out
}

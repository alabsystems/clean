// Added in Clean (not part of upstream Carcara): a step that would expand bit-vectors past the
// checker's resource budget is refused before it is expanded, and a step within the budget is
// checked as before. A width that fits a `usize` but is in the billions is well formed, and
// bit-blasting it ran the checker out of memory. See checker/budget.rs and
// third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource budget".

use carcara::{
    ast::{ProofCommand, ProofStep},
    checker::{
        self,
        budget::{MAX_EXPANDED_BITS, MONOMIAL_WORDS, WORDS_PER_EXPANDED_BIT},
        error::CheckerError,
    },
    parser, Error,
};
use std::time::{Duration, Instant};

/// The words a step may be charged: `MAX_EXPANDED_BITS` expanded bits.
const MAX_WORDS: u128 = MAX_EXPANDED_BITS * WORDS_PER_EXPANDED_BIT;

/// Checks `proof` as `tests/rules/mod.rs` does (its `assume`s are the premises and a final `hole`
/// closes it), under Clean's dialect. Returns the checker's verdict; a parse error fails the test.
fn check(definitions: &str, proof: &str) -> Result<bool, Box<Error>> {
    check_until(parser::Config::clean_dialect(), None, definitions, proof)
}

/// [`check`] under `config`, the checker stopping at `deadline`.
fn check_until(
    config: parser::Config,
    deadline: Option<Instant>,
    definitions: &str,
    proof: &str,
) -> Result<bool, Box<Error>> {
    let (mut problem, mut proof, rare_rules, mut pool) =
        parser::parse_instance(definitions, proof, None, config)
            .unwrap_or_else(|e| panic!("parse error: {e}\n{definitions}"));
    problem.premises = proof
        .commands
        .iter()
        .filter_map(|c| match c {
            ProofCommand::Assume { term, .. } => Some(term.clone()),
            _ => None,
        })
        .collect();
    proof.commands.push(ProofCommand::Step(ProofStep {
        id: "end".into(),
        clause: Vec::new(),
        rule: "hole".into(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
    }));
    let config = checker::Config::new().deadline(deadline);
    checker::ProofChecker::new(&mut pool, &rare_rules, config)
        .check(&problem, &proof)
        .map_err(Box::new)
}

/// The expanded bits a refusal says the step would have reached, or `None` for any other verdict.
/// Only the budget's own error is printed: another error's message can render an unbounded term.
fn budget_refusal(verdict: &Result<bool, Box<Error>>) -> Option<u128> {
    let Err(error) = verdict else {
        return None;
    };
    match &**error {
        Error::Checker {
            inner: e @ CheckerError::ResourceBudgetExceeded(refusal),
            ..
        } => {
            assert_eq!(refusal.budget, MAX_EXPANDED_BITS);
            assert!(refusal.needed > MAX_EXPANDED_BITS, "{e}");
            assert!(
                e.to_string().starts_with("resource budget exceeded: "),
                "{e}"
            );
            Some(refusal.needed)
        }
        _ => None,
    }
}

fn declare(names: &[&str], width: u128) -> String {
    names
        .iter()
        .map(|n| format!("(declare-const {n} (_ BitVec {width}))"))
        .collect()
}

/// One step of `rule` concluding `conclusion`.
fn step(conclusion: &str, rule: &str) -> String {
    format!("(step t1 (cl {conclusion}) :rule {rule})")
}

/// `ceil(log2 w)`, the barrel shifter's stages.
fn stages(w: u128) -> u128 {
    if w <= 1 {
        0
    } else {
        128 - u128::from((w - 1).leading_zeros())
    }
}

/// A step's rule, what it costs at width `w` (see checker/budget.rs), and its conclusion over the
/// declarations of `declarations(w)`, with `w` written `{W}`.
type Shape = (&'static str, fn(u128) -> u128, &'static str);

/// The rules that expand bit-vectors. Every conclusion is false at every width except those of
/// `poly_simp` and `aci_simp`, which hold at any width.
fn shapes() -> Vec<Shape> {
    vec![
        // Linear: `w` for each operand split into bits.
        ("bitblast_ult", |w| 2 * w, "(= (bvult x y) false)"),
        ("bitblast_slt", |w| 2 * w, "(= (bvslt x y) false)"),
        ("bitblast_equal", |w| 2 * w, "(= (= x y) false)"),
        ("bitblast_and", |w| 2 * w, "(= (bvand x y) z)"),
        ("bitblast_xnor", |w| 2 * w, "(= (bvxnor x y) z)"),
        ("bitblast_add", |w| 3 * w, "(= (bvadd x y u) z)"),
        ("bitblast_not", |w| w, "(= (bvnot x) z)"),
        ("bitblast_neg", |w| w, "(= (bvneg x) z)"),
        ("bitblast_var", |w| w, "(= x z)"),
        (
            "bitblast_sign_extend",
            |w| w + 8,
            "(= ((_ sign_extend {W}) s) e)",
        ),
        // Quadratic: the multiplier's products and the divider's steps.
        ("bitblast_mult", |w| w * w + 2 * w, "(= (bvmul x y) z)"),
        ("bitblast_udiv", |w| 4 * w * w + 2 * w, "(= (bvudiv x y) z)"),
        ("bitblast_urem", |w| 4 * w * w + 2 * w, "(= (bvurem x y) z)"),
        // The shifter: its stages and final selection, `(bvult y w)`, and both operands' bits.
        ("bitblast_shl", |w| (stages(w) + 5) * w, "(= (bvshl x y) z)"),
        (
            "bitblast_ashr",
            |w| (stages(w) + 5) * w,
            "(= (bvashr x y) z)",
        ),
        // `2^w`, and the words `poly_simp` charges for its walk (36: a visit and an atom's entry
        // per side) or `aci_simp` for its flattening (2), less than a bit.
        ("poly_simp", |w| w + 1, "(= x x)"),
        ("aci_simp", |w| w + 1, "(= (bvand x x) x)"),
    ]
}

/// `x`, `y`, `u` and `z` of `w` bits, and an 8-bit `s` with `e`, of `w + 8` bits.
fn declarations(w: u128) -> String {
    declare(&["x", "y", "u", "z"], w) + &declare(&["s"], 8) + &declare(&["e"], w + 8)
}

/// The widest step of `cost` within the budget.
fn widest(cost: fn(u128) -> u128) -> u128 {
    let (mut fits, mut over) = (1u128, MAX_EXPANDED_BITS + 1);
    assert!(cost(fits) <= MAX_EXPANDED_BITS && cost(over) > MAX_EXPANDED_BITS);
    while over - fits > 1 {
        let mid = fits + (over - fits) / 2;
        if cost(mid) <= MAX_EXPANDED_BITS {
            fits = mid;
        } else {
            over = mid;
        }
    }
    fits
}

/// For each rule that expands bit-vectors, the widest step within the budget is checked by the
/// rule (each conclusion here is false, so the rule refuses it on its own terms, or accepts it for
/// `poly_simp` and `aci_simp`), and a step one bit wider is refused by the budget. The steps run
/// one at a time: the widest within the budget peak at about 600 MB.
#[test]
fn each_rule_is_checked_up_to_the_budget_and_refused_one_bit_past_it() {
    for (rule, cost, conclusion) in shapes() {
        let w = widest(cost);
        for (width, within) in [(w, true), (w + 1, false)] {
            let proof = step(&conclusion.replace("{W}", &width.to_string()), rule);
            let verdict = check(&declarations(width), &proof);
            match (within, budget_refusal(&verdict)) {
                (true, None) | (false, Some(_)) => {}
                (true, Some(needed)) => panic!(
                    "{rule} at width {width} (cost {}) refused by the budget at {needed}",
                    cost(width)
                ),
                (false, None) => panic!(
                    "{rule} at width {width} (cost {}) not refused by the budget (accepted: {})",
                    cost(width),
                    verdict.is_ok()
                ),
            }
            // Accepted at the budget, not only judged: `poly_simp`'s and `aci_simp`'s hold.
            if within && matches!(rule, "poly_simp" | "aci_simp") {
                assert!(matches!(verdict, Ok(true)), "{rule} at width {width}");
            }
        }
    }
}

/// A correct step at the budget is accepted: `bitblast_var` of the widest variable it may split.
#[test]
fn a_correct_step_at_the_budget_is_accepted() {
    let w = MAX_EXPANDED_BITS;
    let bits: String = (0..w).map(|i| format!(" ((_ @bit_of {i}) x)")).collect();
    let definitions = declare(&["x"], w);
    let proof = step(&format!("(= x (@bbterm{bits}))"), "bitblast_var");
    assert!(matches!(check(&definitions, &proof), Ok(true)));
    // With its top bit wrong, it is refused by the rule, not by the budget.
    let wrong = format!("{} false", &bits[..bits.rfind(" ((_").unwrap()]);
    let proof = step(&format!("(= x (@bbterm{wrong}))"), "bitblast_var");
    let verdict = check(&definitions, &proof);
    assert!(verdict.is_err() && budget_refusal(&verdict).is_none());
}

/// The reported case, two `((_ zero_extend 4294967295) #b0)` operands of `bitblast_ult`, and a
/// step of each kind at a width in the billions, are refused before anything is built.
#[test]
fn billion_bit_steps_are_refused_before_anything_is_built() {
    let w32 = u128::from(u32::MAX);
    let cases = [
        (
            "(declare-const a Bool)".to_owned(),
            format!("(= (bvult ((_ zero_extend {w32}) #b0) ((_ zero_extend {w32}) #b1)) false)"),
            "bitblast_ult",
            w32 + 1,
        ),
        (
            declare(&["y", "z"], w32 + 1),
            format!("(= (bvudiv ((_ zero_extend {w32}) #b1) y) z)"),
            "bitblast_udiv",
            w32 + 1,
        ),
        (
            declare(&["x", "z"], 1 << 32),
            "(= x z)".into(),
            "bitblast_var",
            1 << 32,
        ),
        (
            declare(&["x", "y", "z"], 1 << 20),
            "(= (bvmul x y) z)".into(),
            "bitblast_mult",
            1 << 40,
        ),
        (
            declare(&["x", "y", "z"], 1 << 32),
            "(= (bvshl x y) z)".into(),
            "bitblast_shl",
            33 << 32,
        ),
        (
            declare(&["x"], 8) + &declare(&["z"], (1 << 62) + 8),
            format!("(= ((_ sign_extend {}) x) z)", 1u128 << 62),
            "bitblast_sign_extend",
            1 << 62,
        ),
        (
            declare(&["x"], u128::from(u64::MAX)),
            "(= x x)".into(),
            "poly_simp",
            u128::from(u64::MAX),
        ),
        (
            declare(&["x"], u128::from(u64::MAX)),
            "(= (bvand x x) x)".into(),
            "aci_simp",
            u128::from(u64::MAX),
        ),
    ];
    for (definitions, conclusion, rule, needed) in cases {
        let verdict = check(&definitions, &step(&conclusion, rule));
        assert_eq!(
            budget_refusal(&verdict),
            Some(needed),
            "{rule}: {conclusion}"
        );
    }
}

/// `n` Boolean constants `{name}0` to `{name}{n-1}`, and the `@bbterm` that spells them out.
fn spelled_out(name: &str, n: usize) -> (String, String) {
    let declarations = (0..n)
        .map(|i| format!("(declare-const {name}{i} Bool)"))
        .collect();
    let bits: String = (0..n).map(|i| format!(" {name}{i}")).collect();
    (declarations, format!("(@bbterm{bits})"))
}

/// Asserts that `rule` judges a step concluding `conclusion` on its own terms when `within`, and
/// that the budget refuses it otherwise.
fn assert_judged(rule: &str, definitions: &str, conclusion: &str, within: bool, what: &str) {
    let verdict = check(definitions, &step(conclusion, rule));
    match (within, budget_refusal(&verdict)) {
        (true, None) | (false, Some(_)) => {}
        (true, Some(needed)) => panic!("{rule} {what}: refused by the budget at {needed}"),
        (false, None) => panic!(
            "{rule} {what}: not refused by the budget (accepted: {})",
            verdict.is_ok()
        ),
    }
}

/// Asserts that a `proof` is judged on the rule's own terms when `within`, and that the budget
/// refuses it otherwise.
fn assert_judged_proof(definitions: &str, proof: &str, within: bool, what: &str) {
    let verdict = check(definitions, proof);
    match (within, budget_refusal(&verdict)) {
        (true, None) | (false, Some(_)) => {}
        (true, Some(needed)) => panic!("{what}: refused by the budget at {needed}"),
        (false, None) => panic!(
            "{what}: not refused by the budget (accepted: {})",
            verdict.is_ok()
        ),
    }
}

/// Bits a proof spells out as a `@bbterm` are charged as split ones are: each rule builds terms
/// over every bit it reads. An n-ary step that reads one shared (`:named`) `@bbterm` n times is
/// judged up to the budget and refused past it; charged nothing, a step of this shape of 285 KB
/// grew past 8 GB. So is a comparison of two spelled-out operands, which used to cost nothing at
/// any width.
#[test]
fn spelled_out_bits_are_charged_as_split_ones() {
    let w = 1024;
    let (bools, bbterm) = spelled_out("b", w);
    let definitions = bools + &declare(&["z"], w as u128);
    // `bvand`, `bvor` and `bvxor` read both operands of each of their `n - 1` rounds, the first
    // being the previous round's `@bbterm`; `bvadd` reads each operand once.
    let shapes: [(&str, &str, fn(u128) -> u128); 4] = [
        ("bitblast_and", "bvand", |n| (n - 1) * 2 * 1024),
        ("bitblast_or", "bvor", |n| (n - 1) * 2 * 1024),
        ("bitblast_xor", "bvxor", |n| (n - 1) * 2 * 1024),
        ("bitblast_add", "bvadd", |n| n * 1024),
    ];
    for (rule, op, cost) in shapes {
        let n = widest(cost);
        for (n, within) in [(n, true), (n + 1, false)] {
            let copies = " B".repeat(n as usize - 1);
            let conclusion = format!("(= ({op} (! {bbterm} :named B){copies}) z)");
            let what = format!("over {n} copies of a {w}-bit @bbterm (cost {})", cost(n));
            assert_judged(rule, &definitions, &conclusion, within, &what);
        }
    }

    // Two spelled-out operands of a comparison, each of `w` copies of one constant.
    let w = widest(|w| 2 * w);
    let definitions = "(declare-const p Bool)(declare-const q Bool)";
    for (w, within) in [(w, true), (w + 1, false)] {
        let (p, q) = (" p".repeat(w as usize), " q".repeat(w as usize));
        let conclusion = format!("(= (bvult (@bbterm{p}) (@bbterm{q})) false)");
        let what = format!("of two {w}-bit spelled-out operands");
        assert_judged("bitblast_ult", definitions, &conclusion, within, &what);
    }
}

/// `(! (op (! (op ... x x) :named n1) n1) :named n_depth)`: `depth` nested applications of `op`,
/// each to two copies of the last, so the term is linear in `depth` but has `2^depth` paths.
fn doubling_chain(op: &str, x: &str, depth: usize) -> String {
    let mut term = format!("(! ({op} {x} {x}) :named n1)");
    for i in 2..=depth {
        term = format!("(! ({op} {term} n{}) :named n{i})", i - 1);
    }
    term
}

/// `poly_simp` normalizes without a cache, and a product of `k` sums of two has `2^k` monomials;
/// `aci_simp` keeps every copy of an argument of an operator that is not idempotent. Charged
/// nothing, each of these steps of at most 2 KB grew past 8 GB. They are refused by the budget,
/// while the same shapes a few levels shallower are judged by the rule.
#[test]
fn polynomial_and_flattening_blowups_are_refused() {
    let w8 = declare(&["x", "z"], 8);
    let ints = "(declare-const i Int)(declare-const j Int)";
    let product = |k: usize| {
        let sums: String = (0..k).map(|i| format!(" (bvadd a{i} b{i})")).collect();
        let consts: String = (0..k)
            .map(|i| declare(&[&format!("a{i}"), &format!("b{i}")], 8))
            .collect();
        (consts, format!("(= (bvmul{sums}) #x00)"))
    };
    for (k, within) in [(8, true), (24, false)] {
        let (definitions, conclusion) = product(k);
        let what = format!("of a product of {k} sums");
        assert_judged("poly_simp", &definitions, &conclusion, within, &what);
    }
    let cases = [
        ("poly_simp", &w8, "bvmul", "x", "z"),
        ("poly_simp", &w8, "bvadd", "x", "z"),
        ("poly_simp", &ints.to_owned(), "*", "i", "j"),
        ("aci_simp", &w8, "bvadd", "x", "z"),
        ("aci_simp", &w8, "bvxor", "x", "z"),
        ("aci_simp", &ints.to_owned(), "+", "i", "j"),
    ];
    for (rule, definitions, op, x, z) in cases {
        for (depth, within) in [(8, true), (30, false)] {
            let conclusion = format!("(= {} {z})", doubling_chain(op, x, depth));
            let what = format!("of {depth} nested {op}s over shared copies");
            assert_judged(rule, definitions, &conclusion, within, &what);
        }
    }
}

/// `evaluate` charges what it reads and computes, and a sum, difference, product or quotient before
/// computing it. `(* d d)` squares `d`, so `n` nested products of two copies of the last, over 3,
/// reach `3^(2^n)`, about `1.58 * 2^n` bits, from a term linear in `n`: uncharged, 30 deep peaked
/// at 2.1 GB and 32 deep grew past 3 GB, and past about 2^37 bits GMP aborts. `x + 1 / x` over the
/// rationals doubles the bits of a numerator and of a denominator alike. Each conclusion is false,
/// so the rule refuses it on its own terms when the budget does not; a true one is accepted.
#[test]
fn evaluated_numbers_are_charged_before_they_are_computed() {
    for (depth, within) in [(24, true), (28, false), (64, false)] {
        let conclusion = format!("(= {} 0)", doubling_chain("*", "3", depth));
        let what = format!("of {depth} nested products of two copies");
        assert_judged("evaluate", "", &conclusion, within, &what);
    }
    let reciprocal_sums = |depth: usize| {
        let mut term = "(! (+ 2.0 (/ 1.0 2.0)) :named r1)".to_owned();
        for i in 2..=depth {
            term = format!("(! (+ {term} (/ 1.0 r{})) :named r{i})", i - 1);
        }
        format!("(= {term} 0.0)")
    };
    for (depth, within) in [(16, true), (64, false)] {
        let what = format!("of {depth} nested sums of a rational and its reciprocal");
        assert_judged("evaluate", "", &reciprocal_sums(depth), within, &what);
    }
    let verdict = check("", &step("(= (* 3 (+ 1 2) (- 5 2)) 27)", "evaluate"));
    assert!(matches!(verdict, Ok(true)), "{verdict:?}");
}

/// `la_generic` (and every rule that reads a linear combination) visits a shared subterm once per
/// path to it, and is charged a word a visit, as `poly_simp` is: `n` nested sums of two copies of
/// the last are judged a few levels deep and refused past the budget, where uncharged, 26 deep (1
/// KB) took 4.7 s and 40 deep about 21 hours. Each conclusion is not a contradiction, so the rule
/// refuses it on its own terms when the budget does not.
#[test]
fn linear_combinations_are_charged_per_visit() {
    let definitions = "(declare-const x Int)";
    for (depth, within) in [(16, true), (24, false), (40, false)] {
        let conclusion = format!("(<= {} 0) (> x 0)", doubling_chain("+", "x", depth));
        let what = format!("over {depth} nested sums of two copies");
        assert_judged(
            "la_generic :args (1 1)",
            definitions,
            &conclusion,
            within,
            &what,
        );
    }
}

/// `poly_simp` charges the words of the coefficients it multiplies: a product of a 16,384-bit
/// numeral (256 words) and a sum of `n` terms builds `n` copies of the numeral. The conclusion is
/// false, so the rule refuses it when the budget does not; a numeral of one word is not charged.
#[test]
fn polynomial_coefficients_are_charged_by_their_words() {
    let wide = (rug::Integer::from(1) << 16383u32).to_string();
    let product = |c: &str, n: usize| {
        let names: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
        let definitions: String = names
            .iter()
            .map(|v| format!("(declare-const {v} Int)"))
            .chain(["(declare-const x Int)".to_owned()])
            .collect();
        let sum: String = names.iter().map(|v| format!(" {v}")).collect();
        (definitions, format!("(= (* {c} (+{sum})) x)"))
    };
    // Charged, in words, for a numeral of `w` words times a sum of `n`: visiting the product, the
    // numeral and the sum (3 + w); each term's visit and entry (n (2 + MONOMIAL_WORDS)); the
    // product's entries and the copies of the numeral (n (1 + MONOMIAL_WORDS + w)); moving them out
    // of the product (n MONOMIAL_WORDS); and `x`'s visit and entry (2 + MONOMIAL_WORDS).
    let cost = |w: u128, n: u128| 3 + w + n * (3 + 3 * MONOMIAL_WORDS + w) + 2 + MONOMIAL_WORDS;
    let n = (0..)
        .take_while(|&n| cost(256, n) <= MAX_WORDS)
        .last()
        .unwrap();
    for (c, n, within) in [
        (wide.as_str(), n, true),
        (wide.as_str(), n + 1, false),
        ("3", n + 1, true),
    ] {
        let (definitions, conclusion) = product(c, n as usize);
        let what = format!("of a {}-digit numeral times a sum of {n}", c.len());
        assert_judged("poly_simp", &definitions, &conclusion, within, &what);
    }
    // A true identity is accepted while it is affordable.
    let names: String = (0..8)
        .map(|i| format!("(declare-const v{i} Int)"))
        .collect();
    let scaled: String = (0..8).map(|i| format!(" (* {wide} v{i})")).collect();
    let sum: String = (0..8).map(|i| format!(" v{i}")).collect();
    let conclusion = format!("(= (* {wide} (+{sum})) (+{scaled}))");
    assert!(matches!(
        check(&names, &step(&conclusion, "poly_simp")),
        Ok(true)
    ));
}

/// Added in Clean, 2026-10-14: `poly_simp`, `aci_simp` and `qnt_cnf` are charged in words,
/// `WORDS_PER_EXPANDED_BIT` to a bit, and each is held to its edge. Charged a bit per word, steps
/// of a few kilobytes that check in a few megabytes were refused: a monomial of degree 362, and
/// `aci_simp` over a chain of 724 sums.
#[test]
fn word_charged_rules_are_held_to_their_edges() {
    let edge =
        |cost: &dyn Fn(u128) -> u128| (1..).take_while(|&n| cost(n) <= MAX_WORDS).last().unwrap();

    // `(= M M)`, `M` a product of `d` copies of `x`: each side visits the product and its factors,
    // builds an entry per factor and one per partial product, `x^k` times `x` costing an entry
    // and `k + 1` factors, and moves the result out of the product.
    let monomial = |d: u128| {
        let side = 1
            + d * (2 + MONOMIAL_WORDS)
            + (1..d).map(|k| MONOMIAL_WORDS + k + 1).sum::<u128>()
            + MONOMIAL_WORDS;
        2 * side
    };
    let d = edge(&monomial);
    assert!(d > 4000, "{d}");
    for (d, within) in [(362, true), (d, true), (d + 1, false)] {
        let m = format!("(*{})", " x".repeat(d as usize));
        let conclusion = format!("(= {m} {m})");
        let proof = step(&conclusion, "poly_simp");
        let verdict = check("(declare-const x Int)", &proof);
        if within {
            assert!(matches!(verdict, Ok(true)), "a monomial of degree {d}");
        } else {
            assert!(
                budget_refusal(&verdict).is_some(),
                "a monomial of degree {d}"
            );
        }
    }

    // `poly_simp` over `(bvneg (bvadd y_1 ... y_n))` on both sides at `w` bits: each negative
    // coefficient becomes a `w`-bit number modulo `2^w`, `w / 64` words. Before this charge, a
    // step within the budget built gigabytes of them.
    let w = 1u128 << 16;
    let negated = |n: u128| 64 * w + 2 * (2 + n * (2 + MONOMIAL_WORDS)) + 2 * n * (w / 64);
    let n = edge(&negated);
    for (n, within) in [(n, true), (n + 1, false)] {
        let ys: Vec<String> = (0..n).map(|i| format!("y{i}")).collect();
        let definitions = declare(&ys.iter().map(String::as_str).collect::<Vec<_>>(), w);
        let neg = format!("(bvneg (bvadd {}))", ys.join(" "));
        let conclusion = format!("(= {neg} {neg})");
        let what = format!("negating {n} terms of {w} bits");
        assert_judged("poly_simp", &definitions, &conclusion, within, &what);
        if within {
            assert!(matches!(
                check(&definitions, &step(&conclusion, "poly_simp")),
                Ok(true)
            ));
        }
    }

    // `aci_simp` over `(= (bvadd a_0 (bvadd a_1 ... a_(n-1))) (bvadd a_0 ... a_(n-1)))`: the chain's
    // flattenings build `2 + 3 + ... + n` arguments, the flat side `n`.
    let chain = |n: u128| n * (n + 1) / 2 - 1 + n;
    let n = edge(&chain);
    for (n, within) in [(724, true), (n, true), (n + 1, false)] {
        let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let definitions = declare(&names.iter().map(String::as_str).collect::<Vec<_>>(), 8);
        let nested = names[..names.len() - 1]
            .iter()
            .rev()
            .fold(names[names.len() - 1].clone(), |acc, a| {
                format!("(bvadd {a} {acc})")
            });
        let conclusion = format!("(= {nested} (bvadd {}))", names.join(" "));
        let verdict = check(&definitions, &step(&conclusion, "aci_simp"));
        if within {
            assert!(matches!(verdict, Ok(true)), "a chain of {n}");
        } else {
            assert!(budget_refusal(&verdict).is_some(), "a chain of {n}");
        }
    }

    // `qnt_cnf` over `(forall ((x Int)) (or (and a_0 b_0) ... (and a_(n-1) b_(n-1))))`: `2^n`
    // clauses of `n` literals, plus each conjunction's two and each literal's one. A clause is
    // found whether it is the first or the last; one not in the normal form is refused.
    let cnf = |n: u128| (1 << n) * (n + 1) + 8 * n;
    let n = edge(&cnf);
    assert_eq!(n, 19);
    let qnt_cnf = |n: u128, literal: &str| {
        let definitions: String = (0..n)
            .map(|i| format!("(declare-const a{i} Bool)(declare-const b{i} Bool)"))
            .collect();
        let phi: String = (0..n).map(|i| format!(" (and a{i} b{i})")).collect();
        let clause: String = (0..n).map(|i| format!(" {literal}{i}")).collect();
        let conclusion =
            format!("(or (not (forall ((x Int)) (or{phi}))) (forall ((x Int)) (or{clause})))");
        (definitions, step(&conclusion, "qnt_cnf"))
    };
    for literal in ["a", "b"] {
        let (definitions, proof) = qnt_cnf(n, literal);
        assert!(matches!(check(&definitions, &proof), Ok(true)), "{literal}");
    }
    let (definitions, proof) = qnt_cnf(n, "a");
    let wrong = check(
        &definitions,
        &proof.replace(&format!(" a{}))", n - 1), "))"),
    );
    assert!(wrong.is_err() && budget_refusal(&wrong).is_none());
    let (definitions, proof) = qnt_cnf(n + 1, "a");
    let needed = budget_refusal(&check(&definitions, &proof));
    assert_eq!(needed, Some(cnf(n + 1).div_ceil(WORDS_PER_EXPANDED_BIT)));
    let (definitions, proof) = qnt_cnf(26, "a");
    assert!(budget_refusal(&check(&definitions, &proof)).is_some());

    // The prenexing walks copy a quantifier's variables once per path to it: a quantifier over
    // 2,000 variables under a conjunction doubled `n` times costs `2^n (2 + 8 * 2,000)` words for
    // the copies and the literals, and `n 2^(n+1)` for the conjunctions' clauses.
    let bound = |n: u128| (1 << n) * (2 + 8 * 2000) + n * (2 << n);
    let n = edge(&bound);
    assert_eq!(n, 10);
    let doubled = |n: u128| {
        let bindings: String = (0..2000).map(|i| format!("(x{i} Int)")).collect();
        let mut phi = format!("(! (and (! (forall ({bindings}) p) :named f) f) :named d1)");
        for i in 2..=n {
            phi = format!("(! (and {phi} d{}) :named d{i})", i - 1);
        }
        let conclusion = format!("(or (not (forall ((y Int)) {phi})) (forall ((y Int)) p))");
        step(&conclusion, "qnt_cnf")
    };
    let p = "(declare-const p Bool)";
    assert!(matches!(check(p, &doubled(n)), Ok(true)));
    let needed = budget_refusal(&check(p, &doubled(n + 1)));
    assert_eq!(needed, Some(bound(n + 1).div_ceil(WORDS_PER_EXPANDED_BIT)));
}

/// Added in Clean: `nary_elim` expands an n-ary term with a fold, so a long argument list is judged
/// within a 1 MiB stack (upstream recursed once per argument: 7,000,000 arguments took 1.2 GiB of
/// stack); a list longer than the deepest term the parser reads is refused before it is expanded.
#[test]
fn nary_elim_expands_without_recursion_and_refuses_what_no_conclusion_can_be() {
    let verdict = |n: usize| {
        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || {
                let proof = format!(
                    "(step t1 (cl (= (=>{} p) p)) :rule nary_elim)",
                    " p".repeat(n)
                );
                match check("(declare-const p Bool)", &proof) {
                    Ok(holey) => Ok(holey),
                    Err(e) => Err(match *e {
                        Error::Checker { inner, .. } => inner.to_string(),
                        _ => "another error".to_owned(),
                    }),
                }
            })
            .unwrap()
            .join()
            .unwrap()
    };
    // Judged: the expansion is built and is not `p`.
    let judged = verdict(200_000).unwrap_err();
    assert!(judged.starts_with("expected term"), "{judged}");
    let refused = verdict(parser::MAX_TERM_DEPTH).unwrap_err();
    assert!(refused.contains("expands deeper than"), "{refused}");
}

/// `2^k`, saturating.
fn two_to_the(k: u128) -> u128 {
    u32::try_from(k)
        .ok()
        .and_then(|k| 1u128.checked_shl(k))
        .unwrap_or(u128::MAX)
}

/// `(assume h1 premise)` and a `bfun_elim` step from it concluding `conclusion`.
fn bfun_elim(premise: &str, conclusion: &str) -> String {
    format!("(assume h1 {premise})(step t1 (cl {conclusion}) :rule bfun_elim :premises (h1))")
}

/// `bfun_elim` turns a quantifier over `k` Boolean variables into `2^k` instances of its body, and
/// an application to `m` Boolean arguments that are not constants into `2^m` copies of it. Each is
/// charged before it expands (in words, for each subterm of the body that mentions a variable,
/// `2^j` times an expanded bit plus its argument list, `j` being the variables it mentions, and an
/// expanded bit for each instance; `2^m` times the application's arguments plus one), judged up to
/// the budget and refused one unit past it. Upstream reserved `2^n` slots for a quantifier over
/// `n` variables before expanding it: about 45 aborted the process in the allocator, and 64
/// overflowed `2usize.pow` (a panic, and so an abort, under Clean's release profile).
#[test]
fn boolean_function_elimination_is_charged_before_it_expands() {
    // A quantifier over `x0 .. x{k-1}` whose body is `(or x0 .. x{k-1} (and x0 q0) .. (and x0
    // q{p-1}))`. It is charged `2^k` bits for its instances, `2^k` times a bit and `k + p` words
    // for the `or`, two bits for each variable, and two bits and two words for each `and`, which
    // mentions only `x0`.
    let constants: String = (0..128)
        .map(|i| format!("(declare-const q{i} Bool)"))
        .collect();
    let quantifier = |k: usize, p: usize| {
        let bindings: String = (0..k).map(|i| format!("(x{i} Bool)")).collect();
        let vars: String = (0..k).map(|i| format!(" x{i}")).collect();
        let qs: String = (0..p).map(|i| format!(" (and x0 q{i})")).collect();
        format!("(forall ({bindings}) (or{vars}{qs}))")
    };
    let bit = WORDS_PER_EXPANDED_BIT;
    let words = |k: u128, p: u128| {
        let instances = two_to_the(k).saturating_mul(2 * bit + k + p);
        instances.saturating_add(k * 2 * bit + p * 2 * (bit + 2))
    };
    let k = widest(|k| {
        let bit = WORDS_PER_EXPANDED_BIT;
        let instances = two_to_the(k).saturating_mul(2 * bit + k);
        instances.saturating_add(k * 2 * bit).div_ceil(bit)
    });
    let edge = (0..)
        .take_while(|&p| words(k, p) <= MAX_WORDS)
        .last()
        .unwrap();
    for (k, p, within) in [(k, edge, true), (k, edge + 1, false), (k + 1, 0, false)] {
        let what = format!("over {k} Booleans, its body {} terms over them", 1 + k + p);
        let verdict = check(
            &constants,
            &bfun_elim(&quantifier(k as usize, p as usize), "false"),
        );
        match (within, budget_refusal(&verdict)) {
            (true, None) => assert!(verdict.is_err(), "{what}: the conclusion is false"),
            (false, Some(_)) => {}
            (_, needed) => panic!("{what}: {needed:?}"),
        }
    }

    // `(g b0 .. b{m-1} true ..)`: `m` Boolean arguments that are not constants, `n` in all.
    let declarations = |n: usize| {
        let sorts = " Bool".repeat(n);
        let bs: String = (0..n)
            .map(|i| format!("(declare-const b{i} Bool)"))
            .collect();
        format!("{bs}(declare-fun g ({sorts}) Bool)")
    };
    let application = |m: usize, n: usize| {
        let args: String = (0..n)
            .map(|i| {
                if i < m {
                    format!(" b{i}")
                } else {
                    " true".to_owned()
                }
            })
            .collect();
        format!("(g{args})")
    };
    let m = widest(|m| two_to_the(m).saturating_mul(m + 1)) as usize;
    let n = (MAX_EXPANDED_BITS >> m) as usize - 1;
    for (m, n, within) in [(m, n, true), (m, n + 1, false), (m + 1, n, false)] {
        let what = format!("of an application to {m} Booleans of {n} arguments");
        let proof = bfun_elim(&application(m, n), "false");
        assert_judged_proof(&declarations(n), &proof, within, &what);
    }

    // A correct step is accepted.
    let proof = bfun_elim(
        "(forall ((x Bool) (i Int) (y Bool)) (g x y))",
        "(forall ((i Int)) (and (g false false) (g true false) (g false true) (g true true)))",
    );
    assert!(matches!(check(&declarations(2), &proof), Ok(true)));

    // Quantifiers of 45, 64 and 200 Booleans, and an application to 64, are refused before
    // anything is reserved or built.
    for k in [45, 64, 200] {
        let verdict = check(&constants, &bfun_elim(&quantifier(k, 1), "false"));
        assert!(budget_refusal(&verdict).is_some(), "over {k} Booleans");
    }
    let verdict = check(&declarations(64), &bfun_elim(&application(64, 64), "false"));
    assert!(budget_refusal(&verdict).is_some());
}

/// The checker stops at the deadline its caller sets. `refl` over two chains of conjunctions of
/// two quantifiers over the level below, named apart, where level `i`'s two quantifiers bind
/// `x(i-1)` at different indices (the second binds another variable first) and the leaves read
/// every `xi`, is alpha-equivalence over every path with the bindings of that path: `2^40`
/// comparisons, which no step budget bounds and no cached answer can share (an answer is reused
/// only where the names it read are bound as they were). With a deadline a fifth of a second away
/// the comparison stops when it passes, and the step is refused for it, though `refl` holds: no
/// answer given past the deadline is used. A deadline already passed refuses the first command; a
/// distant one changes nothing.
#[test]
fn the_checker_stops_at_its_deadline() {
    // The levels are defined in the proof, where a definition's names may be captured by the
    // binders it is used under (in the problem that is refused: `ParserError::MacroCapture`).
    let declarations: String = (0..=40)
        .map(|i| format!("(declare-const x{i} Int)"))
        .collect();
    let leaves: String = (0..=40).map(|i| format!(" (= x{i} 0)")).collect();
    let mut chain = format!("(define-fun a0 () Bool (and{leaves}))");
    chain += &format!("(define-fun b0 () Bool (and{leaves}))");
    for i in 1..=40 {
        let j = i - 1;
        chain += &format!(
            "(define-fun a{i} () Bool \
               (and (forall ((x{j} Int)) a{j}) (forall ((y Int) (x{j} Int)) a{j})))\
             (define-fun b{i} () Bool \
               (and (forall ((x{j} Int)) b{j}) (forall ((w Int) (x{j} Int)) b{j})))"
        );
    }
    let refl = |n: usize| {
        let conclusion = format!("(= (forall ((x{n} Int)) a{n}) (forall ((x{n} Int)) b{n}))");
        chain.clone() + &step(&conclusion, "refl")
    };
    let config = parser::Config::clean_dialect;
    let deadline_refusal = |verdict: Result<bool, Box<Error>>| match verdict {
        Err(error) => match *error {
            Error::Checker {
                inner: CheckerError::DeadlineExceeded,
                step,
                ..
            } => step,
            other => panic!("refused, not at the deadline: {other}"),
        },
        Ok(_) => panic!("accepted"),
    };
    let soon = Instant::now() + Duration::from_millis(200);
    let refused = deadline_refusal(check_until(config(), Some(soon), &declarations, &refl(40)));
    assert_eq!(&*refused, "t1");
    assert!(Instant::now() < soon + Duration::from_secs(60));

    let passed = Some(Instant::now());
    let refused = deadline_refusal(check_until(config(), passed, &declarations, &refl(4)));
    assert_eq!(&*refused, "t1");
    let distant = Some(Instant::now() + Duration::from_secs(3600));
    assert!(matches!(
        check_until(config(), distant, &declarations, &refl(4)),
        Ok(true)
    ));
}

/// A quantifier over 100,000 variables, one of them Boolean, is checked within a 1 MiB stack.
/// Upstream skipped each variable that is not Boolean by a recursive call: this step took 60 MB of
/// stack in a release build, past the 8 MB of a process's main thread.
#[test]
fn bfun_elim_does_not_recurse_per_binding() {
    let verdict = std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| {
            let bindings: String = (0..100_000).map(|i| format!(" (i{i} Int)")).collect();
            let premise = format!("(forall ((b Bool){bindings}) (or b (= i0 i1)))");
            let conclusion = format!(
                "(forall ({}) (and (or false (= i0 i1)) (or true (= i0 i1))))",
                &bindings[1..]
            );
            let verdict = check("", &bfun_elim(&premise, &conclusion));
            matches!(verdict, Ok(true))
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(verdict);
}

/// `(! (str.++ (! ... :named {name}1) ...) :named {name}{depth})`: `depth` nested `str.++`
/// applications, each of two copies of the last, over `leaf`. It flattens to `2^depth` copies of
/// `leaf`, and a walk visits its `2^(depth + 1) - 1` paths.
fn string_chain(name: &str, leaf: &str, depth: usize) -> String {
    let mut term = format!("(! (str.++ {leaf} {leaf}) :named {name}1)");
    for i in 2..=depth {
        term = format!("(! (str.++ {term} {name}{}) :named {name}{i})", i - 1);
    }
    term
}

/// What flattening a chain `d` deep over a variable visits: its `2^(d + 1) - 1` paths.
fn string_chain_cost(d: u32) -> u128 {
    (1 << (d + 1)) - 1
}

/// Added in Clean: the string rules flatten `str.++` applications per path to a shared subterm.
/// Charged nothing, `concat_eq` over `(= n24 n24)` (1 KB) peaked at 776 MB, doubling with each
/// level. A flattening is charged a word for each term it visits and each character it splits
/// out, before it is built; the step is refused past the budget and judged by its rule within it.
#[test]
fn string_flattenings_are_charged_before_they_are_built() {
    let defs = "(declare-const x String)";
    let judge = |proof: &str| check(defs, proof);

    // `concat_eq` over `(= n_d n_d)` flattens both sides; the conclusion `(= "" "")` costs one more.
    for (d, within) in [(22, true), (23, false)] {
        let cost = 2 * string_chain_cost(d) + 1;
        assert_eq!(cost <= MAX_WORDS, within, "depth {d}");
        let chain = string_chain("n", "x", d as usize);
        let proof = format!(
            "(assume h1 (= {chain} n{d}))\
             (step t1 (cl (= \"\" \"\")) :rule concat_eq :premises (h1) :args (false))"
        );
        let verdict = judge(&proof);
        if within {
            assert!(matches!(verdict, Ok(true)), "depth {d}: {verdict:?}");
        } else {
            let second = 2 * string_chain_cost(d);
            assert_eq!(
                budget_refusal(&verdict),
                Some(second.div_ceil(WORDS_PER_EXPANDED_BIT))
            );
        }
    }

    // The exact edge: `concat_conflict` over `(= (str.++ "a" c22 ... c1 x ... x) "b")`, chains of
    // depths 22 down to 1 and `k` more copies of `x`, is charged the left side's `str.++`, its
    // `"a"`, the chains and the `x`s, and the right side's `"b"`.
    let chains: String = (1..=22)
        .rev()
        .map(|d| string_chain(&format!("c{d}_"), "x", d))
        .collect();
    let fixed = 3 + (1..=22).map(string_chain_cost).sum::<u128>();
    let k = MAX_WORDS - fixed;
    assert_eq!(k, 23);
    for (k, within) in [(k, true), (k + 1, false)] {
        let xs = " x".repeat(k as usize);
        let proof = format!(
            "(assume h1 (= (str.++ \"a\" {chains}{xs}) \"b\"))\
             (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"
        );
        let verdict = judge(&proof);
        if within {
            assert!(matches!(verdict, Ok(true)), "{k} copies of x: {verdict:?}");
        } else {
            assert_eq!(
                budget_refusal(&verdict),
                Some((fixed + k).div_ceil(WORDS_PER_EXPANDED_BIT))
            );
        }
    }

    // A chain of `(str.++ "" "")` flattens to nothing and has `2^(d + 1) - 1` paths: its walk is
    // charged, and `(= e60 e60)` is refused at once (upstream walked every path: 20 s at 30 deep).
    let chain = string_chain("e", "\"\"", 60);
    let proof = format!(
        "(assume h1 (= {chain} e60))\
         (step t1 (cl (= \"\" \"\")) :rule concat_eq :premises (h1) :args (false))"
    );
    assert_eq!(
        budget_refusal(&judge(&proof)),
        Some(string_chain_cost(60).div_ceil(WORDS_PER_EXPANDED_BIT))
    );

    // `concat_extract` (`re_concat_unfold_pos`) is charged the same way: `(str.to_re n_d)` keeps
    // `2^d` copies of `x`.
    for (d, within) in [(3, true), (23, false)] {
        let chain = string_chain("n", "x", d);
        let r = format!("(re.++ (str.to_re \"a\") (str.to_re {chain}))");
        let xs = " x".repeat(if within { 1 << d } else { 2 });
        let proof = format!(
            "(assume h1 (str.in_re x {r}))\
             (step t1 (cl (= x (str.++ \"a\"{xs}))) :rule re_concat_unfold_pos :premises (h1))"
        );
        let verdict = judge(&proof);
        if within {
            assert!(matches!(verdict, Ok(true)), "depth {d}: {verdict:?}");
        } else {
            assert!(budget_refusal(&verdict).is_some(), "depth {d}");
        }
    }
}

/// Added in Clean: `expand_string_constants` walked a conclusion once per path to a shared subterm
/// even where it has no string to expand: `concat_eq` concluding `(= d30 d30)`, `d_i = (and d_(i-1)
/// d_(i-1))`, ran past 120 s. Each term is expanded once now, so `d60` is judged at once (the rule
/// refuses the conclusion; the budget charges nothing, as nothing is flattened).
#[test]
fn expanding_a_shared_conclusion_visits_each_term_once() {
    let mut chain = "(! (and p p) :named d1)".to_owned();
    for i in 2..=60 {
        chain = format!("(! (and {chain} d{}) :named d{i})", i - 1);
    }
    let proof = format!(
        "(assume h1 (= \"a\" \"a\"))\
         (step t1 (cl (= {chain} d60)) :rule concat_eq :premises (h1) :args (false))"
    );
    let verdict = check("(declare-const p Bool)", &proof);
    assert!(verdict.is_err() && budget_refusal(&verdict).is_none());
}

/// Added in Clean: `re_concat_unfold_pos` recursed once per argument of its `re.++`, adding the
/// rest of the list to the pool at each level: over 20,000 `str.to_re` arguments (a 400 KB proof)
/// it took 1.7 GB, over 50,000 past 8 GB. And it built a Skolem witness for each argument that is
/// not a `str.to_re`, each naming every one before it, before the step was refused: 5,000 such
/// arguments (10 KB) took 2.4 GB in 14 s. It reads the arguments in one pass now and refuses at
/// the first that is not a `str.to_re`, before building anything.
#[test]
fn re_concat_unfold_pos_is_linear_in_its_arguments() {
    let defs = "(declare-const x String)(declare-const R RegLan)";
    let n = 20_000;
    let a = " (str.to_re \"a\")";
    let unfold = |r: &str, word: &str| {
        let proof = format!(
            "(assume h1 (str.in_re x {r}))\
             (step t1 (cl (= x {word})) :rule re_concat_unfold_pos :premises (h1))"
        );
        check(defs, &proof)
    };
    let witness_refused = |verdict: Result<bool, Box<Error>>| match *verdict.unwrap_err() {
        Error::Checker {
            inner: CheckerError::Explanation(e), ..
        } => {
            assert!(
                e.starts_with("re_concat_unfold_pos builds a Skolem witness"),
                "{e}"
            )
        }
        e => panic!("{e}"),
    };
    let word = format!("(str.++{})", " \"a\"".repeat(n));
    let all = format!("(re.++{})", a.repeat(n));
    assert!(matches!(unfold(&all, &word), Ok(true)));
    // One argument that is not a `str.to_re`, last or first: refused by the rule.
    let last = format!("(re.++{} R)", a.repeat(n - 1));
    witness_refused(unfold(&last, &word));
    let first = format!("(re.++ R{})", a.repeat(n - 1));
    witness_refused(unfold(&first, &word));
    // 5,000 of them.
    let many = format!("(re.++{})", " R".repeat(5000));
    witness_refused(unfold(&many, "(str.++ x x)"));
}

/// Added in Clean: `str_fixed_len_re` (`re_unfold_neg_concat_fixed_prefix`, `_suffix`) and
/// `string_decompose`'s check that its split point is non-negative recursed once per path to a
/// shared subterm: a `re.++` of two copies of a `re.++` of two copies ..., or such a sum, 30 deep,
/// took seconds, doubling with each level. Each subterm is visited once now, so 63 levels are judged
/// at once. A length is a `usize`: `2^63` is measured, and `2^64` cannot be evaluated (upstream would
/// have overflowed after `2^64` steps).
#[test]
fn shared_regular_expressions_and_split_points_are_walked_once() {
    let defs = "(declare-const x String)(declare-const y String)";
    let chain = |name: &str, op: &str, leaf: &str, depth: usize| {
        let mut term = format!("(! ({op} {leaf} {leaf}) :named {name}1)");
        for i in 2..=depth {
            term = format!("(! ({op} {term} {name}{}) :named {name}{i})", i - 1);
        }
        term
    };
    for (d, within) in [(63, true), (64, false)] {
        let r = format!(
            "(re.++ {} (str.to_re \"b\"))",
            chain("r", "re.++", "(str.to_re \"a\")", d)
        );
        let n = 1u128 << d;
        let proof = format!(
            "(assume h1 (not (str.in_re x {r})))\
             (step t1 (cl (or (not (str.in_re (str.substr x 0 {n}) r{d})) \
             (not (str.in_re (str.substr x {n} (- (str.len x) {n})) (str.to_re \"b\"))))) \
             :rule re_unfold_neg_concat_fixed_prefix :premises (h1))"
        );
        let verdict = check(defs, &proof);
        if within {
            assert!(matches!(verdict, Ok(true)), "depth {d}: {verdict:?}");
        } else {
            match verdict.map_err(|e| *e) {
                Err(Error::Checker {
                    inner: CheckerError::LengthCannotBeEvaluated(_),
                    ..
                }) => {}
                v => panic!("depth {d}: {v:?}"),
            }
        }
    }

    // `string_decompose` at a split point `m60`, a sum of two copies of a sum ... of `(str.len y)`:
    // judged at once; with a negative leaf anywhere in it, refused.
    for (leaf, within) in [("(str.len y)", true), ("(- 1)", false)] {
        let m = chain("m", "+", &format!("(+ (str.len y) {leaf})"), 60);
        let proof = format!(
            "(assume h1 (>= (str.len x) {m}))\
             (step t1 (cl (and (= x (str.++ (str.substr x 0 m60) (str.substr x m60 (- (str.len x) m60)))) \
             (= (str.len (str.substr x 0 m60)) m60))) :rule string_decompose :premises (h1) :args (false))"
        );
        let verdict = check(defs, &proof);
        assert_eq!(matches!(verdict, Ok(true)), within, "{leaf}: {verdict:?}");
        assert!(budget_refusal(&verdict).is_none());
    }
}

/// Added in Clean: `bfun_elim` charges what its instances build. A subterm of the body that
/// mentions none of the quantifier's variables is its own term in every instance and costs nothing:
/// `(forall ((x Bool) (y Bool)) (or x y (= (+ i0 .. i69999) 0)))`, which `b09c2715c`'s charge (four
/// times the body's 70,006 distinct subterms) refused, is accepted. A subterm that mentions some is
/// built once for each assignment of those its context has not rebound, and each copy of it holds
/// its argument list, closed arguments too: `(or x0 .. x13 q0 .. q15999)` over 14 variables, charged
/// one unit for the `or` and one for each variable in each instance, was admitted at the budget and
/// took 2,065 MB; it is refused, and the edge moves to 881 constants. A subterm that mentions one
/// variable is built twice however many instances share it: over 16 variables, `(or x0 q0 ..
/// q19999)` took 19 s to build the same two terms 65,536 times, and one reached under eight binders
/// that rebind only other variables was charged eight times over; both are judged at once. And a
/// subterm reached under binders that rebind the variables it mentions is charged for each set of
/// them it is instantiated over: over 12 variables, `L_i = (and (forall ((x_i Bool)) L_(i-1))
/// L_(i-1))` was admitted and built 1,254 MB before a nested charge refused it; it is refused before
/// anything is built. With `(let ((x_i true)) ..)` in place of the binders (accepted at 1,702 MB),
/// upstream's substitution renames each `let`'s variable, which is refused.
#[test]
fn bfun_elim_charges_the_terms_its_instances_build() {
    let n = 70_000;
    let declarations: String = (0..n)
        .map(|i| format!("(declare-const i{i} Int)"))
        .collect();
    let sum: String = (0..n).map(|i| format!(" i{i}")).collect();
    let premise = format!("(forall ((x Bool) (y Bool)) (or x y (! (= (+{sum}) 0) :named big)))");
    let conclusion = "(and (or false false big) (or true false big) (or false true big) \
                      (or true true big))";
    let verdict = check(&declarations, &bfun_elim(&premise, conclusion));
    assert!(matches!(verdict, Ok(true)), "{verdict:?}");

    // Over 14 variables, `(or x0 .. x13 q0 .. q{m-1})`: `2^14` bits for the instances and as many
    // for the `or`, which copies `14 + m` words into each, and two bits for each variable.
    let constants: String = (0..20_000)
        .map(|i| format!("(declare-const q{i} Bool)"))
        .collect();
    let wide = |k: usize, mentioned: usize, m: usize| {
        let bindings: String = (0..k).map(|i| format!("(x{i} Bool)")).collect();
        let vars: String = (0..mentioned).map(|i| format!(" x{i}")).collect();
        let qs: String = (0..m).map(|i| format!(" q{i}")).collect();
        format!("(forall ({bindings}) (or{vars}{qs}))")
    };
    let bit = WORDS_PER_EXPANDED_BIT;
    let words = |m: u128| two_to_the(14) * (2 * bit + 14 + m) + 14 * 2 * bit;
    let edge = (0..).take_while(|&m| words(m) <= MAX_WORDS).last().unwrap();
    assert_eq!(edge, 881);
    for (m, within) in [(edge, true), (edge + 1, false), (16_000, false)] {
        let verdict = check(&constants, &bfun_elim(&wide(14, 14, m as usize), "false"));
        match (within, budget_refusal(&verdict)) {
            (true, None) => assert!(verdict.is_err(), "{m}: the conclusion is false"),
            (false, Some(_)) => {}
            (_, needed) => panic!("{m} constants: {needed:?}"),
        }
    }

    // A subterm that mentions one variable is built twice: over 16 variables, `(or x0 q0 ..
    // q19999)`; and `(or x1 q0 .. q3999)` under eight binders rebinding `x2` .. `x9` over
    // `x1` .. `x9`, which, charged once a binder, needed `9 * 2^9` copies of it.
    assert_judged_proof(
        &constants,
        &bfun_elim(&wide(16, 1, 20_000), "false"),
        true,
        "16 Booleans, one of them mentioned",
    );
    let t = format!(
        "(or x1{})",
        (0..4000).map(|i| format!(" q{i}")).collect::<String>()
    );
    let rebinding: String = (2..=9)
        .map(|i| format!(" (forall ((x{i} Bool)) {t})"))
        .collect();
    let bindings: String = (1..=9).map(|i| format!("(x{i} Bool)")).collect();
    let premise = format!("(forall ({bindings}) (and {t}{rebinding}))");
    assert_judged_proof(
        &constants,
        &bfun_elim(&premise, "false"),
        true,
        "a subterm under binders that rebind other variables",
    );

    // Rebinding binders, and rebinding `let`s, over 12 variables.
    let chain = |rebind: &dyn Fn(usize, &str) -> String| {
        let mut t = format!(
            "(or{})",
            (1..=12).map(|i| format!(" x{i}")).collect::<String>()
        );
        for i in 1..=12 {
            t = format!("(and {} {t})", rebind(i, &t));
        }
        let bindings: String = (1..=12).map(|i| format!("(x{i} Bool)")).collect();
        format!("(forall ({bindings}) {t})")
    };
    let binders = chain(&|i, t| format!("(forall ((x{i} Bool)) {t})"));
    assert_judged_proof(
        "",
        &bfun_elim(&binders, "false"),
        false,
        "rebinding binders",
    );
    let lets = chain(&|i, t| format!("(let ((x{i} true)) {t})"));
    match *check("", &bfun_elim(&lets, "false")).unwrap_err() {
        Error::Checker {
            inner: CheckerError::Explanation(e), ..
        } => {
            assert!(e.starts_with("bfun_elim: a `let` or `match`"), "{e}")
        }
        e => panic!("{e}"),
    }
}

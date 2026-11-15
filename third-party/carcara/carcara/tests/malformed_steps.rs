// Added in Clean (not part of upstream Carcara): a malformed step is refused with an error, never a
// panic. A panic fails closed, but it is a crash of the trusted checker on input the certificate's
// author controls, and Clean's release profile has `panic = "abort"`, so it ends the whole
// `clean cert verify-external` process. See third-party/carcara/DOWNSTREAM.md, "Malformed steps are
// refused, not a panic".

use carcara::{
    ast::{ProofCommand, ProofStep},
    checker, parser,
};
use std::panic::{self, AssertUnwindSafe};

/// Every rule name `get_rule` dispatches on, read from its source, plus `sat_refutation` (handled
/// before it). A rule added there is swept here with no list to keep in step.
fn rule_names() -> Vec<String> {
    let source = include_str!("../src/checker/shared.rs");
    let start = source
        .find("pub fn get_rule(")
        .expect("get_rule is in shared.rs");
    let end = start
        + source[start..]
            .find("_ => return None")
            .expect("get_rule ends");
    let mut names = vec!["sat_refutation".to_owned()];
    for line in source[start..end].lines().map(str::trim) {
        let Some(arm) = line.split("=>").next().filter(|_| line.starts_with('"')) else {
            continue;
        };
        for name in arm.split('"').skip(1).step_by(2) {
            if !names.iter().any(|n| n == name) {
                names.push(name.to_owned());
            }
        }
    }
    names
}

#[derive(Debug)]
enum Verdict {
    ParseError(String),
    Checked(Result<bool, String>),
    Panicked(String),
}

/// Checks `proof` as `tests/rules/mod.rs` does: its `assume`s are the premises and a final `hole`
/// closes it. A panic is caught and reported with its message.
fn check(definitions: &str, proof: &str) -> Verdict {
    check_in(
        parser::Config::new().apply_function_defs(true),
        definitions,
        proof,
    )
}

/// `check` under the parser configuration `config`.
fn check_in(config: parser::Config, definitions: &str, proof: &str) -> Verdict {
    let run = || {
        let (mut problem, mut proof, rare_rules, mut pool) =
            match parser::parse_instance(definitions, proof, None, config) {
                Ok(parsed) => parsed,
                Err(e) => return Verdict::ParseError(e.to_string()),
            };
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
        let result = checker::ProofChecker::new(&mut pool, &rare_rules, checker::Config::new())
            .check(&problem, &proof)
            .map_err(|e| e.to_string());
        Verdict::Checked(result)
    };
    panic::catch_unwind(AssertUnwindSafe(run)).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
            .unwrap_or_default();
        Verdict::Panicked(message)
    })
}

/// Asserts that the checker refuses `proof` (it parses), and returns the error.
fn refused(definitions: &str, proof: &str) -> String {
    match check(definitions, proof) {
        Verdict::Checked(Err(e)) => e,
        other => panic!("expected the checker to refuse\n{proof}\ngot {other:?}"),
    }
}

/// Asserts that the parser refuses `proof`, and returns the error.
fn unparsed(definitions: &str, proof: &str) -> String {
    match check(definitions, proof) {
        Verdict::ParseError(e) => e,
        other => panic!("expected a parse error\n{definitions}\n{proof}\ngot {other:?}"),
    }
}

fn balanced_end(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (offset, c) in text[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(open + offset + 1);
                }
            }
            _ => {}
        }
    }
    None
}

/// The byte ranges of the `step` commands of `proof`, in order (including those in subproofs).
fn step_spans(proof: &str) -> Vec<(usize, usize)> {
    proof
        .match_indices("(step ")
        .filter_map(|(start, _)| Some((start, balanced_end(proof, start)?)))
        .collect()
}

/// `step` with its rule renamed to `rule` and its `:args` replaced by `args` (dropped for `None`).
/// Its id, conclusion, premises and discharge are kept.
fn restep(step: &str, rule: &str, args: Option<&str>) -> Option<String> {
    let rule_at = step.find(":rule ")? + ":rule ".len();
    let name_end = rule_at + step[rule_at..].find(|c: char| c.is_whitespace() || c == ')')?;
    let mut tail = step[name_end..step.len() - 1].to_owned();
    if let Some(at) = tail.find(":args") {
        let open = at + tail[at..].find('(')?;
        let end = balanced_end(&tail, open)?;
        tail.replace_range(at..end, "");
    }
    let args = args.map(|a| format!(" :args ({a})")).unwrap_or_default();
    Some(format!("{}{rule}{tail}{args})", &step[..rule_at]))
}

/// The first literal of `step`'s conclusion, as written.
fn first_literal(step: &str) -> Option<String> {
    let clause = step.find("(cl")? + "(cl".len();
    let rest = step[clause..].trim_start();
    let at = step.len() - rest.len();
    match rest.chars().next()? {
        ')' => None,
        '(' => Some(step[at..balanced_end(step, at)?].to_owned()),
        _ => rest
            .split(|c: char| c.is_whitespace() || c == ')')
            .next()
            .map(str::to_owned),
    }
}

/// The argument lists a step is tried with: none, the clause argument `(cl)` of `drup`, one to
/// three integers, and its first conclusion literal one to three times.
fn arg_shapes(step: &str) -> Vec<Option<String>> {
    let mut shapes = vec![None, Some("(cl)".to_owned())];
    for k in 1..=3 {
        shapes.push(Some(["0", "1", "2"][..k].join(" ")));
        if let Some(literal) = first_literal(step) {
            shapes.push(Some(vec![literal.as_str(); k].join(" ")));
        }
    }
    shapes
}

/// Calls `visit` with `proof` with each step renamed to each rule, in each argument shape.
fn renamings(proof: &str, rules: &[String], mut visit: impl FnMut(&str, &str)) {
    for (start, end) in step_spans(proof) {
        let step = &proof[start..end];
        for rule in rules {
            for args in arg_shapes(step) {
                if let Some(renamed) = restep(step, rule, args.as_deref()) {
                    visit(
                        rule,
                        &format!("{}{renamed}{}", &proof[..start], &proof[end..]),
                    );
                }
            }
        }
    }
}

/// Small valid proofs whose steps cover the rule families: resolution and DRUP, bit-blasting,
/// pseudo-Boolean blasting, linear arithmetic, cutting planes, arrays, strings, the subproof
/// rules (`bind` and `onepoint` end anchors with arguments), and a `match` over a datatype (renamed
/// `evaluate`, it reached a `todo!()`).
const BASES: &[(&str, &str)] = &[
    (
        "(declare-const a Bool) (declare-const b Bool) (declare-const c Bool)
         (declare-const d Bool) (declare-const e Bool)",
        "(assume a0 (or a c))
         (assume a1 (or a (not c) d))
         (assume a2 (or (not d) e))
         (assume a3 (or (not d) (not e)))
         (assume a4 (not a))
         (step t0 (cl a c) :rule or :premises (a0))
         (step t1 (cl a (not c) d) :rule or :premises (a1))
         (step t2 (cl (not d) e) :rule or :premises (a2))
         (step t3 (cl (not d) (not e)) :rule or :premises (a3))
         (step t4 (cl a) :rule drup :premises (t0 t1 t2 t3) :args ((cl a)))
         (step t5 (cl) :rule drup :premises (t4 a4) :args ((cl)))",
    ),
    (
        "(declare-const p Bool) (declare-const q Bool)",
        "(assume h1 (and p q))
         (assume h2 (not p))
         (step t1 (cl p) :rule and :premises (h1) :args (0))
         (step t2 (cl (not (and p q)) q) :rule and_pos :args (1))
         (step t3 (cl) :rule resolution :premises (t1 h2))",
    ),
    (
        "(declare-const x (_ BitVec 2)) (declare-const y (_ BitVec 2))",
        "(step t1 (cl (= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))) :rule bitblast_var)
         (step t2 (cl (= (bvand x y) (@bbterm (and ((_ @bit_of 0) x) ((_ @bit_of 0) y))
             (and ((_ @bit_of 1) x) ((_ @bit_of 1) y))))) :rule bitblast_and)
         (step t3 (cl (= #b10 (@bbterm false true))) :rule bitblast_const)",
    ),
    (
        "(declare-const x1 (_ BitVec 1)) (declare-const y1 (_ BitVec 1))
         (declare-const x2 (_ BitVec 2)) (declare-const y2 (_ BitVec 2))",
        "(step t1 (cl (= (bvand x1 y1) (@pbbterm (! (choice ((z Int)) (and
             (>= ((_ @int_of 0) x1) z)
             (>= ((_ @int_of 0) y1) z)
             (>= (+ z 1) (+ ((_ @int_of 0) x1) ((_ @int_of 0) y1))))) :named @r0))))
             :rule pbblast_bvand)
         (step t2 (cl (= (= x2 y2) (= (- (+ (* 1 ((_ @int_of 0) x2)) (* 2 ((_ @int_of 1) x2)))
             (+ (* 1 ((_ @int_of 0) y2)) (* 2 ((_ @int_of 1) y2)))) 0))) :rule pbblast_bveq)",
    ),
    (
        "(declare-const bits (_ BitVec 2))
         (define-fun x () Int ((_ @int_of 0) bits))
         (define-fun y () Int ((_ @int_of 1) bits))
         (define-fun r () Int (choice ((z Int)) (and (>= x z) (>= y z) (>= (+ z 1) (+ x y)))))",
        "(step t1 (cl (and (>= x r) (>= y r) (>= (+ r 1) (+ x y))))
             :rule pbblast_bvand_ith_bit :args (x y))
         (assume c1 (>= (* 2 x) 2))
         (step t2 (cl (>= (* 1 x) 1)) :rule cp_division :premises (c1) :args (2))
         (step t3 (cl (>= x 0)) :rule cp_literal :args (x))",
    ),
    (
        "(declare-const a Real) (declare-const b Real)",
        "(step t1 (cl (> a 0.0) (<= a 0.0)) :rule la_generic :args (1.0 1.0))
         (step t2 (cl (< (+ a b) 1.0) (> (+ a b) 0.0)) :rule la_generic :args (1.0 (- 1.0)))",
    ),
    (
        "(declare-fun A () (Array Int Int)) (declare-fun B () (Array Int Int))
         (declare-const x Int) (declare-const i Int) (declare-const j Int)",
        "(assume h1 (not (= i j)))
         (step t1 (cl (= (select (store A i x) j) (select A j))) :rule arrays_row :premises (h1))
         (assume h2 (not (= A B)))
         (step t2 (cl (not (=
             (select A (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
             (select B (choice ((x Int)) (or (= A B) (not (= (select A x) (select B x))))))
         ))) :rule arrays_ext :premises (h2))",
    ),
    (
        "(declare-fun a () String)",
        r#"(assume h1 (= "0A" (str.++ "0" (str.from_code (str.len a)))))
           (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1)
               :args (false))"#,
    ),
    (
        "(declare-fun p () Bool) (declare-fun q () Bool) (declare-fun y () Real)",
        "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
         (step t1.t1 (cl (= p q)) :rule hole)
         (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)",
    ),
    (
        "(declare-const p Bool) (declare-const t Int)",
        "(anchor :step t1 :args ((:= (x Int) t)))
         (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule hole)
         (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p))) :rule onepoint)",
    ),
    (
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L))))) (declare-const x L)",
        "(step t1 (cl (= (match x ((nil 0) ((cons h t) h))) (match x ((nil 0) ((cons h t) h)))))
             :rule refl)",
    ),
];

/// Every step of every base proof, renamed to every rule, in every argument shape of
/// `arg_shapes`: among them the reported crash, a `drup` step concluding `(cl)` with the argument
/// `(cl)`, renamed `pbblast_bvand`. Each mutant is refused or accepted; none may panic.
#[test]
fn every_rule_on_every_step_shape_is_judged_without_a_panic() {
    let rules = rule_names();
    assert!(
        rules.len() > 150,
        "read only {} rule names from get_rule",
        rules.len()
    );
    for rule in [
        "pbblast_bvand",
        "bitblast_equal",
        "cp_division",
        "arrays_ext",
        "drup",
    ] {
        assert!(
            rules.iter().any(|r| r == rule),
            "{rule} not read from get_rule"
        );
    }
    let (mut runs, mut reached, mut panics) = (0usize, 0usize, Vec::new());
    for (definitions, proof) in BASES {
        assert!(
            matches!(check(definitions, proof), Verdict::Checked(Ok(_))),
            "base proof does not check: {proof}"
        );
        renamings(proof, &rules, |_, mutant| {
            runs += 1;
            match check(definitions, mutant) {
                Verdict::Panicked(message) => panics.push(format!("{message}\n{mutant}")),
                Verdict::Checked(_) => reached += 1,
                Verdict::ParseError(_) => {}
            }
        });
    }
    assert!(
        panics.is_empty(),
        "{} of {runs} mutants panicked; the first:\n{}",
        panics.len(),
        panics[0]
    );
    // Not vacuous: almost every mutant parses, so the renamed rule itself judges it.
    assert!(
        reached * 100 >= runs * 95,
        "only {reached} of {runs} mutants reached the checker"
    );
}

/// Steps over bit-vectors of `{W}` bits, each closed by `hole`: every bit-vector operator a rule
/// expands, the extensions, extraction, constants and the `2^w` of `poly_simp` and `aci_simp`.
const WIDE_STEPS: &str = "
    (step w1 (cl (= (bvult x y) false)) :rule hole)
    (step w2 (cl (= (bvslt x y) false)) :rule hole)
    (step w3 (cl (= (bvadd x y) z)) :rule hole)
    (step w4 (cl (= (bvmul x y) z)) :rule hole)
    (step w5 (cl (= (bvudiv x y) z)) :rule hole)
    (step w6 (cl (= (bvurem x y) z)) :rule hole)
    (step w7 (cl (= (bvshl x y) z)) :rule hole)
    (step w8 (cl (= (bvlshr x y) z)) :rule hole)
    (step w9 (cl (= (bvashr x y) z)) :rule hole)
    (step w10 (cl (= (bvand x y) z)) :rule hole)
    (step w11 (cl (= (bvor x y z) z)) :rule hole)
    (step w12 (cl (= (bvxor x y) z)) :rule hole)
    (step w13 (cl (= (bvxnor x y) z)) :rule hole)
    (step w14 (cl (= (bvnot x) z)) :rule hole)
    (step w15 (cl (= (bvneg x) z)) :rule hole)
    (step w16 (cl (= (bvcomp x y) c)) :rule hole)
    (step w17 (cl (= (= x y) false)) :rule hole)
    (step w18 (cl (= x z)) :rule hole)
    (step w19 (cl (= (bvand x x) x)) :rule hole)
    (step w20 (cl (= (bvsub x y) z)) :rule hole)
    (step w21 (cl (= ((_ extract 3 0) x) ((_ extract 3 0) y))) :rule hole)
    (step w22 (cl (= (concat x c) (concat c x))) :rule hole)
    (step w23 (cl (= ((_ zero_extend 1) x) (concat c x))) :rule hole)
    (step w24 (cl (= ((_ sign_extend 1) x) (concat c x))) :rule hole)
    (step w25 (cl (= (_ bv0 {W}) x)) :rule hole)
    (step w26 (cl (= (bvule x y) (bvuge y x))) :rule hole)
    (step w27 (cl (bvult x y) (bvuge x y)) :rule hole)
    (step w28 (cl (= (bvudiv (_ bv1 {W}) y) z)) :rule hole)
    (step w29 (cl (= (ubv_to_int x) 0)) :rule hole)
    (step w30 (cl (= (bvmul x (_ bv2 {W})) (bvshl x (_ bv1 {W})))) :rule hole)
";

/// Every rule on every step over bit-vectors of 2^32 + 1 and of 2^64 - 2 bits (the widest whose
/// `concat` with a bit fits a `usize`), in every argument shape, is judged without a panic and
/// within the resource budget. Such widths are well formed;
/// expanding one bit-blasted billions of terms, and computing `2^w` aborted the process in GMP
/// (see third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource budget"). A rule
/// that still expanded one would exhaust memory here rather than fail an assertion.
#[test]
fn every_rule_on_a_wide_step_is_judged_within_the_budget() {
    let rules = rule_names();
    let (mut runs, mut over_budget, mut panics) = (0usize, 0usize, Vec::new());
    for width in ["4294967297", "18446744073709551614"] {
        let definitions = format!(
            "(declare-const x (_ BitVec {width})) (declare-const y (_ BitVec {width}))
             (declare-const z (_ BitVec {width})) (declare-const c (_ BitVec 1))"
        );
        let proof = WIDE_STEPS.replace("{W}", width);
        let config = || parser::Config::clean_dialect();
        assert!(
            matches!(
                check_in(config(), &definitions, &proof),
                Verdict::Checked(Ok(_))
            ),
            "the wide base proof does not check"
        );
        renamings(&proof, &rules, |_, mutant| {
            runs += 1;
            match check_in(config(), &definitions, mutant) {
                Verdict::Panicked(message) => panics.push(format!("{message}\n{mutant}")),
                Verdict::Checked(Err(e)) if e.contains("resource budget exceeded") => {
                    over_budget += 1
                }
                _ => {}
            }
        });
    }
    assert!(
        panics.is_empty(),
        "{} of {runs} mutants panicked; the first:\n{}",
        panics.len(),
        panics[0]
    );
    // Not vacuous: the expanding rules reached the budget on the wide steps.
    assert!(
        over_budget >= 100,
        "only {over_budget} of {runs} mutants met the budget"
    );
}

/// Rules that read the first literal of their conclusion without checking the clause length
/// refuse the empty clause (`conclusion[0]` panicked).
#[test]
fn an_empty_conclusion_is_refused() {
    // The reported crash: a `drup` step concluding `(cl)`, renamed.
    let e = refused(
        "(declare-const a Bool)",
        "(assume a0 a) (assume a1 (not a))
         (step t1 (cl) :rule pbblast_bvand :premises (a0 a1) :args ((cl)))",
    );
    assert!(
        e.contains("pbblast_bvand") && e.contains("terms in clause"),
        "{e}"
    );

    for rule in [
        "pbblast_bveq",
        "pbblast_bvult",
        "pbblast_bvugt",
        "pbblast_bvuge",
        "pbblast_bvule",
        "pbblast_bvslt",
        "pbblast_bvsgt",
        "pbblast_bvsge",
        "pbblast_bvsle",
        "pbblast_pbbvar",
        "pbblast_pbbconst",
        "pbblast_bvxor",
        "pbblast_bvand",
    ] {
        let e = refused("", &format!("(step t1 (cl) :rule {rule})"));
        assert!(e.contains("terms in clause"), "{rule}: {e}");
    }
    // The `ith_bit` rules and `cp_literal` check their arguments first, so they get valid ones.
    let bits = "(declare-const bits (_ BitVec 2))
                (define-fun x () Int ((_ @int_of 0) bits))
                (define-fun y () Int ((_ @int_of 1) bits))";
    for (rule, args) in [
        ("pbblast_bvxor_ith_bit", "x y"),
        ("pbblast_bvand_ith_bit", "x y"),
        ("cp_literal", "x"),
    ] {
        let e = refused(bits, &format!("(step t1 (cl) :rule {rule} :args ({args}))"));
        assert!(e.contains("terms in clause"), "{rule}: {e}");
    }
    let e = refused(
        "(declare-fun A () (Array Int Int)) (declare-fun B () (Array Int Int))",
        "(assume h1 (not (= A B))) (step t1 (cl) :rule arrays_ext :premises (h1))",
    );
    assert!(e.contains("terms in clause"), "{e}");
}

/// `bitblast_equal` matches `(= x y)` at any sort; an operand that is not a bit-vector was a
/// `panic!` in `bitvector_size`.
#[test]
fn a_bit_blasting_operand_of_another_sort_is_refused() {
    let e = refused(
        "(declare-const a Int) (declare-const b Int)",
        "(step t1 (cl (= (= a b) (= a b))) :rule bitblast_equal)",
    );
    assert!(e.contains("expected a bit-vector term"), "{e}");
}

/// `cp_division` and `cp_saturation` read the first literal of their premise unchecked: an empty
/// premise clause panicked, and a longer one was used as if its first literal held (fix 41).
#[test]
fn cutting_plane_premises_are_unit_clauses() {
    let defs = "(declare-const bits (_ BitVec 2))
                (define-fun x1 () Int ((_ @int_of 0) bits))
                (define-fun x2 () Int ((_ @int_of 1) bits))";
    for (rule, args) in [("cp_division", ":args (2)"), ("cp_saturation", "")] {
        let e = refused(
            defs,
            &format!(
                "(step t0 (cl) :rule hole)
                 (step t1 (cl (>= (* 1 x1) 1)) :rule {rule} :premises (t0) {args})"
            ),
        );
        assert!(
            e.contains("expected 1 terms in clause, got 0"),
            "{rule}: {e}"
        );
    }
    // Both were accepted before. With x1 = 0 and x2 = 1 the premise clause holds and the
    // conclusion does not.
    let e = refused(
        defs,
        "(assume c1 (or (>= (* 2 x1) 2) (>= (* 2 x2) 2)))
         (step t0 (cl (>= (* 2 x1) 2) (>= (* 2 x2) 2)) :rule or :premises (c1))
         (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (t0) :args (2))",
    );
    assert!(e.contains("expected 1 terms in clause, got 2"), "{e}");
    let e = refused(
        defs,
        "(assume c1 (or (>= (* 2 x1) 1) (>= (* 1 x2) 1)))
         (step t0 (cl (>= (* 2 x1) 1) (>= (* 1 x2) 1)) :rule or :premises (c1))
         (step t1 (cl (>= (* 1 x1) 1)) :rule cp_saturation :premises (t0))",
    );
    assert!(e.contains("expected 1 terms in clause, got 2"), "{e}");
    // The unit forms still check.
    for proof in [
        "(assume c1 (>= (* 2 x1) 2))
         (step t1 (cl (>= (* 1 x1) 1)) :rule cp_division :premises (c1) :args (2))",
        "(assume c1 (>= (* 2 x1) 1))
         (step t1 (cl (>= (* 1 x1) 1)) :rule cp_saturation :premises (c1))",
    ] {
        assert!(
            matches!(check(defs, proof), Verdict::Checked(Ok(_))),
            "{proof}"
        );
    }
}

/// `la_mult_sign` with a factor of the monomial that no hypothesis gives a sign reached `todo!()`.
#[test]
fn a_monomial_factor_without_a_sign_is_refused() {
    let e = refused(
        "(declare-const a Real) (declare-const b Real) (declare-const c Real)",
        "(step t1 (cl (=> (and (< b 0.0) (> c 0.0)) (> (* a b c) 0.0))) :rule la_mult_sign)",
    );
    assert!(e.contains("no sign hypothesis for the factor 'a'"), "{e}");
}

/// `la_mult_pos` and `la_mult_neg` with a multiplied atom whose operator is not a comparison,
/// `(cl x y)`, reached `unreachable!()` (the soundness battery's `--dialect clean --seed 77`).
#[test]
fn a_multiplied_atom_that_is_not_a_comparison_is_refused() {
    let defs = "(declare-const x Real) (declare-const y Real)";
    for (rule, m) in [("la_mult_pos", "(/ 10.0 13.0)"), ("la_mult_neg", "(- 2.0)")] {
        let sign = if rule == "la_mult_pos" { ">" } else { "<" };
        let step = |atom: &str, scaled: &str| {
            format!("(step t1 (cl (=> (and ({sign} {m} 0.0) {atom}) {scaled})) :rule {rule})")
        };
        let scaled = format!("(= (* {m} x) (* {m} y))");
        for config in [parser::Config::new(), parser::Config::clean_dialect()] {
            match check_in(config, defs, &step("(cl x y)", &scaled)) {
                Verdict::Checked(Err(e)) => {
                    assert!(e.contains("expected comparison operation"), "{rule}: {e}")
                }
                other => panic!("{rule}: expected a refusal, got {other:?}"),
            }
        }
        let ok = step("(= x y)", &scaled);
        assert!(
            matches!(check(defs, &ok), Verdict::Checked(Ok(_))),
            "{rule}: {:?}",
            check(defs, &ok)
        );
    }
}

/// An index argument of 2^64 or more was unwrapped into a `usize` (`Term::as_usize_err`).
#[test]
fn an_index_argument_beyond_usize_is_refused() {
    let defs = "(declare-const p Bool) (declare-const q Bool)";
    let e = refused(
        defs,
        "(assume h1 (and p q))
         (step t1 (cl p) :rule and :premises (h1) :args (18446744073709551616))",
    );
    assert!(e.contains("out of range"), "{e}");
    let ok = "(assume h1 (and p q)) (step t1 (cl p) :rule and :premises (h1) :args (0))";
    assert!(matches!(check(defs, ok), Verdict::Checked(Ok(_))));
}

/// Bit-vector widths are positive and fit a `usize`: a width of 2^64 or more panicked in the
/// parser, and width 0 made the bit-blasting rules index an empty list of bits. (A result width
/// past `usize` is `BitVecWidthOverflow`, tested in clean-auto's `parser_width_tests.rs`.)
#[test]
fn bit_vector_widths_are_positive_and_fit_usize() {
    let hole = "(step t1 (cl) :rule hole)";
    for sort in ["(_ BitVec 0)", "(_ BitVec 18446744073709551616)"] {
        let e = unparsed(&format!("(declare-const x {sort})"), hole);
        assert!(e.contains("expected argument value"), "{sort}: {e}");
    }
    for literal in [
        "(_ bv1 18446744073709551616)",
        "(_ bv1 0)",
        "(_ bv 4)",
        "(_ bvx 4)",
    ] {
        unparsed(
            "",
            &format!("(step t1 (cl (= {literal} {literal})) :rule refl)"),
        );
    }
    let x4 = "(declare-const x (_ BitVec 4))";
    let e = unparsed(
        x4,
        "(step t1 (cl (= ((_ repeat 0) x) ((_ repeat 0) x))) :rule refl)",
    );
    assert!(e.contains("expected argument value"), "{e}");
    // The ordinary forms still parse.
    for term in [
        "((_ repeat 1) x)",
        "((_ zero_extend 0) x)",
        "((_ sign_extend 0) x)",
    ] {
        let proof = format!("(step t1 (cl (= {term} {term})) :rule refl)");
        assert!(
            matches!(check(x4, &proof), Verdict::Checked(Ok(_))),
            "{term}"
        );
    }
    let proof = "(step t1 (cl (= (_ bv5 3) #b101)) :rule hole)";
    assert!(matches!(check("", proof), Verdict::Checked(Ok(_))));
}

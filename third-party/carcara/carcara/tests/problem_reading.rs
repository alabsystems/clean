// Added in Clean (not part of upstream Carcara): how the parser reads a problem script. A
// refutation is only as sound as the premises it is checked against, so each test pins the
// reading of a script, or its refusal. See third-party/carcara/DOWNSTREAM.md, fixes 36 to 40.

use carcara::{
    ast::{alpha_equiv, pool::PrimitivePool, Operator, Rc, Term},
    checker, parser,
};
use indexmap::IndexSet;
use std::time::Duration;

/// Checks `proof` against `problem` in one `define-fun` reading. `Ok(is_holey)`, or the error.
fn check(problem: &str, proof: &str, apply_function_defs: bool) -> Result<bool, String> {
    let config = parser::Config::new().apply_function_defs(apply_function_defs);
    let (problem, proof, rules, mut pool) =
        parser::parse_instance(problem, proof, None, config).map_err(|e| e.to_string())?;
    checker::ProofChecker::new(&mut pool, &rules, checker::Config::new())
        .check(&problem, &proof)
        .map_err(|e| e.to_string())
}

/// Whether `proof` is a complete refutation of `problem` in either `define-fun` reading, as Clean's
/// adapter (`clean cert verify-external`) accepts it: the ordinary reading first, then the macro
/// reading. On refusal, both errors.
fn refutes(problem: &str, proof: &str) -> Result<(), String> {
    let ordinary = check(problem, proof, false);
    let macros = check(problem, proof, true);
    match (&ordinary, &macros) {
        (Ok(false), _) | (_, Ok(false)) => Ok(()),
        _ => Err(format!("ordinary: {ordinary:?}; macros: {macros:?}")),
    }
}

/// The premises `problem` is read with, in one `define-fun` reading, interned in `pool`.
fn premises(
    pool: &mut PrimitivePool,
    problem: &str,
    apply_function_defs: bool,
) -> Result<IndexSet<Rc<Term>>, String> {
    let config = parser::Config::new().apply_function_defs(apply_function_defs);
    let mut parser = parser::Parser::new(pool, config, problem).map_err(|e| e.to_string())?;
    let problem = parser.parse_problem().map_err(|e| e.to_string())?;
    Ok(problem.premises)
}

/// Asserts that `problem` is read, in the given `define-fun` reading, with exactly the premises of
/// `expected`, a script written without the definitions.
fn assert_reads_as(problem: &str, apply_function_defs: bool, expected: &str) {
    let mut pool = PrimitivePool::new();
    let got = premises(&mut pool, problem, apply_function_defs)
        .unwrap_or_else(|e| panic!("{problem} should parse: {e}"));
    let want = premises(&mut pool, expected, apply_function_defs)
        .unwrap_or_else(|e| panic!("{expected} should parse: {e}"));
    assert_eq!(got, want, "{problem} is not read as {expected}");
}

/// Whether `problem` is read, in the given `define-fun` reading, with premises alpha-equivalent one
/// by one to those of `expected`, a script whose bound variables have other names.
fn reads_up_to_bound_names(problem: &str, apply_function_defs: bool, expected: &str) -> bool {
    let mut pool = PrimitivePool::new();
    let got = premises(&mut pool, problem, apply_function_defs)
        .unwrap_or_else(|e| panic!("{problem} should parse: {e}"));
    let want = premises(&mut pool, expected, apply_function_defs)
        .unwrap_or_else(|e| panic!("{expected} should parse: {e}"));
    got.len() == want.len()
        && got
            .iter()
            .zip(want.iter())
            .all(|(a, b)| alpha_equiv(a, b, &mut Duration::default()))
}

/// The parse error of `problem` (with a trivial proof) in one `define-fun` reading, if any.
fn parse_error(problem: &str, apply_function_defs: bool) -> Option<String> {
    let config = parser::Config::new().apply_function_defs(apply_function_defs);
    parser::parse_instance(problem, "(step t1 (cl) :rule hole)", None, config)
        .err()
        .map(|e| e.to_string())
}

const X: &str = "(declare-fun x () Int)";
const PAIR: &str = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
    (declare-fun a () Int)
    (declare-fun b () Int)
    (declare-fun g (P) Int)";

/// A `define-fun` parameter does not capture a global symbol that a macro used in its body
/// mentions. Upstream substituted every occurrence of the parameter's `Term::Var` in the expanded
/// body, the global's included: `h` below was the identity, not the constant `x`.
#[test]
fn define_fun_parameters_do_not_capture_globals() {
    // The adversarial review's B03 shape: `(h 5)` is `x`.
    assert_reads_as(
        &format!("{X} (define-fun k () Int x) (define-fun h ((x Int)) Int k) (assert (= (h 5) x))"),
        true,
        &format!("{X} (assert (= x x))"),
    );
    // B06: through a `:named` term, which is always a macro.
    assert_reads_as(
        &format!(
            "{X} (assert (= (! x :named k) x)) (define-fun h ((x Int)) Int k)
            (assert (= (h 5) x))"
        ),
        true,
        &format!("{X} (assert (= x x))"),
    );
    // B04: the captured global is a selector.
    assert_reads_as(
        &format!(
            "{PAIR} (define-fun k ((y P)) Int (fst y)) (define-fun h ((fst (-> P Int))) Int (k (mk a b)))
            (assert (not (= (h g) (g (mk a b)))))"
        ),
        true,
        &format!("{PAIR} (assert (not (= (fst (mk a b)) (g (mk a b)))))"),
    );
    // B10, B11: the captured global is an uninterpreted function.
    for (arg, rhs) in [("fst", "a"), ("oth", "(oth (mk a b))")] {
        assert_reads_as(
            &format!(
                "{PAIR} (define-fun k ((y P)) Int (g y)) (define-fun h ((g (-> P Int))) Int (k (mk a b)))
                (assert (not (= (h {arg}) {rhs})))"
            ),
            true,
            &format!("{PAIR} (assert (not (= (g (mk a b)) {rhs})))"),
        );
    }
    // Where the body names the parameter itself, it is still the parameter.
    assert_reads_as(
        &format!(
            "{X} (define-fun k () Int x) (define-fun h ((x Int)) Int (+ x k))
            (assert (= (h 5) 7))"
        ),
        true,
        &format!("{X} (assert (= (+ 5 x) 7))"),
    );
    // A renamed definition used inside another definition whose parameter has the same name.
    assert_reads_as(
        &format!(
            "{X} (define-fun k () Int x) (define-fun h ((x Int)) Int k)
            (define-fun j ((x Int)) Int (+ (h x) x)) (assert (= (j 7) 1))"
        ),
        true,
        &format!("{X} (assert (= (+ x 7) 1))"),
    );
    // A term named inside such a body defines its name as the global, not as a placeholder.
    assert_reads_as(
        &format!(
            "{X} (define-fun k () Int x) (define-fun h ((x Int)) Int (! k :named m))
            (assert (= m (h 3)))"
        ),
        true,
        &format!("{X} (assert (= x x))"),
    );
}

/// Without a capture, definitions read as they always did, in both readings: the ordinary reading
/// keeps the parameter names of the defining `lambda`, which a proof must write to `assume` it.
#[test]
fn definitions_without_capture_keep_their_reading() {
    assert_reads_as(
        &format!("{X} (define-fun f ((x Int)) Int (+ x 1)) (assert (= (f 5) 6))"),
        false,
        &format!(
            "{X} (declare-fun f (Int) Int) (assert (= f (lambda ((x Int)) (+ x 1))))
            (assert (= (f 5) 6))"
        ),
    );
    assert_reads_as(
        &format!("{X} (define-fun f ((x Int)) Int (+ x 1)) (assert (= (f 5) 6))"),
        true,
        &format!("{X} (assert (= (+ 5 1) 6))"),
    );
    assert_reads_as(
        &format!(
            "{X} (define-fun k () Int x) (define-fun h ((y Int)) Int (+ y k)) (assert (= (h 5) 7))"
        ),
        true,
        &format!("{X} (assert (= (+ 5 x) 7))"),
    );
    // AY's nullary macro and `:named` label shapes.
    assert_reads_as(
        "(declare-const x Int) (define-fun lo () Bool (< x 3)) (define-fun lo2 () Bool lo)
        (assert lo2) (assert (not lo))",
        true,
        "(declare-const x Int) (assert (< x 3)) (assert (not (< x 3)))",
    );
    for apply_function_defs in [false, true] {
        assert_reads_as(
            "(declare-const x Int) (assert (! (< x 3) :named a)) (assert (not a))",
            apply_function_defs,
            "(declare-const x Int) (assert (< x 3)) (assert (not (< x 3)))",
        );
    }
}

/// A local binding shadows a function definition of the same name, as it shadows any other global
/// symbol. Upstream read the bound `k` below as the constant `5`.
#[test]
fn local_bindings_shadow_function_definitions() {
    assert_reads_as(
        "(define-fun k () Int 5) (assert (exists ((k Int)) (not (= k 5))))",
        true,
        "(assert (exists ((k Int)) (not (= k 5))))",
    );
    for apply_function_defs in [false, true] {
        assert_reads_as(
            "(assert (= (! 5 :named k) 5)) (assert (exists ((k Int)) (not (= k 5))))",
            apply_function_defs,
            "(assert (= 5 5)) (assert (exists ((k Int)) (not (= k 5))))",
        );
    }
    // A parameter named like a macro is the parameter.
    assert_reads_as(
        "(define-fun k () Int 5) (define-fun h ((k Int)) Int (+ k 1)) (assert (= (h 2) 3))",
        true,
        "(assert (= (+ 2 1) 3))",
    );
    // Outside the binder the name is the macro again.
    assert_reads_as(
        "(define-fun k () Int 5) (assert (and (forall ((k Int)) (> k 0)) (= k 5)))",
        true,
        "(assert (and (forall ((k Int)) (> k 0)) (= 5 5)))",
    );
}

/// Where a binder other than the enclosing `define-fun`'s parameters rebinds a name that a macro
/// mentions, the problem is refused: its reading would capture the name, and renaming the binder
/// would change the premise a proof has to `assume`. In a proof, the capture is kept as upstream
/// has it (a proof's terms are judged as written).
#[test]
fn macro_capture_under_a_binder_is_refused_in_the_problem() {
    let uses = [
        "(assert (exists ((x Int)) (not (= k x))))",
        "(assert (forall ((x Int)) (= k x)))",
        "(assert (= (lambda ((x Int)) k) (lambda ((y Int)) y)))",
        "(assert (let ((x 1)) (= k x)))",
        "(assert (= (choice ((x Int)) (= k x)) 0))",
        "(define-fun h ((x Int)) Bool (forall ((x Int)) (= k x)))",
        "(declare-datatype L ((nil) (cons (hd Int) (tl L)))) (declare-fun l () L)
        (assert (match l ((nil false) ((cons x t) (= k x)))))",
    ];
    for definition in ["(define-fun k () Int x)", "(assert (= (! x :named k) x))"] {
        for usage in uses {
            let problem = format!("{X} {definition} {usage}");
            let named = definition.contains(":named");
            for apply_function_defs in [false, true] {
                let error = parse_error(&problem, apply_function_defs);
                if named || apply_function_defs {
                    assert!(
                        matches!(&error, Some(e) if e.contains("'k' is used where a binder rebinds 'x'")),
                        "{problem} ({apply_function_defs}): {error:?}"
                    );
                } else {
                    // `k` is a declared constant, which the binder does not capture.
                    assert_eq!(error, None, "{problem}");
                }
            }
        }
    }
    // The S04 refutation: `(exists ((x Int)) (not (= k x)))` is satisfiable, and was read as
    // `(exists ((x Int)) (not (= x x)))` with `k` expanded.
    let problem = format!("{X} (define-fun k () Int x) (assert (exists ((x Int)) (not (= k x))))");
    let proof = "
        (assume a0 (exists ((x Int)) (not (= k x))))
        (anchor :step t3 :args ((x Int)))
        (step t3.t1 (cl (= (= x x) true)) :rule eq_simplify)
        (step t3.t2 (cl (= (not (= x x)) (not true))) :rule cong :premises (t3.t1))
        (step t3 (cl (= (exists ((x Int)) (not (= x x))) (exists ((x Int)) (not true)))) :rule bind)
        (anchor :step t5 :args ((x Int)))
        (step t5.t1 (cl (= (not true) false)) :rule not_simplify)
        (step t5 (cl (= (exists ((x Int)) (not true)) (exists ((x Int)) false))) :rule bind)
        (step t6 (cl (= (exists ((x Int)) false) false)) :rule qnt_rm_unused)
        (step t7 (cl (= (exists ((x Int)) (not (= x x))) false)) :rule trans :premises (t3 t5 t6))
        (step t8 (cl (not (= (exists ((x Int)) (not (= x x))) false))
            (not (exists ((x Int)) (not (= x x)))) false) :rule equiv_pos2)
        (step t9 (cl (not false)) :rule false)
        (step t10 (cl) :rule resolution :premises (a0 t7 t8 t9))
    ";
    assert!(refutes(&problem, proof).is_err());
    // The same shape with the constant written out is a sound refutation, and is accepted.
    let unsat = "(assert (exists ((x Int)) (not (= x x))))";
    let proof = proof.replace("(not (= k x))", "(not (= x x))");
    assert_eq!(refutes(unsat, &proof), Ok(()));

    // In a proof, a named term reused under a binder of its free variable keeps upstream's
    // reading.
    let config = parser::Config::new().apply_function_defs(true);
    let proof = "(assume a0 (forall ((y Int)) (! (> y 0) :named n)))
        (step t1 (cl (forall ((y Int)) n)) :rule hole)";
    let parsed = parser::parse_instance("(assert true)", proof, None, config);
    assert!(parsed.is_ok(), "{:?}", parsed.err());
}

/// A `:named` term in the problem must be closed (SMT-LIB): its name is a global definition.
#[test]
fn named_terms_in_the_problem_must_be_closed() {
    for apply_function_defs in [false, true] {
        let error = parse_error(
            "(assert (forall ((y Int)) (! (> y 0) :named n))) (assert (not n))",
            apply_function_defs,
        );
        assert!(
            matches!(&error, Some(e) if e.contains("the term named 'n' mentions the bound variable 'y'")),
            "{error:?}"
        );
        assert_eq!(
            parse_error(
                "(declare-fun y () Int) (assert (forall ((z Int)) (! (> y 0) :named n))) (assert n)",
                apply_function_defs
            ),
            None
        );
    }
}

/// The adversarial review's refutations of satisfiable problems through a misread definition
/// (B03, B04, B06, B07, B10, B11) and through scoping commands (B08, B09, Z01), and further ones
/// found while fixing them (S01, S02, Q01..Q05; S03 and S04 are in
/// `macro_capture_under_a_binder_is_refused_in_the_problem`). Each was accepted as complete
/// before fixes 36 and 37; each must now be refused.
#[test]
fn refutations_of_misread_problems_are_refused() {
    let resolve_x5 = "(assume a0 (= (h 5) x))
        (assume a1 (not (= x 5)))
        (step t1 (cl (= x 5)) :rule symm :premises (a0))
        (step t2 (cl) :rule resolution :premises (a1 t1))";
    let p_not_p = "(assume a0 p)
        (assume a1 (not p))
        (step t1 (cl) :rule resolution :premises (a0 a1))";
    let shadow_proof = "(assume a0 (exists ((k Int)) (not (= k 5))))
        (step t1 (cl (= (exists ((k Int)) (not (= k 5))) (not (= k 5)))) :rule qnt_rm_unused)
        (step t2 (cl (not (= (exists ((k Int)) (not (= k 5))) (not (= k 5))))
            (not (exists ((k Int)) (not (= k 5)))) (not (= k 5))) :rule equiv_pos2)
        (step t3 (cl (= k 5)) :rule eq_reflexive)
        (step t4 (cl) :rule resolution :premises (a0 t1 t2 t3))";
    let cases: Vec<(&str, String, String)> = vec![
        (
            "B03",
            format!(
                "{X} (define-fun k () Int x) (define-fun h ((x Int)) Int k)
                (assert (= (h 5) x)) (assert (not (= x 5))) (check-sat)"
            ),
            resolve_x5.to_owned(),
        ),
        (
            "B04",
            format!(
                "{PAIR} (define-fun k ((y P)) Int (fst y))
                (define-fun h ((fst (-> P Int))) Int (k (mk a b)))
                (assert (not (= (h g) (g (mk a b))))) (check-sat)"
            ),
            "(assume a0 (not (= (h g) (g (mk a b)))))
            (step t1 (cl (= (g (mk a b)) (g (mk a b)))) :rule refl)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
        (
            "B06",
            format!(
                "{X} (assert (= (! x :named k) x)) (define-fun h ((x Int)) Int k)
                (assert (= (h 5) x)) (assert (not (= x 5))) (check-sat)"
            ),
            resolve_x5.to_owned(),
        ),
        (
            "B07",
            format!(
                "{X} (assert (= (! x :named k) x)) (define-fun h ((x Int)) Int k)
                (assert (= (h 5) x)) (assert (not (= x 5))) (check-sat)"
            ),
            "(assume d0 (= h (lambda ((x Int)) x)))
            (assume a1 (= (h 5) x))
            (assume a2 (not (= x 5)))
            (step t1 (cl (= 5 5)) :rule eq_reflexive)
            (step t2 (cl (= (h 5) ((lambda ((x Int)) x) 5))) :rule ho_cong :premises (d0 t1))
            (step t3 (cl (= ((lambda ((x Int)) x) 5) 5)) :rule beta_equiv)
            (step t4 (cl (= (h 5) 5)) :rule trans :premises (t2 t3))
            (step t5 (cl (= x (h 5))) :rule symm :premises (a1))
            (step t6 (cl (= x 5)) :rule trans :premises (t5 t4))
            (step t7 (cl) :rule resolution :premises (a2 t6))"
                .to_owned(),
        ),
        (
            "B10",
            format!(
                "{PAIR} (define-fun k ((y P)) Int (g y))
                (define-fun h ((g (-> P Int))) Int (k (mk a b)))
                (assert (not (= (h fst) a))) (check-sat)"
            ),
            "(assume a0 (not (= (h fst) a)))
            (step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
        (
            "B11",
            format!(
                "{PAIR} (define-fun k ((y P)) Int (g y))
                (define-fun h ((g (-> P Int))) Int (k (mk a b)))
                (assert (not (= (h oth) (oth (mk a b))))) (check-sat)"
            ),
            "(assume a0 (not (= (h oth) (oth (mk a b)))))
            (step t1 (cl (= (oth (mk a b)) (oth (mk a b)))) :rule refl)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
        (
            "B08",
            "(declare-fun p () Bool) (assert p) (reset-assertions) (assert (not p)) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "B09",
            "(declare-fun p () Bool) (check-sat-assuming (p)) (assert (not p)) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "Z01",
            "(declare-const p Bool) (push 1) (assert (and p (not p))) (pop 1) (check-sat)"
                .to_owned(),
            "(assume h (and p (not p)))
            (step t1 (cl p) :rule and :premises (h) :args (0))
            (step t2 (cl (not p)) :rule and :premises (h) :args (1))
            (step t3 (cl) :rule resolution :premises (t1 t2))"
                .to_owned(),
        ),
        (
            "S01",
            "(define-fun k () Int 5) (assert (exists ((k Int)) (not (= k 5)))) (check-sat)"
                .to_owned(),
            shadow_proof.to_owned(),
        ),
        (
            "S02",
            "(assert (= (! 5 :named k) 5)) (assert (exists ((k Int)) (not (= k 5)))) (check-sat)"
                .to_owned(),
            shadow_proof.to_owned(),
        ),
        (
            "Q01",
            "(declare-fun p () Bool) (assert p) (check-sat) (assert (not p)) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "Q02",
            "(declare-fun p () Bool) (assert p) (check-sat) (assert (not p))".to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "Q03",
            "(declare-fun p () Bool) (assert p) (exit) (assert (not p)) (check-sat)".to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "Q04",
            "(declare-fun p () Bool) (push 1) (assert (not p)) (pop 1) (assert p) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "Q05",
            "(declare-fun p () Bool) (assert p) (reset) (declare-fun p () Bool)
            (assert (not p)) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
    ];
    for (name, problem, proof) in &cases {
        let got = refutes(problem, proof);
        assert!(got.is_err(), "{name} was refuted: {problem}");
    }
}

/// A problem is one query: the assertions before its first `check-sat`, `check-sat-assuming` (with
/// its assumptions) or `exit`, or all of them without one. Scoping commands are refused, and so is
/// any command that changes the problem after the query ends.
#[test]
fn a_problem_is_one_query() {
    for command in [
        "(push 1)",
        "(pop 1)",
        "(push 0)",
        "(reset)",
        "(reset-assertions)",
    ] {
        let error = parse_error(
            &format!("(declare-fun p () Bool) {command} (assert p)"),
            true,
        );
        assert!(
            matches!(&error, Some(e) if e.contains("is not supported: a problem must be a single query")),
            "{command}: {error:?}"
        );
    }
    for end in ["(check-sat)", "(check-sat-assuming (p))", "(exit)"] {
        for after in [
            "(assert p)",
            "(check-sat)",
            "(check-sat-assuming (p))",
            "(declare-fun q () Bool)",
            "(declare-const q Bool)",
            "(define-fun q () Bool p)",
            "(declare-sort S 0)",
            "(define-sort S () Int)",
            "(declare-datatype D ((d)))",
            "(set-logic QF_UF)",
        ] {
            let problem = format!("(declare-fun p () Bool) {end} {after}");
            let error = parse_error(&problem, true);
            assert!(
                matches!(&error, Some(e) if e.contains("the query a proof refutes ends")),
                "{problem}: {error:?}"
            );
        }
    }
    // Commands that do not change the problem may follow the query.
    for after in [
        "(get-value (p))",
        "(get-model)",
        "(get-proof)",
        "(get-info :reason-unknown)",
        "(set-info :status unsat)",
        "(set-option :produce-models true)",
        "(echo \"done\")",
        "(exit)",
    ] {
        let problem =
            format!("(declare-fun p () Bool) (assert p) (assert (not p)) (check-sat) {after}");
        assert_eq!(parse_error(&problem, true), None, "{problem}");
        let proof =
            "(assume a0 p) (assume a1 (not p)) (step t1 (cl) :rule resolution :premises (a0 a1))";
        assert_eq!(refutes(&problem, proof), Ok(()), "{problem}");
    }
    // The assumptions of the query's `check-sat-assuming` are premises.
    let problem = "(declare-fun p () Bool) (assert p) (check-sat-assuming ((not p)))";
    let proof =
        "(assume a0 p) (assume a1 (not p)) (step t1 (cl) :rule resolution :premises (a0 a1))";
    assert_eq!(refutes(problem, proof), Ok(()));
    // Without any query command, every assertion is a premise (Carcara's rule tests rely on it).
    let problem = "(declare-fun p () Bool) (assert p) (assert (not p))";
    assert_eq!(refutes(problem, proof), Ok(()));
}

/// The names `define-fun` hygiene introduces (a renamed parameter, and the placeholder used while
/// its body is parsed) contain a backslash, which no lexed symbol does: a script cannot name them,
/// and the printer still writes a term that holds one.
#[test]
fn renamed_parameters_are_unforgeable_and_printable() {
    // In the ordinary reading `h` is defined by a premise, whose `lambda` binds the renamed
    // parameter (a `:named` term is a macro in both readings).
    let problem = format!(
        "{X} (assert (= (! x :named k) x)) (define-fun h ((x Int)) Int k) (assert (= (h 5) x))"
    );
    let mut pool = PrimitivePool::new();
    let premises = premises(&mut pool, &problem, false).expect("the problem parses");
    let printed: Vec<String> = premises.iter().map(|term| term.to_string()).collect();
    assert!(
        printed
            .iter()
            .any(|t| t.contains("(lambda ((|x\\param| Int)) x)")),
        "{printed:?}"
    );
    for forged in ["|x\\param|", "|x\\global|"] {
        let error = parse_error(&format!("{X} (assert (= {forged} 0))"), true);
        assert!(
            matches!(&error, Some(e) if e.contains("backslash")),
            "{forged}: {error:?}"
        );
    }
}

/// A local binding (a `define-fun` parameter, `let`, quantifier, `lambda`, `choice` or `match`
/// binder) shadows a built-in operator of the same name, as SMT-LIB reads it. Upstream looked the
/// operators up first, so each name below was the built-in inside its own binder (fix 38).
#[test]
fn local_bindings_shadow_builtin_operators() {
    // T6, T7: a `define-fun` parameter, in the macro reading.
    let t6 = "(define-fun h ((re.all RegLan)) Bool (str.in_re \"a\" re.all))";
    assert_reads_as(
        &format!("{t6} (assert (h (str.to_re \"a\"))) (assert (not (h re.none)))"),
        true,
        "(assert (str.in_re \"a\" (str.to_re \"a\"))) (assert (not (str.in_re \"a\" re.none)))",
    );
    assert_reads_as(
        "(define-fun h ((real.pi Real)) Bool (> real.pi 0.0)) (assert (h 1.0))",
        true,
        "(assert (> 1.0 0.0))",
    );
    // ... and in the ordinary reading, where the parameter is the defining `lambda`'s.
    assert!(reads_up_to_bound_names(
        &format!("{t6} (assert (h re.none))"),
        false,
        "(declare-fun h (RegLan) Bool) (assert (= h (lambda ((r RegLan)) (str.in_re \"a\" r))))
        (assert (h re.none))",
    ));

    let s = "(declare-const s String)";
    let shadowed = [
        // T9: `let`.
        (
            format!("{s} (assert (not (let ((re.all re.none)) (str.in_re s re.all))))"),
            format!("{s} (assert (not (let ((r re.none)) (str.in_re s r))))"),
            format!("{s} (assert (not (let ((r re.none)) (str.in_re s re.all))))"),
        ),
        // T8: a quantifier.
        (
            "(assert (not (forall ((re.all RegLan)) (str.in_re \"a\" re.all))))".to_owned(),
            "(assert (not (forall ((r RegLan)) (str.in_re \"a\" r))))".to_owned(),
            "(assert (not (forall ((r RegLan)) (str.in_re \"a\" re.all))))".to_owned(),
        ),
        // A quantified function named like an operator, applied.
        (
            "(assert (forall ((abs (-> Int Int))) (> (abs 3) 0)))".to_owned(),
            "(assert (forall ((f (-> Int Int))) (> (f 3) 0)))".to_owned(),
            "(assert (forall ((f (-> Int Int))) (> (abs 3) 0)))".to_owned(),
        ),
        // `choice`.
        (
            "(assert (= (choice ((real.pi Real)) (> real.pi 4.0)) 5.0))".to_owned(),
            "(assert (= (choice ((r Real)) (> r 4.0)) 5.0))".to_owned(),
            "(assert (= (choice ((r Real)) (> real.pi 4.0)) 5.0))".to_owned(),
        ),
        // `lambda`.
        (
            "(assert (= (lambda ((re.none RegLan)) (str.in_re \"a\" re.none))
                (lambda ((r RegLan)) true)))"
                .to_owned(),
            "(assert (= (lambda ((q RegLan)) (str.in_re \"a\" q)) (lambda ((r RegLan)) true)))"
                .to_owned(),
            "(assert (= (lambda ((q RegLan)) (str.in_re \"a\" re.none))
                (lambda ((r RegLan)) true)))"
                .to_owned(),
        ),
    ];
    for (problem, renamed, builtin) in &shadowed {
        for apply_function_defs in [false, true] {
            assert!(
                reads_up_to_bound_names(problem, apply_function_defs, renamed),
                "{problem} is not read as {renamed}"
            );
            assert!(
                !reads_up_to_bound_names(problem, apply_function_defs, builtin),
                "anti-vacuity: {problem} must not read as {builtin}"
            );
        }
    }
    // A `match` case (`alpha_equiv` compares a case's variables by name, so the body is read
    // directly): the case's `re.all` is its pattern variable.
    let mut pool = PrimitivePool::new();
    let problem = "(declare-datatype L ((nil) (cons (hd RegLan) (tl L)))) (declare-fun l () L)
        (assert (match l ((nil false) ((cons re.all t) (str.in_re \"a\" re.all)))))";
    let read = premises(&mut pool, problem, true).expect("the problem parses");
    let body = match read.first().map(|t| t.as_ref()) {
        Some(Term::Match(_, cases)) => cases[1].body.clone(),
        other => panic!("not a match: {other:?}"),
    };
    let reads_the_variable = matches!(
        body.as_ref(),
        Term::Op(Operator::StrInRe, args) if args[1].as_var() == Some("re.all")
    );
    assert!(reads_the_variable, "{body:?}");

    // Outside its binder the name is the built-in again.
    assert!(reads_up_to_bound_names(
        &format!("{s} (assert (and (let ((re.all re.none)) true) (str.in_re s re.all)))"),
        true,
        &format!("{s} (assert (and (let ((r re.none)) true) (str.in_re s re.all)))"),
    ));
}

/// A local sort parameter (`define-sort`, a `par` datatype) shadows a built-in sort of the same
/// name, and takes no arguments. Upstream read `Bool` in S6's `(par (Bool) ((mk (val Bool))))` as
/// the built-in, so `val` returned `Bool` at every instance (fix 38).
#[test]
fn sort_parameters_shadow_builtin_sorts() {
    let boxes = "(declare-datatypes ((Box 1)) ((par (Bool) ((mk (val Bool))))))";
    // `(val a)` is an `Int` for an `(Box Int)`, and a `Bool` for a `(Box Bool)`.
    for apply_function_defs in [false, true] {
        assert_eq!(
            parse_error(
                &format!(
                    "{boxes} (declare-const a (Box Int)) (declare-const b (Box Bool))
                    (assert (= (val a) 3)) (assert (val b))"
                ),
                apply_function_defs
            ),
            None
        );
        assert!(parse_error(
            &format!("{boxes} (declare-const a (Box Int)) (assert (= (val a) true))"),
            apply_function_defs
        )
        .is_some_and(|e| e.contains("expected")));
    }
    // S1: a `define-sort` parameter.
    assert_reads_as(
        "(define-sort S (Bool) Bool) (declare-const a (S Int)) (assert (= a 3))",
        true,
        "(declare-const a Int) (assert (= a 3))",
    );
    assert_reads_as(
        "(define-sort S (Int) (Array Int Bool)) (declare-const a (S Real)) (assert (select a 0.0))",
        true,
        "(declare-const a (Array Real Bool)) (assert (select a 0.0))",
    );
    // An assertion must be a formula: upstream took S4's `(val a)`, an `Int` under its reading,
    // as a premise.
    for problem in [
        "(declare-datatypes ((Box 1)) ((par (Int) ((mk (val Int)))))) (declare-const a (Box Int))
        (assert (val a))",
        "(declare-const x Int) (assert x)",
        "(declare-const x Int) (check-sat-assuming (x))",
    ] {
        assert!(
            parse_error(problem, true).is_some_and(|e| e.contains("expected 'Bool'")),
            "{problem}: {:?}",
            parse_error(problem, true)
        );
    }
    // A sort parameter takes no arguments (upstream dropped them).
    for problem in [
        "(define-sort S (X) (X Int)) (declare-const a (S Int))",
        "(define-sort S (Array) (Array Int Int)) (declare-const a (S Int))",
    ] {
        assert!(
            parse_error(problem, true).is_some_and(|e| e.contains("expected 0 arguments")),
            "{problem}: {:?}",
            parse_error(problem, true)
        );
    }
}

/// Each name the problem declares or defines is new: not a built-in operator (which the parser
/// keeps reading as the built-in), not a name already declared or defined (a definition takes
/// precedence over every declaration of its name, and a constant declared twice is one
/// `Term::Var`), and likewise for sorts (fix 38). Same-named datatype symbols are judged by
/// `check_global_symbol`, in `rules/datatypes.rs`.
#[test]
fn names_in_use_are_refused_in_the_problem() {
    let builtin = [
        "(declare-const real.pi Real) (assert (= real.pi 1.0))",
        "(declare-fun re.all () RegLan)",
        "(declare-const true Bool)",
        "(declare-fun abs (Int) Int)",
        "(declare-const const Int)",
        "(define-fun true () Bool false)",
        "(declare-const b Bool) (assert (! b :named re.none))",
        "(declare-const b Bool) (assert (or b (! false :named true)))",
        "(declare-datatype D ((true) (other)))",
        "(declare-datatype D ((mk (abs Int))))",
        // Added in Clean: AY's r18 cross-review. A built-in's name declared at the built-in's
        // own arity, which Clean 6a916983 accepted and then read as the built-in at every use,
        // and the quoted `|false|`, which is the symbol `false`.
        "(declare-fun + (Int Int) Int) (assert (= (+ 1 1) 7))",
        "(declare-fun and (Bool Bool) Bool) (assert (not (and true true)))",
        "(declare-fun ite (Bool Int Int) Int) (assert (= (ite true 0 1) 5))",
        "(define-fun = ((a Int) (b Int)) Bool false) (assert (not (= 0 0)))",
        "(declare-datatype D ((or (oa Bool) (ob Bool))))",
        "(declare-const |false| Bool) (assert |false|)",
    ];
    for problem in builtin {
        for apply_function_defs in [false, true] {
            let error = parse_error(problem, apply_function_defs);
            assert!(
                error
                    .as_deref()
                    .is_some_and(|e| e.contains("is a built-in operator")),
                "{problem} ({apply_function_defs}): {error:?}"
            );
        }
    }
    let x = "(declare-fun x () Int) (declare-fun y () Int)";
    let in_use = [
        // R1, R1b, R1f: a label reusing a declared name, before or after it.
        format!("{x} (assert (= y (! 5 :named x)))"),
        "(declare-fun y () Int) (assert (= y (! 5 :named x))) (declare-fun x () Int)".to_owned(),
        format!("{x} (assert (! (= y 5) :named a)) (assert (= y (! 5 :named x)))"),
        // A label used twice, and one reusing a definition's name (R6, R7).
        format!("{x} (assert (= y (! x :named k))) (assert (= y (! 5 :named k)))"),
        format!("{x} (define-fun k () Int x) (assert (= x (! 5 :named k)))"),
        // R1c, R3: a `define-fun` and a declaration of the same name, in either order.
        "(declare-fun x () Int) (define-fun x () Int 5)".to_owned(),
        "(define-fun x () Int 5) (declare-fun x () Int)".to_owned(),
        // R8, R10: a constant declared twice.
        "(declare-const x Int) (define-fun k () Int x) (declare-const x Int)".to_owned(),
        "(declare-const x Int) (declare-const x Int)".to_owned(),
        "(declare-fun f (Int) Int) (declare-fun f (Bool) Int)".to_owned(),
        // R16: a label in `check-sat-assuming`.
        format!("{x} (check-sat-assuming ((! (= y 5) :named x)))"),
    ];
    for problem in &in_use {
        for apply_function_defs in [false, true] {
            let error = parse_error(problem, apply_function_defs);
            assert!(
                error
                    .as_deref()
                    .is_some_and(|e| e.contains("is already declared or defined")),
                "{problem} ({apply_function_defs}): {error:?}"
            );
        }
    }
    let sorts = [
        ("(declare-sort Int 0)", "is a built-in sort"),
        ("(define-sort Bool () Int)", "is a built-in sort"),
        (
            "(declare-datatype Int ((mkI (fi Bool))))",
            "is a built-in sort",
        ),
        (
            "(declare-datatypes ((Set 0)) (((e))))",
            "is a built-in sort",
        ),
        (
            "(declare-sort S 0) (declare-sort S 0)",
            "is already declared or defined",
        ),
        (
            "(declare-sort S 0) (define-sort S () Int)",
            "is already declared or defined",
        ),
        (
            "(define-sort S () Int) (declare-sort S 1)",
            "is already declared or defined",
        ),
    ];
    for (problem, reason) in sorts {
        let error = parse_error(problem, true);
        assert!(
            error.as_deref().is_some_and(|e| e.contains(reason)),
            "{problem}: {error:?}"
        );
    }

    // Fresh names are accepted, labels used as terms included, and a binder may still shadow a
    // declared or defined name.
    let accepted = [
        format!("{x} (assert (= y (! 5 :named five))) (assert (not (= x five)))"),
        format!("{x} (define-fun k () Int x) (assert (forall ((k Int) (x Int)) (> k x)))"),
        "(declare-sort S 0) (define-sort T () S) (declare-const a T)".to_owned(),
        "(declare-const p Bool) (assert (! p :named dn0)) (assert (! (not p) :named dn1))"
            .to_owned(),
    ];
    for problem in &accepted {
        for apply_function_defs in [false, true] {
            assert_eq!(parse_error(problem, apply_function_defs), None, "{problem}");
        }
    }
}

/// A command the parser does not read is refused wherever it appears: it may end the query (AY's
/// `check-sat-using`) or change the assertions in a way the parser cannot see. So is a quoted
/// spelling of a command the parser reads, and a command that is not a symbol (fix 37).
#[test]
fn unknown_commands_are_refused() {
    for command in [
        "(check-sat-using smt)",
        "(check-sat-using (then simplify smt))",
        "(assert-soft p)",
        "(assert-not p)",
        "(define-const q Bool p)",
        "(declare-var q Bool)",
        "(apply simplify)",
        "(simplify p)",
        "(eval p)",
        "(query p)",
        "(declare-rare-rule r ((x Bool)) :args (x) :conclusion (= x x))",
    ] {
        let problem = format!("(declare-fun p () Bool) (assert p) {command} (assert (not p))");
        let error = parse_error(&problem, true);
        assert!(
            error
                .as_deref()
                .is_some_and(|e| e.contains("is not a command this checker reads")),
            "{command}: {error:?}"
        );
    }
    for command in ["(|assert| (not p))", "(|declare-fun| q () Bool)"] {
        let problem = format!("(declare-fun p () Bool) (assert p) {command}");
        let error = parse_error(&problem, true);
        assert!(
            error
                .as_deref()
                .is_some_and(|e| e.contains("is not a command this checker reads")),
            "{command}: {error:?}"
        );
    }
    for command in ["()", "(:named p)", "((assert p))", "(\"assert\" p)"] {
        let problem = format!("(declare-fun p () Bool) {command}");
        let error = parse_error(&problem, true);
        assert!(
            error
                .as_deref()
                .is_some_and(|e| e.contains("unexpected token")),
            "{command}: {error:?}"
        );
    }
}

/// The second adversarial review's refutations of satisfiable problems through a built-in name
/// shadowed by a binder (T6, T7, T8, T9, T1), a sort parameter shadowing a built-in sort (S6,
/// S1), a reused name (R1, R1b, R1c, R1e, R1f, R3, R5, R8, R10, R13), AY's `check-sat-using`
/// (U1, U2) and a chain of definitions (A1, A2). Each was accepted as complete before these
/// fixes (A1 and A2 are closed by fix 36, U1 and U2 by fix 37, the others by fix 38); each must
/// now be refused.
#[test]
fn refutations_through_shadowed_or_reused_names_are_refused() {
    let p_not_p =
        "(assume a0 p) (assume a1 (not p)) (step t1 (cl) :rule resolution :premises (a0 a1))";
    let x_is_5 = "(assume a1 (not (= x 5)))
        (step t1 (cl (= x 5)) :rule refl)
        (step t2 (cl) :rule resolution :premises (a1 t1))";
    let distinct_false = |terms: &str| {
        format!(
            "(assume a0 (distinct {terms}))
            (step t1 (cl (= (distinct {terms}) false)) :rule distinct_elim)
            (step t2 (cl (not (= (distinct {terms}) false)) (not (distinct {terms})) false)
                :rule equiv_pos2)
            (step t3 (cl (not false)) :rule false)
            (step t4 (cl) :rule resolution :premises (a0 t1 t2 t3))"
        )
    };
    let cases: Vec<(&str, String, String)> = vec![
        (
            "T6",
            "(define-fun h ((re.all RegLan)) Bool (str.in_re \"a\" re.all))
            (assert (h (str.to_re \"a\"))) (assert (not (h re.none))) (check-sat)"
                .to_owned(),
            "(assume a0 (h (str.to_re \"a\"))) (assume a1 (not (h re.none)))
            (step t1 (cl) :rule resolution :premises (a0 a1))"
                .to_owned(),
        ),
        (
            "T7",
            "(define-fun h ((real.pi Real)) Bool (> real.pi 0.0))
            (assert (h 1.0)) (assert (not (h (- 1.0)))) (check-sat)"
                .to_owned(),
            "(assume a0 (h 1.0)) (assume a1 (not (h (- 1.0))))
            (step t1 (cl) :rule resolution :premises (a0 a1))"
                .to_owned(),
        ),
        (
            "T8",
            "(assert (str.in_re \"a\" re.all))
            (assert (not (forall ((re.all RegLan)) (str.in_re \"a\" re.all)))) (check-sat)"
                .to_owned(),
            "(assume a0 (str.in_re \"a\" re.all))
            (assume a1 (not (forall ((re.all RegLan)) (str.in_re \"a\" re.all))))
            (step t1 (cl (= (forall ((re.all RegLan)) (str.in_re \"a\" re.all))
                (str.in_re \"a\" re.all))) :rule qnt_rm_unused)
            (step t2 (cl (not (= (forall ((re.all RegLan)) (str.in_re \"a\" re.all))
                (str.in_re \"a\" re.all))) (forall ((re.all RegLan)) (str.in_re \"a\" re.all))
                (not (str.in_re \"a\" re.all))) :rule equiv_pos1)
            (step t3 (cl) :rule resolution :premises (a0 a1 t1 t2))"
                .to_owned(),
        ),
        (
            "T9",
            "(declare-const s String) (assert (str.in_re s re.all))
            (assert (not (let ((re.all re.none)) (str.in_re s re.all)))) (check-sat)"
                .to_owned(),
            "(assume a0 (str.in_re s re.all))
            (assume a1 (not (let ((re.all re.none)) (str.in_re s re.all))))
            (anchor :step t3 :args ((:= (re.all RegLan) re.none)))
            (step t3.t1 (cl (= (str.in_re s re.all) (str.in_re s re.all))) :rule refl)
            (step t3 (cl (= (let ((re.all re.none)) (str.in_re s re.all)) (str.in_re s re.all)))
                :rule let)
            (step t4 (cl (not (= (let ((re.all re.none)) (str.in_re s re.all))
                (str.in_re s re.all))) (let ((re.all re.none)) (str.in_re s re.all))
                (not (str.in_re s re.all))) :rule equiv_pos1)
            (step t5 (cl) :rule resolution :premises (a0 a1 t3 t4))"
                .to_owned(),
        ),
        (
            "T1",
            "(define-fun h ((true Bool)) Bool true) (assert (not (h false))) (check-sat)"
                .to_owned(),
            "(assume a0 (not (h false))) (step t1 (cl true) :rule true)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
        (
            "S6",
            "(declare-datatypes ((Box 1)) ((par (Bool) ((mk (val Bool))))))
            (declare-const a (Box Int)) (declare-const b (Box Int)) (declare-const c (Box Int))
            (assert (distinct (val a) (val b) (val c))) (check-sat)"
                .to_owned(),
            distinct_false("(val a) (val b) (val c)"),
        ),
        (
            "S1",
            "(define-sort S (Bool) Bool) (declare-const a (S Int)) (declare-const b (S Int))
            (declare-const c (S Int)) (assert (distinct a b c)) (check-sat)"
                .to_owned(),
            distinct_false("a b c"),
        ),
        (
            "R1",
            "(declare-fun x () Int) (declare-fun y () Int) (assert (= y (! 5 :named x)))
            (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R1b",
            "(declare-fun y () Int) (assert (= y (! 5 :named x))) (declare-fun x () Int)
            (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R1c",
            "(declare-fun x () Int) (define-fun x () Int 5) (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R1e",
            "(declare-const x Int) (assert (! (= 5 5) :named q)) (assert (! (> 5 4) :named r))
            (assert (= (! 5 :named x) 5)) (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R1f",
            "(declare-const x Int) (declare-const y Int) (assert (! (= y 5) :named a))
            (assert (= y (! 5 :named x))) (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R3",
            "(define-fun x () Int 5) (declare-fun x () Int) (assert (not (= x 5))) (check-sat)"
                .to_owned(),
            x_is_5.to_owned(),
        ),
        (
            "R5",
            "(declare-const b Bool) (assert (or b (! false :named true))) (assert b)
            (assert true) (check-sat)"
                .to_owned(),
            "(assume a2 true) (step t1 (cl (not false)) :rule false)
            (step t2 (cl) :rule resolution :premises (a2 t1))"
                .to_owned(),
        ),
        (
            "R8",
            "(declare-const x Int) (define-fun k () Int x) (declare-const x Int)
            (assert (not (= k x))) (check-sat)"
                .to_owned(),
            "(assume a0 (not (= k x))) (step t1 (cl (= k x)) :rule refl)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
        (
            "R10",
            "(declare-const x Int) (declare-const y Int) (assert (= y x)) (declare-const x Int)
            (assert (not (= y x))) (check-sat)"
                .to_owned(),
            "(assume a0 (= y x)) (assume a1 (not (= y x)))
            (step t2 (cl) :rule resolution :premises (a0 a1))"
                .to_owned(),
        ),
        (
            "R13",
            "(declare-const b Bool) (assert (or b (! true :named false))) (assert (not false))
            (assert (not b)) (check-sat)"
                .to_owned(),
            "(assume a1 (not false)) (step t1 (cl true) :rule true)
            (step t2 (cl) :rule resolution :premises (a1 t1))"
                .to_owned(),
        ),
        (
            "U1",
            "(declare-const p Bool) (assert p) (check-sat-using smt) (assert (not p)) (check-sat)"
                .to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "U2",
            "(declare-const p Bool) (assert p) (check-sat-using smt) (assert (not p))".to_owned(),
            p_not_p.to_owned(),
        ),
        (
            "A1",
            "(declare-fun x () Int) (define-fun k () Int x) (define-fun h ((x Int)) Int k)
            (define-fun g ((x Int)) Int (h x)) (assert (= (g 5) x)) (assert (not (= x 5)))
            (check-sat)"
                .to_owned(),
            "(assume a0 (= (g 5) x)) (assume a1 (not (= x 5)))
            (step t1 (cl (= x 5)) :rule symm :premises (a0))
            (step t2 (cl) :rule resolution :premises (a1 t1))"
                .to_owned(),
        ),
        (
            "A2",
            "(declare-datatype D ((c) (d))) (define-fun k () D c) (define-fun h ((c D)) D k)
            (assert (not (= (h d) d))) (check-sat)"
                .to_owned(),
            "(assume a0 (not (= (h d) d))) (step t1 (cl (= d d)) :rule refl)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
                .to_owned(),
        ),
    ];
    for (name, problem, proof) in &cases {
        assert!(
            refutes(problem, proof).is_err(),
            "{name} was refuted: {problem}"
        );
    }

    // Positive controls: the same refutations of the same shapes with fresh names verify.
    let controls: Vec<(&str, String, String)> = vec![
        (
            "T9 with the built-in",
            "(declare-const s String) (assert (not (str.in_re s re.all)))
            (assert (str.in_re s re.all))"
                .to_owned(),
            "(assume a0 (str.in_re s re.all)) (assume a1 (not (str.in_re s re.all)))
            (step t1 (cl) :rule resolution :premises (a0 a1))"
                .to_owned(),
        ),
        (
            "S6 at Bool",
            "(declare-datatypes ((Box 1)) ((par (Bool) ((mk (val Bool))))))
            (declare-const a (Box Bool)) (declare-const b (Box Bool)) (declare-const c (Box Bool))
            (assert (distinct (val a) (val b) (val c))) (check-sat)"
                .to_owned(),
            distinct_false("(val a) (val b) (val c)"),
        ),
        (
            "R1 with a fresh label",
            "(declare-fun x () Int) (declare-fun y () Int) (assert (= y (! 5 :named five)))
            (assert (not (= five 5))) (check-sat)"
                .to_owned(),
            "(assume a1 (not (= 5 5))) (step t1 (cl (= 5 5)) :rule refl)
            (step t2 (cl) :rule resolution :premises (a1 t1))"
                .to_owned(),
        ),
    ];
    for (name, problem, proof) in &controls {
        assert_eq!(refutes(problem, proof), Ok(()), "{name}: {problem}");
    }
}

/// `define-fun-rec` and `define-funs-rec` are refused in the problem (fix 39). SMT-LIB reads a
/// recursive definition as a declaration and a universally quantified equation, an axiom that
/// need not be consistent, and the third review's R01 and R03 below were refuted through it,
/// while AY 0.27.0 (which unfolds such a definition lazily) answers `sat` for both, and for the
/// `define-funs-rec` group.
#[test]
fn recursive_definitions_are_refused() {
    let r01 = "(define-fun-rec f ((x Int)) Int (+ (f x) 1)) (check-sat)";
    let r01_proof = "(assume a0 (forall ((x Int)) (= (f x) (+ (f x) 1))))
        (step t1 (cl (or (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1))))
            :rule forall_inst :args (0))
        (step t2 (cl (not (forall ((x Int)) (= (f x) (+ (f x) 1)))) (= (f 0) (+ (f 0) 1)))
            :rule or :premises (t1))
        (step t3 (cl (= (f 0) (+ (f 0) 1))) :rule resolution :premises (t2 a0))
        (step t4 (cl (not (= (f 0) (+ (f 0) 1)))) :rule la_generic :args (1))
        (step t5 (cl) :rule resolution :premises (t3 t4))";
    let r03 = "(define-fun-rec c () Int (+ c 1)) (check-sat)";
    let r03_proof = "(assume a0 (= c (+ c 1)))
        (step t1 (cl (not (= c (+ c 1)))) :rule la_generic :args (1))
        (step t2 (cl) :rule resolution :premises (a0 t1))";
    let group = "(define-funs-rec ((f ((n Int)) Int) (g ((n Int)) Int)) ((+ (g n) 1) (f n)))";
    for problem in [
        r01,
        r03,
        group,
        // Consistent definitions are refused as well.
        "(define-fun-rec sumr ((x Int)) Int (+ x (ite (> x 0) (sumr (- x 1)) 0)))",
        "(define-fun-rec five () Int 5)",
        "(declare-fun p () Bool) (define-fun-rec q () Bool p) (assert q)",
        "(declare-fun p () Bool) (assert p) (check-sat) (define-fun-rec q () Bool p)",
    ] {
        for apply_function_defs in [false, true] {
            let error = parse_error(problem, apply_function_defs);
            assert!(
                error
                    .as_deref()
                    .is_some_and(|e| e.contains("is not supported: a recursive definition")),
                "{problem} ({apply_function_defs}): {error:?}"
            );
        }
    }
    assert!(refutes(r01, r01_proof).is_err(), "R01 was refuted");
    assert!(refutes(r03, r03_proof).is_err(), "R03 was refuted");
    // The same refutations of the axioms written out verify: the refusal is not a misreading.
    let axiom = "(declare-fun f (Int) Int) (assert (forall ((x Int)) (= (f x) (+ (f x) 1))))";
    assert_eq!(refutes(axiom, r01_proof), Ok(()));
    let axiom = "(declare-fun c () Int) (assert (= c (+ c 1)))";
    assert_eq!(refutes(axiom, r03_proof), Ok(()));
}

/// The lexer reads SMT-LIB's lexicon where it decides what a problem says (fix 40). A comment ends
/// at CR as well as LF; whitespace is space, tab, LF and CR only; a `.` or `/` is part of a number
/// only when a digit follows; and a number the lexer reads where SMT-LIB reads a symbol in scope
/// (`-5` with `|-5|` declared, `1/2` with `/2` declared) is refused.
#[test]
fn problems_are_lexed_as_smtlib() {
    let ab = "(declare-const a Bool) (declare-const b Bool)";
    // L01: upstream read up to the LF, dropping `b)) (assert (or b`.
    assert_reads_as(
        &format!("{ab} (assert (or a ; c\r b)) (assert (or b\n a))"),
        false,
        &format!("{ab} (assert (or a b)) (assert (or b a))"),
    );
    assert_reads_as(
        &format!("{ab} ; c\r\n(assert a) ; d\r(assert b)"),
        false,
        &format!("{ab} (assert a) (assert b)"),
    );
    // Other Unicode white space is refused outside a comment, string or quoted symbol.
    for space in [
        '\u{0b}', '\u{0c}', '\u{85}', '\u{a0}', '\u{2028}', '\u{3000}',
    ] {
        let problem = format!("{ab}{space}(assert a)");
        let error = parse_error(&problem, false);
        assert!(
            error
                .as_deref()
                .is_some_and(|e| e.contains("unexpected character")),
            "{problem:?}: {error:?}"
        );
        let inside = format!("{ab} ; {space}\n(assert (= \"{space}\" \"{space}\")) (assert |a|)");
        assert_eq!(parse_error(&inside, false), None, "{inside:?}");
    }
    // `1.` and `1.x` are the numeral `1` followed by a symbol; `1/x` made upstream panic.
    assert_reads_as(
        "(set-logic QF_LRA) (declare-fun . () Real) (assert (not (= 1. 1.0)))",
        false,
        "(set-logic QF_LRA) (declare-fun . () Real) (assert (not (= 1 . 1.0)))",
    );
    assert_reads_as(
        "(set-logic QF_LRA) (declare-fun .x () Real) (assert (= 2.x 2.5))",
        false,
        "(set-logic QF_LRA) (declare-fun .x () Real) (assert (= 2 .x 2.5))",
    );
    assert_reads_as(
        "(declare-fun /x () Int) (assert (= 1/x 1))",
        false,
        "(declare-fun /x () Int) (assert (= 1 /x 1))",
    );
    // A number is refused where SMT-LIB reads a symbol declared, defined or bound there.
    for problem in [
        "(declare-const |-5| Int) (assert (= -5 3))",
        "(declare-const |-5abc| Int) (declare-const abc Int) (assert (= (+ 0 -5abc) 7))",
        "(declare-fun /2 () Real) (declare-fun x () Real) (assert (= x 1/2))",
        "(set-logic QF_LRA) (declare-fun /2x () Real) (declare-fun x () Real)
        (assert (= (+ 1/2x) 1.0))",
        "(declare-const |-1/2| Real) (assert (= -1/2 0.0))",
        "(declare-const y Int) (assert (let ((|-5| y)) (= -5 3)))",
        "(assert (forall ((|-5| Int)) (> -5 0)))",
        "(declare-datatype D ((|-1|) (c))) (assert (= -1 -1))",
        "(define-fun |-1| () Int 1) (assert (= -1 1))",
        "(declare-const p Int) (assert (= (! p :named |-1|) -1))",
        "(define-fun h ((|-1| Int)) Bool (> -1 0)) (assert (h 5))",
    ] {
        for apply_function_defs in [false, true] {
            let error = parse_error(problem, apply_function_defs);
            assert!(
                error
                    .as_deref()
                    .is_some_and(|e| e
                        .contains("is a declared or bound symbol, which this checker would read")),
                "{problem} ({apply_function_defs}): {error:?}"
            );
        }
    }
    // Such a symbol may be declared and used quoted (AY's printer quotes it), numbers with no
    // such symbol in scope keep their reading, and symbols that only start like a number are
    // symbols.
    for problem in [
        "(declare-const |-5| Int) (assert (= |-5| 3))",
        "(declare-fun /2 () Real) (declare-fun x () Real) (assert (= x /2))",
        "(declare-const x Int) (assert (= x -5)) (assert (> x (- 6)))",
        "(set-logic QF_LRA) (declare-const x Real) (assert (= x 1/2)) (assert (= x -1.5))",
        "(declare-const -x Int) (declare-const /x Int) (declare-const |.5| Int)
        (declare-const +5 Int) (declare-const |a-5| Int) (assert (= -x /x .5 +5 a-5))",
    ] {
        for apply_function_defs in [false, true] {
            assert_eq!(parse_error(problem, apply_function_defs), None, "{problem}");
        }
    }
    // A proof keeps Carcara's numbers: its terms are judged as written.
    let proof = "(assume a0 (= |-1| 3)) (assume a1 (not (= |-1| 3)))
        (step t1 (cl (not (= 1 (- 1)))) :rule la_generic :args (-1))
        (step t2 (cl) :rule resolution :premises (a0 a1))";
    let parsed = parser::parse_instance(
        "(declare-const |-1| Int) (assert (= |-1| 3)) (assert (not (= |-1| 3)))",
        proof,
        None,
        parser::Config::new(),
    );
    assert!(parsed.is_ok(), "{:?}", parsed.err());

    // The third review's L01 and this lane's L02, L04, L05 and L06: refutations of satisfiable
    // scripts that origin/main certified, each now read correctly (so the proof fails) or
    // refused.
    let cases = [
        (
            "L01",
            format!("{ab} (assert (or a ; c\r b)) (assert (or b\n a)) (assert (not a))"),
            "(assume h1 (or a a)) (assume h2 (not a))
            (step t1 (cl a a) :rule or :premises (h1))
            (step t2 (cl a) :rule contraction :premises (t1))
            (step t3 (cl) :rule resolution :premises (t2 h2))",
        ),
        (
            "L02",
            "(set-logic QF_LIA) (declare-const |-5| Int) (assert (= -5 3))".to_owned(),
            "(assume a0 (= -5 3)) (step t1 (cl (not (= -5 3))) :rule la_generic :args (1))
            (step t2 (cl) :rule resolution :premises (a0 t1))",
        ),
        (
            "L04",
            "(set-logic QF_LRA) (declare-fun /2 () Real) (declare-fun x () Real)
            (assert (= x 1/2)) (assert (= x 1))"
                .to_owned(),
            "(assume a0 (= x 1/2)) (assume a1 (= x 1.0))
            (step t1 (cl (not (= x 1/2)) (not (= x 1.0))) :rule la_generic :args (1 (- 1)))
            (step t2 (cl) :rule resolution :premises (a0 a1 t1))",
        ),
        (
            "L05",
            "(set-logic QF_LRA) (declare-fun . () Real) (assert (not (= 1. 1.0)))".to_owned(),
            "(assume a0 (not (= 1.0 1.0))) (step t1 (cl (= 1.0 1.0)) :rule refl)
            (step t2 (cl) :rule resolution :premises (a0 t1))",
        ),
        (
            "L06",
            "(set-logic QF_LIA) (declare-const |-5abc| Int) (declare-const abc Int)
            (assert (= (+ 0 -5abc) 7)) (assert (= abc 0))"
                .to_owned(),
            "(assume a0 (= (+ 0 -5 abc) 7)) (assume a1 (= abc 0))
            (step t1 (cl (not (= (+ 0 -5 abc) 7)) (not (= abc 0))) :rule la_generic
                :args (1 (- 1)))
            (step t2 (cl) :rule resolution :premises (a0 a1 t1))",
        ),
    ];
    for (name, problem, proof) in &cases {
        assert!(
            refutes(problem, proof).is_err(),
            "{name} was refuted: {problem:?}"
        );
    }
    // Positive controls: the same shapes read as SMT-LIB reads them.
    let controls = [
        (
            format!("{ab} (assert (not a)) ; c\r(assert a)"),
            "(assume h1 a) (assume h2 (not a)) (step t1 (cl) :rule resolution :premises (h1 h2))",
        ),
        (
            "(declare-const |-5| Int) (assert (= |-5| 3)) (assert (not (= |-5| 3)))".to_owned(),
            "(assume a0 (= |-5| 3)) (assume a1 (not (= |-5| 3)))
            (step t1 (cl) :rule resolution :premises (a0 a1))",
        ),
        (
            "(set-logic QF_LRA) (declare-fun x () Real) (assert (= x 1/2)) (assert (= x -1.5))"
                .to_owned(),
            "(assume a0 (= x 1/2)) (assume a1 (= x -1.5))
            (step t1 (cl (not (= x 1/2)) (not (= x -1.5))) :rule la_generic :args (1 (- 1)))
            (step t2 (cl) :rule resolution :premises (a0 a1 t1))",
        ),
    ];
    for (problem, proof) in &controls {
        assert_eq!(refutes(problem, proof), Ok(()), "{problem:?}");
    }
}

/// A tester `(_ is C)` names a constructor `C` of its single argument's datatype, and `C` is that
/// global constructor, not a local binding of its name. Upstream accepted any term and any
/// arguments (see DOWNSTREAM.md, "Also hardened").
#[test]
fn testers_name_a_constructor_of_their_argument() {
    let decls = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
        (declare-datatype Q ((q1) (q2))) (declare-const p P) (declare-const q Q)";
    for assertion in [
        "(assert ((_ is mk) p))",
        "(assert ((_ is other) p))",
        "(assert ((_ is q2) q))",
        "(assert (forall ((r P)) (or ((_ is mk) r) ((_ is other) r))))",
        "(define-fun h ((r P)) Bool ((_ is other) r)) (assert (h p))",
    ] {
        for apply_function_defs in [false, true] {
            let problem = format!("{decls} {assertion}");
            assert_eq!(
                parse_error(&problem, apply_function_defs),
                None,
                "{problem}"
            );
        }
    }
    for (assertion, reason) in [
        ("(assert ((_ is fst) p))", "does not name a constructor"),
        ("(assert ((_ is q1) p))", "does not name a constructor"),
        ("(assert ((_ is mk) q))", "does not name a constructor"),
        ("(assert ((_ is (fst p)) p))", "does not name a constructor"),
        (
            "(define-fun h ((mk Int)) Bool ((_ is mk) p)) (assert (h 1))",
            "does not name a constructor",
        ),
        (
            "(assert (forall ((mk P)) ((_ is mk) p)))",
            "does not name a constructor",
        ),
        ("(assert ((_ is mk) 5))", "expected datatype sort"),
        ("(assert ((_ is mk) p p))", "expected 1 arguments"),
    ] {
        for apply_function_defs in [false, true] {
            let problem = format!("{decls} {assertion}");
            let error = parse_error(&problem, apply_function_defs);
            assert!(
                error.as_deref().is_some_and(|e| e.contains(reason)),
                "{problem} ({apply_function_defs}): {error:?}"
            );
        }
    }
}

/// Runs `f` on a 1 GiB stack, as Clean's adapter checks a certificate: an unoptimized parser takes
/// about ten times the 2.3 KiB a release build takes per level of nesting.
fn on_the_checkers_stack(f: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(scope, f)
            .unwrap()
            .join()
            .unwrap();
    });
}

/// Terms and sorts are read up to `MAX_WRITTEN_NESTING` written inside each other and up to
/// `MAX_TERM_DEPTH` deep as built from definitions, and refused one past either (see
/// third-party/carcara/DOWNSTREAM.md, "Terms nest at most 2^18 deep"). Upstream recursed once per
/// level, so a term a few thousand deep overflowed the stack of the thread that read or checked
/// it.
#[test]
fn nesting_and_depth_are_bounded() {
    on_the_checkers_stack(|| {
        let read = |problem: &str, proof: &str| {
            parser::parse_instance(problem, proof, None, parser::Config::clean_dialect())
                .map(|_| ())
                .map_err(|e| e.to_string())
        };
        let written = format!(
            "terms and sorts written more than {} deep inside each other are not read",
            parser::MAX_WRITTEN_NESTING
        );
        let too_deep = format!(
            "a term or sort more than {} deep is not read",
            parser::MAX_TERM_DEPTH
        );

        // `(not (not ... p))`, and `(Array (Array ... Bool) Bool)`, written `n` deep.
        let n = parser::MAX_WRITTEN_NESTING;
        for (depth, within) in [(n, true), (n + 1, false)] {
            let term = format!("{}p{}", "(not ".repeat(depth), ")".repeat(depth));
            let result = read(&format!("(declare-const p Bool)(assert {term})"), "");
            assert_eq!(result.is_ok(), within, "{depth}: {result:?}");
            if !within {
                assert!(result.unwrap_err().contains(&written));
            }
            let sort = format!("{}Bool{}", "(Array Int ".repeat(depth), ")".repeat(depth));
            let result = read(&format!("(declare-const a {sort})"), "");
            assert_eq!(result.is_ok(), within, "{depth}: {result:?}");
        }

        // `d0 = p`, one deep, and `d_j = (not d_(j-1))`, `j + 1` deep, defined in the proof.
        let max = parser::MAX_TERM_DEPTH;
        let mut proof = String::from("(define-fun d0 () Bool p)\n");
        for j in 1..max {
            proof.push_str(&format!("(define-fun d{j} () Bool (not d{}))\n", j - 1));
        }
        assert_eq!(read("(declare-const p Bool)", &proof), Ok(()));
        proof.push_str(&format!("(define-fun d{max} () Bool (not d{}))\n", max - 1));
        let result = read("(declare-const p Bool)", &proof);
        assert!(
            result.as_ref().unwrap_err().contains(&too_deep),
            "{result:?}"
        );

        // `S0 = Bool`, one deep, and `S_j = (Array Int S_(j-1))`, defined in the problem.
        let mut problem = String::from("(define-sort S0 () Bool)");
        for j in 1..max {
            problem.push_str(&format!("(define-sort S{j} () (Array Int S{}))", j - 1));
        }
        assert_eq!(read(&problem, ""), Ok(()));
        problem.push_str(&format!("(define-sort S{max} () (Array Int S{}))", max - 1));
        let result = read(&problem, "");
        assert!(
            result.as_ref().unwrap_err().contains(&too_deep),
            "{result:?}"
        );
    });
}

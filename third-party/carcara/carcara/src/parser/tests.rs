//! In addition to the parser tests, this module contains some parsing functions that can be
//! useful in tests, and are intended to be used in other modules.
#![cfg(test)]

use super::*;
use crate::ast::pool::PrimitivePool;

const ERROR_MESSAGE: &str = "parser error during test";

// Some tests need function definitions to be applied
const TEST_CONFIG: Config = Config::new().apply_function_defs(true);

pub fn parse_terms<const N: usize>(
    pool: &mut PrimitivePool,
    definitions: &str,
    terms: [&str; N],
) -> [Rc<Term>; N] {
    let mut parser = Parser::new(pool, TEST_CONFIG, definitions).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);

    terms.map(|s| {
        parser.reset(s).expect(ERROR_MESSAGE);
        parser.parse_term().expect(ERROR_MESSAGE)
    })
}

pub fn parse_term(pool: &mut PrimitivePool, input: &str) -> Rc<Term> {
    Parser::new(pool, TEST_CONFIG, input)
        .and_then(|mut parser| parser.parse_term())
        .expect(ERROR_MESSAGE)
}

/// Tries to parse a term from a `&str`, expecting it to fail. Returns the error encountered, or
/// panics if no error is encountered.
pub fn parse_term_err(input: &str) -> Error {
    let mut pool = PrimitivePool::new();
    Parser::new(&mut pool, TEST_CONFIG, input)
        .and_then(|mut p| p.parse_term())
        .expect_err("expected error")
}

/// Parses a proof from a `&str`. Panics if any error is encountered.
pub fn parse_proof(pool: &mut PrimitivePool, input: &str) -> Proof {
    Parser::new(pool, TEST_CONFIG, input)
        .expect(ERROR_MESSAGE)
        .parse_proof()
        .expect(ERROR_MESSAGE)
}

/// Tries to parse a proof from a `&str`, expecting it to fail. Returns the error encountered, or
/// panics if no error is encountered.
pub fn parse_proof_err(pool: &mut PrimitivePool, input: &str) -> Error {
    Parser::new(pool, TEST_CONFIG, input)
        .and_then(|mut p| p.parse_proof())
        .expect_err("expected error")
}

fn run_parser_tests(pool: &mut PrimitivePool, cases: &[(&str, Term)]) {
    for (case, expected) in cases {
        let got = parse_term(pool, case);
        assert_eq!(expected, &*got);
    }
}

#[test]
fn test_hash_consing() {
    use indexmap::IndexSet;

    let mut pool = PrimitivePool::new();
    let input = "(-
        (-
            (+ 1 2)
            (* (+ 1 2) (+ 1 2))
        )
        (* 2 2)
    )";
    let mut parser = Parser::new(&mut pool, Config::new(), input).unwrap();
    parser.parse_term().unwrap();

    // We expect this input to result in 7 unique terms after parsing:
    //   1
    //   2
    //   (+ 1 2)
    //   (* (+ 1 2) (+ 1 2))
    //   (- (+ 1 2) (* ...))
    //   (* 2 2)
    //   (- (- ...) (* 2 2))
    let expected = vec![
        "1",
        "2",
        "(+ 1 2)",
        "(* (+ 1 2) (+ 1 2))",
        "(- (+ 1 2) (* (+ 1 2) (+ 1 2)))",
        "(* 2 2)",
        "(- (- (+ 1 2) (* (+ 1 2) (+ 1 2))) (* 2 2))",
    ]
    .into_iter()
    .collect::<IndexSet<&str>>();

    let pool_terms = pool.terms.into_vec();
    assert_eq!(pool_terms.len(), expected.len());
    for got in pool_terms {
        let formatted: &str = &format!("{:#}", got);
        assert!(expected.contains(formatted), "{}", formatted);
    }
}

#[test]
fn test_constant_terms() {
    let mut p = PrimitivePool::new();
    assert_eq!(Term::new_int(42), *parse_term(&mut p, "42"));
    assert_eq!(Term::new_real((3, 2)), *parse_term(&mut p, "1.5"));
    assert_eq!(Term::new_string("foo"), *parse_term(&mut p, "\"foo\""));
    assert_eq!(Term::new_bv(0, 4), *parse_term(&mut p, "(_ bv0 4)"));
}

#[test]
fn test_arithmetic_ops() {
    let mut p = PrimitivePool::new();
    let [one, two, three, five, seven] = [1, 2, 3, 5, 7].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(+ 2 3)",
            Term::Op(Operator::Add, vec![two.clone(), three.clone()]),
        ),
        (
            "(* 2 3 5 7)",
            Term::Op(
                Operator::Mult,
                vec![two.clone(), three, five.clone(), seven],
            ),
        ),
        ("(- 5)", Term::Op(Operator::Sub, vec![five])),
        ("(- (+ 1 1) 2)", {
            let one_plus_one = p.add(Term::Op(Operator::Add, vec![one.clone(), one]));
            Term::Op(Operator::Sub, vec![one_plus_one, two])
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(+ (- 1 2) (* 3.0 4.2))"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_logic_ops() {
    let mut p = PrimitivePool::new();
    let [zero, one, two, three, four] = [0, 1, 2, 3, 4].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(and true false)",
            Term::Op(Operator::And, vec![p.bool_true(), p.bool_false()]),
        ),
        (
            "(or true true false)",
            Term::Op(
                Operator::Or,
                vec![p.bool_true(), p.bool_true(), p.bool_false()],
            ),
        ),
        ("(and true)", Term::Op(Operator::And, vec![p.bool_true()])),
        ("(or true (and false false))", {
            let false_and_false = Term::Op(Operator::And, vec![p.bool_false(), p.bool_false()]);
            Term::Op(Operator::Or, vec![p.bool_true(), p.add(false_and_false)])
        }),
        (
            "(xor true false false)",
            Term::Op(
                Operator::Xor,
                vec![p.bool_true(), p.bool_false(), p.bool_false()],
            ),
        ),
        (
            "(= 2 3)",
            Term::Op(Operator::Equals, vec![two.clone(), three]),
        ),
        ("(not false)", Term::Op(Operator::Not, vec![p.bool_false()])),
        (
            "(distinct 4 2)",
            Term::Op(Operator::Distinct, vec![four, two]),
        ),
        ("(=> (= 0 1) true false)", {
            let zero_equals_one = p.add(Term::Op(Operator::Equals, vec![zero, one]));
            Term::Op(
                Operator::Implies,
                vec![zero_equals_one, p.bool_true(), p.bool_false()],
            )
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(or true 1.2)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(= 10 10.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(not 1 2 3)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 3), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 2 1.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 0)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 1), _),
    ));
    assert!(matches!(
        parse_term_err("(=> true 0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_ite() {
    let mut p = PrimitivePool::new();
    let [one, two, three] = [1, 2, 3].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(ite true 2 3)",
            Term::Op(Operator::Ite, vec![p.bool_true(), two.clone(), three]),
        ),
        ("(ite (not true) 2 (ite false 2 1))", {
            let not_true = Term::Op(Operator::Not, vec![p.bool_true()]);
            let ite = Term::Op(Operator::Ite, vec![p.bool_false(), two.clone(), one]);
            Term::Op(Operator::Ite, vec![p.add(not_true), two, p.add(ite)])
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(ite true 0)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 2), _),
    ));
    assert!(matches!(
        parse_term_err("(ite 0 1 2)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(ite false 10 10.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_quantifiers() {
    let mut p = PrimitivePool::new();
    let bool_sort = p.add_sort(Sort::Bool);
    let real_sort = p.add_sort(Sort::Real);
    let cases = [
        ("(exists ((p Bool)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort.clone()));
            Term::Binder(
                Binder::Exists,
                BindingList(vec![("p".into(), bool_sort)]),
                inner,
            )
        }),
        ("(forall ((x Real) (y Real)) (= (+ x y) 0.0))", {
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, real_sort.clone())));
            let x_plus_y = p.add(Term::Op(Operator::Add, vec![x, y]));
            let zero = p.add(Term::new_real(0));
            let inner = p.add(Term::Op(Operator::Equals, vec![x_plus_y, zero]));
            Term::Binder(
                Binder::Forall,
                BindingList(vec![
                    ("x".into(), real_sort.clone()),
                    ("y".into(), real_sort),
                ]),
                inner,
            )
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(exists () true)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(forall ((x Int)) (+ x x)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_choice_terms() {
    let mut p = PrimitivePool::new();
    let bool_sort = p.add_sort(Sort::Bool);
    let int_sort = p.add_sort(Sort::Int);
    let cases = [
        ("(choice ((p Bool)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort.clone()));
            let bindings = BindingList(vec![("p".into(), bool_sort)]);
            Term::Binder(Binder::Choice, bindings, inner)
        }),
        ("(choice ((x Int)) (= x 0))", {
            let x = p.add(Term::new_var("x", int_sort.clone()));
            let zero = p.add(Term::new_int(0));
            let inner = p.add(Term::Op(Operator::Equals, vec![x, zero]));
            let bindings = BindingList(vec![("x".into(), int_sort)]);
            Term::Binder(Binder::Choice, bindings, inner)
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(choice () false)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
    assert!(matches!(
        parse_term_err("(choice ((x Int) (y Int)) (= x y))"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
}

#[test]
fn test_let_terms() {
    let mut p = PrimitivePool::new();
    let bool_sort = p.add_sort(Sort::Bool);
    let int_sort = p.add_sort(Sort::Int);
    let cases = [
        ("(let ((p false)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort));
            Term::Let(BindingList(vec![("p".into(), p.bool_false())]), inner)
        }),
        ("(let ((x 1) (y 2)) (+ x y))", {
            let [one, two] = [1, 2].map(|n| p.add(Term::new_int(n)));
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, int_sort.clone())));
            let inner = p.add(Term::Op(Operator::Add, vec![x, y]));
            Term::Let(
                BindingList(vec![("x".into(), one), ("y".into(), two)]),
                inner,
            )
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(let () 0)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
}

#[test]
fn test_lambda_terms() {
    let mut p = PrimitivePool::new();
    let int_sort = p.add_sort(Sort::Int);
    let cases = [
        ("(lambda ((x Int)) x)", {
            let x = p.add(Term::new_var("x", int_sort.clone()));
            let bindings = BindingList(vec![("x".into(), int_sort.clone())]);
            Term::Binder(Binder::Lambda, bindings, x)
        }),
        ("(lambda ((x Int) (y Int)) (+ x y))", {
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, int_sort.clone())));
            let inner = p.add(Term::Op(Operator::Add, vec![x, y]));
            let bindings =
                BindingList(vec![("x".into(), int_sort.clone()), ("y".into(), int_sort)]);
            Term::Binder(Binder::Lambda, bindings, inner)
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(lambda () false)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("((lambda ((x Int)) (+ x 1)) false)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_annotated_terms() {
    let mut p = PrimitivePool::new();
    let zero = Term::new_int(0);
    let [two, three] = [2, 3].map(|n| p.add(Term::new_int(n)));
    let cases = [
        ("(! 0 :named foo)", zero.clone()),
        ("(! (! 0 :named foo) :named bar)", zero.clone()),
        ("(! 0 :named foo :named bar)", zero.clone()),
        ("(! (! 0 :pattern ((+ 1 0) 3)) :named bar)", zero.clone()),
        ("(ite (! true :named baz) 2 3)", {
            Term::Op(Operator::Ite, vec![p.bool_true(), two, three])
        }),
        ("(! 0 :unknown foo)", zero.clone()),
        ("(! 0 :unknown (list of tokens) :named foo)", zero.clone()),
        ("(! 0 :no :arguments)", zero),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(! true)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(! true not_a_keyword)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
    assert!(matches!(
        parse_term_err("(! true :named 1 2 3)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
}

#[test]
fn test_declare_fun() {
    let mut p = PrimitivePool::new();

    parse_terms(
        &mut p,
        "(declare-fun f (Bool Int Real) Real)",
        ["(f false 42 3.14159)"],
    );
    parse_terms(
        &mut p,
        "(declare-fun y () Real)
        (declare-fun f (Real) Int)
        (declare-fun g (Int Int) Bool)",
        ["(g (f y) 0)"],
    );

    let [got] = parse_terms(&mut p, "(declare-fun x () Real)", ["x"]);
    let real_sort = p.add_sort(Sort::Real);
    assert_eq!(p.add(Term::new_var("x", real_sort)), got);
}

#[test]
fn test_declare_sort() {
    let mut p = PrimitivePool::new();

    parse_terms(
        &mut p,
        "(declare-sort T 0)
        (declare-sort U 0)
        (declare-sort Y 0)
        (declare-fun t () T)
        (declare-fun u () U)
        (declare-fun f (T U) Y)",
        ["(f t u)"],
    );

    let [got] = parse_terms(
        &mut p,
        "(declare-sort T 0)
        (declare-fun x () T)",
        ["x"],
    );
    let expected_sort = p.add_sort(Sort::Atom("T".into(), Box::new([])));
    assert_eq!(p.add(Term::new_var("x", expected_sort)), got);
}

#[test]
fn test_define_fun() {
    let mut p = PrimitivePool::new();
    let [got] = parse_terms(
        &mut p,
        "(define-fun add ((a Int) (b Int)) Int (+ a b))",
        ["(add 2 3)"],
    );
    assert_eq!(parse_term(&mut p, "(+ 2 3)"), got);

    let [got] = parse_terms(&mut p, "(define-fun x () Int 2)", ["(+ x 3)"]);
    assert_eq!(parse_term(&mut p, "(+ 2 3)"), got);

    let [got] = parse_terms(
        &mut p,
        "(define-fun f ((x Int)) Int (+ x 1))
         (define-fun g ((a Int) (b Int)) Int (* (f a) (f b)))",
        ["(g 2 3)"],
    );
    let expected = parse_term(&mut p, "(* (+ 2 1) (+ 3 1))");
    assert_eq!(expected, got);
}

#[test]
fn test_define_fun_rec() {
    // Modified in Clean: a problem's `define-fun-rec` or `define-funs-rec` is refused (see
    // third-party/carcara/DOWNSTREAM.md, fix 39). Upstream read each as a declaration and a
    // universally quantified premise, which these cases checked.
    fn run_test(pool: &mut PrimitivePool, problem: &str) {
        let mut parser = Parser::new(pool, TEST_CONFIG, problem).expect(ERROR_MESSAGE);
        let got = parser.parse_problem();
        assert!(
            matches!(
                got,
                Err(Error::Parser(ParserError::RecursiveDefinitionRefused(_), _))
            ),
            "{problem}"
        );
    }
    let mut p = PrimitivePool::new();

    run_test(
        &mut p,
        "(define-fun-rec sumr ((x Int)) Int (+ x (ite (> x 0) (sumr (- x 1)) 0)))",
    );

    run_test(&mut p, "(define-fun-rec five () Int 5)");

    run_test(
        &mut p,
        "(define-funs-rec
            ((is-even ((n Int)) Bool) (is-odd ((n Int)) Bool) (zero () Int))
            (
                (ite (= n zero) true (is-odd (- n 1)))
                (ite (= n zero) false (is-even (- n 1)))
                0
            )
        )",
    );
}

#[test]
fn test_define_sort() {
    let mut p = PrimitivePool::new();
    let [got] = parse_terms(
        &mut p,
        "(define-sort booool () Bool)",
        ["(exists ((b booool)) b)"],
    );
    assert_eq!(parse_term(&mut p, "(exists ((b Bool)) b)"), got);

    let [got] = parse_terms(
        &mut p,
        "(define-sort yarrA (Value Key) (Array Key Value))",
        ["(exists ((a (yarrA String Int))) false)"],
    );
    let expected = parse_term(&mut p, "(exists ((a (Array Int String))) false)");
    assert_eq!(expected, got);

    let [got] = parse_terms(
        &mut p,
        "(define-sort vector (T) (Array Int T))
        (define-sort matrix (T) (vector (vector T)))",
        ["(exists ((a (Array String (Array Int (matrix Bool))))) false)"],
    );
    let expected = parse_term(
        &mut p,
        "(exists ((a (Array String (Array Int (Array Int (Array Int Bool)))))) false)",
    );
    assert_eq!(expected, got);
}

#[test]
fn test_assume() {
    let mut p = PrimitivePool::new();
    let input = "
        (assume h1 true)
        (assume h2 (or true false) :ignore \"extra\" :attributes)
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 2);

    assert_eq!(
        &proof.commands[0],
        &ProofCommand::Assume {
            id: "h1".into(),
            term: p.bool_true(),
        }
    );

    assert_eq!(
        &proof.commands[1],
        &ProofCommand::Assume {
            id: "h2".into(),
            term: parse_term(&mut p, "(or true false)"),
        }
    );
}

#[test]
fn test_step() {
    let mut p = PrimitivePool::new();
    let input = "
        (step t1 (cl (= (+ 2 3) (- 1 2))) :rule rule-name)
        (step t2 (cl) :rule rule-name :premises (t1))
        (step t3 (cl) :rule rule-name :args (1 2.0 \"three\"))
        (step t4 (cl) :rule rule-name :premises (t1 t2 t3) :args (42)
            :ignore_this :and_this (blah blah 0 1))
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 4);

    assert_eq!(
        &proof.commands[0],
        &ProofCommand::Step(ProofStep {
            id: "t1".into(),
            clause: vec![parse_term(&mut p, "(= (+ 2 3) (- 1 2))")],
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[1],
        &ProofCommand::Step(ProofStep {
            id: "t2".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[2],
        &ProofCommand::Step(ProofStep {
            id: "t3".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: {
                vec![
                    Term::new_int(1),
                    Term::new_real(2),
                    Term::new_string("three"),
                ]
                .into_iter()
                .map(|term| p.add(term))
                .collect()
            },
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[3],
        &ProofCommand::Step(ProofStep {
            id: "t4".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (0, 1), (0, 2)],
            args: vec![p.add(Term::new_int(42))],
            discharge: Vec::new(),
        })
    );
}

#[test]
fn test_premises_in_subproofs() {
    let mut p = PrimitivePool::new();
    let input = "
        (assume h1 true)
        (assume h2 true)
        (anchor :step t3)
        (step t3.t1 (cl) :rule rule-name :premises (h1 h2))
        (step t3.t2 (cl) :rule rule-name :premises (t3.t1 h1 h2))
        (step t3 (cl) :rule rule-name :premises (h1 t3.t1 h2 t3.t2))
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 3);
    let subproof = match &proof.commands[2] {
        ProofCommand::Subproof(s) => &s.commands,
        _ => panic!(),
    };
    assert_eq!(subproof.len(), 3);
    assert_eq!(
        &subproof[0],
        &ProofCommand::Step(ProofStep {
            id: "t3.t1".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (0, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
    assert_eq!(
        &subproof[1],
        &ProofCommand::Step(ProofStep {
            id: "t3.t2".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(1, 0), (0, 0), (0, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
    assert_eq!(
        &subproof[2],
        &ProofCommand::Step(ProofStep {
            id: "t3".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (1, 0), (0, 1), (1, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
}

#[test]
fn test_assumes_after_steps_in_subproofs() {
    let mut p = PrimitivePool::new();
    let bad_input = "
        (assume h1 true)
        (assume h2 true)
        (anchor :step t3)
        (step t3.t1 (cl) :rule rule-name :premises (h1 h2))
        (assume h3 false)
        (step t3.t2 (cl) :rule rule-name :premises (t3.t1 h1 h2))
        (step t3 (cl) :rule rule-name :premises (h1 t3.t1 h2 t3.t2))
    ";

    assert!(matches!(
        parse_proof_err(&mut p, bad_input),
        Error::Parser(ParserError::AssumeAfterStepInSubproof(_), _)
    ));
}

#[test]
fn test_bitvectors() {
    let mut p = PrimitivePool::new();
    let cases = [
        (
            "(assume a0 (not (bvuge (bvcomp (_ bv1 4) (_ bv1 4)) (_ bv1 1))))",
            ProofCommand::Assume {
                id: "a0".into(),
                term: parse_term(
                    &mut p,
                    "(not (bvuge (bvcomp (_ bv1 4) (_ bv1 4)) (_ bv1 1)))",
                ),
            },
        ),
        (
            "(assume a0 (not (bvuge (bvcomp #b0000 #b0000) #b1)))",
            ProofCommand::Assume {
                id: "a0".into(),
                term: parse_term(&mut p, "(not (bvuge (bvcomp #b0000 #b0000) #b1)))"),
            },
        ),
    ];

    for (input, expected_value) in cases {
        let proof = parse_proof(&mut p, input);
        assert_eq!(proof.commands.len(), 1);
        assert_eq!(&proof.commands[0], &expected_value);
    }
}

#[test]
fn test_indexed_operators() {
    let mut p = PrimitivePool::new();
    let cases = [
        (
            "(assume a0 (= ((_ zero_extend 2) #b100) #b00100))",
            ProofCommand::Assume {
                id: "a0".into(),
                term: parse_term(&mut p, "(= ((_ zero_extend 2) #b100) #b00100)"),
            },
        ),
        (
            "(assume a0 (= ((_ sign_extend 2) #b100) #b00100))",
            ProofCommand::Assume {
                id: "a0".into(),
                term: parse_term(&mut p, "(= ((_ sign_extend 2) #b100) #b00100)"),
            },
        ),
        (
            "(assume a0 (= ((_ zero_extend 2) (_ bv1 4)) (_ bv1 6)))",
            ProofCommand::Assume {
                id: "a0".into(),
                term: parse_term(&mut p, "(= ((_ zero_extend 2) (_ bv1 4)) (_ bv1 6))"),
            },
        ),
    ];

    for (input, expected_value) in cases {
        let proof = parse_proof(&mut p, input);
        assert_eq!(proof.commands.len(), 1);
        assert_eq!(&proof.commands[0], &expected_value);
    }
}

#[test]
fn test_qualified_operators() {
    let mut p = PrimitivePool::new();
    let cases = [("((as const (Array Int Real)) 0.0)", {
        let [int, real] = [Sort::Int, Sort::Real].map(|s| p.add_sort(s));
        let sort = p.add_sort(Sort::Array(int, real));
        Term::AsOp(
            QualifiedOperator::Const,
            sort,
            vec![p.add(Term::new_real(0))],
        )
    })];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("((as const Real) 0.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("((as undefined (Array Int Int)) 1)"),
        Error::Parser(ParserError::UndefinedIden(_), _),
    ));
}

#[test]
fn test_proofs_with_extra_parens() {
    let mut p = PrimitivePool::new();
    let proof = parse_proof(&mut p, "( (assume h1 true) )");
    assert_eq!(proof.commands.len(), 1);
    assert_eq!(
        &proof.commands[0],
        &ProofCommand::Assume {
            id: "h1".into(),
            term: p.bool_true(),
        }
    );

    // Empty proof with extra parens
    let proof = parse_proof(&mut p, "()");
    assert_eq!(proof.commands.len(), 0);

    // Extra set of parens
    assert!(matches!(
        parse_proof_err(&mut p, "(( (assume h1 true) ))"),
        Error::Parser(ParserError::UnexpectedToken(Token::OpenParen), _)
    ));

    // Stuff after final closing parens
    assert!(matches!(
        parse_proof_err(&mut p, "( (assume h1 true) ) (assume h2 false)"),
        Error::Parser(ParserError::UnexpectedToken(Token::OpenParen), _)
    ));

    // Missing closing parens
    assert!(matches!(
        parse_proof_err(&mut p, "( (assume h1 true)"),
        Error::Parser(ParserError::UnexpectedToken(Token::Eof), _)
    ));

    // Missing opening parens
    assert!(matches!(
        parse_proof_err(&mut p, "(assume h1 true) )"),
        Error::Parser(ParserError::UnexpectedToken(Token::CloseParen), _)
    ));
}

/// Added in Clean: a chain of named links used inside an `exists` that binds many names, with a
/// `let` beside each link. The `let` enters and leaves a scope between two links, which gives the
/// symbol table back the generation it had (`HashMapStack::generation`), so each link is answered
/// from the one before it. When every scope change gave a new generation, the cache emptied at
/// each link, and every link was answered from its free variables, a lookup each (498 of these
/// 500; 20,000 links took 27 s).
#[test]
fn capture_checks_keep_their_answers_across_a_scope_entered_and_left() {
    let n = 500;
    let mut problem = "(declare-const p Bool)".to_owned();
    for j in 0..=n {
        problem.push_str(&format!("(declare-const c{j} (_ BitVec 8))"));
    }
    let links: Vec<String> = (1..=n)
        .map(|j| {
            let previous = if j == 1 {
                "c0".to_owned()
            } else {
                format!("e{}", j - 1)
            };
            format!("(= (! (bvadd c{j} {previous}) :named e{j}) (let ((z c0)) z))")
        })
        .collect();
    let ys: Vec<String> = (0..n).map(|i| format!("(y{i} Bool)")).collect();
    problem.push_str(&format!(
        "(assert (exists ({}) (and y0 {})))",
        ys.join(" "),
        links.join(" ")
    ));
    let mut pool = PrimitivePool::new();
    let mut parser = Parser::new(&mut pool, Config::new(), &problem).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);
    let answered = parser.state.answered_from_free_vars;
    assert!(
        answered <= 2,
        "{answered} links answered from their free variables"
    );
}

/// Added in Clean: a chain of `n` named links, each in `wrappers` binders of its own (`(exists ((u
/// Bool)) (and u link))` for one), inside an `exists` that binds `n` names, or (`nested`) each
/// link one binder deeper than the one before; and how many links the capture checks answered
/// from their free variables.
fn links_answered_from_free_vars(n: usize, wrappers: usize, nested: bool) -> usize {
    let mut problem = "(declare-const p Bool)".to_owned();
    for j in 0..=n {
        problem.push_str(&format!("(declare-const c{j} (_ BitVec 8))"));
    }
    let link = |j: usize| {
        let previous = if j == 1 {
            "c0".to_owned()
        } else {
            format!("e{}", j - 1)
        };
        format!("(= (! (bvadd c{j} {previous}) :named e{j}) c0)")
    };
    let body = if nested {
        let opened: String = (1..=n)
            .map(|j| format!("(exists ((u{j} Bool)) (and u{j} {} ", link(j)))
            .collect();
        format!("{opened}true{}", "))".repeat(n))
    } else {
        let links: Vec<String> = (1..=n)
            .map(|j| {
                let opened: String = (0..wrappers)
                    .map(|w| format!("(exists ((u{w} Bool)) (and u{w} "))
                    .collect();
                format!("{opened}{}{}", link(j), "))".repeat(wrappers))
            })
            .collect();
        let ys: Vec<String> = (0..n).map(|i| format!("(y{i} Bool)")).collect();
        format!("(exists ({}) (and y0 {}))", ys.join(" "), links.join(" "))
    };
    problem.push_str(&format!("(assert {body})"));
    // The nested links are read 2n terms deep, at a few KiB of stack a level.
    let read = move || {
        let mut pool = PrimitivePool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), &problem).expect(ERROR_MESSAGE);
        parser.parse_problem().expect(ERROR_MESSAGE);
        parser.state.answered_from_free_vars
    };
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(read)
        .expect("a thread for the parse")
        .join()
        .expect("the parse returns")
}

/// Added in Clean: links each read in binders of their own, which the symbol table enters for
/// each link alone. Each link's answer is kept with the scopes it was computed in, and answers
/// the next link from the scopes they share (the wide `exists`, or the binders the next link is
/// nested in), with only the names the binders since bind looked up. When answers were kept for
/// one generation of the table alone, nearly every link was answered from its free variables (498
/// of 500 in the first shape; in release probes, 10,000 links each in a binder of its own took
/// 3.5 s and 20,000 19.0 s, where they now take 0.05 s and 0.11 s).
#[test]
fn capture_checks_carry_their_answers_into_scopes_entered_inside() {
    for (wrappers, nested) in [(1, false), (2, false), (0, true)] {
        let answered = links_answered_from_free_vars(500, wrappers, nested);
        assert!(
            answered <= 2,
            "{answered} links answered from their free variables ({wrappers}, {nested})"
        );
    }
}

/// Added in Clean: an answer of the capture checks that holds a variable answers only in the scopes
/// it was computed in. The body of `g` mentions its parameter `x`: used inside `(forall ((x Int))
/// ...)`, the answer for the body holds `x` (a parameter, so nothing is captured); used again
/// after that binder, in the scope around it, where no `x` is bound, it holds nothing. Carried
/// into that scope, the first answer would hold an `x` the scope does not bind, which the check of
/// every answer against its free variables' (in tests) refuses.
#[test]
fn an_answer_holding_a_variable_answers_only_in_its_own_scopes() {
    let problem = "(declare-const a Int)(define-fun g ((x Int)) Int (+ x a))\
        (assert (forall ((y Int)) (and (forall ((x Int)) (= (g y) x)) (= (g y) y))))";
    let mut pool = PrimitivePool::new();
    let mut parser = Parser::new(&mut pool, TEST_CONFIG, problem).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);
}

/// Added in Clean: the capture checks keep only the answers that can still answer. Each of 10,000
/// assertions names a closed term inside a `forall` of its own, whose scope the parser leaves at
/// the end of the assertion; an answer kept with that scope never answers again, and is dropped
/// when the answers are next swept. When every answer was kept for the whole parse, the parser held
/// all 10,000 at the end; now at most `ANSWERS_SWEEP_MIN`.
#[test]
fn capture_checks_drop_the_answers_of_scopes_left() {
    let n = 10_000;
    let mut problem = String::new();
    for j in 0..n {
        problem.push_str(&format!(
            "(declare-const c{j} Int)(assert (forall ((x Int)) (or (> x 0) (! (> c{j} 0) :named n{j}))))"
        ));
    }
    let mut pool = PrimitivePool::new();
    let mut parser = Parser::new(&mut pool, Config::new(), &problem).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);
    let kept = parser.state.locally_bound.len();
    assert!(
        kept <= ANSWERS_SWEEP_MIN,
        "{kept} answers kept after {n} scopes left"
    );
}

/// Added in Clean: the capture checks of named terms and of the uses of definitions answer from
/// answers kept with the scopes they were computed in (`Parser::locally_bound_free_vars`), which,
/// in tests, checks each answer against the one computed from the term's free variables alone.
/// These are random problems whose named terms and definitions are used under binders of one or
/// two names and `let`s that bind the names they mention, globals and parameters shadowed, scopes
/// entered and left between uses of one term, and terms reused in scopes nested inside and beside
/// the ones they were answered in; each is read with definitions as premises and as macros, and
/// some are refused for a capture.
#[test]
fn capture_checks_answer_from_their_cache_as_without_it() {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    struct Script {
        rng: StdRng,
        names: Vec<(String, bool)>,
        next: usize,
    }

    impl Script {
        fn int(&mut self, bound: &mut Vec<&'static str>, depth: usize) -> String {
            let choice = if depth == 0 {
                self.rng.gen_range(0..4)
            } else {
                self.rng.gen_range(0..12)
            };
            match choice {
                0 => "a".to_owned(),
                1 => "b".to_owned(),
                2 if !bound.is_empty() => bound[self.rng.gen_range(0..bound.len())].to_owned(),
                2 | 3 => "k".to_owned(),
                4 => format!("(g {})", self.int(bound, depth - 1)),
                5 => format!("(h {})", self.int(bound, depth - 1)),
                6 => format!(
                    "(+ {} {})",
                    self.int(bound, depth - 1),
                    self.int(bound, depth - 1)
                ),
                7 | 8 => {
                    let inner = self.int(bound, depth - 1);
                    self.next += 1;
                    self.names.push((format!("n{}", self.next), false));
                    format!("(! {inner} :named n{})", self.next)
                }
                9 => {
                    let ints: Vec<String> = self
                        .names
                        .iter()
                        .filter(|(_, b)| !b)
                        .map(|(n, _)| n.clone())
                        .collect();
                    if ints.is_empty() {
                        "a".to_owned()
                    } else {
                        ints[self.rng.gen_range(0..ints.len())].clone()
                    }
                }
                _ => {
                    let name = ["x", "a", "k"][self.rng.gen_range(0..3)];
                    let value = self.int(bound, depth - 1);
                    bound.push(name);
                    let body = self.int(bound, depth - 1);
                    bound.pop();
                    format!("(let (({name} {value})) {body})")
                }
            }
        }

        fn boolean(&mut self, bound: &mut Vec<&'static str>, depth: usize) -> String {
            let choice = if depth == 0 {
                0
            } else {
                self.rng.gen_range(0..8)
            };
            match choice {
                0 | 1 => format!("(= {} {})", self.int(bound, depth), self.int(bound, depth)),
                2 | 3 => {
                    let names: &[&'static str] =
                        [&["x"][..], &["a"], &["y"], &["b"], &["x", "y"], &["a", "k"]]
                            [self.rng.gen_range(0..6)];
                    let quantifier = ["forall", "exists"][self.rng.gen_range(0..2)];
                    bound.extend(names);
                    let body = self.boolean(bound, depth - 1);
                    bound.truncate(bound.len() - names.len());
                    let list: Vec<String> = names.iter().map(|n| format!("({n} Int)")).collect();
                    format!("({quantifier} ({}) {body})", list.join(" "))
                }
                4 => format!(
                    "(and {} {})",
                    self.boolean(bound, depth - 1),
                    self.boolean(bound, depth - 1)
                ),
                5 => {
                    let inner = self.boolean(bound, depth - 1);
                    self.next += 1;
                    self.names.push((format!("m{}", self.next), true));
                    format!("(! {inner} :named m{})", self.next)
                }
                6 => {
                    let bools: Vec<String> = self
                        .names
                        .iter()
                        .filter(|(_, b)| *b)
                        .map(|(n, _)| n.clone())
                        .collect();
                    if bools.is_empty() {
                        "p".to_owned()
                    } else {
                        bools[self.rng.gen_range(0..bools.len())].clone()
                    }
                }
                _ => format!("(not {})", self.boolean(bound, depth - 1)),
            }
        }
    }

    let (mut read, mut refused) = (0, 0);
    for seed in 0..800 {
        let mut script = Script {
            rng: StdRng::seed_from_u64(seed),
            names: Vec::new(),
            next: 0,
        };
        let mut problem = "(set-logic ALL)(declare-const a Int)(declare-const b Int)\
            (declare-const p Bool)(define-fun k () Int (+ a b))(define-fun g ((x Int)) Int (+ x k))\
            (define-fun h ((a Int)) Int (+ a k))"
            .to_owned();
        for _ in 0..6 {
            let depth = 4 + seed as usize % 3;
            let assertion = script.boolean(&mut Vec::new(), depth);
            problem.push_str(&format!("(assert {assertion})"));
        }
        for config in [Config::new(), Config::new().apply_function_defs(true)] {
            let mut pool = PrimitivePool::new();
            let result =
                Parser::new(&mut pool, config, &problem).and_then(|mut p| p.parse_problem());
            match result {
                Ok(_) => read += 1,
                Err(Error::Parser(
                    ParserError::NamedTermNotClosed(..) | ParserError::MacroCapture(..),
                    _,
                )) => refused += 1,
                Err(e) => panic!("{e}: {problem}"),
            }
        }
    }
    eprintln!("{read} read, {refused} refused for a capture");
    assert!(
        read > 100 && refused > 100,
        "{read} read, {refused} refused"
    );
}

/// Added in Clean: a parse given a deadline (`parse_instance_until`) stops at it. A deadline already
/// passed refuses at the parser's first poll, on the first token, rather than once the parse ends
/// (lines later); a distant one changes nothing.
#[test]
fn a_parse_stops_at_its_deadline() {
    use std::time::{Duration, Instant};

    let problem = "(declare-const p Bool)(assert p)(assert (not p))";
    let proof = "(assume h1 p)(assume h2 (not p))(step t1 (cl) :rule resolution :premises (h1 h2))";
    let passed = Some(Instant::now());
    let problem_lines = format!("{problem}\n\n\n");
    match parse_instance_until(&problem_lines, proof, None, Config::new(), passed) {
        Err(Error::Parser(ParserError::DeadlineExceeded, position)) => {
            assert_eq!(position, (0, 0), "refused where the first token is read");
        }
        Err(other) => panic!("expected the deadline's refusal, got {other}"),
        Ok(_) => panic!("expected the deadline's refusal, got a parse"),
    }
    let distant = Some(Instant::now() + Duration::from_secs(3600));
    let (parsed, _, _, _) =
        parse_instance_until(problem, proof, None, Config::new(), distant).expect(ERROR_MESSAGE);
    assert_eq!(parsed.premises.len(), 2);
}

/// Added in Clean: a parse cut short by its deadline is refused, never returned. A problem of
/// 3,000 named terms in binders of their own inside a wide `exists`, each using the one before as
/// a definition, with a proof, is read under deadlines from 0 to past the time it takes without
/// one: each reading is refused with the deadline's refusal or reads the problem and proof whole.
#[test]
fn a_parse_cut_short_by_its_deadline_is_refused_never_returned() {
    use std::time::Instant;

    let n = 3_000;
    let mut problem = "(declare-const p Bool)".to_owned();
    for j in 0..=n {
        problem.push_str(&format!("(declare-const c{j} (_ BitVec 8))"));
    }
    let ys: Vec<String> = (0..n).map(|i| format!("(y{i} Bool)")).collect();
    let links: Vec<String> = (1..=n)
        .map(|j| {
            let previous = if j == 1 {
                "c0".to_owned()
            } else {
                format!("e{}", j - 1)
            };
            format!("(exists ((u Bool)) (and u (= (! (bvadd c{j} c0) :named e{j}) {previous})))")
        })
        .collect();
    problem.push_str(&format!(
        "(assert (exists ({}) (and y0 {})))(assert p)(assert (not p))",
        ys.join(" "),
        links.join(" ")
    ));
    let mut proof = "(assume h1 p)(assume h2 (not p))".to_owned();
    for j in 0..n {
        proof.push_str(&format!(
            "(step s{j} (cl) :rule resolution :premises (h1 h2))"
        ));
    }
    let whole = |deadline: Option<Instant>| {
        parse_instance_until(&problem, &proof, None, Config::new(), deadline).map(
            |(problem, proof, _, _)| {
                let premises: Vec<String> =
                    problem.premises.iter().map(ToString::to_string).collect();
                (premises.join("\n"), proof.commands.len())
            },
        )
    };
    let start = Instant::now();
    let expected = whole(None).expect(ERROR_MESSAGE);
    let took = start.elapsed();
    let (mut read, mut refused) = (0, 0);
    for step in 0..=40u32 {
        let deadline = Instant::now() + took * step / 30;
        match whole(Some(deadline)) {
            Ok(parsed) => {
                assert_eq!(
                    parsed, expected,
                    "a parse under a deadline {step}/30 differs"
                );
                read += 1;
            }
            Err(Error::Parser(ParserError::DeadlineExceeded, _)) => refused += 1,
            Err(other) => panic!("deadline {step}/30: {other}"),
        }
    }
    eprintln!("took {took:?}: {read} read whole, {refused} refused at the deadline");
    assert!(refused >= 1, "{read} read, {refused} refused");
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean's Alethe dialect reads `zero_extend` as its SMT-LIB definition at the
//! parse boundary (`third-party/carcara/DOWNSTREAM.md` § Dialect,
//! `expand_zero_extend`). These tests hold that reading.
//!
//! A wrong reading would not be visible to rule checking: the refutation would
//! then be about a different problem. So the parsed term is compared with the
//! definition computed here from the numerals as written, at every position the
//! parser builds a term, across the width class where a `u32` cast would hide
//! (fix 35 in DOWNSTREAM.md).

use super::verify_alethe_proof;
use carcara::{
    ast::{
        pool::{PrimitivePool, TermPool},
        AnchorArg, Constant, Operator, ParamOperator, ProofCommand, Rc, Sort, Term,
    },
    parser::{parse_instance_with_pool, Config},
};
use std::collections::HashSet;

/// Operand widths and extension amounts: small, word-sized, and the `2^32`
/// class a 32-bit truncation of a width would misread.
const WIDTHS: [usize; 7] = [1, 8, 64, 65, (1 << 32) - 1, 1 << 32, (1 << 33) + 1];
const EXTRAS: [usize; 7] = [0, 1, 7, 24, 64, 1 << 32, (1 << 33) + 1];

/// `((_ zero_extend k) t)` by SMT-LIB's definition: `t` when `k = 0`,
/// otherwise `(concat Z t)` with `Z` the all-zero constant of width `k`.
fn definition(pool: &mut PrimitivePool, k: usize, t: Rc<Term>) -> Rc<Term> {
    if k == 0 {
        return t;
    }
    let zero = pool.add(Term::Const(Constant::BitVec(0.into(), k)));
    pool.add(Term::Op(Operator::BvConcat, vec![zero, t]))
}

fn var(pool: &mut PrimitivePool, name: &str, width: usize) -> Rc<Term> {
    let sort = pool.add_sort(Sort::BitVec(width));
    pool.add(Term::new_var(name, sort))
}

fn children(term: &Term) -> Vec<Rc<Term>> {
    match term {
        Term::Const(_) | Term::Var(..) => Vec::new(),
        Term::App(function, args) => std::iter::once(function.clone())
            .chain(args.iter().cloned())
            .collect(),
        Term::Op(_, args) | Term::AsOp(_, _, args) => args.clone(),
        Term::Binder(_, _, body) => vec![body.clone()],
        Term::Let(bindings, body) => bindings
            .0
            .iter()
            .map(|(_, value)| value.clone())
            .chain(std::iter::once(body.clone()))
            .collect(),
        Term::Match(scrutinee, cases) => std::iter::once(scrutinee.clone())
            .chain(cases.iter().map(|case| case.body.clone()))
            .collect(),
        Term::ParamOp { op_args, args, .. } => op_args.iter().chain(args).cloned().collect(),
    }
}

/// Every distinct subterm reachable from `roots`, `let` values included.
fn subterms(roots: impl IntoIterator<Item = Rc<Term>>) -> Vec<Rc<Term>> {
    let mut seen = HashSet::new();
    let mut stack: Vec<_> = roots.into_iter().collect();
    let mut all = Vec::new();
    while let Some(term) = stack.pop() {
        if seen.insert(term.clone()) {
            stack.extend(children(&term));
            all.push(term);
        }
    }
    all
}

fn is_zero_extend(term: &Term) -> bool {
    matches!(
        term,
        Term::ParamOp {
            op: ParamOperator::ZeroExtend,
            ..
        }
    )
}

/// The right-hand side of every `(= <name> rhs)` in `terms`.
fn defined_as<'t>(terms: &'t [Rc<Term>], name: &str) -> Vec<&'t Rc<Term>> {
    terms
        .iter()
        .filter_map(|term| match term.as_ref() {
            Term::Op(Operator::Equals, args) if args.len() == 2 => {
                (args[0].as_var() == Some(name)).then_some(&args[1])
            }
            _ => None,
        })
        .collect()
}

struct Instance {
    problem: String,
    proof: String,
    rules: String,
}

/// One `zero_extend` of `d : (_ BitVec w)` by `k` at every position the
/// parser builds a term. Each position defines a distinct constant
/// (`c_<position>`) so the check can find it after parsing.
fn instance(w: usize, k: usize) -> Instance {
    let wk = w + k;
    let wk1 = wk + 1;
    let ext = format!("((_ zero_extend {k}) d)");
    let problem = format!(
        "(declare-const d (_ BitVec {w}))
(declare-const c_assert (_ BitVec {wk}))
(declare-const c_fun (_ BitVec {wk}))
(declare-const c_app (_ BitVec {wk}))
(declare-const c_forall (_ BitVec {wk}))
(declare-const c_let (_ BitVec {wk}))
(declare-const c_nested (_ BitVec {wk1}))
(declare-const c_step (_ BitVec {wk}))
(declare-const c_def (_ BitVec {wk}))
(define-fun f () (_ BitVec {wk}) {ext})
(define-fun g ((z (_ BitVec {w}))) (_ BitVec {wk}) ((_ zero_extend {k}) z))
(assert (= c_assert {ext}))
(assert (= c_fun f))
(assert (= c_app (g d)))
(assert (forall ((d (_ BitVec {w}))) (= c_forall {ext})))
(assert (let ((l (= c_let {ext}))) l))
(assert (= c_nested ((_ zero_extend 1) {ext})))
"
    );
    let proof = format!(
        "(define-fun e () (_ BitVec {wk}) {ext})
(step s_clause (cl (= c_step {ext})) :rule hole)
(step s_def (cl (= c_def e)) :rule hole)
(step s_args (cl) :rule forall_inst :args ({ext}))
(anchor :step s_end :args ((:= (c_anchor (_ BitVec {wk})) {ext})))
(step s_inner (cl) :rule hole)
(step s_end (cl) :rule hole)
"
    );
    let rules = format!(
        "(declare-rare-rule zx ((x (_ BitVec {w}))) :args (x) :premises () \
         :conclusion (= ((_ zero_extend {k}) x) ((_ zero_extend {k}) x)))"
    );
    Instance {
        problem,
        proof,
        rules,
    }
}

/// Every term the parse produced: premises, proof definitions, step clauses
/// and arguments, anchor assignments, and RARE conclusions.
struct Parsed {
    terms: Vec<Rc<Term>>,
    definitions: Vec<(String, Rc<Term>)>,
    step_args: Vec<(String, Vec<Rc<Term>>)>,
    assignments: Vec<(String, Rc<Term>)>,
    rare: Vec<Rc<Term>>,
}

fn parse(instance: &Instance, config: Config, pool: &mut PrimitivePool) -> Parsed {
    let (problem, proof, rules) = parse_instance_with_pool(
        &instance.problem,
        &instance.proof,
        Some(instance.rules.as_str()),
        config,
        pool,
    )
    .unwrap_or_else(|error| panic!("{config:?} refused\n{}\n{error}", instance.problem));
    let mut roots: Vec<Rc<Term>> = problem.premises.iter().cloned().collect();
    let mut step_args = Vec::new();
    let mut assignments = Vec::new();
    let mut stack = vec![proof.commands.as_slice()];
    while let Some(commands) = stack.pop() {
        for command in commands {
            match command {
                ProofCommand::Assume { term, .. } => roots.push(term.clone()),
                ProofCommand::Step(step) => {
                    roots.extend(step.clause.iter().cloned());
                    roots.extend(step.args.iter().cloned());
                    step_args.push((step.id.clone(), step.args.clone()));
                }
                ProofCommand::Subproof(subproof) => {
                    for arg in &subproof.args {
                        if let AnchorArg::Assign((name, _), value) = arg {
                            roots.push(value.clone());
                            assignments.push((name.clone(), value.clone()));
                        }
                    }
                    stack.push(&subproof.commands);
                }
            }
        }
    }
    roots.extend(proof.constant_definitions.iter().map(|(_, t)| t.clone()));
    let rare: Vec<_> = rules
        .rules
        .values()
        .map(|rule| rule.conclusion.clone())
        .collect();
    roots.extend(rare.iter().cloned());
    Parsed {
        terms: subterms(roots),
        definitions: proof.constant_definitions,
        step_args,
        assignments,
        rare,
    }
}

fn the_one<'t>(found: Vec<&'t Rc<Term>>, what: &str) -> &'t Rc<Term> {
    let [one] = found.as_slice() else {
        panic!("expected exactly one {what}, found {}", found.len());
    };
    one
}

#[test]
fn zero_extend_is_read_as_its_definition_everywhere() {
    for w in WIDTHS {
        for k in EXTRAS {
            let instance = instance(w, k);
            for expanded_defs in [false, true] {
                let config = Config::clean_dialect().apply_function_defs(expanded_defs);
                let mut pool = PrimitivePool::new();
                let parsed = parse(&instance, config, &mut pool);
                let at = format!("w={w} k={k} apply_function_defs={expanded_defs}");
                assert!(
                    !parsed.terms.iter().any(|t| is_zero_extend(t)),
                    "{at}: a zero_extend survived the parse"
                );
                let d = var(&mut pool, "d", w);
                let want = definition(&mut pool, k, d);
                assert_eq!(*pool.sort(&want), Sort::BitVec(w + k), "{at}");
                let nested = definition(&mut pool, 1, want.clone());
                assert_eq!(*pool.sort(&nested), Sort::BitVec(w + k + 1), "{at}");
                for name in ["c_assert", "c_forall", "c_let", "c_step", "c_def"] {
                    let got = the_one(defined_as(&parsed.terms, name), name);
                    assert_eq!(got, &want, "{at}: {name}");
                }
                let got = the_one(defined_as(&parsed.terms, "c_nested"), "c_nested");
                assert_eq!(got, &nested, "{at}: nested");
                // A problem `define-fun`: expanded in place, or kept as a
                // defining premise `(= f body)` (`g` as a lambda).
                if expanded_defs {
                    for name in ["c_fun", "c_app"] {
                        let got = the_one(defined_as(&parsed.terms, name), name);
                        assert_eq!(got, &want, "{at}: {name}");
                    }
                } else {
                    let got = the_one(defined_as(&parsed.terms, "f"), "f");
                    assert_eq!(got, &want, "{at}: define-fun body");
                    let z = var(&mut pool, "z", w);
                    let body = definition(&mut pool, k, z);
                    let lambda = the_one(defined_as(&parsed.terms, "g"), "g");
                    assert!(
                        matches!(lambda.as_ref(), Term::Binder(_, _, b) if *b == body),
                        "{at}: define-fun with a parameter: {lambda}"
                    );
                }
                let [(name, value)] = parsed.definitions.as_slice() else {
                    panic!("{at}: one proof definition");
                };
                assert_eq!((name.as_str(), value), ("e", &want), "{at}");
                let args = parsed
                    .step_args
                    .iter()
                    .find(|(id, _)| id == "s_args")
                    .map(|(_, args)| args.as_slice());
                assert_eq!(args, Some(&[want.clone()][..]), "{at}: :args");
                let [(name, value)] = parsed.assignments.as_slice() else {
                    panic!("{at}: one anchor assignment");
                };
                assert_eq!((name.as_str(), value), ("c_anchor", &want), "{at}");
                let x = var(&mut pool, "x", w);
                let rare = definition(&mut pool, k, x);
                let [conclusion] = parsed.rare.as_slice() else {
                    panic!("{at}: one RARE rule");
                };
                assert!(
                    matches!(conclusion.as_ref(), Term::Op(Operator::Equals, sides)
                        if sides.iter().all(|side| *side == rare)),
                    "{at}: RARE conclusion {conclusion}"
                );
            }
        }
    }
}

/// Without the option the parser keeps the indexed operator, so the reading
/// is the dialect's and nothing else's.
#[test]
fn without_the_dialect_the_operator_is_kept() {
    for (w, k) in [(8, 24), (1 << 32, 1)] {
        let mut pool = PrimitivePool::new();
        let parsed = parse(&instance(w, k), Config::new(), &mut pool);
        let got = the_one(defined_as(&parsed.terms, "c_assert"), "c_assert");
        assert!(is_zero_extend(got), "{got}");
        assert_eq!(*pool.sort(got), Sort::BitVec(w + k));
    }
}

// The five behavioural tests below moved unchanged from the deleted adapter
// post-pass (`carcara_verify/zero_extend/tests.rs`). They run the production
// adapter end to end.

fn identity(declarations: &str, left: &str, right: &str) -> (String, String) {
    let equality = format!("(= {left} {right})");
    let problem = format!("{declarations}(assert (not {equality}))(check-sat)");
    let proof = format!("(assume a (not {equality}))\n(step e (cl {equality}) :rule refl)\n(step done (cl) :rule resolution :premises (a e))\n");
    (problem, proof)
}

#[test]
fn zero_extension_is_exact_at_full_width_and_zero_extra() {
    for width in [1, 8, 64, 128] {
        let declarations = format!("(declare-const x (_ BitVec {width}))");
        for extra in [0, 1, 7, 64] {
            let left = format!("((_ zero_extend {extra}) x)");
            let right = if extra == 0 {
                "x".into()
            } else {
                format!("(concat (_ bv0 {extra}) x)")
            };
            let (problem, proof) = identity(&declarations, &left, &right);
            assert!(
                verify_alethe_proof(&problem, &proof).unwrap(),
                "width={width} extra={extra}"
            );
        }
    }
}

#[test]
fn zero_extension_rejects_changed_high_bits_low_bits_and_assertion() {
    let declarations = "(declare-const x (_ BitVec 64))(declare-const y (_ BitVec 64))";
    for wrong in ["(concat #b1 x)", "(concat #b0 y)", "(concat x #b0)"] {
        let (problem, proof) = identity(declarations, "((_ zero_extend 1) x)", wrong);
        assert!(verify_alethe_proof(&problem, &proof).is_err(), "{wrong}");
    }
    let (problem, proof) = identity(declarations, "((_ zero_extend 1) x)", "(concat #b0 x)");
    let different_problem = problem.replace("(concat #b0 x)", "(concat #b1 x)");
    assert!(verify_alethe_proof(&different_problem, &proof).is_err());
}

#[test]
fn zero_extension_preserves_scopes_and_expanded_definitions() {
    let (problem, proof) = identity(
        "(declare-const x (_ BitVec 8))",
        "((_ zero_extend 0) ((_ zero_extend 2) x))",
        "(concat #b00 x)",
    );
    let proof = format!(
        "(define-fun ext () (_ BitVec 10) ((_ zero_extend 2) x))\n{}",
        proof.replace("((_ zero_extend 2) x)", "ext"),
    );
    assert!(verify_alethe_proof(&problem, &proof).unwrap());
    let left = "(forall ((x (_ BitVec 8))) (= ((_ zero_extend 1) x) (concat #b0 x)))";
    let right = "(forall ((x (_ BitVec 8))) (= (concat #b0 x) (concat #b0 x)))";
    let (problem, proof) = identity("", left, right);
    assert!(verify_alethe_proof(&problem, &proof).unwrap());
    let wrong = "(forall ((y (_ BitVec 8))) (= (concat #b1 y) (concat #b0 y)))";
    let (problem, proof) = identity("", left, wrong);
    assert!(verify_alethe_proof(&problem, &proof).is_err());
}

#[test]
fn zero_extension_normalizes_local_assumptions() {
    let problem = "(declare-const x (_ BitVec 8))(assert (not (= ((_ zero_extend 1) x) (concat #b0 x))))(check-sat)";
    let proof = "(assume a (not (= ((_ zero_extend 1) x) (concat #b0 x))))
(anchor :step local)
(assume h true)
(step e (cl (= ((_ zero_extend 1) x) (concat #b0 x))) :rule refl)
(step local (cl (not true) (= ((_ zero_extend 1) x) (concat #b0 x))) :rule subproof :discharge (h))
(step yes (cl true) :rule true)
(step eq (cl (= ((_ zero_extend 1) x) (concat #b0 x))) :rule resolution :premises (local yes))
(step done (cl) :rule resolution :premises (a eq))";
    assert!(verify_alethe_proof(problem, proof).unwrap());
}

#[test]
fn zero_extension_normalizes_instantiation_arguments_without_changing_binding() {
    let quantified = "(forall ((y (_ BitVec 9))) (not (= y (concat #b0 x))))";
    let instance = "(not (= ((_ zero_extend 1) x) (concat #b0 x)))";
    let problem = format!("(declare-const x (_ BitVec 8))(assert {quantified})(check-sat)");
    let proof = format!(
        "(assume a {quantified})
(step inst (cl (or (not {quantified}) {instance})) :rule forall_inst :args (((_ zero_extend 1) x)))
(step unpack (cl (not {quantified}) {instance}) :rule or :premises (inst))
(step bad (cl {instance}) :rule resolution :premises (a unpack))
(step eq (cl (= ((_ zero_extend 1) x) (concat #b0 x))) :rule refl)
(step done (cl) :rule resolution :premises (bad eq))"
    );
    assert!(verify_alethe_proof(&problem, &proof).unwrap());
    let wrong = proof.replace(":args (((_ zero_extend 1) x))", ":args ((concat #b1 x))");
    assert_ne!(wrong, proof);
    assert!(verify_alethe_proof(&problem, &wrong).is_err());
}

/// The deleted post-pass charged every command and every term visit of a
/// whole certificate against 4,000,000 units and refused past that, whether
/// or not the certificate mentioned `zero_extend` (`invalid or over-budget
/// zero-extension normalization`). The dialect reads `zero_extend` while it
/// parses and bounds nothing else, so size is not a refusal.
///
/// Sizing: each `and_pos` step below states one 1,000-conjunct `and` of
/// distinct atoms `(= x <numeral>)`. The post-pass charged about 8 units per
/// conjunct (two visits of each new node plus its child count), so 600 steps
/// are about 4.8 million units, past its budget; on a tree that still has the
/// post-pass this test fails with that refusal.
#[test]
fn a_certificate_without_zero_extend_is_not_refused_for_its_size() {
    const STEPS: usize = 600;
    const CONJUNCTS: usize = 1_000;
    let problem = "(declare-const x Int)(assert (not (= x x)))(check-sat)";
    let mut proof = String::with_capacity(STEPS * CONJUNCTS * 14);
    for step in 0..STEPS {
        proof.push_str(&format!("(step big{step} (cl (not (and"));
        for conjunct in 0..CONJUNCTS {
            proof.push_str(&format!(" (= x {})", step * CONJUNCTS + conjunct));
        }
        let first = step * CONJUNCTS;
        proof.push_str(&format!(")) (= x {first})) :rule and_pos :args (0))\n"));
    }
    proof.push_str("(assume a (not (= x x)))\n(step e (cl (= x x)) :rule refl)\n");
    proof.push_str("(step done (cl) :rule resolution :premises (a e))\n");
    let started = std::time::Instant::now();
    let verdict = verify_alethe_proof(problem, &proof);
    eprintln!(
        "{} bytes checked in {:.1?} (this profile)",
        proof.len(),
        started.elapsed()
    );
    assert!(matches!(verdict, Ok(true)), "{verdict:?}");
}

/// The `### Dialect:` headings of DOWNSTREAM.md, each naming the one parser
/// option it states, are exactly the options `Config::clean_dialect()` turns
/// on: an option without its statement, or a statement without its option,
/// fails here.
#[test]
fn the_dialect_section_lists_exactly_the_clean_dialect_options() {
    fn fields(config: Config) -> Vec<(String, String)> {
        let debug = format!("{config:?}");
        let inner = debug
            .strip_prefix("Config { ")
            .and_then(|rest| rest.strip_suffix(" }"))
            .unwrap_or_else(|| panic!("unexpected Debug of Config: {debug}"));
        inner
            .split(", ")
            .map(|field| {
                let (name, value) = field
                    .split_once(": ")
                    .unwrap_or_else(|| panic!("not a field: {field}"));
                (name.to_owned(), value.to_owned())
            })
            .collect()
    }
    let default = fields(Config::new());
    let dialect = fields(Config::clean_dialect());
    assert_eq!(default.len(), dialect.len());
    let names: HashSet<String> = default.iter().map(|(name, _)| name.clone()).collect();
    let selected: HashSet<String> = default
        .iter()
        .zip(&dialect)
        .filter_map(|((name, from), (dialect_name, to))| {
            assert_eq!(name, dialect_name);
            match (name.as_str(), from.as_str(), to.as_str()) {
                ("array_lambda_dialect", from, to) => {
                    assert_eq!((from, to), ("FunctionsOnly", "TypedArrayContexts"));
                    Some(name.clone())
                }
                (_, "false", "true") | (_, "true", "false") => Some(name.clone()),
                (_, "false", "false") | (_, "true", "true") => None,
                _ => panic!("unrecognized dialect option {name}: {from} -> {to}"),
            }
        })
        .collect();
    let downstream = include_str!("../../../../../../third-party/carcara/DOWNSTREAM.md");
    let mut stated = HashSet::new();
    for heading in downstream
        .lines()
        .filter(|line| line.starts_with("### Dialect:"))
    {
        let named: Vec<&str> = heading
            .split('`')
            .skip(1)
            .step_by(2)
            .filter(|token| names.contains(*token))
            .collect();
        let [option] = named.as_slice() else {
            panic!("a Dialect heading names exactly one Config option: {heading}");
        };
        assert!(
            stated.insert((*option).to_owned()),
            "stated twice: {option}"
        );
    }
    assert!(!selected.is_empty());
    assert_eq!(stated, selected);
}

// Added in Clean (not part of upstream Carcara): the `dt_project` rule and the parser refusals it
// relies on. See checker/rules/datatypes.rs and third-party/carcara/DOWNSTREAM.md, C2.

use carcara::{checker, parser};

/// `P` has two constructors, so a selector can be applied to the other one; `Tree`/`Forest` are
/// mutually recursive; `B1`/`B2` both have a field named `same`, of different sorts (`s1` was
/// parsed while `same` still meant `B1`'s selector); `Opt` is parametric.
#[test]
fn dt_project() {
    test_cases! {
        definitions = "
            (declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
            (declare-datatype A ((cA (fld Int))))
            (declare-datatypes ((Tree 0) (Forest 0))
                (((leaf (val Int)) (node (children Forest)))
                 ((fnil) (fcons (head Tree) (tail Forest)))))
            (declare-datatype Color ((red) (green)))
            (declare-datatype Opt (par (T) ((none) (some (value T)))))
            (declare-datatype B1 ((b1 (same Int))))
            (declare-fun a () Int)
            (define-fun s1 () Int (same (b1 a)))
            (declare-datatype B2 ((b2 (same Bool))))
            (declare-fun g (P) Int)
            (declare-fun b () Int)
            (declare-fun x () P)
            (declare-fun t () Tree)
            (declare-fun f () Forest)
            (declare-fun p () Bool)
            (define-fun mkab () P (mk a b))
            (define-fun snd2 ((q P)) Int (snd q))
        ",
        "Selector of the constructor, projecting the matching field" {
            "(step t1 (cl (= (fld (cA 5)) 5)) :rule dt_project)": true,
            "(step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)": true,
            "(step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)": true,
            "(step t1 (cl (= (oth (other a)) a)) :rule dt_project)": true,
            "(step t1 (cl (= (fst (mk 1 2)) 1)) :rule dt_project)": true,
            "(step t1 (cl (= (fst (mk a a)) a)) :rule dt_project)": true,
            "(step t1 (cl (= (fst (mk (+ a 1) b)) (+ a 1))) :rule dt_project)": true,
        }
        "Wrong value" {
            "(step t1 (cl (= (fld (cA 5)) 6)) :rule dt_project)": false,
            "(step t1 (cl (= (snd (mk a b)) a)) :rule dt_project)": false,
            "(step t1 (cl (= (fst (mk a b)) b)) :rule dt_project)": false,
            "(step t1 (cl (= (snd (mk a a)) b)) :rule dt_project)": false,
            "(step t1 (cl (= (fst (mk 1 2)) 2)) :rule dt_project)": false,
        }
        "The value is compared syntactically, never up to evaluation" {
            "(step t1 (cl (= (snd (mk a b)) (+ b 0))) :rule dt_project)": false,
            "(step t1 (cl (= (fst (mk (+ a 1) b)) (+ 1 a))) :rule dt_project)": false,
        }
        "Reversed orientation needs symm" {
            "(step t1 (cl (= b (snd (mk a b)))) :rule dt_project)": false,
            "(step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
            (step t2 (cl (= b (snd (mk a b)))) :rule symm :premises (t1))": true,
        }
        "Selector of another constructor (value unspecified by SMT-LIB)" {
            "(step t1 (cl (= (oth (mk a b)) a)) :rule dt_project)": false,
            "(step t1 (cl (= (oth (mk a b)) b)) :rule dt_project)": false,
            "(step t1 (cl (= (fst (other a)) a)) :rule dt_project)": false,
            "(step t1 (cl (= (snd (other a)) a)) :rule dt_project)": false,
        }
        "Uninterpreted function, or no constructor application" {
            "(step t1 (cl (= (g (mk a b)) a)) :rule dt_project)": false,
            "(step t1 (cl (= (g (mk a b)) b)) :rule dt_project)": false,
            "(step t1 (cl (= (fst x) a)) :rule dt_project)": false,
            "(step t1 (cl (= (fst (ite p (mk a b) x)) a)) :rule dt_project)": false,
        }
        "Nullary constructors have no selectors" {
            "(step t1 (cl (= (head fnil) t)) :rule dt_project)": false,
            "(step t1 (cl (= (tail fnil) fnil)) :rule dt_project)": false,
            "(step t1 (cl (= red red)) :rule dt_project)": false,
        }
        "Mutually recursive datatypes" {
            "(step t1 (cl (= (val (leaf a)) a)) :rule dt_project)": true,
            "(step t1 (cl (= (children (node f)) f)) :rule dt_project)": true,
            "(step t1 (cl (= (head (fcons t f)) t)) :rule dt_project)": true,
            "(step t1 (cl (= (tail (fcons t f)) f)) :rule dt_project)": true,
            "(step t1 (cl (= (head (fcons (leaf a) fnil)) (leaf a))) :rule dt_project)": true,
            "(step t1 (cl (= (tail (fcons (node fnil) (fcons t f))) (fcons t f))) :rule dt_project)": true,
            "(step t1 (cl (= (val (node f)) a)) :rule dt_project)": false,
            "(step t1 (cl (= (children (leaf a)) f)) :rule dt_project)": false,
            "(step t1 (cl (= (head (fcons t f)) (leaf a))) :rule dt_project)": false,
            "(step t1 (cl (= (children (node f)) fnil)) :rule dt_project)": false,
            "(step t1 (cl (= (val (head (fcons (leaf a) fnil))) a)) :rule dt_project)": false,
        }
        "Two datatypes with a field of the same name are told apart by sort" {
            "(step t1 (cl (= s1 a)) :rule dt_project)": true,
            "(step t1 (cl (= (same (b2 p)) p)) :rule dt_project)": true,
            "(step t1 (cl (= (same (b2 p)) (not p))) :rule dt_project)": false,
        }
        "A define-fun is a macro, expanded before the rule sees the term" {
            "(step t1 (cl (= (snd mkab) b)) :rule dt_project)": true,
            "(step t1 (cl (= (snd2 (mk a b)) b)) :rule dt_project)": true,
            "(step t1 (cl (= (snd2 mkab) b)) :rule dt_project)": true,
            "(step t1 (cl (= (snd2 mkab) a)) :rule dt_project)": false,
        }
        "A let is not looked through" {
            "(step t1 (cl (= (let ((q (mk a b))) (snd q)) b)) :rule dt_project)": false,
            "(step t1 (cl (let ((q (mk a b))) (= (snd q) b))) :rule dt_project)": false,
            "(step t1 (cl (= (snd (let ((q b)) (mk a q))) b)) :rule dt_project)": false,
        }
        "A binder inside a field that shadows a constructor name is not the constructor" {
            "(step t1 (cl (= (fst (mk (choice ((mk Int)) (= mk 1)) b)) (choice ((mk Int)) (= mk 1)))) :rule dt_project)": true,
            "(step t1 (cl (= (snd (mk a (choice ((snd Int)) (= snd 1)))) (choice ((snd Int)) (= snd 1)))) :rule dt_project)": true,
            "(step t1 (cl (= (snd (mk a (choice ((snd Int)) (= snd 1)))) (choice ((snd Int)) (= snd 2)))) :rule dt_project)": false,
        }
        "An anchor that binds the selector or constructor name" {
            "(anchor :step t1 :args ((snd (-> P Int))))
            (step t1.t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
            (step t1.t2 (cl (= (= (snd (mk a b)) b) (= b b))) :rule cong :premises (t1.t1))
            (step t1 (cl (= (forall ((snd (-> P Int))) (= (snd (mk a b)) b))
                            (forall ((snd (-> P Int))) (= b b)))) :rule bind)": false,
            "(anchor :step t1 :args ((mk (-> Int Int P))))
            (step t1.t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
            (step t1.t2 (cl (= (= (snd (mk a b)) b) (= b b))) :rule cong :premises (t1.t1))
            (step t1 (cl (= (forall ((mk (-> Int Int P))) (= (snd (mk a b)) b))
                            (forall ((mk (-> Int Int P))) (= b b)))) :rule bind)": false,
            "(anchor :step t1 :args ((y Int)))
            (step t1.t1 (cl (= (snd (mk a y)) y)) :rule dt_project)
            (step t1.t2 (cl (= (= (snd (mk a y)) y) (= y y))) :rule cong :premises (t1.t1))
            (step t1 (cl (= (forall ((y Int)) (= (snd (mk a y)) y))
                            (forall ((y Int)) (= y y)))) :rule bind)": true,
        }
        "Parametric datatypes are refused, bare or qualified with `as`" {
            "(step t1 (cl (= (value (some 5)) 5)) :rule dt_project)": false,
            "(step t1 (cl (= (value (some p)) p)) :rule dt_project)": false,
            "(step t1 (cl (= (value ((as some (Opt Int)) 5)) 5)) :rule dt_project)": false,
            "(step t1 (cl (= (value ((as some (Opt Bool)) p)) p)) :rule dt_project)": false,
        }
        "Exactly one literal, no premises, no arguments" {
            "(step t1 (cl (= (snd (mk a b)) b) p) :rule dt_project)": false,
            "(step t1 (cl p (= (snd (mk a b)) b)) :rule dt_project)": false,
            "(step t1 (cl) :rule dt_project)": false,
            "(step t1 (cl (not (= (snd (mk a b)) b))) :rule dt_project)": false,
            "(step t1 (cl (= (snd (mk a b)) b b)) :rule dt_project)": false,
            "(assume h p)
            (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project :premises (h))": false,
            "(step t1 (cl (= (snd (mk a b)) b)) :rule dt_project :args (a))": false,
            "(step t1 (cl (= (snd (mk a b)) b)) :rule dt_project :args (b))": false,
        }
        "Used in a refutation" {
            "(assume a0 (and (= x (mk a 5)) (not (= (snd x) 5))))
            (step t1 (cl (= x (mk a 5))) :rule and :premises (a0) :args (0))
            (step t2 (cl (not (= (snd x) 5))) :rule and :premises (a0) :args (1))
            (step t3 (cl (= (snd (mk a 5)) 5)) :rule dt_project)
            (step t4 (cl (= (snd x) (snd (mk a 5)))) :rule cong :premises (t1))
            (step t5 (cl (= (snd x) 5)) :rule trans :premises (t4 t3))
            (step t6 (cl) :rule resolution :premises (t2 t5))": true,
            "(assume a0 (and (= x (mk a 5)) (not (= (snd x) 5))))
            (step t1 (cl (= x (mk a 5))) :rule and :premises (a0) :args (0))
            (step t2 (cl (not (= (snd x) 5))) :rule and :premises (a0) :args (1))
            (step t3 (cl (= (snd (mk a 5)) 6)) :rule dt_project)
            (step t4 (cl (= (snd x) (snd (mk a 5)))) :rule cong :premises (t1))
            (step t5 (cl (= (snd x) 6)) :rule trans :premises (t4 t3))": false,
        }
    }
}

/// Checks `proof` against `problem` with the sequential checker and the parallel one (1 and 4
/// threads), which must agree on acceptance and on the holey flag. `Ok(is_holey)` or the
/// sequential checker's error text.
fn check_both(problem: &str, proof: &str) -> Result<bool, String> {
    use std::sync::Arc;

    let config = parser::Config::new().apply_function_defs(true);
    let (prob, prf, rules, mut pool) =
        parser::parse_instance(problem, proof, None, config).map_err(|e| e.to_string())?;
    let sequential = checker::ProofChecker::new(&mut pool, &rules, checker::Config::new())
        .check(&prob, &prf)
        .map_err(|e| e.to_string());
    for num_threads in [1, 4] {
        let (prob, prf, rules, pool) =
            parser::parse_instance(problem, proof, None, config).map_err(|e| e.to_string())?;
        let (scheduler, usage) = checker::Scheduler::new(num_threads, &prf);
        let mut parallel = checker::ParallelProofChecker::new(
            Arc::new(pool),
            checker::Config::new(),
            &prob.prelude,
            &usage,
            128 * 1024 * 1024,
            rules,
        );
        let got = parallel
            .check(&prob, &prf, &scheduler)
            .map_err(|e| e.to_string());
        // Both accept with the same holey flag, or both refuse (the error texts may differ).
        assert_eq!(
            got.as_ref().ok(),
            sequential.as_ref().ok(),
            "the parallel checker ({num_threads} threads) disagrees: {got:?} vs {sequential:?}"
        );
    }
    sequential
}

/// The rule is fully checked: a refutation through it is complete, not holey, in the sequential
/// and the parallel checker.
#[test]
fn dt_project_refutations_are_not_holey() {
    let problem = "
        (declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (= (snd (mk a b)) b)))
    ";
    let proof = "
        (assume a0 (not (= (snd (mk a b)) b)))
        (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
        (step t2 (cl) :rule resolution :premises (a0 t1))
    ";
    assert_eq!(check_both(problem, proof), Ok(false));

    // The same refutation through `hole` is holey: `dt_project` is not hole-like.
    let holey = proof.replace(":rule dt_project", ":rule hole");
    assert_eq!(check_both(problem, &holey), Ok(true));

    // Reversed orientation through `symm`.
    let problem = "
        (declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (= b (snd (mk a b)))))
    ";
    let proof = "
        (assume a0 (not (= b (snd (mk a b)))))
        (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
        (step t2 (cl (= b (snd (mk a b)))) :rule symm :premises (t1))
        (step t3 (cl) :rule resolution :premises (a0 t2))
    ";
    assert_eq!(check_both(problem, proof), Ok(false));
}

/// Complete refutations of satisfiable problems. Each would be a false UNSAT if `dt_project`
/// accepted its step, so each must be refused at that step.
#[test]
fn dt_project_refuses_refutations_of_satisfiable_problems() {
    let pair = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun g (P) Int)";
    let cases = [
        // `oth` of an `mk` value is unconstrained: a model picks `(oth (mk a b)) = a + 1`.
        (
            "(assert (not (= (oth (mk a b)) a)))",
            "(= (oth (mk a b)) a)",
        ),
        (
            "(assert (not (= (fst (other a)) a)))",
            "(= (fst (other a)) a)",
        ),
        // An uninterpreted function.
        ("(assert (not (= (g (mk a b)) a)))", "(= (g (mk a b)) a)"),
        // The other field: satisfiable whenever `a != b`.
        (
            "(assert (not (= (snd (mk a b)) a)))",
            "(= (snd (mk a b)) a)",
        ),
    ];
    // A selector redeclared as an uninterpreted function of the same sort is the same `Term::Var`.
    // The parser refuses the problem; without that, `dt_project` would read `snd` as the selector.
    let problem = format!("{pair}\n(declare-fun snd (P) Int)\n(assert (not (= (snd (mk a b)) b)))");
    let proof = "(assume a0 (not (= (snd (mk a b)) b)))
        (step t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
        (step t2 (cl) :rule resolution :premises (a0 t1))";
    let got = check_both(&problem, proof);
    assert!(
        matches!(&got, Err(e) if e.contains("'snd' is declared both as a datatype")),
        "redeclared selector: {got:?}"
    );

    for (assertion, lemma) in cases {
        let problem = format!("{pair}\n{assertion}");
        let proof = format!(
            "(assume a0 (not {lemma}))
            (step t1 (cl {lemma}) :rule dt_project)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
        );
        let got = check_both(&problem, &proof);
        assert!(
            matches!(&got, Err(e) if e.contains("'t1'") && e.contains("dt_project")),
            "{lemma}: {got:?}"
        );
    }

    // An anchor that rebinds the selector: `(forall ((snd (-> P Int))) (= (snd (mk a b)) b))` is
    // false (take `snd` constantly `b + 1`), so its negation is satisfiable.
    let problem =
        format!("{pair}\n(assert (not (forall ((snd (-> P Int))) (= (snd (mk a b)) b))))");
    let proof = "
        (assume a0 (not (forall ((snd (-> P Int))) (= (snd (mk a b)) b))))
        (anchor :step t1 :args ((snd (-> P Int))))
        (step t1.t1 (cl (= (snd (mk a b)) b)) :rule dt_project)
        (step t1.t2 (cl (= (= (snd (mk a b)) b) (= b b))) :rule cong :premises (t1.t1))
        (step t1 (cl (= (forall ((snd (-> P Int))) (= (snd (mk a b)) b))
                        (forall ((snd (-> P Int))) (= b b)))) :rule bind)
        (step t2 (cl (= (forall ((snd (-> P Int))) (= b b)) (= b b))) :rule qnt_rm_unused)
        (step t3 (cl (= (forall ((snd (-> P Int))) (= (snd (mk a b)) b)) (= b b)))
            :rule trans :premises (t1 t2))
        (step t4 (cl (= b b)) :rule eq_reflexive)
        (step t5 (cl (not (= (forall ((snd (-> P Int))) (= (snd (mk a b)) b)) (= b b)))
                     (forall ((snd (-> P Int))) (= (snd (mk a b)) b))
                     (not (= b b))) :rule equiv_pos1)
        (step t6 (cl) :rule resolution :premises (a0 t3 t4 t5))
    ";
    let got = check_both(&problem, proof);
    assert!(
        matches!(&got, Err(e) if e.contains("'t1.t1'") && e.contains("dt_project")),
        "anchor-bound selector: {got:?}"
    );
}

/// A parametric datatype is refused (until `(par ..)` sorts are instantiated), whichever way its
/// constructor is written: bare, its sort is `(par ..)`; qualified with `as`, its sort is
/// instantiated and the datatype sort has arguments.
#[test]
fn dt_project_refuses_parametric_datatypes() {
    let opt = "(declare-datatype Opt (par (T) ((none) (some (value T)))))
        (declare-fun a () Int)";
    for (lemma, reason) in [
        (
            "(= (value ((as some (Opt Int)) a)) a)",
            "parametric datatypes are not supported",
        ),
        (
            "(= (value (some a)) a)",
            "the constructor is not a function symbol",
        ),
    ] {
        let problem = format!("{opt}\n(assert (not {lemma}))");
        let proof = format!(
            "(assume a0 (not {lemma}))
            (step t1 (cl {lemma}) :rule dt_project)
            (step t2 (cl) :rule resolution :premises (a0 t1))"
        );
        let got = check_both(&problem, &proof);
        assert!(
            matches!(&got, Err(e) if e.contains("'t1'") && e.contains(reason)),
            "{lemma}: {got:?}"
        );
    }
}

/// `(as f S)` instantiates a `par` symbol `f` at `S`, so `S` must be an instance of `f`'s sort.
/// Upstream built `f` at any sort `S`. The datatype guard lets a `par` symbol share a name with a
/// symbol of another arity, so with `L` declaring a `par` constructor `snd` after `P` declared its
/// selector `snd`, `(as snd (-> P Int))` was the very `Term::Var` of `P`'s selector, and
/// `dt_project` accepted refutations of satisfiable problems (read as a free symbol, the way
/// Carcara read `(as snd Int)`, `g` below is arbitrary).
#[test]
fn par_symbols_are_qualified_only_at_an_instance_of_their_sort() {
    let pair = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))";
    let consts = "(declare-const a Int) (declare-const b Int) (declare-fun g (P) Int)";
    let nullary_snd = "(declare-datatype L (par (X) ((snd) (cns (hd X)))))";
    let refused = [
        // A nullary `par` constructor qualified as `P`'s selector, through a problem `define-fun`
        // (refused in both modes) or an equation.
        format!(
            "{pair} {nullary_snd} {consts} (define-fun ap ((f (-> P Int)) (x P)) Int (f x)) \
             (assert (not (= (ap (as snd (-> P Int)) (mk a b)) b)))"
        ),
        format!("{pair} {nullary_snd} {consts} (assert (= g (as snd (-> P Int))))"),
        // ... at a sort no symbol has, or at the sort of a constant.
        format!(
            "{pair} {nullary_snd} {consts} (assert (= (as snd (-> P Bool)) (as snd (-> P Bool))))"
        ),
        format!("{pair} {nullary_snd} {consts} (assert (= a (as snd Int)))"),
        // A binary `par` constructor qualified as `P`'s selector: its sort has three components
        // and `(-> P Int)` two. With `(h2 Int)`, matching component by component up to the
        // shorter sort (as `zip` did) succeeded.
        format!(
            "{pair} (declare-datatype L (par (X) ((nl) (snd (h1 X) (h2 X))))) {consts} \
             (assert (= g (as snd (-> P Int))))"
        ),
        format!(
            "{pair} (declare-datatype L (par (X) ((nl) (snd (h1 X) (h2 Int))))) {consts} \
             (assert (= g (as snd (-> P Int))))"
        ),
        // Both datatypes in one block.
        format!(
            "(declare-datatypes ((P 0) (L 1)) (((mk (fst Int) (snd Int)) (other (oth Int))) \
             (par (X) ((snd) (cns (hd X)))))) {consts} (assert (= g (as snd (-> P Int))))"
        ),
        // A nullary `par` constructor qualified as `P`'s constructor.
        format!(
            "{pair} (declare-datatype L (par (X) ((mk) (cns (hd X))))) {consts} \
             (declare-fun h (Int Int) P) (assert (= h (as mk (-> Int Int P))))"
        ),
    ];
    for problem in &refused {
        let err = parse_error(problem);
        assert!(
            err.as_deref()
                .is_some_and(|e| e.contains("not an instance of its sort")),
            "expected a refused `as` for {problem}: {err:?}"
        );
    }

    // The same qualification in a proof, against a problem that does not use it.
    let problem = format!("{pair} {nullary_snd} {consts} (assert (not (= (g (mk a b)) b)))");
    let proof = "(define-fun ap ((f (-> P Int)) (x P)) Int (f x))
        (assume h (not (= (g (mk a b)) b)))
        (step t1 (cl (= (ap (as snd (-> P Int)) (mk a b)) b)) :rule dt_project)
        (step t2 (cl) :rule hole :premises (h t1))";
    for apply_function_defs in [false, true] {
        let err = parse_error_with(&problem, proof, apply_function_defs);
        assert!(
            err.as_deref()
                .is_some_and(|e| e.contains("not an instance of its sort")),
            "expected a refused `as` in the proof: {err:?}"
        );
    }

    // Instances of the `par` sort stay legal, nullary or not, bare or applied.
    let opt = "(declare-datatype Opt (par (T) ((none) (some (value T)))))";
    let accepted = [
        format!("{opt} (declare-const o (Opt Int)) (assert (= o (as none (Opt Int))))"),
        format!("{opt} (declare-const o (Opt Int)) (assert (= o ((as some (Opt Int)) 5)))"),
        format!(
            "{opt} (declare-fun s (Int) (Opt Int)) (assert (= s (as some (-> Int (Opt Int)))))"
        ),
        format!(
            "{opt} (declare-fun v ((Opt Int)) Int) (assert (= v (as value (-> (Opt Int) Int))))"
        ),
        format!(
            "{opt} (declare-fun s (Bool) (Opt Bool)) (assert (= s (as some (-> Bool (Opt Bool)))))"
        ),
        format!("{pair} {nullary_snd} (declare-const l (L Int)) (assert (= l (as snd (L Int))))"),
        format!(
            "{pair} {nullary_snd} (declare-const l (L P)) (assert (= l ((as cns (L P)) (mk 1 2))))"
        ),
    ];
    for problem in &accepted {
        assert_eq!(parse_error(problem), None, "{problem}");
    }

    // The X16f refutation, end to end: refused before any rule runs.
    let problem = format!(
        "{pair} {nullary_snd} {consts} (assert (= g (as snd (-> P Int)))) \
         (assert (not (= (g (mk a b)) b)))"
    );
    let proof = "(define-fun ap ((f (-> P Int)) (x P)) Int (f x))
        (assume h0 (= g (as snd (-> P Int))))
        (assume h (not (= (g (mk a b)) b)))
        (step t1 (cl (= (ap (as snd (-> P Int)) (mk a b)) b)) :rule dt_project)
        (step t2 (cl (= (g (mk a b)) (ap (as snd (-> P Int)) (mk a b)))) :rule ho_cong :premises (h0))
        (step t3 (cl (= (g (mk a b)) b)) :rule trans :premises (t2 t1))
        (step t4 (cl) :rule resolution :premises (h t3))";
    let got = check_both(&problem, proof);
    assert!(
        matches!(&got, Err(e) if e.contains("not an instance of its sort")),
        "X16f: {got:?}"
    );
}

fn parse_error_with(problem: &str, proof: &str, apply_function_defs: bool) -> Option<String> {
    let config = parser::Config::new().apply_function_defs(apply_function_defs);
    parser::parse_instance(problem, proof, None, config)
        .err()
        .map(|e| e.to_string())
}

/// The parse error for `problem` (with a trivial proof), in both `define-fun` modes. The two
/// modes must agree.
fn parse_error(problem: &str) -> Option<String> {
    let proof = "(step t1 (cl) :rule hole)";
    let declared = parse_error_with(problem, proof, false);
    let expanded = parse_error_with(problem, proof, true);
    assert_eq!(
        declared.is_some(),
        expanded.is_some(),
        "the define-fun modes disagree on {problem}: {declared:?} vs {expanded:?}"
    );
    declared
}

/// Declarations that would make one symbol (a name and a sort) denote both a datatype symbol and
/// something else, or that redeclare a datatype, are ill-formed SMT-LIB and refused at parse time.
/// `dt_project` relies on this to read a constructor or selector symbol as the datatype's own.
#[test]
fn ambiguous_datatype_symbols_are_refused() {
    let pair = "(declare-datatype P ((mk (fst Int) (snd Int)) (other (oth Int))))";
    let refused = [
        // A later global declaration with the name and sort of a constructor or selector.
        format!("{pair} (declare-fun mk (Int Int) P)"),
        format!("{pair} (declare-fun snd (P) Int)"),
        format!("{pair} (declare-const snd (-> P Int))"),
        format!("{pair} (define-fun snd ((q P)) Int 0)"),
        // (`define-fun-rec` and `define-funs-rec` are refused outright since fix 39, see
        // `carcara/tests/problem_reading.rs`.)
        // A datatype declared twice, or twice in one command.
        format!("{pair} (declare-datatype P ((k (h Int))))"),
        "(declare-datatypes ((Q 0) (Q 0)) (((q1)) ((q2))))".to_owned(),
        // A name used twice inside one datatype.
        "(declare-datatype D ((c1 (f Int)) (c2 (f Int))))".to_owned(),
        "(declare-datatype D ((c (f Int) (f Int))))".to_owned(),
        "(declare-datatype D ((c (h Int)) (c (k Int))))".to_owned(),
        "(declare-datatype D ((c (c Int))))".to_owned(),
        // A constructor of one datatype that is also a selector of another, with the same sort.
        "(declare-datatypes ((D 0) (E 0)) (((snd (e E)) (dnil)) ((k (snd D)))))".to_owned(),
        // The same argument sorts and a different result sort: an ambiguous overload, which
        // Carcara would resolve to the later declaration.
        "(declare-datatype P ((mk (fst Int) (snd Int)))) \
         (declare-datatype Q ((mk (snd Int) (fst Int))))"
            .to_owned(),
        format!("{pair} (declare-fun mk (Int Int) Int)"),
        format!("(declare-fun mk (Int Int) Int) {pair}"),
        format!("{pair} (declare-fun oth (P) Bool)"),
        format!("{pair} (define-fun snd ((q P)) Bool true)"),
        "(declare-datatype C1 ((red) (blue))) (declare-datatype C2 ((red)))".to_owned(),
        "(declare-datatype C1 ((red) (blue))) (declare-const red Int)".to_owned(),
        "(declare-const red Int) (declare-datatype C1 ((red) (blue)))".to_owned(),
        // A parametric symbol overlaps any declaration of the same arity.
        "(declare-datatype Opt (par (T) ((none) (some (value T))))) (declare-fun some (Int) Int)"
            .to_owned(),
        "(declare-datatype Opt (par (T) ((none) (some (value T))))) (declare-const none Int)"
            .to_owned(),
        // A `define-fun` expanded as a macro, or a `:named` term, is a global symbol too.
        format!("{pair} (define-fun mk ((x Int) (y Int)) P (mk y x))"),
        "(declare-const a Int) (declare-datatype C1 ((red))) (assert (! (= a a) :named red))"
            .to_owned(),
        "(declare-const a Int) (assert (! (= a a) :named red)) (declare-datatype C1 ((red)))"
            .to_owned(),
        // A datatype named like another sort, in either order.
        format!("(declare-sort P 0) {pair}"),
        format!("{pair} (declare-sort P 0)"),
        format!("(define-sort P () Int) {pair}"),
        format!("{pair} (define-sort P () Int)"),
        format!("(declare-sort P 0) (declare-fun snd (P) Int) {pair}"),
    ];
    for problem in &refused {
        let err = parse_error(problem);
        assert!(
            err.as_deref().is_some_and(|e| e.contains("datatype")),
            "expected a datatype declaration error for {problem}: {err:?}"
        );
    }

    let accepted = [
        // Two datatypes with a same-named field of different sorts are two symbols.
        "(declare-datatype B1 ((b1 (same Int)))) (declare-datatype B2 ((b2 (same Bool))))"
            .to_owned(),
        "(declare-datatypes ((B1 0) (B2 0)) (((b1 (same Int))) ((b2 (same Bool)))))".to_owned(),
        // The name of a constructor with a different sort is a different symbol.
        format!("{pair} (declare-fun mk (Int) Int)"),
        // Binders may shadow a constructor or selector name.
        format!("{pair} (assert (forall ((mk Int) (snd Bool)) (or snd (= mk 0))))"),
        format!("{pair} (assert (let ((snd 1)) (= snd 1)))"),
        // Same name, different argument sorts: a use of the earlier symbol after the later one
        // is a sort error, never a misreading.
        "(declare-datatype P ((mk (fst Int) (snd Int)))) (declare-datatype Q ((mk (fst Int))))"
            .to_owned(),
        format!("{pair} (declare-const mk Int)"),
        format!("{pair} (define-fun fst ((q Int)) Int q)"),
        "(declare-const a Int) (declare-datatype C1 ((red))) (assert (! (= a a) :named blue))"
            .to_owned(),
    ];
    // Redeclaring an ordinary symbol or sort, which upstream allowed, is refused since fix 38
    // (`carcara/tests/problem_reading.rs`), with its own message.
    for problem in &accepted {
        assert_eq!(parse_error(problem), None, "{problem}");
    }

    // A proof's `define-fun` and `:named` terms are checked against the problem's datatypes.
    let problem = format!("{pair} (declare-datatype C1 ((red))) (declare-const a Int)");
    for proof in [
        "(define-fun snd ((q P)) Int 0) (step t1 (cl) :rule hole)",
        "(define-fun other ((x Int)) P (mk x x)) (step t1 (cl) :rule hole)",
        "(step t1 (cl (! (= a a) :named red)) :rule hole)",
    ] {
        for apply_function_defs in [false, true] {
            let err = parse_error_with(&problem, proof, apply_function_defs);
            assert!(
                err.as_deref().is_some_and(|e| e.contains("datatype")),
                "expected a datatype declaration error for {proof}: {err:?}"
            );
        }
    }
    let proof = "(define-fun snd ((x Int)) Int x) (step t1 (cl (! (= a a) :named t)) :rule hole)";
    assert_eq!(parse_error_with(&problem, proof, false), None);
}

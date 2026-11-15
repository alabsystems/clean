use super::{
    node::ProofNodeForest,
    pool::{PrimitivePool, TermPool},
    Polyeq, Rc, Term,
};
use crate::parser::tests::parse_terms;
use indexmap::IndexSet;

#[test]
fn test_free_vars() {
    fn run_tests(definitions: &str, cases: &[(&str, &[&str])]) {
        for &(term, expected) in cases {
            let mut pool = PrimitivePool::new();
            let [root] = parse_terms(&mut pool, definitions, [term]);
            let expected: IndexSet<_> = expected.iter().copied().collect();
            let set = pool.free_vars(&root);
            let got: IndexSet<_> = set.iter().map(|t| t.as_var().unwrap()).collect();

            assert_eq!(expected, got);
        }
    }
    run_tests(
        "(declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun r () Bool)
        (declare-fun a () Int)
        (declare-fun b () Int)",
        &[
            ("(and p q r)", &["p", "q", "r"]),
            ("(= a b)", &["a", "b"]),
            ("(= b b)", &["b"]),
            ("(forall ((a Int) (b Int)) (= a b))", &[]),
            ("(forall ((a Int)) (= a b))", &["b"]),
            ("(forall ((a Int)) (forall ((b Int)) (= a b)))", &[]),
            ("(and (forall ((a Int)) (= a 0)) (= a 0))", &["a"]),
            ("(and (= a 0) (forall ((a Int)) (= a 0)))", &["a"]),
        ],
    );
}

#[test]
fn test_polyeq() {
    enum TestType {
        ModReordering,
        AlphaEquiv,
        ModNary,
    }

    fn run_tests(definitions: &str, cases: &[(&str, &str)], test_type: TestType) {
        let mut pool = PrimitivePool::new();
        for (i, (a, b)) in cases.iter().enumerate() {
            let [a, b] = parse_terms(&mut pool, definitions, [a, b]);
            let mut comp = match test_type {
                TestType::ModReordering => Polyeq::new().mod_reordering(true),
                TestType::AlphaEquiv => Polyeq::new().mod_reordering(true).alpha_equiv(true),
                TestType::ModNary => Polyeq::new().mod_nary(true),
            };
            assert!(comp.eq(&a, &b), "test case #{i} failed: `{a}` != `{b}`");
        }
    }
    let definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun t () Bool)
            (declare-fun x () Int)
            (declare-fun y () Int)
        ";
    run_tests(
        definitions,
        &[
            ("(= a b)", "(= b a)"),
            ("(= p (= p (= p q)))", "(= p (= (= p q) p))"),
            (
                "(ite (= a b) (= x (+ x y)) (and p (not (= x y))))",
                "(ite (= b a) (= (+ x y) x) (and p (not (= y x))))",
            ),
        ],
        TestType::ModReordering,
    );
    run_tests(
        definitions,
        &[
            ("(= a b)", "(= b a)"),
            ("(forall ((p Bool)) p)", "(forall ((q Bool)) q)"),
            (
                "(forall ((x Int) (y Int)) (< x y))",
                "(forall ((y Int) (x Int)) (< y x))",
            ),
            (
                "(forall ((p Bool)) (forall ((q Bool)) p))",
                "(forall ((q Bool)) (forall ((p Bool)) q))",
            ),
            (
                "(choice ((x Int)) (forall ((y Int)) (exists ((z Int)) (= x y z))))",
                "(choice ((a Int)) (forall ((b Int)) (exists ((c Int)) (= a b c))))",
            ),
            (
                "(let ((x 0)) (let ((y (+ x 2))) (let ((z (< x y))) (and z (= x y)))))",
                "(let ((z 0)) (let ((x (+ z 2))) (let ((y (< z x))) (and y (= z x)))))",
            ),
        ],
        TestType::AlphaEquiv,
    );
    run_tests(
        definitions,
        &[
            // Chainable
            ("(= p q r s)", "(and (= p q) (= q r) (= r s))"),
            ("(and (= p q) (= q r) (= r s))", "(= p q r s)"),
            // Left-associative
            ("(and (and (and p q) r) s)", "(and p q r s)"),
            ("(and p q r s)", "(and (and (and p q) r) s)"),
            ("(and (and (and p q) r) s t)", "(and (and (and p q r) s) t)"),
            // Right-associative
            ("(=> p (=> q (=> r s)))", "(=> p q r s)"),
            ("(=> p q r s)", "(=> p (=> q (=> r s)))"),
            ("(=> p q (=> r (=> s t)))", "(=> p (=> q (=> r s t)))"),
            // Singleton cases
            ("(and p)", "p"),
            ("(and (and (and p)))", "p"),
            ("(and p)", "(and (and (and p)))"),
            ("(and (and p q))", "(and p q)"),
        ],
        TestType::ModNary,
    );
}

/// Added in Clean: a `Polyeq` caches the pairs it finds unequal as well as the equal ones, under the
/// same scope rule (see `PolyeqComparable for Rc<Term>`). Caching only equalities, two shared
/// chains `E_i = (= E_(i-1) E_(i-1))` that differ at the bottom took time doubling with each level:
/// each equality is tried in both orientations, and the failing sub-pair was compared again on
/// every path. Under alpha-equivalence, an answer found inside a binder is not reused outside it,
/// nor one found outside reused inside, in either direction.
#[test]
fn polyeq_caches_unequal_pairs_within_their_scope() {
    use super::{Operator, Rc, Term};

    let definitions = "(declare-fun k () Int) (declare-fun m () Int) (declare-fun j () Int)
                       (declare-fun y () Int) (declare-fun z () Int)";
    let mut pool = PrimitivePool::new();
    let [e, f, g] = parse_terms(&mut pool, definitions, ["(= k m)", "(= k j)", "(= m k)"]);
    let chain = |pool: &mut PrimitivePool, mut t: Rc<Term>| {
        for _ in 0..64 {
            t = pool.add(Term::Op(Operator::Equals, vec![t.clone(), t]));
        }
        t
    };
    let (e, f, g) = (
        chain(&mut pool, e),
        chain(&mut pool, f),
        chain(&mut pool, g),
    );
    for alpha in [false, true] {
        let comparator = || Polyeq::new().mod_reordering(true).alpha_equiv(alpha);
        assert!(!comparator().eq(&e, &f), "alpha {alpha}");
        assert!(comparator().eq(&e, &g), "alpha {alpha}");
    }

    let [p, q, bound_y, bound_z, r, bound_r] = parse_terms(
        &mut pool,
        definitions,
        [
            "(= y 1)",
            "(= 1 y)",
            "(forall ((y Int)) (= y 1))",
            "(forall ((z Int)) (= 1 y))",
            "(= 1 z)",
            "(forall ((z Int)) (= 1 z))",
        ],
    );
    // `(= y 1)` and `(= 1 y)` are unequal under binders of `y` on one side only, and equal outside.
    let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
    assert!(!comp.eq(&bound_y, &bound_z));
    assert!(comp.eq(&p, &q));
    // `(= y 1)` and `(= 1 z)` are unequal outside, and equal under binders of `y` and `z`.
    let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
    assert!(!comp.eq(&p, &r));
    assert!(comp.eq(&bound_y, &bound_r));
}

/// Added in Clean: two chains of conjunctions of sibling binders over the level below, `depth`
/// deep, the two sides named apart: `a_i = (and (forall ((x Int)) a_(i-1)) (forall ((y Int))
/// a_(i-1)))` against the same over `z` and `w`. `shape` picks the variant (see the test below);
/// `fresh` names each level's variables apart from every other level's (`xi`, `yi`, `zi`, `wi`).
fn sibling_chains(pool: &mut PrimitivePool, shape: &str, depth: usize) -> (Rc<Term>, Rc<Term>) {
    use super::{Binder, BindingList, Operator, Rc, Sort, Term};

    let int = pool.add_sort(Sort::Int);
    let boolean = pool.add_sort(Sort::Bool);
    let var = |pool: &mut PrimitivePool, name: &str, sort: &Rc<Sort>| {
        pool.add(Term::Var(name.to_owned(), sort.clone()))
    };
    let zero = pool.add(Term::new_int(0));
    let leaf = |pool: &mut PrimitivePool, name: &str| {
        let v = var(pool, name, &int);
        pool.add(Term::Op(Operator::Equals, vec![v, zero.clone()]))
    };
    // The sibling binders' variables and sorts on each side, and each side's leaf.
    let (a_vars, b_vars, a_leaf, b_leaf) = match shape {
        "equal" | "differ" | "fresh" => (
            [("x", &int), ("y", &int)],
            [("z", &int), ("w", &int)],
            var(pool, "p", &boolean),
            var(pool, if shape == "differ" { "q" } else { "p" }, &boolean),
        ),
        "sorts" => (
            [("x", &int), ("y", &boolean)],
            [("z", &int), ("w", &boolean)],
            var(pool, "p", &boolean),
            var(pool, "p", &boolean),
        ),
        "outer" => (
            [("x", &int), ("y", &int)],
            [("z", &int), ("w", &int)],
            leaf(pool, "v"),
            leaf(pool, "t"),
        ),
        "shadow" | "shadow_alike" => (
            [("x", &int), ("v", &int)],
            [
                ("z", &int),
                (if shape == "shadow" { "w" } else { "t" }, &int),
            ],
            leaf(pool, "v"),
            leaf(pool, "t"),
        ),
        _ => unreachable!("{shape}"),
    };
    // `differ` joins the siblings with `=`, which the comparison tries in both orientations.
    let op = if shape == "differ" {
        Operator::Equals
    } else {
        Operator::And
    };
    let level =
        |pool: &mut PrimitivePool, i: usize, vars: [(&str, &Rc<Sort>); 2], below: &Rc<Term>| {
            let siblings = vars.map(|(name, sort)| {
                let name = if shape == "fresh" {
                    format!("{name}{i}")
                } else {
                    name.to_owned()
                };
                let binding = BindingList(vec![(name, sort.clone())]);
                pool.add(Term::Binder(Binder::Forall, binding, below.clone()))
            });
            pool.add(Term::Op(op, siblings.to_vec()))
        };
    let (mut a, mut b) = (a_leaf, b_leaf);
    for i in 0..depth {
        a = level(pool, i, a_vars, &a);
        b = level(pool, i, b_vars, &b);
    }
    if matches!(shape, "outer" | "shadow" | "shadow_alike") {
        let bind = |pool: &mut PrimitivePool, name: &str, inner: &Rc<Term>| {
            let binding = BindingList(vec![(name.to_owned(), int.clone())]);
            pool.add(Term::Binder(Binder::Forall, binding, inner.clone()))
        };
        (a, b) = (bind(pool, "v", &a), bind(pool, "t", &b));
    }
    (a, b)
}

/// Added in Clean: under alpha-equivalence, an answer found under a binder is reused under its
/// siblings wherever the names it read are bound as they were. Upstream reused an answer only
/// under the binder it was found under, and Clean's fix 10 kept that: each level compared the
/// level below once per sibling, so these chains 64 deep took `2^64` comparisons (26 deep, 55 s;
/// without the change this test does not finish). Each answer is also the oracle's on chains 6
/// deep: `shadow` is not alpha-equivalent only because a second sibling rebinds the name its
/// leaves read on one side, so reusing the first sibling's answer there would accept it; `sorts`
/// binds an `Int` and a `Bool` sibling; `outer`'s leaves read a name bound above every sibling;
/// `fresh` binds names no other level binds, each first bound under the level above.
#[test]
fn alpha_equivalence_reuses_answers_across_sibling_binders() {
    use super::polyeq::oracle;

    for (shape, equal) in [
        ("equal", true),
        ("fresh", true),
        ("differ", false),
        ("sorts", true),
        ("outer", true),
        ("shadow", false),
        ("shadow_alike", true),
    ] {
        let mut pool = PrimitivePool::new();
        let (a, b) = sibling_chains(&mut pool, shape, 64);
        let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
        assert_eq!(comp.eq(&a, &b), equal, "{shape}");
        // Each level's pair and its two pairs of binders are compared once (193 comparisons for
        // `equal`). Under `shadow_alike`'s second siblings, which rebind the name the leaves read
        // on both sides, the chain below is compared again, once per level (4,356).
        let most = if shape == "shadow_alike" {
            66 * 66
        } else {
            4 * 64
        };
        assert!(
            comp.compared <= most,
            "{shape}: {} comparisons",
            comp.compared
        );

        let (a, b) = sibling_chains(&mut pool, shape, 6);
        let mut oracle = oracle::Polyeq::new().mod_reordering(true).alpha_equiv(true);
        assert_eq!(oracle.eq(&a, &b), equal, "{shape}, oracle");
        assert_eq!(
            Polyeq::new()
                .mod_reordering(true)
                .alpha_equiv(true)
                .eq(&a, &b),
            equal
        );
    }
}

/// The sixteen configurations of a comparator, as `(reordering, alpha, nary, string_concat)`.
fn configurations() -> impl Iterator<Item = [bool; 4]> {
    (0..16).map(|bits: u32| [0, 1, 2, 3].map(|bit| bits & (1 << bit) != 0))
}

fn comparator([reordering, alpha, nary, concat]: [bool; 4]) -> Polyeq {
    Polyeq::new()
        .mod_reordering(reordering)
        .alpha_equiv(alpha)
        .mod_nary(nary)
        .mod_string_concat(concat)
}

fn oracle_comparator(
    [reordering, alpha, nary, concat]: [bool; 4],
) -> super::polyeq::oracle::Polyeq {
    super::polyeq::oracle::Polyeq::new()
        .mod_reordering(reordering)
        .alpha_equiv(alpha)
        .mod_nary(nary)
        .mod_string_concat(concat)
}

/// Added in Clean: pairs where reusing an answer found under one binder under another binding of
/// the names it reads would change it -- shadowing, a name bound at different depths, sibling
/// binders over different sorts, `choice`, `lambda` and `let` binders -- each compared in all
/// sixteen configurations, alone and one after another through one comparator, answers as the
/// oracle (the comparator before the change) does, and as stated.
#[test]
fn the_comparator_answers_as_its_oracle_where_bindings_differ() {
    let definitions = "(declare-fun P (Int) Bool) (declare-fun Q (Int Int) Bool)
                       (declare-fun x () Int) (declare-fun y () Int) (declare-fun z () Int)
                       (declare-fun p () Bool) (declare-fun R (Bool) Bool)
                       (declare-fun S (Bool) Bool) (declare-fun m () Int)";
    // A conjunction reading twenty bound names, more than a comparison records reading
    // (`MAX_READS` in `ast/polyeq.rs`), under a binder of all twenty and again under a binder
    // that rebinds one of them on one side only: its answer is recorded as reading every binding.
    let wide = |prefix: &str| {
        let list: String = (1..=20).map(|i| format!("({prefix}{i} Int)")).collect();
        let reads: String = (1..=20).map(|i| format!(" (P {prefix}{i})")).collect();
        (list, format!("(and{reads})"))
    };
    let ((xs, x_reads), (ys, y_reads)) = (wide("x"), wide("y"));
    let wide_cases = [
        (
            format!("(forall ({xs}) (and {x_reads} (forall ((x5 Int)) {x_reads})))"),
            format!("(forall ({ys}) (and {y_reads} (forall ((z Int)) {y_reads})))"),
            false,
        ),
        (
            format!("(forall ({xs}) (and {x_reads} (forall ((u Int)) {x_reads})))"),
            format!("(forall ({ys}) (and {y_reads} (forall ((z Int)) {y_reads})))"),
            true,
        ),
        (
            format!("(forall ({xs}) (and {x_reads} (forall ((x5 Int)) {x_reads})))"),
            format!("(forall ({ys}) (and {y_reads} (forall ((y5 Int)) {y_reads})))"),
            true,
        ),
    ];
    let cases: &[(&str, &str, bool)] = &[
        // An occurrence bound by an inner binder on one side and by an outer one on the other.
        (
            "(forall ((x Int)) (and (P x) (forall ((x Int)) (P x))))",
            "(forall ((y Int)) (and (P y) (forall ((x Int)) (P y))))",
            false,
        ),
        (
            "(forall ((x Int)) (and (P x) (forall ((x Int)) (P x))))",
            "(forall ((y Int)) (and (P y) (forall ((z Int)) (P z))))",
            true,
        ),
        // The same name bound at different depths, the shared `(P x)` read under each.
        (
            "(and (forall ((x Int)) (P x)) (forall ((y Int)) (forall ((x Int)) (P x))))",
            "(and (forall ((z Int)) (P z)) (forall ((y Int)) (forall ((z Int)) (P y))))",
            false,
        ),
        (
            "(and (forall ((x Int)) (P x)) (forall ((y Int)) (forall ((x Int)) (Q x y))))",
            "(and (forall ((z Int)) (P z)) (forall ((x Int)) (forall ((z Int)) (Q z x))))",
            true,
        ),
        // Sibling binders over different sorts.
        (
            "(and (forall ((x Int)) (= x x)) (forall ((x Bool)) (= x x)))",
            "(and (forall ((y Int)) (= y y)) (forall ((y Bool)) (= y y)))",
            true,
        ),
        (
            "(and (forall ((x Int)) (= x x)) (forall ((x Bool)) (= x x)))",
            "(and (forall ((y Bool)) (= y y)) (forall ((y Int)) (= y y)))",
            false,
        ),
        // A shared subterm whose free name a sibling rebinds on one side only.
        (
            "(forall ((x Int)) (and (forall ((y Int)) (P x)) (forall ((x Int)) (P x))))",
            "(forall ((z Int)) (and (forall ((y Int)) (P z)) (forall ((y Int)) (P z))))",
            false,
        ),
        (
            "(forall ((x Int)) (and (forall ((y Int)) (P x)) (forall ((x Int)) (P x))))",
            "(forall ((z Int)) (and (forall ((y Int)) (P z)) (forall ((z Int)) (P z))))",
            true,
        ),
        // The same pair free outside and bound inside, both ways (fix 10).
        (
            "(and (= y 1) (forall ((y Int)) (= y 1)))",
            "(and (= 1 y) (forall ((z Int)) (= 1 y)))",
            false,
        ),
        (
            "(and (= y 1) (forall ((y Int)) (= y 1)))",
            "(and (= 1 y) (forall ((z Int)) (= 1 z)))",
            true,
        ),
        // A name read free under a binder, then bound for the first time by a later sibling on
        // one side only. An answer found while it was free may not be reused under it (`(P y)`),
        // nor the answer of the comparison whose read made it late (`y` against `y`), nor one
        // found later that relied on such an answer, directly (`(S (P y))`) or through a
        // comparison inside it (`(R (S (P y)))`), nor under a binder inside the one that binds it.
        (
            "(forall ((u Int)) (and (P y) (forall ((y Int)) (P y))))",
            "(forall ((u Int)) (and (P y) (forall ((z Int)) (P y))))",
            false,
        ),
        (
            "(forall ((u Int)) (and (P y) (forall ((y Int)) (P y))))",
            "(forall ((u Int)) (and (P y) (forall ((z Int)) (P z))))",
            true,
        ),
        (
            "(forall ((u Int)) (and (P y) (R (S (P y))) (forall ((y Int)) (R (S (P y))))))",
            "(forall ((u Int)) (and (P y) (R (S (P y))) (forall ((z Int)) (R (S (P y))))))",
            false,
        ),
        (
            "(forall ((u Int)) (and (P y) (S (P y)) (forall ((y Int)) (S (P y)))))",
            "(forall ((u Int)) (and (P y) (S (P y)) (forall ((z Int)) (S (P y)))))",
            false,
        ),
        (
            "(forall ((u Int)) (and (P y) (forall ((y Int)) (forall ((w Int)) (P y)))))",
            "(forall ((u Int)) (and (P y) (forall ((z Int)) (forall ((w Int)) (P y)))))",
            false,
        ),
        (
            "(forall ((u Int)) (and (P y) (forall ((y Int)) (forall ((w Int)) (P y)))))",
            "(forall ((u Int)) (and (P y) (forall ((z Int)) (forall ((w Int)) (P z)))))",
            true,
        ),
        // The same, where the name is read free again, and stamped again, after a name read free
        // before it was made late by its first binding: the answers found by the later read must
        // not be reused where the name is bound.
        (
            "(forall ((u Int)) (and (Q y m) (forall ((m Int)) (Q y y))
                                    (forall ((y Int)) (forall ((m Int)) (Q y y)))))",
            "(forall ((u Int)) (and (Q y m) (forall ((m Int)) (Q y y))
                                    (forall ((z Int)) (forall ((m Int)) (Q y y)))))",
            false,
        ),
        (
            "(forall ((u Int)) (and (Q y m) (forall ((m Int)) (Q y y))
                                    (forall ((y Int)) (forall ((m Int)) (Q y y)))))",
            "(forall ((u Int)) (and (Q y m) (forall ((m Int)) (Q y y))
                                    (forall ((z Int)) (forall ((m Int)) (Q z z)))))",
            true,
        ),
        // A pair found unequal under an inner binder that binds the name it reads at different
        // indices on the two sides (the first orientation of `=`), and equal outside it, where the
        // name is free: its answer is anchored at the inner level, and dropped there.
        (
            "(forall ((x Int)) (and (forall ((y Int) (t Int)) (= (Q x y) (Q x t))) (Q x y)))",
            "(forall ((w Int)) (and (forall ((t Int) (y Int)) (= (Q w y) (Q w t))) (Q w y)))",
            true,
        ),
        // `choice`, `lambda` and `let` binders.
        (
            "(choice ((x Int)) (forall ((y Int)) (Q x y)))",
            "(choice ((y Int)) (forall ((x Int)) (Q y x)))",
            true,
        ),
        (
            "(choice ((x Int)) (forall ((y Int)) (Q x y)))",
            "(choice ((y Int)) (forall ((x Int)) (Q x y)))",
            false,
        ),
        (
            "(= (lambda ((x Int)) (+ x y)) (lambda ((z Int)) (+ z y)))",
            "(= (lambda ((z Int)) (+ z y)) (lambda ((x Int)) (+ x y)))",
            true,
        ),
        (
            "(lambda ((x Int)) (+ x y))",
            "(lambda ((y Int)) (+ y y))",
            false,
        ),
        (
            "(let ((x 1) (y x)) (+ x y))",
            "(let ((z 1) (y z)) (+ z y))",
            false,
        ),
        (
            "(let ((x 1) (y z)) (+ x y))",
            "(let ((z 1) (y z)) (+ z y))",
            true,
        ),
        (
            "(let ((x z)) (let ((x (+ x 1)) (y x)) (Q x y)))",
            "(let ((y z)) (let ((z (+ y 1)) (y y)) (Q z y)))",
            true,
        ),
        (
            "(let ((x z)) (let ((x (+ x 1)) (y x)) (Q x y)))",
            "(let ((y z)) (let ((z (+ y 1)) (w z)) (Q z w)))",
            false,
        ),
    ];
    let cases: Vec<(&str, &str, bool)> = cases
        .iter()
        .copied()
        .chain(
            wide_cases
                .iter()
                .map(|(a, b, equal)| (a.as_str(), b.as_str(), *equal)),
        )
        .collect();
    let mut pool = PrimitivePool::new();
    let pairs: Vec<_> = cases
        .iter()
        .map(|(a, b, _)| parse_terms(&mut pool, definitions, [*a, *b]))
        .collect();
    let mut reading_all = 0;
    for config in configurations() {
        let mut session = comparator(config);
        let mut oracle_session = oracle_comparator(config);
        for (i, [a, b]) in pairs.iter().enumerate() {
            let expected = oracle_comparator(config).eq(a, b);
            if config == [true, true, false, false] {
                assert_eq!(expected, cases[i].2, "case {i}: oracle");
            }
            let mut fresh = comparator(config);
            assert_eq!(fresh.eq(a, b), expected, "case {i} under {config:?}");
            reading_all += fresh.answers_reading_all;
            assert_eq!(
                session.eq(a, b),
                expected,
                "case {i} under {config:?}, in turn"
            );
            assert_eq!(
                oracle_session.eq(a, b),
                expected,
                "case {i}, oracle in turn"
            );
            // Each side against itself, and the pair reversed.
            for (a, b) in [(a, a), (b, b), (b, a)] {
                let expected = oracle_comparator(config).eq(a, b);
                assert_eq!(
                    comparator(config).eq(a, b),
                    expected,
                    "case {i} under {config:?}"
                );
                assert_eq!(
                    session.eq(a, b),
                    expected,
                    "case {i} under {config:?}, in turn"
                );
            }
        }
    }
    assert!(reading_all > 0);
}

/// Added in Clean: random terms over few names (so binders shadow, rebind and capture them), of
/// four sorts, with `forall`, `exists`, `choice`, `lambda`, `let` and `match` binders, sharing
/// subterms across binders, for the comparator's differential test.
struct RandomTerms<'p> {
    pool: &'p mut PrimitivePool,
    rng: rand::rngs::StdRng,
    /// Terms built so far, by sort, to share.
    built: [Vec<Rc<Term>>; 4],
    /// The names binders bind, and the most variables a binder binds.
    names: &'static [&'static str],
    widest: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Bool = 0,
    Int = 1,
    Real = 2,
    Str = 3,
}

impl RandomTerms<'_> {
    const FEW: [&'static str; 6] = ["x", "y", "z", "w", "u", "v"];
    /// More names than a comparison records reading (`MAX_READS` in `ast/polyeq.rs`).
    const MANY: [&'static str; 24] = [
        "x", "y", "z", "w", "u", "v", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "y1",
        "y2", "y3", "y4", "y5", "y6", "y7", "y8", "y9",
    ];

    fn sort(&mut self, kind: Kind) -> Rc<super::Sort> {
        use super::Sort;
        self.pool.add_sort(match kind {
            Kind::Bool => Sort::Bool,
            Kind::Int => Sort::Int,
            Kind::Real => Sort::Real,
            Kind::Str => Sort::String,
        })
    }

    fn chance(&mut self, p: f64) -> bool {
        use rand::Rng;
        self.rng.gen_bool(p)
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        use rand::Rng;
        &items[self.rng.gen_range(0..items.len())]
    }

    fn var(&mut self, name: &str, kind: Kind) -> Rc<Term> {
        let sort = self.sort(kind);
        self.pool.add(Term::Var(name.to_owned(), sort))
    }

    /// A variable of sort `kind`: one bound around it, mostly, or a free one; sometimes a name
    /// bound around it at another sort.
    fn leaf_var(&mut self, kind: Kind, scope: &[(&'static str, Kind)]) -> Rc<Term> {
        let bound: Vec<_> = scope.iter().filter(|(_, k)| *k == kind).collect();
        if !bound.is_empty() && self.chance(0.7) {
            let &&(name, _) = self.pick(&bound);
            return self.var(name, kind);
        }
        let free: &[&str] = match kind {
            Kind::Bool => &["p", "q", "x"],
            Kind::Int => &["x", "y", "z", "a"],
            Kind::Real => &["r", "w"],
            Kind::Str => &["s", "y"],
        };
        let name = *self.pick(free);
        self.var(name, kind)
    }

    fn leaf(&mut self, kind: Kind, scope: &[(&'static str, Kind)]) -> Rc<Term> {
        use super::Operator;
        use rand::Rng;
        if self.chance(0.5) {
            return self.leaf_var(kind, scope);
        }
        match kind {
            Kind::Bool => {
                let value = self.chance(0.5);
                self.pool.add(Term::new_bool(value))
            }
            Kind::Int => {
                let n = self.rng.gen_range(-1i64..3);
                self.pool.add(Term::new_int(n))
            }
            Kind::Real => {
                let (n, d) = (self.rng.gen_range(-2i64..3), self.rng.gen_range(1i64..3));
                match self.rng.gen_range(0..3) {
                    0 => self.pool.add(Term::new_real(rug::Rational::from((n, d)))),
                    1 => {
                        let (n, d) = (Term::new_int(n.abs()), Term::new_int(d));
                        let (n, d) = (self.pool.add(n), self.pool.add(d));
                        let n = if self.chance(0.3) {
                            self.pool.add(Term::Op(Operator::Sub, vec![n]))
                        } else {
                            n
                        };
                        self.pool.add(Term::Op(Operator::RealDiv, vec![n, d]))
                    }
                    _ => {
                        let r = self
                            .pool
                            .add(Term::new_real(rug::Rational::from((n.abs(), d))));
                        self.pool.add(Term::Op(Operator::Sub, vec![r]))
                    }
                }
            }
            Kind::Str => {
                let s = *self.pick(&["", "a", "b", "ab"]);
                self.pool.add(Term::new_string(s))
            }
        }
    }

    /// A binding list of one or two variables of random sorts and names.
    fn bindings(&mut self) -> Vec<(&'static str, Kind)> {
        use rand::Rng;
        let n = if self.chance(0.6) {
            1
        } else {
            self.rng.gen_range(2..=self.widest)
        };
        (0..n)
            .map(|_| {
                let names = self.names;
                let name = *self.pick(&names[..names.len() - 2]);
                let kind = *self.pick(&[Kind::Int, Kind::Int, Kind::Bool, Kind::Real]);
                (name, kind)
            })
            .collect()
    }

    fn binding_list(&mut self, vars: &[(&'static str, Kind)]) -> super::BindingList {
        super::BindingList(
            vars.iter()
                .map(|&(name, kind)| (name.to_owned(), self.sort(kind)))
                .collect(),
        )
    }

    fn term(
        &mut self,
        kind: Kind,
        depth: usize,
        scope: &mut Vec<(&'static str, Kind)>,
    ) -> Rc<Term> {
        use super::{Binder, MatchCase, MatchPattern, Operator};
        use rand::Rng;

        if depth == 0 || self.chance(0.2) {
            return self.leaf(kind, scope);
        }
        // A term built before, maybe under other binders: it reads its names under these.
        if !self.built[kind as usize].is_empty() && self.chance(0.3) {
            let built = self.built[kind as usize].clone();
            return self.pick(&built).clone();
        }
        let d = depth - 1;
        let term = match kind {
            Kind::Bool => match self.rng.gen_range(0..14) {
                0 => {
                    let a = self.term(Kind::Bool, d, scope);
                    Term::Op(Operator::Not, vec![a])
                }
                1 | 2 => {
                    let n = self.rng.gen_range(1..4);
                    let op = *self.pick(&[Operator::And, Operator::Or]);
                    let args = (0..n).map(|_| self.term(Kind::Bool, d, scope)).collect();
                    Term::Op(op, args)
                }
                3 | 4 => {
                    let k = *self.pick(&[Kind::Int, Kind::Bool, Kind::Real, Kind::Str]);
                    let (a, b) = (self.term(k, d, scope), self.term(k, d, scope));
                    Term::Op(Operator::Equals, vec![a, b])
                }
                5 => {
                    let (a, b) = (
                        self.term(Kind::Int, d, scope),
                        self.term(Kind::Int, d, scope),
                    );
                    Term::Op(Operator::LessThan, vec![a, b])
                }
                6 => {
                    let c = self.term(Kind::Bool, d, scope);
                    let (a, b) = (
                        self.term(Kind::Bool, d, scope),
                        self.term(Kind::Bool, d, scope),
                    );
                    Term::Op(Operator::Ite, vec![c, a, b])
                }
                7..=9 => {
                    let vars = self.bindings();
                    let list = self.binding_list(&vars);
                    let len = scope.len();
                    scope.extend(&vars);
                    let inner = self.term(Kind::Bool, d, scope);
                    scope.truncate(len);
                    let binder = *self.pick(&[Binder::Forall, Binder::Exists]);
                    Term::Binder(binder, list, inner)
                }
                10 | 11 => {
                    let vars = self.bindings();
                    let values: Vec<_> =
                        vars.iter().map(|&(_, k)| self.term(k, d, scope)).collect();
                    let len = scope.len();
                    scope.extend(&vars);
                    let inner = self.term(Kind::Bool, d, scope);
                    scope.truncate(len);
                    let list = vars
                        .iter()
                        .zip(values)
                        .map(|(&(n, _), v)| (n.to_owned(), v));
                    Term::Let(super::BindingList(list.collect()), inner)
                }
                12 => {
                    let f_sort = {
                        let (int, boolean) = (self.sort(Kind::Int), self.sort(Kind::Bool));
                        self.pool
                            .add_sort(super::Sort::Function(vec![int, boolean]))
                    };
                    let f = self.pool.add(Term::Var("f".to_owned(), f_sort));
                    let arg = self.term(Kind::Int, d, scope);
                    Term::App(f, vec![arg])
                }
                _ => {
                    // A `match` on an integer, binding a name in its one case.
                    let scrutinee = self.term(Kind::Int, d, scope);
                    let (name, int) = (*self.pick(self.names), self.sort(Kind::Int));
                    scope.push((name, Kind::Int));
                    let body = self.term(Kind::Bool, d, scope);
                    scope.pop();
                    let pattern = MatchPattern::Variable((name.to_owned(), int));
                    Term::Match(scrutinee, vec![MatchCase { pattern, body }])
                }
            },
            Kind::Int => match self.rng.gen_range(0..6) {
                0 | 1 => {
                    let n = self.rng.gen_range(1..4);
                    let op = *self.pick(&[Operator::Add, Operator::Sub]);
                    let args = (0..n).map(|_| self.term(Kind::Int, d, scope)).collect();
                    Term::Op(op, args)
                }
                2 => {
                    let c = self.term(Kind::Bool, d, scope);
                    let (a, b) = (
                        self.term(Kind::Int, d, scope),
                        self.term(Kind::Int, d, scope),
                    );
                    Term::Op(Operator::Ite, vec![c, a, b])
                }
                3 => {
                    let name = *self.pick(self.names);
                    let list = self.binding_list(&[(name, Kind::Int)]);
                    scope.push((name, Kind::Int));
                    let inner = self.term(Kind::Bool, d, scope);
                    scope.pop();
                    Term::Binder(Binder::Choice, list, inner)
                }
                4 => {
                    let name = *self.pick(self.names);
                    let list = self.binding_list(&[(name, Kind::Int)]);
                    scope.push((name, Kind::Int));
                    let body = self.term(Kind::Int, d, scope);
                    scope.pop();
                    let lambda = self.pool.add(Term::Binder(Binder::Lambda, list, body));
                    let arg = self.term(Kind::Int, d, scope);
                    Term::App(lambda, vec![arg])
                }
                _ => return self.leaf(kind, scope),
            },
            Kind::Real => {
                let n = self.rng.gen_range(1..3);
                let args = (0..n).map(|_| self.term(Kind::Real, d, scope)).collect();
                Term::Op(Operator::Add, args)
            }
            Kind::Str => {
                let n = self.rng.gen_range(1..4);
                let args = (0..n).map(|_| self.term(Kind::Str, d, scope)).collect();
                Term::Op(Operator::StrConcat, args)
            }
        };
        let term = self.pool.add(term);
        self.built[kind as usize].push(term.clone());
        term
    }

    /// `term` with the variables of some binders renamed, consistently or not (a new name may
    /// capture one read inside), and now and then an equality flipped, a leaf changed, or a
    /// conjunction regrouped: a pair that is often, and not always, equivalent.
    fn variant(&mut self, term: &Rc<Term>, renamed: &mut Vec<(String, String)>) -> Rc<Term> {
        use super::{BindingList, Operator};
        let rename_list = |this: &mut Self, list: &[(String, Rc<super::Sort>)]| {
            list.iter()
                .map(|(name, sort)| {
                    let new = if this.chance(0.6) {
                        (*this.pick(this.names)).to_owned()
                    } else {
                        name.clone()
                    };
                    (name.clone(), new, sort.clone())
                })
                .collect::<Vec<_>>()
        };
        let new = match term.as_ref() {
            Term::Var(name, sort) => {
                if self.chance(0.03) {
                    let other = *self.pick(&["x", "y", "p"]);
                    Term::Var(other.to_owned(), sort.clone())
                } else {
                    let to = renamed.iter().rev().find(|(from, _)| from == name);
                    Term::Var(to.map_or(name, |(_, to)| to).clone(), sort.clone())
                }
            }
            Term::Const(_) => return term.clone(),
            Term::Op(op, args) => {
                let mut args: Vec<_> = args.iter().map(|a| self.variant(a, renamed)).collect();
                if *op == Operator::Equals && args.len() == 2 && self.chance(0.2) {
                    args.swap(0, 1);
                }
                if matches!(op, Operator::And | Operator::Or) && args.len() > 2 && self.chance(0.2)
                {
                    let rest = args.split_off(1);
                    let rest = self.pool.add(Term::Op(*op, rest));
                    args.push(rest);
                }
                Term::Op(*op, args)
            }
            Term::App(f, args) => {
                let f = self.variant(f, renamed);
                Term::App(f, args.iter().map(|a| self.variant(a, renamed)).collect())
            }
            Term::Binder(binder, list, inner) => {
                let names = rename_list(self, &list.0);
                let len = renamed.len();
                renamed.extend(names.iter().map(|(from, to, _)| (from.clone(), to.clone())));
                let inner = self.variant(inner, renamed);
                renamed.truncate(len);
                let list = names.into_iter().map(|(_, to, sort)| (to, sort)).collect();
                Term::Binder(*binder, BindingList(list), inner)
            }
            Term::Let(list, inner) => {
                let values: Vec<_> = list.iter().map(|(_, v)| self.variant(v, renamed)).collect();
                let names: Vec<_> = list
                    .iter()
                    .map(|(name, _)| {
                        let new = if self.chance(0.6) {
                            (*self.pick(self.names)).to_owned()
                        } else {
                            name.clone()
                        };
                        (name.clone(), new)
                    })
                    .collect();
                let len = renamed.len();
                renamed.extend(names.iter().cloned());
                let inner = self.variant(inner, renamed);
                renamed.truncate(len);
                let list = names.into_iter().map(|(_, to)| to).zip(values).collect();
                Term::Let(BindingList(list), inner)
            }
            Term::Match(..) | Term::ParamOp { .. } | Term::AsOp(..) => return term.clone(),
        };
        self.pool.add(new)
    }
}

/// Added in Clean: the comparator holds to its oracle, the comparator before answers found under
/// binders were reused across them, on random pairs of terms (see `RandomTerms`) in all sixteen
/// configurations, each pair alone and all of them one after another through one comparator.
#[test]
fn the_comparator_answers_as_its_oracle_on_random_terms() {
    use rand::SeedableRng;

    let (mut pairs_seen, mut equal_seen, mut bound_seen) = (0, 0, 0);
    for seed in 0..160u64 {
        let mut pool = PrimitivePool::new();
        let mut terms = RandomTerms {
            pool: &mut pool,
            rng: rand::rngs::StdRng::seed_from_u64(seed),
            built: Default::default(),
            // A quarter of the seeds bind many names, up to six at a time, so that comparisons
            // read many bound names and rebind few.
            names: if seed % 4 == 3 {
                &RandomTerms::MANY
            } else {
                &RandomTerms::FEW
            },
            widest: if seed % 4 == 3 { 6 } else { 2 },
        };
        let roots: Vec<_> = (0..8)
            .map(|_| terms.term(Kind::Bool, 6, &mut Vec::new()))
            .collect();
        let mut pairs = Vec::new();
        for (i, root) in roots.iter().enumerate() {
            pairs.push((root.clone(), root.clone()));
            for _ in 0..3 {
                pairs.push((root.clone(), terms.variant(root, &mut Vec::new())));
            }
            pairs.push((root.clone(), roots[(i + 1) % roots.len()].clone()));
        }
        // Pairs of shared subterms too, which the comparisons above also meet under binders.
        for kind in [Kind::Bool, Kind::Int, Kind::Real, Kind::Str] {
            let built = terms.built[kind as usize].clone();
            for chunk in built.chunks(2).take(12) {
                if let [a, b] = chunk {
                    pairs.push((a.clone(), terms.variant(a, &mut Vec::new())));
                    pairs.push((a.clone(), b.clone()));
                }
            }
        }
        for config in configurations() {
            let mut session = comparator(config);
            for (a, b) in &pairs {
                let expected = oracle_comparator(config).eq(a, b);
                let mut fresh = comparator(config);
                assert_eq!(
                    fresh.eq(a, b),
                    expected,
                    "seed {seed} {config:?}: {a} vs {b}"
                );
                assert_eq!(
                    session.eq(a, b),
                    expected,
                    "seed {seed} {config:?} in turn: {a} vs {b}"
                );
                pairs_seen += 1;
                equal_seen += usize::from(expected);
                bound_seen += usize::from(fresh.decided_under_binders() > 0);
            }
        }
    }
    // The pairs are not all equal, nor all unequal, and many are compared under binders.
    assert!(equal_seen * 5 > pairs_seen && equal_seen * 5 < pairs_seen * 4);
    assert!(bound_seen * 10 > pairs_seen, "{bound_seen} of {pairs_seen}");
}

/// Added in Clean: a comparison costs what it compares. The comparator once numbered every name a
/// binder of the two terms binds before entering the first binder, walking both terms whole in
/// every comparison, and `refl` builds a comparator for each of the up to four comparisons of a
/// step: steps comparing `(forall ((z Int)) (or (= x z) H))` with `(forall ((z Int)) (or (= y z)
/// H))`, which differ at `x` and `y`, each walked all of `H` (10,000 such steps over an `H` of
/// 10,000 atoms took 18.7 s, against 0.06 s before). A name is now numbered when it is first bound.
#[test]
fn alpha_equivalence_refused_at_its_first_argument_costs_only_what_it_compared() {
    let definitions = "(declare-fun c () Int) (declare-fun x () Int) (declare-fun y () Int)";
    let mut pool = PrimitivePool::new();
    let mut cost = Vec::new();
    for atoms in [1_000, 4_000] {
        let h: String = (1..=atoms).map(|i| format!(" (= c {i})")).collect();
        let [left, right] = parse_terms(
            &mut pool,
            definitions,
            [
                &format!("(forall ((z Int)) (or (= x z) (or{h})))"),
                &format!("(forall ((z Int)) (or (= y z) (or{h})))"),
            ],
        );
        let mut total = 0;
        for _ in 0..8 {
            let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
            assert!(!comp.eq(&left, &right));
            total += comp.compared + comp.work;
        }
        cost.push(total);
    }
    assert_eq!(cost[0], cost[1], "the cost grows with H: {cost:?}");
    assert!(cost[0] <= 8 * 16, "{cost:?}");
}

/// `depth` levels `A_i = (forall ((v Int)) (and PS A_(i-1)))` over `A_0 = PS`, where `PS = (and P1
/// .. Pn)` and `Pk = (= (+ o1 .. o7 v) k)`, under a binder of `o1 .. o7`; against the same over
/// `q1 .. q7`, whose deepest `PS` has `k + offset` for `k`.
fn rebinding_levels(
    pool: &mut PrimitivePool,
    depth: usize,
    conjuncts: usize,
    offset: usize,
) -> [Rc<Term>; 2] {
    let side = |prefix: &str, offset: usize| {
        let vars: Vec<String> = (1..=7).map(|i| format!("{prefix}{i}")).collect();
        let sum = vars.join(" ");
        let ps = |offset: usize| {
            let conjuncts: String = (1..=conjuncts)
                .map(|k| format!(" (= (+ {sum} v) {})", k + offset))
                .collect();
            format!("(and{conjuncts})")
        };
        let mut term = ps(offset);
        for _ in 0..depth {
            term = format!("(forall ((v Int)) (and {} {term}))", ps(0));
        }
        let binders: String = vars.iter().map(|var| format!(" ({var} Int)")).collect();
        format!("(forall ({binders}) {term})")
    };
    parse_terms(pool, "", [&side("o", 0), &side("q", offset)])
}

/// Added in Clean: a lookup examines at most a few answers of its pair. Each `Pk` of
/// `rebinding_levels` reads `v`, which every level rebinds, so its pair is compared once per level
/// and gets an answer there; the comparator once kept them all while their levels were open and
/// examined every one on each lookup, so `d` levels of `n` conjuncts cost `n * d^2` (1,000 of
/// 1,000 took 12.6 s, against 0.25 s before). Past `MAX_ANSWERS` answers for a pair, the outermost
/// is dropped now.
#[test]
fn a_lookup_examines_few_answers_where_a_name_it_reads_is_rebound_at_every_level() {
    use super::polyeq::oracle;

    let mut pool = PrimitivePool::new();
    let mut cost = Vec::new();
    for depth in [32, 64] {
        let [a, b] = rebinding_levels(&mut pool, depth, 8, 0);
        let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
        assert!(comp.eq(&a, &b));
        cost.push(comp.compared + comp.work);
    }
    // Twice the levels, twice the pairs to compare, and about twice the work.
    assert!(cost[1] * 2 <= cost[0] * 5, "{cost:?}");
    // The answers are the oracle's, where the two differ at the deepest level only.
    for offset in [0, 1] {
        let [a, b] = rebinding_levels(&mut pool, 8, 3, offset);
        let expected = oracle::Polyeq::new()
            .mod_reordering(true)
            .alpha_equiv(true)
            .eq(&a, &b);
        assert_eq!(expected, offset == 0);
        let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
        assert_eq!(comp.eq(&a, &b), expected, "offset {offset}");
    }
}

/// `(and (forall ((x0 Int)) (and (= c 1) .. (= c atoms))) (forall ((x1 Int)) p) .. (forall
/// ((xn Int)) p))`, `n` being `siblings`, against the same over `y0 .. yn`.
fn new_names_at_every_sibling(
    pool: &mut PrimitivePool,
    atoms: usize,
    siblings: usize,
) -> [Rc<Term>; 2] {
    let big: String = (1..=atoms).map(|i| format!(" (= c {i})")).collect();
    let side = |var: &str| {
        let rest: String = (1..=siblings)
            .map(|k| format!(" (forall (({var}{k} Int)) p)"))
            .collect();
        format!("(and (forall (({var}0 Int)) (and{big})){rest})")
    };
    let definitions = "(declare-fun c () Int) (declare-fun p () Bool)";
    parse_terms(pool, definitions, [&side("x"), &side("y")])
}

/// Added in Clean: answers found under a binder outlive its siblings, which bind names never bound
/// before. The comparator once numbered the names a top-level binder binds as it entered it, and
/// dropped every answer it held if one was new, by clearing a table whose capacity it kept: each
/// later sibling paid for all the first one had found (`atoms` of 10^6 under 10^5 siblings took
/// 19.1 s, against 2.2 s before). Nothing is dropped now, and a table is replaced, not cleared.
#[test]
fn answers_found_under_a_binder_outlive_siblings_that_bind_new_names() {
    let mut pool = PrimitivePool::new();
    let mut cost = Vec::new();
    for size in [200, 400] {
        let [a, b] = new_names_at_every_sibling(&mut pool, size, size);
        let mut comp = Polyeq::new().mod_reordering(true).alpha_equiv(true);
        assert!(comp.eq(&a, &b));
        assert!(
            comp.decided_under_binders() > size,
            "{} answers held",
            comp.decided_under_binders()
        );
        cost.push(comp.compared + comp.work);
    }
    // Twice the atoms and twice the siblings, about twice the work.
    assert!(cost[1] * 2 <= cost[0] * 5, "{cost:?}");
}

#[test]
fn test_node() {
    use crate::parser::tests::*;

    let original = "
        (assume h0 (= 0 0))
        (assume h1 (= 1 1))
        (assume h2 (= 2 2))
        (step t3 (cl true) :rule blah :premises (h0 h2))
        (step t4 (cl true) :rule blah)
        (anchor :step t5)
            (assume t5.h1 (= 3 3))
            (step t5.t2 (cl true) :rule blah :premises (t4))
            (step t5.t3 (cl true) :rule blah)
            (step t5.t4 (cl true) :rule blah)
            (step t5 (cl true) :rule blah :premises (t5.t2) :discharge (t5.h1))
        (step t6 (cl) :rule blah :premises (t3 t5))
    ";
    let mut pool = PrimitivePool::new();
    let original = parse_proof(&mut pool, original);

    let node = ProofNodeForest::from_commands(original.commands.clone());
    let got = node.into_commands();
    assert_eq!(original.commands, got);
}

// Added in Clean (not part of upstream Carcara): the free variables of a chain's links cost memory
// linear in its length, by each route that asks for them, and so do two chains merged at every
// link (since 2026-10-16), also with each link in binders of its own; and `bfun_elim`'s walk over
// nested quantifiers is linear in their depth. Upstream cached an `IndexSet` per term, so a chain of `n` links over distinct
// constants cached `n^2 / 2` entries: 10,000 links took 1.75 GB. These tests check the
// verdicts end to end at sizes the quadratic code also finished (2,000 links: under 100 MB); the
// costs are held where they can be counted as they grow, so that a regression fails at once rather
// than exhaust the machine: the sets' nodes (`ast/pool/free_vars.rs`,
// `a_chains_sets_share_structure`), the walk's subterms (`checker/rules/clausification.rs`,
// `the_mentions_walk_skips_what_holds_none_of_the_names`) and its sets' fuel
// (`names_below_spend_their_fuel_on_chains_merged_apart`), the merges of two chains
// (`two_chains_merged_at_every_link_cost_a_few_paths_a_link`) and the capture checks' answers
// (`parser/tests.rs`, `capture_checks_carry_their_answers_into_scopes_entered_inside`). See
// third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure" and "Nested quantifiers
// named apart".

use carcara::{checker, parser};

/// Parses and checks on a thread with Clean's adapter's 1 GiB stack, as the adapter does.
fn check(problem: String, proof: String, config: parser::Config) -> Result<bool, String> {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let (problem, proof, rules, mut pool) =
                parser::parse_instance(&problem, &proof, None, config)
                    .map_err(|e| e.to_string())?;
            checker::ProofChecker::new(&mut pool, &rules, checker::Config::new())
                .check(&problem, &proof)
                .map(|holey| !holey)
                .map_err(|e| e.to_string())
        })
        .unwrap()
        .join()
        .unwrap()
}

const CONTRADICTION: &str =
    "(assume h1 p)(assume h2 (not p))(step tz (cl) :rule resolution :premises (h1 h2))";

fn declarations(n: usize) -> String {
    let mut text = "(set-logic ALL)(declare-const p Bool)".to_owned();
    for j in 0..=n {
        text.push_str(&format!("(declare-const c{j} (_ BitVec 8))"));
    }
    text
}

/// The links `e_j = (bvadd c_j e_(j-1))`, each named where it is written.
fn named_links(n: usize) -> Vec<String> {
    let mut links = vec!["(= (! (bvadd c1 c0) :named e1) c0)".to_owned()];
    for j in 2..=n {
        links.push(format!("(= (! (bvadd c{j} e{}) :named e{j}) c0)", j - 1));
    }
    links
}

/// The three routes by which the pool was asked for the free variables of a chain's links: each
/// link named in the problem at top level (`check_named_term_is_closed`), the same inside one
/// `exists` (the parser's capture check of each use of a name), and the links defined in the proof
/// and read once by `qnt_rm_unused`. All are checked.
#[test]
fn chains_of_links_are_checked_by_each_route() {
    let n = 2_000;
    let end = "(assert p)(assert (not p))";
    let links = named_links(n);

    let top: String = links.iter().map(|l| format!("(assert {l})")).collect();
    let problem = format!("{}{top}{end}", declarations(n));
    let verdict = check(
        problem,
        CONTRADICTION.to_owned(),
        parser::Config::clean_dialect(),
    );
    assert_eq!(verdict, Ok(true), "named at top level");

    let problem = format!(
        "{}(assert (exists ((x Bool)) (and x {}))){end}",
        declarations(n),
        links.join(" ")
    );
    let verdict = check(
        problem,
        CONTRADICTION.to_owned(),
        parser::Config::clean_dialect(),
    );
    assert_eq!(verdict, Ok(true), "named inside an exists");

    let mut definitions = "(define-fun e1 () (_ BitVec 8) (bvadd c1 c0))".to_owned();
    for j in 2..=n {
        definitions.push_str(&format!(
            "(define-fun e{j} () (_ BitVec 8) (bvadd c{j} e{}))",
            j - 1
        ));
    }
    let proof = format!(
        "{definitions}(step t1 (cl (= (forall ((z Int)) (= e{n} c0)) (= e{n} c0))) \
         :rule qnt_rm_unused){CONTRADICTION}"
    );
    let problem = format!("{}{end}", declarations(n));
    let verdict = check(problem, proof, parser::Config::clean_dialect());
    assert_eq!(verdict, Ok(true), "read by qnt_rm_unused");
}

/// The same routes still refuse what they refused: a named link that mentions a variable bound
/// where it is named, and a `qnt_rm_unused` step removing a variable the chain mentions.
#[test]
fn chains_of_links_still_refuse_what_they_mention() {
    let n = 2_000;
    let end = "(assert p)(assert (not p))";
    let mut links = named_links(n);
    links[n / 2] = format!("(= (! (bvadd x e{}) :named e{}) c0)", n / 2, n / 2 + 1);
    let problem = format!(
        "{}(assert (exists ((x (_ BitVec 8))) (and {}))){end}",
        declarations(n),
        links.join(" ")
    );
    let verdict = check(
        problem,
        CONTRADICTION.to_owned(),
        parser::Config::clean_dialect(),
    );
    let error = verdict.expect_err("a named term mentioning a bound variable");
    assert!(
        error.contains(&format!("e{}", n / 2 + 1)) && error.contains("'x'"),
        "{error}"
    );

    let mut definitions = "(define-fun e1 () (_ BitVec 8) (bvadd z c0))".to_owned();
    for j in 2..=n {
        definitions.push_str(&format!(
            "(define-fun e{j} () (_ BitVec 8) (bvadd c{j} e{}))",
            j - 1
        ));
    }
    let proof = format!(
        "{definitions}(step t1 (cl (= (forall ((z (_ BitVec 8))) (= e{n} c0)) (= e{n} c0))) \
         :rule qnt_rm_unused){CONTRADICTION}"
    );
    let problem = format!("{}(declare-const z (_ BitVec 8)){end}", declarations(n));
    let verdict = check(problem, proof, parser::Config::clean_dialect());
    assert!(verdict.is_err(), "{verdict:?}");
}

/// `bfun_elim` over `B_k = (forall ((x Int) (b_k Bool)) (and (F b_k) (P x) B_(k-1)))`, nested
/// 2,048 deep with each level's Boolean named apart, is checked (the walk that finds which variables
/// each subterm mentions visited every level below each level: 8,192 levels took 14 s).
#[test]
fn bfun_elim_over_quantifiers_named_apart_is_checked() {
    let depth = 2_048;
    let mut problem = "(set-logic ALL)(declare-const p Bool)(declare-fun P (Int) Bool)\
                       (declare-fun F (Bool) Bool)(define-fun B0 () Bool p)(define-fun E0 () Bool p)"
        .to_owned();
    for k in 1..=depth {
        problem.push_str(&format!(
            "(define-fun B{k} () Bool (forall ((x Int) (b{k} Bool)) (and (F b{k}) (P x) B{})))\
             (define-fun E{k} () Bool (forall ((x Int)) (and (and (F false) (P x) E{}) \
             (and (F true) (P x) E{}))))",
            k - 1,
            k - 1,
            k - 1
        ));
    }
    problem.push_str(&format!("(assert B{depth})(assert (not E{depth}))"));
    let proof = format!(
        "(assume h0 B{depth})(assume h1 (not E{depth}))\
         (step t1 (cl E{depth}) :rule bfun_elim :premises (h0))\
         (step t2 (cl) :rule resolution :premises (t1 h1))"
    );
    let config = parser::Config::clean_dialect().apply_function_defs(true);
    assert_eq!(check(problem, proof, config), Ok(true));
}

/// `bfun_elim` over `(forall ((b Bool)) (and b BIG Z))`, where `BIG` merges two chains over
/// distinct constants at each of its 1,000 links, `(h A_j B_j)` with `A_j = (f c_j A_(j-1))` and
/// `B_j = (g d_j B_(j-1))`, and `Z = (and (pz c_1 d_1) ...)`, all named in the proof, is checked
/// (the walk's sets of names, computed without fuel, took 1,560 MB at 5,000 links).
#[test]
fn bfun_elim_over_chains_merged_apart_is_checked() {
    let n = 1_000;
    let mut problem = "(set-logic ALL)(declare-const q Bool)(declare-fun f (Int Int) Int)\
                       (declare-fun g (Int Int) Int)(declare-fun h (Int Int) Bool)\
                       (declare-fun pz (Int Int) Bool)"
        .to_owned();
    for j in 0..=n {
        problem.push_str(&format!("(declare-const c{j} Int)(declare-const d{j} Int)"));
    }
    problem.push_str("(assert q)(assert (not q))");
    let links: Vec<String> = (1..=n)
        .map(|j| {
            let (a, b) = if j == 1 {
                ("c0".to_owned(), "d0".to_owned())
            } else {
                (format!("A{}", j - 1), format!("B{}", j - 1))
            };
            format!("(h (! (f c{j} {a}) :named A{j}) (! (g d{j} {b}) :named B{j}))")
        })
        .collect();
    let pairs: Vec<String> = (1..=n).map(|j| format!("(pz c{j} d{j})")).collect();
    let big = format!("(! (and {}) :named BIG)", links.join(" "));
    let z = format!("(! (and {}) :named Z)", pairs.join(" "));
    let expanded = "(and (and false BIG Z) (and true BIG Z))";
    let proof = format!(
        "(anchor :step t9)(assume a1 (! (forall ((b Bool)) (and b {big} {z})) :named Q))\
         (step a2 (cl {expanded}) :rule bfun_elim :premises (a1))\
         (step t9 (cl (not Q) {expanded}) :rule subproof :discharge (a1)){}",
        "(assume h1 q)(assume h2 (not q))(step tz (cl) :rule resolution :premises (h1 h2))"
    );
    assert_eq!(
        check(problem, proof, parser::Config::clean_dialect()),
        Ok(true)
    );
}

/// Two chains merged at every link, `r_j = (bvor p_j q_j)` with `p_j = (bvadd c_j p_(j-1))` and
/// `q_j = (bvmul d_j q_(j-1))` over distinct constants, or `q_j = (bvmul c_j q_(j-1))` over the
/// same ones (`twin`), each link named where it is written.
fn merged_links(n: usize, twin: bool) -> Vec<String> {
    let d = if twin { "c" } else { "d" };
    let mut links = vec![format!(
        "(= (! (bvadd c1 c0) :named p1) (! (bvmul {d}1 {d}0) :named q1))"
    )];
    for j in 2..=n {
        let (p, q) = (format!("p{}", j - 1), format!("q{}", j - 1));
        links.push(format!(
            "(= (! (bvor (! (bvadd c{j} {p}) :named p{j}) (! (bvmul {d}{j} {q}) :named q{j})) \
             :named r{j}) c0)"
        ));
    }
    links
}

fn declarations_of_two(n: usize) -> String {
    let mut text = declarations(n);
    for j in 0..=n {
        text.push_str(&format!("(declare-const d{j} (_ BitVec 8))"));
    }
    text
}

/// Two chains merged at every link, over distinct constants and over the same ones, by each route
/// that asks for their free variables: named at top level, inside one `exists`, each link in an
/// `exists` of its own inside an `exists` of `n` variables, each link one binder deeper than the
/// last, and defined in the proof and read once by `qnt_rm_unused`. All are checked.
#[test]
fn chains_merged_at_every_link_are_checked_by_each_route() {
    let n = 2_000;
    let end = "(assert p)(assert (not p))";
    for twin in [false, true] {
        let links = merged_links(n, twin);
        let declared = declarations_of_two(n);
        let top: String = links.iter().map(|l| format!("(assert {l})")).collect();
        let own: Vec<String> = links
            .iter()
            .map(|l| format!("(exists ((u Bool)) (and u {l}))"))
            .collect();
        let ys: Vec<String> = (0..n).map(|i| format!("(y{i} Bool)")).collect();
        let nested: String = links
            .iter()
            .enumerate()
            .map(|(j, l)| format!("(exists ((u{j} Bool)) (and u{j} {l} "))
            .collect();
        let problems = [
            ("named at top level", format!("{declared}{top}{end}")),
            (
                "inside an exists",
                format!(
                    "{declared}(assert (exists ((x Bool)) (and x {}))){end}",
                    links.join(" ")
                ),
            ),
            (
                "each in an exists of its own",
                format!(
                    "{declared}(assert (exists ({}) (and y0 {}))){end}",
                    ys.join(" "),
                    own.join(" ")
                ),
            ),
            (
                "each one binder deeper",
                format!("{declared}(assert {nested}true{}){end}", "))".repeat(n)),
            ),
        ];
        for (route, problem) in problems {
            let verdict = check(
                problem,
                CONTRADICTION.to_owned(),
                parser::Config::clean_dialect(),
            );
            assert_eq!(verdict, Ok(true), "{route}, twin {twin}");
        }

        let d = if twin { "c" } else { "d" };
        let mut definitions = format!(
            "(define-fun p1 () (_ BitVec 8) (bvadd c1 c0))\
             (define-fun q1 () (_ BitVec 8) (bvmul {d}1 {d}0))\
             (define-fun s1 () (_ BitVec 8) (bvor p1 q1))"
        );
        for j in 2..=n {
            definitions.push_str(&format!(
                "(define-fun p{j} () (_ BitVec 8) (bvadd c{j} p{}))\
                 (define-fun q{j} () (_ BitVec 8) (bvmul {d}{j} q{}))\
                 (define-fun s{j} () (_ BitVec 8) (bvand (bvor p{j} q{j}) s{}))",
                j - 1,
                j - 1,
                j - 1
            ));
        }
        let proof = format!(
            "{definitions}(step t1 (cl (= (forall ((z Int)) (= s{n} c0)) (= s{n} c0))) \
             :rule qnt_rm_unused){CONTRADICTION}"
        );
        let verdict = check(
            format!("{declared}{end}"),
            proof,
            parser::Config::clean_dialect(),
        );
        assert_eq!(verdict, Ok(true), "read by qnt_rm_unused, twin {twin}");
    }
}

/// The same routes still refuse what they refused: a merged link, in a binder of its own, that
/// mentions the variable that binder binds (named where it is bound), and a `qnt_rm_unused` step
/// removing a variable the second chain mentions.
#[test]
fn chains_merged_at_every_link_still_refuse_what_they_mention() {
    let n = 2_000;
    let end = "(assert p)(assert (not p))";
    let mut links = merged_links(n, false);
    let k = n / 2;
    links[k - 1] = format!(
        "(= (! (bvor (! (bvadd c{k} p{}) :named p{k}) (! (bvmul u q{}) :named q{k})) \
         :named r{k}) c0)",
        k - 1,
        k - 1
    );
    let own: Vec<String> = links
        .iter()
        .map(|l| format!("(exists ((u (_ BitVec 8))) (and (= u c0) {l}))"))
        .collect();
    let ys: Vec<String> = (0..n).map(|i| format!("(y{i} Bool)")).collect();
    let problem = format!(
        "{}(assert (exists ({}) (and y0 {}))){end}",
        declarations_of_two(n),
        ys.join(" "),
        own.join(" ")
    );
    let verdict = check(
        problem,
        CONTRADICTION.to_owned(),
        parser::Config::clean_dialect(),
    );
    let error = verdict.expect_err("a named term mentioning a bound variable");
    assert!(
        error.contains(&format!("q{k}")) && error.contains("'u'"),
        "{error}"
    );

    let mut definitions = "(define-fun p1 () (_ BitVec 8) (bvadd c1 c0))\
                           (define-fun q1 () (_ BitVec 8) (bvmul z d0))\
                           (define-fun s1 () (_ BitVec 8) (bvor p1 q1))"
        .to_owned();
    for j in 2..=n {
        definitions.push_str(&format!(
            "(define-fun p{j} () (_ BitVec 8) (bvadd c{j} p{}))\
             (define-fun q{j} () (_ BitVec 8) (bvmul d{j} q{}))\
             (define-fun s{j} () (_ BitVec 8) (bvand (bvor p{j} q{j}) s{}))",
            j - 1,
            j - 1,
            j - 1
        ));
    }
    let proof = format!(
        "{definitions}(step t1 (cl (= (forall ((z (_ BitVec 8))) (= s{n} c0)) (= s{n} c0))) \
         :rule qnt_rm_unused){CONTRADICTION}"
    );
    let problem = format!(
        "{}(declare-const z (_ BitVec 8)){end}",
        declarations_of_two(n)
    );
    let verdict = check(problem, proof, parser::Config::clean_dialect());
    assert!(verdict.is_err(), "{verdict:?}");
}

#[test]
fn drup() {
    test_cases! {
        definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
        ",
        "Simple working examples" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a3 (or (not d) (not e)))
            (assume a4 (not a))
            (assume a5 (not b))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t3 (cl (not d) (not e)) :rule or :premises (a3))
            (step t4 (cl a b) :rule drup :premises (t0 t1 t2 t3) :args ((cl a b)))": true,

            "
            (assume a1 (not a))
            (assume a2 (not b))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drup :premises (a1 a2 t0) :args ((cl)))": true,
        }

        "Simple false-working examples" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a4 (not a))
            (assume a5 (not b))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t4 (cl a) :rule drup :premises (t0 t1 t2) :args ((cl a b)))": false,

            "
            (assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drup :premises (a1 t0) :args ((cl)))": false,
        }
    }
}

#[test]
fn drat() {
    test_cases! {
        definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
        ",
        "DRAT working examples (validates DRAT rule functionality)" {
            "(assume a1 (not a))
            (assume a2 (not b))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drat :premises (a1 a2 t0) :args ((cl)))": true,

            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (assume a3 (or (not d) (not e)))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t3 (cl (not d) (not e)) :rule or :premises (a3))
            (step t4 (cl a b) :rule drat :premises (t0 t1 t2 t3) :args ((cl a b)))": true,
        }

        "DRAT failing examples" {
            "(assume a1 (not a))
            (assume a3 (or a b))
            (step t0 (cl a b) :rule or :premises (a3))
            (step t1 (cl) :rule drat :premises (a1 t0) :args ((cl)))": false,

            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a2 (or (not d) e))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t2 (cl (not d) e) :rule or :premises (a2))
            (step t4 (cl a) :rule drat :premises (t0 t1 t2) :args ((cl a b)))": false,
        }
    }
}

// Added in Clean: a RAT lemma only preserves satisfiability, so a `drat` step that uses one may
// only conclude the empty clause. The first case was accepted by upstream Carcara; `(cl a b)` is
// false when a, b are false and c, d are true (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn drat_rat_lemmas_only_refute() {
    test_cases! {
        definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const e Bool)
        ",
        "RAT lemma with a non-empty conclusion" {
            "(assume a0 (or a c))
            (assume a1 (or a (not c) d))
            (assume a3 (or (not d) (not e)))
            (step t0 (cl a c) :rule or :premises (a0))
            (step t1 (cl a (not c) d) :rule or :premises (a1))
            (step t3 (cl (not d) (not e)) :rule or :premises (a3))
            (step t4 (cl a b) :rule drat :premises (t0 t1 t3) :args ((cl a b)))": false,
        }
        "RAT lemma that leads to the empty clause" {
            "(assume a1 (or a b))
            (assume a2 (or (not a) b))
            (assume a3 (or a (not b)))
            (assume a4 (or (not a) (not b)))
            (step t1 (cl a b) :rule or :premises (a1))
            (step t2 (cl (not a) b) :rule or :premises (a2))
            (step t3 (cl a (not b)) :rule or :premises (a3))
            (step t4 (cl (not a) (not b)) :rule or :premises (a4))
            (step t5 (cl) :rule drat :premises (t1 t2 t3 t4) :args ((cl c) (cl a) (cl)))": true,
        }
    }
}

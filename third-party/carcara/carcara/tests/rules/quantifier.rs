#[test]
fn forall_inst() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
            (declare-fun y () Bool)
            (declare-fun y_renamed () Bool)
            (declare-fun z () Bool)
            (declare-fun c () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (or (not (forall ((p Bool)) p)) q))
                :rule forall_inst :args (q))": true,

            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args (a b))": true,

            "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= a a)))
                :rule forall_inst :args (a))": true,

            "(step t1 (cl (or (not (forall ((p Bool)) p)) (ite q (= a b) (and (= a 0.0) true))))
                :rule forall_inst :args ((ite q (= a b) (and (= a 0.0) true))))": true,
        }
        // Added in Clean: the substitution renamed a bound variable to `<name>_renamed` without
        // looking at the body, so a free occurrence of that name was captured
        "The renaming may not capture a free variable of the body" {
            "(step t1 (cl (or
                (not (forall ((v Bool)) (forall ((y Bool)) (or v y y_renamed))))
                (forall ((w Bool)) (or y w w))
            )) :rule forall_inst :args (y))": false,
            "(step t1 (cl (or
                (not (forall ((v Bool)) (forall ((y Bool)) (or v y y_renamed))))
                (forall ((y_renamed_renamed Bool)) (or y y_renamed_renamed y_renamed))
            )) :rule forall_inst :args (y))": true,
        }
        // Added in Clean: `Substitution::apply` never substituted into a `let` value, so the
        // instance kept reading the outer variable
        "The instantiation reaches a `let` value" {
            // `z` is also a declared constant, so the wrong instance below still parses: the
            // value reads that outer `z` instead of the instantiation term
            "(step t1 (cl (or
                (not (forall ((z Bool)) (let ((w z)) (= w z))))
                (let ((w z)) (= w c))
            )) :rule forall_inst :args (c))": false,
            "(step t1 (cl (or
                (not (forall ((z Bool)) (let ((w z)) (= w z))))
                (let ((w c)) (= w c))
            )) :rule forall_inst :args (c))": true,
            // The free variables of a `let` value are free in the `let`, so the binder below has
            // to be renamed
            "(step t1 (cl (or
                (not (forall ((v Bool)) (forall ((y Bool)) (or v y))))
                (forall ((y Bool)) (or (let ((w y)) w) y))
            )) :rule forall_inst :args ((let ((w y)) w)))": false,
            "(step t1 (cl (or
                (not (forall ((v Bool)) (forall ((y Bool)) (or v y))))
                (forall ((y_renamed Bool)) (or (let ((w y)) w) y_renamed))
            )) :rule forall_inst :args ((let ((w y)) w)))": true,
        }
        "Equalities may be flipped" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (and (= x y) (= 1 0))))
                (and (= b a) (= 1 0)))) :rule forall_inst :args (a b))": true,
        }
        "Bound variables may be renamed by substitution" {
            // The variable shadowing makes it so the substitution applied by Carcara renames p
            "(step t1 (cl (or
                (not (forall ((p Bool) (r Bool)) (and p (forall ((p Bool)) p))))
                (and q (forall ((p Bool)) p))
            )) :rule forall_inst :args (q q))": true,
        }
        "Argument is not in quantifier bindings" {
            "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= b 0.0)))
                :rule forall_inst :args (b 0.0))": false,
        }
        "Binding has no associated substitution" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x x))) (= a a)))
                :rule forall_inst :args (a))": false,
        }
        "Substitution was not applied" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= x b)))
                :rule forall_inst :args (a b))": false,
        }
        "Applied substitution was not passed as argument" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args (a))": false,
        }
        "Wrong type of rule argument" {
            "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                :rule forall_inst :args ((= x a) b))": false,
        }
    }
}

#[test]
fn qnt_join() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((x Real)) (forall ((y Real)) (= x y)))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                (forall ((x Real) (y Real) (z Real) (w Real)) (= (+ x y) (+ z w)))
            )) :rule qnt_join)": true,
        }
        "Bindings in wrong order" {
            "(step t1 (cl (=
                (forall ((x Real)) (forall ((y Real)) (= x y)))
                (forall ((y Real) (x Real)) (= x y))
            )) :rule qnt_join)": false,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                (forall ((z Real) (y Real) (w Real) (x Real)) (= (+ x y) (+ z w)))
            )) :rule qnt_join)": false,
        }
        "Removing duplicates" {
            "(step t1 (cl (=
                (forall ((p Bool)) (forall ((p Bool)) p))
                (forall ((p Bool)) p)
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((y Real) (z Real)) (distinct x y z)))
                (forall ((x Real) (y Real) (z Real)) (distinct x y z))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((x Real) (y Real)) (= x y)))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_join)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real)) (forall ((z Real) (x Real)) (distinct x y z)))
                (forall ((x Real) (y Real) (z Real) (x Real)) (distinct x y z))
            )) :rule qnt_join)": false,
        }
    }
}

#[test]
fn qnt_rm_unused() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun x () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real)) (= x z))
                (forall ((x Real) (z Real)) (= x z))
            )) :rule qnt_rm_unused)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                (forall ((y Real)) (= y y))
            )) :rule qnt_rm_unused)": true,
        }
        "Bindings in wrong order" {
            // Deviates from spec, but is still sound
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real)) (= x z))
                (forall ((z Real) (x Real)) (= x z))
            )) :rule qnt_rm_unused)": true,
        }
        "Not all unused bindings were removed" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                (forall ((y Real) (w Real)) (= y y))
            )) :rule qnt_rm_unused)": true,
        }
        "Inner term is the opposite quantifier" {
            "(step t1 (cl (=
                (exists ((?v0 Int)) (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2)))
                (forall ((?v1 Int) (?v2 Int)) (= ?v1 ?v2))
            )) :rule qnt_rm_unused)": true,
        }
        "Duplicate removal" {
            "(step t1 (cl (=
                (forall ((x Real) (y Real) (x Real)) (= x y))
                (forall ((x Real) (y Real)) (= x y))
            )) :rule qnt_rm_unused)": true,

            "(step t1 (cl (=
                (forall ((x Real) (y Real) (x Real)) (= x y))
                (forall ((y Real) (x Real)) (= x y))
            )) :rule qnt_rm_unused)": true,
        }
    }
}

#[test]
fn qnt_cnf() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (or (not (forall ((p Bool)) p)) (forall ((p Bool)) p)))
                :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool)) (not (and p q))))
                (forall ((p Bool) (q Bool)) (or (not p) (not q)))
            )) :rule qnt_cnf)": true,
        }
        "Selecting only one clause from conjunction" {
            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool)) (or (and p true) (and q false))))
                (forall ((p Bool) (q Bool)) (or true q))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool) (q Bool))
                    (not (and (=> p q) (or q (not (not p))) (or true false (not q))))
                ))
                (forall ((p Bool) (q Bool)) (or p (not q) (not true)))
            )) :rule qnt_cnf)": true,
        }
        "Quantifier bindings added due to prenexing" {
            "(step t1 (cl (or
                (not (forall ((p Bool)) (forall ((q Bool)) (or p q))))
                (forall ((p Bool) (q Bool)) (or p q))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool)) (not (exists ((q Bool)) (and p q)))))
                (forall ((p Bool) (q Bool)) (or (not p) (not q)))
            )) :rule qnt_cnf)": true,

            "(step t1 (cl (or
                (not (forall ((p Bool)) (or p (and false (forall ((q Bool)) q)))))
                (forall ((p Bool)) (or p false))
            )) :rule qnt_cnf)": true,
        }
    }
}

#[test]
fn miniscope_distribute() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool) (q Bool)) false)
                )
            )) :rule miniscope_distribute)": true,

            "(step t1 (cl (=
                (exists ((p Bool)) (or r s p))
                (or (exists ((p Bool)) r) (exists ((p Bool)) s) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": true,
        }
        "Different quantifiers" {
            "(step t1 (cl (=
                (exists ((p Bool)) (or r s p))
                (or (exists ((p Bool)) r) (forall ((p Bool)) s) (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong operator" {
            "(step t1 (cl (=
                (forall ((p Bool)) (and p p))
                (or (forall ((p Bool)) p) (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (exists ((p Bool)) (and p p))
                (or (exists ((p Bool)) p) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (=
                (forall ((p Bool)) (and p p))
                (and (forall ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool)) false)
                )
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (and p q false))
                (and
                    (forall ((p Bool) (q Bool)) p)
                    (forall ((p Bool) (q Bool)) q)
                    (forall ((p Bool) (x Int)) false)
                )
            )) :rule miniscope_distribute)": false,
        }
    }
}

#[test]
fn miniscope_split() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (or p q))
                (or (forall ((p Bool)) p) (forall ((q Bool)) q))
            )) :rule miniscope_split)": true,

            "(step t1 (cl (=
                (exists ((p Bool) (q Bool) (s Bool)) (and p q s))
                (and (exists ((p Bool)) p) (exists ((q Bool)) q) (exists ((s Bool)) s))
            )) :rule miniscope_split)": true,
        }
        "Different quantifiers" {
            "(step t1 (cl (=
                (forall ((p Bool)) (or p p))
                (or (forall ((p Bool)) p) (exists ((p Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong operator" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (or p q))
                (and (forall ((p Bool)) p) (forall ((q Bool)) q))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (exists ((p Bool) (q Bool)) (or p q))
                (and (exists ((p Bool)) p) (exists ((q Bool)) q))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong number of arguments" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (or p q))
                (or (forall ((p Bool) (q Bool)) p))
            )) :rule miniscope_distribute)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (or p q))
                (or (forall ((p Bool)) p) (forall ((q Bool) (x Int)) q))
            )) :rule miniscope_distribute)": false,

            "(step t1 (cl (=
                (forall ((p Bool) (q Bool) (r Bool)) (or p (= q r)))
                (or (forall ((p Bool)) p) (forall ((q Bool)) (= q r)))
            )) :rule miniscope_distribute)": false,
        }
        "Overlapping binding lists" {
            "(step t1 (cl (=
                (forall ((p Bool)) (or p (not p)))
                (or (forall ((p Bool)) p) (forall ((p Bool)) (not p)))
            )) :rule miniscope_distribute)": false,
        }
    }
}

#[test]
fn miniscope_ite() {
    test_cases! {
        definitions = "
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (=
                (forall ((p Bool) (q Bool)) (ite r true false))
                (ite r (forall ((p Bool) (q Bool)) true) (forall ((p Bool) (q Bool)) false))
            )) :rule miniscope_ite)": true,
        }
        "Wrong format" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) true) (exists ((p Bool)) false))
            )) :rule miniscope_ite)": false,

            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite (forall ((p Bool)) r) (forall ((p Bool)) true) (forall ((p Bool)) false))
            )) :rule miniscope_ite)": false,
        }
        "Wrong binding list" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) true) (forall ((q Bool)) false))
            )) :rule miniscope_ite)": false,
        }
        "Wrong phis" {
            "(step t1 (cl (=
                (forall ((p Bool)) (ite r true false))
                (ite r (forall ((p Bool)) false) (forall ((p Bool)) true))
            )) :rule miniscope_ite)": false,
        }
        "Bound variable in condition" {
            "(step t1 (cl (=
                (forall ((r Bool)) (ite r true false))
                (ite r (forall ((r Bool)) false) (forall ((r Bool)) true))
            )) :rule miniscope_ite)": false,
        }
    }
}

// Added in Clean: prenexing must not capture a free occurrence of the pulled variable (see
// third-party/carcara/DOWNSTREAM.md).
#[test]
fn qnt_cnf_capture() {
    test_cases! {
        definitions = "
            (declare-fun x () Int)
        ",
        "Pulled binder captures a free variable" {
            "(step t1 (cl (or
                (not (forall ((y Int)) (or (forall ((x Int)) (= x 0)) (= x 1))))
                (forall ((x Int)) (or (= x 0) (= x 1)))
            )) :rule qnt_cnf)": false,
        }
        "Pulled binder with a fresh name" {
            "(step t1 (cl (or
                (not (forall ((y Int)) (or (forall ((z Int)) (= z 0)) (= x 1))))
                (forall ((z Int)) (or (= z 0) (= x 1)))
            )) :rule qnt_cnf)": true,
        }
    }
}

#[test]
fn eq_reflexive() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun f (Int Int) Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= a a)) :rule eq_reflexive)": true,
            "(step t1 (cl (= false false)) :rule eq_reflexive)": true,
            "(step t1 (cl (= (f a b) (f a b))) :rule eq_reflexive)": true,
            "(step t1 (cl (= (+ b a) (+ b a))) :rule eq_reflexive)": true,
        }
        "Number of terms in clause != 1" {
            "(step t1 (cl) :rule eq_reflexive)": false,
            "(step t1 (cl (= a a) (= b b)) :rule eq_reflexive)": false,
        }
        "Term is not an equality" {
            "(step t1 (cl (not (= b b))) :rule eq_reflexive)": false,
            "(step t1 (cl (and (= a a) (= b b))) :rule eq_reflexive)": false,
        }
        "Terms in equality aren't equal" {
            "(step t1 (cl (= a b)) :rule eq_reflexive)": false,
            "(step t1 (cl (= (f a b) (f b a))) :rule eq_reflexive)": false,
            "(step t1 (cl (= (+ a b) (+ b a))) :rule eq_reflexive)": false,
        }
    }
}

#[test]
fn refl() {
    test_cases! {
        definitions = "
            (declare-fun f (Real) Real)
            (declare-fun g (Real) Real)
            (declare-fun z () Real)
            (declare-fun y_renamed () Real)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x y)) :rule refl)
            (step t1 (cl) :rule hole)": true,

            "(anchor :step t1)
            (step t1.t1 (cl (= z z)) :rule refl)
            (step t1 (cl) :rule hole)": true,

        }
        "Multiple substitutions in sequence" {
            "(anchor :step t1 :args ((z Real) (:= (y Real) z) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule refl)
            (step t1 (cl) :rule hole)": true,
        }
        "Nested subproofs" {
            // Since an inner subproof cannot end an outer subproof, we need to have a dummy
            // step to the end the outer subproofs in these examples

            // This step is valid because the outer context transforms the `y` in the `(:= x y)`
            // mapping, such that the context becomes `(:= x z)`
            "(anchor :step t1 :args ((z Real) (:= (y Real) z)))
            (anchor :step t1.t1 :args ((:= (x Real) y)))
            (step t1.t1.t1 (cl (= x z)) :rule refl)
            (step t1.t1 (cl) :rule hole)
            (step t1 (cl) :rule hole)": true,

            // This should fail because the semantics of `refl` are such that the substitution
            // is simultaneous, and not until a fixed point
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (anchor :step t1.t1 :args ((z Real) (:= (y Real) z)))
            (step t1.t1.t1 (cl (= x z)) :rule refl)
            (step t1.t1 (cl) :rule hole)
            (step t1 (cl) :rule hole)": false,
        }
        "Terms aren't equal after applying context substitution" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule refl)
            (step t1 (cl) :rule hole)": false,
        }
        "Name collision with variables of different types" {
            "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
            (step t1.t1 (cl (=
                (forall ((y Bool)) (and y (> x 0)))
                (forall ((z Bool)) (and z (> y 0)))
            )) :rule refl)
            (step t1 (cl) :rule hole)": true,
        }
        // Added in Clean: `compare_binder` zipped the two binding lists, so a binder was
        // alpha-equivalent to one binding more variables (see third-party/carcara/DOWNSTREAM.md)
        "Binders of different arity" {
            "(step t1 (cl (= (forall ((x Bool)) (or x p)) (forall ((x Bool) (p Bool)) (or x p)))) :rule refl)": false,
            "(step t1 (cl (= (forall ((x Bool) (p Bool)) (or x p)) (forall ((x Bool)) (or x p)))) :rule refl)": false,
            "(step t1 (cl (= (exists ((x Bool) (p Bool)) (and x p)) (exists ((x Bool)) (and x p)))) :rule refl)": false,
            "(step t1 (cl (= (let ((x true)) (and x p)) (let ((x true) (p true)) (and x p)))) :rule refl)": false,
            // The same binders, renamed, are still equal
            "(step t1 (cl (= (forall ((x Bool)) (or x p)) (forall ((w Bool)) (or w p)))) :rule refl)": true,
            "(step t1 (cl (= (exists ((x Bool) (y Bool)) (and x y)) (exists ((u Bool) (v Bool)) (and u v)))) :rule refl)": true,
        }
        // Added in Clean: SMT-LIB `let` binds in parallel, so a value is read in the enclosing
        // scope. The De Bruijn map used to be extended between values, which identified the two
        // outer constants below (see third-party/carcara/DOWNSTREAM.md)
        "`let` values are read in the enclosing scope" {
            "(step t1 (cl (= (let ((p true) (y p)) y) (let ((q true) (y q)) y))) :rule refl)": false,
            "(step t1 (cl (= (let ((p true) (y p)) y) (let ((q true) (y p)) y))) :rule refl)": true,
            "(step t1 (cl (= (let ((a true) (b p)) (and a b)) (let ((c true) (b p)) (and c b)))) :rule refl)": true,
        }
        // Added in Clean: under `(:= (x Real) y)` the bound `y` has to be renamed, and the name
        // `y_renamed` used to be taken even when the body already had a free one
        "The renaming may not capture a free variable of the body" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (=
                (exists ((y Real)) (= (f y) (g y_renamed)))
                (exists ((w Real)) (= (f w) (g w)))
            )) :rule refl)
            (step t1 (cl) :rule hole)": false,
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (=
                (exists ((y Real)) (= (f y) (g y_renamed)))
                (exists ((w Real)) (= (f w) (g y_renamed)))
            )) :rule refl)
            (step t1 (cl) :rule hole)": true,
        }
    }
}

#[test]
fn strict_refl() {
    test_cases! {
        definitions = "
            (declare-fun f (Real) Real)
            (declare-fun g (Real) Real)
            (declare-fun z () Real)
        ",
        "Simple working examples (same as refl)" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x y)) :rule strict_refl)
            (step t1 (cl) :rule hole)": true,
            "(anchor :step t1)
            (step t1.t1 (cl (= z z)) :rule strict_refl)
            (step t1 (cl) :rule hole)": true,
        }
        "Multiple substitutions in sequence" {
            "(anchor :step t1 :args ((z Real) (:= (y Real) z) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule strict_refl)
            (step t1 (cl) :rule hole)": true,
        }
        "Should reject alpha-equivalent terms (unlike refl)" {
            // strict_refl does NOT use alpha equivalence, so this should fail
            // even though refl would accept it
            "(step t1 (cl (=
                (forall ((x Int)) (> x 0))
                (forall ((y Int)) (> y 0))
            )) :rule strict_refl)": false,
        }
        "Terms aren't equal after applying context substitution" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x z)) :rule strict_refl)
            (step t1 (cl) :rule hole)": false,
        }
    }
}

// Added in Clean: alpha-equivalence must not reuse an equality cached outside a binder that
// rebinds one of its variables. Upstream Carcara accepted the first case, which is false when
// `y = 1` (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn refl_alpha_equivalence_under_binders() {
    test_cases! {
        definitions = "
            (declare-fun y () Int)
        ",
        "Cached equality reused under a rebinding binder" {
            "(step t1 (cl (= (and (= y 1) (forall ((y Int)) (= y 1)))
                            (and (= 1 y) (forall ((z Int)) (= 1 y))))) :rule refl)": false,
        }
        "Genuine renaming" {
            "(step t1 (cl (= (and (= y 1) (forall ((y Int)) (= y 1)))
                            (and (= 1 y) (forall ((z Int)) (= 1 z))))) :rule refl)": true,
        }
    }
}

// Added in Clean: the values of a `let` are compared in the enclosing scope, and an equality
// found for them used to be cached in the `let`'s own scope, so the body reused it after the
// `let` had rebound one of its names. The first case is false when `p` is false; the others are
// the same leak under a quantifier and with an extra binding (fix 34, see
// third-party/carcara/DOWNSTREAM.md).
#[test]
fn refl_let_values_do_not_leak_into_the_body() {
    test_cases! {
        definitions = "
            (declare-const p Bool)
            (declare-const a Bool)
        ",
        "A value's equality is not reused after the `let` rebinds its variable" {
            "(step t1 (cl (= (let ((u p)) (let ((u (not u)) (w u)) (or u w)))
                            (let ((v p)) (let ((z (not v)) (w v)) (or v w))))) :rule refl)": false,
            "(step t1 (cl (= (forall ((u Bool)) (let ((u (not u)) (w u)) (or u w)))
                            (forall ((v Bool)) (let ((z (not v)) (w v)) (or v w))))) :rule refl)": false,
            "(step t1 (cl (= (exists ((u Bool)) (let ((u (not u)) (w u)) (and u w)))
                            (exists ((v Bool)) (let ((z (not v)) (w v)) (and v w))))) :rule refl)": false,
            "(step t1 (cl (= (let ((u a)) (let ((u (not u)) (w u) (k true)) (or u w)))
                            (let ((v a)) (let ((z (not v)) (w v) (k true)) (or v w))))) :rule refl)": false,
        }
        "Genuine renamings of the same terms" {
            "(step t1 (cl (= (let ((u p)) (let ((u (not u)) (w u)) (or u w)))
                            (let ((v p)) (let ((z (not v)) (w v)) (or z w))))) :rule refl)": true,
            "(step t1 (cl (= (forall ((u Bool)) (let ((u (not u)) (w u)) (or u w)))
                            (forall ((v Bool)) (let ((z (not v)) (w v)) (or z w))))) :rule refl)": true,
            "(step t1 (cl (= (let ((u a)) (let ((u (not u)) (w u) (k true)) (or u w k)))
                            (let ((v a)) (let ((z (not v)) (w v) (k true)) (or z w k))))) :rule refl)": true,
        }
    }
}

// Added in Clean: a division literal has exactly two arguments. Upstream Carcara accepted
// `(/ 3.0 3.0 0.0)` as equal to `1.0` (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn division_literals() {
    test_cases! {
        definitions = "",
        "Extra arguments are not ignored" {
            "(step t1 (cl (= (/ 3.0 3.0 0.0) 1.0)) :rule ite_intro)": false,
            "(step t1 (cl (= (/ 3.0 3.0 0.0) 1.0)) :rule refl)": false,
        }
    }
}

#[test]
fn reordering() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl p q r s) :rule hole)
            (step t2 (cl r q p s) :rule reordering :premises (t1))": true,

            "(step t1 (cl p q q p r s) :rule hole)
            (step t2 (cl r q p p s q) :rule reordering :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl) :rule reordering :premises (t1))": true,
        }
    }
}

#[test]
fn shuffle() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (+ x y z) (+ z x y))) :rule shuffle)": true,

            "(step t1 (cl (= (and p q q r p) (and q q p p r))) :rule shuffle)": true,
        }
        "Invalid examples" {
            "(step t1 (cl (= (- x y z) (- x y z))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) (and p q r))) :rule shuffle)": false,
            "(step t1 (cl (= (or p q r) true)) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (* x y y))) :rule shuffle)": false,
            "(step t1 (cl (= (* x x y) (+ x y))) :rule shuffle)": false,
        }
    }
}

#[test]
fn symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule symm :premises (h1))": false,
        }
    }
}

#[test]
fn not_symm() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(assume h1 (not (= a b)))
            (step t1 (cl (not (= b a))) :rule not_symm :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (= a b))
            (step t1 (cl (= b a)) :rule not_symm :premises (h1))": false,
        }
    }
}

#[test]
fn eq_symmetric() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (= b a) (= a b))) :rule eq_symmetric)": true,
            "(step t1 (cl (= (= a a) (= a a))) :rule eq_symmetric)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (= a b) (= a b))) :rule eq_symmetric)": false,
            "(step t1 (cl (= (not (= a b)) (not (= b a)))) :rule eq_symmetric)": false,
        }
    }
}

#[test]
fn eq_mp() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun a () Int)
            (declare-fun b () Int)
        ",
        "Simple working examples" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 (not p))
            (assume h2 (= (not p) (or q r)))
            (step t3 (cl (or q r)) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 (< a b))
            (assume h2 (= (< a b) (not (>= a b))))
            (step t3 (cl (not (>= a b))) :rule eq_mp :premises (h1 h2))": true,

            "(assume h1 p)
            (assume h2 (= p p))
            (step t3 (cl p) :rule eq_mp :premises (h1 h2))": true,
        }
        "Premises in the wrong order" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h2 h1))": false,
        }
        "Equivalence is flipped" {
            "(assume h1 p)
            (assume h2 (= q p))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": false,
        }
        "Failing examples" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl r) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q r) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 p)
            (assume h2 (=> p q))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))": false,

            "(assume h1 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h1))": false,

            "(step t1 (cl p r) :rule hole)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (t1 h2))": false,
        }
    }
}

#[test]
fn weakening() {
    test_cases! {
        definitions = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a b c) :rule weakening :premises (t1))": true,

            "(step t1 (cl) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": true,
        }
        "Failing examples" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl a c b) :rule weakening :premises (t1))": false,

            "(step t1 (cl a b c) :rule hole)
            (step t2 (cl a b) :rule weakening :premises (t1))": false,
        }
    }
}

#[test]
fn and_intro() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
        ",
        "Simple working examples" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1 h2))": true,

            "(assume h1 p)
            (assume h2 q)
            (assume h3 r)
            (step t1 (cl (and p q r)) :rule and_intro :premises (h1 h2 h3))": true,
        }
        "Non-unit premise corresponds to a disjunction" {
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and (or p q) r)) :rule and_intro :premises (t1 h2))": true,

            // A unit premise whose term is itself an `or` matches the same conjunct.
            "(assume h1 (or p q))
            (assume h2 r)
            (step t1 (cl (and (or p q) r)) :rule and_intro :premises (h1 h2))": true,
        }
        "Premises must be in the right order" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and q p)) :rule and_intro :premises (h1 h2))": false,
        }
        "A conjunct does not match its premise" {
            "(assume h1 p)
            (assume h2 q)
            (step t1 (cl (and p r)) :rule and_intro :premises (h1 h2))": false,

            // The disjuncts of the conjunct must match the clause order.
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and (or q p) r)) :rule and_intro :premises (t1 h2))": false,

            // A non-unit premise must correspond to an `or`, not a single literal.
            "(step t1 (cl p q) :rule hole)
            (assume h2 r)
            (step t2 (cl (and p r)) :rule and_intro :premises (t1 h2))": false,
        }
        "Wrong number of premises" {
            "(assume h1 p)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1))": false,

            "(assume h1 p)
            (assume h2 q)
            (assume h3 r)
            (step t1 (cl (and p q)) :rule and_intro :premises (h1 h2 h3))": false,
        }
        "Conclusion is not a conjunction" {
            "(assume h1 p)
            (step t1 (cl p) :rule and_intro :premises (h1))": false,
        }
    }
}

#[test]
fn bind_let() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": true,
        }
        "Premise is of the wrong form" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (< (+ x y) 0)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": false,
        }
        "Premise doesn't justify inner terms' equality" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) a) (let ((a 0)) 0))) :rule bind_let)": false,

            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) y) (let ((a 0)) x))) :rule bind_let)": false,
        }
        "Bindings can't be renamed" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a 0)) x) (let ((b 0)) y))) :rule bind_let)": false,
        }
        "Polyequality in variable values" {
            "(anchor :step t1 :args ((x Int) (y Int)))
            (step t1.t1 (cl (= (= 0 1) (= 1 0))) :rule hole)
            (step t1.t2 (cl (= x y)) :rule hole)
            (step t1 (cl (= (let ((a (= 0 1))) x) (let ((a (= 1 0))) y)))
                :rule bind_let :premises (t1.t1))": true,
        }
    }
}

// Added in Clean: `bind_let` instantiates the inner equality with the let values, so a let
// variable that occurs in it must be a fixed variable of the anchor, and the anchor may not assign
// anything. Every `false` case was accepted by upstream Carcara and is false when `P a` and `P b`
// differ (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn bind_let_scoping() {
    test_cases! {
        definitions = "
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-const a U)
            (declare-const b U)
            (declare-const x U)
        ",
        "Let variable not fixed by the anchor" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (let ((x b)) (P x)) (let ((x b)) (P a)))) :rule bind_let)": false,

            "(assume h (= x a))
            (anchor :step t1 :args ((z U)))
            (step t1.t1 (cl (= (P x) (P a))) :rule cong :premises (h))
            (step t1 (cl (= (let ((x b)) (P x)) (let ((x b)) (P a)))) :rule bind_let)": false,
        }
        "Let variable fixed by the anchor" {
            "(anchor :step t1 :args ((x U)))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (let ((x b)) (P x)) (let ((x b)) (P x)))) :rule bind_let)": true,
        }
    }
}

#[test]
fn la_mult_pos() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (> 2 0) (> a b)) (> (* 2 a) (* 2 b))))
                :rule la_mult_pos)": true,
            "(step t1 (cl (=>
                (and (> (/ 10.0 13.0) 0.0) (= x y))
                (= (* (/ 10.0 13.0) x) (* (/ 10.0 13.0) y)))
            ) :rule la_mult_pos)": true,
        }
    }
}

#[test]
fn la_mult_neg() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (and (< (- 2) 0) (>= a b)) (<= (* (- 2) a) (* (- 2) b))))
                :rule la_mult_neg)": true,
            "(step t1 (cl (=>
                (and (< (/ (- 1.0) 13.0) 0.0) (= x y))
                (= (* (/ (- 1.0) 13.0) x) (* (/ (- 1.0) 13.0) y)))
            ) :rule la_mult_neg)": true,
        }
    }
}

#[test]
fn la_mult_sign() {
    test_cases! {
        definitions = "
            (declare-fun a () Real)
            (declare-fun b () Real)
            (declare-fun c () Real)
            (declare-fun d () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (=> (> a 0.0) (> a 0.0))) :rule la_mult_sign)": true,

            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0))
                (< (* a b c) 0.0))
            ) :rule la_mult_sign)": true,
        }
        "Even powers" {
            "(step t1 (cl (=> (not (= a 0.0)) (> (* a a) 0.0))) :rule la_mult_sign)": true,
        }
        "Not using some variables" {
            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0) (> d 0.0))
                (< (* a b b b) 0.0))
            ) :rule la_mult_sign)": true,
        }
        "Wrong relation" {
            "(step t1 (cl (=>
                (and (> a 0.0) (< b 0.0) (> c 0.0))
                (> (* a b c) 0.0))
            ) :rule la_mult_sign)": false,
        }
        "Could not calculate sign" {
            // this is technically sound, but still an error
            "(step t1 (cl (=>
                (and (> a 0.0) (not (= b 0.0)) (> c 0.0))
                (not (= (* a b c) 0.0)))
            ) :rule la_mult_sign)": false,
        }
    }
}

#[test]
fn la_mult_abs_comparison() {
    test_cases! {
        definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun c () Int)
            (declare-fun d () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (abs a) (abs b))) :rule hole)
            (step t2 (cl (= (abs c) (abs d))) :rule hole)
            (step t3 (cl (= (abs (* a c)) (abs (* b d))))
                :rule la_mult_abs_comparison :premises (t1 t2))": true,

            "(step t1 (cl (> (abs a) (abs 1))) :rule hole)
            (step t2 (cl (> (abs b) (abs 1))) :rule hole)
            (step t3 (cl (and (= (abs c) (abs 1)) (not (= c 0)))) :rule hole)
            (step t4 (cl (and (= (abs d) (abs 1)) (not (= d 0)))) :rule hole)
            (step t5 (cl (> (abs (* a b c d)) (abs (* 1 1 1 1))))
                :rule la_mult_abs_comparison :premises (t1 t2 t3 t4))": true,
        }
        "Premise has the wrong form" {
            "(step t1 (cl (> (abs a) (abs b))) :rule hole)
            (step t2 (cl (= (abs c) (abs d))) :rule hole)
            (step t3 (cl (= (abs (* a c)) (abs (* b d))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,

            "(step t1 (cl (and (= (abs a) (abs 1)) (not (= a 0)))) :rule hole)
            (step t2 (cl (> (abs b) (abs 1))) :rule hole)
            (step t3 (cl (> (abs (* a b)) (abs (* 1 1))))
                :rule la_mult_abs_comparison :premises (t1 t2))": false,
        }
    }
}

#[test]
fn mod_simplify() {
    test_cases! {
        definitions = "",
        "Simple working examples" {
            "(step t1 (cl (= (mod 2 2) 0)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 42 8) 2)) :rule mod_simplify)": true,
        }
        "Negative numbers" {
            "(step t1 (cl (= (mod (- 8) 3) 1)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod 8 (- 3)) 2)) :rule mod_simplify)": true,
            "(step t1 (cl (= (mod (- 8) (- 3)) 1)) :rule mod_simplify)": true,

            "(step t1 (cl (= (mod (- 8) 3) (- 2))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod 8 (- 3)) (- 1))) :rule mod_simplify)": false,
            "(step t1 (cl (= (mod (- 8) (- 3)) (- 2))) :rule mod_simplify)": false,
        }
        "Modulo by zero" {
            "(step t1 (cl (= (mod 3 0) 1)) :rule mod_simplify)": false,
        }
    }
}

#[test]
fn evaluate() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-fun f (Int Int) Int)
        ",
        "Booleans" {
            "(step t1 (cl (=
                (=> (and true true) (or true false) (ite false false true))
                true
            )) :rule evaluate)": true,

            "(step t1 (cl (= (or (= 0 0 1) (distinct 1 2 3 1)) false)) :rule evaluate)": true,
        }
        "Arithmetic" {
            "(step t1 (cl (= (+ 1 2 (* 3 (- 1))) 0)) :rule evaluate)": true,
            // Modified in Clean: SMT-LIB `div`/`mod` are Euclidean, so `(mod (- 7) (- 3))` is 2 and
            // the sum is 3. The upstream expectation `0` used truncating division.
            "(step t1 (cl (= (+ (div 3 (abs 2)) (mod (- 7) (- 3))) 3)) :rule evaluate)": true,
            "(step t1 (cl (= (+ (div 3 (abs 2)) (mod (- 7) (- 3))) 0)) :rule evaluate)": false,
            "(step t1 (cl (= (/ 1.0 (to_real 7)) 1/7)) :rule evaluate)": true,
        }
        "Bitvectors" {
            "(step t1 (cl (=
                (bvnot (bvudiv #b100 (@bbterm false true false)))
                #b101
            )) :rule evaluate)": true,

            "(step t1 (cl (=
                (bvashr ((_ rotate_left 3) #b0101100) #b0000001)
                #b1110001
            )) :rule evaluate)": true,
        }
        "Partial evaluation" {
            "(step t1 (cl (= (+ x (+ 1 1)) (+ x 2))) :rule evaluate)": true,
            "(step t1 (cl (= (f x (+ 1 1)) (f x 2))) :rule evaluate)": false,
        }
        "Invalid examples" {
            "(step t1 (cl (= 2 (+ 1 1))) :rule evaluate)": false,
            "(step t1 (cl (= (forall ((x Int)) true) true)) :rule evaluate)": false,
        }
    }
}

#[test]
fn beta_equiv() {
    test_cases! {
        definitions = "
            (declare-fun y () Bool)
            (declare-fun y_renamed () Bool)
            (declare-fun z () Bool)
            (declare-fun c () Bool)
        ",
        "Simple working examples" {
            "(step t1 (cl (= ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1 2 3) (+ 1 2 3)))
                :rule beta_equiv)": true,

            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((b Int) (c Int)) (+ 1 b c))
            )) :rule beta_equiv)": true,
        }
        "Not an application" {
            "(step t1 (cl (=
                (lambda ((a Int) (b Int) (c Int)) (+ a b c))
                (lambda ((a Int) (b Int) (c Int)) (+ a b c))
            )) :rule beta_equiv)": false,
        }
        "Wrong arg names" {
            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((c Int) (b Int)) (+ 1 c b))
            )) :rule beta_equiv)": false,
        }
        "Wrong body" {
            "(step t1 (cl (=
                ((lambda ((a Int) (b Int) (c Int)) (+ a b c)) 1)
                (lambda ((b Int) (c Int)) (+ 1 c b))
            )) :rule beta_equiv)": false,
        }
        // Added in Clean: the substitution renamed a bound variable to `<name>_renamed` without
        // looking at the body, so a free occurrence of that name was captured
        "The renaming may not capture a free variable of the body" {
            "(step t1 (cl (=
                ((lambda ((v Bool)) (forall ((y Bool)) (or y v y_renamed))) y)
                (forall ((y_renamed Bool)) (or y_renamed y y_renamed))
            )) :rule beta_equiv)": false,
            "(step t1 (cl (=
                ((lambda ((v Bool)) (forall ((y Bool)) (or y v y_renamed))) y)
                (forall ((y_renamed_renamed Bool)) (or y_renamed_renamed y y_renamed))
            )) :rule beta_equiv)": true,
        }
        // Added in Clean: `Substitution::apply` never substituted into a `let` value, so the
        // reduced term kept reading the outer variable. `z` is also a declared constant, which
        // is what makes the wrong term below parse
        "The reduction reaches a `let` value" {
            "(step t1 (cl (=
                ((lambda ((z Bool)) (let ((w z)) (= w z))) c)
                (let ((w z)) (= w c))
            )) :rule beta_equiv)": false,
            "(step t1 (cl (=
                ((lambda ((z Bool)) (let ((w z)) (= w z))) c)
                (let ((w c)) (= w c))
            )) :rule beta_equiv)": true,
        }
    }
}

#[test]
fn div_intro() {
    test_cases! {
        definitions = "
            (declare-const a Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) 1)))))
                :rule div_intro)": true,

            "(step t1 (cl (and
                (<= (* (- 5) (div a (- 5))) a)
                (< a (* (- 5) (+ (div a (- 5)) (- 1))))
            )) :rule div_intro)": true,
        }
        "Division by 0!" {
            "(step t1 (cl (and (<= (* 0 (div a 0)) a) (< a (* 0 (+ (div a 0) 1)))))
                :rule div_intro)": false,
        }
        "Different values of b" {
            "(step t1 (cl (and (<= (* 5 (div a 3)) a) (< a (* 5 (+ (div a 5) 1)))))
                :rule div_intro)": false,
        }
        "Wrong coefficient" {
            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) 2)))))
                :rule div_intro)": false,

            "(step t1 (cl (and (<= (* 5 (div a 5)) a) (< a (* 5 (+ (div a 5) (- 1))))))
                :rule div_intro)": false,

            "(step t1 (cl (and
                (<= (* (- 5) (div a (- 5))) a)
                (< a (* (- 5) (+ (div a (- 5)) 1)))
            )) :rule div_intro)": false,
        }
    }
}

#[test]
fn log2_intro() {
    test_cases! {
        definitions = "
            (declare-const x Int)
            (declare-const y Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (and
                (=> (< 0 x)
                    (and (<= (int.pow2 (int.log2 x)) x) (< x (int.pow2 (+ (int.log2 x) 1)))))
                (=> (not (< 0 x)) (= (int.log2 x) 0))
            )) :rule log2_intro)": true,
        }
        "Different values of x" {
            "(step t1 (cl (and
                (=> (< 0 x)
                    (and (<= (int.pow2 (int.log2 x)) y) (< x (int.pow2 (+ (int.log2 x) 1)))))
                (=> (not (< 0 x)) (= (int.log2 x) 0))
            )) :rule log2_intro)": false,
        }
    }
}

#[test]
fn to_int_intro() {
    test_cases! {
        definitions = "
            (declare-const x Real)
            (declare-const y Real)
        ",
        "Simple working examples" {
            "(step t1 (cl
                (and (<= 0 (- x (to_real (to_int x)))) (< (- x (to_real (to_int x))) 1))
            ) :rule to_int_intro)": true,
        }
        "Different values of x" {
            "(step t1 (cl
                (and (<= 0 (- x (to_real (to_int x)))) (< (- y (to_real (to_int x))) 1))
            ) :rule to_int_intro)": false,
        }
    }
}

// Added in Clean: every `evaluate` counterexample found by the soundness battery
// (third-party/carcara/soundness), next to the correct value.
#[test]
fn evaluate_smt_lib_semantics() {
    test_cases! {
        definitions = "",
        // Added in Clean: SMT-LIB reads `(_ bv<n> <w>)` as `n mod 2^w`, and the literal used to
        // be taken as written (see third-party/carcara/DOWNSTREAM.md)
        "Bitvector literals are reduced modulo 2^w" {
            "(step t1 (cl (= (= (_ bv5 2) #b01) false)) :rule evaluate)": false,
            "(step t1 (cl (= (= (_ bv5 2) #b01) true)) :rule evaluate)": true,
            "(step t1 (cl (= (bvult #b10 (_ bv5 2)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (bvult #b10 (_ bv5 2)) false)) :rule evaluate)": true,
            "(step t1 (cl (= (bvadd (_ bv7 2) #b01) #b00)) :rule evaluate)": true,
            "(step t1 (cl (= (bvslt (_ bv6 2) #b01) true)) :rule evaluate)": true,
            "(step t1 (cl (= (_ bv4 2) #b00)) :rule eq_reflexive)": true,
        }
        // Added in Clean: widths were cast to `u32`, so a width of `2^32 + k` was read as `k`
        // (fix 35, see third-party/carcara/DOWNSTREAM.md). Each false case below is false in
        // SMT-LIB and was accepted; evaluation now leaves widths above 2^16 unevaluated.
        "Bit-vector widths are not truncated to 32 bits" {
            "(step t1 (cl (= (= ((_ sign_extend 4294967295) #b1) ((_ sign_extend 4294967295) #b0)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (= (bvadd (concat ((_ sign_extend 4294967295) #b0) #b1) (concat ((_ sign_extend 4294967295) #b0) #b1)) (concat ((_ sign_extend 4294967295) #b0) #b0)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (= ((_ zero_extend 4294967295) #b1) ((_ zero_extend 4294967295) #b0)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (= (_ bv5 4294967298) (_ bv1 4294967298)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (= ((_ repeat 4294967296) #b1) ((_ repeat 4294967296) #b0)) true)) :rule evaluate)": false,
            "(step t1 (cl (= (bvult ((_ zero_extend 4294967295) #b0) ((_ zero_extend 4294967295) #b1)) false)) :rule evaluate)": false,
            // Up to the bound, wide widths still evaluate
            "(step t1 (cl (= (= ((_ zero_extend 65535) #b1) ((_ zero_extend 65535) #b0)) false)) :rule evaluate)": true,
            "(step t1 (cl (= (= ((_ sign_extend 65535) #b1) ((_ sign_extend 65535) #b1)) true)) :rule evaluate)": true,
        }
        "Wide literals are distinct terms" {
            "(step t1 (cl (= (_ bv5 4294967298) (_ bv1 4294967298))) :rule refl)": false,
            "(step t1 (cl (= (_ bv7 4294967296) (_ bv0 4294967296))) :rule refl)": false,
            "(step t1 (cl (= (_ bv5 4294967298) (_ bv5 4294967298))) :rule refl)": true,
            "(step t1 (cl (= (_ bv5 2) #b01)) :rule refl)": true,
        }
        "Signed comparisons use two's complement" {
            "(step t1 (cl (= (bvslt #b1111 #b0001) false)) :rule evaluate)": false,
            "(step t1 (cl (= (bvslt #b1111 #b0001) true)) :rule evaluate)": true,
            "(step t1 (cl (= (bvslt #b0 #b1) true)) :rule evaluate)": false,
            "(step t1 (cl (= (bvslt #b0 #b1) false)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsge #b1000 #b0111) false)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsle #b1000 #b1111) true)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsgt #b0001 #b1111) true)) :rule evaluate)": true,
            "(step t1 (cl (= (sbv_to_int #b0111) 7)) :rule evaluate)": true,
            "(step t1 (cl (= (sbv_to_int #b1) 1)) :rule evaluate)": false,
        }
        "Subtraction and signed division" {
            "(step t1 (cl (= (bvsub #b0000 #b1111) #b1111)) :rule evaluate)": false,
            "(step t1 (cl (= (bvsub #b0000 #b1111) #b0001)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsmod #b1011 #b0100) #b0001)) :rule evaluate)": false,
            "(step t1 (cl (= (bvsmod #b1011 #b0100) #b0011)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsmod #b0101 #b1100) #b1101)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsmod #b1011 #b1100) #b1111)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsrem #b1011 #b0100) #b1111)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsrem #b0101 #b1100) #b0001)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsdiv #b1011 #b0100) #b1111)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsdiv #b01 #b11) #b11)) :rule evaluate)": true,
            "(step t1 (cl (= (bvsdiv #b01 #b11) #b01)) :rule evaluate)": false,
        }
        "Sign extension, extraction and rotation" {
            "(step t1 (cl (= ((_ sign_extend 4) #b1011) #b00000101)) :rule evaluate)": false,
            "(step t1 (cl (= ((_ sign_extend 4) #b1011) #b11111011)) :rule evaluate)": true,
            "(step t1 (cl (= ((_ extract 0 0) #b1) #b0)) :rule evaluate)": false,
            "(step t1 (cl (= ((_ extract 0 0) #b1) #b1)) :rule evaluate)": true,
            "(step t1 (cl (= ((_ extract 3 2) #b1000) #b10)) :rule evaluate)": true,
            "(step t1 (cl (= ((_ rotate_left 4) #b001) #b001)) :rule evaluate)": false,
            "(step t1 (cl (= ((_ rotate_left 4) #b001) #b010)) :rule evaluate)": true,
        }
        "Shifts by at least the width" {
            "(step t1 (cl (= (bvashr #b1000 #b0100) #b1111)) :rule evaluate)": true,
            "(step t1 (cl (= (bvashr #b0101100 #b0101100) #b0000000)) :rule evaluate)": true,
            "(step t1 (cl (= (bvshl #b0011 #b1111) #b0000)) :rule evaluate)": true,
        }
        "Integer division is Euclidean" {
            "(step t1 (cl (= (div (- 4) (- 3)) 1)) :rule evaluate)": false,
            "(step t1 (cl (= (div (- 4) (- 3)) 2)) :rule evaluate)": true,
            "(step t1 (cl (= (mod (- 4) (- 3)) (- 1))) :rule evaluate)": false,
            "(step t1 (cl (= (mod (- 4) (- 3)) 2)) :rule evaluate)": true,
            "(step t1 (cl (= (div (- 7) (- 2)) 3)) :rule evaluate)": false,
            "(step t1 (cl (= (div (- 7) (- 2)) 4)) :rule evaluate)": true,
        }
        "Division by zero has no value" {
            "(step t1 (cl (= (div 3 0) 0)) :rule evaluate)": false,
            "(step t1 (cl (= (mod 3 0) 3)) :rule evaluate)": false,
            "(step t1 (cl (= (/ 1.0 0.0) 0.0)) :rule evaluate)": false,
            "(step t1 (cl (= (div 3 0) (div 3 0))) :rule evaluate)": true,
        }
    }
}

// Added in Clean: `beta_equiv` on a partial application must not capture an argument.
#[test]
fn beta_equiv_capture() {
    test_cases! {
        definitions = "
            (declare-const y Int)
            (declare-const v Int)
            (declare-const w Int)
        ",
        "Captured argument" {
            "(step t1 (cl (= ((lambda ((z Int) (y Int)) (+ z y)) y) (lambda ((y Int)) (+ y y))))
                :rule beta_equiv)": false,
            // An argument with more free variables than there are remaining binders: the binders'
            // names are looked up in its set
            "(step t1 (cl (= ((lambda ((z Int) (y Int)) (+ z y)) (+ v y))
                (lambda ((y Int)) (+ (+ v y) y)))) :rule beta_equiv)": false,
        }
        "Shadowed applied binder" {
            "(step t1 (cl (= ((lambda ((x Int) (x Int)) x) 5) (lambda ((x Int)) 5)))
                :rule beta_equiv)": false,
        }
        "No capture" {
            "(step t1 (cl (= ((lambda ((z Int) (w Int)) (+ z w)) y) (lambda ((w Int)) (+ y w))))
                :rule beta_equiv)": true,
            "(step t1 (cl (= ((lambda ((z Int) (y Int)) (+ z y)) 1) (lambda ((y Int)) (+ 1 y))))
                :rule beta_equiv)": true,
            "(step t1 (cl (= ((lambda ((z Int) (y Int)) (+ z y)) (+ v w))
                (lambda ((y Int)) (+ (+ v w) y)))) :rule beta_equiv)": true,
        }
    }
}
